//! M11 (`GOALS.md` G5 / adversarial `.olean` & daemon socket fuzzing):
//! adversarial daemon socket framing must be rejected deterministically
//! fail-closed with a structured HTTP error (0 panics, 0 hangs) on both the
//! local daemon unix socket and the TCP transport, while valid payloads
//! (`GET /health`) keep passing end-to-end.
#![cfg(target_os = "linux")]

use std::io::{Read, Write};
use std::net::{Shutdown, TcpListener, TcpStream};
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

const BIN: &str = env!("CARGO_BIN_EXE_turbo-lean");

trait ReadWrite: Read + Write + Socket {}
impl<T: Read + Write + Socket> ReadWrite for T {}

/// Socket controls shared by the unix-socket and TCP transports.
trait Socket {
    fn set_read_timeout(&mut self, timeout: Option<Duration>) -> std::io::Result<()>;
    fn set_write_timeout(&mut self, timeout: Option<Duration>) -> std::io::Result<()>;
    fn shutdown(&mut self, how: Shutdown) -> std::io::Result<()>;
}

impl Socket for UnixStream {
    fn set_read_timeout(&mut self, timeout: Option<Duration>) -> std::io::Result<()> {
        UnixStream::set_read_timeout(self, timeout)
    }
    fn set_write_timeout(&mut self, timeout: Option<Duration>) -> std::io::Result<()> {
        UnixStream::set_write_timeout(self, timeout)
    }
    fn shutdown(&mut self, how: Shutdown) -> std::io::Result<()> {
        UnixStream::shutdown(self, how)
    }
}

impl Socket for TcpStream {
    fn set_read_timeout(&mut self, timeout: Option<Duration>) -> std::io::Result<()> {
        TcpStream::set_read_timeout(self, timeout)
    }
    fn set_write_timeout(&mut self, timeout: Option<Duration>) -> std::io::Result<()> {
        TcpStream::set_write_timeout(self, timeout)
    }
    fn shutdown(&mut self, how: Shutdown) -> std::io::Result<()> {
        TcpStream::shutdown(self, how)
    }
}

struct ChildGuard(Child);

impl Drop for ChildGuard {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

struct Server {
    _child: ChildGuard,
    port: u16,
    socket: PathBuf,
    root: PathBuf,
    staging: PathBuf,
    stderr: std::sync::Arc<std::sync::Mutex<Vec<u8>>>,
}

impl Drop for Server {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.root);
        let _ = std::fs::remove_dir_all(&self.staging);
    }
}

fn unique_tag(name: &str) -> String {
    format!(
        "turbo-socket-framing-{name}-{}-{}",
        std::process::id(),
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    )
}

/// Continuously drain a child pipe into a shared buffer so the test can
/// inspect stderr while the daemon is still running.
fn drain_pipe<R: Read + Send + 'static>(mut pipe: R) -> std::sync::Arc<std::sync::Mutex<Vec<u8>>> {
    let shared = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
    let sink = shared.clone();
    std::thread::spawn(move || {
        let mut chunk = [0u8; 4096];
        loop {
            match pipe.read(&mut chunk) {
                Ok(0) | Err(_) => break,
                Ok(n) => {
                    if let Ok(mut buf) = sink.lock() {
                        buf.extend_from_slice(&chunk[..n]);
                    }
                }
            }
        }
    });
    shared
}

fn spawn_server(tag: &str) -> Server {
    let root = std::env::temp_dir().join(unique_tag(tag));
    let staging = Path::new("/dev/shm").join(unique_tag(tag));
    std::fs::create_dir_all(root.join("home")).unwrap();
    std::fs::create_dir_all(&staging).unwrap();
    let socket = root.join("daemon.sock");
    // Pick a free TCP port deterministically: bind an ephemeral listener, read
    // its port, and drop it before the server binds.
    let port = {
        let probe = TcpListener::bind("127.0.0.1:0").unwrap();
        probe.local_addr().unwrap().port()
    };
    let mut cmd = Command::new(BIN);
    cmd.args([
        "serve",
        "--listen",
        &format!("127.0.0.1:{port}"),
        "--allow-unauthenticated-local",
    ])
    .current_dir(&root)
    .env("HOME", root.join("home"))
    .env("TURBO_LEAN_HOME", root.join("cas"))
    .env("TURBO_LEAN_STAGING_DIR", &staging)
    .env("TURBO_LEAN_TELEMETRY", "off")
    .env("LEAN_NATIVE_TELEMETRY", "off")
    .env("LEAN_NUM_THREADS", "2")
    .env("TURBO_LEAN_DAEMON", "1")
    .env("TURBO_LEAN_DAEMON_IDLE_SECS", "600")
    .env("TURBO_LEAN_DAEMON_SOCKET", &socket)
    .stdin(Stdio::null())
    .stdout(Stdio::piped())
    .stderr(Stdio::piped());
    let mut child = cmd.spawn().unwrap();
    drain_pipe(child.stdout.take().unwrap());
    let stderr = drain_pipe(child.stderr.take().unwrap());
    // Wait for both listeners (the startup receipt also proves the binary came up).
    let deadline = Instant::now() + Duration::from_secs(60);
    loop {
        let tcp_ready = TcpStream::connect_timeout(
            &std::net::SocketAddr::from(([127, 0, 0, 1], port)),
            Duration::from_secs(2),
        )
        .is_ok();
        let unix_ready = socket.exists();
        if tcp_ready && unix_ready {
            break;
        }
        assert!(
            Instant::now() < deadline,
            "serve did not become ready: tcp_ready={tcp_ready} unix_ready={unix_ready}"
        );
        std::thread::sleep(Duration::from_millis(50));
    }
    Server {
        _child: ChildGuard(child),
        port,
        socket,
        root,
        staging,
        stderr,
    }
}

/// Read one complete HTTP reply (head + content-length body), bounded.
/// Returns `None` when the connection is closed/truncated before a full reply.
fn read_http_reply(stream: &mut dyn Read) -> Option<(u16, String)> {
    let mut head = Vec::with_capacity(512);
    let mut byte = [0u8; 1];
    loop {
        match stream.read(&mut byte) {
            Ok(0) => return None,
            Ok(_) => head.push(byte[0]),
            Err(_) => return None,
        }
        if head.ends_with(b"\r\n\r\n") || head.len() > 128 * 1024 {
            break;
        }
    }
    let head = String::from_utf8_lossy(&head).into_owned();
    let status: u16 = head.split_whitespace().nth(1)?.parse().ok()?;
    let len: usize = head
        .lines()
        .find_map(|l| {
            let (k, v) = l.split_once(':')?;
            k.eq_ignore_ascii_case("content-length")
                .then(|| v.trim().parse().ok())?
        })
        .unwrap_or(0);
    let mut body = vec![0u8; len];
    stream.read_exact(&mut body).ok()?;
    Some((status, String::from_utf8_lossy(&body).into_owned()))
}

fn send_raw(stream: &mut dyn ReadWrite, raw: &[u8]) -> Option<(u16, String)> {
    stream
        .set_read_timeout(Some(Duration::from_secs(10)))
        .ok()?;
    stream
        .set_write_timeout(Some(Duration::from_secs(10)))
        .ok()?;
    stream.write_all(raw).ok()?;
    // Half-close so the server's bounded error drain observes EOF deterministically.
    let _ = stream.shutdown(Shutdown::Write);
    read_http_reply(stream)
}

fn expect(failures: &mut Vec<String>, label: &str, cond: bool) {
    if !cond {
        failures.push(label.to_string());
    }
}

fn expect_reply(
    failures: &mut Vec<String>,
    none_label: &str,
    stream: &mut impl ReadWrite,
    raw: &[u8],
) -> (u16, String) {
    match send_raw(stream, raw) {
        Some(reply) => reply,
        None => {
            failures.push(none_label.to_string());
            (0, String::new())
        }
    }
}

fn connect_unix(server: &Server) -> UnixStream {
    UnixStream::connect(&server.socket).unwrap()
}

fn connect_tcp(server: &Server) -> TcpStream {
    TcpStream::connect(("127.0.0.1", server.port)).unwrap()
}

const HEALTH_OK_BODY: &str = "GET /health HTTP/1.1\r\nHost: localhost\r\n\r\n";

#[test]
fn adversarial_daemon_socket_framing_is_fail_closed() {
    let server = spawn_server("main");
    let mut failures: Vec<String> = Vec::new();

    // Valid payloads keep passing on both transports before the adversarial set.
    let (status, body) = expect_reply(
        &mut failures,
        "tcp valid /health got no reply",
        &mut connect_tcp(&server),
        HEALTH_OK_BODY.as_bytes(),
    );
    expect(
        &mut failures,
        "tcp valid /health answers 200 ok",
        status == 200 && body.contains("\"ok\":true"),
    );
    let (status, body) = expect_reply(
        &mut failures,
        "unix valid /health got no reply",
        &mut connect_unix(&server),
        HEALTH_OK_BODY.as_bytes(),
    );
    expect(
        &mut failures,
        "unix valid /health answers 200 ok",
        status == 200 && body.contains("\"ok\":true"),
    );

    // Adversarial 1: multi-byte UTF-8 inside framing-sensitive header names
    // (`content-lengthé`, `beareré`) must never panic the handler thread nor
    // drop the connection without a reply.
    for (transport, raw) in [
        (
            "unix",
            "GET /health HTTP/1.1\r\ncontent-lengthé: 5\r\n\r\n".as_bytes(),
        ),
        (
            "tcp",
            "GET /health HTTP/1.1\r\ncontent-lengthé: 5\r\n\r\n".as_bytes(),
        ),
        (
            "unix",
            "GET /health HTTP/1.1\r\nauthorization: beareré\r\n\r\n".as_bytes(),
        ),
    ] {
        let mut stream: Box<dyn ReadWrite> = match transport {
            "unix" => Box::new(connect_unix(&server)),
            _ => Box::new(connect_tcp(&server)),
        };
        let reply = send_raw(&mut *stream, raw);
        expect(
            &mut failures,
            &format!("{transport} multibyte header yields a deterministic reply (got {reply:?})"),
            reply.is_some(),
        );
    }

    // Adversarial 2: oversized header line (1 MiB) must be rejected with a
    // structured 4xx, not buffered unboundedly and answered 200.
    let mut oversized_header = String::from("GET /health HTTP/1.1\r\nX-Big: ");
    oversized_header.extend(std::iter::repeat_n('A', 1024 * 1024));
    oversized_header.push_str("\r\n\r\n");
    let reply = send_raw(&mut connect_unix(&server), oversized_header.as_bytes());
    expect(
        &mut failures,
        &format!("unix oversized header line rejected with 4xx (got {reply:?})"),
        matches!(reply, Some((status, body)) if (400..500).contains(&status) && body.contains("\"error\"")),
    );

    // Adversarial 3: garbage request line (single token) must get a structured
    // 400 instead of a silent connection close.
    let reply = send_raw(&mut connect_unix(&server), b"garbage\r\n\r\n");
    expect(
        &mut failures,
        &format!("unix garbage request line rejected with 400 (got {reply:?})"),
        matches!(reply, Some((400, body)) if body.contains("\"error\"")),
    );

    // Adversarial 4: oversized request line (64 KiB) must be rejected with a
    // structured 4xx instead of a silent close.
    let mut oversized_line = String::new();
    oversized_line.extend(std::iter::repeat_n('A', 64 * 1024));
    oversized_line.push_str("\r\n\r\n");
    let reply = send_raw(&mut connect_unix(&server), oversized_line.as_bytes());
    expect(
        &mut failures,
        &format!("unix oversized request line rejected with 4xx (got {reply:?})"),
        matches!(reply, Some((status, body)) if (400..500).contains(&status) && body.contains("\"error\"")),
    );

    // Adversarial 5: oversized content-length is refused with 413 (existing
    // contract, must survive the head-parser hardening).
    let reply = send_raw(
        &mut connect_unix(&server),
        b"POST /eval HTTP/1.1\r\ncontent-length: 999999999999\r\n\r\n",
    );
    expect(
        &mut failures,
        &format!("unix oversized content-length refused with 413 (got {reply:?})"),
        matches!(reply, Some((413, _))),
    );

    // The daemon must still be healthy on both transports after the barrage
    // (0 hangs, 0 crashes), and stderr must be panic-free.
    let (status, body) = expect_reply(
        &mut failures,
        "tcp post-adversarial /health got no reply",
        &mut connect_tcp(&server),
        HEALTH_OK_BODY.as_bytes(),
    );
    expect(
        &mut failures,
        "tcp post-adversarial /health answers 200 ok",
        status == 200 && body.contains("\"ok\":true"),
    );
    let (status, body) = expect_reply(
        &mut failures,
        "unix post-adversarial /health got no reply",
        &mut connect_unix(&server),
        HEALTH_OK_BODY.as_bytes(),
    );
    expect(
        &mut failures,
        "unix post-adversarial /health answers 200 ok",
        status == 200 && body.contains("\"ok\":true"),
    );

    // Give in-flight handler threads a moment to flush stderr, then inspect it.
    std::thread::sleep(Duration::from_millis(500));
    let stderr = String::from_utf8_lossy(&server.stderr.lock().unwrap()).into_owned();
    expect(
        &mut failures,
        &format!("daemon stderr is panic-free (stderr: {stderr})"),
        !stderr.contains("panicked at"),
    );

    assert!(
        failures.is_empty(),
        "M11 adversarial framing violations:\n  - {}",
        failures.join("\n  - ")
    );
}
