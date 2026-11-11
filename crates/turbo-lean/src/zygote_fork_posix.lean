/-
  TurboLean.ZygoteFork: CompactedRegion-Backed POSIX CoW Fork Pool & Parallel Race Orchestrator

  Architectural Invariant (Zero RC-Dirty CoW Pages & Task-Manager Quiescing):
  1. Never `fork()` across a live uncompacted Lean heap for shared environment data: Lean 4's
     per-object reference counter (`m_rc != 0`) mutates cache lines on every read/drop, triggering
     immediate OS copy-on-write page faults across child processes. Instead, every imported module
     closure (`Lean.importModules`) and compacted `.olean` prefix outline (`Lean.saveModuleData` /
     `Lean.readModuleData` returning `ModuleData × CompactedRegion`) resides in mmap/compacted
     memory regions where `m_rc == 0` (persistent/immortal objects), so forked children read the
     entire imported environment with zero reference-count writes and zero CoW page faults.
  2. Why `Lean.Elab.Command.State` is not directly compacted: `Command.State` (`Lean/Elab/Command.lean`)
     stores live `Task` handles (`snapshotTasks`, `prevLinterStates`, `codeQualityEntryTasks`) and
     `EnvExtension` `IO.Ref`/closure state that cannot be serialized into a `CompactedRegion`.
     Accordingly, forked workers either import a compacted prefix outline `.olean` into `baseEnv`
     before `fork()` or re-elaborate any uncompacted prefix delta inside the child after `fork()`.
  3. Task-manager quiescing: POSIX `fork()` only clones the calling OS thread, stranding any active
     Lean `std::thread` task-manager workers and internal mutexes in the child. Every `fork()` call
     is bracketed by `lean_finalize_task_manager()` immediately prior to `fork()` and
     `lean_init_task_manager_using(...)` immediately after `fork()` in both parent and child.
  4. Descriptor & lock isolation: Forked children never read from the parent's `stdin`, never write
     to the parent's `stdout` protocol stream, and never touch parent file locks; each child writes
     its serialized result exclusively to its private pipe write-end and terminates via `_exit(0)`.
-/
import Lean.Environment

namespace TurboLean.ZygoteFork

@[extern c inline "({ lean_finalize_task_manager(); lean_io_result_mk_ok(lean_box(0)); })"]
opaque finalizeTaskManager : IO Unit

@[extern c inline "({ lean_init_task_manager(); lean_io_result_mk_ok(lean_box(0)); })"]
opaque initTaskManager : IO Unit

@[extern c inline "({ lean_init_task_manager_using((unsigned)(#1)); lean_io_result_mk_ok(lean_box(0)); })"]
opaque initTaskManagerUsing (numWorkers : UInt32) : IO Unit

@[extern c inline "({ extern long sysconf(int); long n = sysconf(84); if (n < 1) n = sysconf(58); if (n < 1) n = 2; lean_io_result_mk_ok(lean_box_uint32((uint32_t)(n > 64 ? 64 : n))); })"]
opaque detectHardwareParallelism : IO UInt32

/-- Create an anonymous POSIX pipe, returning `(readFd, writeFd)` with `FD_CLOEXEC` set. -/
@[extern c inline "({ extern int pipe(int[2]); extern int fcntl(int, int, ...); int fds[2] = {-1, -1}; lean_object *res_ = NULL; if (pipe(fds) != 0) { res_ = lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(\"pipe() failed\"))); } else { fcntl(fds[0], 2, 1); fcntl(fds[1], 2, 1); lean_object *p = lean_alloc_ctor(0, 2, 0); lean_ctor_set(p, 0, lean_box_uint32((uint32_t)fds[0])); lean_ctor_set(p, 1, lean_box_uint32((uint32_t)fds[1])); res_ = lean_io_result_mk_ok(p); } res_; })"]
opaque posixPipe : IO (UInt32 × UInt32)

/-- Close a raw POSIX file descriptor, ignoring errors if already closed. -/
@[extern c inline "({ extern int close(int); (void)close((int)(#1)); lean_io_result_mk_ok(lean_box(0)); })"]
opaque posixClose (fd : UInt32) : IO Unit

/-- Invoke POSIX `fork()`. Caller MUST call `finalizeTaskManager` before and `initTaskManager*` after.
    Returns `0` in the child process and `childPid > 0` in the parent process. -/
@[extern c inline "({ extern int fork(void); int pid = fork(); (pid < 0) ? lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(\"fork() failed\"))) : lean_io_result_mk_ok(lean_box_uint32((uint32_t)pid)); })"]
opaque posixForkRaw : IO UInt32

/-- Connect a private clone channel; the child replaces all protocol and diagnostic descriptors. -/
@[extern c inline "({ extern int socket(int,int,int); extern int connect(int,const void*,unsigned); extern int dup2(int,int); extern int close(int); struct { unsigned short family; char path[108]; } a = {1,{0}}; const char *p = lean_string_cstr(#1); int fd = -1; if (__builtin_strlen(p) < sizeof(a.path)) { __builtin_strcpy(a.path,p); fd = socket(1,1,0); if (fd >= 0 && connect(fd,&a,sizeof(a)) != 0) { close(fd); fd = -1; } } if (fd >= 0) { dup2(fd,(int)(#2)); if ((uint32_t)(#2) == 0) dup2(fd,1); close(fd); } fd < 0 ? lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(\"clone connect failed\"))) : lean_io_result_mk_ok(lean_box(0)); })"]
opaque connectCloneChannel (path : @& String) (target : UInt32) : IO Unit

@[extern c inline "({ extern int waitpid(int,int*,int); int s; while (waitpid(-1,&s,1) > 0) {} lean_io_result_mk_ok(lean_box(0)); })"]
opaque reapClones : IO Unit

/-- Terminate the current forked child process immediately via POSIX `_exit(code)` without flushing parent stdio buffers. -/
@[extern c inline "({ extern void _exit(int) __attribute__((noreturn)); _exit((int)(#1)); lean_io_result_mk_ok(lean_box(0)); })"]
opaque posixExitImmediate (code : UInt32) : IO Unit

/-- Send `SIGKILL` (`9`) to a child PID. Ignores `ESRCH` if the child already exited. -/
@[extern c inline "({ extern int kill(int, int); int pid = (int)(#1); if (pid > 0) { (void)kill(pid, 9); } lean_io_result_mk_ok(lean_box(0)); })"]
opaque posixKillSigkill (pid : UInt32) : IO Unit

/-- Wait for any child (`pid == 0`) or a specific child (`pid > 0`).
    Retries automatically on `EINTR` (`errno == 4`).
    Returns `(reapedPid, rawWaitStatus)` or `(0, 0)` on `ECHILD`/error. -/
@[extern c inline "({ extern int waitpid(int, int *, int); extern int *__errno_location(void) __attribute__((weak)); int target = ((uint32_t)(#1) == 0) ? -1 : (int)(#1); int status = 0; int r = -1; for (;;) { r = waitpid(target, &status, 0); if (r >= 0) break; if (__errno_location && *__errno_location() == 4) continue; break; } uint32_t out_pid = (r > 0) ? (uint32_t)r : 0u; uint32_t out_st = (r > 0) ? (uint32_t)status : 0u; lean_object *p = lean_alloc_ctor(0, 2, 0); lean_ctor_set(p, 0, lean_box_uint32(out_pid)); lean_ctor_set(p, 1, lean_box_uint32(out_st)); lean_io_result_mk_ok(p); })"]
opaque posixWaitPid (pid : UInt32) : IO (UInt32 × UInt32)

/-- Write all bytes of `ba` to `fd`, retrying on partial writes. Returns `true` iff all bytes were written. -/
@[extern c inline "({ extern long write(int, const void *, size_t); int fd = (int)(#1); const uint8_t *buf = lean_sarray_cptr(#2); size_t len = lean_sarray_size(#2); size_t off = 0; int ok = 1; while (off < len) { long w = write(fd, buf + off, len - off); if (w <= 0) { ok = 0; break; } off += (size_t)w; } lean_io_result_mk_ok(lean_box(ok ? 1 : 0)); })"]
opaque posixWriteAll (fd : UInt32) (ba : @& ByteArray) : IO Bool

/-- Read up to `maxBytes` from `fd` until EOF (`0`). -/
@[extern c inline "({ extern long read(int, void *, size_t); int fd = (int)(#1); size_t cap = (size_t)(#2); if (cap < 64) cap = 64; lean_object *arr = lean_alloc_sarray(1, 0, cap); size_t total = 0; for (;;) { if (total == cap) { size_t next_cap = cap * 2; if (next_cap > 16777216) break; lean_object *next = lean_alloc_sarray(1, total, next_cap); __builtin_memcpy(lean_sarray_cptr(next), lean_sarray_cptr(arr), total); lean_dec_ref(arr); arr = next; cap = next_cap; } long r = read(fd, lean_sarray_cptr(arr) + total, cap - total); if (r <= 0) break; total += (size_t)r; } lean_sarray_set_size(arr, total); lean_io_result_mk_ok(arr); })"]
opaque posixReadAll (fd : UInt32) (maxBytes : USize := 65536) : IO ByteArray

/-- True iff `rawWaitStatus` exited normally with exit code `0` (`(status & 0x7f) == 0 && ((status >> 8) & 0xff) == 0`). -/
def waitStatusExitedZero (rawStatus : UInt32) : Bool :=
  (rawStatus &&& 0x7f) == 0 && ((rawStatus >>> 8) &&& 0xff) == 0

/-- Configured concurrency cap for forked candidate racing (`1..=4`, default `min(ncpus, 4)`). -/
def raceForkConcurrency : IO Nat := do
  match ← IO.getEnv "TURBO_LEAN_RACE_FORK_JOBS" with
  | some raw =>
    match raw.trimAscii.toString.toNat? with
    | some n => return Nat.min 4 (Nat.max 1 n)
    | none => pure ()
  | none => pure ()
  let hw ← detectHardwareParallelism
  return Nat.min 4 (Nat.max 1 hw.toNat)

/-- Whether POSIX CoW `fork()` execution is enabled for parallel `race_candidates` (`TURBO_LEAN_ZYGOTE_FORK != "0"`). -/
def isForkEnabled : IO Bool := do
  match ← IO.getEnv "TURBO_LEAN_ZYGOTE_FORK" with
  | some "0" | some "false" => return false
  | _ => return true

/-- Whether single-shard isolated CoW `fork()` execution is requested (`TURBO_LEAN_ZYGOTE_FORK_SHARDS == "1"`). -/
def isSingleShardForkEnabled : IO Bool := do
  match ← IO.getEnv "TURBO_LEAN_ZYGOTE_FORK_SHARDS" with
  | some "1" | some "true" => return true
  | _ => return false

/-- Quiesce the Lean task manager, fork a child with `childWorkers` task threads, and reinitialize
    the parent task manager before returning `some childPid` in the parent (child runs `childAction`
    and immediately `_exit`s, never returning to the caller). -/
def spawnQuiescedForkChild (childWorkers : UInt32 := 2) (childAction : IO UInt32) : IO UInt32 := do
  finalizeTaskManager
  let pid ← try
      posixForkRaw
    catch e =>
      initTaskManager
      throw e
  if pid == 0 then
    initTaskManagerUsing childWorkers
    let code ← try childAction catch _ => pure 1
    posixExitImmediate code
    return 0
  else
    initTaskManager
    return pid

/-- Run an isolated action inside a CoW-forked child over an already-compacted `baseEnv`,
    returning the child's serialized `ByteArray` payload and whether the child exited cleanly (`0`). -/
def runIsolatedInFork (childWorkers : UInt32 := 2) (producePayload : IO ByteArray) : IO (Bool × ByteArray) := do
  let (rFd, wFd) ← posixPipe
  let pid ← try
      spawnQuiescedForkChild childWorkers do
        posixClose rFd
        let bytes ← producePayload
        let ok ← posixWriteAll wFd bytes
        posixClose wFd
        return (if ok then 0 else 2)
    catch e =>
      posixClose rFd
      posixClose wFd
      throw e
  posixClose wFd
  let payload ← posixReadAll rFd 65536
  posixClose rFd
  let (_, rawSt) ← posixWaitPid pid
  return (waitStatusExitedZero rawSt, payload)

end TurboLean.ZygoteFork
