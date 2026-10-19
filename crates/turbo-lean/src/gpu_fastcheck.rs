//! GPU & CPU FastCheck counterexample runner and Lean 4 Prop -> CUDA transpiler.

pub fn parse_gpu_fastcheck_output(
    stdout: &str,
    exec_ms: u128,
    total_ms: u128,
    remote_host: Option<&str>,
) -> serde_json::Value {
    let mut gpu_device = String::new();
    let mut valid_lemma_10m_ms = 0.0f64;
    let mut valid_lemma_10m_mstates_s = 0.0f64;
    let mut suite_10m_ms = 0.0f64;
    let mut suite_10m_mstates_s = 0.0f64;
    let mut cumutate_kernel_ms = 0.0f64;
    let mut cumutate_throughput_mevals_s = 0.0f64;
    let mut mutants_killed = 0u64;
    let mut mutants_total = 0u64;

    for line in stdout.lines() {
        let l = line.trim();
        if l.starts_with("=== CuDenote GPU Benchmark on ") {
            if let Some(rest) = l.strip_prefix("=== CuDenote GPU Benchmark on ") {
                if let Some(end) = rest.find(" ===") {
                    gpu_device = rest[..end].to_string();
                }
            }
        } else if l.starts_with("[Fast-Check Valid Lemma (10000000 states)]") {
            if let Some(t_idx) = l.find("Time: ") {
                let after = &l[t_idx + 6..];
                if let Some(ms_idx) = after.find(" ms") {
                    valid_lemma_10m_ms = after[..ms_idx].trim().parse().unwrap_or(0.0);
                }
            }
            if let Some(tp_idx) = l.find("Throughput: ") {
                let after = &l[tp_idx + 12..];
                if let Some(m_idx) = after.find(" M states/s") {
                    valid_lemma_10m_mstates_s = after[..m_idx].trim().parse().unwrap_or(0.0);
                }
            }
        } else if l.starts_with("[Fast-Reject 3-Lemma Suite (10000000 states)]") {
            if let Some(t_idx) = l.find("Time: ") {
                let after = &l[t_idx + 6..];
                if let Some(ms_idx) = after.find(" ms") {
                    suite_10m_ms = after[..ms_idx].trim().parse().unwrap_or(0.0);
                }
            }
            if let Some(tp_idx) = l.find("Throughput: ") {
                let after = &l[tp_idx + 12..];
                if let Some(m_idx) = after.find(" M states/s") {
                    suite_10m_mstates_s = after[..m_idx].trim().parse().unwrap_or(0.0);
                }
            }
        } else if l.starts_with("-> Kernel Time: ") {
            if let Some(after) = l.strip_prefix("-> Kernel Time: ") {
                if let Some(ms_idx) = after.find(" ms") {
                    cumutate_kernel_ms = after[..ms_idx].trim().parse().unwrap_or(0.0);
                }
            }
            if let Some(tp_idx) = l.find("Throughput: ") {
                let after = &l[tp_idx + 12..];
                if let Some(m_idx) = after.find(" M Denote-evals/s") {
                    cumutate_throughput_mevals_s = after[..m_idx].trim().parse().unwrap_or(0.0);
                }
            }
        } else if l.starts_with("-> Mutants Killed: ") {
            if let Some(after) = l.strip_prefix("-> Mutants Killed: ") {
                if let Some((k_str, rest)) = after.split_once(" / ") {
                    mutants_killed = k_str.trim().parse().unwrap_or(0);
                    if let Some((tot_str, _)) = rest.split_once(' ') {
                        mutants_total = tot_str.trim().parse().unwrap_or(0);
                    }
                }
            }
        }
    }

    serde_json::json!({
        "status": "ok",
        "mode": if remote_host.is_some() { "remote_gpu_cuda" } else { "local_gpu_cuda" },
        "remote_host": remote_host,
        "gpu_device": gpu_device,
        "throughput_mstates_s": valid_lemma_10m_mstates_s,
        "valid_lemma_10m_kernel_ms": valid_lemma_10m_ms,
        "fast_reject_3lemma_10m_kernel_ms": suite_10m_ms,
        "fast_reject_3lemma_mstates_s": suite_10m_mstates_s,
        "cumutate_kernel_ms": cumutate_kernel_ms,
        "cumutate_throughput_mevals_s": cumutate_throughput_mevals_s,
        "mutants_killed": mutants_killed,
        "mutants_total": mutants_total,
        "exec_ms": exec_ms,
        "total_ms": total_ms,
        "output": stdout.trim()
    })
}

