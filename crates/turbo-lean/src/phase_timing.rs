//! End-to-end phase timing ledger for `turbo-lean check` (`#408`).
//!
//! Records wall-clock phase intervals relative to a single immutable command start [`Instant`],
//! merges overlapping intervals to compute honest non-overlapping wall coverage, and reports
//! both the raw phase sum (`phase_sum_ms`) and the merged union (`phase_covered_ms`) alongside
//! any overlap (`phase_overlap_ms`).

use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct PhaseInterval {
    start_ns: u64,
    end_ns: u64,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq)]
pub struct PhaseTimingReport {
    pub wall_ms: f64,
    pub phase_sum_ms: f64,
    pub phase_covered_ms: f64,
    pub phase_overlap_ms: f64,
    pub coverage_ratio: f64,
    pub phases_ms: BTreeMap<String, f64>,
}

#[derive(Debug, Clone, Default)]
struct PhaseLedger {
    phases_ns: BTreeMap<&'static str, u64>,
    intervals: Vec<PhaseInterval>,
}

#[derive(Debug, Clone)]
pub struct PhaseTimer {
    t0: Instant,
    ledger: Arc<Mutex<PhaseLedger>>,
}

thread_local! {
    static ACTIVE_PHASE_TIMER: std::cell::RefCell<Option<PhaseTimer>> = const { std::cell::RefCell::new(None) };
}

pub struct ActivePhaseTimerGuard {
    prev: Option<PhaseTimer>,
}

impl Drop for ActivePhaseTimerGuard {
    fn drop(&mut self) {
        ACTIVE_PHASE_TIMER.with(|cell| {
            *cell.borrow_mut() = self.prev.take();
        });
    }
}

pub fn activate_phase_timer(timer: &PhaseTimer) -> ActivePhaseTimerGuard {
    let prev = ACTIVE_PHASE_TIMER.with(|cell| cell.borrow_mut().replace(timer.clone()));
    ActivePhaseTimerGuard { prev }
}

pub fn active_phase_timer() -> Option<PhaseTimer> {
    ACTIVE_PHASE_TIMER.with(|cell| cell.borrow().clone())
}

pub fn record_active_phase<T>(name: &'static str, f: impl FnOnce() -> T) -> T {
    if let Some(timer) = active_phase_timer() {
        timer.time_phase(name, f)
    } else {
        f()
    }
}

pub fn record_active_span_since(name: &'static str, phase_start: Instant) {
    if let Some(timer) = active_phase_timer() {
        let start_ns = phase_start
            .checked_duration_since(timer.t0)
            .map(|d| d.as_nanos() as u64)
            .unwrap_or(0);
        let end_ns = timer.now_ns().max(start_ns);
        timer.record_span_ns(name, start_ns, end_ns);
    }
}

impl PhaseTimer {
    pub fn new() -> Self {
        Self::from_start(Instant::now())
    }

    pub fn from_start(t0: Instant) -> Self {
        Self {
            t0,
            ledger: Arc::new(Mutex::new(PhaseLedger::default())),
        }
    }

    pub fn start_instant(&self) -> Instant {
        self.t0
    }

    pub fn started_at(&self) -> Instant {
        self.t0
    }

    pub fn record_span_since(&self, name: &'static str, span_start: Instant) {
        let start_ns = span_start
            .checked_duration_since(self.t0)
            .map_or(0, |d| d.as_nanos() as u64);
        let end_ns = self.now_ns().max(start_ns);
        self.record_span_ns(name, start_ns, end_ns);
    }

    pub fn elapsed(&self) -> Duration {
        self.t0.elapsed()
    }

    pub fn elapsed_ms(&self) -> u64 {
        self.t0.elapsed().as_millis() as u64
    }

    pub fn now_ns(&self) -> u64 {
        self.t0.elapsed().as_nanos() as u64
    }

    pub fn time_phase<T>(&self, name: &'static str, f: impl FnOnce() -> T) -> T {
        let start_ns = self.now_ns();
        let out = f();
        let end_ns = self.now_ns().max(start_ns);
        self.record_span_ns(name, start_ns, end_ns);
        out
    }

    pub fn record_span_ns(&self, name: &'static str, start_ns: u64, end_ns: u64) {
        let end_ns = end_ns.max(start_ns);
        let dur_ns = end_ns - start_ns;
        let mut guard = self.ledger.lock().unwrap_or_else(|e| e.into_inner());
        *guard.phases_ns.entry(name).or_insert(0) += dur_ns;
        if dur_ns > 0 {
            guard.intervals.push(PhaseInterval { start_ns, end_ns });
        }
    }

    pub fn finish(&self) -> PhaseTimingReport {
        self.finish_at(self.t0.elapsed())
    }

    pub fn finish_at(&self, wall: Duration) -> PhaseTimingReport {
        let wall_ns = wall.as_nanos() as u64;
        let guard = self.ledger.lock().unwrap_or_else(|e| e.into_inner());
        let sum_ns: u64 = guard.phases_ns.values().copied().sum();
        let covered_ns = merged_interval_ns(&guard.intervals).min(wall_ns.max(1));
        let overlap_ns = sum_ns.saturating_sub(covered_ns);
        let coverage_ratio = if wall_ns == 0 {
            1.0
        } else {
            (covered_ns as f64 / wall_ns as f64).min(1.0)
        };
        let phases_ms = guard
            .phases_ns
            .iter()
            .map(|(k, &v)| ((*k).to_string(), round_ms(v)))
            .collect();
        PhaseTimingReport {
            wall_ms: round_ms(wall_ns),
            phase_sum_ms: round_ms(sum_ns),
            phase_covered_ms: round_ms(covered_ns),
            phase_overlap_ms: round_ms(overlap_ns),
            coverage_ratio: (coverage_ratio * 10_000.0).round() / 10_000.0,
            phases_ms,
        }
    }

    pub fn attach_to_json(&self, out_json: &mut serde_json::Value) -> PhaseTimingReport {
        let wall = self.t0.elapsed();
        let rep = self.finish_at(wall);
        let wall_ms_i64 = (wall.as_millis() as i64).max(rep.wall_ms.round() as i64);
        if let Some(obj) = out_json.as_object_mut() {
            obj.insert("elapsed_ms".to_string(), serde_json::json!(wall_ms_i64));
            if let Ok(val) = serde_json::to_value(&rep) {
                obj.insert("phase_timings".to_string(), val);
            }
        }
        rep
    }
}

impl Default for PhaseTimer {
    fn default() -> Self {
        Self::new()
    }
}

fn round_ms(ns: u64) -> f64 {
    ((ns as f64 / 1_000_000.0) * 1000.0).round() / 1000.0
}

fn merged_interval_ns(intervals: &[PhaseInterval]) -> u64 {
    if intervals.is_empty() {
        return 0;
    }
    let mut sorted = intervals.to_vec();
    sorted.sort_by_key(|iv| (iv.start_ns, iv.end_ns));
    let mut total = 0u64;
    let mut cur = sorted[0];
    for iv in sorted.into_iter().skip(1) {
        if iv.start_ns <= cur.end_ns {
            cur.end_ns = cur.end_ns.max(iv.end_ns);
        } else {
            total += cur.end_ns - cur.start_ns;
            cur = iv;
        }
    }
        total + (cur.end_ns - cur.start_ns)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn phase_timer_reports_honest_coverage_and_overlap() {
        let timer = PhaseTimer::new();
        timer.record_span_ns("setup", 0, 10_000_000);
        timer.record_span_ns("import_refresh", 10_000_000, 50_000_000);
        timer.record_span_ns("zygote_prewarm", 40_000_000, 60_000_000);
        timer.record_span_ns("elaboration", 60_000_000, 95_000_000);
        let rep = timer.finish_at(Duration::from_millis(100));
        assert!((rep.wall_ms - 100.0).abs() < 1e-6);
        assert!((rep.phase_sum_ms - 105.0).abs() < 1e-6);
        assert!((rep.phase_covered_ms - 95.0).abs() < 1e-6);
        assert!((rep.phase_overlap_ms - 10.0).abs() < 1e-6);
        assert!((rep.coverage_ratio - 0.95).abs() < 1e-6);
    }

    #[test]
    fn active_phase_timer_records_nested_spans() {
        let timer = PhaseTimer::new();
        {
            let _guard = activate_phase_timer(&timer);
            let outer_start = Instant::now();
            record_active_phase("zygote_prewarm", || {
                std::thread::sleep(Duration::from_millis(5));
            });
            std::thread::sleep(Duration::from_millis(5));
            record_active_span_since("elaboration", outer_start);
        }
        let rep = timer.finish();
        assert!(rep.phases_ms.contains_key("zygote_prewarm"));
        assert!(rep.phases_ms.contains_key("elaboration"));
        assert!(rep.phase_overlap_ms >= rep.phases_ms["zygote_prewarm"] * 0.8);
        assert!(rep.coverage_ratio >= 0.90);
    }
}
