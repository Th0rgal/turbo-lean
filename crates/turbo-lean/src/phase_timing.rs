//! End-to-end phase timing ledger for `turbo-lean check` (`#408`).
//!
//! Records wall-clock phase intervals relative to a single immutable command start [`Instant`],
//! merges overlapping intervals to compute honest non-overlapping wall coverage, and reports
//! both the raw phase sum (`phase_sum_ms`) and the merged union (`phase_covered_ms`) alongside
//! any overlap (`phase_overlap_ms`).

use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
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

#[derive(Debug, Clone)]
pub struct PhaseTimer {
    t0: Instant,
    phases_ns: BTreeMap<&'static str, u64>,
    intervals: Vec<PhaseInterval>,
}

impl PhaseTimer {
    pub fn new() -> Self {
        Self::from_start(Instant::now())
    }

    pub fn from_start(t0: Instant) -> Self {
        Self {
            t0,
            phases_ns: BTreeMap::new(),
            intervals: Vec::new(),
        }
    }

    pub fn start_instant(&self) -> Instant {
        self.t0
    }

    pub fn elapsed(&self) -> Duration {
        self.t0.elapsed()
    }

    pub fn elapsed_ms(&self) -> u64 {
        self.t0.elapsed().as_millis() as u64
    }

    pub fn time_phase<T>(&mut self, name: &'static str, f: impl FnOnce(&mut Self) -> T) -> T {
        let start_ns = self.t0.elapsed().as_nanos() as u64;
        let out = f(self);
        let end_ns = (self.t0.elapsed().as_nanos() as u64).max(start_ns);
        self.record_span_ns(name, start_ns, end_ns);
        out
    }

    pub fn record_span_ns(&mut self, name: &'static str, start_ns: u64, end_ns: u64) {
        let end_ns = end_ns.max(start_ns);
        let dur_ns = end_ns - start_ns;
        *self.phases_ns.entry(name).or_insert(0) += dur_ns;
        if dur_ns > 0 {
            self.intervals.push(PhaseInterval { start_ns, end_ns });
        }
    }

    pub fn finish(&self) -> PhaseTimingReport {
        self.finish_at(self.t0.elapsed())
    }

    pub fn finish_at(&self, wall: Duration) -> PhaseTimingReport {
        let wall_ns = wall.as_nanos() as u64;
        let sum_ns: u64 = self.phases_ns.values().copied().sum();
        let covered_ns = merged_interval_ns(&self.intervals);
        let overlap_ns = sum_ns.saturating_sub(covered_ns);
        let coverage_ratio = if wall_ns == 0 {
            1.0
        } else {
            (covered_ns as f64 / wall_ns as f64).min(1.0)
        };
        let phases_ms = self
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
