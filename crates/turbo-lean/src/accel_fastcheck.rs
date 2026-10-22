//! Hardware-agnostic Stage-1 counterexample fast-check (`accel_fastcheck`), re-exporting
//! `gpu_fastcheck` (CPU SIMD Perceus FBIP, NVIDIA CUDA GB10, Apple Metal MSL, Cloud TPU XLA).
pub use crate::gpu_fastcheck::*;
