# clifv paired benchmark (A0e) — vast.ai dedicated VM (`rtx4090-a`), 2026-11-01

Status: **setup in progress** (toolchains & `turbo-lean` release build starting).

- `turbo-lean` origin/main SHA: `0212d865be1a1093decef308225a0badcdccb526`
- `clifv` target SHA: `5018b95` (`5018b9509dc124154dbe08a5bd85862595d8eab7`)
- Host: Vast.ai dedicated VM (`3fc010451603`, `rtx4090-a`), Intel(R) Xeon(R) CPU E5-2680 v4 @ 2.40GHz (`nproc=28`, cgroup CPU quota 26.88 cores, cgroup RAM cap 60.13 GiB / 62 GiB host, 117 GiB free local disk on device 96 vs `/dev/shm` device 163).
- Initial load before setup: `0.15, 0.22, 0.78` (idle dedicated VM).
