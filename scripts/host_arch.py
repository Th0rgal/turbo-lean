"""Host CPU architecture in the Lean `TargetArch` spelling, shared by the stage scripts.

One source of truth for "what does this host's CPU natively run" so the scripts
agree with each other and with `TargetArch.host` on the Lean side and
`host_cpu_arch` on the Rust side (crates/turbo-lean/src/gpu_fastcheck.rs).
An unsupported machine raises instead of silently mapping to x86_64: the legs
that use this value emit IR and link it natively, and x86 IR on a riscv64 or
s390x host would fail in confusing downstream ways.
"""
from __future__ import annotations

import platform

SUPPORTED_MACHINES: dict[str, str] = {
    "x86_64": "x86_64",
    "amd64": "x86_64",
    "aarch64": "arm64",
    "arm64": "arm64",
}


def host_target_arch() -> str:
    """`"x86_64"` or `"arm64"` for the host CPU, in the `--arch` spelling the
    Lean CLIs take. Raises `RuntimeError` on machines the native-emission legs
    do not support."""
    machine = platform.machine().lower()
    try:
        return SUPPORTED_MACHINES[machine]
    except KeyError:
        raise RuntimeError(
            f"unsupported host CPU architecture {machine!r}: the native-emission "
            "legs support x86_64 and aarch64 hosts only"
        ) from None
