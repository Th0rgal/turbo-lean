"""Host CPU architecture in the Lean `TargetArch` spelling, shared by the stage scripts.

One source of truth for "what does this host's CPU natively run" so the scripts
agree with each other and with `TargetArch.host` on the Lean side. An
unsupported machine raises instead of silently mapping to x86_64: the legs that
use this value emit IR and link it natively, and x86 IR on a riscv64 or s390x
host would fail in confusing downstream ways. (The Rust-side `host_cpu_arch` in
crates/turbo-lean/src/gpu_fastcheck.rs still takes that silent x86_64 fallback
for its builtin module; this module is deliberately stricter.)
"""
from __future__ import annotations

import os
import platform

SUPPORTED_MACHINES: dict[str, str] = {
    "x86_64": "x86_64",
    "amd64": "x86_64",
    "aarch64": "arm64",
    "arm64": "arm64",
}


def strict_tools_default(env_var: str) -> bool:
    """Strict missing-engine handling for a stage: `true`/`1` turns it on,
    `false`/`0`/unset leaves it off. There is no implicit CI default: the jobs
    that provision the tools opt in explicitly in their workflow env (the
    impact-gate jobs run the self-tests on runners with no LLVM install, so a
    CI-keyed default would fail them). Any other value (`yes`, `on`, a typo) is
    refused loudly instead of silently reading as unset."""
    raw = os.environ.get(env_var, "")
    value = raw.strip().lower()
    if value in ("true", "1"):
        return True
    if value in ("false", "0", ""):
        return False
    raise RuntimeError(f"{env_var} must be true/1 or false/0/unset (got {raw!r})")


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
