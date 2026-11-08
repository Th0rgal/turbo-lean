#!/usr/bin/env python3
"""Stage 3A/3B/3C: GPU/TPU Backend & Target-ISA Differential Validation Gate.

Executes concrete modules emitted by `PTXLower`/`MLIRGPU` (PTX 8.0), `StableHLOLower`/`MLIRGPU`
(OpenXLA StableHLO), and `MetalLower`/`Metal` (Apple Metal MSL 3.0) through real external target
compilers and reference interpreters, cross-checking bit-exact agreement against `PTXAst.evalPTXKernel`,
`StableHLOAst.evalFuncOp`, `MetalAst.evalMSLKernel`, and `LeanNative.Semantics.Eval`, plus negative
mutant rejection (`M6..M10` and `H1..H3`):

  1. PTX 8.0 (`ptxas -arch=sm_90 -Werror` + SIMT CTA/warp reference execution):
     - Compiles the full production `emitPTXModule` (including 1D kernels, warp-shuffle `dot_reduce_u64`,
       2D shared-memory `matmul_tiled_u64`, `saxpy_f64`, `map_scale_add_f64`, `fma_f32`) and every lowered
       `PTXLower` kernel to real Hopper `sm_90` SASS cubins with `-Werror` (`0` warnings/errors), and
       verifies `ptxas -Werror` rejects malformed/type-mismatched PTX mutants.
     - Executes every lowered PTX kernel and `matmul_tiled_u64` / `dot_reduce_u64` across multi-thread
       SIMT blocks in an independent PTX ISA reference interpreter, checking 64-bit bit-exact agreement
       and rejecting semantic mutants `M7` (`sub.u64` operand swap) and `M8` (`setp.lt` -> `setp.le`).
  2. OpenXLA StableHLO (`mlir.ir.Module.parse` + `operation.verify()` + `stablehlo.eval_module`):
     - Parses and verifies the full production Google Cloud TPU v6e Trillium `emitStableHLOModule`
       (`bf16`/`f32`/`ui64` `dot_general`, `reduce`, MXU/VPU attributes) via OpenXLA's official MLIR verifier.
     - Executes every `StableHLOLower` / `StableHLOAst.ppModuleOp` case through OpenXLA's official C++
       StableHLO reference interpreter (`mlir.dialects.stablehlo.eval_module`), checking bit-exact tensor
       output agreement and rejecting mutants `H1` (`subtract` swap), `H2` (unmasked `shift_left >= 64`),
       and `H3` (unguarded `divide` by zero).
  3. Apple Metal MSL 3.0 (`clang++ -std=c++17 -O1 -Wall -Wextra -fsanitize=address,undefined`):
     - Compiles the full production `emitMetalModule` (including `ln_u256`, `ln_clmul64`, `dot_reduce_u64`,
       `matmul_tiled_u64`, SNARK `F_{2^128}` NTT, BLAKE3, and `emitFastCheckMetal`) plus every `MetalLower`
       kernel as host C++17 with ASan + UBSan (`-fno-sanitize-recover=all`), executing multi-thread grids
       and verifying bit-exact 64-bit agreement while rejecting `M9` (unguarded `/ 0` caught by UBSan) and
       `M10` (`& 31UL` narrowed shift mask).
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import struct
import subprocess
import sys
import tarfile
import tempfile
import unittest
import urllib.request
import zipfile
from pathlib import Path
from typing import Any

ROOT_DIR = Path(__file__).resolve().parent.parent

# Pinned wheel artifacts for hermetic `--ensure-tools` bootstrapping (no `venv`/`ensurepip` required).
PTXAS_WHEEL_URL = (
    "https://files.pythonhosted.org/packages/25/48/"
    "b54a06168a2190572a312bfe4ce443687773eb61367ced31e064953dd2f7/"
    "nvidia_cuda_nvcc_cu12-12.9.86-py3-none-manylinux2010_x86_64.manylinux_2_12_x86_64.whl"
)
PTXAS_WHEEL_SHA256 = "5d6a0d32fdc7ea39917c20065614ae93add6f577d840233237ff08e9a38f58f0"

STABLEHLO_WHEELS: dict[str, tuple[str, str]] = {
    "cp310": (
        "https://github.com/openxla/stablehlo/releases/download/dev-wheels/"
        "stablehlo-1.12.1.1751868789%2B6f7b4ab8-cp310-cp310-linux_x86_64.whl",
        "00b581e6e67990e810a2b0da5a245f7d49a2e5d461991b2d0bb0711507449153",
    ),
    "cp311": (
        "https://github.com/openxla/stablehlo/releases/download/dev-wheels/"
        "stablehlo-1.12.1.1751868715%2B6f7b4ab8-cp311-cp311-linux_x86_64.whl",
        "7e6bd731377bb4ca38b3e5bb104c499feba868892e1b61fb1f08d9a9ab0da743",
    ),
    "cp312": (
        "https://github.com/openxla/stablehlo/releases/download/dev-wheels/"
        "stablehlo-1.12.1.1751868740%2B6f7b4ab8-cp312-cp312-linux_x86_64.whl",
        "80a1601a97e9e5eb7e232247dc67dd1eec8056a75e33146bc5a1ed57fa9304c3",
    ),
}

NUMPY_WHEELS: dict[str, tuple[str, str]] = {
    "cp310": (
        "https://files.pythonhosted.org/packages/c2/07/"
        "2e5cc71193e3ef3a219ffcf6ca4858e46ea2be09c026ddd480d596b32867/"
        "numpy-2.2.4-cp310-cp310-manylinux_2_17_x86_64.manylinux2014_x86_64.whl",
        "adf8c1d66f432ce577d0197dceaac2ac00c0759f573f28516246351c58a85020",
    ),
    "cp311": (
        "https://files.pythonhosted.org/packages/c5/5c/"
        "ceefca458559f0ccc7a982319f37ed07b0d7b526964ae6cc61f8ad1b6119/"
        "numpy-2.2.4-cp311-cp311-manylinux_2_17_x86_64.manylinux2014_x86_64.whl",
        "f4162988a360a29af158aeb4a2f4f09ffed6a969c9776f8f3bdee9b06a8ab7e5",
    ),
    "cp312": (
        "https://files.pythonhosted.org/packages/02/e2/"
        "e2cbb8d634151aab9528ef7b8bab52ee4ab10e076509285602c2a3a686e0/"
        "numpy-2.2.4-cp312-cp312-manylinux_2_17_x86_64.manylinux2014_x86_64.whl",
        "4f92084defa704deadd4e0a5ab1dc52d8ac9e8a8ef617f3fbb853e79b0ea3592",
    ),
}

STANDALONE_CP312_URL = (
    "https://github.com/astral-sh/python-build-standalone/releases/download/20261026/"
    "cpython-3.12.16%2B20261026-x86_64-unknown-linux-gnu-install_only.tar.gz"
)
STANDALONE_CP312_SHA256 = "6a79e922e50006b601f29e688407659da1c2b86ebcd4e9c7254cf234be8b89de"


def find_compatible_python(cache_dir: Path) -> str | None:
    """Locate an installed CPython 3.10..3.12 binary if current `sys.executable` lacks StableHLO wheels."""
    candidates: list[Path] = [cache_dir / "python312" / "python" / "bin" / "python3"]
    for ver in ("python3.12", "python3.11", "python3.10"):
        w = shutil.which(ver)
        if w:
            candidates.append(Path(w))
    for tc_root in (Path("/opt/hostedtoolcache/Python"), Path(os.environ.get("RUNNER_TOOL_CACHE", "")) / "Python"):
        if tc_root.is_dir():
            for minor in ("3.12", "3.11", "3.10"):
                candidates.extend(sorted(tc_root.glob(f"{minor}.*/x64/bin/python3"), reverse=True))
    for cand in candidates:
        if cand.is_file() and os.access(cand, os.X_OK):
            return str(cand)
    return None


def ensure_compatible_python(cache_dir: Path) -> str:
    found = find_compatible_python(cache_dir)
    if found:
        return found
    cache_dir.mkdir(parents=True, exist_ok=True)
    archive = cache_dir / "cpython-3.12.16-x86_64-linux.tar.gz"
    download_verified(STANDALONE_CP312_URL, archive, STANDALONE_CP312_SHA256)
    dest_dir = cache_dir / "python312"
    dest_dir.mkdir(parents=True, exist_ok=True)
    with tarfile.open(archive, "r:gz") as tf:
        tf.extractall(dest_dir, filter="data")
    py_bin = dest_dir / "python" / "bin" / "python3"
    if not py_bin.is_file():
        raise RuntimeError(f"Expected python3 binary at {py_bin}")
    return str(py_bin)

MASK64 = (1 << 64) - 1
MASK32 = (1 << 32) - 1


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def download_verified(url: str, dest: Path, expected_sha256: str | None = None) -> None:
    dest.parent.mkdir(parents=True, exist_ok=True)
    if dest.is_file():
        if expected_sha256 is None or sha256_file(dest) == expected_sha256:
            return
        dest.unlink()
    tmp = dest.with_suffix(dest.suffix + ".part")
    req = urllib.request.Request(url, headers={"User-Agent": "turbo-lean-ci/1.0"})
    with urllib.request.urlopen(req, timeout=120) as resp, tmp.open("wb") as out:
        shutil.copyfileobj(resp, out)
    if expected_sha256 is not None:
        got = sha256_file(tmp)
        if got != expected_sha256:
            tmp.unlink(missing_ok=True)
            raise RuntimeError(f"SHA-256 mismatch for {url}: expected {expected_sha256}, got {got}")
    tmp.replace(dest)


def safe_extract_zip(zf: zipfile.ZipFile, dest_dir: Path) -> None:
    root = dest_dir.resolve()
    for info in zf.infolist():
        target = (dest_dir / info.filename).resolve()
        if target != root and root not in target.parents:
            raise RuntimeError(f"Refusing zip path traversal entry: {info.filename}")
    zf.extractall(dest_dir)


def ensure_gpu_tpu_tools(cache_dir: Path) -> tuple[str, Path | None]:
    """Ensure `ptxas` and `mlir.dialects.stablehlo` + `numpy` are available, extracting wheels into `cache_dir`."""
    cache_dir.mkdir(parents=True, exist_ok=True)
    ptxas_bin = find_ptxas(cache_dir)
    if ptxas_bin is None:
        whl_path = cache_dir / "nvidia_cuda_nvcc_cu12-12.9.86.whl"
        download_verified(PTXAS_WHEEL_URL, whl_path, PTXAS_WHEEL_SHA256)
        out_ptxas = cache_dir / "bin" / "ptxas"
        out_ptxas.parent.mkdir(parents=True, exist_ok=True)
        with zipfile.ZipFile(whl_path) as zf:
            names = [n for n in zf.namelist() if n.endswith("/bin/ptxas") or n == "bin/ptxas"]
            if not names:
                raise RuntimeError("ptxas binary not found inside nvidia_cuda_nvcc_cu12 wheel")
            out_ptxas.write_bytes(zf.read(names[0]))
        out_ptxas.chmod(0o755)
        ptxas_bin = str(out_ptxas)

    site_dir = cache_dir / "site-packages"
    if site_dir.is_dir() and str(site_dir) not in sys.path:
        sys.path.insert(0, str(site_dir))

    try:
        import numpy as _np  # noqa: F401
        from mlir.dialects import stablehlo as _shlo  # noqa: F401
        return ptxas_bin, (site_dir if site_dir.is_dir() else None)
    except ImportError:
        pass

    py_tag = f"cp{sys.version_info.major}{sys.version_info.minor}"
    site_dir.mkdir(parents=True, exist_ok=True)

    try:
        import numpy as _np  # noqa: F401
    except ImportError:
        if py_tag not in NUMPY_WHEELS:
            raise RuntimeError(f"Unsupported Python ABI tag {py_tag} for pinned numpy wheel")
        np_url, np_sha = NUMPY_WHEELS[py_tag]
        np_whl = cache_dir / f"numpy-2.2.4-{py_tag}.whl"
        download_verified(np_url, np_whl, np_sha)
        with zipfile.ZipFile(np_whl) as zf:
            safe_extract_zip(zf, site_dir)

    if py_tag not in STABLEHLO_WHEELS:
        raise RuntimeError(f"Unsupported Python ABI tag {py_tag} for prebuilt OpenXLA stablehlo wheel")
    shlo_url, shlo_sha = STABLEHLO_WHEELS[py_tag]
    if len(shlo_sha) != 64:
        raise RuntimeError(f"Expected 64-hex SHA-256 for {shlo_url}")
    shlo_whl = cache_dir / f"stablehlo-1.12.1-{py_tag}.whl"
    download_verified(shlo_url, shlo_whl, shlo_sha)
    with zipfile.ZipFile(shlo_whl) as zf:
        safe_extract_zip(zf, site_dir)

    if str(site_dir) not in sys.path:
        sys.path.insert(0, str(site_dir))
    return ptxas_bin, site_dir


def find_ptxas(cache_dir: Path | None = None) -> str | None:
    env_p = os.environ.get("PTXAS")
    if env_p and Path(env_p).is_file() and os.access(env_p, os.X_OK):
        return env_p
    if cache_dir is not None:
        for rel in ("bin/ptxas", "ptxas"):
            cand = cache_dir / rel
            if cand.is_file() and os.access(cand, os.X_OK):
                return str(cand)
    found = shutil.which("ptxas")
    if found:
        return found
    for cand_str in ("/usr/local/cuda/bin/ptxas", "/usr/bin/ptxas"):
        if Path(cand_str).is_file() and os.access(cand_str, os.X_OK):
            return cand_str
    return None


def find_clangxx() -> str | None:
    env_cxx = os.environ.get("CLANGXX")
    if env_cxx and Path(env_cxx).is_file() and os.access(env_cxx, os.X_OK):
        return env_cxx
    for name in ("clang++", "clang++-18", "clang++-19", "clang++-17"):
        found = shutil.which(name)
        if found:
            return found
    return None


# ---------------------------------------------------------------------------
# 1. PTX 8.0 `ptxas` Hardware Assembler Gate + Independent SIMT Reference VM
# ---------------------------------------------------------------------------


def compile_ptx_with_ptxas(ptxas_bin: str, ptx_text: str, arch: str = "sm_90") -> tuple[int, str]:
    with tempfile.TemporaryDirectory(prefix="ln-ptxas-") as tmp:
        ptx_file = Path(tmp) / "module.ptx"
        cubin_file = Path(tmp) / "module.cubin"
        ptx_file.write_text(ptx_text, encoding="utf-8")
        proc = subprocess.run(
            [ptxas_bin, f"-arch={arch}", "-Werror", str(ptx_file), "-o", str(cubin_file)],
            capture_output=True,
            text=True,
            timeout=60,
        )
        out = (proc.stdout or "") + (proc.stderr or "")
        if proc.returncode == 0 and (not cubin_file.is_file() or cubin_file.stat().st_size == 0):
            return 1, "ptxas returned 0 but emitted empty cubin"
        return proc.returncode, out


def _s64(u: int) -> int:
    u &= MASK64
    return u - (1 << 64) if (u & (1 << 63)) else u


def _s32(u: int) -> int:
    u &= MASK32
    return u - (1 << 32) if (u & (1 << 31)) else u


def _parse_ptx_imm_or_reg(
    tok: str,
    regs: dict[str, int],
    preds: dict[str, bool],
    sregs: dict[str, int],
    shared_syms: dict[str, int],
) -> int:
    tok = tok.strip()
    if tok in sregs:
        return sregs[tok]
    if tok in shared_syms:
        return shared_syms[tok]
    if tok.startswith("%p"):
        return 1 if preds.get(tok, False) else 0
    if tok.startswith("%"):
        return regs.get(tok, 0)
    if tok.startswith("0f") or tok.startswith("0F"):
        return int(tok[2:], 16) & MASK32
    if tok.startswith("0d") or tok.startswith("0D"):
        return int(tok[2:], 16) & MASK64
    if tok.startswith("0x") or tok.startswith("0X") or tok.startswith("-0x"):
        return int(tok, 16) & MASK64
    return int(tok, 10) & MASK64


def _parse_ptx_addr(
    addr_tok: str,
    regs: dict[str, int],
    shared_syms: dict[str, int],
) -> int:
    inner = addr_tok.strip()
    assert inner.startswith("[") and inner.endswith("]"), f"bad PTX address token: {addr_tok}"
    body = inner[1:-1].strip()
    m = re.match(r"^([A-Za-z0-9_$.%]+)\s*(?:([+-])\s*([+-]?\s*\d+))?$", body)
    if not m:
        raise ValueError(f"unsupported PTX address expression: {addr_tok}")
    base_sym, sign_op, disp_str = m.group(1), m.group(2), m.group(3)
    base = shared_syms[base_sym] if base_sym in shared_syms else regs.get(base_sym, 0)
    if disp_str:
        val_disp = int(disp_str.replace(" ", ""), 10)
        disp = -val_disp if sign_op == "-" else val_disp
    else:
        disp = 0
    eff = _s64(base) + disp
    if eff < 0:
        raise ValueError(f"negative effective address {eff} in {addr_tok}")
    return eff


def extract_ptx_entry_body(ptx_text: str, kernel_name: str) -> tuple[list[str], dict[str, int], int]:
    pat = re.compile(
        rf"\.visible\s+\.entry\s+{re.escape(kernel_name)}\s*\((.*?)\)\s*\{{(.*?)\n\}}",
        re.S,
    )
    m = pat.search(ptx_text)
    if not m:
        raise ValueError(f"PTX kernel {kernel_name} not found")
    raw_body = m.group(2)
    shared_syms: dict[str, int] = {}
    shared_total = 0
    stmts: list[str] = []
    elem_bytes = {".b8": 1, ".u16": 2, ".b16": 2, ".u32": 4, ".b32": 4, ".u64": 8, ".b64": 8}
    for raw_line in raw_body.splitlines():
        line = raw_line.split("//", 1)[0].strip()
        if not line:
            continue
        sm = re.match(
            r"^\.shared\s+\.align\s+(\d+)\s+(\.[A-Za-z0-9]+)\s+([A-Za-z0-9_$]+)\[(\d+)\]\s*;$",
            line,
        )
        if sm:
            align = int(sm.group(1))
            ety = sm.group(2)
            sname = sm.group(3)
            cnt = int(sm.group(4))
            if shared_total % align != 0:
                shared_total += align - (shared_total % align)
            shared_syms[sname] = shared_total
            shared_total += cnt * elem_bytes[ety]
            continue
        if line.startswith(".reg ") or line.startswith(".local "):
            continue
        stmts.append(line)
    return stmts, shared_syms, max(shared_total, 1)


def _split_ptx_operands(arg_str: str) -> list[str]:
    out: list[str] = []
    cur: list[str] = []
    depth = 0
    for ch in arg_str:
        if ch in "{[":
            depth += 1
        elif ch in "}]":
            depth -= 1
        if ch == "," and depth == 0:
            out.append("".join(cur).strip())
            cur = []
        else:
            cur.append(ch)
    if cur:
        out.append("".join(cur).strip())
    return out


def simt_execute_ptx_kernel(
    ptx_text: str,
    kernel_name: str,
    params: dict[str, int],
    global_mem: bytearray,
    grid_dim: tuple[int, int, int] = (1, 1, 1),
    block_dim: tuple[int, int, int] = (1, 1, 1),
    step_budget: int = 200_000,
) -> bytearray:
    """Execute a `.visible .entry` PTX kernel across a 3D grid of CTAs with barrier & warp-shuffle sync."""
    raw_stmts, shared_syms, shared_size = extract_ptx_entry_body(ptx_text, kernel_name)
    labels: dict[str, int] = {}
    insns: list[str] = []
    for item in raw_stmts:
        if item.endswith(":"):
            labels[item[:-1].strip()] = len(insns)
        else:
            insns.append(item.rstrip(";").strip())

    gx, gy, gz = grid_dim
    bx, by, bz = block_dim
    n_threads = bx * by * bz

    for cz in range(gz):
        for cy in range(gy):
            for cx in range(gx):
                shared_mem = bytearray(shared_size)
                threads: list[dict[str, Any]] = []
                for tz in range(bz):
                    for ty in range(by):
                        for tx in range(bx):
                            threads.append(
                                {
                                    "pc": 0,
                                    "halted": False,
                                    "regs": {},
                                    "preds": {},
                                    "sregs": {
                                        "%tid.x": tx,
                                        "%tid.y": ty,
                                        "%tid.z": tz,
                                        "%ntid.x": bx,
                                        "%ntid.y": by,
                                        "%ntid.z": bz,
                                        "%ctaid.x": cx,
                                        "%ctaid.y": cy,
                                        "%ctaid.z": cz,
                                        "%nctaid.x": gx,
                                        "%nctaid.y": gy,
                                        "%nctaid.z": gz,
                                    },
                                }
                            )

                steps = 0
                while not all(t["halted"] for t in threads):
                    steps += 1
                    if steps > step_budget:
                        raise RuntimeError(f"PTX SIMT step budget exceeded in {kernel_name}")
                    progressed = False
                    for t in threads:
                        if t["halted"]:
                            continue
                        if t["pc"] >= len(insns):
                            t["halted"] = True
                            progressed = True
                            continue
                        stmt = insns[t["pc"]]
                        guard_ok = True
                        if stmt.startswith("@"):
                            g_tok, stmt = stmt.split(None, 1)
                            neg = g_tok.startswith("@!")
                            preg = g_tok[2:] if neg else g_tok[1:]
                            pval = t["preds"].get(preg, False)
                            guard_ok = (not pval) if neg else pval
                        op_parts = stmt.split(None, 1)
                        op = op_parts[0]
                        arg_str = op_parts[1] if len(op_parts) > 1 else ""

                        if op == "bar.sync":
                            if not guard_ok:
                                t["pc"] += 1
                                progressed = True
                            continue
                        if op.startswith("shfl.sync.bfly"):
                            if not guard_ok:
                                t["pc"] += 1
                                progressed = True
                            continue

                        progressed = True
                        if not guard_ok:
                            t["pc"] += 1
                            continue

                        ops = _split_ptx_operands(arg_str) if arg_str else []
                        regs = t["regs"]
                        preds = t["preds"]
                        sregs = t["sregs"]

                        def val(tok: str) -> int:
                            return _parse_ptx_imm_or_reg(tok, regs, preds, sregs, shared_syms)

                        if op == "ret":
                            t["halted"] = True
                            continue
                        elif op == "bra":
                            t["pc"] = labels[ops[0]]
                            continue
                        elif op.startswith("ld.param."):
                            pname = ops[1].strip()[1:-1].strip()
                            regs[ops[0]] = params[pname] & MASK64
                        elif op.startswith("cvta.to.global."):
                            regs[ops[0]] = val(ops[1]) & MASK64
                        elif op == "mov.b64" and ops[0].startswith("{"):
                            pair = [x.strip() for x in ops[0][1:-1].split(",")]
                            src = val(ops[1]) & MASK64
                            regs[pair[0]] = src & MASK32
                            regs[pair[1]] = (src >> 32) & MASK32
                        elif op == "mov.b64" and ops[1].startswith("{"):
                            pair = [x.strip() for x in ops[1][1:-1].split(",")]
                            lo = val(pair[0]) & MASK32
                            hi = val(pair[1]) & MASK32
                            regs[ops[0]] = lo | (hi << 32)
                        elif op.startswith("mov."):
                            mask = MASK32 if op.endswith("32") else MASK64
                            regs[ops[0]] = val(ops[1]) & mask
                        elif op == "cvt.u64.u32" or op == "cvt.u64.b32":
                            regs[ops[0]] = val(ops[1]) & MASK32
                        elif op == "cvt.u32.u64" or op == "cvt.u32.b64":
                            regs[ops[0]] = val(ops[1]) & MASK32
                        elif op.startswith("ld.global.") or op.startswith("ld.shared."):
                            mem = global_mem if op.startswith("ld.global.") else shared_mem
                            addr = _parse_ptx_addr(ops[1], regs, shared_syms)
                            width = 4 if op.endswith("32") else 8
                            fmt = "<I" if width == 4 else "<Q"
                            regs[ops[0]] = struct.unpack_from(fmt, mem, addr)[0]
                        elif op.startswith("st.global.") or op.startswith("st.shared."):
                            mem = global_mem if op.startswith("st.global.") else shared_mem
                            addr = _parse_ptx_addr(ops[0], regs, shared_syms)
                            width = 4 if op.endswith("32") else 8
                            fmt = "<I" if width == 4 else "<Q"
                            mask = MASK32 if width == 4 else MASK64
                            struct.pack_into(fmt, mem, addr, val(ops[1]) & mask)
                        elif op == "atom.global.add.u64":
                            addr = _parse_ptx_addr(ops[1], regs, shared_syms)
                            old = struct.unpack_from("<Q", global_mem, addr)[0]
                            upd = (old + val(ops[2])) & MASK64
                            struct.pack_into("<Q", global_mem, addr, upd)
                            regs[ops[0]] = old
                        elif op.startswith("add."):
                            if op.endswith(".f64"):
                                fa = struct.unpack("<d", struct.pack("<Q", val(ops[1]) & MASK64))[0]
                                fb = struct.unpack("<d", struct.pack("<Q", val(ops[2]) & MASK64))[0]
                                regs[ops[0]] = struct.unpack("<Q", struct.pack("<d", fa + fb))[0]
                            else:
                                mask = MASK32 if op.endswith("32") else MASK64
                                regs[ops[0]] = (val(ops[1]) + val(ops[2])) & mask
                        elif op.startswith("sub."):
                            mask = MASK32 if op.endswith("32") else MASK64
                            regs[ops[0]] = (val(ops[1]) - val(ops[2])) & mask
                        elif op == "mul.wide.u32":
                            regs[ops[0]] = ((val(ops[1]) & MASK32) * (val(ops[2]) & MASK32)) & MASK64
                        elif op.startswith("mul.lo."):
                            mask = MASK32 if op.endswith("32") else MASK64
                            regs[ops[0]] = (val(ops[1]) * val(ops[2])) & mask
                        elif op.startswith("mul.rn.f64"):
                            fa = struct.unpack("<d", struct.pack("<Q", val(ops[1]) & MASK64))[0]
                            fb = struct.unpack("<d", struct.pack("<Q", val(ops[2]) & MASK64))[0]
                            regs[ops[0]] = struct.unpack("<Q", struct.pack("<d", fa * fb))[0]
                        elif op.startswith("mad.lo."):
                            mask = MASK32 if op.endswith("32") else MASK64
                            regs[ops[0]] = ((val(ops[1]) & mask) * (val(ops[2]) & mask) + (val(ops[3]) & mask)) & mask
                        elif op == "mad.wide.u32":
                            prod = (val(ops[1]) & MASK32) * (val(ops[2]) & MASK32)
                            regs[ops[0]] = (prod + (val(ops[3]) & MASK64)) & MASK64
                        elif op.startswith("div.u64"):
                            d = val(ops[2]) & MASK64
                            if d == 0:
                                raise ZeroDivisionError("PTX div.u64 by zero")
                            regs[ops[0]] = (val(ops[1]) & MASK64) // d
                        elif op.startswith("rem.u64"):
                            d = val(ops[2]) & MASK64
                            if d == 0:
                                raise ZeroDivisionError("PTX rem.u64 by zero")
                            regs[ops[0]] = (val(ops[1]) & MASK64) % d
                        elif op.startswith("and."):
                            if op == "and.pred":
                                preds[ops[0]] = bool(val(ops[1])) and bool(val(ops[2]))
                            else:
                                mask = MASK32 if op.endswith("32") else MASK64
                                regs[ops[0]] = (val(ops[1]) & val(ops[2])) & mask
                        elif op.startswith("or."):
                            if op == "or.pred":
                                preds[ops[0]] = bool(val(ops[1])) or bool(val(ops[2]))
                            else:
                                mask = MASK32 if op.endswith("32") else MASK64
                                regs[ops[0]] = (val(ops[1]) | val(ops[2])) & mask
                        elif op.startswith("xor."):
                            if op == "xor.pred":
                                preds[ops[0]] = bool(val(ops[1])) != bool(val(ops[2]))
                            else:
                                mask = MASK32 if op.endswith("32") else MASK64
                                regs[ops[0]] = (val(ops[1]) ^ val(ops[2])) & mask
                        elif op.startswith("not."):
                            if op == "not.pred":
                                preds[ops[0]] = not bool(val(ops[1]))
                            else:
                                mask = MASK32 if op.endswith("32") else MASK64
                                regs[ops[0]] = (~val(ops[1])) & mask
                        elif op.startswith("neg.s64"):
                            regs[ops[0]] = (-_s64(val(ops[1]))) & MASK64
                        elif op.startswith("shl."):
                            is32 = op.endswith("32")
                            sh = val(ops[2]) & MASK32
                            if is32:
                                regs[ops[0]] = 0 if sh >= 32 else ((val(ops[1]) & MASK32) << sh) & MASK32
                            else:
                                regs[ops[0]] = 0 if sh >= 64 else ((val(ops[1]) & MASK64) << sh) & MASK64
                        elif op.startswith("shr."):
                            sh = val(ops[2]) & MASK32
                            if op == "shr.s64":
                                a_s = _s64(val(ops[1]))
                                regs[ops[0]] = ((a_s >> 63) if sh >= 64 else (a_s >> sh)) & MASK64
                            elif op.endswith("32"):
                                regs[ops[0]] = 0 if sh >= 32 else ((val(ops[1]) & MASK32) >> sh)
                            else:
                                regs[ops[0]] = 0 if sh >= 64 else ((val(ops[1]) & MASK64) >> sh)
                        elif op == "clz.b64":
                            v = val(ops[1]) & MASK64
                            regs[ops[0]] = 64 if v == 0 else (64 - v.bit_length())
                        elif op.startswith("setp."):
                            parts = op.split(".")
                            cmp_op, ty_op = parts[1], parts[2]
                            if ty_op in ("u64", "b64"):
                                a_v, b_v = val(ops[1]) & MASK64, val(ops[2]) & MASK64
                            elif ty_op in ("u32", "b32"):
                                a_v, b_v = val(ops[1]) & MASK32, val(ops[2]) & MASK32
                            elif ty_op == "s64":
                                a_v, b_v = _s64(val(ops[1])), _s64(val(ops[2]))
                            elif ty_op == "s32":
                                a_v, b_v = _s32(val(ops[1])), _s32(val(ops[2]))
                            else:
                                raise ValueError(f"unsupported setp type: {op}")
                            cmp_map = {
                                "eq": a_v == b_v,
                                "ne": a_v != b_v,
                                "lt": a_v < b_v,
                                "le": a_v <= b_v,
                                "gt": a_v > b_v,
                                "ge": a_v >= b_v,
                            }
                            preds[ops[0]] = cmp_map[cmp_op]
                        elif op.startswith("selp."):
                            mask = MASK32 if op.endswith("32") else MASK64
                            cond = preds.get(ops[3], False)
                            regs[ops[0]] = (val(ops[1]) if cond else val(ops[2])) & mask
                        else:
                            raise ValueError(f"unsupported PTX instruction in SIMT runner: {stmt}")
                        t["pc"] += 1

                    if progressed:
                        continue

                    # Check warp-synchronous `shfl.sync.bfly.b32`
                    did_shfl = False
                    for w_start in range(0, n_threads, 32):
                        warp = threads[w_start : w_start + 32]
                        active_warp = [t for t in warp if not t["halted"]]
                        if active_warp and all(
                            insns[t["pc"]].split()[0].startswith("shfl.sync.bfly")
                            or (
                                insns[t["pc"]].startswith("@")
                                and insns[t["pc"]].split(None, 1)[1].split()[0].startswith("shfl.sync.bfly")
                            )
                            for t in active_warp
                        ):
                            src_vals: list[int] = []
                            parsed_ops: list[list[str]] = []
                            for lane_idx, t in enumerate(warp):
                                if t["halted"]:
                                    src_vals.append(0)
                                    parsed_ops.append([])
                                    continue
                                st = insns[t["pc"]]
                                if st.startswith("@"):
                                    _, st = st.split(None, 1)
                                ops = _split_ptx_operands(st.split(None, 1)[1])
                                parsed_ops.append(ops)
                                src_vals.append(
                                    _parse_ptx_imm_or_reg(
                                        ops[1], t["regs"], t["preds"], t["sregs"], shared_syms
                                    )
                                    & MASK32
                                )
                            for lane_idx, t in enumerate(warp):
                                if t["halted"]:
                                    continue
                                ops = parsed_ops[lane_idx]
                                mask_x = _parse_ptx_imm_or_reg(
                                    ops[2], t["regs"], t["preds"], t["sregs"], shared_syms
                                ) & 31
                                partner = lane_idx ^ mask_x
                                t["regs"][ops[0]] = src_vals[partner] if partner < len(src_vals) else src_vals[lane_idx]
                                t["pc"] += 1
                            did_shfl = True
                            break
                    if did_shfl:
                        continue

                    # Otherwise synchronize CTA barrier (`bar.sync`)
                    if all((not t["halted"]) and insns[t["pc"]].split()[0] == "bar.sync" for t in threads):
                        for t in threads:
                            t["pc"] += 1
                    else:
                        pcs = [(i, t["halted"], insns[t["pc"]] if not t["halted"] else "HALT") for i, t in enumerate(threads[:8])]
                        raise RuntimeError(f"Barrier divergence / deadlock in {kernel_name}: {pcs}")
    return global_mem


def run_ptx_1d_vector(ptx_text: str, kernel_name: str, arity: int, inputs: list[list[int]]) -> list[int]:
    n = len(inputs[0]) if inputs else 0
    total_words = (arity + 1) * n
    gmem = bytearray(max(8, total_words * 8))
    params: dict[str, int] = {"param_n": n, "param_out": arity * n * 8}
    for j in range(arity):
        params[f"param_in{j}"] = j * n * 8
        for i, w in enumerate(inputs[j]):
            struct.pack_into("<Q", gmem, (j * n + i) * 8, w & MASK64)
    block_x = 8
    grid_x = max(1, (n + block_x - 1) // block_x)
    simt_execute_ptx_kernel(
        ptx_text,
        kernel_name,
        params=params,
        global_mem=gmem,
        grid_dim=(grid_x, 1, 1),
        block_dim=(block_x, 1, 1),
    )
    out_base = arity * n * 8
    return [struct.unpack_from("<Q", gmem, out_base + i * 8)[0] for i in range(n)]


# ---------------------------------------------------------------------------
# 2. Official OpenXLA StableHLO `eval_module` Differential Execution
# ---------------------------------------------------------------------------


def verify_stablehlo_mlir_module(mlir_text: str) -> None:
    from mlir import ir
    from mlir.dialects import stablehlo

    with ir.Context() as ctx:
        stablehlo.register_dialect(ctx)
        mod = ir.Module.parse(mlir_text)
        if not mod.operation.verify():
            raise RuntimeError("OpenXLA MLIR verifier rejected StableHLO module")


def eval_stablehlo_with_openxla(mlir_text: str, args_spec: list[dict[str, Any]]) -> tuple[list[int], str, list[int]]:
    import numpy as np
    from mlir import ir
    from mlir.dialects import stablehlo

    def to_dense_attr(spec: dict[str, Any]) -> Any:
        shape = tuple(spec["shape"])
        elem = spec["elem"]
        words = spec["words"]
        if elem == "ui64":
            arr = np.array(words, dtype=np.uint64).reshape(shape)
            return ir.DenseElementsAttr.get(arr, type=ir.IntegerType.get_unsigned(64))
        elif elem == "i64":
            signed_vals = [_s64(w) for w in words]
            arr = np.array(signed_vals, dtype=np.int64).reshape(shape)
            return ir.DenseElementsAttr.get(arr, type=ir.IntegerType.get_signless(64))
        elif elem == "ui32":
            arr = np.array([w & MASK32 for w in words], dtype=np.uint32).reshape(shape)
            return ir.DenseElementsAttr.get(arr, type=ir.IntegerType.get_unsigned(32))
        elif elem == "i32":
            arr = np.array([_s32(w) for w in words], dtype=np.int32).reshape(shape)
            return ir.DenseElementsAttr.get(arr, type=ir.IntegerType.get_signless(32))
        elif elem == "i1":
            arr = np.array([bool(w & 1) for w in words], dtype=np.bool_).reshape(shape)
            return ir.DenseElementsAttr.get(arr, type=ir.IntegerType.get_signless(1))
        else:
            raise ValueError(f"Unsupported StableHLO differential element type: {elem}")

    with ir.Context() as ctx:
        stablehlo.register_dialect(ctx)
        mod = ir.Module.parse(mlir_text)
        if not mod.operation.verify():
            raise RuntimeError("StableHLO module failed MLIR verification")
        dense_args = [to_dense_attr(a) for a in args_spec]
        outs = stablehlo.eval_module(mod, dense_args)
        if len(outs) != 1:
            raise RuntimeError(f"Expected 1 result from eval_module, got {len(outs)}")
        res_attr = ir.DenseElementsAttr(outs[0])
        res_ty = ir.RankedTensorType(res_attr.type)
        out_shape = list(res_ty.shape)
        et_str = str(res_ty.element_type)
        arr = np.array(res_attr)
        if et_str == "i1":
            flat_words = [1 if bool(x) else 0 for x in arr.reshape(-1)]
        elif et_str.startswith("ui"):
            flat_words = [int(x) & MASK64 for x in arr.view(np.uint64).reshape(-1)] if arr.itemsize == 8 else [int(x) & MASK32 for x in arr.reshape(-1)]
        elif et_str == "i64":
            flat_words = [int(x) & MASK64 for x in arr.astype(np.int64).reshape(-1)]
        else:
            flat_words = [int(x) & MASK64 for x in arr.reshape(-1)]
        return out_shape, et_str, flat_words


def _eval_stablehlo_isolated(
    mlir_text: str,
    args_spec: list[dict[str, Any]],
    tools_cache_dir: Path,
) -> tuple[int, tuple[list[int], str, list[int]] | None]:
    """Run `eval_stablehlo_with_openxla` in a child process so C++ `llvm::APInt`
    assertions (e.g., unguarded division-by-zero mutant `H3` hitting `SIGABRT`)
    are cleanly caught as non-zero return codes instead of aborting the harness."""
    code = (
        "import json, sys\n"
        "from pathlib import Path\n"
        f"sys.path.insert(0, {repr(str(Path(__file__).resolve().parent))})\n"
        "import run_gpu_tpu_diff as rgt\n"
        "req = json.loads(sys.stdin.read())\n"
        "rgt.ensure_openxla_stablehlo(Path(req['cache']))\n"
        "out = rgt.eval_stablehlo_with_openxla(req['mlir'], req['args'])\n"
        "print(json.dumps({'ok': list(out)}))\n"
    )
    proc = subprocess.run(
        [sys.executable, "-c", code],
        input=json.dumps({"cache": str(tools_cache_dir), "mlir": mlir_text, "args": args_spec}),
        capture_output=True,
        text=True,
        timeout=60,
    )
    if proc.returncode != 0:
        return proc.returncode, None
    for ln in reversed(proc.stdout.splitlines()):
        ln = ln.strip()
        if ln.startswith("{"):
            data = json.loads(ln)["ok"]
            return 0, (list(data[0]), str(data[1]), [int(x) for x in data[2]])
    return 1, None


# ---------------------------------------------------------------------------
# 3. Apple Metal MSL 3.0 Host C++17 Execution (`clang++` + ASan/UBSan)
# ---------------------------------------------------------------------------

METAL_CXX17_SHIM = r"""
#include <cstdint>
#include <cstring>
#include <cmath>
#include <atomic>
#include <type_traits>
#include <cstdio>
#include <vector>

namespace metal {
using uchar = uint8_t;
using ushort = uint16_t;
using uint = uint32_t;
using ulong = uint64_t;
using half = _Float16;

struct uint2 {
    uint x, y;
    constexpr uint2() : x(0), y(0) {}
    constexpr uint2(uint v) : x(v), y(v) {}
    constexpr uint2(uint x_, uint y_) : x(x_), y(y_) {}
};

struct ulong2 {
    ulong x, y;
    constexpr ulong2() : x(0), y(0) {}
    constexpr ulong2(ulong v) : x(v), y(v) {}
    constexpr ulong2(ulong x_, ulong y_) : x(x_), y(y_) {}
    constexpr ulong2 operator^(const ulong2& o) const { return ulong2(x ^ o.x, y ^ o.y); }
};

struct uint4 {
    uint x, y, z, w;
    constexpr uint4() : x(0), y(0), z(0), w(0) {}
    constexpr uint4(uint v) : x(v), y(v), z(v), w(v) {}
    constexpr uint4(uint x_, uint y_, uint z_, uint w_) : x(x_), y(y_), z(z_), w(w_) {}
    constexpr uint4 operator^(const uint4& o) const { return uint4(x ^ o.x, y ^ o.y, z ^ o.z, w ^ o.w); }
    uint4& operator^=(const uint4& o) { x ^= o.x; y ^= o.y; z ^= o.z; w ^= o.w; return *this; }
};

enum class mem_flags { mem_none = 0, mem_device = 1, mem_threadgroup = 2 };
static constexpr std::memory_order memory_order_relaxed = std::memory_order_relaxed;
using atomic_uint = std::atomic<uint>;
using atomic_ulong = std::atomic<ulong>;

inline uint atomic_fetch_add_explicit(atomic_uint* obj, uint val, std::memory_order order) {
    return obj->fetch_add(val, order);
}
inline uint atomic_exchange_explicit(atomic_uint* obj, uint val, std::memory_order order) {
    return obj->exchange(val, order);
}
inline void threadgroup_barrier(mem_flags) {}

template <typename Dst, typename Src>
inline Dst as_type(Src s) {
    static_assert(sizeof(Dst) == sizeof(Src), "as_type size mismatch");
    Dst d;
    std::memcpy(&d, &s, sizeof(Dst));
    return d;
}

inline uint clz(uint x) { return x == 0 ? 32u : (uint)__builtin_clz(x); }
inline ulong clz(ulong x) { return x == 0 ? 64UL : (ulong)__builtin_clzll(x); }

template <typename T>
inline T select(T fval, T tval, bool cond) { return cond ? tval : fval; }

inline half fma(half a, half b, half c) {
    return (half)std::fma((float)a, (float)b, (float)c);
}
inline float fma(float a, float b, float c) { return std::fma(a, b, c); }
inline double fma(double a, double b, double c) { return std::fma(a, b, c); }

// Single-lane host fallback for static compilation of multi-lane reductions
inline ulong simd_shuffle_xor(ulong val, uint) { return val; }
inline ulong simd_sum(ulong val) { return val; }
} // namespace metal

#define kernel
#define device
#define constant const
#define threadgroup
#define thread
"""


def translate_msl_to_cxx17(msl_text: str) -> str:
    src = msl_text.replace("#include <metal_stdlib>", METAL_CXX17_SHIM)
    src = re.sub(r"\[\[[A-Za-z0-9_()\s]+\]\]", "", src)
    return src


def compile_and_check_metal_module(clangxx: str, msl_text: str, extra_main_cpp: str) -> tuple[int, str, str]:
    cpp_src = translate_msl_to_cxx17(msl_text) + "\n" + extra_main_cpp
    with tempfile.TemporaryDirectory(prefix="ln-msl-") as tmp:
        cpp_path = Path(tmp) / "kernel.cpp"
        bin_path = Path(tmp) / "kernel_runner"
        cpp_path.write_text(cpp_src, encoding="utf-8")
        comp = subprocess.run(
            [
                clangxx,
                "-std=c++17",
                "-O1",
                "-Wall",
                "-Wextra",
                "-Wno-unused-parameter",
                "-Wno-unused-variable",
                "-fsanitize=address,undefined",
                "-fno-sanitize-recover=all",
                str(cpp_path),
                "-o",
                str(bin_path),
            ],
            capture_output=True,
            text=True,
            timeout=60,
        )
        if comp.returncode != 0:
            return comp.returncode, comp.stdout, comp.stderr
        env = os.environ.copy()
        env["UBSAN_OPTIONS"] = "halt_on_error=1:print_stacktrace=1"
        env["ASAN_OPTIONS"] = "detect_leaks=0:halt_on_error=1"
        run = subprocess.run(
            [str(bin_path)],
            capture_output=True,
            text=True,
            timeout=60,
            env=env,
        )
        return run.returncode, run.stdout, run.stderr


def run_metal_1d_case_vectors(
    clangxx: str,
    msl_text: str,
    kernel_name: str,
    arity: int,
    vectors: list[dict[str, Any]],
) -> tuple[int, list[list[int]], str]:
    """Compile a lowered Metal 1D kernel once for all test vectors and execute over an over-provisioned grid."""
    lines = ["int main() {"]
    for vi, vec in enumerate(vectors):
        ins: list[list[int]] = vec["inputs"]
        n = len(ins[0]) if ins else 0
        for j in range(arity):
            init_vals = ", ".join(f"{w & MASK64}ULL" for w in ins[j])
            lines.append(f"  std::vector<metal::ulong> in_{vi}_{j} = {{{init_vals}}};")
        lines.append(f"  std::vector<metal::ulong> out_{vi}({max(1, n)}, 0ULL);")
        lines.append(f"  const metal::ulong len_{vi} = {n}ULL;")
        # Launch n + 3 threads to exercise the `gid < n` SIMT guard under ASan!
        call_args = [f"in_{vi}_{j}.data()" for j in range(arity)] + [f"out_{vi}.data()", f"len_{vi}", "gid"]
        lines.append(f"  for (metal::uint gid = 0; gid < {n + 3}u; ++gid) {{")
        lines.append(f"    {kernel_name}({', '.join(call_args)});")
        lines.append("  }")
        lines.append(f'  std::printf("VEC {vi}:");')
        lines.append(f"  for (size_t i = 0; i < {n}; ++i) std::printf(\" %llu\", (unsigned long long)out_{vi}[i]);")
        lines.append('  std::printf("\\n");')
    lines.append("  return 0;\n}")
    rc, stdout, stderr = compile_and_check_metal_module(clangxx, msl_text, "\n".join(lines))
    if rc != 0:
        return rc, [], stderr
    results: list[list[int]] = []
    for line in stdout.strip().splitlines():
        if line.startswith("VEC "):
            _, rest = line.split(":", 1)
            toks = rest.strip().split()
            results.append([int(x) for x in toks])
    return 0, results, stderr


# ---------------------------------------------------------------------------
# 4. End-to-End Suite Execution & Self-Tests
# ---------------------------------------------------------------------------


def run_production_ptx_checks(ptxas_bin: str, prod_ptx: str) -> dict[str, Any]:
    rc, log = compile_ptx_with_ptxas(ptxas_bin, prod_ptx, arch="sm_90")
    if rc != 0:
        raise RuntimeError(f"Production emitPTXModule failed ptxas -Werror:\n{log}")

    # Negative assembler gate: verify `ptxas -Werror` rejects a register-width mismatch mutant.
    bad_ptx = prod_ptx.replace("add.u64      %rd7, %rd5, %rd6;", "add.u64      %r1, %rd5, %rd6;", 1)
    assert bad_ptx != prod_ptx, "expected production PTX pattern for negative ptxas test"
    bad_rc, _ = compile_ptx_with_ptxas(ptxas_bin, bad_ptx, arch="sm_90")
    if bad_rc == 0:
        raise RuntimeError("ptxas -Werror unexpectedly accepted ill-typed PTX register mutant")

    # Execute 2D shared-memory `lean_native_kernel_matmul_tiled_u64` (16x16 CTA with bar.sync)
    dim = 16
    mat_a = [(i * 3 + j + 1) for i in range(dim) for j in range(dim)]
    mat_b = [(i + j * 5 + 2) for i in range(dim) for j in range(dim)]
    expected_c = [
        sum(mat_a[r * dim + k] * mat_b[k * dim + c] for k in range(dim)) & MASK64
        for r in range(dim)
        for c in range(dim)
    ]
    n_bytes = dim * dim * 8
    gmem = bytearray(n_bytes * 3)
    for idx, v in enumerate(mat_a):
        struct.pack_into("<Q", gmem, n_bytes + idx * 8, v)
    for idx, v in enumerate(mat_b):
        struct.pack_into("<Q", gmem, 2 * n_bytes + idx * 8, v)
    simt_execute_ptx_kernel(
        prod_ptx,
        "lean_native_kernel_matmul_tiled_u64",
        params={"param_c": 0, "param_a": n_bytes, "param_b": 2 * n_bytes, "param_dim": dim},
        global_mem=gmem,
        grid_dim=(1, 1, 1),
        block_dim=(16, 16, 1),
        step_budget=500_000,
    )
    got_c = [struct.unpack_from("<Q", gmem, idx * 8)[0] for idx in range(dim * dim)]
    if got_c != expected_c:
        raise RuntimeError("SIMT execution of lean_native_kernel_matmul_tiled_u64 diverged from reference matmul")

    # Execute warp-shuffle + shared-memory + atom.global.add `lean_native_kernel_dot_reduce_u64` (256 threads)
    n_dot = 300
    vec_x = [(i * 7 + 3) for i in range(n_dot)]
    vec_y = [(i * 11 + 5) for i in range(n_dot)]
    exp_dot = sum(x * y for x, y in zip(vec_x, vec_y)) & MASK64
    dot_mem = bytearray(8 + 2 * n_dot * 8)
    for i, x in enumerate(vec_x):
        struct.pack_into("<Q", dot_mem, 8 + i * 8, x)
    for i, y in enumerate(vec_y):
        struct.pack_into("<Q", dot_mem, 8 + (n_dot + i) * 8, y)
    simt_execute_ptx_kernel(
        prod_ptx,
        "lean_native_kernel_dot_reduce_u64",
        params={"param_out": 0, "param_in0": 8, "param_in1": 8 + n_dot * 8, "param_n": n_dot},
        global_mem=dot_mem,
        grid_dim=(2, 1, 1),
        block_dim=(256, 1, 1),
        step_budget=800_000,
    )
    got_dot = struct.unpack_from("<Q", dot_mem, 0)[0]
    if got_dot != exp_dot:
        raise RuntimeError(f"SIMT execution of dot_reduce_u64 diverged: got {got_dot}, expected {exp_dot}")

    return {"matmul16x16Verified": True, "dotReduce256Verified": True}


def run_production_metal_checks(clangxx: str, prod_metal: str, prod_fastcheck: str) -> dict[str, Any]:
    harness = r"""
int main() {
    // 1. Verify 256-bit carry/borrow and 64x64->128 carryless polynomial multiplication
    ln_u256 a = { 0xffffffffffffffffULL, 0xffffffffffffffffULL, 0ULL, 1ULL };
    ln_u256 b = { 1ULL, 0ULL, 0ULL, 2ULL };
    ln_u256 s = ln_u256_add(a, b);
    if (s.l0 != 0ULL || s.l1 != 0ULL || s.l2 != 1ULL || s.l3 != 3ULL) return 2;
    ln_u256 d = ln_u256_sub(s, b);
    if (d.l0 != a.l0 || d.l1 != a.l1 || d.l2 != a.l2 || d.l3 != a.l3) return 3;
    if (ln_clmul64(0x87ULL, 0x87ULL) != (0x87ULL ^ (0x87ULL << 1) ^ (0x87ULL << 2) ^ (0x87ULL << 7))) return 4;

    // 2. Execute SNARK F_{2^128} butterfly kernel over 4 lanes
    metal::ulong2 top[4] = { {1, 2}, {3, 4}, {5, 6}, {7, 8} };
    metal::ulong2 bot[4] = { {9, 10}, {11, 12}, {13, 14}, {15, 16} };
    const metal::ulong2 tw_ident = { 1ULL, 0ULL };
    for (metal::uint gid = 0; gid < 6u; ++gid) {
        lean_native_kernel_ntt_butterfly_f128(top, bot, tw_ident, 4ULL, gid);
    }
    // For gid=0, tw=(1,0) is multiplicative identity in F_{2^128}: p = bot[0] = (9,10),
    // top'[0] = (1^9, 2^10) = (8, 8), bot'[0] = (8^9, 8^10) = (1, 2).
    if (top[0].x != 8ULL || top[0].y != 8ULL || bot[0].x != 1ULL || bot[0].y != 2ULL) return 5;

    // 3. Execute BLAKE3 Merkle parent compression kernel
    metal::uint children[16];
    for (metal::uint i = 0; i < 16u; ++i) children[i] = i + 1u;
    metal::uint parents[8] = {0};
    lean_native_kernel_blake3_merkle_parents(children, parents, 1u, 0u);
    bool any_nz = false;
    for (int i = 0; i < 8; ++i) if (parents[i] != 0u) any_nz = true;
    if (!any_nz) return 6;
    return 0;
}
"""
    rc, _, err = compile_and_check_metal_module(clangxx, prod_metal, harness)
    if rc != 0:
        raise RuntimeError(f"Production emitMetalModule ASan/UBSan check failed (rc={rc}):\n{err}")

    fc_harness = r"""
int main() {
    metal::ulong seed = 0x123456789abcdef0ULL;
    metal::ulong rounds = 8ULL;
    metal::atomic_uint sat_cnt(0u);
    metal::atomic_uint cex_flag(0u);
    ln_u256 witness[2] = {};
    for (metal::uint gid = 0; gid < 4u; ++gid) {
        lean_native_fastcheck_metal_kernel(seed, rounds, &sat_cnt, &cex_flag, witness, gid);
    }
    return (sat_cnt.load() == 32u) ? 0 : 7;
}
"""
    fc_rc, _, fc_err = compile_and_check_metal_module(clangxx, prod_fastcheck, fc_harness)
    if fc_rc != 0:
        raise RuntimeError(f"Production emitFastCheckMetal ASan/UBSan check failed (rc={fc_rc}):\n{fc_err}")

    return {"u256ClmulSnarkBlake3Verified": True, "fastCheckMetalVerified": True}


def run_m6_mlir_mutant_check(prod_tpu_mlir: str) -> None:
    """Verify OpenXLA `eval_module` executes an extracted TPU v6e vector op and rejects M6 shift swap."""
    fn_mlir = """
module @m6_probe {
  func.func @shl_probe(%a: tensor<2xui64>, %b: tensor<2xui64>) -> tensor<2xui64> {
    %0 = stablehlo.shift_left %a, %b : tensor<2xui64>
    return %0 : tensor<2xui64>
  }
}
"""
    args = [
        {"shape": [2], "elem": "ui64", "words": [3, 8]},
        {"shape": [2], "elem": "ui64", "words": [2, 1]},
    ]
    _, _, pos_words = eval_stablehlo_with_openxla(fn_mlir, args)
    if pos_words != [12, 16]:
        raise RuntimeError(f"Unexpected shl_probe output: {pos_words}")
    m6_mlir = fn_mlir.replace("stablehlo.shift_left", "stablehlo.shift_right_logical")
    _, _, neg_words = eval_stablehlo_with_openxla(m6_mlir, args)
    if neg_words == pos_words:
        raise RuntimeError("M6 shift swap mutant was not killed by OpenXLA eval_module")
    verify_stablehlo_mlir_module(prod_tpu_mlir)


def run_suite_from_payload(
    payload: dict[str, Any],
    ptxas_bin: str,
    clangxx: str,
    tools_cache_dir: Path,
) -> dict[str, Any]:
    prod = payload["productionModules"]
    ptx_prod_summary = run_production_ptx_checks(ptxas_bin, prod["ptxModule"])
    run_m6_mlir_mutant_check(prod["stablehloTpuModule"])
    metal_prod_summary = run_production_metal_checks(clangxx, prod["metalModule"], prod["metalFastCheckModule"])

    ptx_vectors_checked = 0
    ptx_mutants_killed = 0
    for case in payload["ptxCases"]:
        cid = case["id"]
        kname = case["kernelName"]
        arity = case["arity"]
        ptx_text = case["ptxText"]
        rc, log = compile_ptx_with_ptxas(ptxas_bin, ptx_text, arch="sm_90")
        if rc != 0:
            raise RuntimeError(f"[PTX:{cid}] ptxas -Werror failed:\n{log}")
        for vec in case["vectors"]:
            got = run_ptx_1d_vector(ptx_text, kname, arity, vec["inputs"])
            if got != vec["expected"]:
                raise RuntimeError(f"[PTX:{cid}] SIMT mismatch: got {got}, expected {vec['expected']}")
            ptx_vectors_checked += 1
        if "negativeMutantPtx" in case:
            mut_ptx = case["negativeMutantPtx"]
            mut_rc, _ = compile_ptx_with_ptxas(ptxas_bin, mut_ptx, arch="sm_90")
            diverged = mut_rc != 0
            if not diverged:
                for vec in case["vectors"]:
                    try:
                        mgot = run_ptx_1d_vector(mut_ptx, kname, arity, vec["inputs"])
                    except Exception:
                        diverged = True
                        break
                    if mgot != vec["expected"]:
                        diverged = True
                        break
            if not diverged:
                raise RuntimeError(f"[PTX:{cid}] Negative mutant ({case.get('negativeMutantReason')}) was NOT killed!")
            ptx_mutants_killed += 1

    hlo_vectors_checked = 0
    hlo_mutants_killed = 0
    for case in payload["stablehloCases"]:
        cid = case["id"]
        mlir_text = case["mlirText"]
        for vec in case["vectors"]:
            exp = vec["expected"]
            got_shape, _, got_words = eval_stablehlo_with_openxla(mlir_text, vec["args"])
            if got_shape != exp["shape"] or got_words != exp["words"]:
                raise RuntimeError(
                    f"[StableHLO:{cid}] OpenXLA eval_module mismatch: got ({got_shape}, {got_words}) "
                    f"vs expected ({exp['shape']}, {exp['words']})"
                )
            hlo_vectors_checked += 1
        if "negativeMutantMlir" in case:
            mut_mlir = case["negativeMutantMlir"]
            diverged = False
            for vec in case["vectors"]:
                exp = vec["expected"]
                rc_m, m_out = _eval_stablehlo_isolated(mut_mlir, vec["args"], tools_cache_dir)
                if rc_m != 0 or m_out is None:
                    diverged = True
                    break
                m_shape, _, m_words = m_out
                if m_shape != exp["shape"] or m_words != exp["words"]:
                    diverged = True
                    break
            if not diverged:
                raise RuntimeError(
                    f"[StableHLO:{cid}] Negative mutant ({case.get('negativeMutantReason')}) was NOT killed!"
                )
            hlo_mutants_killed += 1

    metal_vectors_checked = 0
    metal_mutants_killed = 0
    for case in payload["metalCases"]:
        cid = case["id"]
        kname = case["kernelName"]
        arity = case["arity"]
        msl_text = case["mslText"]
        vecs = case["vectors"]
        rc, outs, err = run_metal_1d_case_vectors(clangxx, msl_text, kname, arity, vecs)
        if rc != 0:
            raise RuntimeError(f"[Metal:{cid}] clang++ ASan/UBSan execution failed (rc={rc}):\n{err}")
        for vec, got in zip(vecs, outs):
            if got != vec["expected"]:
                raise RuntimeError(f"[Metal:{cid}] Metal host mismatch: got {got}, expected {vec['expected']}")
            metal_vectors_checked += 1
        if "negativeMutantMsl" in case:
            mut_msl = case["negativeMutantMsl"]
            m_rc, m_outs, _ = run_metal_1d_case_vectors(clangxx, mut_msl, kname, arity, vecs)
            diverged = m_rc != 0 or any(g != v["expected"] for v, g in zip(vecs, m_outs))
            if not diverged:
                raise RuntimeError(
                    f"[Metal:{cid}] Negative mutant ({case.get('negativeMutantReason')}) was NOT killed!"
                )
            metal_mutants_killed += 1

    return {
        "ok": True,
        "ptxCases": len(payload["ptxCases"]),
        "ptxVectorsChecked": ptx_vectors_checked,
        "ptxMutantsKilled": ptx_mutants_killed,
        "stablehloCases": len(payload["stablehloCases"]),
        "stablehloVectorsChecked": hlo_vectors_checked,
        "stablehloMutantsKilled": hlo_mutants_killed + 1,  # +1 for M6 shift swap probe
        "metalCases": len(payload["metalCases"]),
        "metalVectorsChecked": metal_vectors_checked,
        "metalMutantsKilled": metal_mutants_killed,
        "productionChecks": {**ptx_prod_summary, **metal_prod_summary, "tpuV6eModuleVerified": True},
    }


class GPUDiffRunnerSelfTests(unittest.TestCase):
    def test_ptx_simt_and_mutant_detection(self) -> None:
        ptx = """.version 8.0
.target sm_90
.address_size 64

.visible .entry k_sub(
    .param .u64 param_out,
    .param .u64 param_in0,
    .param .u64 param_in1,
    .param .u64 param_n
)
{
    .reg .pred %p<2>;
    .reg .b32 %r<3>;
    .reg .b64 %rd<10>;
    ld.param.u64 %rd0, [param_out];
    ld.param.u64 %rd3, [param_n];
    mov.u32 %r0, %ctaid.x;
    mov.u32 %r1, %ntid.x;
    mov.u32 %r2, %tid.x;
    mul.wide.u32 %rd1, %r0, %r1;
    cvt.u64.u32 %rd2, %r2;
    add.u64 %rd2, %rd1, %rd2;
    setp.ge.u64 %p0, %rd2, %rd3;
    @%p0 bra $L_done;
    cvta.to.global.u64 %rd4, %rd0;
    shl.b64 %rd5, %rd2, 3;
    add.u64 %rd6, %rd4, %rd5;
    ld.param.u64 %rd7, [param_in0];
    cvta.to.global.u64 %rd7, %rd7;
    add.u64 %rd7, %rd7, %rd5;
    ld.global.u64 %rd7, [%rd7];
    ld.param.u64 %rd8, [param_in1];
    cvta.to.global.u64 %rd8, %rd8;
    add.u64 %rd8, %rd8, %rd5;
    ld.global.u64 %rd8, [%rd8];
    sub.u64 %rd9, %rd7, %rd8;
    st.global.u64 [%rd6], %rd9;
$L_done:
    ret;
}
"""
        out = run_ptx_1d_vector(ptx, "k_sub", 2, [[10, 1], [3, 2]])
        self.assertEqual(out, [7, MASK64])
        mut = ptx.replace("sub.u64 %rd9, %rd7, %rd8;", "sub.u64 %rd9, %rd8, %rd7;")
        self.assertNotEqual(run_ptx_1d_vector(mut, "k_sub", 2, [[10, 1], [3, 2]]), out)

    def test_metal_cxx17_ubsan_catches_div_zero(self) -> None:
        clangxx = find_clangxx()
        if clangxx is None:
            self.skipTest("clang++ not installed")
        msl = """#include <metal_stdlib>
using namespace metal;
kernel void k_div(
    device const ulong* in0 [[buffer(0)]],
    device const ulong* in1 [[buffer(1)]],
    device ulong* out [[buffer(2)]],
    constant ulong& n [[buffer(3)]],
    uint gid [[thread_position_in_grid]]
) {
    if ((ulong)gid < n) {
        out[(ulong)gid] = (in1[(ulong)gid] == 0UL) ? 0UL : (in0[(ulong)gid] / in1[(ulong)gid]);
    }
}
"""
        vecs = [{"inputs": [[18, 7], [3, 0]], "expected": [6, 0]}]
        rc, outs, err = run_metal_1d_case_vectors(clangxx, msl, "k_div", 2, vecs)
        self.assertEqual(rc, 0, err)
        self.assertEqual(outs, [[6, 0]])
        bad_msl = msl.replace("(in1[(ulong)gid] == 0UL) ? 0UL : (in0[(ulong)gid] / in1[(ulong)gid])", "in0[(ulong)gid] / in1[(ulong)gid]")
        bad_rc, _, _ = run_metal_1d_case_vectors(clangxx, bad_msl, "k_div", 2, vecs)
        self.assertNotEqual(bad_rc, 0, "UBSan must trap on unguarded Metal division by zero")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--core-bin", type=Path, default=ROOT_DIR / "lean" / ".lake" / "build" / "bin" / "lean-native-core")
    ap.add_argument("--fixtures-json", type=Path, default=None, help="Pre-generated `gpu-tpu-diff-suite` JSON")
    ap.add_argument("--tools-cache-dir", type=Path, default=Path(os.environ.get("GPU_TPU_TOOLS_CACHE", "/tmp/tl-gpu-tpu-tools")))
    ap.add_argument("--ensure-tools", action="store_true", help="Bootstrap ptxas + OpenXLA stablehlo wheels if missing")
    ap.add_argument("--self-test", action="store_true", help="Run harness unit self-tests (and OpenXLA check if available)")
    ap.add_argument("--receipt", type=Path, default=None)
    args = ap.parse_args()

    py_tag = f"cp{sys.version_info.major}{sys.version_info.minor}"
    if py_tag not in STABLEHLO_WHEELS and not os.environ.get("_TL_GPU_DIFF_REEXEC"):
        if args.ensure_tools:
            compat_py = ensure_compatible_python(args.tools_cache_dir)
        else:
            compat_py = find_compatible_python(args.tools_cache_dir)
        if compat_py:
            child_env = dict(os.environ, _TL_GPU_DIFF_REEXEC="1")
            proc = subprocess.run([compat_py, str(Path(__file__).resolve()), *sys.argv[1:]], env=child_env)
            return proc.returncode

    if args.ensure_tools:
        ptxas_bin, site_dir = ensure_gpu_tpu_tools(args.tools_cache_dir)
    else:
        site_cand = args.tools_cache_dir / "site-packages"
        if site_cand.is_dir() and str(site_cand) not in sys.path:
            sys.path.insert(0, str(site_cand))
        ptxas_bin = find_ptxas(args.tools_cache_dir) or ""
        site_dir = site_cand if site_cand.is_dir() else None

    if args.self_test:
        suite = unittest.defaultTestLoader.loadTestsFromTestCase(GPUDiffRunnerSelfTests)
        res = unittest.TextTestRunner(verbosity=2).run(suite)
        if not res.wasSuccessful():
            return 1
        if ptxas_bin:
            rc, log = compile_ptx_with_ptxas(
                ptxas_bin,
                ".version 8.0\n.target sm_90\n.address_size 64\n.visible .entry nop() {\n  ret;\n}\n",
            )
            if rc != 0:
                print(f"[FAIL] ptxas self-test failed: {log}", file=sys.stderr)
                return 1
        try:
            from mlir.dialects import stablehlo as _shlo  # noqa: F401
            run_m6_mlir_mutant_check(
                "module @t {\n  func.func @f(%x: tensor<2xui64>) -> tensor<2xui64> {\n    return %x : tensor<2xui64>\n  }\n}\n"
            )
        except ImportError:
            if args.ensure_tools:
                raise
        print("[gpu-tpu-diff] self-test PASSED")
        return 0

    if not ptxas_bin:
        print("[FAIL] `ptxas` not found; pass --ensure-tools or set PTXAS", file=sys.stderr)
        return 1
    clangxx = find_clangxx()
    if not clangxx:
        print("[FAIL] `clang++` not found; install clang or set CLANGXX", file=sys.stderr)
        return 1

    if args.fixtures_json is not None:
        payload = json.loads(args.fixtures_json.read_text(encoding="utf-8"))
    else:
        if not args.core_bin.is_file():
            print(f"[FAIL] Missing lean-native-core binary at {args.core_bin}", file=sys.stderr)
            return 1
        proc = subprocess.run(
            [str(args.core_bin), "gpu-tpu-diff-suite"],
            capture_output=True,
            text=True,
            timeout=120,
        )
        if proc.returncode != 0:
            print(f"[FAIL] `lean-native-core gpu-tpu-diff-suite` failed:\n{proc.stderr}", file=sys.stderr)
            return 1
        payload = json.loads(proc.stdout)

    summary = run_suite_from_payload(
        payload,
        ptxas_bin=ptxas_bin,
        clangxx=clangxx,
        tools_cache_dir=args.tools_cache_dir,
    )
    if args.receipt is not None:
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(summary))
    return 0


if __name__ == "__main__":
    sys.exit(main())
