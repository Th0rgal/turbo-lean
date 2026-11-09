#!/usr/bin/env python3
"""Stage 4: Multi-Backend Seeded Target-IR Differential & Sanitizer/UB Fuzzing Gate.

Executes deterministic SplitMix64-seeded valid + intentional UB/trap + negative semantic mutant
Target-IR programs emitted and roundtrip-verified by `LeanNative.Driver.TargetIRFuzzCLI`
(`lean-native-core target-ir-fuzz-suite`) across all four typed backend ASTs (`LLVMAst`, `PTXAst`,
`StableHLOAst`, `MetalAst`):

  1. `LLVMAst` (`opt -passes=verify` + `lli --force-interpreter` + `opt -passes=asan` + `clang`
     `-fsanitize=address,undefined -fno-sanitize-recover=all`):
     - Valid cases: bit-exact 64-bit differential agreement across all seeded input vectors, plus
       negative mutant divergence verification.
     - Trap cases (`udiv_zero`, `sdiv_int64_min_neg1`, `srem_int64_min_neg1`, `null_load`,
       `null_store`, `oob_alloca_gep_load`): two-sided trap agreement (`LLVMAst.execFn = .ub _`
       AND native ASan/UBSan instrumented binary terminates non-zero).

  2. `PTXAst` (`ptxas -arch=sm_90 -Werror` + trap-checking SIMT CTA reference executor):
     - Valid cases: `ptxas -Werror` SASS assembly (`0` warnings/errors), bit-exact 64-bit SIMT
       agreement (including `.shared` + `bar.sync`), and negative mutant rejection.
     - Trap cases (`divisionByZero`, `signedDivOverflow`, `outOfBoundsLoad`, `misalignedAccess`,
       `dataRace`, `barrierDivergence`, `typeMismatch`): two-sided trap agreement (`ptxas -Werror`
       rejects static `typeMismatch`; SIMT reference executor traps on all runtime UB classes).

  3. `StableHLOAst` (OpenXLA `mlir.ir.Module.parse` + `operation.verify()` +
     `mlir.dialects.stablehlo.eval_module`):
     - Valid cases: multi-width integer (`i1`, `i8`/`ui8`, `i16`/`ui16`, `i32`/`ui32`, `i64`/`ui64`),
       `INT64_MIN / -1` & `INT64_MIN % -1`, `reshape`/`slice`/`broadcast_in_dim`/`convert`,
       `dot_general`, and clamped OOB `dynamic_slice` bit-exact tensor agreement + mutant rejection.
     - Trap cases (`divisionByZero`, `volumeMismatch`): two-sided trap agreement (`Module.parse` /
       `verify()` rejects static `volumeMismatch`; isolated OpenXLA child traps non-zero on `/ 0`
       and `% 0`).

  4. `MetalAst` (`clang++ -std=c++17` with `-fsanitize=address,undefined` and `-fsanitize=thread`):
     - Valid cases: concurrent `std::thread` + `pthread_barrier_t` multi-lane execution under both
       ASan+UBSan and TSan (`0` sanitizer errors), bit-exact 64-bit output agreement, and negative
       mutant rejection.
     - Trap cases (`divisionByZero`, `signedDivOverflow`, `shiftOutOfRange`, `outOfBoundsLoad`,
       `dataRace`): two-sided trap agreement (`MetalAst.evalMSLKernel ≠ .ok` AND ASan/UBSan/TSan
       host binary aborts non-zero).
"""
from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import struct
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
ROOT_DIR = SCRIPT_DIR.parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import run_gpu_tpu_diff as gpu_diff
import run_llvm_lli_diff as llvm_diff

MASK8 = 0xFF
MASK16 = 0xFFFF
MASK32 = 0xFFFF_FFFF
MASK64 = 0xFFFF_FFFF_FFFF_FFFF


def find_clang_c() -> str | None:
    env_cc = os.environ.get("CLANG")
    if env_cc and Path(env_cc).is_file() and os.access(env_cc, os.X_OK):
        return env_cc
    for name in ("clang-18", "clang-19", "clang", "clang-17", "clang-20"):
        found = shutil.which(name)
        if found:
            return found
    for ver in ("18", "19", "17", "20"):
        cand = f"/usr/lib/llvm-{ver}/bin/clang"
        if Path(cand).is_file() and os.access(cand, os.X_OK):
            return cand
    return None


def _s8(u: int) -> int:
    u &= MASK8
    return u - 0x100 if (u & 0x80) else u


def _s16(u: int) -> int:
    u &= MASK16
    return u - 0x10000 if (u & 0x8000) else u


def _s32(u: int) -> int:
    u &= MASK32
    return u - (1 << 32) if (u & (1 << 31)) else u


def _s64(u: int) -> int:
    u &= MASK64
    return u - (1 << 64) if (u & (1 << 63)) else u


# ---------------------------------------------------------------------------
# 1. `LLVMAst` Valid (`lli --force-interpreter`) & Trap (`opt -passes=asan` + UBSan)
# ---------------------------------------------------------------------------


def run_llvm_valid_case(lli_bin: str, opt_bin: str, case: dict[str, Any]) -> None:
    cid = case["id"]
    fn_name = case["fnName"]
    if not case.get("roundtripVerified", False):
        raise RuntimeError(f"[{cid}] in-Lean roundtripVerified flag is false")
    ir_text = case["irText"]
    mut_ir = case["negativeMutantIr"]
    vectors = case["vectors"]
    if not vectors:
        raise RuntimeError(f"[{cid}] empty input vectors")

    mutant_diverged = False
    with tempfile.TemporaryDirectory(prefix="ln-fuzz-llvm-") as tmp_str:
        tmp = Path(tmp_str)
        for v_idx, vec in enumerate(vectors):
            inputs = [int(x) & MASK64 for x in vec["inputs"]]
            expected = int(vec["expectedWord"]) & MASK64

            valid_path = tmp / f"{cid}_v{v_idx}.ll"
            valid_path.write_text(
                llvm_diff.build_lli_harness_ir(ir_text, fn_name, inputs),
                encoding="utf-8",
            )
            got = llvm_diff.run_lli_u64(lli_bin, opt_bin, valid_path, verify_ir=(v_idx == 0))
            if got != expected:
                raise RuntimeError(
                    f"[{cid}] vector #{v_idx} mismatch: Lean={expected:#018x}, lli={got:#018x}"
                )

            if not mutant_diverged:
                mut_path = tmp / f"{cid}_mut_v{v_idx}.ll"
                mut_path.write_text(
                    llvm_diff.build_lli_harness_ir(mut_ir, fn_name, inputs),
                    encoding="utf-8",
                )
                got_mut = llvm_diff.run_lli_u64(lli_bin, opt_bin, mut_path, verify_ir=(v_idx == 0))
                if got_mut != expected:
                    mutant_diverged = True

    if not mutant_diverged:
        raise RuntimeError(
            f"[{cid}] negative mutant ({case.get('negativeMutantReason')}) failed to diverge under lli!"
        )


def run_llvm_trap_case_native(clang_bin: str, opt_bin: str, case: dict[str, Any]) -> int:
    """Instrument `@<fnName>` with `sanitize_address` + `opt -passes=asan`, link against a C
    driver compiled with `-fsanitize=address,undefined -fno-sanitize-recover=all`, and execute.
    Returns the child process exit code (must be `!= 0` on UB/trap)."""
    cid = case["id"]
    fn_name = case["fnName"]
    if not case.get("roundtripVerified", False):
        raise RuntimeError(f"[{cid}] in-Lean roundtripVerified flag is false")
    ir_text = case["irText"]
    inputs = [int(x) & MASK64 for x in case["inputs"]]

    # Attach `sanitize_address` to `@<fnName>(...)` so `opt -passes=asan` instruments stack `alloca` redzones.
    pat = re.compile(rf"(@{re.escape(fn_name)}\([^)]*\))\s*\{{")
    instrumentable_ir, count = pat.subn(r"\1 sanitize_address {", ir_text, count=1)
    if count != 1:
        raise RuntimeError(f"[{cid}] failed to inject sanitize_address onto @{fn_name}")

    with tempfile.TemporaryDirectory(prefix="ln-fuzz-llvm-trap-") as tmp_str:
        tmp = Path(tmp_str)
        raw_ll = tmp / "trap_raw.ll"
        asan_ll = tmp / "trap_asan.ll"
        drv_c = tmp / "driver.c"
        bin_path = tmp / "trap_runner"

        raw_ll.write_text(instrumentable_ir, encoding="utf-8")
        ver = subprocess.run(
            [opt_bin, "-passes=verify", "-disable-output", str(raw_ll)],
            capture_output=True,
            text=True,
            timeout=30,
        )
        if ver.returncode != 0:
            raise RuntimeError(f"[{cid}] opt -passes=verify failed on trap IR:\n{ver.stderr}")

        opt_asan = subprocess.run(
            [opt_bin, "-passes=asan", "-S", str(raw_ll), "-o", str(asan_ll)],
            capture_output=True,
            text=True,
            timeout=30,
        )
        if opt_asan.returncode != 0:
            raise RuntimeError(f"[{cid}] opt -passes=asan failed:\n{opt_asan.stderr}")

        c_params = ", ".join(f"uint64_t p{i}" for i in range(len(inputs)))
        c_args = ", ".join(f"(uint64_t){u}ULL" for u in inputs)
        drv_c.write_text(
            "#include <stdint.h>\n"
            f"extern uint64_t {fn_name}({c_params});\n"
            "int main(void) {\n"
            f"  volatile uint64_t r = {fn_name}({c_args});\n"
            "  (void)r;\n"
            "  return 0;\n"
            "}\n",
            encoding="utf-8",
        )

        comp = subprocess.run(
            [
                clang_bin,
                "-O0",
                "-g",
                "-Wno-override-module",
                "-fsanitize=address,undefined",
                "-fno-sanitize-recover=all",
                str(asan_ll),
                str(drv_c),
                "-o",
                str(bin_path),
            ],
            capture_output=True,
            text=True,
            timeout=60,
        )
        if comp.returncode != 0:
            raise RuntimeError(f"[{cid}] clang ASan/UBSan link failed:\n{comp.stderr}")

        env = os.environ.copy()
        env["ASAN_OPTIONS"] = "detect_leaks=0:halt_on_error=1:abort_on_error=1"
        env["UBSAN_OPTIONS"] = "halt_on_error=1:abort_on_error=1"
        proc = subprocess.run(
            [str(bin_path)],
            capture_output=True,
            text=True,
            timeout=30,
            env=env,
        )
        return proc.returncode


# ---------------------------------------------------------------------------
# 2. `PTXAst` Valid & Trap (`ptxas -Werror` + Trap-Checking SIMT Reference VM)
# ---------------------------------------------------------------------------


class PTXTrapError(RuntimeError):
    def __init__(self, trap_class: str, detail: str) -> None:
        super().__init__(f"{trap_class}: {detail}")
        self.trap_class = trap_class


def simt_execute_ptx_strict(
    ptx_text: str,
    kernel_name: str,
    params: dict[str, int],
    global_mem: bytearray,
    grid_dim: tuple[int, int, int] = (1, 1, 1),
    block_dim: tuple[int, int, int] = (1, 1, 1),
    step_budget: int = 100_000,
) -> bytearray:
    """Independent PTX SIMT CTA executor with explicit runtime UB/trap enforcement:
    - `divisionByZero` (`div.*` / `rem.*` by 0)
    - `signedDivOverflow` (`div.s64` / `div.s32` `INT_MIN / -1`)
    - `misalignedAccess` (`.global`/`.shared` effective address not aligned to access width)
    - `outOfBoundsLoad` / `outOfBoundsStore` (`.global`/`.shared` range outside buffer)
    - `dataRace` (overlapping `.shared` W-W or R-W across distinct threads in the same barrier epoch,
      or overlapping non-atomic `.global` W-W / R-W across distinct CTAs/threads)
    - `barrierDivergence` (divergent `bar.sync` barrier IDs or fallen-off threads)
    """
    raw_stmts, shared_syms, shared_size = gpu_diff.extract_ptx_entry_body(ptx_text, kernel_name)
    labels: dict[str, int] = {}
    insns: list[str] = []
    for item in raw_stmts:
        if item.endswith(":"):
            labels[item[:-1].strip()] = len(insns)
        else:
            insns.append(item.rstrip(";").strip())

    elem_widths = {
        "b8": 1, "u8": 1, "s8": 1,
        "b16": 2, "u16": 2, "s16": 2,
        "b32": 4, "u32": 4, "s32": 4, "f32": 4,
        "b64": 8, "u64": 8, "s64": 8, "f64": 8,
    }

    gx, gy, gz = grid_dim
    bx, by, bz = block_dim
    global_accesses: list[tuple[int, int, int, int, bool]] = []

    def check_mem_access(
        space: str,
        mem: bytearray,
        addr: int,
        width: int,
        is_write: bool,
        cta_idx: int,
        tid_idx: int,
        epoch_log: list[tuple[int, int, int, bool]],
    ) -> None:
        if addr < 0 or addr + width > len(mem):
            cls = "outOfBoundsStore" if is_write else "outOfBoundsLoad"
            raise PTXTrapError(cls, f"{space} addr={addr} width={width} size={len(mem)}")
        if addr % width != 0:
            raise PTXTrapError("misalignedAccess", f"{space} addr={addr} width={width}")
        if space == "shared":
            for p_tid, p_addr, p_w, p_write in epoch_log:
                if p_tid != tid_idx and (is_write or p_write):
                    if addr < p_addr + p_w and p_addr < addr + width:
                        raise PTXTrapError("dataRace", f"shared race at {addr} between tid {p_tid} and {tid_idx}")
            epoch_log.append((tid_idx, addr, width, is_write))
        elif space == "global":
            for p_cta, p_tid, p_addr, p_w, p_write in global_accesses:
                if (p_cta != cta_idx or p_tid != tid_idx) and (is_write or p_write):
                    if addr < p_addr + p_w and p_addr < addr + width:
                        raise PTXTrapError("dataRace", f"global race at {addr}")
            global_accesses.append((cta_idx, tid_idx, addr, width, is_write))

    cta_linear = 0
    for cz in range(gz):
        for cy in range(gy):
            for cx in range(gx):
                shared_mem = bytearray(shared_size)
                epoch_log: list[tuple[int, int, int, bool]] = []
                threads: list[dict[str, Any]] = []
                for tz in range(bz):
                    for ty in range(by):
                        for tx in range(bx):
                            threads.append(
                                {
                                    "tid_idx": len(threads),
                                    "pc": 0,
                                    "halted": False,
                                    "exited_by_ret": False,
                                    "regs": {},
                                    "preds": {},
                                    "sregs": {
                                        "%tid.x": tx, "%tid.y": ty, "%tid.z": tz,
                                        "%ntid.x": bx, "%ntid.y": by, "%ntid.z": bz,
                                        "%ctaid.x": cx, "%ctaid.y": cy, "%ctaid.z": cz,
                                        "%nctaid.x": gx, "%nctaid.y": gy, "%nctaid.z": gz,
                                    },
                                }
                            )

                steps = 0
                while not all(t["halted"] for t in threads):
                    steps += 1
                    if steps > step_budget:
                        raise PTXTrapError("fuelExhausted", f"step budget exceeded in {kernel_name}")
                    progressed = False
                    for t in threads:
                        if t["halted"]:
                            continue
                        if t["pc"] >= len(insns):
                            t["halted"] = True
                            t["exited_by_ret"] = False
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

                        progressed = True
                        if not guard_ok:
                            t["pc"] += 1
                            continue

                        ops = gpu_diff._split_ptx_operands(arg_str) if arg_str else []
                        regs = t["regs"]
                        preds = t["preds"]
                        sregs = t["sregs"]

                        def val(tok: str) -> int:
                            return gpu_diff._parse_ptx_imm_or_reg(tok, regs, preds, sregs, shared_syms)

                        def parse_addr_raw(addr_tok: str) -> int:
                            inner = addr_tok.strip()
                            body = inner[1:-1].strip()
                            m = re.match(r"^([A-Za-z0-9_$.%]+)\s*(?:([+-])\s*([+-]?\s*\d+))?$", body)
                            if not m:
                                raise ValueError(f"bad PTX addr: {addr_tok}")
                            base_sym, sign_op, disp_str = m.group(1), m.group(2), m.group(3)
                            base = shared_syms[base_sym] if base_sym in shared_syms else regs.get(base_sym, 0)
                            disp = 0
                            if disp_str:
                                vd = int(disp_str.replace(" ", ""), 10)
                                disp = -vd if sign_op == "-" else vd
                            return _s64(base) + disp

                        if op == "ret":
                            t["halted"] = True
                            t["exited_by_ret"] = True
                            continue
                        elif op == "bra":
                            t["pc"] = labels[ops[0]]
                            continue
                        elif op.startswith("ld.param."):
                            pname = ops[1].strip()[1:-1].strip()
                            regs[ops[0]] = params[pname] & MASK64
                        elif op.startswith("cvta.to.global."):
                            regs[ops[0]] = val(ops[1]) & MASK64
                        elif op.startswith("mov."):
                            mask = MASK32 if op.endswith("32") else MASK64
                            regs[ops[0]] = val(ops[1]) & mask
                        elif op in ("cvt.u64.u32", "cvt.u64.b32", "cvt.u32.u64", "cvt.u32.b64"):
                            regs[ops[0]] = val(ops[1]) & MASK32
                        elif op.startswith("ld.global.") or op.startswith("ld.shared."):
                            is_glob = op.startswith("ld.global.")
                            space = "global" if is_glob else "shared"
                            mem = global_mem if is_glob else shared_mem
                            ty_suf = op.split(".")[-1]
                            width = elem_widths[ty_suf]
                            addr = parse_addr_raw(ops[1])
                            check_mem_access(space, mem, addr, width, False, cta_linear, t["tid_idx"], epoch_log)
                            fmt = {1: "<B", 2: "<H", 4: "<I", 8: "<Q"}[width]
                            regs[ops[0]] = struct.unpack_from(fmt, mem, addr)[0]
                        elif op.startswith("st.global.") or op.startswith("st.shared."):
                            is_glob = op.startswith("st.global.")
                            space = "global" if is_glob else "shared"
                            mem = global_mem if is_glob else shared_mem
                            ty_suf = op.split(".")[-1]
                            width = elem_widths[ty_suf]
                            addr = parse_addr_raw(ops[0])
                            check_mem_access(space, mem, addr, width, True, cta_linear, t["tid_idx"], epoch_log)
                            fmt = {1: "<B", 2: "<H", 4: "<I", 8: "<Q"}[width]
                            mask = (1 << (width * 8)) - 1
                            struct.pack_into(fmt, mem, addr, val(ops[1]) & mask)
                        elif op.startswith("add."):
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
                        elif op.startswith("mad.lo."):
                            mask = MASK32 if op.endswith("32") else MASK64
                            regs[ops[0]] = ((val(ops[1]) & mask) * (val(ops[2]) & mask) + (val(ops[3]) & mask)) & mask
                        elif op == "div.u64" or op == "div.u32":
                            mask = MASK32 if op.endswith("32") else MASK64
                            d = val(ops[2]) & mask
                            if d == 0:
                                raise PTXTrapError("divisionByZero", f"{op} by zero")
                            regs[ops[0]] = (val(ops[1]) & mask) // d
                        elif op == "rem.u64" or op == "rem.u32":
                            mask = MASK32 if op.endswith("32") else MASK64
                            d = val(ops[2]) & mask
                            if d == 0:
                                raise PTXTrapError("divisionByZero", f"{op} by zero")
                            regs[ops[0]] = (val(ops[1]) & mask) % d
                        elif op == "div.s64":
                            a_s, b_s = _s64(val(ops[1])), _s64(val(ops[2]))
                            if b_s == 0:
                                raise PTXTrapError("divisionByZero", "div.s64 by zero")
                            if a_s == -(1 << 63) and b_s == -1:
                                raise PTXTrapError("signedDivOverflow", "div.s64 INT64_MIN / -1")
                            q = int(a_s / b_s) if (a_s ^ b_s) >= 0 else -((-a_s) // b_s if b_s > 0 else a_s // (-b_s))
                            regs[ops[0]] = q & MASK64
                        elif op == "rem.s64":
                            a_s, b_s = _s64(val(ops[1])), _s64(val(ops[2]))
                            if b_s == 0:
                                raise PTXTrapError("divisionByZero", "rem.s64 by zero")
                            q = -(abs(a_s) // abs(b_s)) if (a_s < 0) != (b_s < 0) else (abs(a_s) // abs(b_s))
                            regs[ops[0]] = (a_s - q * b_s) & MASK64
                        elif op.startswith("and."):
                            mask = MASK32 if op.endswith("32") else MASK64
                            regs[ops[0]] = (val(ops[1]) & val(ops[2])) & mask
                        elif op.startswith("or."):
                            mask = MASK32 if op.endswith("32") else MASK64
                            regs[ops[0]] = (val(ops[1]) | val(ops[2])) & mask
                        elif op.startswith("xor."):
                            mask = MASK32 if op.endswith("32") else MASK64
                            regs[ops[0]] = (val(ops[1]) ^ val(ops[2])) & mask
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
                                "eq": a_v == b_v, "ne": a_v != b_v,
                                "lt": a_v < b_v, "le": a_v <= b_v,
                                "gt": a_v > b_v, "ge": a_v >= b_v,
                            }
                            preds[ops[0]] = cmp_map[cmp_op]
                        elif op.startswith("selp."):
                            mask = MASK32 if op.endswith("32") else MASK64
                            cond = preds.get(ops[3], False)
                            regs[ops[0]] = (val(ops[1]) if cond else val(ops[2])) & mask
                        else:
                            raise ValueError(f"unsupported PTX instruction: {stmt}")
                        t["pc"] += 1

                    if progressed:
                        continue

                    # Synchronize CTA barrier (`bar.sync <bid>`): match PTX 8.0 / `stepCTABarrierGen`.
                    bar_bids: list[int | None] = []
                    for t in threads:
                        if t["halted"]:
                            if not t["exited_by_ret"]:
                                raise PTXTrapError("barrierDivergence", "thread fell off end while CTA at bar.sync")
                            bar_bids.append(None)
                        else:
                            st = insns[t["pc"]]
                            if st.startswith("@"):
                                _, st = st.split(None, 1)
                            toks = st.split()
                            if toks[0] != "bar.sync":
                                raise PTXTrapError("barrierDivergence", f"thread not at bar.sync: {st}")
                            bar_bids.append(int(toks[1], 10))
                    active_bids = {b for b in bar_bids if b is not None}
                    if len(active_bids) != 1:
                        raise PTXTrapError("barrierDivergence", f"divergent barrier IDs: {bar_bids}")
                    for t in threads:
                        if not t["halted"]:
                            t["pc"] += 1
                    epoch_log.clear()

                cta_linear += 1
    return global_mem


def _run_ptx_buffers(
    ptx_text: str,
    kernel_name: str,
    grid_x: int,
    block_x: int,
    inputs: list[list[int]],
) -> list[int]:
    arity = len(inputs)
    n = len(inputs[0]) if inputs else 0
    total_words = (arity + 1) * n
    gmem = bytearray(total_words * 8)
    params: dict[str, int] = {"param_n": n, "param_out": arity * n * 8}
    for j in range(arity):
        params[f"param_in{j}"] = j * n * 8
        for i, w in enumerate(inputs[j]):
            struct.pack_into("<Q", gmem, (j * n + i) * 8, int(w) & MASK64)
    simt_execute_ptx_strict(
        ptx_text,
        kernel_name,
        params=params,
        global_mem=gmem,
        grid_dim=(grid_x, 1, 1),
        block_dim=(block_x, 1, 1),
    )
    out_base = arity * n * 8
    return [struct.unpack_from("<Q", gmem, out_base + i * 8)[0] for i in range(n)]


def run_ptx_case(ptxas_bin: str, case: dict[str, Any]) -> None:
    cid = case["id"]
    if not case.get("roundtripVerified", False):
        raise RuntimeError(f"[{cid}] in-Lean roundtripVerified flag is false")
    kname = case["kernelName"]
    grid_x = int(case["gridX"])
    block_x = int(case["blockX"])
    ptx_text = case["ptxText"]
    inputs = [[int(x) & MASK64 for x in arr] for arr in case["inputs"]]

    if case["kind"] == "valid":
        rc, out = gpu_diff.compile_ptx_with_ptxas(ptxas_bin, ptx_text)
        if rc != 0:
            raise RuntimeError(f"[{cid}] ptxas -Werror failed on valid PTX:\n{out}")
        got = _run_ptx_buffers(ptx_text, kname, grid_x, block_x, inputs)
        expected = [int(x) & MASK64 for x in case["expected"]]
        if got != expected:
            raise RuntimeError(f"[{cid}] PTX SIMT mismatch: Lean={expected}, SIMT={got}")

        mut_ptx = case["negativeMutantPtx"]
        rc_m, out_m = gpu_diff.compile_ptx_with_ptxas(ptxas_bin, mut_ptx)
        if rc_m != 0:
            raise RuntimeError(f"[{cid}] ptxas failed on negative semantic mutant:\n{out_m}")
        got_mut = _run_ptx_buffers(mut_ptx, kname, grid_x, block_x, inputs)
        if got_mut == expected:
            raise RuntimeError(
                f"[{cid}] PTX negative mutant ({case.get('negativeMutantReason')}) failed to diverge!"
            )
    else:
        trap_cls = case["trapClass"]
        static_reject = bool(case.get("staticReject", False))
        rc, out = gpu_diff.compile_ptx_with_ptxas(ptxas_bin, ptx_text)
        if static_reject:
            if rc == 0:
                raise RuntimeError(f"[{cid}] expected ptxas -Werror to reject static {trap_cls}, but rc=0")
        else:
            if rc != 0:
                raise RuntimeError(f"[{cid}] expected runtime trap {trap_cls} to assemble cleanly, got:\n{out}")
            try:
                _run_ptx_buffers(ptx_text, kname, grid_x, block_x, inputs)
            except PTXTrapError as trap_exc:
                if trap_exc.trap_class != trap_cls:
                    raise RuntimeError(
                        f"[{cid}] PTX runtime trap mismatch: Lean={trap_cls}, SIMT={trap_exc.trap_class}"
                    ) from trap_exc
            else:
                raise RuntimeError(f"[{cid}] PTX runtime trap {trap_cls} did NOT trap in SIMT reference VM!")


# ---------------------------------------------------------------------------
# 3. `StableHLOAst` Valid & Trap (OpenXLA `Module.parse` + `eval_module`)
# ---------------------------------------------------------------------------


def eval_stablehlo_multiwidth(mlir_text: str, args_spec: list[dict[str, Any]]) -> tuple[list[int], str, list[int]]:
    """Evaluate a StableHLO module via OpenXLA across `i1`, `i8`/`ui8`, `i16`/`ui16`,
    `i32`/`ui32`, and `i64`/`ui64` tensors."""
    import numpy as np
    from mlir import ir
    from mlir.dialects import stablehlo

    def to_dense_attr(spec: dict[str, Any]) -> Any:
        shape = tuple(spec["shape"])
        elem = spec["elem"]
        words = [int(w) & MASK64 for w in spec["words"]]
        if elem == "i1":
            arr = np.array([bool(w & 1) for w in words], dtype=np.bool_).reshape(shape)
            return ir.DenseElementsAttr.get(arr, type=ir.IntegerType.get_signless(1))
        if elem == "i8":
            arr = np.array([_s8(w) for w in words], dtype=np.int8).reshape(shape)
            return ir.DenseElementsAttr.get(arr, type=ir.IntegerType.get_signless(8))
        if elem == "ui8":
            arr = np.array([w & MASK8 for w in words], dtype=np.uint8).reshape(shape)
            return ir.DenseElementsAttr.get(arr, type=ir.IntegerType.get_unsigned(8))
        if elem == "i16":
            arr = np.array([_s16(w) for w in words], dtype=np.int16).reshape(shape)
            return ir.DenseElementsAttr.get(arr, type=ir.IntegerType.get_signless(16))
        if elem == "ui16":
            arr = np.array([w & MASK16 for w in words], dtype=np.uint16).reshape(shape)
            return ir.DenseElementsAttr.get(arr, type=ir.IntegerType.get_unsigned(16))
        if elem == "i32":
            arr = np.array([_s32(w) for w in words], dtype=np.int32).reshape(shape)
            return ir.DenseElementsAttr.get(arr, type=ir.IntegerType.get_signless(32))
        if elem == "ui32":
            arr = np.array([w & MASK32 for w in words], dtype=np.uint32).reshape(shape)
            return ir.DenseElementsAttr.get(arr, type=ir.IntegerType.get_unsigned(32))
        if elem == "i64":
            arr = np.array([_s64(w) for w in words], dtype=np.int64).reshape(shape)
            return ir.DenseElementsAttr.get(arr, type=ir.IntegerType.get_signless(64))
        if elem == "ui64":
            arr = np.array(words, dtype=np.uint64).reshape(shape)
            return ir.DenseElementsAttr.get(arr, type=ir.IntegerType.get_unsigned(64))
        raise ValueError(f"Unsupported StableHLO element type: {elem}")

    with ir.Context() as ctx:
        stablehlo.register_dialect(ctx)
        mod = ir.Module.parse(mlir_text)
        if not mod.operation.verify():
            raise RuntimeError("StableHLO module failed OpenXLA MLIR verification")
        dense_args = [to_dense_attr(a) for a in args_spec]
        outs = stablehlo.eval_module(mod, dense_args)
        if len(outs) != 1:
            raise RuntimeError(f"Expected 1 result from eval_module, got {len(outs)}")
        res_attr = ir.DenseElementsAttr(outs[0])
        res_ty = ir.RankedTensorType(res_attr.type)
        out_shape = list(res_ty.shape)
        et_str = str(res_ty.element_type)
        arr = np.array(res_attr)
        width_masks = {
            "i8": MASK8, "ui8": MASK8,
            "i16": MASK16, "ui16": MASK16,
            "i32": MASK32, "ui32": MASK32,
            "i64": MASK64, "ui64": MASK64,
        }
        if et_str == "i1":
            flat_words = [1 if bool(x) else 0 for x in arr.reshape(-1)]
        elif et_str in width_masks:
            m = width_masks[et_str]
            if et_str == "ui64":
                flat_words = [int(x) & MASK64 for x in arr.view(np.uint64).reshape(-1)]
            elif et_str == "i64":
                flat_words = [int(x) & MASK64 for x in arr.astype(np.int64).reshape(-1)]
            else:
                flat_words = [int(x) & m for x in arr.reshape(-1)]
        else:
            raise ValueError(f"Unexpected StableHLO output element type: {et_str}")
        return out_shape, et_str, flat_words


def eval_stablehlo_trap_isolated(
    mlir_text: str,
    args_spec: list[dict[str, Any]],
    tools_cache_dir: Path,
) -> tuple[int, str, str]:
    """Run OpenXLA `eval_stablehlo_multiwidth` in a child process so C++ `llvm::APInt`
    `SIGABRT` traps on `/ 0` and `% 0` return a clean non-zero exit code without
    conflating harness/Python exceptions with genuine OpenXLA interpreter traps."""
    code = (
        "import json, sys\n"
        "from pathlib import Path\n"
        f"sys.path.insert(0, {repr(str(SCRIPT_DIR))})\n"
        "import run_gpu_tpu_diff as rgt\n"
        "import run_target_ir_fuzz as rtf\n"
        "req = json.loads(sys.stdin.read())\n"
        "try:\n"
        "    rgt.ensure_openxla_stablehlo(Path(req['cache']))\n"
        "except Exception as exc:\n"
        "    print(json.dumps({'bootstrap_error': f'{type(exc).__name__}: {exc}'}))\n"
        "    sys.exit(99)\n"
        "print('__SHLO_FUZZ_BOOTSTRAP_OK__', flush=True)\n"
        "try:\n"
        "    out = rtf.eval_stablehlo_multiwidth(req['mlir'], req['args'])\n"
        "except Exception as exc:\n"
        "    print(json.dumps({'eval_error': f'{type(exc).__name__}: {exc}'}), flush=True)\n"
        "    sys.exit(98)\n"
        "print(json.dumps({'ok': list(out)}), flush=True)\n"
    )
    proc = subprocess.run(
        [sys.executable, "-c", code],
        input=json.dumps({"cache": str(tools_cache_dir), "mlir": mlir_text, "args": args_spec}),
        capture_output=True,
        text=True,
        timeout=60,
    )
    if proc.returncode == 99 or "__SHLO_FUZZ_BOOTSTRAP_OK__" not in proc.stdout:
        raise RuntimeError(
            f"Isolated OpenXLA child bootstrap failed (rc={proc.returncode}):\n{proc.stdout}\n{proc.stderr}"
        )
    if proc.returncode == 98:
        # Distinguish genuine MLIR/OpenXLA evaluation errors (`MLIRError` / `ValueError` from MLIR)
        # from unexpected harness bugs (AttributeError, TypeError, KeyError, NameError, etc.).
        if '"MLIRError:' not in proc.stdout:
            raise RuntimeError(
                f"Isolated OpenXLA child failed with unexpected Python exception:\n{proc.stdout}\n{proc.stderr}"
            )
    return proc.returncode, proc.stdout, proc.stderr


def run_stablehlo_case(tools_cache_dir: Path, case: dict[str, Any]) -> None:
    cid = case["id"]
    mlir_text = case["mlirText"]
    args_spec = case["args"]

    if case["kind"] == "valid":
        out_shape, out_elem, out_words = eval_stablehlo_multiwidth(mlir_text, args_spec)
        exp = case["expected"]
        exp_shape = [int(d) for d in exp["shape"]]
        exp_elem = exp["elem"]
        exp_words = [int(w) & MASK64 for w in exp["words"]]
        if out_shape != exp_shape or out_elem != exp_elem or out_words != exp_words:
            raise RuntimeError(
                f"[{cid}] StableHLO OpenXLA mismatch:\n"
                f"  Lean   = ({exp_shape}, {exp_elem}, {exp_words})\n"
                f"  OpenXLA= ({out_shape}, {out_elem}, {out_words})"
            )

        mut_mlir = case["negativeMutantMlir"]
        _, _, mut_words = eval_stablehlo_multiwidth(mut_mlir, args_spec)
        if mut_words == exp_words:
            raise RuntimeError(
                f"[{cid}] StableHLO negative mutant ({case.get('negativeMutantReason')}) failed to diverge!"
            )
    else:
        trap_cls = case["trapClass"]
        static_reject = bool(case.get("staticReject", False))
        if static_reject:
            from mlir import ir
            from mlir.dialects import stablehlo

            rejected = False
            with ir.Context() as ctx:
                stablehlo.register_dialect(ctx)
                try:
                    mod = ir.Module.parse(mlir_text)
                    if not mod.operation.verify():
                        rejected = True
                except Exception:
                    rejected = True
            if not rejected:
                raise RuntimeError(f"[{cid}] OpenXLA verifier accepted static invalid {trap_cls} MLIR!")
        else:
            rc, _, _ = eval_stablehlo_trap_isolated(mlir_text, args_spec, tools_cache_dir)
            if rc == 0:
                raise RuntimeError(f"[{cid}] OpenXLA eval_module did NOT trap on runtime {trap_cls}!")


# ---------------------------------------------------------------------------
# 4. `MetalAst` Valid & Trap (`clang++ -std=c++17` ASan+UBSan and TSan)
# ---------------------------------------------------------------------------

METAL_FUZZ_CXX17_SHIM = r"""
#include <cstdint>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <pthread.h>
#include <thread>
#include <vector>

using host_thread = std::thread;
static pthread_barrier_t g_msl_tg_barrier;
static pthread_barrier_t g_msl_start_barrier;

namespace metal {
using uchar  = uint8_t;
using ushort = uint16_t;
using uint   = uint32_t;
using ulong  = uint64_t;
using char_t = int8_t;
using short_t = int16_t;
using int_t  = int32_t;
using long_t = int64_t;

struct mem_flags {
    static constexpr int mem_none = 0;
    static constexpr int mem_device = 1;
    static constexpr int mem_threadgroup = 2;
};

inline void threadgroup_barrier(int) {
    pthread_barrier_wait(&g_msl_tg_barrier);
}

inline ulong clz(ulong x) {
    return x == 0 ? 64ULL : (ulong)__builtin_clzll(x);
}
inline uint clz(uint x) {
    return x == 0 ? 32U : (uint)__builtin_clz(x);
}

template <typename T>
inline T select(T fval, T tval, bool cond) { return cond ? tval : fval; }
} // namespace metal

using metal::uchar;
using metal::ushort;
using metal::uint;
using metal::ulong;
using metal::mem_flags;
using metal::threadgroup_barrier;
using metal::clz;
using metal::select;

#define kernel __attribute__((noinline))
#define device
#define constant const
#define threadgroup static
#define thread
"""


def translate_fuzz_msl_to_cxx17(msl_text: str) -> str:
    src = msl_text.replace("#include <metal_stdlib>\nusing namespace metal;", METAL_FUZZ_CXX17_SHIM)
    if "#include <metal_stdlib>" in src:
        src = src.replace("#include <metal_stdlib>", METAL_FUZZ_CXX17_SHIM)
    src = re.sub(r"\[\[[A-Za-z0-9_()\s]+\]\]", "", src)
    return (
        src
        + "\n#undef thread\n#undef threadgroup\n#undef constant\n#undef device\n#undef kernel\n"
    )


def _exec_metal_host_kernel(
    clangxx: str,
    msl_text: str,
    kernel_name: str,
    grid_x: int,
    group_x: int,
    inputs: list[list[int]],
    sanitizer: str,
) -> tuple[int, list[int], str]:
    arity = len(inputs)
    n = len(inputs[0]) if inputs else 0
    total_lanes = max(1, grid_x * group_x)

    cpp_lines = [translate_fuzz_msl_to_cxx17(msl_text), "int main() {"]
    for j in range(arity):
        cpp_lines.append(f"  ulong* in_{j} = (ulong*)std::malloc({max(1, n)} * sizeof(ulong));")
        for i, w in enumerate(inputs[j]):
            cpp_lines.append(f"  in_{j}[{i}] = {int(w) & MASK64}ULL;")
    cpp_lines.append(f"  ulong* out_buf = (ulong*)std::malloc({max(1, n)} * sizeof(ulong));")
    cpp_lines.append(f"  std::memset(out_buf, 0, {max(1, n)} * sizeof(ulong));")
    cpp_lines.append(f"  const ulong n_val = {n}ULL;")

    # Execute CTAs sequentially and launch `group_x` concurrent `host_thread`s per CTA,
    # synchronized at start via `g_msl_start_barrier` (so TSan reliably observes concurrent races)
    # and synchronized on `threadgroup_barrier` via `g_msl_tg_barrier`.
    call_args = [f"in_{j}" for j in range(arity)] + ["out_buf", "n_val", "gid"]
    cpp_lines.append(f"  for (uint cta = 0; cta < {grid_x}u; ++cta) {{")
    cpp_lines.append(f"    pthread_barrier_init(&g_msl_tg_barrier, nullptr, {group_x}u);")
    cpp_lines.append(f"    pthread_barrier_init(&g_msl_start_barrier, nullptr, {group_x}u);")
    cpp_lines.append("    std::vector<host_thread> lanes;")
    cpp_lines.append(f"    lanes.reserve({group_x}u);")
    cpp_lines.append(f"    for (uint tid = 0; tid < {group_x}u; ++tid) {{")
    cpp_lines.append(f"      uint gid = cta * {group_x}u + tid;")
    cpp_lines.append("      lanes.emplace_back([&, gid]() {")
    cpp_lines.append("        pthread_barrier_wait(&g_msl_start_barrier);")
    cpp_lines.append(f"        {kernel_name}({', '.join(call_args)});")
    cpp_lines.append("      });")
    cpp_lines.append("    }")
    cpp_lines.append("    for (auto& th : lanes) th.join();")
    cpp_lines.append("    pthread_barrier_destroy(&g_msl_start_barrier);")
    cpp_lines.append("    pthread_barrier_destroy(&g_msl_tg_barrier);")
    cpp_lines.append("  }")
    cpp_lines.append('  std::printf("OUT:");')
    cpp_lines.append(
        f'  for (size_t i = 0; i < {n}; ++i) std::printf(" %llu", (unsigned long long)out_buf[i]);'
    )
    cpp_lines.append('  std::printf("\\n");')
    for j in range(arity):
        cpp_lines.append(f"  std::free(in_{j});")
    cpp_lines.append("  std::free(out_buf);")
    cpp_lines.append(f"  (void){total_lanes};")
    cpp_lines.append("  return 0;\n}")
    cpp_src = "\n".join(cpp_lines)

    with tempfile.TemporaryDirectory(prefix="ln-fuzz-msl-") as tmp_str:
        tmp = Path(tmp_str)
        cpp_path = tmp / "kernel.cpp"
        bin_path = tmp / "kernel_runner"
        cpp_path.write_text(cpp_src, encoding="utf-8")
        comp = subprocess.run(
            [
                clangxx,
                "-std=c++17",
                "-O0",
                "-g",
                "-pthread",
                "-Wno-unused-parameter",
                "-Wno-unused-variable",
                f"-fsanitize={sanitizer}",
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
            raise RuntimeError(f"clang++ ({sanitizer}) failed to compile Metal C++17:\n{comp.stderr}\n{cpp_src}")

        env = os.environ.copy()
        env["ASAN_OPTIONS"] = "detect_leaks=0:halt_on_error=1:abort_on_error=1"
        env["UBSAN_OPTIONS"] = "halt_on_error=1:abort_on_error=1"
        env["TSAN_OPTIONS"] = "halt_on_error=1:abort_on_error=1:second_deadlock_stack=1"
        proc = subprocess.run(
            [str(bin_path)],
            capture_output=True,
            text=True,
            timeout=60,
            env=env,
        )
        if proc.returncode != 0:
            return proc.returncode, [], (proc.stdout or "") + (proc.stderr or "")
        out_words: list[int] = []
        for line in proc.stdout.splitlines():
            if line.startswith("OUT:"):
                toks = line[len("OUT:") :].strip().split()
                out_words = [int(t, 10) & MASK64 for t in toks]
        return 0, out_words, ""


def run_metal_case(clangxx: str, case: dict[str, Any]) -> None:
    cid = case["id"]
    if case.get("roundtripScope") not in (None, "kernel", "block"):
        raise RuntimeError(f"[{cid}] unexpected roundtripScope: {case.get('roundtripScope')!r}")
    if not case.get("roundtripVerified", False):
        raise RuntimeError(f"[{cid}] in-Lean roundtripVerified flag is false")
    kname = case["kernelName"]
    grid_x = int(case["gridX"])
    group_x = int(case["groupX"])
    msl_text = case["mslText"]
    inputs = [[int(x) & MASK64 for x in arr] for arr in case["inputs"]]

    if case["kind"] == "valid":
        rc_a, got, err_a = _exec_metal_host_kernel(
            clangxx, msl_text, kname, grid_x, group_x, inputs, sanitizer="address,undefined"
        )
        if rc_a != 0:
            raise RuntimeError(f"[{cid}] ASan+UBSan failed on valid Metal kernel:\n{err_a}")
        expected = [int(x) & MASK64 for x in case["expected"]]
        if got != expected:
            raise RuntimeError(f"[{cid}] Metal C++17 mismatch: Lean={expected}, Host={got}")

        rc_t, got_t, err_t = _exec_metal_host_kernel(
            clangxx, msl_text, kname, grid_x, group_x, inputs, sanitizer="thread"
        )
        if rc_t != 0:
            raise RuntimeError(f"[{cid}] TSan detected race on valid Metal kernel:\n{err_t}")
        if got_t != expected:
            raise RuntimeError(f"[{cid}] Metal TSan output mismatch: Lean={expected}, Host={got_t}")

        mut_msl = case["negativeMutantMsl"]
        rc_m, got_m, err_m = _exec_metal_host_kernel(
            clangxx, mut_msl, kname, grid_x, group_x, inputs, sanitizer="address,undefined"
        )
        if rc_m != 0:
            raise RuntimeError(f"[{cid}] Metal negative mutant unexpectedly crashed:\n{err_m}")
        if got_m == expected:
            raise RuntimeError(
                f"[{cid}] Metal negative mutant ({case.get('negativeMutantReason')}) failed to diverge!"
            )
    else:
        trap_cls = case["trapClass"]
        san = "thread" if trap_cls == "dataRace" else "address,undefined"
        rc, _, _ = _exec_metal_host_kernel(
            clangxx, msl_text, kname, grid_x, group_x, inputs, sanitizer=san
        )
        if rc == 0:
            raise RuntimeError(
                f"[{cid}] Metal trap case ({trap_cls}) did NOT abort under -fsanitize={san}!"
            )


# ---------------------------------------------------------------------------
# 5. Suite Runner & Self-Tests
# ---------------------------------------------------------------------------


def execute_suite_payload(
    suite: dict[str, Any],
    *,
    backends: list[str] | None = None,
    lli_bin: str | None,
    opt_bin: str | None,
    clang_bin: str | None,
    clangxx_bin: str | None,
    ptxas_bin: str | None,
    tools_cache_dir: Path,
) -> dict[str, int]:
    want = set(backends) if backends is not None else {"llvm", "ptx", "stablehlo", "metal"}
    counts = {
        "llvm_valid": 0, "llvm_trap": 0,
        "ptx_valid": 0, "ptx_trap": 0,
        "stablehlo_valid": 0, "stablehlo_trap": 0,
        "metal_valid": 0, "metal_trap": 0,
    }

    llvm_cases = suite.get("llvmCases", []) if "llvm" in want else []
    if llvm_cases:
        if not lli_bin or not opt_bin or not clang_bin:
            raise RuntimeError(f"Missing LLVM tools: lli={lli_bin}, opt={opt_bin}, clang={clang_bin}")
        for c in llvm_cases:
            if c["kind"] == "valid":
                run_llvm_valid_case(lli_bin, opt_bin, c)
                counts["llvm_valid"] += 1
            else:
                rc = run_llvm_trap_case_native(clang_bin, opt_bin, c)
                if rc == 0:
                    raise RuntimeError(f"[{c['id']}] native ASan/UBSan binary exited 0 on {c['trapClass']}!")
                counts["llvm_trap"] += 1

    ptx_cases = suite.get("ptxCases", []) if "ptx" in want else []
    if ptx_cases:
        if not ptxas_bin:
            raise RuntimeError("Missing ptxas binary for PTX fuzz cases")
        for c in ptx_cases:
            run_ptx_case(ptxas_bin, c)
            counts["ptx_valid" if c["kind"] == "valid" else "ptx_trap"] += 1

    hlo_cases = suite.get("stablehloCases", []) if "stablehlo" in want else []
    if hlo_cases:
        gpu_diff.ensure_openxla_stablehlo(tools_cache_dir)
        for c in hlo_cases:
            run_stablehlo_case(tools_cache_dir, c)
            counts["stablehlo_valid" if c["kind"] == "valid" else "stablehlo_trap"] += 1

    metal_cases = suite.get("metalCases", []) if "metal" in want else []
    if metal_cases:
        if not clangxx_bin:
            raise RuntimeError("Missing clang++ binary for Metal fuzz cases")
        for c in metal_cases:
            run_metal_case(clangxx_bin, c)
            counts["metal_valid" if c["kind"] == "valid" else "metal_trap"] += 1

    return counts


class TargetIRFuzzSelfTests(unittest.TestCase):
    def test_ptx_strict_trap_classes(self) -> None:
        div0_ptx = (
            ".version 8.0\n.target sm_90\n.address_size 64\n"
            ".visible .entry k(.param .u64 param_out, .param .u64 param_in0, .param .u64 param_n) {\n"
            "  .reg .u64 %rd<3>;\n"
            "  mov.u64 %rd0, 9;\n  mov.u64 %rd1, 0;\n  div.u64 %rd2, %rd0, %rd1;\n  ret;\n}\n"
        )
        with self.assertRaises(PTXTrapError) as ctx:
            _run_ptx_buffers(div0_ptx, "k", 1, 1, [[1]])
        self.assertEqual(ctx.exception.trap_class, "divisionByZero")

        race_ptx = (
            ".version 8.0\n.target sm_90\n.address_size 64\n"
            ".visible .entry kr(.param .u64 param_out, .param .u64 param_in0, .param .u64 param_n) {\n"
            "  .shared .align 8 .u64 sh[2];\n  .reg .u32 %r<2>;\n  .reg .u64 %rd<3>;\n"
            "  mov.u32 %r0, %tid.x;\n  cvt.u64.u32 %rd0, %r0;\n"
            "  mov.u64 %rd1, sh;\n  st.shared.u64 [%rd1], %rd0;\n  ret;\n}\n"
        )
        with self.assertRaises(PTXTrapError) as ctx2:
            _run_ptx_buffers(race_ptx, "kr", 1, 2, [[1, 2]])
        self.assertEqual(ctx2.exception.trap_class, "dataRace")

    def test_llvm_native_asan_ubsan_trap(self) -> None:
        strict_tools = os.environ.get("TARGET_IR_FUZZ_STRICT_TOOLS", "").lower() == "true"
        clang_bin = find_clang_c()
        opt_bin = llvm_diff.find_llvm_tool(["opt-18", "opt-19", "opt"])
        if not clang_bin or not opt_bin:
            if strict_tools:
                self.fail(f"Required clang/opt missing under strict mode: clang={clang_bin}, opt={opt_bin}")
            self.skipTest("clang/opt not available")
        oob_case = {
            "id": "selftest_llvm_oob",
            "fnName": "f_oob",
            "roundtripVerified": True,
            "inputs": [11, 2],
            "irText": (
                'target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"\n'
                'target triple = "x86_64-unknown-linux-gnu"\n'
                "define ccc i64 @f_oob(i64 %a, i64 %b) {\n"
                "entry:\n"
                "  %slot = alloca i64, align 8\n"
                "  store i64 %a, ptr %slot, align 8\n"
                "  %oob = getelementptr inbounds i64, ptr %slot, i64 2\n"
                "  %r = load i64, ptr %oob, align 8\n"
                "  ret i64 %r\n"
                "}\n"
            ),
        }
        rc = run_llvm_trap_case_native(clang_bin, opt_bin, oob_case)
        self.assertNotEqual(rc, 0)

    def test_metal_tsan_and_asan_traps(self) -> None:
        strict_tools = os.environ.get("TARGET_IR_FUZZ_STRICT_TOOLS", "").lower() == "true"
        clangxx = gpu_diff.find_clangxx()
        if not clangxx:
            if strict_tools:
                self.fail("Required clang++ missing under strict mode")
            self.skipTest("clang++ not available")
        race_msl = (
            "#include <metal_stdlib>\nusing namespace metal;\n\n"
            "kernel void k_race(\n"
            "    device const ulong* in0 [[buffer(0)]],\n"
            "    device ulong* out [[buffer(1)]],\n"
            "    constant ulong& n [[buffer(2)]],\n"
            "    uint gid [[thread_position_in_grid]]\n"
            ") {\n"
            "    threadgroup ulong sh[2];\n"
            "    sh[0ULL] = in0[gid];\n"
            "    out[gid] = sh[0ULL];\n"
            "    return;\n"
            "}\n"
        )
        rc_race, _, _ = _exec_metal_host_kernel(
            clangxx, race_msl, "k_race", 1, 2, [[10, 20]], sanitizer="thread"
        )
        self.assertNotEqual(rc_race, 0)

    def test_cli_flags_and_fail_closed_validation(self) -> None:
        args_core = parse_args(["--core-bin", "/tmp/lean-native-core", "--seeds", "4"])
        self.assertEqual(args_core.lean_bin, Path("/tmp/lean-native-core"))
        args_lean = parse_args(["--lean-bin", "/tmp/lean-native", "--seeds", "8"])
        self.assertEqual(args_lean.lean_bin, Path("/tmp/lean-native"))
        self.assertEqual(main(["--seeds", "0"]), 2)
        self.assertEqual(main(["--seeds", "-1"]), 2)
        self.assertEqual(main(["--backends", "   "]), 2)
        self.assertEqual(main(["--backends", "llvm,unknown_backend"]), 2)


VALID_BACKENDS = ("llvm", "ptx", "stablehlo", "metal")


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument(
        "--core-bin",
        "--lean-bin",
        dest="lean_bin",
        type=Path,
        help="Path to `lean-native-core` or `lean-native`",
    )
    p.add_argument("--suite-json", type=Path, help="Pre-generated `target-ir-fuzz-suite` JSON file")
    p.add_argument("--seed-start", type=int, default=0)
    p.add_argument("--seeds", type=int, default=16)
    p.add_argument("--backends", type=str, default="llvm,ptx,stablehlo,metal")
    p.add_argument(
        "--tools-cache-dir",
        type=Path,
        default=Path(os.environ.get("GPU_TPU_TOOLS_CACHE", "/tmp/turbo-lean-gpu-tpu-tools")),
    )
    p.add_argument("--ensure-tools", action="store_true", help="Bootstrap ptxas + OpenXLA stablehlo wheels")
    p.add_argument("--self-test", action="store_true", help="Run built-in unit self-tests and exit")
    return p.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    if args.self_test:
        suite = unittest.defaultTestLoader.loadTestsFromTestCase(TargetIRFuzzSelfTests)
        ok = unittest.TextTestRunner(verbosity=2).run(suite).wasSuccessful()
        return 0 if ok else 1

    backends = [b.strip() for b in args.backends.split(",") if b.strip()]
    unknown = [b for b in backends if b not in VALID_BACKENDS]
    if not backends or unknown or args.seeds <= 0:
        print(
            f"[target-ir-fuzz] ERROR: invalid non-empty fuzz configuration required "
            f"(seeds={args.seeds}, backends={backends}, unknown={unknown})",
            file=sys.stderr,
        )
        return 2

    if args.ensure_tools and ("ptx" in backends or "stablehlo" in backends):
        gpu_diff.ensure_gpu_tpu_tools(args.tools_cache_dir)

    if args.suite_json:
        payload = json.loads(args.suite_json.read_text(encoding="utf-8"))
    else:
        if not args.lean_bin or not args.lean_bin.is_file():
            raise RuntimeError(f"--core-bin / --lean-bin not found: {args.lean_bin}")
        self_chk = subprocess.run(
            [str(args.lean_bin), "target-ir-fuzz-suite", "--self-test"],
            capture_output=True,
            text=True,
            timeout=120,
        )
        if self_chk.returncode != 0:
            raise RuntimeError(
                f"target-ir-fuzz-suite --self-test failed:\n{self_chk.stdout}\n{self_chk.stderr}"
            )
        gen = subprocess.run(
            [
                str(args.lean_bin),
                "target-ir-fuzz-suite",
                "--seed-start",
                str(args.seed_start),
                "--seeds",
                str(args.seeds),
                "--backends",
                ",".join(backends),
            ],
            capture_output=True,
            text=True,
            timeout=180,
        )
        if gen.returncode != 0:
            raise RuntimeError(f"target-ir-fuzz-suite failed:\n{gen.stderr}")
        payload = json.loads(gen.stdout)

    lli_bin = llvm_diff.find_llvm_tool(["lli-18", "lli-19", "lli", "lli-17", "lli-20"])
    opt_bin = llvm_diff.find_llvm_tool(["opt-18", "opt-19", "opt", "opt-17", "opt-20"])
    clang_bin = find_clang_c()
    clangxx_bin = gpu_diff.find_clangxx()
    ptxas_bin = gpu_diff.find_ptxas(args.tools_cache_dir)

    counts = execute_suite_payload(
        payload,
        backends=backends,
        lli_bin=lli_bin,
        opt_bin=opt_bin,
        clang_bin=clang_bin,
        clangxx_bin=clangxx_bin,
        ptxas_bin=ptxas_bin,
        tools_cache_dir=args.tools_cache_dir,
    )
    print(
        "[target-ir-fuzz] PASSED "
        f"(seeds={payload.get('seeds')}, "
        + ", ".join(f"{k}={v}" for k, v in counts.items())
        + ")"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
