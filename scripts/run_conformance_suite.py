#!/usr/bin/env python3
"""Run tiered differential conformance (`--tier` / `--tiers`), sanitizer checks, and certificate/plugin gates.

The former Python reference formulas and C runtime stubs were not independent
Lean execution. They are deliberately excluded from acceptance. Full loop
(`seqFor`), external ecosystem Lake packages beyond `Batteries` (`SciLean`,
`ArkLib`), and hardware target qualification remain open. Tier `C1` runs the
eight authored 3-way fixtures and, with `--c1-upstream` (or
`TURBO_C1_UPSTREAM=1`), a manifest-driven 250-program upstream corpus
(`scripts/c1_corpus_manifest.json`, pinned `leanprover/lean4` @ tag `v4.35.0`,
provisioned like the C2 external arm by `git fetch --depth 1` into
`TURBO_LEAN_HOME/c1-upstream` and gated on program count, per-file sha256 at
the pin, and matrix-construct coverage before execution; frontend-rejected
programs are recorded fail-closed with their syntactic matrix constructs,
never silently dropped). Tier `C2` runs 3-way multi-module Lake package differential
conformance (`lean -c` + `leanc`, `lean-native emit-lnir --wire` + `eval-lnir`
+ `validate-tv`, and `compile-llvm` + `clang` under ASan/UBSan) when
provisioned via `TURBO_C2_PACKAGES_DIR` (or `--c2-packages-dir`, including
`auto` for `verification/c2-lake-packages`), and fails closed
(`BLOCKED_MISSING_DEPENDENCY`) otherwise. With `--c2-external` (or
`TURBO_C2_EXTERNAL=1`; the nightly workflow's mode), Tier `C2` additionally
runs driver fixtures against pinned external ecosystem packages
(`leanprover-community/batteries`), each pinned by `(repo_url, commit_sha,
lean_toolchain)` and provisioned by `git fetch` + `lake build <lib>:static`
into `TURBO_LEAN_HOME/c2-external` (default `~/.cache/turbo-lean/c2-external`),
failing closed when provisioning or the recorded pin check fails. Tier `C3` runs the `R1`–`R6`
cross-regime holdout portfolio and adversarial `.olean` rejection battery
through pinned upstream `leanprover/con-leche --verified` when provisioned via
`TURBO_CON_LECHE_BIN` (or `--con-leche-bin`), and fails closed
(`BLOCKED_MISSING_DEPENDENCY`) otherwise.
arm64 (aarch64) qualification: the differential tiers, sanitizer legs, and C2/C4 clang gates run natively on arm64 hosts via host-arch emission; the CUDA/PTX leg and the pinned x86_64-only artifacts (ptxas wheel, StableHLO wheels, cpython-standalone) skip there with named reasons, and hardware target qualification remains open on arm64 exactly as on x86_64.
"""
from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
import shutil
import struct
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any

import build_c1_corpus_manifest as c1_corpus
import fuzz_lcnf_conformance as fuzz

ROOT = Path(__file__).resolve().parent.parent
CORE = ROOT / "lean/.lake/build/bin/lean-native-core"
PINNED_CON_LECHE_REV = "501589f5680d9599dee1bcef30a420bc8924c490"
PINNED_CON_LECHE_TOOLCHAIN = "leanprover/lean4:v4.35.0"
BRIDGE_CON_LECHE_BIN = (
    ROOT
    / "verification/con-leche-bridge/.lake/packages/con-leche/.lake/build/bin/con-leche"
)
DEFAULT_C2_PACKAGES_DIR = ROOT / "verification/c2-lake-packages"
C2_LAKE_PACKAGE_SPECS: tuple[tuple[str, tuple[str, ...], tuple[str, ...]], ...] = (
    ("C2BitwiseScan", ("Swar", "Scan"), ("c2_bitwise_scan_digest", "c2_swar_sip_mix")),
    ("C2FieldButterfly", ("Field", "Butterfly"), ("c2_babybear_radix4", "c2_gf2_clmul_tower")),
    ("C2ProtocolMachine", ("Types", "Transition"), ("c2_protocol_step6", "c2_usize_stencil_clamp")),
    ("C2CryptoSipHash", ("SipRound", "Mac"), ("c2_siphash24_word", "c2_chacha_quarter_mix")),
)
# Tier C2 external ecosystem packages, pinned by (repo_url, commit_sha,
# lean_toolchain) per roadmap/CONFORMANCE_SUITE.md; the lean_toolchain of every
# pin is PINNED_CON_LECHE_TOOLCHAIN (asserted against each fresh clone).
# `batteries` is upstream tag `v4.35.0`.
C2_EXTERNAL_DEPS: dict[str, tuple[str, str, str]] = {
    # dep key -> (repo_url, commit_sha, lake static-lib/olean root name)
    "batteries": (
        "https://github.com/leanprover-community/batteries",
        "66e469188fe07963e5cf666c7d4433f45b8131c5",
        "Batteries",
    ),
}
# (package fixture name, submodules, @[export] kernels, external dep keys).
# Opt-in via --c2-external / TURBO_C2_EXTERNAL=1 (the nightly workflow runs it):
# each driver fixture compiles against the pinned dep's oleans and links its
# static archive, so a cold cache needs one network fetch per pin.
C2_EXTERNAL_LAKE_PACKAGE_SPECS: tuple[tuple[str, tuple[str, ...], tuple[str, ...], tuple[str, ...]], ...] = (
    ("C2BatteriesDriver", ("Scan", "Fold"), ("c2_batteries_scan_mix", "c2_batteries_fold_rank"), ("batteries",)),
)
C2_TEST_VECTORS: tuple[int, ...] = (
    0,
    1,
    42,
    0x00000000000000AA,
    0x41393A0A7E7D03AA,
    0x0123456789ABCDEF,
    0x8000000000000001,
    0xFFFFFFFFFFFFFFFF,
)

VALID_TIERS = ("C1", "C2", "C3", "C4")
C1_CORPUS_TESTS = (
    "ScalarFrontend.test_small_width_comparisons",
    "ScalarFrontend.test_narrow_wrapping_arithmetic_shifts_and_div_zero",
    "ScalarFrontend.test_join_point_param_swap_and_nested_helper_inlining",
    "ScalarFrontend.test_chained_boolean_join_points_and_tuple_helpers",
    "ScalarFrontend.test_unsigned_casts_and_input_dependent_boolean_branches",
    "ScalarFrontend.test_stage1b_narrow_abi_usize_bool_enums_joinpoints_and_divmod_zero",
    "ScalarFrontend.test_c1_bitwise_rotations_clmul_swar_and_diamond_merges",
    "ScalarFrontend.test_c1_multi_enum_state_machine_and_crc_polynomial_fold",
)

C3_HOLDOUT_REGIMES: tuple[tuple[str, str, str], ...] = (
    (
        "R1",
        "HoldoutR1Algebra",
        """/- Regime R1: Commutative semiring / monoid algebraic identities. -/
structure CommMonoidCarrier (α : Type u) where
  op : α → α → α
  one : α
  op_assoc : ∀ a b c, op (op a b) c = op a (op b c)
  op_comm : ∀ a b, op a b = op b a
  one_op : ∀ a, op one a = a

def natAddMonoid : CommMonoidCarrier Nat where
  op := Nat.add
  one := 0
  op_assoc := Nat.add_assoc
  op_comm := Nat.add_comm
  one_op := Nat.zero_add

theorem r1_four_way_reassoc {α : Type u} (M : CommMonoidCarrier α) (a b c d : α) :
    M.op (M.op a b) (M.op c d) = M.op (M.op a c) (M.op b d) := by
  rw [M.op_assoc a b (M.op c d)]
  rw [← M.op_assoc b c d, M.op_comm b c, M.op_assoc c b d]
  rw [← M.op_assoc a c (M.op b d)]

theorem r1_nat_instance (x y z w : Nat) :
    (x + y) + (z + w) = (x + z) + (y + w) :=
  r1_four_way_reassoc natAddMonoid x y z w
""",
    ),
    (
        "R2",
        "HoldoutR2Analysis",
        """/- Regime R2: Order bounds, discrete Lipschitz / triangle inequalities. -/
def natDist (a b : Nat) : Nat := (a - b) + (b - a)

theorem r2_natDist_self (a : Nat) : natDist a a = 0 := by
  simp [natDist]

theorem r2_natDist_symm (a b : Nat) : natDist a b = natDist b a := by
  simp [natDist, Nat.add_comm]

theorem r2_monotone_step_bound (a b k : Nat) (h : a ≤ b) :
    a + k ≤ b + k ∧ k + a ≤ k + b :=
  ⟨Nat.add_le_add_right h k, Nat.add_le_add_left h k⟩
""",
    ),
    (
        "R3",
        "HoldoutR3Combinatorics",
        """/- Regime R3: Finite combinatorics, list reversals, and length invariants. -/
def pairSwap {α β : Type u} (p : α × β) : β × α := (p.2, p.1)

theorem r3_pairSwap_involutive {α β : Type u} (p : α × β) :
    pairSwap (pairSwap p) = p := by
  cases p
  rfl

theorem r3_append_length_invariant {α : Type u} (xs ys zs : List α) :
    (xs ++ ys ++ zs).length = xs.length + (ys.length + zs.length) := by
  simp [List.length_append, Nat.add_assoc]
""",
    ),
    (
        "R4",
        "HoldoutR4Foundations",
        """/- Regime R4: Higher-universe indexed inductives and quotient soundness lifts. -/
inductive TermTree (α : Type u) : Nat → Type u where
  | leaf : α → TermTree α 0
  | node : {n : Nat} → TermTree α n → TermTree α n → TermTree α (n + 1)

def treeDepth {α : Type u} {n : Nat} (_ : TermTree α n) : Nat := n

theorem r4_node_depth {α : Type u} {n : Nat} (l r : TermTree α n) :
    treeDepth (TermTree.node l r) = treeDepth l + 1 := rfl

def modTwoRel (a b : Nat) : Prop := a % 2 = b % 2

def parityLift : Quot modTwoRel → Nat :=
  Quot.lift (fun n => n % 2) (fun _ _ h => h)

theorem r4_quot_parity_sound (a b : Nat) (h : modTwoRel a b) :
    parityLift (Quot.mk modTwoRel a) = parityLift (Quot.mk modTwoRel b) := by
  exact congrArg parityLift (Quot.sound h)
""",
    ),
    (
        "R5",
        "HoldoutR5SystemsBitwise",
        """/- Regime R5: Verified systems & fixed-width UInt64 XOR involutive masking. -/
def xorCipher (word key : UInt64) : UInt64 :=
  word ^^^ key

theorem r5_uint64_xor_roundtrip (w k : UInt64) :
    xorCipher (xorCipher w k) k = w := by
  simp [xorCipher, UInt64.xor_assoc, UInt64.xor_self, UInt64.xor_zero]
""",
    ),
    (
        "R6",
        "HoldoutR6StencilPhysics",
        """/- Regime R6: 1D discrete conservation / telescoping stencil invariant. -/
def stencilFluxSum : List Nat → Nat
  | [] => 0
  | x :: xs => x + stencilFluxSum xs

theorem r6_stencilFluxSum_append (xs ys : List Nat) :
    stencilFluxSum (xs ++ ys) = stencilFluxSum xs + stencilFluxSum ys := by
  induction xs with
  | nil => simp [stencilFluxSum]
  | cons x xs ih =>
    simp [stencilFluxSum, ih, Nat.add_assoc]
""",
    ),
)


def parse_tiers(raw_tiers: list[str] | None) -> list[str]:
    if not raw_tiers:
        return ["C4"]
    selected: list[str] = []
    for raw in raw_tiers:
        for item in raw.split(","):
            tier = item.strip().upper()
            if not tier:
                continue
            if tier not in VALID_TIERS:
                raise ValueError(f"Unknown conformance tier '{item}'; expected subset of {','.join(VALID_TIERS)}")
            if tier not in selected:
                selected.append(tier)
    if not selected:
        raise ValueError("At least one non-empty conformance tier is required")
    return selected


def command_json(*args: str) -> dict[str, Any]:
    result = subprocess.run([str(CORE), *args], cwd=ROOT, check=True,
                            capture_output=True, text=True)
    value = json.loads(result.stdout)
    if not isinstance(value, dict):
        raise RuntimeError("Expected a structured gate report")
    return value


def resolve_con_leche_bin(cli_bin: str | None) -> Path | None:
    raw = (cli_bin if cli_bin is not None else os.environ.get("TURBO_CON_LECHE_BIN", "")).strip()
    if not raw:
        return None
    if raw == "auto":
        cand = BRIDGE_CON_LECHE_BIN
    else:
        cand = Path(raw)
    if cand.is_file() and os.access(cand, os.X_OK):
        return cand.resolve()
    return None


def resolve_c2_packages_dir(cli_dir: str | None) -> tuple[str, Path | None]:
    raw = (cli_dir if cli_dir is not None else os.environ.get("TURBO_C2_PACKAGES_DIR", "")).strip()
    if not raw:
        return "", None
    cand = DEFAULT_C2_PACKAGES_DIR if raw == "auto" else Path(raw)
    if cand.is_dir():
        return raw, cand.resolve()
    return raw, None


def c2_external_cache_root() -> Path:
    raw_home = os.environ.get("TURBO_LEAN_HOME", "").strip()
    base = Path(raw_home) if raw_home else Path.home() / ".cache" / "turbo-lean"
    return base / "c2-external"


def ensure_c2_external_dep(dep_key: str) -> dict[str, Any]:
    """Provision one pinned external ecosystem package into the persistent cache.

    Clones `repo_url` at `commit_sha` (one shallow fetch on a cold cache),
    asserts its `lean-toolchain` equals the suite's C2 pin, and runs
    `lake build <lib>:static` once; a stamp file records the provisioned rev so
    warm runs (and the nightly workflow's actions/cache restore) are offline.
    Returns `{"ok": True, "oleanDir": ..., "staticLibs": [...]}` or
    `{"ok": False, "reason": ...}` (the caller fails closed)."""
    repo_url, rev, lib_name = C2_EXTERNAL_DEPS[dep_key]
    dep_dir = c2_external_cache_root() / f"{dep_key}-{rev[:12]}"
    stamp = dep_dir / ".turbo-c2-provisioned"
    base: dict[str, Any] = {
        "dep": dep_key, "repoUrl": repo_url, "rev": rev,
        "toolchain": PINNED_CON_LECHE_TOOLCHAIN, "libName": lib_name, "path": str(dep_dir),
    }
    env = fuzz.pinned_toolchain_env(toolchain=PINNED_CON_LECHE_TOOLCHAIN)
    env["PATH"] = os.pathsep.join([str(Path.home() / ".elan" / "bin"), env.get("PATH", "")])
    try:
        if not (stamp.is_file() and stamp.read_text(encoding="utf-8").strip() == rev):
            dep_dir.mkdir(parents=True, exist_ok=True)
            if not (dep_dir / ".git").is_dir():
                subprocess.run(["git", "init", "-q", str(dep_dir)], check=True, capture_output=True, text=True)
            subprocess.run(["git", "-C", str(dep_dir), "fetch", "-q", "--depth", "1", repo_url, rev],
                           check=True, capture_output=True, text=True)
            subprocess.run(["git", "-C", str(dep_dir), "checkout", "-q", "--detach", rev],
                           check=True, capture_output=True, text=True)
            dep_tc = (dep_dir / "lean-toolchain").read_text(encoding="utf-8").strip()
            if dep_tc != PINNED_CON_LECHE_TOOLCHAIN:
                return {**base, "ok": False,
                        "reason": f"pinned rev declares lean-toolchain {dep_tc!r}, expected {PINNED_CON_LECHE_TOOLCHAIN!r}"}
            subprocess.run(["lake", "build", f"{lib_name}:static"], cwd=dep_dir, env=env,
                           check=True, capture_output=True, text=True)
        lib_flat = dep_dir / ".lake" / "build" / "lib"
        lib_lean = lib_flat / "lean"
        olean_dir = lib_lean if (lib_lean / f"{lib_name}.olean").is_file() else lib_flat
        static_libs = sorted(str(p) for p in lib_flat.glob(f"**/lib*{lib_name}.a"))
        if not (olean_dir / f"{lib_name}.olean").is_file() or not static_libs:
            return {**base, "ok": False,
                    "reason": f"built artifacts missing ({lib_name}.olean / lib*{lib_name}.a under {lib_flat})"}
        stamp.write_text(rev + "\n", encoding="utf-8")
        return {**base, "ok": True, "oleanDir": str(olean_dir), "staticLibs": static_libs}
    except subprocess.CalledProcessError as err:
        return {**base, "ok": False,
                "reason": f"`{' '.join(str(c) for c in err.cmd)}` failed with exit {err.returncode}",
                "stderrTail": (err.stderr or "")[-1200:]}
    except OSError as err:
        return {**base, "ok": False, "reason": str(err)}


def find_v435_lean_and_init() -> tuple[Path, Path] | None:
    candidates: list[str | None] = [
        fuzz.find_lean_binary(),
        shutil.which("lean"),
        *fuzz.toolchain_bin_candidates("lean", PINNED_CON_LECHE_TOOLCHAIN),
    ]
    for elan_cand in [shutil.which("elan"), "/var/lib/orb-node/work/caches/elan/bin/elan"]:
        if elan_cand and Path(elan_cand).is_file() and os.access(elan_cand, os.X_OK):
            try:
                out = subprocess.run(
                    [elan_cand, "which", "lean"],
                    cwd=ROOT / "verification" / "con-leche-bridge"
                    if (ROOT / "verification" / "con-leche-bridge").is_dir()
                    else ROOT,
                    env=fuzz.pinned_toolchain_env(toolchain=PINNED_CON_LECHE_TOOLCHAIN),
                    check=True,
                    capture_output=True,
                    text=True,
                ).stdout.strip()
                if out:
                    candidates.insert(0, out)
            except (OSError, subprocess.SubprocessError):
                pass
    seen: set[str] = set()
    for cand in candidates:
        if not cand or cand in seen:
            continue
        seen.add(cand)
        p = Path(cand)
        if not (p.is_file() and os.access(p, os.X_OK)):
            continue
        try:
            ver = subprocess.run(
                [str(p), "--version"],
                cwd=ROOT / "lean" if (ROOT / "lean").is_dir() else ROOT,
                env=fuzz.pinned_toolchain_env(toolchain=PINNED_CON_LECHE_TOOLCHAIN),
                check=True,
                capture_output=True,
                text=True,
            ).stdout
            if fuzz.toolchain_version_token(PINNED_CON_LECHE_TOOLCHAIN) not in ver:
                continue
            prefix = subprocess.run(
                [str(p), "--print-prefix"],
                cwd=ROOT / "lean" if (ROOT / "lean").is_dir() else ROOT,
                env=fuzz.pinned_toolchain_env(toolchain=PINNED_CON_LECHE_TOOLCHAIN),
                check=True,
                capture_output=True,
                text=True,
            ).stdout.strip()
            lean_bin = Path(prefix) / "bin" / "lean"
            init_dir = Path(prefix) / "lib" / "lean"
            if lean_bin.is_file() and (init_dir / "Init.olean").is_file():
                return lean_bin, init_dir
        except (OSError, subprocess.SubprocessError):
            continue
    return None


def corrupt_private_theorem_proof(olean_dir: Path, mod_name: str, thm_suffix: str, replacement_const: str) -> None:
    parts: dict[str, tuple[int, bytearray]] = {}
    for ext in ("olean", "olean.server", "olean.private"):
        fp = olean_dir / f"{mod_name}.{ext}"
        if fp.is_file():
            buf = bytearray(fp.read_bytes())
            base_addr = struct.unpack_from("<Q", buf, 80)[0]
            parts[ext] = (base_addr, buf)

    def at(addr: int) -> tuple[bytearray, int]:
        for base_addr, buf in parts.values():
            off = addr - base_addr
            if 0 <= off < len(buf):
                return buf, off
        raise RuntimeError(f"Address {addr:#x} outside `.olean` parts for {mod_name}")

    def fld(addr: int, idx: int) -> int:
        buf, off = at(addr)
        return struct.unpack_from("<Q", buf, off + 8 + 8 * idx)[0]

    def setfld(addr: int, idx: int, val: int) -> None:
        buf, off = at(addr)
        struct.pack_into("<Q", buf, off + 8 + 8 * idx, val)

    def decode_name(addr: int) -> str:
        if addr == 1:
            return ""
        prefix = decode_name(fld(addr, 0))
        b0, o0 = at(addr)
        if b0[o0 + 7] == 2:
            seg = str(fld(addr, 1) >> 1)
        else:
            sb, so = at(fld(addr, 1))
            sz = struct.unpack_from("<Q", sb, so + 8)[0]
            seg = sb[so + 32 : so + 32 + sz - 1].decode("utf-8")
        return f"{prefix}.{seg}" if prefix else seg

    def const_map(ext: str) -> dict[str, int]:
        _, buf = parts[ext]
        arr_buf, arr_off = at(fld(struct.unpack_from("<Q", buf, 88)[0], 2))
        count = struct.unpack_from("<Q", arr_buf, arr_off + 8)[0]
        out: dict[str, int] = {}
        for i in range(count):
            c_ptr = struct.unpack_from("<Q", arr_buf, arr_off + 24 + 8 * i)[0]
            cname = decode_name(fld(fld(fld(c_ptr, 0), 0), 0))
            out[cname] = c_ptr
        return out

    priv_consts = const_map("olean.private")
    target_names = [k for k in priv_consts if k.endswith(thm_suffix)]
    if len(target_names) != 1 or replacement_const not in priv_consts:
        raise RuntimeError(
            f"Expected unique `{thm_suffix}` and `{replacement_const}` in {mod_name}.olean.private; got {list(priv_consts)}"
        )
    thm_val_ptr = fld(priv_consts[target_names[0]], 0)
    repl_val_expr_ptr = fld(priv_consts[replacement_const], 0)
    setfld(thm_val_ptr, 1, fld(repl_val_expr_ptr, 1))
    for ext, (_, buf) in parts.items():
        (olean_dir / f"{mod_name}.{ext}").write_bytes(buf)


def run_c3_corpus(con_leche_bin_arg: str | None) -> dict[str, Any]:
    con_leche_bin = resolve_con_leche_bin(con_leche_bin_arg)
    if con_leche_bin is None:
        return {
            "tier": "C3",
            "ok": False,
            "status": "BLOCKED_MISSING_DEPENDENCY",
            "reason": (
                "Cross-regime holdouts (R1-R6) require provisioned upstream leanprover/con-leche "
                f"binary via TURBO_CON_LECHE_BIN or --con-leche-bin (expected rev {PINNED_CON_LECHE_REV})"
            ),
        }
    lean_env = find_v435_lean_and_init()
    if lean_env is None:
        return {
            "tier": "C3",
            "ok": False,
            "status": "BLOCKED_MISSING_DEPENDENCY",
            "reason": f"Lean toolchain {PINNED_CON_LECHE_TOOLCHAIN} (`Init.olean`) not found for C3 `.olean` compilation",
        }
    lean_bin, init_dir = lean_env
    jobs = max(1, min(4, os.cpu_count() or 2))

    with tempfile.TemporaryDirectory(prefix="turbo_c3_con_leche_") as tmp:
        tmp_path = Path(tmp)
        holdout_dir = tmp_path / "holdouts"
        adv_dir = tmp_path / "adversarial"
        scratch_tmp = tmp_path / "scratch"
        holdout_dir.mkdir(parents=True, exist_ok=True)
        adv_dir.mkdir(parents=True, exist_ok=True)
        scratch_tmp.mkdir(parents=True, exist_ok=True)

        sub_env = fuzz.pinned_toolchain_env(toolchain=PINNED_CON_LECHE_TOOLCHAIN)
        sub_env["TMPDIR"] = str(scratch_tmp)

        compiled_holdouts: list[dict[str, Any]] = []
        root_modules: list[str] = []
        for regime_id, mod_name, src_code in C3_HOLDOUT_REGIMES:
            src_file = holdout_dir / f"{mod_name}.lean"
            olean_file = holdout_dir / f"{mod_name}.olean"
            src_file.write_text(src_code, encoding="utf-8")
            comp = subprocess.run(
                [str(lean_bin), "-R", str(holdout_dir), "-o", str(olean_file), str(src_file)],
                cwd=holdout_dir,
                env=sub_env,
                capture_output=True,
                text=True,
            )
            if comp.returncode != 0 or not olean_file.is_file():
                return {
                    "tier": "C3",
                    "ok": False,
                    "status": "holdout_compilation_failed",
                    "regime": regime_id,
                    "module": mod_name,
                    "stderr": ((comp.stdout or "") + "\n" + (comp.stderr or "")).strip()[-1200:],
                }
            compiled_holdouts.append(
                {
                    "regime": regime_id,
                    "module": mod_name,
                    "oleanSha256": hashlib.sha256(olean_file.read_bytes()).hexdigest(),
                }
            )
            root_modules.append(mod_name)

        holdout_search_path = f"{holdout_dir}:{init_dir}"
        holdout_cmd = [
            str(con_leche_bin),
            "--verified",
            f"--jobs={jobs}",
            "--olean",
            f"--search-path={holdout_search_path}",
            "--",
            *root_modules,
        ]
        holdout_res = subprocess.run(holdout_cmd, cwd=holdout_dir, env=sub_env, capture_output=True, text=True)
        holdouts_accepted = holdout_res.returncode == 0 and "accepted " in (holdout_res.stdout or "")

        # Compile adversarial `.olean` fixtures modeled on upstream `con-leche/tests/olean.sh`.
        adv_sources = {
            "Tiny": (
                "module\nprelude\npublic section\ninductive T : Type where\n  | a\n  | b\nend\n"
            ),
            "ClashA": (
                "module\nprelude\npublic import Tiny\npublic section\ndef clash : T := T.a\nend\n"
            ),
            "ClashB": (
                "module\nprelude\npublic import Tiny\npublic section\ndef clash : T := T.b\nend\n"
            ),
            "NpAx": (
                "module\nprelude\npublic section\nset_option genCtorIdx false in\n"
                "inductive Nat where\n  | zero : Nat\n  | succ (n : Nat) : Nat\n"
                "axiom Nat.div : Nat → Nat → Nat\nend\n"
            ),
            "PrivUnused": (
                "module\nprelude\npublic section\ninductive Yes : Prop where\n  | intro\n"
                "inductive Two : Type where\n  | a\n  | b\ndef two : Two := Two.a\nend\n"
                "private theorem secret : Yes := Yes.intro\n"
            ),
        }
        adv_env = dict(sub_env)
        adv_env["LEAN_PATH"] = str(adv_dir)
        for mod_name, src_txt in adv_sources.items():
            sf = adv_dir / f"{mod_name}.lean"
            of = adv_dir / f"{mod_name}.olean"
            sf.write_text(src_txt, encoding="utf-8")
            cp = subprocess.run(
                [str(lean_bin), "-R", str(adv_dir), "-o", str(of), str(sf)],
                cwd=adv_dir,
                env=adv_env,
                capture_output=True,
                text=True,
            )
            if cp.returncode != 0 or not of.is_file():
                return {
                    "tier": "C3",
                    "ok": False,
                    "status": "adversarial_fixture_compile_failed",
                    "module": mod_name,
                    "stderr": (cp.stderr or "")[-1200:],
                }

        corrupt_dir = tmp_path / "corrupt_priv"
        shutil.copytree(adv_dir, corrupt_dir)
        corrupt_private_theorem_proof(corrupt_dir, "PrivUnused", ".secret", "two")

        adversarial_checks: list[dict[str, Any]] = []
        adv_matrix: list[tuple[str, int, Path, list[str]]] = [
            ("conflicting_constants_ClashA_ClashB", 1, adv_dir, ["ClashA", "ClashB"]),
            ("spoofed_nat_div_axiom_NpAx", 1, adv_dir, ["NpAx"]),
            ("unreferenced_private_theorem_clean_control", 0, adv_dir, ["PrivUnused"]),
            ("corrupted_private_theorem_proof_PrivUnused", 1, corrupt_dir, ["PrivUnused"]),
            ("missing_module_fail_closed", 3, adv_dir, ["NoSuchModuleInC3"]),
        ]
        for case_name, expected_rc, sp_dir, mods in adv_matrix:
            rc_res = subprocess.run(
                [
                    str(con_leche_bin),
                    "--verified",
                    "--jobs=2",
                    "--olean",
                    f"--search-path={sp_dir}",
                    "--",
                    *mods,
                ],
                cwd=sp_dir,
                env=sub_env,
                capture_output=True,
                text=True,
            )
            adversarial_checks.append(
                {
                    "case": case_name,
                    "expectedExit": expected_rc,
                    "actualExit": rc_res.returncode,
                    "matched": rc_res.returncode == expected_rc,
                }
            )

        adv_all_matched = all(c["matched"] for c in adversarial_checks)
        ok = holdouts_accepted and adv_all_matched
        return {
            "tier": "C3",
            "ok": ok,
            "status": "passed_con_leche_verified_holdouts" if ok else "failed_con_leche_holdouts",
            "conLecheBin": str(con_leche_bin),
            "conLecheRev": PINNED_CON_LECHE_REV,
            "leanToolchain": PINNED_CON_LECHE_TOOLCHAIN,
            "jobs": jobs,
            "regimesChecked": [h["regime"] for h in compiled_holdouts],
            "holdoutModules": compiled_holdouts,
            "holdoutExitCode": holdout_res.returncode,
            "holdoutStdoutTail": (holdout_res.stdout or "").strip()[-400:],
            "holdoutStderrTail": (holdout_res.stderr or "").strip()[-800:],
            "adversarialChecks": adversarial_checks,
        }


def run_c2_corpus(cli_dir: str | None, asan: bool, ubsan: bool, external: bool = False) -> dict[str, Any]:
    raw_spec, pkgs_root = resolve_c2_packages_dir(cli_dir)
    if not raw_spec or pkgs_root is None:
        return {
            "tier": "C2",
            "ok": False,
            "status": "BLOCKED_MISSING_DEPENDENCY",
            "requestedPackagesDir": raw_spec or None,
            "reason": (
                "Ecosystem Lake codegen corpus requires --c2-packages-dir / TURBO_C2_PACKAGES_DIR "
                "(use `auto` for verification/c2-lake-packages; pinned external Batteries runs with "
                "--c2-external / TURBO_C2_EXTERNAL=1; external SciLean/ArkLib remain open)"
            ),
        }

    engines = fuzz.probe_engines(asan=asan, ubsan=ubsan)
    if not (engines["stock_lean_c"] and engines["lnir_eval"] and engines["c_abi_llvm"]):
        return {
            "tier": "C2",
            "ok": False,
            "status": "incomplete_missing_engine",
            "packagesDir": str(pkgs_root),
            "asan": asan,
            "ubsan": ubsan,
            "engines": {
                "stock_lean_c": engines["stock_lean_c"],
                "lnir_validate_tv": engines["lnir_eval"],
                "c_abi_llvm": engines["c_abi_llvm"],
            },
        }

    lean_bin = engines["lean_bin"]
    core_bin = engines["core_bin"]
    full_bin = engines["full_bin"]
    clang_bin = engines["clang_bin"]
    extra_inc = fuzz.clang_extra_flags(clang_bin)
    lean_prefix = Path(
        subprocess.run([lean_bin, "--print-prefix"], env=fuzz.pinned_toolchain_env(toolchain=PINNED_CON_LECHE_TOOLCHAIN),
                       check=True, capture_output=True, text=True).stdout.strip()
    )
    leanc_bin = str(lean_prefix / "bin" / "leanc")

    specs: list[tuple[str, tuple[str, ...], tuple[str, ...], tuple[str, ...]]] = [
        (name, submods, exports, ()) for (name, submods, exports) in C2_LAKE_PACKAGE_SPECS
    ]
    external_dep_infos: dict[str, dict[str, Any]] = {}
    if external:
        specs.extend(C2_EXTERNAL_LAKE_PACKAGE_SPECS)
        for dep_key in sorted({k for (_, _, _, dks) in C2_EXTERNAL_LAKE_PACKAGE_SPECS for k in dks}):
            info = ensure_c2_external_dep(dep_key)
            if info.get("ok") is not True:
                return {
                    "tier": "C2",
                    "ok": False,
                    "status": "c2_external_dependency_unprovisioned",
                    "packagesDir": str(pkgs_root),
                    "externalDep": info,
                }
            external_dep_infos[dep_key] = info

    package_reports: list[dict[str, Any]] = []
    mismatches: list[dict[str, Any]] = []
    total_cases = 0
    total_live_objs = 0

    with tempfile.TemporaryDirectory(prefix="turbo_c2_lake_") as tmp:
        tmp_root = Path(tmp)
        for pkg_name, submods, exports, dep_keys in specs:
            src_pkg = pkgs_root / pkg_name
            req_files = [
                src_pkg / "lakefile.lean",
                src_pkg / "lean-toolchain",
                src_pkg / f"{pkg_name}.lean",
                *(src_pkg / pkg_name / f"{sub}.lean" for sub in submods),
            ]
            missing_files = [str(p.relative_to(pkgs_root)) for p in req_files if not p.is_file()]
            if missing_files:
                return {
                    "tier": "C2",
                    "ok": False,
                    "status": "invalid_c2_package_fixture",
                    "package": pkg_name,
                    "missingFiles": missing_files,
                }
            tc_txt = (src_pkg / "lean-toolchain").read_text(encoding="utf-8").strip()
            if tc_txt != PINNED_CON_LECHE_TOOLCHAIN:
                return {
                    "tier": "C2",
                    "ok": False,
                    "status": "toolchain_mismatch",
                    "package": pkg_name,
                    "expectedToolchain": PINNED_CON_LECHE_TOOLCHAIN,
                    "actualToolchain": tc_txt,
                }

            dep_infos = [external_dep_infos[k] for k in dep_keys]
            lakefile_txt = (src_pkg / "lakefile.lean").read_text(encoding="utf-8")
            for info in dep_infos:
                if info["repoUrl"] not in lakefile_txt or info["rev"] not in lakefile_txt:
                    return {
                        "tier": "C2",
                        "ok": False,
                        "status": "c2_external_pin_mismatch",
                        "package": pkg_name,
                        "dep": info["dep"],
                        "expectedRepoUrl": info["repoUrl"],
                        "expectedRev": info["rev"],
                        "reason": "driver lakefile.lean must `require` the exact (repo_url, commit_sha) this suite pins",
                    }

            work_pkg = tmp_root / pkg_name
            shutil.copytree(src_pkg, work_pkg, ignore=shutil.ignore_patterns(".lake"))
            sub_env = fuzz.pinned_toolchain_env(toolchain=PINNED_CON_LECHE_TOOLCHAIN)
            sub_env["LEAN_SYSROOT"] = str(lean_prefix)
            lean_path_entries = [str(work_pkg)]
            lean_path_entries.extend(info["oleanDir"] for info in dep_infos)
            lean_path_entries.append(str(lean_prefix / "lib" / "lean"))
            sub_env["LEAN_PATH"] = os.pathsep.join(lean_path_entries)

            c_units: list[str] = []
            for sub in submods:
                sf = work_pkg / pkg_name / f"{sub}.lean"
                of = work_pkg / pkg_name / f"{sub}.olean"
                cf = work_pkg / f"{pkg_name}_{sub}.c"
                subprocess.run(
                    [lean_bin, "-R", str(work_pkg), "-DautoImplicit=false", "-o", str(of), "-c", str(cf), str(sf)],
                    cwd=work_pkg,
                    env=sub_env,
                    check=True,
                    capture_output=True,
                    text=True,
                )
                c_units.append(str(cf))

            umb_f = work_pkg / f"{pkg_name}.lean"
            umb_o = work_pkg / f"{pkg_name}.olean"
            umb_c = work_pkg / f"{pkg_name}_root.c"
            subprocess.run(
                [lean_bin, "-R", str(work_pkg), "-DautoImplicit=false", "-o", str(umb_o), "-c", str(umb_c), str(umb_f)],
                cwd=work_pkg,
                env=sub_env,
                check=True,
                capture_output=True,
                text=True,
            )
            c_units.append(str(umb_c))

            call_pairs: list[tuple[str, int]] = [
                (fn, fuzz.u64(vec)) for fn in exports for vec in C2_TEST_VECTORS
            ]
            stock_drv = work_pkg / "StockDriver.lean"
            stock_drv_c = work_pkg / "StockDriver.c"
            stock_calls = [f"toString ({fn} {arg})" for fn, arg in call_pairs]
            stock_drv.write_text(
                f"import {pkg_name}\n"
                'def main : IO Unit :=\n  IO.println ("[" ++ String.intercalate "," ['
                + ", ".join(stock_calls)
                + '] ++ "]")\n',
                encoding="utf-8",
            )
            subprocess.run(
                [lean_bin, "-R", str(work_pkg), "-DautoImplicit=false", "-c", str(stock_drv_c), str(stock_drv)],
                cwd=work_pkg,
                env=sub_env,
                check=True,
                capture_output=True,
                text=True,
            )
            stock_bin = work_pkg / "stock_runner"
            dep_static_libs = [lib for info in dep_infos for lib in info["staticLibs"]]
            subprocess.run(
                [leanc_bin, "-O2", *c_units, str(stock_drv_c), *dep_static_libs, "-o", str(stock_bin)],
                env=sub_env,
                check=True,
                capture_output=True,
                text=True,
            )
            stock_vals = [
                int(x)
                for x in json.loads(
                    subprocess.run([str(stock_bin)], check=True, capture_output=True, text=True).stdout
                )
            ]

            wire_path = work_pkg / f"{pkg_name}.lnir"
            subprocess.run(
                [full_bin, "emit-lnir", "--wire", str(umb_f), "-o", str(wire_path)],
                cwd=work_pkg,
                env=sub_env,
                check=True,
                capture_output=True,
                text=True,
            )
            tv_json = json.loads(
                subprocess.run(
                    [core_bin, "validate-tv", "--lnir", str(wire_path), "--json"],
                    check=True,
                    capture_output=True,
                    text=True,
                ).stdout
            )
            wire_tokens = wire_path.read_text(encoding="utf-8").strip().split("|")
            lowered_decls = [
                bytes.fromhex(wire_tokens[i + 1]).decode("utf-8")
                for i, tok in enumerate(wire_tokens)
                if tok == "D_decl"
            ]
            if not set(exports) <= set(lowered_decls):
                return {
                    "tier": "C2",
                    "ok": False,
                    "status": "missing_lowered_exports",
                    "package": pkg_name,
                    "expectedExports": list(exports),
                    "loweredDecls": lowered_decls,
                }
            fuzz.validate_tv_coverage(tv_json, set(lowered_decls))

            lnir_vals: list[int] = []
            pkg_live_objs = 0
            for vec in C2_TEST_VECTORS:
                uvec = fuzz.u64(vec)
                arg_str = ";".join(f"{fn}:{uvec}" for fn in exports)
                ev_rows = json.loads(
                    subprocess.run(
                        [core_bin, "eval-lnir", "--lnir", str(wire_path), "--args", arg_str, "--opt", "--batch-json"],
                        check=True,
                        capture_output=True,
                        text=True,
                    ).stdout
                )
                if len(ev_rows) != len(exports) or any(r.get("ok") is not True for r in ev_rows):
                    return {
                        "tier": "C2",
                        "ok": False,
                        "status": "lnir_eval_failed",
                        "package": pkg_name,
                        "rows": ev_rows,
                    }
                by_decl = {r["decl"]: int(r["value_u64"]) for r in ev_rows}
                pkg_live_objs += sum(int(r.get("live_objects", 0)) for r in ev_rows)
                for fn in exports:
                    lnir_vals.append(by_decl[fn])
            # Reorder `lnir_vals` to match `call_pairs` (`for fn in exports for vec in C2_TEST_VECTORS`)
            lnir_by_pair: dict[tuple[str, int], int] = {}
            idx_lv = 0
            for vec in C2_TEST_VECTORS:
                uvec = fuzz.u64(vec)
                for fn in exports:
                    lnir_by_pair[(fn, uvec)] = lnir_vals[idx_lv]
                    idx_lv += 1
            ordered_lnir_vals = [lnir_by_pair[pair] for pair in call_pairs]
            total_live_objs += pkg_live_objs

            ll_path = work_pkg / f"{pkg_name}.ll"
            ln_bin = work_pkg / "ln_runner"
            c_drv = work_pkg / "cabi_driver.c"
            c_decls = ["#include <stdint.h>", "#include <stdio.h>"] + [
                f"extern uint64_t {fn}(uint64_t);" for fn in exports
            ]
            c_body = ["int main(void) {", '  printf("[");']
            for idx_c, (fn, arg) in enumerate(call_pairs):
                sep = "," if idx_c > 0 else ""
                c_body.append(f'  printf("{sep}\\"%llu\\"", (unsigned long long){fn}({arg}ULL));')
            c_body.extend(['  printf("]\\n");', "  return 0;", "}"])
            c_drv.write_text("\n".join(c_decls + c_body) + "\n", encoding="utf-8")

            subprocess.run(
                [core_bin, "compile-llvm", "--no-telemetry", "--lnir", str(wire_path), "-o", str(ll_path)],
                check=True,
                capture_output=True,
                text=True,
            )
            raw_ll_sha = fuzz.sha256_bytes(ll_path.read_bytes())
            san_meta = fuzz.compile_and_link_llvm_driver(
                clang_bin=clang_bin,
                extra_inc=extra_inc,
                ll_path=ll_path,
                driver_c_path=c_drv,
                out_bin_path=ln_bin,
                asan=asan,
                ubsan=ubsan,
                sanitizer_linker=engines.get("sanitizer_linker"),
            )
            san_verified = (
                san_meta.get("asan") is asan
                and san_meta.get("ubsan") is ubsan
                and (
                    san_meta.get("compiled_llvm_ir_sha256") != raw_ll_sha
                    if asan
                    else san_meta.get("compiled_llvm_ir_sha256") == raw_ll_sha
                )
            )
            run_env = dict(os.environ)
            if asan:
                run_env["ASAN_OPTIONS"] = "detect_leaks=0:abort_on_error=1:halt_on_error=1"
            if ubsan:
                run_env["UBSAN_OPTIONS"] = "print_stacktrace=1:halt_on_error=1"
            llvm_vals = [
                int(x)
                for x in json.loads(
                    subprocess.run([str(ln_bin)], env=run_env, check=True, capture_output=True, text=True).stdout
                )
            ]

            pkg_mismatches = 0
            for idx_p, (fn, arg) in enumerate(call_pairs):
                sv = stock_vals[idx_p]
                lv = ordered_lnir_vals[idx_p]
                nv = llvm_vals[idx_p]
                if sv != lv or lv != nv:
                    pkg_mismatches += 1
                    mismatches.append(
                        {
                            "package": pkg_name,
                            "export": fn,
                            "arg": str(arg),
                            "stock_lean_c": str(sv),
                            "lnir_eval": str(lv),
                            "c_abi_llvm": str(nv),
                        }
                    )
            total_cases += len(call_pairs)
            package_reports.append(
                {
                    "package": pkg_name,
                    "submodules": list(submods),
                    "exports": list(exports),
                    "externalDeps": [
                        {"dep": i["dep"], "repoUrl": i["repoUrl"], "rev": i["rev"], "toolchain": i["toolchain"]}
                        for i in dep_infos
                    ],
                    "casesChecked": len(call_pairs),
                    "liveObjects": pkg_live_objs,
                    "mismatches": pkg_mismatches,
                    "sanitizerVerified": san_verified,
                    "llvmIrSha256": raw_ll_sha,
                    "compiledLlvmIrSha256": san_meta.get("compiled_llvm_ir_sha256"),
                }
            )

    all_san_ok = all(p["sanitizerVerified"] for p in package_reports)
    external_pkg_count = sum(1 for p in package_reports if p["externalDeps"])
    ok = len(package_reports) == len(specs) and not mismatches and total_live_objs == 0 and all_san_ok
    return {
        "tier": "C2",
        "ok": ok,
        "status": "passed_multi_module_lake_packages" if ok else "failed_c2_lake_packages",
        "scope": (
            "in_repo_multi_module_lake_fixtures_plus_pinned_external_ecosystem_drivers"
            if external
            else "in_repo_multi_module_lake_fixtures_not_external_ecosystem"
        ),
        "packagesDir": str(pkgs_root),
        "packageCount": len(package_reports),
        "externalRequested": external,
        "externalPackageCount": external_pkg_count,
        "externalEcosystem": bool(ok and external and external_pkg_count > 0),
        "casesChecked": total_cases,
        "rcLeakCount": total_live_objs,
        "asan": asan,
        "ubsan": ubsan,
        "sanitizerReceiptsVerified": all_san_ok,
        "packages": package_reports,
        "mismatches": mismatches,
    }


def ensure_c1_upstream_corpus() -> dict[str, Any]:
    """Provision the pinned upstream `leanprover/lean4` checkout for the Tier C1
    manifest corpus into the persistent cache (mirrors `ensure_c2_external_dep`:
    one shallow fetch on a cold cache; a stamp file keeps warm runs offline).

    The pin's toolchain correspondence is by tag (`v4.35.0`, the version of
    PINNED_CON_LECHE_TOOLCHAIN); the lean4 repo's own `lean-toolchain` is its
    bootstrap pointer (`build/release/stage1`), so the post-checkout assertion
    is `git rev-parse HEAD` == the pinned commit plus the presence of the
    corpus piles the manifest selects from."""
    repo_url = c1_corpus.C1_UPSTREAM_REPO_URL
    rev = c1_corpus.C1_UPSTREAM_REV
    dep_dir = c1_corpus.corpus_cache_dir()
    stamp = dep_dir / ".turbo-c1-provisioned"
    base: dict[str, Any] = {
        "repoUrl": repo_url,
        "rev": rev,
        "tag": c1_corpus.C1_UPSTREAM_TAG,
        "path": str(dep_dir),
    }
    # F2 (round 2): the stamp records the pile set beside the rev, so a
    # CORPUS_PILES change re-provisions a warm sparse cache instead of
    # leaving it stuck without the new pile.
    want_stamp = rev + "\n" + ",".join(c1_corpus.CORPUS_PILES) + "\n"
    try:
        if not (stamp.is_file() and stamp.read_text(encoding="utf-8") == want_stamp):
            dep_dir.mkdir(parents=True, exist_ok=True)
            if not (dep_dir / ".git").is_dir():
                subprocess.run(["git", "init", "-q", str(dep_dir)], check=True, capture_output=True,
                               text=True, errors="replace")
            # R8: blob-filtered fetch plus sparse checkout of the corpus piles
            # only (measured at the pin: 4.9M .git + 22M tree vs the full
            # checkout). The lazy blob fetch at checkout time needs a NAMED
            # promisor remote, hence `origin` instead of a bare URL.
            subprocess.run(["git", "-C", str(dep_dir), "config", "remote.origin.url", repo_url],
                           check=True, capture_output=True, text=True, errors="replace")
            subprocess.run(["git", "-C", str(dep_dir), "fetch", "-q", "--depth", "1",
                            "--filter=blob:none", "origin", rev],
                           check=True, capture_output=True, text=True, errors="replace")
            subprocess.run(["git", "-C", str(dep_dir), "sparse-checkout", "set", *c1_corpus.CORPUS_PILES],
                           check=True, capture_output=True, text=True, errors="replace")
            subprocess.run(["git", "-C", str(dep_dir), "checkout", "-q", "--detach", rev],
                           check=True, capture_output=True, text=True, errors="replace")
            head = subprocess.run(["git", "-C", str(dep_dir), "rev-parse", "HEAD"],
                                  check=True, capture_output=True, text=True, errors="replace").stdout.strip()
            if head != rev:
                return {**base, "ok": False, "reason": f"checkout is at {head!r}, expected the pinned rev"}
            stamp.write_text(want_stamp, encoding="utf-8")
        missing_piles = [pile for pile in c1_corpus.CORPUS_PILES if not (dep_dir / pile).is_dir()]
        if missing_piles:
            # F2 (round 2): a stamped cache can still lack a pile (an older
            # sparse cone, a partial cache restore); re-running the sparse
            # checkout is cheap and self-heals it instead of failing.
            subprocess.run(["git", "-C", str(dep_dir), "sparse-checkout", "set", *c1_corpus.CORPUS_PILES],
                           check=True, capture_output=True, text=True, errors="replace")
            subprocess.run(["git", "-C", str(dep_dir), "checkout", "-q", "--detach", rev],
                           check=True, capture_output=True, text=True, errors="replace")
            missing_piles = [pile for pile in c1_corpus.CORPUS_PILES if not (dep_dir / pile).is_dir()]
        if missing_piles:
            return {**base, "ok": False, "reason": f"corpus piles missing at the pin: {missing_piles}"}
        return {**base, "ok": True}
    except subprocess.CalledProcessError as err:
        return {**base, "ok": False,
                "reason": f"`{' '.join(str(c) for c in err.cmd)}` failed with exit {err.returncode}",
                "stderrTail": (err.stderr or "")[-1200:]}
    except OSError as err:
        return {**base, "ok": False, "reason": str(err)}


C1_UPSTREAM_PROGRAM_TIMEOUT_S = 240

# R1: deliberate frontend refusal diagnostics, measured live at the pin over
# all 250 manifest programs (2026-11-26). Every fail-closed refusal the
# frontend emits carries one of these stderr shapes (sources:
# lean/LeanNative/Driver/CoreCLI.lean, lean/LeanNative/IR/RealLCNFBridge.lean).
# An elaboration failure prints "Elaboration failed for <file>" instead
# (lean/LeanNative/Driver/BuildExe.lean), and an internal bridge invariant
# trip prints "[lean-native] internal bridge error: ..."; neither is a
# deliberate refusal, so neither counts as rejected_fail_closed.
C1_UPSTREAM_REJECTION_MARKERS: tuple[str, ...] = (
    "[lean-native] Unsupported ",
    "[lean-native] unsupported ",
    "[lean-native] Failed to extract any LCNF declarations",
    "[lean-native] Module contains no Stage 1B scalar functions",
)
# F1 (round 2): fatal shapes that DISQUALIFY a refusal classification even
# when a refusal marker is also present (Lean can print a panic and keep
# running, so a fatal line can sit beside per-declaration refusal notes).
# Spellings read at their sources: "[lean-native] internal bridge error"
# (lean/LeanNative/IR/RealLCNFBridge.lean:526), "Elaboration failed for"
# (lean/LeanNative/Driver/BuildExe.lean:99, EvalLCNFCLI.lean:739), and from
# the pinned lean4 checkout: "PANIC at " (src/Init/Util.lean:51),
# "INTERNAL PANIC" (src/runtime/object.cpp:93), "uncaught exception: "
# (src/runtime/io.cpp:66).
C1_UPSTREAM_FATAL_MARKERS: tuple[str, ...] = (
    "[lean-native] internal bridge error",
    "Elaboration failed for",
    "PANIC at ",
    "INTERNAL PANIC",
    "uncaught exception: ",
)
# R1: authored scalar-subset canary, manifest-external; the opt-in leg is ok
# only when the frontend lowers it end to end.
C1_UPSTREAM_CANARY = ROOT / "scripts" / "fixtures" / "c1_upstream_canary.lean"


def classify_c1_upstream_rejection(returncode: int, stderr: str, stdout: str = "") -> str:
    """R1 + round-2 F1: a nonzero `emit-lnir` exit counts as
    rejected_fail_closed only when stderr carries a deliberate refusal
    diagnostic AND no fatal shape appears in stderr or stdout. A negative
    returncode, or one >= 128 (a shell-encoded signal death), is
    frontend_error whatever the output says; so are usage, elaboration,
    panic and internal-bridge shapes. Any frontend_error makes the leg not
    ok."""
    if returncode < 0 or returncode >= 128:
        return "frontend_error"
    combined = f"{stderr}\n{stdout}"
    if any(marker in combined for marker in C1_UPSTREAM_FATAL_MARKERS):
        return "frontend_error"
    if returncode > 0 and any(marker in stderr for marker in C1_UPSTREAM_REJECTION_MARKERS):
        return "rejected_fail_closed"
    return "frontend_error"


def run_c1_upstream_corpus(enabled: bool) -> dict[str, Any]:
    """Manifest-driven upstream Tier C1 leg (roadmap leaf C1x). Opt-in like the
    C2 external arm; fails closed (`BLOCKED_MISSING_DEPENDENCY`) when opted in
    but provisioning fails, and fails the manifest gate (count == 250, per-file
    sha256 at the pin, matrix-construct coverage) before any execution.

    Each program runs through the real frontend (`emit-lnir --wire`). A
    nonzero exit counts as rejected_fail_closed ONLY when stderr carries a
    deliberate `[lean-native]` refusal diagnostic
    (C1_UPSTREAM_REJECTION_MARKERS); any other nonzero outcome is recorded as
    frontend_error and makes the leg not ok (R1). The authored scalar canary
    (C1_UPSTREAM_CANARY, manifest-external) runs with every opt-in leg and
    must reach lowered_llvm_emitted. A program the frontend lowers is
    additionally compiled (`compile-llvm`); none of the pinned 250 currently
    lower with exported scalar entrypoints, so 3-way case-vector execution of
    upstream programs remains open."""
    if not enabled:
        return {
            "executed": False,
            "optedIn": False,
            "reason": (
                "upstream corpus leg opts in via --c1-upstream / TURBO_C1_UPSTREAM=1; it "
                "provisions the pinned leanprover/lean4 checkout into TURBO_LEAN_HOME/c1-upstream "
                "(one network fetch per cold cache) and fails closed on a missing dependency"
            ),
        }
    # R2, relocated here by F5 (round 2): the corpus pin consistency check
    # lives in the opted-in leg, not suite startup, so a lean/lean-toolchain
    # bump cannot break tiers that never run this corpus. The leg still fails
    # closed, before any provisioning, with a named status.
    repo_pin = fuzz.repo_pinned_toolchain()
    if c1_corpus.C1_UPSTREAM_TOOLCHAIN != repo_pin:
        return {
            "executed": False,
            "optedIn": True,
            "ok": False,
            "status": "failed_toolchain_pin_mismatch",
            "manifestToolchain": c1_corpus.C1_UPSTREAM_TOOLCHAIN,
            "repoToolchain": repo_pin,
            "reason": (
                "scripts/build_c1_corpus_manifest.py C1_UPSTREAM_TOOLCHAIN must equal "
                "lean/lean-toolchain; update the corpus pin (repoUrl/rev/tag/toolchain) "
                "and regenerate scripts/c1_corpus_manifest.json together"
            ),
        }
    prov = ensure_c1_upstream_corpus()
    if prov.get("ok") is not True:
        return {
            "executed": False,
            "optedIn": True,
            "ok": False,
            "status": "BLOCKED_MISSING_DEPENDENCY",
            "provision": prov,
        }
    corpus_root = Path(prov["path"])
    gate = c1_corpus.verify_manifest(corpus_root=corpus_root)
    if gate.get("ok") is not True:
        return {"executed": True, "optedIn": True, "ok": False,
                "status": "failed_manifest_gate", "manifestGate": gate, "provision": prov}
    engines = fuzz.probe_engines()
    if not (engines["full_bin"] and engines["core_bin"]):
        return {"executed": False, "optedIn": True, "ok": False,
                "status": "incomplete_missing_engine", "manifestGate": gate,
                "engines": {"full_bin": engines["full_bin"], "core_bin": engines["core_bin"]}}
    manifest = json.loads(c1_corpus.MANIFEST_PATH.read_text(encoding="utf-8"))
    env = fuzz.pinned_toolchain_env()

    def run_one(prog: dict[str, Any], tmp_dir: str, src: Path | None = None) -> dict[str, Any]:
        src = corpus_root / prog["path"] if src is None else src
        # R3: each program subprocess runs in its own directory under the
        # leg's tmp dir (the C2 leg's explicit per-package cwd shape), so a
        # cwd-relative write can land neither in the suite's cwd nor in a
        # sibling program's scratch.
        prog_dir = tempfile.mkdtemp(prefix="prog_", dir=tmp_dir)
        wire = Path(prog_dir) / (prog["path"].replace("/", "__") + ".lnir")
        constructs = ", ".join(prog["matrixConstructs"])
        try:
            res = subprocess.run(
                [engines["full_bin"], "emit-lnir", "--wire", str(src), "-o", str(wire)],
                capture_output=True, text=True, errors="replace", env=env,
                timeout=C1_UPSTREAM_PROGRAM_TIMEOUT_S, cwd=prog_dir,
            )
        except subprocess.TimeoutExpired:
            return {"path": prog["path"], "outcome": "infrastructure_timeout",
                    "skippedReason": f"emit-lnir exceeded {C1_UPSTREAM_PROGRAM_TIMEOUT_S}s"}
        if res.returncode != 0:
            if classify_c1_upstream_rejection(res.returncode, res.stderr or "", res.stdout or "") != "rejected_fail_closed":
                return {
                    "path": prog["path"],
                    "outcome": "frontend_error",
                    "returncode": res.returncode,
                    "matrixConstructs": prog["matrixConstructs"],
                    "skippedReason": (
                        f"emit-lnir exit {res.returncode} without a deliberate refusal "
                        f"diagnostic (negative rc = signal death; elaboration, usage and "
                        f"internal errors land here); syntactic matrix constructs: {constructs}"
                    ),
                    "stderrTail": (res.stderr or "")[-240:],
                }
            return {
                "path": prog["path"],
                "outcome": "rejected_fail_closed",
                "returncode": res.returncode,
                "matrixConstructs": prog["matrixConstructs"],
                "skippedReason": (
                    f"frontend failed closed (emit-lnir exit {res.returncode}); "
                    f"syntactic matrix constructs: {constructs}"
                ),
                "stderrTail": (res.stderr or "")[-240:],
            }
        ll = wire.with_suffix(".ll")
        try:
            comp = subprocess.run(
                [engines["core_bin"], "compile-llvm", "--lnir", str(wire), "-o", str(ll)],
                capture_output=True, text=True, errors="replace", env=env,
                timeout=C1_UPSTREAM_PROGRAM_TIMEOUT_S, cwd=prog_dir,
            )
        except subprocess.TimeoutExpired:
            return {"path": prog["path"], "outcome": "infrastructure_timeout",
                    "skippedReason": f"compile-llvm exceeded {C1_UPSTREAM_PROGRAM_TIMEOUT_S}s"}
        if comp.returncode != 0:
            return {"path": prog["path"], "outcome": "lowered_llvm_failed",
                    "returncode": comp.returncode,
                    "matrixConstructs": prog["matrixConstructs"],
                    "stderrTail": (comp.stderr or "")[-240:]}
        return {"path": prog["path"], "outcome": "lowered_llvm_emitted",
                "matrixConstructs": prog["matrixConstructs"],
                "threeWay": "frontend+LLVM engines exercised; no exported scalar case vectors to execute"}

    with tempfile.TemporaryDirectory(prefix="turbo_c1_upstream_") as tmp:
        workers = max(1, min(8, (os.cpu_count() or 2) // 4))
        with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
            rows = list(pool.map(lambda p: run_one(p, tmp), manifest["programs"]))
        # R1: the authored scalar canary runs with the leg but stays
        # manifest-external: it proves the frontend still LOWERS (so a
        # regression that rejects everything cannot read as 250 expected
        # rejections) and never counts toward outcomeCounts or the
        # upstream_lean4_run_250_three_way missing-coverage token.
        if C1_UPSTREAM_CANARY.is_file():
            canary = run_one(
                {"path": "scripts/fixtures/c1_upstream_canary.lean", "matrixConstructs": []},
                tmp,
                src=C1_UPSTREAM_CANARY,
            )
        else:
            canary = {"path": str(C1_UPSTREAM_CANARY), "outcome": "canary_missing",
                      "skippedReason": "authored canary fixture absent"}
        canary["manifestExternal"] = True
    rows.sort(key=lambda r: r["path"])
    counts = {"rejected_fail_closed": 0, "lowered_llvm_emitted": 0,
              "lowered_llvm_failed": 0, "infrastructure_timeout": 0, "frontend_error": 0}
    failing: list[str] = []
    for r in rows:
        counts[r["outcome"]] += 1
        if r["outcome"] in ("lowered_llvm_failed", "infrastructure_timeout", "frontend_error"):
            failing.append(r["path"])
    ok = (
        not failing
        and counts["frontend_error"] == 0
        and len(rows) == manifest["programCount"]
        and counts["rejected_fail_closed"] + counts["lowered_llvm_emitted"] == manifest["programCount"]
        and canary.get("outcome") == "lowered_llvm_emitted"
    )
    return {
        "executed": True,
        "optedIn": True,
        "ok": ok,
        "status": "passed_upstream_manifest_corpus" if ok else "failed_upstream_corpus",
        "corpusPath": str(corpus_root),
        "manifest": str(c1_corpus.MANIFEST_PATH),
        "manifestGate": gate,
        "programCount": manifest["programCount"],
        "outcomeCounts": counts,
        "failingPrograms": failing,
        # No manifest program executes 3-way case vectors yet; the
        # upstream_lean4_run_250_three_way missing-coverage token keys on
        # this staying 0 (the canary is deliberately outside it).
        "caseVectorExecutions": 0,
        "canary": canary,
        "programs": rows,
    }


def c1_upstream_subresult(enabled: bool) -> dict[str, Any]:
    """R4: the upstream corpus leg never raises past the C1 tier; an exception
    becomes a failed upstream sub-result recorded on the tier."""
    try:
        return run_c1_upstream_corpus(enabled=enabled)
    except (OSError, ValueError, RuntimeError, subprocess.CalledProcessError) as err:
        return {
            "executed": False,
            "optedIn": enabled,
            "ok": False,
            "status": "failed_upstream_leg_exception",
            "error": f"{type(err).__name__}: {err}",
        }


def run_c1_corpus(asan: bool, ubsan: bool) -> dict[str, Any]:
    engines = fuzz.probe_engines(asan=asan, ubsan=ubsan)
    if not (engines["stock_lean_c"] and engines["lnir_eval"] and engines["c_abi_llvm"]):
        return {
            "tier": "C1",
            "ok": False,
            "status": "incomplete_missing_engine",
            "asan": asan,
            "ubsan": ubsan,
            "ubsanScope": "c_driver_and_link_runtime_only_not_llvm_ir" if ubsan else "disabled",
            "tests": list(C1_CORPUS_TESTS),
            "engines": {
                "stock_lean_c": engines["stock_lean_c"],
                "lnir_validate_tv": engines["lnir_eval"],
                "c_abi_llvm": engines["c_abi_llvm"],
            },
        }
    with tempfile.TemporaryDirectory(prefix="turbo_c1_receipts_") as tmp:
        receipt_path = Path(tmp) / "sanitizer-receipts.jsonl"
        cmd = [
            sys.executable,
            "-m",
            "unittest",
            "-v",
            *(f"scripts.test_scalar_frontend.{name}" for name in C1_CORPUS_TESTS),
        ]
        sub_env = fuzz.pinned_toolchain_env()
        sub_env["TURBO_CONFORMANCE_ASAN"] = "1" if asan else "0"
        sub_env["TURBO_CONFORMANCE_UBSAN"] = "1" if ubsan else "0"
        sub_env["TURBO_C1_RECEIPT_FILE"] = str(receipt_path)
        res = subprocess.run(cmd, cwd=ROOT, env=sub_env, capture_output=True, text=True)
        rows = []
        if receipt_path.is_file():
            rows = [json.loads(line) for line in receipt_path.read_text(encoding="utf-8").splitlines() if line.strip()]
        sanitizers_verified = (
            len(rows) == len(C1_CORPUS_TESTS)
            and all(
                r.get("asan") is asan
                and r.get("ubsan") is ubsan
                and r.get("ubsan_scope") == ("c_driver_and_link_runtime_only_not_llvm_ir" if ubsan else "disabled")
                and (
                    r.get("compiled_llvm_ir_sha256") != r.get("llvm_ir_sha256")
                    if asan
                    else r.get("compiled_llvm_ir_sha256") == r.get("llvm_ir_sha256")
                )
                for r in rows
            )
        )
        ok = res.returncode == 0 and sanitizers_verified
        return {
            "tier": "C1",
            "ok": ok,
            "status": "passed_scalar_tuple_subset" if ok else "failed_or_incomplete",
            "coverage": "scalar_narrow_unsigned_joinpoint_flat_tuple_and_stage1b_subset",
            "tests": list(C1_CORPUS_TESTS),
            "testCount": len(C1_CORPUS_TESTS),
            "asan": asan,
            "ubsan": ubsan,
            "ubsanScope": "c_driver_and_link_runtime_only_not_llvm_ir" if ubsan else "disabled",
            "sanitizerReceiptsVerified": sanitizers_verified,
            "sanitizerReceiptCount": len(rows),
            "returncode": res.returncode,
            "stderrTail": (res.stderr or "")[-1200:],
        }


def assert_toolchain_pins_consistent() -> None:
    """Fail loudly at suite startup when the repo pin and the con-leche pin
    diverge: C2 fixtures and C3 `.olean` compilation are built against
    PINNED_CON_LECHE_TOOLCHAIN, while C1/C4 follow lean/lean-toolchain."""
    repo_pin = fuzz.repo_pinned_toolchain()
    if repo_pin != PINNED_CON_LECHE_TOOLCHAIN:
        raise SystemExit(
            f"Toolchain pin mismatch: lean/lean-toolchain pins {repo_pin!r} but this suite "
            f"pins {PINNED_CON_LECHE_TOOLCHAIN!r} for C2/C3 (con-leche). Update "
            "PINNED_CON_LECHE_TOOLCHAIN, PINNED_CON_LECHE_REV and the C2 package "
            "fixtures together."
        )
    # The R2 check on c1_corpus.C1_UPSTREAM_TOOLCHAIN moved into the opted-in
    # upstream leg (F5, round 2): a repo toolchain bump must not break tiers
    # that never run that corpus.


def main() -> int:
    assert_toolchain_pins_consistent()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--fuzz-seeds", "--seeds", dest="fuzz_seeds", type=int, default=50)
    parser.add_argument(
        "--tier",
        "--tiers",
        dest="tiers",
        action="append",
        default=None,
        help="Comma-separated conformance tiers (C1,C2,C3,C4). Default: C4; C2 requires TURBO_C2_PACKAGES_DIR / --c2-packages-dir; C3 requires TURBO_CON_LECHE_BIN / --con-leche-bin; C1's upstream corpus leg opts in via --c1-upstream / TURBO_C1_UPSTREAM=1.",
    )
    parser.add_argument(
        "--c2-packages-dir",
        default=None,
        help="Path to multi-module Lake package corpus (or `auto` for verification/c2-lake-packages) for `--tier C2`.",
    )
    parser.add_argument(
        "--con-leche-bin",
        default=None,
        help="Path to verified `con-leche` binary (or `auto` for verification/con-leche-bridge build) for `--tier C3`.",
    )
    parser.add_argument(
        "--c2-external",
        action="store_true",
        default=os.environ.get("TURBO_C2_EXTERNAL") == "1",
        help=(
            "Also run the pinned external ecosystem Tier C2 driver packages (leanprover-community/batteries); "
            "provisions each (repo_url, commit_sha, lean_toolchain) pin into TURBO_LEAN_HOME/c2-external "
            "(default ~/.cache/turbo-lean/c2-external; one network fetch per cold pin). The nightly workflow runs this."
        ),
    )
    parser.add_argument(
        "--c1-upstream",
        action="store_true",
        default=os.environ.get("TURBO_C1_UPSTREAM") == "1",
        help=(
            "Also run the manifest-driven upstream Tier C1 corpus (scripts/c1_corpus_manifest.json: "
            "250 pinned leanprover/lean4 programs chosen by the LCNF coverage matrix); provisions the "
            "pin into TURBO_LEAN_HOME/c1-upstream (default ~/.cache/turbo-lean/c1-upstream; one network "
            "fetch per cold cache) and fails closed when provisioning or the manifest gate fails."
        ),
    )
    parser.add_argument("--asan", action="store_true", help="Instrument compiled LLVM IR + C driver with AddressSanitizer")
    parser.add_argument(
        "--ubsan",
        action="store_true",
        help="Instrument C driver and link runtime with UndefinedBehaviorSanitizer (pre-emitted LLVM IR is not UBSan-instrumented)",
    )
    args = parser.parse_args()

    failures: list[dict[str, Any]] = []
    tier_results: dict[str, Any] = {}
    certs: dict[str, Any] = {}
    plugins: dict[str, Any] = {}
    execution: dict[str, Any] = {}

    try:
        tiers = parse_tiers(args.tiers)
    except ValueError as err:
        parser.error(str(err))
        return 2

    needs_core_gates = any(t in ("C1", "C4") for t in tiers)
    try:
        if needs_core_gates or (CORE.is_file() and os.access(CORE, os.X_OK)):
            certs = command_json("verify-certs", "--canonical-benchmark", "--json")
            plugins = command_json("plugins", "--canonical-benchmark", "--test-adversarial", "--json")
            if certs.get("verified") is not True or not certs.get("declSummaries"):
                failures.append({"stage": "certificate_chain", "detail": certs})
            if (
                plugins.get("adversarialRejected") is not True
                or type(plugins.get("rejectedCount")) is not int
                or plugins["rejectedCount"] < 1
                or not plugins.get("declAudits")
                or any(r.get("tvVerified") is not True for r in plugins["declAudits"])
            ):
                failures.append({"stage": "adversarial_plugin_gate", "detail": plugins})

        for tier in tiers:
            if tier == "C1":
                c1 = run_c1_corpus(asan=args.asan, ubsan=args.ubsan)
                # R4: record the tier result before the upstream leg runs, and
                # take the upstream leg through its exception wrapper, so an
                # upstream failure can never lose the authored-corpus result.
                tier_results["C1"] = c1
                c1["upstream"] = c1_upstream_subresult(enabled=args.c1_upstream)
                if args.c1_upstream and c1["upstream"].get("ok") is not True:
                    c1["ok"] = False
                if c1.get("ok") is not True:
                    failures.append({"stage": "tier_C1_scalar_corpus", "detail": c1})
            elif tier == "C2":
                c2 = run_c2_corpus(args.c2_packages_dir, asan=args.asan, ubsan=args.ubsan, external=args.c2_external)
                tier_results["C2"] = c2
                if c2.get("ok") is not True:
                    failures.append({"stage": "tier_C2_lake_packages", "detail": c2})
            elif tier == "C3":
                c3 = run_c3_corpus(args.con_leche_bin)
                tier_results["C3"] = c3
                if c3.get("ok") is not True:
                    failures.append({"stage": "tier_C3_con_leche_holdouts", "detail": c3})
            elif tier == "C4":
                execution = fuzz.run_fuzzer(args.fuzz_seeds, asan=args.asan, ubsan=args.ubsan)
                tier_results["C4"] = execution
                if execution.get("ok") is not True or execution.get("checked", 0) != args.fuzz_seeds or args.fuzz_seeds < 1:
                    failures.append({"stage": "scalar_three_engine_execution", "detail": execution})
    except (OSError, ValueError, RuntimeError, subprocess.CalledProcessError) as error:
        failures.append({"stage": "execution_failure", "detail": str(error)})

    c1_upstream = tier_results.get("C1", {}).get("upstream", {})
    missing_coverage = [
        "alias_RC_seqFor_llvm",
        # R7: the former single upstream_lean4_run_250 token is split. The
        # manifest-gate token clears when the opt-in manifest leg runs green;
        # the three-way token stays until a MANIFEST program records
        # lowered_llvm_emitted with executed 3-way case vectors. The authored
        # canary fixture is manifest-external and deliberately outside the
        # three-way condition: it proves the frontend still lowers, not that
        # upstream programs execute three ways (outcomeCounts never includes
        # it, and caseVectorExecutions stays 0 until case vectors exist).
        *(
            []
            if c1_upstream.get("ok") is True
            else ["upstream_lean4_run_250_manifest_gate"]
        ),
        *(
            []
            if (
                c1_upstream.get("ok") is True
                and c1_upstream.get("outcomeCounts", {}).get("lowered_llvm_emitted", 0) > 0
                and c1_upstream.get("caseVectorExecutions", 0) > 0
            )
            else ["upstream_lean4_run_250_three_way"]
        ),
        *(
            []
            if tier_results.get("C2", {}).get("externalEcosystem") is True
            else ["tier_C2_ecosystem_packages"]
        ),
        *(
            []
            if tier_results.get("C3", {}).get("ok") is True
            else ["tier_C3_sealed_corpus_and_cas_replay"]
        ),
        "target_qualification",
    ]
    report = {
        "schemaVersion": "turbo-lean-conformance-v2",
        "ok": not failures,
        "tiersRequested": tiers,
        "tierResults": tier_results,
        "asan": args.asan,
        "ubsan": args.ubsan,
        "ubsanScope": "c_driver_and_link_runtime_only_not_llvm_ir" if args.ubsan else "disabled",
        "scope": "scalar_three_engine_and_separate_certificate_plugin_gates",
        "fullRoadmapAccepted": False,
        "missingCoverage": missing_coverage,
        "divergences": len(failures),
        "divergenceDetails": failures,
        "lcnfFuzzSeedsChecked": execution.get("checked", 0),
        "lcnfFuzzRcLeaks": execution.get("rc_leak_count"),
        "certificateChainVerified": certs.get("verified", False),
        "overallAssurance": certs.get("overallAssurance", "Unknown"),
        "adversarialMutantRejected": plugins.get("adversarialRejected", False),
        "execution": execution,
    }
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(
            f"[conformance] tiers={','.join(tiers)} asan={args.asan} ubsan={args.ubsan}: "
            f"{'PASSED' if report['ok'] else 'FAILED'}; "
            f"fuzz_checked={report['lcnfFuzzSeedsChecked']}; full roadmap acceptance remains open"
        )
        for failure in failures:
            print(json.dumps(failure, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
