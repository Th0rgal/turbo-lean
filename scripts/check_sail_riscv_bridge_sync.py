#!/usr/bin/env python3
"""Stage 3E / Milestone M5: Exact Model Synchronization & Upstream Pin Gate for `verification/sail-riscv-bridge/`.

Verifies:
1. `verification/sail-riscv-bridge/SailRiscvBridge/MirroredModel.lean` contains byte-identical slices of:
   - `riscvDivU64Spec` and `riscvRemU64Spec` from `lean/TurboLean/PolicyGates.lean`
   - `clmul64` and `clmul64Hi` from `lean/LeanNative/IR/Types.lean`
   preventing any drift or shadow divergence between the main `TurboLean` / `LeanNative` modules
   and the upstream `opencompl/sail-riscv-lean` formal RV64 bisimulation package.
2. `verification/sail-riscv-bridge/lean-toolchain` pins `leanprover/lean4:v4.29.0`, and both
   `lakefile.toml` and `lake-manifest.json` pin `opencompl/sail-riscv-lean` (`Lean_RV64D`) at commit
   `51c635c460125ac87955d061fcd902ce03b8011f` and `rems-project/lean-sail` (`Sail`) at commit
   `079463134b9c50450b8393e1566a09fc492a34d9` (`len(packages) == 2`).
3. `SailRiscvBridge` proof modules never import heavy monolithic generated modules
   (`LeanRV64D.InstsEnd`, `LeanRV64D.Step`, `LeanRV64D.ZicsrInsts`, `LeanRV64D.RiscvExtras`, or root `import LeanRV64D`),
   contain `#verify_sail_riscv_bridge_axioms` (>= 54 unique audited theorems via `Lean.collectAxioms`
   and `bridgedTheorems.Nodup`), and contain zero `sorry`, `sorryAx`, `admit`, `axiom`, `native_decide`,
   `bv_decide`, `trustCompiler`, or `ofReduceBool` tokens outside Lean comments/strings.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import sys
import tempfile
import unittest
from pathlib import Path

ROOT_DIR = Path(__file__).resolve().parent.parent
BRIDGE_DIR = ROOT_DIR / "verification" / "sail-riscv-bridge"

PINNED_TOOLCHAIN = "leanprover/lean4:v4.29.0"
PINNED_SAIL_RISCV_URL = "https://github.com/opencompl/sail-riscv-lean.git"
PINNED_SAIL_RISCV_REV = "51c635c460125ac87955d061fcd902ce03b8011f"
PINNED_SAIL_URL = "https://github.com/rems-project/lean-sail"
PINNED_SAIL_REV = "079463134b9c50450b8393e1566a09fc492a34d9"

POLICY_GATES_REL = "lean/TurboLean/PolicyGates.lean"
TYPES_REL = "lean/LeanNative/IR/Types.lean"

FORBIDDEN_PROOF_TOKENS = re.compile(
    r"\b(?:sorry|sorryAx|admit|axiom|native_decide|bv_decide|trustCompiler|ofReduceBool)\b",
    re.M,
)
FORBIDDEN_IMPORTS = re.compile(
    r"^\s*import\s+(?:LeanRV64D\s*$|LeanRV64D\.(?:InstsEnd|Step|ZicsrInsts|RiscvExtras)\b)",
    re.M,
)

MIN_AUDITED_THEOREMS = 54

UPSTREAM_INSTSEND_REL = ".lake/packages/Lean_RV64D/LeanRV64D/InstsEnd.lean"
PINNED_INSTSEND_SNIPPET_DIGESTS: dict[str, str] = {
    "execute_DIV": "4394ab1c2623f0687728cc0ab7c0d317009f11b00ccab473222c19d365ff612c",
    "execute_REM": "fb4f86ac254fb647f41a41e6f26f765c9087770677b49a2e739e14b8d515db31",
    "execute_MUL": "234e8035ff4daca5a6ad658fdf12502347b6a72bfacd75f2c903dfe4d3f493c2",
    "execute_CLMUL": "72358990b97db7eae91b51cb959f67e279e096da12d293d0b61826747ec0e5b0",
    "execute_CLMULH": "67c9d5f275bc1af5af8cd471d8eb088884d06e92fb3e5dc494f98c26896e9f39",
    "execute_CLMULR": "d7e51abe9d8e334e0609a847d92435a67f9fb11acc07ef2ecc7b3136aa91e387",
    "execute_RTYPE": "d1785beb7a32d8a262bdb300b428a8087d67930409e4be1dcac12cc1b5515085",
    "execute_ITYPE": "1813fbb5a72a8fb1b10596e1707ce461df64c72503576e20634eab120203dfe1",
    "execute_SHIFTIOP": "c59c039a540b8698df6cd94cfaf2b53eca51328d3ce442f179acd2a2e36722e2",
    "execute_UTYPE": "9c284f4e64a21d4a129ea96a6ef8c9d759d953ae6788261a0eed4e42e11ccb24",
    "execute_BTYPE": "3774f7e36ab761a98a6cbf764f93447ea643c51fba6d5f683dcc03812225993b",
    "execute_RTYPEW": "ab270b2daa652098e974da13fe436041b1aea02735a699fcd42a71a9b682c791",
    "execute_ADDIW": "d530a33b9a50c53b159717b4f35779b0a885fea19bd2e87c370059abac6b8d41",
    "execute_SHIFTIWOP": "46a0c55d12d3b4b30d17983e723c7508daf1434ebef4710af4dbdd9c7c4137af",
    "execute_MULW": "100aa3ff7ea218b03d70a9898382f4d4048a2665d1b19dc10fa2d994935b4411",
    "execute_DIVW": "984d1176ebdd2ccaf520c9724e1b4b0532178174d4512f104e801e748516bb62",
    "execute_REMW": "aba41e6ed0863496fc54a6a88ba82aa3db7a181e53654a73a1f537ccb15c795c",
    "execute_JAL": "b850479aee4f29c4542dd4b2d9857d57b04794f9a587e90fa2377be6f64c962c",
    "execute_JALR": "139c832101e69ab7d95f5807054fa0e9c4b373610eaf6970784b87bef0403004",
    "execute_ZBA_RTYPE": "8db4811954a3849493010308cbf1fa622597528948ba51ca6c6ec4990dc4df47",
    "execute_ZBA_RTYPEUW": "6e7b015b91752162c15bf4ec29976290cbf0426b1ff1c8f1394e34af50d70a1d",
    "execute_SLLIUW": "0319be6f870da63b53b009e541049ea61eae8787c0fbfbd706c29cf72e28a879",
    "execute_ZBS_RTYPE": "f4d853548e72f58c24c21929860c23a884043f109751f61f0c5b8e5dc997432c",
    "execute_ZBS_IOP": "2a490f2b60ed6c8e953eb374922fa4212aabffb853be571d7485b0dfb78cc586",
    "execute_ZBB_RTYPE": "501dda2321ad1cfdf0eb958ba4d62728eca29e5e6833f1e8112269f9d52bbb81",
    "execute_ZBB_RTYPEW": "6a332f1159157f5d86209ddd1a58e6813183739d074adbb1f05c917c6b5a46dd",
    "execute_RORI": "31efd803326e6d546f913928c79b3e6f27de33c4f87753de3f44171b9b83e762",
    "execute_RORIW": "77851b15138ceda3df28d2f088c65ca2107e2a62a93a195a7f913bd8316826bc",
    "execute_ZBB_EXTOP": "9ba3f7e90897b89973ad71eb7575a59d53231a47b10ce7dc3f09fa63257aee30",
    "execute_REV8": "b234cd12e497657fd4293ee326f6b9bc86bff11a6bd6a497be12e2eea65ad828",
    "execute_ORCB": "66023e65f48b814e64038cefba62d3aceb6c3e06c28e10c8c6e70368eeb0f7cf",
    "execute_CLZ": "c73bfa76c3031cf3f6a59ab0378a92804dd3e8a865d116ef85a327ba7e62f07d",
    "execute_CLZW": "4b97b4c0f41d5d712550517dca33b8c49aa23a58b9d40fe1bcf189bd8919e7ca",
    "execute_CTZ": "a80a5e54be59e80547ef7fbc22f61d725bbb43ae516ab65928e43d4774261073",
    "execute_CTZW": "47beb551d2158db05ba9e401ea30fbc793c7fa825dd10307eafb8665edd6973c",
    "execute_CPOP": "dc593565e3ae94358c4a67a0969befdbde6e211a3ec038fda5c95ba9b00f6e41",
    "execute_CPOPW": "81a2ab36c9d46ee81040788401a05645b7dbddaa11f253576439a5a337398fdd",
}


def extract_instsend_def_snippet(text: str, def_name: str) -> str:
    marker = f"def {def_name} "
    s_idx = text.find(marker)
    if s_idx < 0:
        raise ValueError(f"Could not locate `{marker.strip()}` in {UPSTREAM_INSTSEND_REL}")
    e_idx = text.find("\n\n", s_idx)
    if e_idx < 0:
        e_idx = len(text)
    return text[s_idx:e_idx]


def sha256_bytes(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def strip_lean_comments_and_strings(text: str) -> str:
    out: list[str] = []
    depth = 0
    in_str = False
    i = 0
    while i < len(text):
        if depth == 0 and not in_str and text.startswith("--", i):
            while i < len(text) and text[i] != "\n":
                i += 1
        elif not in_str and text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
        elif in_str:
            if text[i] == "\\" and i + 1 < len(text):
                out.append("  ")
                i += 2
            elif text[i] == '"':
                in_str = False
                out.append('"')
                i += 1
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text[i] == '"':
            in_str = True
            out.append('"')
            i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def extract_canonical_policy_slice(text: str) -> str:
    start_marker = "@[inline]\ndef riscvDivU64Spec"
    end_marker = "\n\n@[inline]\ndef specAuditWitnessGate"
    s_idx = text.find(start_marker)
    e_idx = text.find(end_marker, s_idx if s_idx >= 0 else 0)
    if s_idx < 0 or e_idx < 0:
        raise ValueError(f"Could not locate riscvDivU64Spec..riscvRemU64Spec slice in {POLICY_GATES_REL}")
    return text[s_idx:e_idx]


def extract_canonical_types_slice(text: str) -> str:
    start_marker = "/-- Carryless product, low 64 bits. One definition for Eval, LLVM, Metal and PTX. -/\ndef clmul64"
    end_marker = "\n/-- Parity of the low 8 bits:"
    s_idx = text.find(start_marker)
    e_idx = text.find(end_marker, s_idx if s_idx >= 0 else 0)
    if s_idx < 0 or e_idx < 0:
        raise ValueError(f"Could not locate clmul64..clmul64Hi slice in {TYPES_REL}")
    return text[s_idx:e_idx]


def extract_mirrored_slice(text: str, rel: str) -> str:
    b_tag = f"-- BEGIN MIRRORED SLICE: {rel}\n"
    e_tag = f"\n-- END MIRRORED SLICE: {rel}"
    s_idx = text.find(b_tag)
    e_idx = text.find(e_tag, s_idx if s_idx >= 0 else 0)
    if s_idx < 0 or e_idx < 0:
        raise ValueError(f"Missing mirrored slice markers for {rel}")
    return text[s_idx + len(b_tag) : e_idx]


def render_mirrored_model(policy_slice: str, types_slice: str) -> str:
    return (
        "/-!\n"
        "# Stage 3E / Milestone `M5` Mirrored `TurboLean` & `LeanNative` RV64 Scalar/Zbc Model\n\n"
        "This module contains exact, byte-synchronized slices of:\n"
        "1. `TurboLean.PolicyGates.riscvDivU64Spec` and `TurboLean.PolicyGates.riscvRemU64Spec`\n"
        f"   (`{POLICY_GATES_REL}`)\n"
        "2. `LeanNative.IR.clmul64` and `LeanNative.IR.clmul64Hi`\n"
        f"   (`{TYPES_REL}`)\n\n"
        "Enforced byte-for-byte against the root `turbo-lean` repository by\n"
        "`scripts/check_sail_riscv_bridge_sync.py`.\n"
        "-/\n\n"
        "namespace TurboLean.PolicyGates\n\n"
        f"-- BEGIN MIRRORED SLICE: {POLICY_GATES_REL}\n"
        f"{policy_slice}\n"
        f"-- END MIRRORED SLICE: {POLICY_GATES_REL}\n\n"
        "end TurboLean.PolicyGates\n\n"
        "namespace LeanNative.IR\n\n"
        f"-- BEGIN MIRRORED SLICE: {TYPES_REL}\n"
        f"{types_slice}\n"
        f"-- END MIRRORED SLICE: {TYPES_REL}\n\n"
        "end LeanNative.IR\n"
    )


def check_bridge_tree(root_dir: Path, sync_mirrors: bool = False) -> dict[str, object]:
    bridge_root = root_dir / "verification" / "sail-riscv-bridge"
    errors: list[str] = []

    if not bridge_root.is_dir():
        return {"ok": False, "errors": [f"Missing bridge directory: {bridge_root}"]}

    policy_path = root_dir / POLICY_GATES_REL
    types_path = root_dir / TYPES_REL
    mirrored_path = bridge_root / "SailRiscvBridge" / "MirroredModel.lean"
    slice_digests: dict[str, str] = {}

    if not policy_path.is_file():
        errors.append(f"Missing canonical file: {policy_path}")
    if not types_path.is_file():
        errors.append(f"Missing canonical file: {types_path}")

    if policy_path.is_file() and types_path.is_file():
        try:
            c_policy = extract_canonical_policy_slice(policy_path.read_text(encoding="utf-8"))
            c_types = extract_canonical_types_slice(types_path.read_text(encoding="utf-8"))
            slice_digests[POLICY_GATES_REL] = sha256_bytes(c_policy.encode("utf-8"))
            slice_digests[TYPES_REL] = sha256_bytes(c_types.encode("utf-8"))
            if sync_mirrors:
                mirrored_path.parent.mkdir(parents=True, exist_ok=True)
                mirrored_path.write_text(render_mirrored_model(c_policy, c_types), encoding="utf-8")
            if not mirrored_path.is_file():
                errors.append(f"Missing mirrored model file: {mirrored_path}")
            else:
                m_txt = mirrored_path.read_text(encoding="utf-8")
                m_policy = extract_mirrored_slice(m_txt, POLICY_GATES_REL)
                m_types = extract_mirrored_slice(m_txt, TYPES_REL)
                if m_policy != c_policy:
                    errors.append(
                        f"Drift detected in {POLICY_GATES_REL} slice "
                        "(run `python3 scripts/check_sail_riscv_bridge_sync.py --sync`)"
                    )
                if m_types != c_types:
                    errors.append(
                        f"Drift detected in {TYPES_REL} slice "
                        "(run `python3 scripts/check_sail_riscv_bridge_sync.py --sync`)"
                    )
        except Exception as exc:
            errors.append(f"Slice extraction failed: {exc}")

    tc_file = bridge_root / "lean-toolchain"
    if not tc_file.is_file():
        errors.append(f"Missing {tc_file}")
    elif tc_file.read_text(encoding="utf-8").strip() != PINNED_TOOLCHAIN:
        errors.append(
            f"lean-toolchain mismatch: {tc_file.read_text(encoding='utf-8').strip()!r} != {PINNED_TOOLCHAIN!r}"
        )

    lakefile = bridge_root / "lakefile.toml"
    if not lakefile.is_file():
        errors.append(f"Missing {lakefile}")
    else:
        lf_txt = lakefile.read_text(encoding="utf-8")
        if PINNED_SAIL_RISCV_URL not in lf_txt:
            errors.append(f"lakefile.toml missing {PINNED_SAIL_RISCV_URL}")
        if PINNED_SAIL_RISCV_REV not in lf_txt:
            errors.append(f"lakefile.toml missing pinned rev {PINNED_SAIL_RISCV_REV}")

    manifest = bridge_root / "lake-manifest.json"
    if not manifest.is_file():
        errors.append(f"Missing committed {manifest}")
    else:
        try:
            mf = json.loads(manifest.read_text(encoding="utf-8"))
            if mf.get("name") not in ("«sail-riscv-bridge»", "sail-riscv-bridge"):
                errors.append(
                    f"lake-manifest.json root `name` must be '«sail-riscv-bridge»', got {mf.get('name')!r}"
                )
            raw_pkgs = mf.get("packages", [])
            if len(raw_pkgs) != 2:
                errors.append(
                    f"lake-manifest.json expected exactly 2 dependencies (`Lean_RV64D` and `Sail`), got {len(raw_pkgs)}"
                )
            pkgs = {p.get("name"): p for p in raw_pkgs}
            rv_pkg = pkgs.get("Lean_RV64D")
            if not rv_pkg or rv_pkg.get("rev") != PINNED_SAIL_RISCV_REV:
                errors.append(
                    f"lake-manifest.json Lean_RV64D rev mismatch: {rv_pkg.get('rev') if rv_pkg else None} != {PINNED_SAIL_RISCV_REV}"
                )
            if rv_pkg and rv_pkg.get("url") != PINNED_SAIL_RISCV_URL:
                errors.append(
                    f"lake-manifest.json Lean_RV64D url mismatch: {rv_pkg.get('url')} != {PINNED_SAIL_RISCV_URL}"
                )
            sail_pkg = pkgs.get("Sail")
            if not sail_pkg or sail_pkg.get("rev") != PINNED_SAIL_REV:
                errors.append(
                    f"lake-manifest.json Sail rev mismatch: {sail_pkg.get('rev') if sail_pkg else None} != {PINNED_SAIL_REV}"
                )
            if sail_pkg and not str(sail_pkg.get("url", "")).rstrip(".git").endswith("rems-project/lean-sail"):
                errors.append(
                    f"lake-manifest.json Sail url mismatch: {sail_pkg.get('url')} != {PINNED_SAIL_URL}"
                )
        except Exception as exc:
            errors.append(f"Invalid lake-manifest.json: {exc}")

    root_bridge_lean = bridge_root / "SailRiscvBridge.lean"
    bridged_refs: list[str] = []
    if not root_bridge_lean.is_file():
        errors.append(f"Missing {root_bridge_lean}")
    else:
        rb_stripped = strip_lean_comments_and_strings(root_bridge_lean.read_text(encoding="utf-8"))
        if "#verify_sail_riscv_bridge_axioms" not in rb_stripped:
            errors.append("SailRiscvBridge.lean missing `#verify_sail_riscv_bridge_axioms` gate")
        if "Lean.collectAxioms" not in rb_stripped:
            errors.append("SailRiscvBridge.lean missing `Lean.collectAxioms` audit")
        if "bridgedTheorems.Nodup" not in rb_stripped:
            errors.append("SailRiscvBridge.lean missing `bridgedTheorems.Nodup` uniqueness theorem")
        bridged_refs = re.findall(r"``SailRiscvBridge\.[A-Za-z0-9_?']+", rb_stripped)
        if len(bridged_refs) != len(set(bridged_refs)):
            seen_refs: set[str] = set()
            dups = sorted({r for r in bridged_refs if r in seen_refs or seen_refs.add(r)})  # type: ignore[func-returns-value]
            errors.append(
                f"SailRiscvBridge.lean contains duplicate bridged theorem references: {dups}"
            )
        if len(set(bridged_refs)) < MIN_AUDITED_THEOREMS:
            errors.append(
                f"SailRiscvBridge.lean audits only {len(set(bridged_refs))} unique bridged theorems "
                f"(expected >= {MIN_AUDITED_THEOREMS})"
            )

    sub_lean_files = (
        sorted((bridge_root / "SailRiscvBridge").rglob("*.lean"))
        if (bridge_root / "SailRiscvBridge").is_dir()
        else []
    )
    proof_files = [root_bridge_lean, *sub_lean_files]
    if len(proof_files) < 3:
        errors.append("Expected SailRiscvBridge.lean, MirroredModel.lean, and Bisimulation.lean")

    for pf in proof_files:
        if not pf.is_file():
            errors.append(f"Missing proof file: {pf}")
            continue
        rel_str = str(pf.relative_to(root_dir))
        stripped = strip_lean_comments_and_strings(pf.read_text(encoding="utf-8"))
        m = FORBIDDEN_PROOF_TOKENS.search(stripped)
        if m:
            errors.append(f"Forbidden token `{m.group(0).strip()}` in {rel_str}")
        mi = FORBIDDEN_IMPORTS.search(stripped)
        if mi:
            errors.append(f"Forbidden heavy import `{mi.group(0).strip()}` in {rel_str}")

    instsend_path = bridge_root / UPSTREAM_INSTSEND_REL
    upstream_instsend_checked = False
    upstream_instsend_digests: dict[str, str] = {}
    if instsend_path.is_file():
        upstream_instsend_checked = True
        try:
            instsend_txt = instsend_path.read_text(encoding="utf-8")
            for def_name, expected_sha in PINNED_INSTSEND_SNIPPET_DIGESTS.items():
                snippet = extract_instsend_def_snippet(instsend_txt, def_name)
                actual_sha = sha256_bytes(snippet.encode("utf-8"))
                upstream_instsend_digests[def_name] = actual_sha
                if actual_sha != expected_sha:
                    errors.append(
                        f"Upstream InstsEnd.lean `{def_name}` snippet SHA-256 mismatch: "
                        f"{actual_sha} != {expected_sha}"
                    )
        except Exception as exc:
            errors.append(f"Upstream InstsEnd.lean snippet check failed: {exc}")

    return {
        "ok": len(errors) == 0,
        "pinned_toolchain": PINNED_TOOLCHAIN,
        "pinned_sail_riscv_rev": PINNED_SAIL_RISCV_REV,
        "pinned_sail_rev": PINNED_SAIL_REV,
        "bridged_theorems_count": len(bridged_refs),
        "slice_digests": slice_digests,
        "upstream_instsend_checked": upstream_instsend_checked,
        "upstream_instsend_digests": upstream_instsend_digests,
        "proof_files_checked": len(proof_files),
        "errors": errors,
    }


SYNTHETIC_EXECUTE_DIV_SNIPPET = """\
def execute_DIV (rs2 : regidx) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  let rs2_bits ← do (rX_bits rs2)
  let rs1_int :=
    if (is_unsigned : Bool)
    then (BitVec.toNatInt rs1_bits)
    else (BitVec.toInt rs1_bits)
  let rs2_int :=
    if (is_unsigned : Bool)
    then (BitVec.toNatInt rs2_bits)
    else (BitVec.toInt rs2_bits)
  let quotient :=
    if ((rs2_int == 0) : Bool)
    then (Neg.neg 1)
    else (Int.tdiv rs1_int rs2_int)
  let quotient :=
    if (((not is_unsigned) && (quotient ≥b (2 ^i (xlen -i 1)))) : Bool)
    then (Neg.neg (2 ^i (xlen -i 1)))
    else quotient
  (wX_bits rd (to_bits_truncate (l := 64) quotient))
  (pure RETIRE_SUCCESS)"""

SYNTHETIC_EXECUTE_REM_SNIPPET = """\
def execute_REM (rs2 : regidx) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  let rs2_bits ← do (rX_bits rs2)
  let rs1_int :=
    if (is_unsigned : Bool)
    then (BitVec.toNatInt rs1_bits)
    else (BitVec.toInt rs1_bits)
  let rs2_int :=
    if (is_unsigned : Bool)
    then (BitVec.toNatInt rs2_bits)
    else (BitVec.toInt rs2_bits)
  let remainder :=
    if ((rs2_int == 0) : Bool)
    then rs1_int
    else (Int.tmod rs1_int rs2_int)
  (wX_bits rd (to_bits_truncate (l := 64) remainder))
  (pure RETIRE_SUCCESS)"""

SYNTHETIC_EXECUTE_RTYPE_SNIPPET = """\
def execute_RTYPE (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : rop) : SailM ExecutionResult := do
  (wX_bits rd
    (← do
      match op with
      | .ADD => (pure ((← (rX_bits rs1)) + (← (rX_bits rs2))))
      | .SLT =>
        (pure (zero_extend (m := 64)
            (bool_to_bit (zopz0zI_s (← (rX_bits rs1)) (← (rX_bits rs2))))))
      | .SLTU =>
        (pure (zero_extend (m := 64)
            (bool_to_bit (zopz0zI_u (← (rX_bits rs1)) (← (rX_bits rs2))))))
      | .AND => (pure ((← (rX_bits rs1)) &&& (← (rX_bits rs2))))
      | .OR => (pure ((← (rX_bits rs1)) ||| (← (rX_bits rs2))))
      | .XOR => (pure ((← (rX_bits rs1)) ^^^ (← (rX_bits rs2))))
      | .SLL =>
        (pure (shift_bits_left (← (rX_bits rs1))
            (Sail.BitVec.extractLsb (← (rX_bits rs2)) (log2_xlen -i 1) 0)))
      | .SRL =>
        (pure (shift_bits_right (← (rX_bits rs1))
            (Sail.BitVec.extractLsb (← (rX_bits rs2)) (log2_xlen -i 1) 0)))
      | .SUB => (pure ((← (rX_bits rs1)) - (← (rX_bits rs2))))
      | .SRA =>
        (pure (shift_bits_right_arith (← (rX_bits rs1))
            (Sail.BitVec.extractLsb (← (rX_bits rs2)) (log2_xlen -i 1) 0)))))
  (pure RETIRE_SUCCESS)"""

SYNTHETIC_EXECUTE_ITYPE_SNIPPET = """\
def execute_ITYPE (imm : (BitVec 12)) (rs1 : regidx) (rd : regidx) (op : iop) : SailM ExecutionResult := do
  let immext : xlenbits := (sign_extend (m := 64) imm)
  (wX_bits rd
    (← do
      match op with
      | .ADDI => (pure ((← (rX_bits rs1)) + immext))
      | .SLTI => (pure (zero_extend (m := 64) (bool_to_bit (zopz0zI_s (← (rX_bits rs1)) immext))))
      | .SLTIU =>
        (pure (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (← (rX_bits rs1)) immext))))
      | .ANDI => (pure ((← (rX_bits rs1)) &&& immext))
      | .ORI => (pure ((← (rX_bits rs1)) ||| immext))
      | .XORI => (pure ((← (rX_bits rs1)) ^^^ immext))))
  (pure RETIRE_SUCCESS)"""

SYNTHETIC_EXECUTE_SHIFTIOP_SNIPPET = """\
def execute_SHIFTIOP (shamt : (BitVec 6)) (rs1 : regidx) (rd : regidx) (op : sop) : SailM ExecutionResult := do
  let shamt := (Sail.BitVec.extractLsb shamt (log2_xlen -i 1) 0)
  (wX_bits rd
    (← do
      match op with
      | .SLLI => (pure (shift_bits_left (← (rX_bits rs1)) shamt))
      | .SRLI => (pure (shift_bits_right (← (rX_bits rs1)) shamt))
      | .SRAI => (pure (shift_bits_right_arith (← (rX_bits rs1)) shamt))))
  (pure RETIRE_SUCCESS)"""

SYNTHETIC_EXECUTE_UTYPE_SNIPPET = """\
def execute_UTYPE (imm : (BitVec 20)) (rd : regidx) (op : uop) : SailM ExecutionResult := do
  let off : xlenbits := (sign_extend (m := 64) (imm +++ 0x000#12))
  (wX_bits rd
    (← do
      match op with
      | .LUI => (pure off)
      | .AUIPC => (pure ((← (get_arch_pc ())) + off))))
  (pure RETIRE_SUCCESS)"""

SYNTHETIC_EXECUTE_BTYPE_SNIPPET = """\
def execute_BTYPE (imm : (BitVec 13)) (rs2 : regidx) (rs1 : regidx) (op : bop) : SailM ExecutionResult := do
  let taken ← (( do
    match op with
    | .BEQ => (pure ((← (rX_bits rs1)) == (← (rX_bits rs2))))
    | .BNE => (pure ((← (rX_bits rs1)) != (← (rX_bits rs2))))
    | .BLT => (pure (zopz0zI_s (← (rX_bits rs1)) (← (rX_bits rs2))))
    | .BGE => (pure (zopz0zKzJ_s (← (rX_bits rs1)) (← (rX_bits rs2))))
    | .BLTU => (pure (zopz0zI_u (← (rX_bits rs1)) (← (rX_bits rs2))))
    | .BGEU => (pure (zopz0zKzJ_u (← (rX_bits rs1)) (← (rX_bits rs2)))) ) : SailM Bool )
  if (taken : Bool)
  then (jump_to ((← readReg PC) + (sign_extend (m := 64) imm)))
  else (pure RETIRE_SUCCESS)"""

SYNTHETIC_EXTRA_INSTSEND_SNIPPETS = """\
def execute_MUL (rs2 : regidx) (rs1 : regidx) (rd : regidx) (mul_op : mul_op) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  let rs2_bits ← do (rX_bits rs2)
  (wX_bits rd
    (mult_to_bits_half (l := xlen) mul_op.signed_rs1 mul_op.signed_rs2 rs1_bits rs2_bits
      mul_op.result_part))
  (pure RETIRE_SUCCESS)

def execute_CLMUL (rs2 : regidx) (rs1 : regidx) (rd : regidx) : SailM ExecutionResult := do
  let prod ← do (pure (carryless_mul (← (rX_bits rs1)) (← (rX_bits rs2))))
  (wX_bits rd (Sail.BitVec.extractLsb prod (xlen -i 1) 0))
  (pure RETIRE_SUCCESS)

def execute_CLMULH (rs2 : regidx) (rs1 : regidx) (rd : regidx) : SailM ExecutionResult := do
  let prod ← do (pure (carryless_mul (← (rX_bits rs1)) (← (rX_bits rs2))))
  (wX_bits rd (Sail.BitVec.extractLsb prod ((2 *i xlen) -i 1) xlen))
  (pure RETIRE_SUCCESS)

def execute_CLMULR (rs2 : regidx) (rs1 : regidx) (rd : regidx) : SailM ExecutionResult := do
  (wX_bits rd (carryless_mulr (← (rX_bits rs1)) (← (rX_bits rs2))))
  (pure RETIRE_SUCCESS)

def execute_RTYPEW (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : ropw) : SailM ExecutionResult := do
  let rs1_val ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs1)) 31 0))
  let rs2_val ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs2)) 31 0))
  let result : (BitVec 32) :=
    match op with
    | .ADDW => (rs1_val + rs2_val)
    | .SUBW => (rs1_val - rs2_val)
    | .SLLW => (shift_bits_left rs1_val (Sail.BitVec.extractLsb rs2_val 4 0))
    | .SRLW => (shift_bits_right rs1_val (Sail.BitVec.extractLsb rs2_val 4 0))
    | .SRAW => (shift_bits_right_arith rs1_val (Sail.BitVec.extractLsb rs2_val 4 0))
  (wX_bits rd (sign_extend (m := 64) result))
  (pure RETIRE_SUCCESS)

def execute_ADDIW (imm : (BitVec 12)) (rs1 : regidx) (rd : regidx) : SailM ExecutionResult := do
  let result ← do (pure ((← (rX_bits rs1)) + (sign_extend (m := 64) imm)))
  (wX_bits rd (sign_extend (m := 64) (Sail.BitVec.extractLsb result 31 0)))
  (pure RETIRE_SUCCESS)

def execute_SHIFTIWOP (shamt : (BitVec 5)) (rs1 : regidx) (rd : regidx) (op : sopw) : SailM ExecutionResult := do
  let rs1_val ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs1)) 31 0))
  let result : (BitVec 32) :=
    match op with
    | .SLLIW => (shift_bits_left rs1_val shamt)
    | .SRLIW => (shift_bits_right rs1_val shamt)
    | .SRAIW => (shift_bits_right_arith rs1_val shamt)
  (wX_bits rd (sign_extend (m := 64) result))
  (pure RETIRE_SUCCESS)

def execute_MULW (rs2 : regidx) (rs1 : regidx) (rd : regidx) : SailM ExecutionResult := do
  let rs1_bits ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs1)) 31 0))
  let rs2_bits ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs2)) 31 0))
  let rs1_int := (BitVec.toInt rs1_bits)
  let rs2_int := (BitVec.toInt rs2_bits)
  let result32 : (BitVec 32) := (to_bits_truncate (l := 32) (rs1_int *i rs2_int))
  (wX_bits rd (sign_extend (m := 64) result32))
  (pure RETIRE_SUCCESS)

def execute_DIVW (rs2 : regidx) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) : SailM ExecutionResult := do
  let rs1_bits ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs1)) 31 0))
  let rs2_bits ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs2)) 31 0))
  let rs1_int :=
    if (is_unsigned : Bool)
    then (BitVec.toNatInt rs1_bits)
    else (BitVec.toInt rs1_bits)
  let rs2_int :=
    if (is_unsigned : Bool)
    then (BitVec.toNatInt rs2_bits)
    else (BitVec.toInt rs2_bits)
  let quotient :=
    if ((rs2_int == 0) : Bool)
    then (Neg.neg 1)
    else (Int.tdiv rs1_int rs2_int)
  let quotient :=
    if (((not is_unsigned) && (quotient ≥b (2 ^i 31))) : Bool)
    then (Neg.neg (2 ^i 31))
    else quotient
  (wX_bits rd (sign_extend (m := 64) (to_bits_truncate (l := 32) quotient)))
  (pure RETIRE_SUCCESS)

def execute_REMW (rs2 : regidx) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) : SailM ExecutionResult := do
  let rs1_bits ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs1)) 31 0))
  let rs2_bits ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs2)) 31 0))
  let rs1_int :=
    if (is_unsigned : Bool)
    then (BitVec.toNatInt rs1_bits)
    else (BitVec.toInt rs1_bits)
  let rs2_int :=
    if (is_unsigned : Bool)
    then (BitVec.toNatInt rs2_bits)
    else (BitVec.toInt rs2_bits)
  let remainder :=
    if ((rs2_int == 0) : Bool)
    then rs1_int
    else (Int.tmod rs1_int rs2_int)
  (wX_bits rd (sign_extend (m := 64) (to_bits_truncate (l := 32) remainder)))
  (pure RETIRE_SUCCESS)

def execute_JAL (imm : (BitVec 21)) (rd : regidx) : SailM ExecutionResult := do
  let link_address ← do (get_next_pc ())
  match (← (jump_to ((← readReg PC) + (sign_extend (m := 64) imm)))) with
  | .Retire_Success () =>
    (do
      (wX_bits rd link_address)
      (pure (Retire_Success ())))
  | failure => (pure failure)

def execute_JALR (imm : (BitVec 12)) (rs1 : regidx) (rd : regidx) : SailM ExecutionResult := do
  (update_elp_state rs1)
  let link_address ← do (get_next_pc ())
  let target ← do (pure ((← (rX_bits rs1)) + (sign_extend (m := 64) imm)))
  match (← (jump_to (BitVec.update target 0 0#1))) with
  | .Retire_Success () =>
    (do
      (wX_bits rd link_address)
      (pure (Retire_Success ())))
  | failure => (pure failure)

def execute_ZBA_RTYPE (rs2 : regidx) (rs1 : regidx) (rd : regidx) (shamt : (BitVec 2)) : SailM ExecutionResult := do
  (wX_bits rd ((shift_bits_left (← (rX_bits rs1)) shamt) + (← (rX_bits rs2))))
  (pure RETIRE_SUCCESS)

def execute_ZBA_RTYPEUW (rs2 : regidx) (rs1 : regidx) (rd : regidx) (shamt : (BitVec 2)) : SailM ExecutionResult := do
  (wX_bits rd
    ((shift_bits_left (zero_extend (m := 64) (Sail.BitVec.extractLsb (← (rX_bits rs1)) 31 0))
        shamt) + (← (rX_bits rs2))))
  (pure RETIRE_SUCCESS)

def execute_SLLIUW (shamt : (BitVec 6)) (rs1 : regidx) (rd : regidx) : SailM ExecutionResult := do
  (wX_bits rd
    (shift_bits_left (zero_extend (m := 64) (Sail.BitVec.extractLsb (← (rX_bits rs1)) 31 0)) shamt))
  (pure RETIRE_SUCCESS)

def execute_ZBS_RTYPE (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : brop_zbs) : SailM ExecutionResult := do
  let rs1_val ← do (rX_bits rs1)
  let rs2_val ← do (rX_bits rs2)
  let mask : xlenbits :=
    (shift_bits_left (zero_extend (m := 64) 1#1) (Sail.BitVec.extractLsb rs2_val 5 0))
  let result : xlenbits :=
    match op with
    | .BCLR => (rs1_val &&& (Complement.complement mask))
    | .BEXT => (zero_extend (m := 64) (bool_to_bit ((rs1_val &&& mask) != (zeros (n := 64)))))
    | .BINV => (rs1_val ^^^ mask)
    | .BSET => (rs1_val ||| mask)
  (wX_bits rd result)
  (pure RETIRE_SUCCESS)

def execute_ZBS_IOP (shamt : (BitVec 6)) (rs1 : regidx) (rd : regidx) (op : biop_zbs) : SailM ExecutionResult := do
  let rs1_val ← do (rX_bits rs1)
  let mask : xlenbits := (shift_bits_left (zero_extend (m := 64) 1#1) shamt)
  let result : xlenbits :=
    match op with
    | .BCLRI => (rs1_val &&& (Complement.complement mask))
    | .BEXTI => (zero_extend (m := 64) (bool_to_bit ((rs1_val &&& mask) != (zeros (n := 64)))))
    | .BINVI => (rs1_val ^^^ mask)
    | .BSETI => (rs1_val ||| mask)
  (wX_bits rd result)
  (pure RETIRE_SUCCESS)

def execute_ZBB_RTYPE (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : brop_zbb) : SailM ExecutionResult := do
  let rs1_val ← do (rX_bits rs1)
  let rs2_val ← do (rX_bits rs2)
  let result : xlenbits :=
    match op with
    | .ANDN => (rs1_val &&& (Complement.complement rs2_val))
    | .ORN => (rs1_val ||| (Complement.complement rs2_val))
    | .XNOR => (Complement.complement (rs1_val ^^^ rs2_val))
    | .MAX =>
      (if ((zopz0zK_s rs1_val rs2_val) : Bool)
      then rs1_val
      else rs2_val)
    | .MAXU =>
      (if ((zopz0zK_u rs1_val rs2_val) : Bool)
      then rs1_val
      else rs2_val)
    | .MIN =>
      (if ((zopz0zI_s rs1_val rs2_val) : Bool)
      then rs1_val
      else rs2_val)
    | .MINU =>
      (if ((zopz0zI_u rs1_val rs2_val) : Bool)
      then rs1_val
      else rs2_val)
    | .ROL => (rotate_bits_left rs1_val (Sail.BitVec.extractLsb rs2_val (log2_xlen -i 1) 0))
    | .ROR => (rotate_bits_right rs1_val (Sail.BitVec.extractLsb rs2_val (log2_xlen -i 1) 0))
  (wX_bits rd result)
  (pure RETIRE_SUCCESS)

def execute_ZBB_RTYPEW (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : bropw_zbb) : SailM ExecutionResult := do
  let rs1_val ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs1)) 31 0))
  let shamt ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs2)) 4 0))
  let result : (BitVec 32) :=
    match op with
    | .ROLW => (rotate_bits_left rs1_val shamt)
    | .RORW => (rotate_bits_right rs1_val shamt)
  (wX_bits rd (sign_extend (m := 64) result))
  (pure RETIRE_SUCCESS)

def execute_RORI (shamt : (BitVec 6)) (rs1 : regidx) (rd : regidx) : SailM ExecutionResult := do
  let shamt := (Sail.BitVec.extractLsb shamt (log2_xlen -i 1) 0)
  (wX_bits rd (rotate_bits_right (← (rX_bits rs1)) shamt))
  (pure RETIRE_SUCCESS)

def execute_RORIW (shamt : (BitVec 5)) (rs1 : regidx) (rd : regidx) : SailM ExecutionResult := do
  (wX_bits rd
    (sign_extend (m := 64)
      (rotate_bits_right (Sail.BitVec.extractLsb (← (rX_bits rs1)) 31 0) shamt)))
  (pure RETIRE_SUCCESS)

def execute_ZBB_EXTOP (rs1 : regidx) (rd : regidx) (op : extop_zbb) : SailM ExecutionResult := do
  let rs1_val ← do (rX_bits rs1)
  let result : xlenbits :=
    match op with
    | .SEXTB => (sign_extend (m := 64) (Sail.BitVec.extractLsb rs1_val 7 0))
    | .SEXTH => (sign_extend (m := 64) (Sail.BitVec.extractLsb rs1_val 15 0))
    | .ZEXTH => (zero_extend (m := 64) (Sail.BitVec.extractLsb rs1_val 15 0))
  (wX_bits rd result)
  (pure RETIRE_SUCCESS)

def execute_REV8 (rs1 : regidx) (rd : regidx) : SailM ExecutionResult := do
  (wX_bits rd (rev8 (← (rX_bits rs1))))
  (pure RETIRE_SUCCESS)

def execute_ORCB (rs1 : regidx) (rd : regidx) : SailM ExecutionResult := do
  let rs1_val ← do (rX_bits rs1)
  let result : xlenbits := (zeros (n := 64))
  let result ← (( do
    let loop_i_lower := 0
    let loop_i_upper := (xlen -i 8)
    let mut loop_vars := result
    for i in [loop_i_lower:loop_i_upper:8]i do
      let result := loop_vars
      loop_vars :=
        (Sail.BitVec.updateSubrange result (i +i 7) i
          (if (((Sail.BitVec.extractLsb rs1_val (i +i 7) i) == (zeros (n := (((i +i 7) -i i) +i 1)))) : Bool)
          then 0x00#8
          else 0xFF#8))
    (pure loop_vars) ) : SailM (BitVec 64) )
  (wX_bits rd result)
  (pure RETIRE_SUCCESS)

def execute_CLZ (rs1 : regidx) (rd : regidx) : SailM ExecutionResult := do
  (wX_bits rd (to_bits (l := 64) (BitVec.countLeadingZeros (← (rX_bits rs1)))))
  (pure RETIRE_SUCCESS)

def execute_CLZW (rs1 : regidx) (rd : regidx) : SailM ExecutionResult := do
  (wX_bits rd
    (to_bits (l := 64) (BitVec.countLeadingZeros (Sail.BitVec.extractLsb (← (rX_bits rs1)) 31 0))))
  (pure RETIRE_SUCCESS)

def execute_CTZ (rs1 : regidx) (rd : regidx) : SailM ExecutionResult := do
  (wX_bits rd (to_bits (l := 64) (BitVec.countTrailingZeros (← (rX_bits rs1)))))
  (pure RETIRE_SUCCESS)

def execute_CTZW (rs1 : regidx) (rd : regidx) : SailM ExecutionResult := do
  (wX_bits rd
    (to_bits (l := 64) (BitVec.countTrailingZeros (Sail.BitVec.extractLsb (← (rX_bits rs1)) 31 0))))
  (pure RETIRE_SUCCESS)

def execute_CPOP (rs1 : regidx) (rd : regidx) : SailM ExecutionResult := do
  (wX_bits rd (to_bits (l := 64) (← (count_ones (← (rX_bits rs1))))))
  (pure RETIRE_SUCCESS)

def execute_CPOPW (rs1 : regidx) (rd : regidx) : SailM ExecutionResult := do
  (wX_bits rd
    (to_bits (l := 64) (← (count_ones (Sail.BitVec.extractLsb (← (rX_bits rs1)) 31 0)))))
  (pure RETIRE_SUCCESS)"""

SYNTHETIC_INSTSEND_TEXT = "\n\n".join(
    [
        SYNTHETIC_EXECUTE_UTYPE_SNIPPET,
        SYNTHETIC_EXECUTE_SHIFTIOP_SNIPPET,
        SYNTHETIC_EXECUTE_RTYPE_SNIPPET,
        SYNTHETIC_EXECUTE_REM_SNIPPET,
        SYNTHETIC_EXECUTE_ITYPE_SNIPPET,
        SYNTHETIC_EXECUTE_DIV_SNIPPET,
        SYNTHETIC_EXECUTE_BTYPE_SNIPPET,
        SYNTHETIC_EXTRA_INSTSEND_SNIPPETS,
    ]
) + "\n\n"


class SelfTests(unittest.TestCase):
    def test_live_repo_passes(self) -> None:
        rep = check_bridge_tree(ROOT_DIR)
        self.assertTrue(rep["ok"], rep)

    def test_detects_slice_drift_forbidden_tokens_and_heavy_imports(self) -> None:
        with tempfile.TemporaryDirectory(prefix="sail-riscv-sync-test-") as tmp:
            root = Path(tmp)
            for rel in (POLICY_GATES_REL, TYPES_REL):
                src = ROOT_DIR / rel
                dst = root / rel
                dst.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(src, dst)
            b_root = root / "verification" / "sail-riscv-bridge"
            (b_root / "SailRiscvBridge").mkdir(parents=True, exist_ok=True)
            for fn in ("lean-toolchain", "lakefile.toml", "lake-manifest.json", "SailRiscvBridge.lean"):
                shutil.copy2(BRIDGE_DIR / fn, b_root / fn)
            drifted = (BRIDGE_DIR / "SailRiscvBridge" / "MirroredModel.lean").read_text(encoding="utf-8")
            drifted = drifted.replace("0xffffffffffffffff", "0")
            (b_root / "SailRiscvBridge" / "MirroredModel.lean").write_text(drifted, encoding="utf-8")
            (b_root / "SailRiscvBridge" / "Bisimulation.lean").write_text(
                "import LeanRV64D.InstsEnd\n"
                'def ok := "-- bv_decide in string"\n'
                "theorem bad (x : BitVec 8) : x = x := by bv_decide\n",
                encoding="utf-8",
            )
            rep = check_bridge_tree(root)
            self.assertFalse(rep["ok"])
            errs = "\n".join(str(e) for e in rep["errors"])
            self.assertIn("Drift detected", errs)
            self.assertIn("Forbidden token `bv_decide`", errs)
            self.assertIn("Forbidden heavy import", errs)

    def test_upstream_instsend_snippet_digests_optional_and_tamper_detected(self) -> None:
        with tempfile.TemporaryDirectory(prefix="sail-riscv-instsend-test-") as tmp:
            root = Path(tmp)
            for rel in (POLICY_GATES_REL, TYPES_REL):
                src = ROOT_DIR / rel
                dst = root / rel
                dst.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(src, dst)
            b_root = root / "verification" / "sail-riscv-bridge"
            (b_root / "SailRiscvBridge").mkdir(parents=True, exist_ok=True)
            for fn in ("lean-toolchain", "lakefile.toml", "lake-manifest.json", "SailRiscvBridge.lean"):
                shutil.copy2(BRIDGE_DIR / fn, b_root / fn)
            for fn in ("MirroredModel.lean", "Bisimulation.lean"):
                shutil.copy2(BRIDGE_DIR / "SailRiscvBridge" / fn, b_root / "SailRiscvBridge" / fn)

            rep_absent = check_bridge_tree(root)
            self.assertTrue(rep_absent["ok"], rep_absent)
            self.assertFalse(rep_absent["upstream_instsend_checked"])
            self.assertEqual(rep_absent["upstream_instsend_digests"], {})

            instsend_file = b_root / UPSTREAM_INSTSEND_REL
            instsend_file.parent.mkdir(parents=True, exist_ok=True)
            instsend_file.write_text(SYNTHETIC_INSTSEND_TEXT, encoding="utf-8")
            rep_present = check_bridge_tree(root)
            self.assertTrue(rep_present["ok"], rep_present)
            self.assertTrue(rep_present["upstream_instsend_checked"])
            self.assertEqual(rep_present["upstream_instsend_digests"], PINNED_INSTSEND_SNIPPET_DIGESTS)

            instsend_file.write_text(
                SYNTHETIC_INSTSEND_TEXT.replace("(Neg.neg 1)", "(0 : Int)", 1),
                encoding="utf-8",
            )
            rep_tampered = check_bridge_tree(root)
            self.assertFalse(rep_tampered["ok"])
            self.assertTrue(rep_tampered["upstream_instsend_checked"])
            errs = "\n".join(str(e) for e in rep_tampered["errors"])
            self.assertIn("Upstream InstsEnd.lean `execute_DIV` snippet SHA-256 mismatch", errs)

    def test_rejects_duplicate_and_undercounted_bridged_theorems(self) -> None:
        with tempfile.TemporaryDirectory(prefix="sail-riscv-thm-ratchet-") as tmp:
            root = Path(tmp)
            for rel in (POLICY_GATES_REL, TYPES_REL):
                src = ROOT_DIR / rel
                dst = root / rel
                dst.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(src, dst)
            b_root = root / "verification" / "sail-riscv-bridge"
            (b_root / "SailRiscvBridge").mkdir(parents=True, exist_ok=True)
            for fn in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"):
                shutil.copy2(BRIDGE_DIR / fn, b_root / fn)
            for fn in ("MirroredModel.lean", "Bisimulation.lean"):
                shutil.copy2(BRIDGE_DIR / "SailRiscvBridge" / fn, b_root / "SailRiscvBridge" / fn)

            orig_root_lean = (BRIDGE_DIR / "SailRiscvBridge.lean").read_text(encoding="utf-8")
            dup_root_lean = orig_root_lean.replace(
                "``SailRiscvBridge.rv64ZbbCpop_bisim_sail",
                "``SailRiscvBridge.rv64_xlen_params",
                1,
            )
            (b_root / "SailRiscvBridge.lean").write_text(dup_root_lean, encoding="utf-8")
            rep_dup = check_bridge_tree(root)
            self.assertFalse(rep_dup["ok"])
            errs = "\n".join(str(e) for e in rep_dup["errors"])
            self.assertIn("duplicate bridged theorem references", errs)
            self.assertIn(f"expected >= {MIN_AUDITED_THEOREMS}", errs)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--sync", action="store_true", help="Re-render MirroredModel.lean from canonical slices")
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    if args.self_test:
        res = unittest.TextTestRunner(verbosity=2).run(
            unittest.defaultTestLoader.loadTestsFromTestCase(SelfTests)
        )
        return 0 if res.wasSuccessful() else 1

    rep = check_bridge_tree(ROOT_DIR, sync_mirrors=args.sync)
    if args.json:
        print(json.dumps(rep, indent=2, sort_keys=True))
    else:
        print(
            f"[sail-riscv-bridge-sync] ok={rep['ok']} "
            f"rev={str(rep['pinned_sail_riscv_rev'])[:12]} "
            f"theorems={rep.get('bridged_theorems_count', 0)} "
            f"slices={len(rep.get('slice_digests', {}))} "
            f"instsend={rep.get('upstream_instsend_checked', False)} "
            f"proof_files={rep.get('proof_files_checked', 0)}"
        )
    if not rep["ok"]:
        for err in rep["errors"]:  # type: ignore[union-attr]
            print(f"  [ERROR] {err}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
