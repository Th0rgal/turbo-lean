#!/usr/bin/env python3
"""Unit tests for `scripts/h1_lowering_inventory.py` (Horizon H1.0)."""
from __future__ import annotations

import json
import shutil
import tempfile
import unittest
from pathlib import Path
import sys

ROOT_DIR = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT_DIR / "scripts"))

import h1_lowering_inventory as h1  # noqa: E402


class TestH1LoweringInventory(unittest.TestCase):
    def test_live_repo_inventory_and_schema(self) -> None:
        rep = h1.check_inventory(ROOT_DIR)
        self.assertTrue(rep["ok"], rep.get("errors"))

        inv = h1.build_inventory(ROOT_DIR)
        self.assertEqual(inv["schemaVersion"], "turbo-lean-h1-lowering-inventory-v1")
        self.assertEqual(inv["horizon"], "H1.0")

        matrix = inv["lcnf_constructor_matrix"]
        self.assertGreaterEqual(len(matrix["rows"]), 25)
        valid_states = {"proved", "lowered_unproved", "rejected"}
        seen_ids: set[str] = set()
        for row in matrix["rows"]:
            cid = row["id"]
            self.assertNotIn(cid, seen_ids, f"duplicate constructor id {cid}")
            seen_ids.add(cid)
            self.assertIn(row["status"], valid_states)
            self.assertTrue(row["category"])
            self.assertTrue(row["evidence_file"])
            self.assertTrue(row["evidence_symbol"])

        summary = matrix["summary"]
        self.assertEqual(
            summary["total"],
            summary["proved"] + summary["lowered_unproved"] + summary["rejected"],
        )
        self.assertEqual(summary["total"], len(matrix["rows"]))

        corpora = inv["corpora"]
        for key in ("con_leche", "batteries_and_c2", "c1_run_tests"):
            self.assertIn(key, corpora)
            corp = corpora[key]
            self.assertEqual(
                corp["total_declarations"],
                corp["proved"] + corp["lowered_unproved"] + corp["rejected"],
            )
            rej_sum = sum(r["count"] for r in corp["rejection_reasons"])
            self.assertEqual(rej_sum, corp["rejected"])

        cl_exec = corpora["con_leche"]["executed_from_main"]
        self.assertEqual(
            cl_exec["total_declarations"],
            cl_exec["proved"] + cl_exec["lowered_unproved"] + cl_exec["rejected"],
        )
        self.assertEqual(
            sum(r["count"] for r in cl_exec["rejection_reasons"]),
            cl_exec["rejected"],
        )

    def test_detects_bridge_source_digest_and_matrix_drift(self) -> None:
        with tempfile.TemporaryDirectory(prefix="h1-inv-test-") as tmp:
            root = Path(tmp)
            for rel in h1.TRACKED_BRIDGE_FILES:
                src = ROOT_DIR / rel
                dst = root / rel
                dst.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(src, dst)
            art_src = ROOT_DIR / h1.INVENTORY_ARTIFACT_REL
            art_dst = root / h1.INVENTORY_ARTIFACT_REL
            art_dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(art_src, art_dst)

            # Mutating a tracked bridge file invalidates the recorded SHA-256 digest.
            bridge_file = root / "lean/LeanNative/IR/Bridge.lean"
            bridge_file.write_text(
                bridge_file.read_text(encoding="utf-8") + "\n-- drift probe\n",
                encoding="utf-8",
            )
            rep = h1.check_inventory(root)
            self.assertFalse(rep["ok"])
            self.assertTrue(
                any("digest mismatch" in e for e in rep["errors"]),
                rep["errors"],
            )

    def test_detects_corrupted_rejection_sum(self) -> None:
        with tempfile.TemporaryDirectory(prefix="h1-inv-sum-") as tmp:
            root = Path(tmp)
            for rel in h1.TRACKED_BRIDGE_FILES:
                src = ROOT_DIR / rel
                dst = root / rel
                dst.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(src, dst)
            art_dst = root / h1.INVENTORY_ARTIFACT_REL
            art_dst.parent.mkdir(parents=True, exist_ok=True)
            payload = json.loads(
                (ROOT_DIR / h1.INVENTORY_ARTIFACT_REL).read_text(encoding="utf-8")
            )
            payload["corpora"]["con_leche"]["rejected"] += 5
            art_dst.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

            rep = h1.check_inventory(root)
            self.assertFalse(rep["ok"])
            self.assertTrue(
                any("con_leche" in e for e in rep["errors"]),
                rep["errors"],
            )


if __name__ == "__main__":
    unittest.main()
