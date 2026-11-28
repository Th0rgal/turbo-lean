# Batteries nightly C2 dependency

This Lake package pins the external `leanprover-community/batteries` corpus to
`v4.35.0` (`66e469188fe07963e5cf666c7d4433f45b8131c5`) for the nightly C2
workflow. Its `lean-toolchain` matches the C2 fixtures consumed by
`scripts/run_conformance_suite.py`.

Run `lake build Batteries` in this directory to build the pinned corpus.
The nightly workflow then runs the repository's C2 three-way conformance gate
with `TURBO_C2_PACKAGES_DIR=auto`; that runner intentionally continues to
own its fixed, exportable C2 fixture set.
