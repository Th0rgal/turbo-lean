/-! `--help` text shared by the `lean-native` and `lean-native-core` drivers, with the `H1.F`
(`roadmap/HORIZONS.md`) unverified-tier label pins. -/

namespace LeanNative.Driver.CoreCLI

/-- `H1.F` (`roadmap/HORIZONS.md`): the marker labelling every backend command whose emitted code
no machine-checked soundness theorem covers. Backends other than the proved `LCNF → LNIR` → LLVM
path are an unverified tier and get no features until H3 (H1 rules); the `#guard` pins below fail
the build if a label is dropped or leaks onto the verified path. -/
def unverifiedTierLabel : String := "[unverified tier]"

/-- The `--help` lines, pure so the `H1.F` label pins can inspect them. -/
def coreUsageLines (tag : String) (hasFrontend : Bool) : List String :=
  let fe (xs : List String) : List String := if hasFrontend then xs else []
  [s!"{tag} v0.5.0 — Formally Validated Lean 4 Optimizer, TV, FastCheck & Multi-Target Codegen", s!"Usage: {tag} <command> [options]", "Commands:"] ++
    fe ["  build-exe          Compile a .lean source file directly to a native executable (<file.lean> -o <bin>)"] ++ [
    "  compile-llvm       Emit baseline or optimized LLVM 18 IR (--input <file>, --arch <target>, --freestanding, --baseline, -o <path>)",
    "  emit-llvm          Alias of compile-llvm (--target thumbv6m|thumbv8m.main|riscv32imac, --freestanding, -o <path>)",
    s!"  compile-static-lib Emit C-ABI static library (.a) + C header (.h) (--input <file>, -o <lib.a>, --header <lib.h>) {unverifiedTierLabel}",
    "  emit-freestanding-c-lib Emit verified freestanding .ll + C99 .h + .o/.a + .su (--target thumbv6m|thumbv8m.main|riscv32imac, -o <lib.a>)",
    s!"  emit-cabi-bindings Emit C/Rust/Swift/modulemap/fixture bindings (--emit-header|--emit-rust|--emit-swift|--emit-modulemap|--emit-fixtures <path>) {unverifiedTierLabel}",
    s!"  emit-c-abi         Alias of emit-cabi-bindings (--target <arch>, --freestanding, --emit-header <lib.h>) {unverifiedTierLabel}"] ++
    (if hasFrontend then [] else [
    "                     A .lean input needs the full 'lean-native' frontend (Stage 1D RC-ADT gate); here it is a hard error unless",
    "                     --signatures-only: bindings from exported source signatures only, no helper/RC-ADT runtime prototypes,",
    "                     fails closed on any non-scalar exported signature, and records 'signatures-only: no Stage1D gate applied'.",
    "                     compile-c-abi / compile-static-lib reject .lean inputs here (use lean-native or --lnir)."]) ++ [
    s!"  compile-c-abi      Alias of emit-cabi-bindings (no --signatures-only) {unverifiedTierLabel}",
    s!"  compile-mlir       Emit GPU MLIR module (--input <file>, -o <path>) {unverifiedTierLabel}",
    s!"  compile-ptx        Emit NVIDIA PTX 8.0 assembly (--input <file>, --sm sm_90, --fastcheck, -o <path>) {unverifiedTierLabel}",
    s!"  compile-metal      Emit Apple Metal Shading Language 3.0 (--input <file>, --fastcheck, -o <path>) {unverifiedTierLabel}",
    s!"  compile-fastcheck  Run Constraint-Propagating FastCheck or emit SIMD/PTX/Metal kernels (--samples N, --json, -o <path>) {unverifiedTierLabel}",
    s!"  compile-hybrid     Partition module into CPU/GPU and emit hybrid host dispatch glue (--input <file>, -o <path>) {unverifiedTierLabel}",
    "  superopt           Run cost-guided enumerative superoptimizer (--target x86_64|arm64|cuda_ptx|apple_metal, --profile profiles/<name>.json, --json)",
    "  calibrate-cost     Calibrate hardware cost profile (--target x86_64|arm64|zen5|neoverse|scaleway|..., e.g. --target arm64 on an aarch64 host; --samples-json <path>, --json)",
    "  plugins            Run segregated optimization plugins under Law 1 TV/Cost Gate (--target <arch>, --test-adversarial, --json)",
    "  pr-verify          Run Law 5 PR & Spec-Pinning Gate (--base <ref>, --disallow-spec-changes, --json)",
    "  turbo-plugin       Run JSONL-stdio external accelerator plugin for turbo-lean",
    "  verify-certs       Run optimization pipeline and verify translation certificates (--input <file>, --json, -o <path>)",
    "  validate-tv        Run Alive2-style symbolic translation validation (--input <file>, --json, -o <path>)",
    "  audit-axioms       Run in-kernel transitive axiom audit (Lean.collectAxioms snapshot, --json)",
    "  emit-lnir          Emit LNIR module in wire/JSON format (--wire, --json, --fastcheck, -o <path>)",
    "  eval-lnir          Evaluate LNIR declaration or module (--decl <name>, --args <csv>, --batch-json, --opt)",
    "  self-test          Run end-to-end Core, Spec (Laws 1-5), Plugins, Codec, FastCheck, Superopt, SymbolicTV, LLVM/PTX/Metal self-tests",
    "  worker             Run persistent sub-millisecond JSON-RPC worker loop over stdin/stdout",
    "Backend tiers (roadmap/HORIZONS.md H1): the LLVM path (compile-llvm / emit-llvm / emit-freestanding-c-lib",
    "  / build-exe via the full frontend) lowers LCNF → LNIR under the frozen H1 theorem",
    "  (lean/LeanNative/SpecLocked.lean); the LNIR → LLVM printer, LLVM and the Lean runtime are trusted, not",
    "  proved (docs/TRUSTED_BASE.md).",
    s!"{unverifiedTierLabel}: no machine-checked soundness theorem covers this backend's emitted code; the",
    "  backend is frozen until H3 — no new features (roadmap/HORIZONS.md H1 rules)." ]

def printCoreUsage (tag : String) (hasFrontend : Bool) : IO Unit :=
  IO.println (String.intercalate "\n" (coreUsageLines tag hasFrontend))

/-- `H1.F` pin predicate: the usage line of command `cmd` carries `unverifiedTierLabel`. -/
def usageLineHasUnverifiedLabel (lines : List String) (cmd : String) : Bool :=
  lines.any fun l => l.startsWith ("  " ++ cmd ++ " ") && (l.splitOn unverifiedTierLabel).length > 1

-- `H1.F` (`roadmap/HORIZONS.md`): unverified backends are labelled in `--help`; the proved-path
-- LLVM commands are not. Elaborate-time pins: dropping a label, or leaking one onto the verified
-- path, fails the build.
#guard usageLineHasUnverifiedLabel (coreUsageLines "lean-native" true) "compile-static-lib"
#guard usageLineHasUnverifiedLabel (coreUsageLines "lean-native" true) "emit-cabi-bindings"
#guard usageLineHasUnverifiedLabel (coreUsageLines "lean-native" true) "emit-c-abi"
#guard usageLineHasUnverifiedLabel (coreUsageLines "lean-native" true) "compile-c-abi"
#guard usageLineHasUnverifiedLabel (coreUsageLines "lean-native" true) "compile-mlir"
#guard usageLineHasUnverifiedLabel (coreUsageLines "lean-native" true) "compile-ptx"
#guard usageLineHasUnverifiedLabel (coreUsageLines "lean-native" true) "compile-metal"
#guard usageLineHasUnverifiedLabel (coreUsageLines "lean-native" true) "compile-fastcheck"
#guard usageLineHasUnverifiedLabel (coreUsageLines "lean-native" true) "compile-hybrid"
#guard usageLineHasUnverifiedLabel (coreUsageLines "lean-native-core" false) "compile-ptx"
#guard !usageLineHasUnverifiedLabel (coreUsageLines "lean-native" true) "compile-llvm"
#guard !usageLineHasUnverifiedLabel (coreUsageLines "lean-native" true) "emit-llvm"
#guard !usageLineHasUnverifiedLabel (coreUsageLines "lean-native" true) "build-exe"
#guard !usageLineHasUnverifiedLabel (coreUsageLines "lean-native" true) "emit-freestanding-c-lib"
#guard (coreUsageLines "lean-native" true).any (·.startsWith "Backend tiers")
#guard (coreUsageLines "lean-native-core" false).any (·.startsWith "Backend tiers")

end LeanNative.Driver.CoreCLI
