import LeanNative.Semantics.Eval
import LeanNative.Backend.LLVM
import LeanNative.Driver.CoreCLI
import LeanNative.Driver.BuildExe

/-!
# H3.1 Step 2: opt-in RC-ADT LLVM leaf (`--allow-rc-adt-llvm`)

(a) Default mode still refuses every RC-ADT module (`findUnsupportedLLVMCall?`,
`buildExeLLVMGate?`, `compile-llvm`). (b) The opt-in admits non-recursive `allocCtor` /
`ctorGetObj` / `ctorGetScalar` / `incRef` / `decRef` decls; the emitted LLVM IR, compiled by
`clang` and run natively, returns the `evalCode` result on every fixture. `ctorGetScalar` reads
`numObjs` from the header byte `m_other`.
-/

namespace LeanNative.Tests.H3RcAdtLlvm

open LeanNative.IR LeanNative.Semantics LeanNative.Backend.LLVM LeanNative.Driver.CoreCLI

/-! ## Fixtures (scalar `i64` signatures; heap objects stay function-local) -/

def addV (dst a b : VarId) (k : LNIRCode) : LNIRCode :=
  .letBind dst .i64 (.scalar (.binOp .add (.var a) (.var b))) k

def p2 : List LNIRParam :=
  [{ id := 0, name := "x", ty := .i64 }, { id := 1, name := "y", ty := .i64 }]

/-- Scalar-only ctor: `ctorGetScalar o 1` is slot `8 + 8·0 + 8`. -/
def ctorScalar : LNIRDecl where
  name := "h3_ctor_scalar"
  params := p2
  retTy := .i64
  body := .letBind 2 .objPtr (.allocCtor 3 [] [0, 1])
    (.letBind 3 .i64 (.ctorGetScalar 2 1 .i64) (.decRef 2 1 (.ret 3)))

/-- Mixed ctor (1 object field): scalars start after the object word, so slot `i` is `16 + 8·i`. -/
def ctorMixed : LNIRDecl where
  name := "h3_ctor_mixed"
  params := p2
  retTy := .i64
  body := .letBind 2 .objPtr (.allocCtor 0 [] [0])
    (.letBind 3 .objPtr (.allocCtor 1 [2] [1, 0])
    (.letBind 4 .objPtr (.ctorGetObj 3 0)
    (.letBind 5 .i64 (.ctorGetScalar 4 0 .i64)
    (.letBind 6 .i64 (.ctorGetScalar 3 0 .i64)
    (.letBind 7 .i64 (.ctorGetScalar 3 1 .i64)
    (addV 8 5 6 (addV 9 8 7 (addV 10 9 6 (.decRef 3 1 (.ret 10))))))))))

/-- `incRef` / `decRef` round trip on a live object, then a read and the final release. -/
def ctorIncDec : LNIRDecl where
  name := "h3_ctor_incdec"
  params := p2
  retTy := .i64
  body := .letBind 2 .objPtr (.allocCtor 2 [] [0, 1])
    (.incRef 2 2 (.decRef 2 1 (.letBind 3 .i64 (.ctorGetScalar 2 0 .i64)
    (.decRef 2 1 (.letBind 4 .i64 (.ctorGetScalar 2 1 .i64)
    (addV 5 3 4 (.decRef 2 1 (.ret 5))))))))

/-- Two object fields + three scalars: `ctorGetScalar o 2` is at `8 + 16 + 16`. -/
def ctorWide : LNIRDecl where
  name := "h3_ctor_wide"
  params := p2
  retTy := .i64
  body := .letBind 2 .objPtr (.allocCtor 0 [] [1])
    (.letBind 3 .objPtr (.allocCtor 0 [] [0])
    (.letBind 4 .objPtr (.allocCtor 7 [2, 3] [0, 1, 0])
    (.letBind 5 .i64 (.ctorGetScalar 4 2 .i64)
    (.letBind 6 .objPtr (.ctorGetObj 4 1)
    (.letBind 7 .i64 (.ctorGetScalar 6 0 .i64)
    (.letBind 8 .objPtr (.ctorGetObj 4 0)
    (.letBind 9 .i64 (.ctorGetScalar 8 0 .i64)
    (.letBind 10 .i64 (.ctorGetScalar 4 1 .i64)
    (addV 11 5 7 (addV 12 11 9 (addV 13 12 10 (.decRef 4 1 (.ret 13)))))))))))))

def fixtures : List LNIRDecl := [ctorScalar, ctorMixed, ctorIncDec, ctorWide]

def modOf (d : LNIRDecl) : LNIRModule := { moduleName := d.name, decls := [d] }

def fixtureModule : LNIRModule := { moduleName := "h3_rc_adt_llvm", decls := fixtures }

def inputs : List (UInt64 × UInt64) := [(0, 0), (7, 11), (42, 1000), (0xFFFFFFFFFFFFFFF0, 0x7F)]

/-- `evalCode` reference result (`none` on any UB error). -/
def evalU64? (d : LNIRDecl) (x y : UInt64) : Option UInt64 :=
  match evalDeclWith 4096 (fun _ => none) d [.u64 x, .u64 y] HeapState.empty with
  | .ok (.u64 r, _) => some r
  | _ => none

-- Every fixture is well defined under `evalCode` and returns the intended field arithmetic.
#guard inputs.all fun (x, y) =>
  evalU64? ctorScalar x y == some y && evalU64? ctorMixed x y == some (x + y + x + y) &&
  evalU64? ctorIncDec x y == some (x + y) && evalU64? ctorWide x y == some (x + x + y + y)

/-! ## (a) Default mode: RC-ADT is refused at every LLVM gate -/

#guard fixtures.all fun d => (findUnsupportedLLVMCall? (modOf d)).isSome
#guard fixtures.all fun d => (findUnsupportedLLVMCallWith? false (modOf d)).isSome
#guard fixtures.all fun d => (buildExeLLVMGate? (modOf d) (modOf d)).isSome
#guard fixtures.all fun d => fixtureModule.findRcAdtDecl?.isSome && d.containsRcAdt

/-! ## (b) Opt-in mode: the leaf is admitted, everything outside it still fails closed -/

#guard findUnsupportedLLVMCallWith? true fixtureModule == none
#guard (buildExeLLVMGate? fixtureModule fixtureModule .x86_64 true).isNone
#guard findUnsupportedLLVMCallWith? true fixtureModule .arm64 == none

def optInRejects (d : LNIRDecl) (target : TargetArch := .x86_64) : Option String :=
  (findUnsupportedLLVMCallWith? true (modOf d) target).map (·.2)

def heapParam : LNIRDecl :=
  { name := "h3_heap_param", params := [{ id := 0, name := "p", ty := .objPtr }], retTy := .i64,
    body := .letBind 1 .i64 (.ctorGetScalar 0 0 .i64) (.ret 1) }

def heapRet : LNIRDecl :=
  { name := "h3_heap_ret", params := p2, retTy := .objPtr,
    body := .letBind 2 .objPtr (.allocCtor 0 [] [0]) (.ret 2) }

def withIsx : LNIRDecl :=
  { ctorScalar with
    name := "h3_isx"
    body := .letBind 2 .objPtr (.allocCtor 0 [] [0]) (.letBind 3 .i1 (.isExclusive 2) (.ret 0)) }

def withCtorSet : LNIRDecl :=
  { ctorScalar with
    name := "h3_ctor_set"
    body := .letBind 2 .objPtr (.allocCtor 0 [] [0])
      (.letBind 3 .unit (.call "lean_native_ctor_set_scalar" [2, 0, 1] .unit) (.ret 0)) }

def wideScalarGet : LNIRDecl :=
  { ctorScalar with
    name := "h3_u256_get"
    body := .letBind 2 .objPtr (.allocCtor 0 [] [0])
      (.letBind 3 .u256 (.ctorGetScalar 2 0 .u256) (.ret 0)) }

def bigTag : LNIRDecl :=
  { ctorScalar with
    name := "h3_big_tag"
    body := .letBind 2 .objPtr (.allocCtor 245 [] [0]) (.decRef 2 1 (.ret 0)) }

#guard optInRejects heapParam == some "rc_adt_signature"
#guard optInRejects heapRet == some "rc_adt_signature"
#guard optInRejects withIsx == some "isExclusive"
#guard optInRejects withCtorSet == some "lean_native_ctor_set_scalar"
#guard optInRejects wideScalarGet == some "ctorGetScalar"
#guard optInRejects bigTag == some "allocCtor"
#guard optInRejects ctorScalar .wasm32 == some "rc_adt_target"
#guard optInRejects ctorScalar .nvptx64 == some "rc_adt_target"

/-- One-binder RC-ADT probe: `let 3 : ty := e` after a live heap object `2`, then `ret 0`. -/
def probe (nm : String) (ty : LNIRType) (e : LNIRExpr) : LNIRDecl :=
  { ctorScalar with
    name := nm
    body := .letBind 2 .objPtr (.allocCtor 0 [] [0]) (.letBind 3 ty e (.decRef 2 1 (.ret 0))) }

#guard optInRejects (probe "h3_box" .objPtr (.boxScalar 0 .i64)) == some "boxScalar"
#guard optInRejects (probe "h3_unbox" .i64 (.unboxScalar 2 .i64)) == some "unboxScalar"
-- `allocCtor` must bind a `ptr` slot: a tuple / scalar binder would silently drop the object.
#guard optInRejects (probe "h3_tup" (.tuple [.objPtr, .i64]) (.allocCtor 1 [] [0])) ==
  some "allocCtor"
#guard optInRejects (probe "h3_i64" .i64 (.allocCtor 1 [] [0])) == some "allocCtor"
-- The heap-box helpers and `ensure_exclusive` on a ctor object stay outside the leaf.
#guard optInRejects (probe "h3_bx" .objPtr (.call "lean_native_box_u64" [0] .objPtr false)) ==
  some "lean_native_box_u64"
#guard optInRejects (probe "h3_ux" .i64 (.call "lean_native_unbox_u64" [2] .i64 false)) ==
  some "lean_native_unbox_u64"
#guard optInRejects
    (probe "h3_ex" .objPtr (.call "lean_native_ensure_exclusive" [2] .objPtr false)) ==
  some "lean_native_ensure_exclusive"
-- A scalar module takes the unchanged default gate under the opt-in.
#guard findUnsupportedLLVMCallWith? true (modOf scalarIdDecl) == none
#guard (checkFreestandingModule fixtureModule).isSome

/-! ## IR shape: `ctorGetScalar` reads `m_other`, never traps on the heap path -/

def hasSub (s pat : String) : Bool := (s.splitOn pat).length > 1

def scalarIR : String := emitLLVMOptimized (modOf ctorMixed)

#guard hasSub scalarIR "= getelementptr inbounds i8, ptr %ldp_" && hasSub scalarIR ", i64 6\n"
#guard hasSub scalarIR "load i8, ptr" && hasSub scalarIR "shl i64" && hasSub scalarIR "sproj_imm"
#guard hasSub (emitLLVMBaseline (modOf ctorWide)) "sproj_cont"

/-! ## Native execution: clang-compiled IR matches `evalCode` -/

def cHarness : String :=
  let protos := fixtures.map fun d => s!"uint64_t {d.name}(uint64_t, uint64_t);"
  let calls := fixtures.map fun d =>
    s!"  for (int i = 0; i < n; i++) printf(\"%llu\\n\", " ++
      s!"(unsigned long long){d.name}(xs[i], ys[i]));"
  let xs := ", ".intercalate (inputs.map fun (x, _) => s!"{x}ULL")
  let ys := ", ".intercalate (inputs.map fun (_, y) => s!"{y}ULL")
  let main := ["int main(void) {", s!"  const uint64_t xs[] = \{{xs}};",
    s!"  const uint64_t ys[] = \{{ys}};", s!"  const int n = {inputs.length};"]
  let lines := ["#include <stdint.h>", "#include <stdio.h>"] ++ protos ++ main ++ calls
  "\n".intercalate (lines ++ ["  return 0;", "}"]) ++ "\n"

def expectedLines : List String :=
  fixtures.flatMap fun d => inputs.map fun (x, y) => toString ((evalU64? d x y).getD 0)

def tool? (names : List String) : IO (Option String) := do
  for n in names do
    try
      let out ← IO.Process.output { cmd := n, args := #["--version"] }
      if out.exitCode == 0 then return some n
    catch _ => pure ()
  return none

def run (cmd : String) (args : Array String) : IO Unit := do
  let out ← IO.Process.output { cmd, args }
  if out.exitCode != 0 then throw <| IO.userError s!"{cmd} failed:\n{out.stderr}"

/-- Compile `ir` (+ the C harness) with clang, run it, and compare with `evalCode` line by line. -/
def nativeMatches (dir : System.FilePath) (tag ir clang : String) (opt? : Option String) :
    IO Unit := do
  let ll := (dir / s!"{tag}.ll").toString
  let exe := (dir / s!"{tag}.exe").toString
  IO.FS.writeFile ll ir
  if let some opt := opt? then run opt #["-passes=verify", "-disable-output", ll]
  run clang #["-O2", "-Wno-override-module", ll, (dir / "harness.c").toString, "-o", exe]
  let out ← IO.Process.output { cmd := exe }
  let got := (out.stdout.splitOn "\n").filter (!·.isEmpty)
  if out.exitCode != 0 || got != expectedLines then
    throw <| IO.userError s!"[H3] {tag}: native {got} ≠ evalCode {expectedLines}"

def nativeSuite : IO Unit := do
  let some clang ← tool? ["clang", "clang-18"]
    | IO.println "[H3] clang unavailable: native execution check skipped"
  let opt? ← tool? ["opt", "opt-18", "/usr/lib/llvm-18/bin/opt"]
  let dir : System.FilePath := s!"/tmp/h3_rc_adt_llvm_{← IO.monoNanosNow}"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / "harness.c") cHarness
  let optMod := (LeanNative.Transform.runDefaultPipeline fixtureModule).1
  if let some (d, c) := findUnsupportedLLVMCallWith? true optMod then
    throw <| IO.userError s!"[H3] optimized module rejected: {c} in {d}"
  for (tag, ir) in [("baseline", emitLLVMBaseline fixtureModule),
      ("optimized", emitLLVMOptimized fixtureModule), ("pipeline", emitLLVMOptimized optMod)] do
    nativeMatches dir tag ir clang opt?
  IO.FS.removeDirAll dir
  let n := fixtures.length * inputs.length
  IO.println s!"[H3] native == evalCode on {n} (fixture, input) runs × 3 IRs"

#eval nativeSuite

/-! ## CLI: `compile-llvm` refuses by default and emits under `--allow-rc-adt-llvm` -/

def cliSuite : IO Unit := do
  let dir : System.FilePath := s!"/tmp/h3_rc_adt_cli_{← IO.monoNanosNow}"
  IO.FS.createDirAll dir
  let lnir := (dir / "m.lnir").toString
  let out := (dir / "m.ll").toString
  IO.FS.writeFile lnir fixtureModule.toWire
  let refused ← try
      discard <| runCompileLLVM "h3" none ["--lnir", lnir, "-o", out]
      pure false
    catch _ => pure true
  if !refused then throw <| IO.userError "[H3] default compile-llvm accepted an RC-ADT module"
  let rc ← runCompileLLVM "h3" none ["--lnir", lnir, "--allow-rc-adt-llvm", "-o", out]
  let ir ← IO.FS.readFile out
  let refusedStatic ← try
      discard <| loadInputModule none ["--lnir", lnir]
      pure false
    catch _ => pure true
  IO.FS.removeDirAll dir
  if rc != 0 || !hasSub ir "@lean_alloc_ctor" || !hasSub ir "sproj_cont" || !refusedStatic then
    throw <| IO.userError "[H3] --allow-rc-adt-llvm compile-llvm did not emit the RC-ADT leaf"

#guard rcAdtLLVMOptIn ["compile-llvm", "--allow-rc-adt-llvm"] && !rcAdtLLVMOptIn ["--allow-rc-adt"]

-- The opt-in is refused outside LLVM emission, including the `superopt-evolve` early return.
#guard ["compile", "compile-llvm", "emit-llvm", "build-exe"].all fun c =>
  (rcAdtLLVMMisuse? [c, "--allow-rc-adt-llvm"]).isNone
#guard ["superopt-evolve", "superopt", "eval-lnir", "compile-ptx", "emit-lnir"].all fun c =>
  (rcAdtLLVMMisuse? [c, "--allow-rc-adt-llvm"]).isSome
#guard ["--c-abi", "--emit-ptx", "--metal"].all fun f =>
  (rcAdtLLVMMisuse? ["compile", f, "--allow-rc-adt-llvm"]).isSome

def dispatchRefuses (args : List String) : IO Bool := do
  try
    discard <| dispatchSharedCommand "h3" none args
    pure false
  catch e => pure ((toString e).startsWith "[lean-native] --allow-rc-adt-llvm")

/-- info: true -/
#guard_msgs in
#eval do
  let a ← dispatchRefuses ["superopt-evolve", "--allow-rc-adt-llvm", "--lnir", "/nonexistent"]
  let b ← dispatchRefuses ["compile", "--c-abi", "--allow-rc-adt-llvm", "--lnir", "/nonexistent"]
  IO.println (a && b)

#guard buildExeLLVMGate? fixtureModule fixtureModule == some
  "[lean-native] build-exe: RC-ADT declaration 'h3_ctor_scalar' is unsupported by the LLVM backend"

#eval cliSuite

end LeanNative.Tests.H3RcAdtLlvm
