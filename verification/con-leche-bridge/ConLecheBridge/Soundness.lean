import ConLeche.MainTheorem
import ConLeche.Driver.Cli
import ConLeche.Verify.Driver.Main
import ConLeche.Verify.Driver.Oleans
import ConLeche.Verify.Frontend.Olean.Files

namespace ConLecheBridge

open ConLeche
open ConLeche.Frontend

universe w

theorem checkDecls_verified_model_exists (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (ds : Array Declaration) (env : Env)
    (hacc : Cached.checkDecls .verified pins ds = .ok env) :
    Nonempty (Model V env) :=
  ConLeche.model_exists V pins ds env hacc

theorem ndjson_false_declaration_rejected (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (chunks : List ByteArray)
    (hfalse : jsonWithTheoremFalse chunks) :
    ∃ e, (do
      let pre ← builtinPreludeE
      let r ← parseChunks chunks
      let ds := preparePrelude pre r.decls
      Cached.checkDecls .verified pins ds) = .error e :=
  ConLeche.no_False_declaration V pins chunks hfalse

theorem driver_ndjson_false_never_exits_zero (V : Type w) [SetTheory V]
    {file : String} {fs : FS} {b : ByteArray}
    (hb : fs.file file = some b) (hfalse : jsonWithTheoremFalse [b]) :
    ¬ ModelIO.CanGive (Driver.runArgs ["--", file]) fs 0 :=
  ConLeche.main_no_False V hb hfalse

theorem driver_oleans_false_never_exits_zero (V : Type w) [SetTheory V]
    {dirs root : String} {r m : Name} {fs : FS}
    {d : Olean.ModDecoded} {c : Olean.CEntryF Name Expr} {v : Expr} {all : List Name}
    (hr : Olean.parseModName root = some r)
    (hcl : Olean.InClosure (Driver.searchPathOf dirs) fs #[r] m)
    (hv : Olean.ViewOf (Driver.searchPathOf dirs) fs m d)
    (hmem : c ∈ d.constants) (hk : c.kind = .thm v all)
    (hty : c.type = .const falseName []) :
    ¬ ModelIO.CanGive (Driver.runArgs ["--olean", "--search-path=" ++ dirs, "--", root]) fs 0 :=
  ConLeche.main_oleans_no_False V hr hcl hv hmem hk hty

theorem driver_ndjson_exit_zero_model_exists (V : Type w) [SetTheory V]
    {file : String} {fs : FS} {hs hs' : HS}
    (h : (Driver.runArgs ["--", file] : ModelIO _) fs hs (.ok 0) hs') :
    ∃ pre b r env,
      builtinPreludeE = .ok pre ∧
      fs.file file = some b ∧
      parseChunks [b] = .ok r ∧
      Cached.checkDecls .verified natOpPinSets (preparePrelude pre r.decls) = .ok env ∧
      Nonempty (Model V env) := by
  obtain ⟨pre, b, r, env, hpre, hfs, hparse, hchk⟩ := Driver.runArgs_accept h
  exact ⟨pre, b, r, env, hpre, hfs, hparse, hchk, ConLeche.model_exists V natOpPinSets _ env hchk⟩

theorem driver_olean_exit_zero_model_exists (V : Type w) [SetTheory V]
    {dirs root : String} {fs : FS} {hs hs' : HS}
    (h : (Driver.runArgs ["--olean", "--search-path=" ++ dirs, "--", root] : ModelIO _) fs hs (.ok 0) hs') :
    ∃ pre rd env,
      builtinPreludeE = .ok pre ∧
      ModelIO.CanGive
        (Olean.readOleans (Driver.searchPathOf dirs) (#[root].filterMap Olean.parseModName) none)
        fs (.ok rd) ∧
      Cached.checkDecls .verified natOpPinSets
        ((prepareD pre rd.decls (Driver.usedOf (some (Driver.searchPathOf dirs, rd)))).decls.map
          (Cached.fillDecl (Driver.fillOf (Driver.searchPathOf dirs) fs rd.values))) = .ok env ∧
      Nonempty (Model V env) := by
  obtain ⟨pre, rd, env, hpre, hrd, hchk⟩ := Driver.runArgs_olean_accept h
  exact ⟨pre, rd, env, hpre, hrd, hchk, ConLeche.model_exists V natOpPinSets _ env hchk⟩

theorem checkError_exitCode_in_arena_band (e : CheckError) :
    e.exitCode = 1 ∨ e.exitCode = 2 ∨ e.exitCode = 3 := by
  cases e <;> simp [CheckError.exitCode]

theorem checkError_exitCode_never_accept (e : CheckError) :
    e.exitCode ≠ 0 :=
  CheckError.exitCode_ne_zero e

theorem parseArgs_verified_olean_invariants (dirs root : String) :
    let a := Driver.parseArgs ["--verified", "--olean", "--search-path=" ++ dirs, "--", root] {}
    a.mode = .verified ∧ a.olean = true ∧ a.bad = none ∧
      a.searchPath = Driver.searchPathOf dirs ∧ a.files = #[root] := by
  have h0 :
      Driver.parseArgs ["--verified", "--olean", "--search-path=" ++ dirs, "--", root] {} =
        Driver.parseArgs ["--olean", "--search-path=" ++ dirs, "--", root] {} := by
    rw [Driver.parseArgs.eq_def]
    rfl
  rw [h0, Driver.parseArgs_olean dirs root]
  simp

end ConLecheBridge
