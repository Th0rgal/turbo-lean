import ConLeche.MainTheorem
import ConLeche.Driver.Cli
import ConLeche.Verify.Driver.Main
import ConLeche.Verify.Driver.Oleans
import ConLeche.Verify.Frontend.Olean.Files
import ConLeche.Verify.Frontend.Prepare
import ConLeche.Verify.Cached.StreamThm
import ConLeche.Verify.Cached.MainC

namespace ConLecheBridge

open ConLeche
open ConLeche.Frontend
open SetTheory

universe w

/-! ## Core Declaration Fold & Stream Soundness -/

theorem checkDecls_verified_model_exists (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (ds : Array Declaration) (env : Env)
    (hacc : Cached.checkDecls .verified pins ds = .ok env) :
    Nonempty (Model V env) :=
  ConLeche.model_exists V pins ds env hacc

theorem checkDecls_empty_stream_accepts_with_model (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) :
    Cached.checkDecls .verified pins #[] = .ok Env.empty ∧
      Nonempty (Model V Env.empty) := by
  have hacc : Cached.checkDecls .verified pins #[] = .ok Env.empty := rfl
  exact ⟨hacc, ConLeche.model_exists V pins #[] Env.empty hacc⟩

theorem checkDecls_jobs_accepts_streamEnv_with_model (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (ds : Array Declaration)
    (hjobs : ∀ k (hk : k < ds.size),
      Cached.recordJob .verified pins (Cached.buildIndex ds) k ds[k] = .ok ()) :
    Cached.checkDecls .verified pins ds = .ok (Cached.streamEnv ds.toList) ∧
      Nonempty (Model V (Cached.streamEnv ds.toList)) := by
  have hacc := Cached.checkDecls_of_jobs (mode := .verified) (pins := pins) hjobs
  exact ⟨hacc, ConLeche.model_exists V pins ds _ hacc⟩

theorem checkDecls_verified_no_Empty_constant (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (ds : Array Declaration) (env : Env)
    (hacc : Cached.checkDecls .verified pins ds = .ok env) :
    ∀ c ∈ env.consts, c.toConstantVal.type = .const emptyName [] → False :=
  Cached.no_proof_of_Empty_cached V hacc

theorem checkDecls_verified_no_False_constant (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (ds : Array Declaration) (env : Env)
    (hacc : Cached.checkDecls .verified pins ds = .ok env) :
    ∀ c ∈ env.consts, c.toConstantVal.type = .const falseName [] → False :=
  Cached.no_proof_of_False_cached V hacc

theorem checkDecls_verified_no_Empty_theorem_accepted (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (ds : Array Declaration) (cv : ConstantVal) (v : Expr)
    (hmem : Declaration.thmDecl cv v ∈ ds) (hty : cv.type = .const emptyName []) :
    ∀ env, Cached.checkDecls .verified pins ds ≠ .ok env := by
  intro env hacc
  obtain ⟨c, hc, hcty⟩ := Cached.checkDecls_thmDecl_const hty hmem hacc
  exact Cached.no_proof_of_Empty_cached V hacc c hc hcty

/-! ## Set-Model & Denotation Soundness -/

theorem checkDecls_thmDecl_const_inhabited_in_model (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (ds : Array Declaration) (env : Env)
    (cv : ConstantVal) (value : Expr) (n : Name) (ls : List Level)
    (hty : cv.type = .const n ls)
    (hmem : Declaration.thmDecl cv value ∈ ds)
    (hacc : Cached.checkDecls .verified pins ds = .ok env)
    (M : Model V env) (φ : LevelParam → Nat) (ρ : BVarIdx → V) :
    ∃ c ∈ env.consts, ∃ T : V,
      c.toConstantVal.type = .const n ls ∧
      Denotes M.cval env φ ρ (.const n ls) T ∧
      M.cval c.name φ ∈ˢ T := by
  obtain ⟨c, hc, hcty⟩ := Cached.checkDecls_thmDecl_const hty hmem hacc
  obtain ⟨T, hden, hmemT⟩ := M.mem c hc φ ρ
  rw [hcty] at hden
  exact ⟨c, hc, T, hcty, hden, hmemT⟩

theorem model_stored_eq_theorem_denotes_equal (V : Type w) [SetTheory V]
    {env : Env} (M : Model V env) {c : ConstantInfo} (hc : c ∈ env.consts)
    {u : Level} {ty lhs rhs : Expr}
    (hty : c.toConstantVal.type = .app (.app (.app (.const eqName [u]) ty) lhs) rhs)
    {φ : LevelParam → Nat} {ρ : BVarIdx → V} {A a b : V}
    (hA : Denotes M.cval env φ ρ ty A) (hAu : A ∈ˢ SetTheory.univ (Level.eval φ u))
    (ha : Denotes M.cval env φ ρ lhs a) (haA : a ∈ˢ A)
    (hb : Denotes M.cval env φ ρ rhs b) (hbA : b ∈ˢ A) :
    a = b := by
  obtain ⟨T, hT, hcT⟩ := M.mem c hc φ ρ
  rw [hty] at hT
  cases hT with
  | app hf1 hrhs =>
    cases hf1 with
    | app hf2 hlhs =>
      cases hf2 with
      | app heq hty' =>
        obtain rfl := Denotes_functional hA hty'
        obtain rfl := Denotes_functional ha hlhs
        obtain rfl := Denotes_functional hb hrhs
        rw [M.eq_equality u φ ρ _ A a b heq hAu haA hbA] at hcT
        exact SetTheory.eq_of_mem_eqv hcT

/-! ## Prelude Preparation & Ground Hoisting Soundness -/

theorem prepareD_preserves_and_extends_with_prelude (pre : PreludeIx)
    (ds : Array Declaration) (used : Declaration → Array Name) :
    (∀ pd ∈ ds, pd ∈ (prepareD pre ds used).decls) ∧
      ∃ extra : List Declaration,
        (∀ d ∈ extra, d ∈ pre.decls.toList) ∧
        (prepareD pre ds used).decls.toList.Perm (ds.toList ++ extra) :=
  ⟨fun _ h => mem_prepareD h, prepareD_perm pre ds used⟩

theorem ndjson_false_declaration_rejected (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (chunks : List ByteArray)
    (hfalse : jsonWithTheoremFalse chunks) :
    ∃ e, (do
      let pre ← builtinPreludeE
      let r ← parseChunks chunks
      let ds := preparePrelude pre r.decls
      Cached.checkDecls .verified pins ds) = .error e :=
  ConLeche.no_False_declaration V pins chunks hfalse

/-! ## Arena Exit-Code & Verdict Contract -/

theorem checkError_exitCode_in_arena_band (e : CheckError) :
    e.exitCode = 1 ∨ e.exitCode = 2 ∨ e.exitCode = 3 := by
  cases e <;> simp [CheckError.exitCode]

theorem checkError_exitCode_never_accept (e : CheckError) :
    e.exitCode ≠ 0 :=
  CheckError.exitCode_ne_zero e

theorem checkError_exitCode_classification (msg : String) :
    (CheckError.invalid msg).exitCode = 1 ∧
      (CheckError.notImplemented msg).exitCode = 2 ∧
      (CheckError.internal msg).exitCode = 3 :=
  ⟨rfl, rfl, rfl⟩

theorem verdictG_exit_zero_iff_ok {modeTag : String} {size t0 : Nat}
    {decls : Array Declaration} {r : Except (CheckError × Nat) Unit}
    {fs : FS} {hs hs' : HS}
    (h : (Driver.verdictG modeTag size t0 decls r : ModelIO _) fs hs (.ok 0) hs') :
    r = .ok () :=
  Driver.verdictG_ok h rfl

/-! ## `.olean` Sparse Decoder, Deferred Theorem-Value Filling & Closure Read -/

theorem sparse_decoder_matches_region_spec (r : Olean.Region)
    (b : Olean.Frontier) (hB : b.Good r) (c : Nat) (v : UInt64)
    (sk : Olean.CEntryF UInt64 UInt64) :
    Olean.frontierExpr r b c = Olean.exprAt r c ∧
      Olean.sparseNameP r v = Olean.nameP r v ∧
      Olean.sparseExprP r v = Olean.exprP r v ∧
      Olean.sparseEntry r sk = sk.mapM (Olean.nameP r) (Olean.exprP r) :=
  ⟨Olean.frontierExpr_eq hB c, Olean.sparseNameP_eq r v,
    Olean.sparseExprP_eq r v, Olean.sparseEntry_eq r sk⟩

theorem fillDecl_preserves_index_and_installs_unique_value
    {sp : Olean.SearchPath} {fs : FS} {values : Array Olean.ModRef}
    {code : Nat} {e₁ e₂ : Expr} (cv : ConstantVal) (ds : Array Declaration)
    (hv₁ : Olean.ValueAt sp fs values code e₁)
    (hv₂ : Olean.ValueAt sp fs values code e₂) :
    e₁ = e₂ ∧
      Cached.fillDecl (Driver.fillOf sp fs values) (.thmDecl cv (.bvar code)) = .thmDecl cv e₁ ∧
      Cached.buildIndex (ds.map (Cached.fillDecl (Driver.fillOf sp fs values))) =
        Cached.buildIndex ds :=
  ⟨hv₁.unique hv₂,
    congrArg (Declaration.thmDecl cv) (Driver.fillOf_value hv₁),
    Cached.buildIndex_fill (Driver.fillOf sp fs values) ds⟩

theorem readOleans_closure_merge_and_filled_spec
    {sp : Olean.SearchPath} {roots : Array Name} {constants : Option (Array Name)}
    {jobs : Nat} {fs : FS} {hs hs' : HS} {rd : Olean.OleanRead}
    {cv : ConstantVal} {code : Nat} {e : Expr}
    (hrd : (Olean.readOleans sp roots constants jobs : ModelIO _) fs hs (.ok (.ok rd)) hs')
    (hd : Declaration.thmDecl cv (.bvar code) ∈ rd.decls)
    (hv : Olean.ValueAt sp fs rd.values code e) :
    (∃ order : Array Name,
      Olean.ClosedOrder sp fs order ∧ (∀ r ∈ roots, r ∈ order) ∧
        rd.merged.order.toList.Nodup) ∧
    (∃ md f r a sk loc c all,
      rd.values[Olean.refModule code]? = some md ∧
        ModelIO.CanGive (Olean.readFiles sp md.name .private) fs (.ok f) ∧
        f.viewRegion .private = some (r, a) ∧
        Olean.moduleSkel r a = some sk ∧
        loc ∈ sk.consts ∧
        Olean.constSpec r loc = some c ∧
        c.kind = .thm e all ∧
        cv = ⟨c.name, c.levelParams, c.type⟩) := by
  obtain ⟨order, _, mg, _, _, _, _, hco, hcr, _, hm, _, _, _, _, hmg⟩ := Olean.readOleans_ok hrd
  obtain ⟨-, -, -, hnodup⟩ := Olean.mergeAll_ok hm
  subst hmg
  exact ⟨⟨order, hco, hcr, hnodup⟩, Olean.readOleans_filled hrd hd hv⟩

theorem readOleans_closure_thm_in_prepared_filled_stream
    {sp : Olean.SearchPath} {roots : Array Name} {jobs : Nat} {fs : FS}
    {rd : Olean.OleanRead} {m : Name} {d : Olean.ModDecoded}
    {c : Olean.CEntryF Name Expr} {v : Expr} {all : List Name}
    {pre : PreludeIx} {used : Declaration → Array Name} {F : Expr → Expr}
    {hs hs' : HS}
    (hrd : (Olean.readOleans sp roots none jobs : ModelIO _) fs hs (.ok (.ok rd)) hs')
    (hcl : Olean.InClosure sp fs roots m)
    (hv : Olean.ViewOf sp fs m d)
    (hc : c ∈ d.constants) (hk : c.kind = .thm v all) :
    ∃ v',
      Declaration.thmDecl ⟨c.name, c.levelParams, c.type⟩ v' ∈
        (prepareD pre rd.decls used).decls.map (Cached.fillDecl F) := by
  obtain ⟨v₀, hmem⟩ := Olean.readOleans_thm hrd hcl hv hc hk
  exact ⟨F v₀, Array.mem_map_of_mem (f := Cached.fillDecl F) (mem_prepareD hmem)⟩

theorem checkOleansG_verified_accept_model_exists (V : Type w) [SetTheory V]
    {sp : Olean.SearchPath} {fs : FS} {values : Array Olean.ModRef}
    {pace : Pace} {t0 tIndex tParse jobs : Nat}
    {ds : Array Declaration} {J : Driver.Jobs ds}
    (hgood : ∀ md ∈ values, ∃ f r a,
      ModelIO.CanGive (Olean.readFiles sp md.name .private) fs (.ok f) ∧
        f.viewRegion .private = some (r, a) ∧ md.frontier.Good r)
    {hs hs' : HS}
    (h : (Driver.checkOleansG .verified pace t0 tIndex tParse jobs sp values J : ModelIO _)
      fs hs (.ok (.ok ())) hs') :
    ∃ env,
      Cached.checkDecls .verified natOpPinSets
        (ds.map (Cached.fillDecl (Driver.fillOf sp fs values))) = .ok env ∧
      Nonempty (Model V env) := by
  obtain ⟨env, hchk⟩ := Driver.checkOleansG_accept hgood h
  exact ⟨env, hchk, ConLeche.model_exists V natOpPinSets _ env hchk⟩

/-! ## Generic `checkMainG` Driver Soundness -/

theorem checkMainG_ndjson_verified_exit_zero_model_exists (V : Type w) [SetTheory V]
    {file : String} {pace : Pace} {jobs : Nat} {fs : FS} {hs hs' : HS}
    (h : (Driver.checkMainG (.ndjson file) .verified pace jobs : ModelIO _) fs hs (.ok 0) hs') :
    ∃ pre b r env,
      builtinPreludeE = .ok pre ∧
      fs.file file = some b ∧
      parseChunks [b] = .ok r ∧
      Cached.checkDecls .verified natOpPinSets (preparePrelude pre r.decls) = .ok env ∧
      Nonempty (Model V env) := by
  obtain ⟨pre, b, r, env, hpre, hfs, hparse, hchk⟩ := Driver.checkMainG_ndjson_accept h
  exact ⟨pre, b, r, env, hpre, hfs, hparse, hchk, ConLeche.model_exists V natOpPinSets _ env hchk⟩

theorem checkMainG_oleans_verified_exit_zero_model_exists (V : Type w) [SetTheory V]
    {sp : Olean.SearchPath} {roots : Array Name} {cs : Option (Array Name)}
    {pace : Pace} {jobs : Nat} {fs : FS} {hs hs' : HS}
    (h : (Driver.checkMainG (.oleans sp roots cs) .verified pace jobs : ModelIO _)
      fs hs (.ok 0) hs') :
    ∃ pre rd env,
      builtinPreludeE = .ok pre ∧
      ModelIO.CanGive (Olean.readOleans sp roots cs) fs (.ok rd) ∧
      Cached.checkDecls .verified natOpPinSets
        ((prepareD pre rd.decls (Driver.usedOf (some (sp, rd)))).decls.map
          (Cached.fillDecl (Driver.fillOf sp fs rd.values))) = .ok env ∧
      Nonempty (Model V env) := by
  obtain ⟨pre, rd, env, hpre, hrd, hchk⟩ := Driver.checkMainG_oleans_accept h
  exact ⟨pre, rd, env, hpre, hrd, hchk, ConLeche.model_exists V natOpPinSets _ env hchk⟩

/-! ## `turbo-lean` CLI Invocation Parsing & End-to-End `runArgs` Soundness -/

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

private theorem flagValue_progress_jobs (d : String) :
    Driver.flagValue "--progress=" ("--jobs=" ++ d) = none := by
  simp [Driver.flagValue]

private theorem parseArgs_constants_loop (cs : List String) (rest : List String)
    (a : Driver.Args) :
    Driver.parseArgs (cs.map ("--constant=" ++ ·) ++ rest) a =
      Driver.parseArgs rest { a with constants := a.constants ++ cs.toArray } := by
  induction cs generalizing a with
  | nil =>
    cases a
    simp
  | cons c cs ih =>
    simp only [List.map_cons, List.cons_append]
    rw [Driver.parseArgs_flag _ _
        (Driver.append_ne _ (by decide))
        (Driver.append_ne _ (by decide))
        (Driver.append_ne _ (by decide))
        (Driver.append_ne _ (by decide))
        (Driver.append_ne _ (by decide)),
      Driver.flagValue_other c (by decide) (by decide),
      Driver.flagValue_other c (by decide) (by decide),
      Driver.flagValue_append]
    have hj : (("--constant=" ++ c) == "--jobs") = false := by
      simp only [beq_eq_false_iff_ne]
      exact Driver.append_ne _ (by decide)
    simp only [hj, Bool.false_eq_true, ↓reduceIte]
    rw [ih]
    congr 1
    cases a
    simp only [Driver.Args.mk.injEq, true_and, and_true]
    apply Array.ext'
    simp

private theorem helpWanted_constants_tail (cs roots : List String) :
    ((cs.map ("--constant=" ++ ·) ++ "--" :: roots).takeWhile (· != "--")).contains "--help" =
      false := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    have h1 : (("--constant=" ++ c) != "--") = true := by
      simp only [bne_iff_ne]
      exact Driver.append_ne _ (by decide)
    have h2 : ¬ ("--help" = "--constant=" ++ c) :=
      (Driver.append_ne _ (by decide)).symm
    simp only [List.map_cons, List.cons_append, List.takeWhile_cons, h1, ↓reduceIte,
      List.contains_cons]
    simpa [h2] using ih

theorem parseArgs_turbo_ndjson_invocation (jobsStr file : String) (jobs : Nat)
    (hjobs : Driver.jobsCount jobsStr = .ok jobs) :
    let args := ["--verified", "--jobs=" ++ jobsStr, "--", file]
    Driver.helpWanted args = false ∧
      Driver.parseArgs args {} =
        { mode := .verified, jobs := some jobs, files := #[file] } := by
  refine ⟨?_, ?_⟩
  · have h1 : (("--jobs=" ++ jobsStr) != "--") = true := by
      simp only [bne_iff_ne]
      exact Driver.append_ne _ (by decide)
    have h2 : ¬ ("--help" = "--jobs=" ++ jobsStr) :=
      (Driver.append_ne _ (by decide)).symm
    simp [Driver.helpWanted, List.takeWhile, h1, h2]
  · have hfst :
        Driver.parseArgs ["--verified", "--jobs=" ++ jobsStr, "--", file] {} =
          Driver.parseArgs ["--jobs=" ++ jobsStr, "--", file] { mode := .verified } := by
      rw [Driver.parseArgs.eq_def]
      rfl
    rw [hfst, Driver.parseArgs_flag _ _
        (Driver.append_ne _ (by decide))
        (Driver.append_ne _ (by decide))
        (Driver.append_ne _ (by decide))
        (Driver.append_ne _ (by decide))
        (Driver.append_ne _ (by decide)),
      flagValue_progress_jobs jobsStr,
      Driver.flagValue_append]
    simp only [hjobs]
    simp [Driver.parseArgs]

theorem parseArgs_turbo_olean_invocation (jobsStr dirs : String) (jobs : Nat)
    (constants roots : List String)
    (hjobs : Driver.jobsCount jobsStr = .ok jobs) :
    let args :=
      ["--verified", "--jobs=" ++ jobsStr, "--olean", "--search-path=" ++ dirs] ++
        constants.map ("--constant=" ++ ·) ++ ("--" :: roots)
    Driver.helpWanted args = false ∧
      Driver.parseArgs args {} =
        { mode := .verified
          jobs := some jobs
          olean := true
          searchPath := Driver.searchPathOf dirs
          constants := constants.toArray
          files := roots.toArray } := by
  refine ⟨?_, ?_⟩
  · have hj1 : (("--jobs=" ++ jobsStr) != "--") = true := by
      simp only [bne_iff_ne]
      exact Driver.append_ne _ (by decide)
    have hj2 : ¬ ("--help" = "--jobs=" ++ jobsStr) :=
      (Driver.append_ne _ (by decide)).symm
    have hs1 : (("--search-path=" ++ dirs) != "--") = true := by
      simp only [bne_iff_ne]
      exact Driver.append_ne _ (by decide)
    have hs2 : ¬ ("--help" = "--search-path=" ++ dirs) :=
      (Driver.append_ne _ (by decide)).symm
    simpa [Driver.helpWanted, List.takeWhile, hj1, hj2, hs1, hs2] using
      helpWanted_constants_tail constants roots
  · have h1 :
        Driver.parseArgs
          (["--verified", "--jobs=" ++ jobsStr, "--olean", "--search-path=" ++ dirs] ++
            constants.map ("--constant=" ++ ·) ++ ("--" :: roots)) {} =
          Driver.parseArgs
            (["--jobs=" ++ jobsStr, "--olean", "--search-path=" ++ dirs] ++
              constants.map ("--constant=" ++ ·) ++ ("--" :: roots))
            { mode := .verified } := by
      rw [Driver.parseArgs.eq_def]
      rfl
    rw [h1]
    simp only [List.cons_append]
    rw [Driver.parseArgs_flag _ _
        (Driver.append_ne _ (by decide))
        (Driver.append_ne _ (by decide))
        (Driver.append_ne _ (by decide))
        (Driver.append_ne _ (by decide))
        (Driver.append_ne _ (by decide)),
      flagValue_progress_jobs jobsStr,
      Driver.flagValue_append]
    simp only [hjobs]
    have h2 :
        Driver.parseArgs
          ("--olean" :: ("--search-path=" ++ dirs) ::
            ([] ++ constants.map ("--constant=" ++ ·) ++ ("--" :: roots)))
          { mode := .verified, jobs := some jobs } =
          Driver.parseArgs
            (("--search-path=" ++ dirs) ::
              ([] ++ constants.map ("--constant=" ++ ·) ++ ("--" :: roots)))
            { mode := .verified, jobs := some jobs, olean := true } := by
      rw [Driver.parseArgs.eq_def]
      rfl
    rw [h2, Driver.parseArgs_flag _ _
        (Driver.append_ne _ (by decide))
        (Driver.append_ne _ (by decide))
        (Driver.append_ne _ (by decide))
        (Driver.append_ne _ (by decide))
        (Driver.append_ne _ (by decide)),
      Driver.flagValue_other dirs (by decide) (by decide),
      Driver.flagValue_other dirs (by decide) (by decide),
      Driver.flagValue_other dirs (by decide) (by decide),
      Driver.flagValue_append]
    have hj : (("--search-path=" ++ dirs) == "--jobs") = false := by
      simp only [beq_eq_false_iff_ne]
      exact Driver.append_ne _ (by decide)
    simp only [hj, Bool.false_eq_true, ↓reduceIte, List.nil_append]
    rw [parseArgs_constants_loop]
    simp [Driver.parseArgs]

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

theorem driver_turbo_ndjson_exit_zero_model_exists (V : Type w) [SetTheory V]
    {jobsStr file : String} {jobs : Nat} {fs : FS} {hs hs' : HS}
    (hjobs : Driver.jobsCount jobsStr = .ok jobs)
    (h : (Driver.runArgs ["--verified", "--jobs=" ++ jobsStr, "--", file] : ModelIO _)
      fs hs (.ok 0) hs') :
    ∃ pre b r env,
      builtinPreludeE = .ok pre ∧
      fs.file file = some b ∧
      parseChunks [b] = .ok r ∧
      Cached.checkDecls .verified natOpPinSets (preparePrelude pre r.decls) = .ok env ∧
      Nonempty (Model V env) := by
  obtain ⟨hh, hp⟩ := parseArgs_turbo_ndjson_invocation jobsStr file jobs hjobs
  suffices H : ModelIO.AllOk
      (Driver.runArgs ["--verified", "--jobs=" ++ jobsStr, "--", file]) fs hs
      (fun c => c = 0 → ∃ pre b r env,
        builtinPreludeE = .ok pre ∧
        fs.file file = some b ∧
        parseChunks [b] = .ok r ∧
        Cached.checkDecls .verified natOpPinSets (preparePrelude pre r.decls) = .ok env ∧
        Nonempty (Model V env)) from
    H 0 hs' h rfl
  refine ModelIO.allOk_tryCatch ?_ fun _ _ _ => ?_
  · simp only [hh, hp, Bool.false_eq_true, ↓reduceIte, Option.getD_some,
      Driver.runReq]
    intro c hs₁ hc h0
    subst h0
    exact checkMainG_ndjson_verified_exit_zero_model_exists V hc
  · simp

theorem driver_turbo_olean_exit_zero_model_exists (V : Type w) [SetTheory V]
    {jobsStr dirs : String} {jobs : Nat} {constants roots : List String}
    {fs : FS} {hs hs' : HS}
    (hjobs : Driver.jobsCount jobsStr = .ok jobs)
    (h : (Driver.runArgs
      (["--verified", "--jobs=" ++ jobsStr, "--olean", "--search-path=" ++ dirs] ++
        constants.map ("--constant=" ++ ·) ++ ("--" :: roots)) : ModelIO _)
      fs hs (.ok 0) hs') :
    let rootConsts :=
      if constants.toArray.isEmpty then none
      else some (constants.toArray.filterMap Olean.parseConstName)
    ∃ pre rd env,
      builtinPreludeE = .ok pre ∧
      ModelIO.CanGive
        (Olean.readOleans (Driver.searchPathOf dirs)
          (roots.toArray.filterMap Olean.parseModName) rootConsts)
        fs (.ok rd) ∧
      Cached.checkDecls .verified natOpPinSets
        ((prepareD pre rd.decls (Driver.usedOf (some (Driver.searchPathOf dirs, rd)))).decls.map
          (Cached.fillDecl (Driver.fillOf (Driver.searchPathOf dirs) fs rd.values))) = .ok env ∧
      Nonempty (Model V env) := by
  obtain ⟨hh, hp⟩ := parseArgs_turbo_olean_invocation jobsStr dirs jobs constants roots hjobs
  obtain ⟨pre, rd, env, hpre, hrd, hchk⟩ :=
    Driver.runArgs_oleans_accept hh (by rw [hp]) (by rw [hp]) h
  rw [hp] at hrd hchk
  simp only [Driver.Args.rootConstants] at hrd
  exact ⟨pre, rd, env, hpre, hrd, hchk, ConLeche.model_exists V natOpPinSets _ env hchk⟩

theorem driver_turbo_olean_false_never_exits_zero (V : Type w) [SetTheory V]
    {jobsStr dirs : String} {jobs : Nat} {roots : List String}
    {m : Name} {fs : FS} {d : Olean.ModDecoded}
    {c : Olean.CEntryF Name Expr} {v : Expr} {all : List Name}
    (hjobs : Driver.jobsCount jobsStr = .ok jobs)
    (hcl : Olean.InClosure (Driver.searchPathOf dirs) fs
      (roots.toArray.filterMap Olean.parseModName) m)
    (hv : Olean.ViewOf (Driver.searchPathOf dirs) fs m d)
    (hmem : c ∈ d.constants) (hk : c.kind = .thm v all)
    (hty : c.type = .const falseName []) :
    ¬ ModelIO.CanGive
      (Driver.runArgs
        (["--verified", "--jobs=" ++ jobsStr, "--olean", "--search-path=" ++ dirs] ++
          ([] : List String).map ("--constant=" ++ ·) ++ ("--" :: roots)))
      fs 0 := by
  rintro ⟨hs, hs', h⟩
  obtain ⟨pre, rd, env, -, ⟨_, _, hrd⟩, hchk, -⟩ :=
    driver_turbo_olean_exit_zero_model_exists V
      (constants := []) (roots := roots) hjobs h
  have hempty : (([] : List String).toArray).isEmpty = true := rfl
  simp only [hempty, ↓reduceIte] at hrd
  obtain ⟨v', hd⟩ :=
    readOleans_closure_thm_in_prepared_filled_stream
      (pre := pre)
      (used := Driver.usedOf (some (Driver.searchPathOf dirs, rd)))
      (F := Driver.fillOf (Driver.searchPathOf dirs) fs rd.values)
      hrd hcl hv hmem hk
  exact no_False_theorem_accepted V _ _ _ hd hty env hchk

end ConLecheBridge
