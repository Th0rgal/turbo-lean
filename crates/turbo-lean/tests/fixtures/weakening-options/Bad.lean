import Lean

-- True.intro is deliberately given the type False without an extra axiom.
-- addDecl must reject it unless debug.skipKernelTC bypasses kernel checking.
open Lean Elab Command in
run_elab do
  Lean.addDecl <| .thmDecl {
    name := `bad
    levelParams := []
    type := Lean.mkConst ``False
    value := Lean.mkConst ``True.intro
  }

#print axioms bad
