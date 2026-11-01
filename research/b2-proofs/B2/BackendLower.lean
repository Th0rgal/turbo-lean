import B2.CollatzClif
import B2.BackendEval
import FV.Backend.InputScope

/-! The exact instruction-selection artifact of the real shared CLIF lowering. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option cbv.maxSteps 1000000
set_option Elab.async false
namespace B2.Artifacts
open Backend
attribute [local irreducible] B2.Smoke.collatz

/-- Kernel-tied snapshot avoids repeatedly evaluating the LNIR lowering inside backend checks. -/
def input : Clif.Function :=
  { name := "collatz_steps"
    sig := { params := [⟨.i64, .none, .normal⟩, ⟨.i64, .none, .normal⟩]
             returns := [⟨.i64, .none, .normal⟩] }
    blocks := [B2.CollatzClif.entryBlock, B2.CollatzClif.headerBlock,
      B2.CollatzClif.bodyBlock, B2.CollatzClif.exitBlock] }

theorem input_eq : input = B2.Smoke.collatz := by
  obtain ⟨blocks, hf, _⟩ := B2.Lowering.lower_success _ _ B2.Smoke.collatz_lowered
  have hb : blocks = [B2.CollatzClif.entryBlock, B2.CollatzClif.headerBlock,
      B2.CollatzClif.bodyBlock, B2.CollatzClif.exitBlock] := by
    simpa only [hf, LeanNative.Backend.Clif.assemble] using B2.CollatzClif.generated_blocks
  rw [hf, hb]
  rfl

#print axioms input_eq

def vc : VCode :=
  { name := "collatz_steps",
    blocks := #[{ label := 0,
                  insts := #[Backend.MInst.args
                               [(Backend.Reg.vreg 0 (Backend.RegClass.int), Backend.Reg.x 0),
                                (Backend.Reg.vreg 1 (Backend.RegClass.int), Backend.Reg.x 1)],
                             Backend.MInst.movWide
                               (Backend.MoveWideOp.movZ)
                               (Backend.Reg.vreg 18 (Backend.RegClass.int))
                               { bits := 0, shift := 0 }
                               (Backend.OperandSize.size64),
                             Backend.MInst.jump 1],
                  params := #[],
                  branchArgs := #[Backend.Reg.vreg 18 (Backend.RegClass.int),
                                  Backend.Reg.vreg 0 (Backend.RegClass.int)] },
                { label := 1,
                  insts := #[Backend.MInst.aluRRR
                               (Backend.ALUOp.subS)
                               (Backend.OperandSize.size64)
                               (Backend.Reg.xzr)
                               (Backend.Reg.vreg 3 (Backend.RegClass.int))
                               (Backend.Reg.vreg 1 (Backend.RegClass.int)),
                             Backend.MInst.cset (Backend.Reg.vreg 19 (Backend.RegClass.int)) (Backend.Cond.lo),
                             Backend.MInst.aluRRR
                               (Backend.ALUOp.subS)
                               (Backend.OperandSize.size64)
                               (Backend.Reg.xzr)
                               (Backend.Reg.vreg 3 (Backend.RegClass.int))
                               (Backend.Reg.vreg 1 (Backend.RegClass.int)),
                             Backend.MInst.condBr 2 3 (Backend.CondBrKind.cond (Backend.Cond.lo))],
                  params := #[Backend.Reg.vreg 3 (Backend.RegClass.int), Backend.Reg.vreg 4 (Backend.RegClass.int)],
                  branchArgs := #[] },
                { label := 2,
                  insts := #[Backend.MInst.movWide
                               (Backend.MoveWideOp.movZ)
                               (Backend.Reg.vreg 20 (Backend.RegClass.int))
                               { bits := 2, shift := 0 }
                               (Backend.OperandSize.size64),
                             Backend.MInst.aluRRRR
                               (Backend.ALUOp3.mAdd)
                               (Backend.OperandSize.size64)
                               (Backend.Reg.vreg 21 (Backend.RegClass.int))
                               (Backend.Reg.vreg 4 (Backend.RegClass.int))
                               (Backend.Reg.vreg 20 (Backend.RegClass.int))
                               (Backend.Reg.xzr),
                             Backend.MInst.aluRRRR
                               (Backend.ALUOp3.mAdd)
                               (Backend.OperandSize.size64)
                               (Backend.Reg.vreg 22 (Backend.RegClass.int))
                               (Backend.Reg.vreg 4 (Backend.RegClass.int))
                               (Backend.Reg.vreg 20 (Backend.RegClass.int))
                               (Backend.Reg.vreg 4 (Backend.RegClass.int)),
                             Backend.MInst.movWide
                               (Backend.MoveWideOp.movZ)
                               (Backend.Reg.vreg 23 (Backend.RegClass.int))
                               { bits := 1, shift := 0 }
                               (Backend.OperandSize.size64),
                             Backend.MInst.aluRRImm12
                               (Backend.ALUOp.add)
                               (Backend.OperandSize.size64)
                               (Backend.Reg.vreg 24 (Backend.RegClass.int))
                               (Backend.Reg.vreg 22 (Backend.RegClass.int))
                               { bits := 1, shift12 := false },
                             Backend.MInst.movWide
                               (Backend.MoveWideOp.movZ)
                               (Backend.Reg.vreg 25 (Backend.RegClass.int))
                               { bits := 2, shift := 0 }
                               (Backend.OperandSize.size64),
                             Backend.MInst.movWide
                               (Backend.MoveWideOp.movZ)
                               (Backend.Reg.vreg 26 (Backend.RegClass.int))
                               { bits := 1, shift := 0 }
                               (Backend.OperandSize.size64),
                             Backend.MInst.aluRRImmShift
                               (Backend.ALUOp.lsr)
                               (Backend.OperandSize.size64)
                               (Backend.Reg.vreg 27 (Backend.RegClass.int))
                               (Backend.Reg.vreg 24 (Backend.RegClass.int))
                               1,
                             Backend.MInst.movWide
                               (Backend.MoveWideOp.movZ)
                               (Backend.Reg.vreg 28 (Backend.RegClass.int))
                               { bits := 0, shift := 0 }
                               (Backend.OperandSize.size64),
                             Backend.MInst.aluRRImm12
                               (Backend.ALUOp.add)
                               (Backend.OperandSize.size64)
                               (Backend.Reg.vreg 29 (Backend.RegClass.int))
                               (Backend.Reg.vreg 27 (Backend.RegClass.int))
                               { bits := 0, shift12 := false },
                             Backend.MInst.movWide
                               (Backend.MoveWideOp.movZ)
                               (Backend.Reg.vreg 30 (Backend.RegClass.int))
                               { bits := 1, shift := 0 }
                               (Backend.OperandSize.size64),
                             Backend.MInst.aluRRImm12
                               (Backend.ALUOp.add)
                               (Backend.OperandSize.size64)
                               (Backend.Reg.vreg 31 (Backend.RegClass.int))
                               (Backend.Reg.vreg 3 (Backend.RegClass.int))
                               { bits := 1, shift12 := false },
                             Backend.MInst.jump 1],
                  params := #[],
                  branchArgs := #[Backend.Reg.vreg 31 (Backend.RegClass.int),
                                  Backend.Reg.vreg 29 (Backend.RegClass.int)] },
                { label := 3,
                  insts := #[Backend.MInst.rets [(Backend.Reg.vreg 4 (Backend.RegClass.int), Backend.Reg.x 0)]],
                  params := #[],
                  branchArgs := #[] }],
    classes := #[Backend.RegClass.int, Backend.RegClass.int, Backend.RegClass.int, Backend.RegClass.int,
                 Backend.RegClass.int, Backend.RegClass.int, Backend.RegClass.int, Backend.RegClass.int,
                 Backend.RegClass.int, Backend.RegClass.int, Backend.RegClass.int, Backend.RegClass.int,
                 Backend.RegClass.int, Backend.RegClass.int, Backend.RegClass.int, Backend.RegClass.int,
                 Backend.RegClass.int, Backend.RegClass.int, Backend.RegClass.int, Backend.RegClass.int,
                 Backend.RegClass.int, Backend.RegClass.int, Backend.RegClass.int, Backend.RegClass.int,
                 Backend.RegClass.int, Backend.RegClass.int, Backend.RegClass.int, Backend.RegClass.int,
                 Backend.RegClass.int, Backend.RegClass.int, Backend.RegClass.int, Backend.RegClass.int],
    slotBytes := 0,
    outgoing := 0,
    rulesFired := #[79, 124, 322, 1, 582, 559, 6, 1139, 79, 156, 508, 196, 29, 961, 1, 958, 79, 156, 508, 493, 561, 48,
                    1135, 7, 1132, 79, 124, 322, 1, 582, 79, 148, 213, 1, 759, 79, 148, 213, 1, 598, 79, 124, 322, 1, 582,
                    79, 142, 203, 1, 589, 79, 124, 322, 1, 582, 79, 124, 322, 1, 582, 336, 79, 127, 882, 1, 884, 79, 124,
                    322, 1, 582, 79, 142, 203, 1, 589, 79, 124, 322, 1, 582, 79, 142, 203, 1, 589, 559, 6, 1139, 77,
                    1037] }
theorem verifiable : Backend.verifiable B2.Smoke.collatz = true := by decide +kernel

#print axioms verifiable

theorem lower : lowerFunction B2.Smoke.collatz = .ok vc := by
  rw [← input_eq]
  cbv

#print axioms lower

end B2.Artifacts
