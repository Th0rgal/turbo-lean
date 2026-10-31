import B2.CollatzClif
import FV.Backend.Regalloc
import FV.Backend.Encode
import FV.Backend.InputScope

/-! O5 artifacts from clifv's real executable pipeline, including its checked spill allocation.
These definitions are not a model of compilation; each successful equation is kernel-checked. -/
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace B2.Artifacts
open Backend

deriving instance DecidableEq for Except
deriving instance DecidableEq for Backend.VBlock
deriving instance DecidableEq for Backend.VCode

/-- Kernel-tied snapshot avoids repeatedly evaluating the LNIR lowering inside backend checks. -/
def input : Clif.Function :=
  { name := "collatz_steps"
    sig := { params := [⟨.i64, .none, .normal⟩, ⟨.i64, .none, .normal⟩]
             returns := [⟨.i64, .none, .normal⟩] }
    blocks := [B2.CollatzClif.entryBlock, B2.CollatzClif.headerBlock,
      B2.CollatzClif.bodyBlock, B2.CollatzClif.exitBlock] }

theorem input_eq : input = B2.Smoke.collatz := by decide +kernel

#print axioms input_eq

-- Concrete output of the real lowerFunction, certified by `lower` below.
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
def vcp : VCode := (prepare vc).toOption.getD default
def rf : RFunc := spillAlloc vcp
def af : AFunc := (lowerRFunc vcp rf).toOption.getD default
def fa : FnAsm := (emitFunc 0 af).toOption.getD default
def fb : FnBin := fa.layout.toOption.getD default

private theorem success {α : Type} [Inhabited α] (e : Except String α)
    (h : e.isOk = true) : e = .ok (e.toOption.getD default) := by
  cases e with
  | error _ => cases h
  | ok _ => rfl

theorem verifiable : Backend.verifiable B2.Smoke.collatz = true := by decide +kernel

#print axioms verifiable

theorem lower : lowerFunction B2.Smoke.collatz = .ok vc := by
  rw [← input_eq]
  decide +kernel

#print axioms lower

theorem prepared : prepare vc = .ok vcp := success _ (by decide +kernel)

#print axioms prepared

theorem allocation_checked : checkAlloc vcp rf = .ok () := by
  have h : (checkAlloc vcp rf).isOk = true := by decide +kernel
  cases hc : checkAlloc vcp rf with
  | error _ => rw [hc] at h; cases h
  | ok u => cases u; rfl

#print axioms allocation_checked

theorem allocated : lowerRFunc vcp rf = .ok af := success _ (by decide +kernel)

#print axioms allocated

theorem emitted : emitFunc 0 af = .ok fa := success _ (by decide +kernel)

#print axioms emitted

theorem laid_out : fa.layout = .ok fb := success _ (by decide +kernel)

#print axioms laid_out

end B2.Artifacts
