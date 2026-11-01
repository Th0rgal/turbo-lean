import B2.BackendLower
import B2.AllocationEval

/-! Concrete preparation and spill allocation, tied to the actual upstream pipeline. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option cbv.maxSteps 1000000
set_option Elab.async false
namespace B2.Artifacts
open Backend

def vcp : VCode :=
  { vc with blocks := #[vc.blocks[0]!, vc.blocks[1]!, vc.blocks[3]!, vc.blocks[2]!] }

/-- Literal allocation keeps later certificates from repeating the spill allocator. -/
def rf : RFunc :=
  { blocks := #[#[RItem.move (Loc.reg (Reg.x 19)) (Loc.save (Reg.x 19)),
                  RItem.move (Loc.reg (Reg.x 20)) (Loc.save (Reg.x 20)),
                  RItem.move (Loc.reg (Reg.x 21)) (Loc.save (Reg.x 21)),
                  RItem.move (Loc.reg (Reg.x 22)) (Loc.save (Reg.x 22)),
                  RItem.move (Loc.reg (Reg.x 23)) (Loc.save (Reg.x 23)),
                  RItem.move (Loc.reg (Reg.x 24)) (Loc.save (Reg.x 24)),
                  RItem.move (Loc.reg (Reg.x 25)) (Loc.save (Reg.x 25)),
                  RItem.move (Loc.reg (Reg.x 26)) (Loc.save (Reg.x 26)),
                  RItem.move (Loc.reg (Reg.x 27)) (Loc.save (Reg.x 27)),
                  RItem.move (Loc.reg (Reg.x 28)) (Loc.save (Reg.x 28)),
                  RItem.move (Loc.reg (Reg.v 8)) (Loc.save (Reg.v 8)),
                  RItem.move (Loc.reg (Reg.v 9)) (Loc.save (Reg.v 9)),
                  RItem.move (Loc.reg (Reg.v 10)) (Loc.save (Reg.v 10)),
                  RItem.move (Loc.reg (Reg.v 11)) (Loc.save (Reg.v 11)),
                  RItem.move (Loc.reg (Reg.v 12)) (Loc.save (Reg.v 12)),
                  RItem.move (Loc.reg (Reg.v 13)) (Loc.save (Reg.v 13)),
                  RItem.move (Loc.reg (Reg.v 14)) (Loc.save (Reg.v 14)),
                  RItem.move (Loc.reg (Reg.v 15)) (Loc.save (Reg.v 15)),
                  RItem.op 0 #[Loc.reg (Reg.x 0), Loc.reg (Reg.x 1)],
                  RItem.move (Loc.reg (Reg.x 0)) (Loc.stack 1 (RegClass.int)),
                  RItem.move (Loc.reg (Reg.x 1)) (Loc.stack 2 (RegClass.int)),
                  RItem.op 1 #[Loc.reg (Reg.x 0)],
                  RItem.move (Loc.reg (Reg.x 0)) (Loc.stack 0 (RegClass.int)),
                  RItem.move (Loc.stack 0 (RegClass.int)) (Loc.reg (Reg.x 9)),
                  RItem.move (Loc.reg (Reg.x 9)) (Loc.stack 18 (RegClass.int)),
                  RItem.move (Loc.stack 1 (RegClass.int)) (Loc.reg (Reg.x 9)),
                  RItem.move (Loc.reg (Reg.x 9)) (Loc.stack 19 (RegClass.int)),
                  RItem.move (Loc.stack 18 (RegClass.int)) (Loc.reg (Reg.x 9)),
                  RItem.move (Loc.reg (Reg.x 9)) (Loc.stack 3 (RegClass.int)),
                  RItem.move (Loc.stack 19 (RegClass.int)) (Loc.reg (Reg.x 9)),
                  RItem.move (Loc.reg (Reg.x 9)) (Loc.stack 4 (RegClass.int)),
                  RItem.op 2 #[]],
                #[RItem.move (Loc.stack 3 (RegClass.int)) (Loc.reg (Reg.x 0)),
                  RItem.move (Loc.stack 2 (RegClass.int)) (Loc.reg (Reg.x 1)),
                  RItem.op 0 #[Loc.reg (Reg.x 0), Loc.reg (Reg.x 1)],
                  RItem.op 1 #[Loc.reg (Reg.x 0)],
                  RItem.move (Loc.reg (Reg.x 0)) (Loc.stack 5 (RegClass.int)),
                  RItem.move (Loc.stack 3 (RegClass.int)) (Loc.reg (Reg.x 0)),
                  RItem.move (Loc.stack 2 (RegClass.int)) (Loc.reg (Reg.x 1)),
                  RItem.op 2 #[Loc.reg (Reg.x 0), Loc.reg (Reg.x 1)],
                  RItem.op 3 #[]],
                #[RItem.move (Loc.save (Reg.x 19)) (Loc.reg (Reg.x 19)),
                  RItem.move (Loc.save (Reg.x 20)) (Loc.reg (Reg.x 20)),
                  RItem.move (Loc.save (Reg.x 21)) (Loc.reg (Reg.x 21)),
                  RItem.move (Loc.save (Reg.x 22)) (Loc.reg (Reg.x 22)),
                  RItem.move (Loc.save (Reg.x 23)) (Loc.reg (Reg.x 23)),
                  RItem.move (Loc.save (Reg.x 24)) (Loc.reg (Reg.x 24)),
                  RItem.move (Loc.save (Reg.x 25)) (Loc.reg (Reg.x 25)),
                  RItem.move (Loc.save (Reg.x 26)) (Loc.reg (Reg.x 26)),
                  RItem.move (Loc.save (Reg.x 27)) (Loc.reg (Reg.x 27)),
                  RItem.move (Loc.save (Reg.x 28)) (Loc.reg (Reg.x 28)),
                  RItem.move (Loc.save (Reg.v 8)) (Loc.reg (Reg.v 8)),
                  RItem.move (Loc.save (Reg.v 9)) (Loc.reg (Reg.v 9)),
                  RItem.move (Loc.save (Reg.v 10)) (Loc.reg (Reg.v 10)),
                  RItem.move (Loc.save (Reg.v 11)) (Loc.reg (Reg.v 11)),
                  RItem.move (Loc.save (Reg.v 12)) (Loc.reg (Reg.v 12)),
                  RItem.move (Loc.save (Reg.v 13)) (Loc.reg (Reg.v 13)),
                  RItem.move (Loc.save (Reg.v 14)) (Loc.reg (Reg.v 14)),
                  RItem.move (Loc.save (Reg.v 15)) (Loc.reg (Reg.v 15)),
                  RItem.move (Loc.stack 4 (RegClass.int)) (Loc.reg (Reg.x 0)),
                  RItem.op 0 #[Loc.reg (Reg.x 0)]],
                #[RItem.op 0 #[Loc.reg (Reg.x 0)],
                  RItem.move (Loc.reg (Reg.x 0)) (Loc.stack 8 (RegClass.int)),
                  RItem.move (Loc.stack 4 (RegClass.int)) (Loc.reg (Reg.x 1)),
                  RItem.move (Loc.stack 8 (RegClass.int)) (Loc.reg (Reg.x 2)),
                  RItem.op
                    1
                    #[Loc.reg (Reg.x 0), Loc.reg (Reg.x 1),
                      Loc.reg (Reg.x 2)],
                  RItem.move (Loc.reg (Reg.x 0)) (Loc.stack 9 (RegClass.int)),
                  RItem.move (Loc.stack 4 (RegClass.int)) (Loc.reg (Reg.x 1)),
                  RItem.move (Loc.stack 8 (RegClass.int)) (Loc.reg (Reg.x 2)),
                  RItem.move (Loc.stack 4 (RegClass.int)) (Loc.reg (Reg.x 3)),
                  RItem.op
                    2
                    #[Loc.reg (Reg.x 0), Loc.reg (Reg.x 1),
                      Loc.reg (Reg.x 2), Loc.reg (Reg.x 3)],
                  RItem.move (Loc.reg (Reg.x 0)) (Loc.stack 10 (RegClass.int)),
                  RItem.op 3 #[Loc.reg (Reg.x 0)],
                  RItem.move (Loc.reg (Reg.x 0)) (Loc.stack 11 (RegClass.int)),
                  RItem.move (Loc.stack 10 (RegClass.int)) (Loc.reg (Reg.x 1)),
                  RItem.op 4 #[Loc.reg (Reg.x 0), Loc.reg (Reg.x 1)],
                  RItem.move (Loc.reg (Reg.x 0)) (Loc.stack 12 (RegClass.int)),
                  RItem.op 5 #[Loc.reg (Reg.x 0)],
                  RItem.move (Loc.reg (Reg.x 0)) (Loc.stack 13 (RegClass.int)),
                  RItem.op 6 #[Loc.reg (Reg.x 0)],
                  RItem.move (Loc.reg (Reg.x 0)) (Loc.stack 14 (RegClass.int)),
                  RItem.move (Loc.stack 12 (RegClass.int)) (Loc.reg (Reg.x 1)),
                  RItem.op 7 #[Loc.reg (Reg.x 0), Loc.reg (Reg.x 1)],
                  RItem.move (Loc.reg (Reg.x 0)) (Loc.stack 15 (RegClass.int)),
                  RItem.op 8 #[Loc.reg (Reg.x 0)],
                  RItem.move (Loc.reg (Reg.x 0)) (Loc.stack 16 (RegClass.int)),
                  RItem.move (Loc.stack 15 (RegClass.int)) (Loc.reg (Reg.x 1)),
                  RItem.op 9 #[Loc.reg (Reg.x 0), Loc.reg (Reg.x 1)],
                  RItem.move (Loc.reg (Reg.x 0)) (Loc.stack 7 (RegClass.int)),
                  RItem.op 10 #[Loc.reg (Reg.x 0)],
                  RItem.move (Loc.reg (Reg.x 0)) (Loc.stack 17 (RegClass.int)),
                  RItem.move (Loc.stack 3 (RegClass.int)) (Loc.reg (Reg.x 1)),
                  RItem.op 11 #[Loc.reg (Reg.x 0), Loc.reg (Reg.x 1)],
                  RItem.move (Loc.reg (Reg.x 0)) (Loc.stack 6 (RegClass.int)),
                  RItem.move (Loc.stack 6 (RegClass.int)) (Loc.reg (Reg.x 9)),
                  RItem.move (Loc.reg (Reg.x 9)) (Loc.stack 18 (RegClass.int)),
                  RItem.move (Loc.stack 7 (RegClass.int)) (Loc.reg (Reg.x 9)),
                  RItem.move (Loc.reg (Reg.x 9)) (Loc.stack 19 (RegClass.int)),
                  RItem.move (Loc.stack 18 (RegClass.int)) (Loc.reg (Reg.x 9)),
                  RItem.move (Loc.reg (Reg.x 9)) (Loc.stack 3 (RegClass.int)),
                  RItem.move (Loc.stack 19 (RegClass.int)) (Loc.reg (Reg.x 9)),
                  RItem.move (Loc.reg (Reg.x 9)) (Loc.stack 4 (RegClass.int)),
                  RItem.op 12 #[]]],
    spillSlots := 20,
    saved := [Reg.x 19,
              Reg.x 20,
              Reg.x 21,
              Reg.x 22,
              Reg.x 23,
              Reg.x 24,
              Reg.x 25,
              Reg.x 26,
              Reg.x 27,
              Reg.x 28,
              Reg.v 8,
              Reg.v 9,
              Reg.v 10,
              Reg.v 11,
              Reg.v 12,
              Reg.v 13,
              Reg.v 14,
              Reg.v 15] }

theorem prepared : prepare vc = .ok vcp := by cbv

theorem spill_alloc : spillAlloc vcp = rf := by cbv

theorem allocation_checked : checkAlloc vcp rf = .ok () := by cbv

#print axioms prepared
#print axioms spill_alloc
#print axioms allocation_checked
end B2.Artifacts
