import unittest
from report import nonaux

class ExampleSelection(unittest.TestCase):
    def test_generated_names_are_excluded(self):
        for name in ('Clif.Ty.isInt.eq_7', 'Isle.Program.patText.eq_def',
                     'Isle.Expr.rec_1', 'Clif.Stmt.mk.injEq',
                     'A._proof_1.member', '_private.FV.File.0.foo',
                     'Backend.instReprV.repr', 'A.match_1', 'A.foo_eq_2'):
            with self.subTest(name=name):self.assertFalse(nonaux(name))

    def test_named_declarations_remain_candidates(self):
        for name in ('Backend.Proof.tryIndOkP_of_rules', 'Opt.Proof.KernelBV.refute',
                     'Clif.Parse.lexLine', 'Backend.Proof.FastSubst.substVars'):
            with self.subTest(name=name):self.assertTrue(nonaux(name))

if __name__=='__main__':unittest.main()
