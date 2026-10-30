#!/usr/bin/env python3
"""Behavioral checks for graph propagation, cycle closure, and order independence."""
import copy, json, pathlib, unittest
from hash_rows import closure, node_hashes

class ClosureTests(unittest.TestCase):
    def setUp(self):
        self.fixtures=json.loads((pathlib.Path(__file__).parent/'fixtures.json').read_text())['fixtures']
    def test_order_independent(self):
        rows=copy.deepcopy(self.fixtures['p_true'])
        a=closure(rows,True)
        b=closure(list(reversed(copy.deepcopy(rows))),True)
        self.assertEqual({r['name']:(r['IF'],r['K']) for r in a},
                         {r['name']:(r['IF'],r['K']) for r in b})
    def test_scc_body_change_propagates_to_every_member_and_dependent(self):
        def row(name,deps,body):
            return {'name':name,'if_deps':deps,'k_deps':deps,
                    'if_payload':['definition',name,body],'k_payload':['definition',name,body]}
        rs=[row('a',['b'],1),row('b',['a'],2),row('consumer',['a'],3),row('unrelated',[],4)]
        a={r['name']:r['IF'] for r in closure(copy.deepcopy(rs))}
        rs[1]['if_payload'][-1]=42
        b={r['name']:r['IF'] for r in closure(rs)}
        self.assertNotEqual(a['a'],b['a']); self.assertNotEqual(a['b'],b['b'])
        self.assertNotEqual(a['consumer'],b['consumer']); self.assertEqual(a['unrelated'],b['unrelated'])
    def test_missing_dependencies_rejected_for_experiment(self):
        with self.assertRaises(ValueError):closure(copy.deepcopy(self.fixtures['p_true']))
    def test_node_hash_ignores_sharing_and_node_indices(self):
        shared=[['nat',7],['app',0,0]]
        copied=[['string','unrelated'],['nat',7],['nat',7],['app',1,2]]
        self.assertEqual(node_hashes(shared)[-1],node_hashes(copied)[-1])
if __name__=='__main__':unittest.main()
