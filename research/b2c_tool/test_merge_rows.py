#!/usr/bin/env python3
"""A resumed timing join must preserve measured declaration and group keys."""
import gzip, json, pathlib, shutil, tempfile, unittest
from run_experiment import merge_rows

class JoinTests(unittest.TestCase):
    def test_repeating_join_preserves_keys_and_distinct_timing_counts(self):
        validation=pathlib.Path(__file__).parent.parent/'b2c_data/validation'
        with tempfile.TemporaryDirectory() as tmp:
            d=pathlib.Path(tmp)
            shutil.copyfile(validation/'prelude_rows.jsonl.gz',d/'rows.jsonl.gz')
            raw=(validation/'init_prelude_replay.jsonl').read_text()
            with gzip.open(d/'replay.jsonl.gz','wt') as f:f.write(raw)
            (d/'replay_total.json').write_text(json.dumps(json.loads(raw.splitlines()[-1])))
            def keys():
                with gzip.open(d/'rows.jsonl.gz','rt') as f:
                    return [(r['name'],r['IF'],r['K'],r['constant_K']) for line in f if (r:=json.loads(line))]
            before=keys()
            merge_rows(d)
            self.assertEqual(before,keys())
            merge_rows(d)
            self.assertEqual(before,keys())
            with gzip.open(d/'kernel_by_K.jsonl.gz','rt') as f:ts=[json.loads(line) for line in f]
            self.assertEqual(len(ts),2033)
            self.assertEqual(sum(t['occurrences'] for t in ts),2033)
if __name__=='__main__':unittest.main()
