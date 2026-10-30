#!/usr/bin/env python3
"""Derive unique-K timing tables from preserved measured calls; no new replay."""
import collections, gzip, json, pathlib, statistics
from run_experiment import DATA

def summarize(d):
    bykey=collections.defaultdict(list)
    with gzip.open(d/'kernel_groups.jsonl.gz','rt') as f:
        for line in f:
            g=json.loads(line);bykey[g['K']].append(g)
    tmp=d/'kernel_by_K.tmp.jsonl.gz'
    with gzip.open(tmp,'wt') as f:
        for k,gs in sorted(bykey.items()):
            times=[g['cpu_ns']/1e6 for g in gs]
            f.write(json.dumps({'K':k,'kernel_ms':statistics.median(times),'mean_kernel_ms':statistics.mean(times),
                'total_kernel_ms':sum(times),'min_kernel_ms':min(times),'max_kernel_ms':max(times),
                'occurrences':len(times),'kind':gs[0]['kind'],'modules':sorted({g['module'] for g in gs}),
                'names':gs[0]['names']},separators=(',',':'))+'\n')
    tmp.replace(d/'kernel_by_K.jsonl.gz')
    return len(bykey)

def main():
    for p in sorted(DATA.glob('*/complete.json')):
        d=p.parent
        if not (d/'kernel_by_K.jsonl.gz').exists():print(d.name,summarize(d))
if __name__=='__main__':main()
