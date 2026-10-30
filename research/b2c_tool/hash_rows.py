#!/usr/bin/env python3
"""SHA-256 of Lean's explicit Expr DAG serialization; Expr.hash is never a key.

Lean extracts structures; this companion applies SHA-256 and SCC closure. JSON UTF-8,
compact separators, sorted object keys, and tagged/versioned hash domains are canonical.
"""
import argparse, gzip, hashlib, json, sys

def H(x):
    return hashlib.sha256(json.dumps(x, ensure_ascii=False, sort_keys=True, separators=(',', ':')).encode()).hexdigest()

def normalize(r):
    hashes = []
    for node in r.pop('nodes'):
        q = list(node)
        positions = {'app': (1,2), 'lam': (3,4), 'forall': (3,4),
                     'let': (3,4,5), 'mdata': (2,), 'proj': (3,)}.get(q[0], ())
        for i in positions:
            q[i] = hashes[q[i]]
        hashes.append(H(['Expr-v1', q]))
    for key in ('if_payload', 'k_payload'):
        p = r[key]
        p[3] = hashes[p[3]]
        if p[0] in ('definition', 'opaque') or (p[0] == 'theorem' and key == 'k_payload'):
            p[4] = hashes[p[4]]
        if p[0] == 'recursor':
            for rule in p[9]:
                rule[2] = hashes[rule[2]]
    return r

def closure(rows, allow_missing=False):
    byname = {r['name']:r for r in rows}
    graph = {k:sorted(set(r['if_deps'])) for k,r in byname.items()}
    missing = sorted({d for ds in graph.values() for d in ds if d not in graph})
    if missing and not allow_missing:
        raise ValueError(f'{len(missing)} missing IF dependencies: {missing[:20]}')
    # Iterative Kosaraju, then dependency-first condensation evaluation.
    seen, order = set(), []
    for start in sorted(graph):
        stack = [(start, False)]
        while stack:
            v, exit_ = stack.pop()
            if exit_:
                order.append(v)
            elif v not in seen:
                seen.add(v); stack.append((v, True))
                stack.extend((d,False) for d in reversed(graph[v]) if d in graph and d not in seen)
    rev = {v:[] for v in graph}
    for v, ds in graph.items():
        for d in ds:
            if d in rev: rev[d].append(v)
    comps, owner, seen = [], {}, set()
    for start in reversed(order):
        if start in seen: continue
        members, stack = [], [start]
        while stack:
            v = stack.pop()
            if v in seen: continue
            seen.add(v); members.append(v); stack.extend(rev[v])
        members.sort(); idx=len(comps); comps.append(members)
        owner.update((v,idx) for v in members)
    interfaces = {v:H(['fixture-external',v]) for v in missing}
    done = set()
    for start in range(len(comps)):
        stack = [(start,False)]
        while stack:
            i, exit_ = stack.pop()
            if i in done: continue
            if not exit_:
                stack.append((i,True))
                stack.extend((owner[d],False) for v in comps[i] for d in graph[v]
                             if d in owner and owner[d]!=i and owner[d] not in done)
                continue
            members = comps[i]; local = set(members)
            material = [[v,byname[v]['if_payload'],
                         [['internal',d] if d in local else ['external',d,interfaces[d]]
                          for d in graph[v]]] for v in members]
            ch = H(['IF-SCC-v1',material])
            for v in members: interfaces[v] = H(['IF-member-v1',ch,v])
            done.add(i)
    for r in rows:
        r['IF'] = interfaces[r['name']]
        kd = sorted(set(r['k_deps']))
        absent = [d for d in kd if d not in interfaces]
        if absent and not allow_missing: raise ValueError(f"missing K dependencies {r['name']}: {absent[:10]}")
        r['K'] = H(['K-optimistic-v1',r['k_payload'],
                    [[d,interfaces.get(d,H(['fixture-external',d]))] for d in kd],
                    'leanprover/lean4:v4.34.1', '5045d0056413266e57c625dcd7c365b10e377c52'])
    return rows

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('input'); ap.add_argument('output'); ap.add_argument('--fixtures',action='store_true')
    a=ap.parse_args(); modules=[]; rows=[]; fixtures={}; label=None
    with open(a.input) as f:
        for line in f:
            r=json.loads(line)
            if r['event']=='fixture': label=r['label']; fixtures[label]=[]
            elif r['event']=='module': modules.append(r)
            elif r['event']=='constant':
                normalize(r)
                (fixtures[label] if a.fixtures else rows).append(r)
    if a.fixtures:
        for rs in fixtures.values(): closure(rs,True)
        def get(label,name,key): return next(r[key] for r in fixtures[label] if r['name']==name)
        checks={
            'proposition_body_changes_theorem_IF':get('p_true','h','IF')!=get('p_conj','h','IF'),
            'ordered_levelParams_change_IF':get('uv','ordered','IF')!=get('vu','ordered','IF'),
            'proof_body_preserves_IF':get('proof_a','proof','IF')==get('proof_b','proof','IF'),
            'proof_body_changes_K':get('proof_a','proof','K')!=get('proof_b','proof','K')}
        assert all(checks.values()),checks
        with open(a.output,'w') as f: json.dump({'checks':checks,'kernel_validated':True,'fixtures':fixtures,'external_dependency_policy':'fixture-only symbolic leaves'},f,indent=2)
        print(json.dumps(checks)); return
    closure(rows)
    with gzip.open(a.output,'wt',compresslevel=6) as f:
        for r in rows:
            for k in ('if_payload','k_payload','name_struct'): r.pop(k,None)
            f.write(json.dumps(r,separators=(',',':'))+'\n')
    with open(a.output+'.modules.json','w') as f: json.dump(modules,f,indent=2)
    print(json.dumps({'rows':len(rows),'modules':len(modules),'output':a.output}))
if __name__=='__main__':main()
