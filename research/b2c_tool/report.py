#!/usr/bin/env python3
"""Analyze completed, replay-covered commits. No inferred or synthetic timings."""
import collections, gzip, hashlib, json, pathlib, re, subprocess
from run_experiment import DATA, RESULTS, CLIFV, H, TARGETS

def readj(p):return json.loads(p.read_text())
def readgz(p):
    with gzip.open(p,'rt') as f:return [json.loads(l) for l in f]
def frac(n,d):return n/d if d else None

def nonaux(name):
    return (not name.startswith('_private.') and
            not re.search(r'(^|\.)(_.*|match_\d+|rec|recOn|casesOn|brecOn|below|noConfusion.*|ctorIdx|sizeOf_spec|.*_eq_\d+)$',name))
def examples(groups,limit=3):
    byname={}
    for g in sorted(groups,key=lambda x:-x['cpu_ns']):
        for n in g['names']:
            if nonaux(n):byname.setdefault(n,{'name':n,'commit':g['commit'],'module':g['module'],
                'K':g['K'],'kernel_ms':g['cpu_ns']/1e6})
    return list(byname.values())[:limit]

def load(commit):
    d=DATA/commit[:8]; assert readj(d/'complete.json')['commit']==commit
    coverage=readj(d/'coverage.json');total=readj(d/'replay_total.json')
    assert coverage['all_constants_covered'] and total['sum_le_total_cpu']
    assert total['cpu_clock']=='CLOCK_PROCESS_CPUTIME_ID'
    assert total['kernel_cpu_ns']<=total['cpu_ns']
    assert coverage['kernel_cpu_ns']==total['kernel_cpu_ns']
    rows=readgz(d/'rows.jsonl.gz')
    assert len(rows)==coverage['rows']
    bymod=collections.defaultdict(list)
    for r in rows:bymod[r['module']].append(r)
    interfaces={m:H(['module-interface-multiset-v1',sorted(r['IF'] for r in rs)]) for m,rs in bymod.items()}
    # Include genuinely empty modules, whose interfaces are the empty multiset.
    moduledata=readj(d/'rows.jsonl.gz.modules.json')
    for m in moduledata:interfaces.setdefault(m['module'],H(['module-interface-multiset-v1',[]]))
    mods={m['module']:m for m in moduledata}
    assert set(TARGETS)<=set(mods),'missing requested target in extraction'
    assert len(mods)==len(moduledata),'duplicate module records'
    assert sum(m['count'] for m in moduledata)==len(rows)
    for mod,md in mods.items():
        rs=bymod[mod]
        assert len(rs)==md['count'],f'constant-count mismatch: {mod}'
        assert len({r['name'] for r in rs})==len(rs),f'duplicate names within module: {mod}'
    reachable=set();todo=TARGETS[:]
    while todo:
        mod=todo.pop()
        if mod in reachable:continue
        assert mod in mods,f'missing imported module: {mod}'
        reachable.add(mod);todo.extend(mods[mod]['imports'])
    assert {m for m in mods if m.startswith('FV.')}=={m for m in reachable if m.startswith('FV.')}
    groups=readgz(d/'kernel_groups.jsonl.gz')
    for g in groups:g['commit']=commit
    assert sum(g['cpu_ns'] for g in groups)==total['kernel_cpu_ns']
    build=readj(d/'build.json');assert build['exit_code']==0
    for r in build['modules']:assert r['exit_code']==0
    return {'commit':commit,'d':d,'rows':rows,'bymod':bymod,'interfaces':interfaces,'mods':mods,
            'groups':groups,'build':build,'sources':readj(d/'sources.json'),'replay':total,'coverage':coverage}

def bucket(gs,total_kernel,build_cpu,build_elapsed):
    ns=sum(g['cpu_ns'] for g in gs)
    ex=examples(gs)
    return {'kernel_seconds':ns/1e9,'share_of_rebuilt_kernel':frac(ns,total_kernel),
            'share_of_build_cpu':frac(ns/1e9,build_cpu),'share_of_summed_module_elapsed':frac(ns/1e9,build_elapsed),
            'group_occurrences':len(gs),'distinct_K':len({g['K'] for g in gs}),
            'examples':ex,'nonauxiliary_example_shortfall':max(0,3-len(ex)) if ns else 0}

def main():
    overview=readj(RESULTS/'research/B2c.json');commits=overview['commits']
    assert len(commits)==20 and len(overview['completed_commits'])==20
    previous=load(commits[0])
    allc=[{k:previous[k] for k in ('commit','replay','coverage')}]
    sums=collections.Counter();transitions=[];reuse=[];cutgroups=[]
    module_stats=collections.defaultdict(collections.Counter)
    module_reuse=collections.defaultdict(list);module_cutexamples=collections.defaultdict(list)
    all_cone_reuse=[];all_cone_total=0
    for commit in commits[1:]:
        prev=previous;cur=load(commit)
        allc.append({k:cur[k] for k in ('commit','replay','coverage')})
        built={r['module']:r for r in cur['build']['modules']}
        assert len(built)==len(cur['build']['modules']),'retry timings require explicit attempt selection'
        # Any build-configuration change is conservatively treated as a local
        # invalidation, rather than attributed to an upstream-interface cutoff.
        config_changed=any(subprocess.check_output(['git','diff',prev['commit'],cur['commit'],'--',p],cwd=CLIFV)
                           for p in ('lakefile.toml','lake-manifest.json','lean-toolchain'))
        must={};propagate={};unmodeled_invalidations=[]
        for mod,md in cur['mods'].items():
            own=cur['sources'].get(mod)!=prev['sources'].get(mod)
            need=own or config_changed or any(propagate.get(d,cur['interfaces'].get(d)!=prev['interfaces'].get(d)) for d in md['imports'])
            changed=cur['interfaces'].get(mod)!=prev['interfaces'].get(mod)
            # Do not credit a module whose observed output interface changed,
            # even if an omitted elaborator input would otherwise hide the cause.
            if changed and not need:
                unmodeled_invalidations.append(mod);need=True
            must[mod]=need
            propagate[mod]=need and changed
        dep={m for m in built if cur['sources'].get(m)==prev['sources'].get(m)}
        cut={m for m in dep if not must.get(m,True)}
        prevkeys={g['K'] for g in prev['groups']}
        allgs=[g for g in cur['groups'] if g['module'].startswith('FV.')]
        gs=[g for g in allgs if g['module'] in built]
        eligible=[g for g in gs if g['kind'] not in ('inductive','quotient') and g['K'] in prevkeys]
        cg=[g for g in gs if g['module'] in cut]
        reuse.extend(eligible);cutgroups.extend(cg)
        all_cone_total+=sum(g['cpu_ns'] for g in allgs)
        all_cone_reuse.extend(g for g in allgs if g['kind'] not in ('inductive','quotient') and g['K'] in prevkeys)
        vals={'build_cpu_seconds':cur['build']['module_cpu_seconds'],
              'module_elapsed_seconds':cur['build']['module_elapsed_seconds'],
              'build_wall_seconds':cur['build']['wall_seconds'],
              'dependent_rebuild_elapsed_seconds':sum(built[m]['seconds'] for m in dep),
              'cutoff_avoidable_elapsed_seconds':sum(built[m]['seconds'] for m in cut),
              'cutoff_avoidable_build_cpu_seconds':sum(built[m]['cpu_seconds'] for m in cut),
              'rebuilt_kernel_ns':sum(g['cpu_ns'] for g in gs),
              'optimistic_reusable_kernel_ns':sum(g['cpu_ns'] for g in eligible),
              'cutoff_kernel_ns':sum(g['cpu_ns'] for g in cg)}
        sums.update(vals)
        for m,r in built.items():
            ms=module_stats[m];ms['build_elapsed_seconds']+=r['seconds'];ms['build_cpu_seconds']+=r['cpu_seconds']
            ms['rebuilt_transitions']+=1
            if m in dep:ms['dependent_rebuild_elapsed_seconds']+=r['seconds']
            if m in cut:
                ms['cutoff_avoidable_elapsed_seconds']+=r['seconds'];ms['cutoff_avoidable_build_cpu_seconds']+=r['cpu_seconds']
                module_cutexamples[m].extend(g for g in cg if g['module']==m)
        for g in gs:module_stats[g['module']]['kernel_seconds']+=g['cpu_ns']/1e9
        for g in eligible:
            module_stats[g['module']]['optimistic_reusable_kernel_seconds']+=g['cpu_ns']/1e9
            module_reuse[g['module']].append(g)
        transitions.append({'previous_commit':prev['commit'],'commit':cur['commit'],'config_changed':bool(config_changed),'unmodeled_interface_invalidations':unmodeled_invalidations,
                            'built_modules':sorted(built),'dependent_rebuilt_modules':sorted(dep),'cutoff_avoidable_modules':sorted(cut),**vals})
        previous=cur
    total=sums['rebuilt_kernel_ns'];bc=sums['build_cpu_seconds'];be=sums['module_elapsed_seconds']
    bykind={k:bucket([g for g in reuse if g['kind']==k],total,bc,be) for k in sorted({g['kind'] for g in reuse})}
    cutkind={k:bucket([g for g in cutgroups if g['kind']==k],total,bc,be) for k in sorted({g['kind'] for g in cutgroups})}
    mt=[]
    for mod,v in module_stats.items():
        mt.append({'module':mod,**dict(v),'kernel_reuse_examples':examples(module_reuse[mod]),
                   'cutoff_examples':examples(module_cutexamples[mod])})
    top_reuse=sorted(mt,key=lambda x:-x.get('optimistic_reusable_kernel_seconds',0))[:20]
    top_cut=sorted(mt,key=lambda x:-x.get('cutoff_avoidable_elapsed_seconds',0))[:20]
    result={**overview,'status':'measured','interpretation':'DIAGNOSTIC ONLY; declaration reuse is an OPTIMISTIC UPPER BOUND',
      'denominators':'C2..C20 only; primary kernel figures include declarations in modules actually rebuilt by Lake. C1 is a cold baseline. Standard-library kernel time is excluded from FV avoidance shares.',
      'sums':dict(sums),'module_cutoff':{
        'share_of_dependent_module_rebuild_elapsed':frac(sums['cutoff_avoidable_elapsed_seconds'],sums['dependent_rebuild_elapsed_seconds']),
        'share_of_total_module_build_elapsed':frac(sums['cutoff_avoidable_elapsed_seconds'],be),
        'share_of_total_build_cpu':frac(sums['cutoff_avoidable_build_cpu_seconds'],bc),
        'elapsed_work_over_total_build_wall':frac(sums['cutoff_avoidable_elapsed_seconds'],sums['build_wall_seconds']),
        'share_of_rebuilt_kernel_cpu':frac(sums['cutoff_kernel_ns'],total)},
      'optimistic_kernel_reuse':{**bucket(reuse,total,bc,be),
          'kernel_cpu_over_total_build_wall':frac(sums['optimistic_reusable_kernel_ns']/1e9,sums['build_wall_seconds'])},
      'all_cone_revisit_diagnostic':{'kernel_seconds':all_cone_total/1e9,'optimistically_reusable_seconds':sum(g['cpu_ns'] for g in all_cone_reuse)/1e9,
          'share':frac(sum(g['cpu_ns'] for g in all_cone_reuse),all_cone_total),
          'note':'Includes modules Lake did not rebuild; not incremental build savings.'},
      'kernel_reuse_by_kind':bykind,'cutoff_kernel_by_kind':cutkind,'top_20_kernel_reuse_modules':top_reuse,
      'top_20_module_cutoff_modules':top_cut,'all_module_buckets':mt,'transitions':transitions,
      'replay_by_commit':[{'commit':c['commit'],**c['replay'],**c['coverage']} for c in allc]}
    (RESULTS/'research/B2c.json').write_text(json.dumps(result,indent=2)+'\n')
    def pct(x):return 'n/a' if x is None else f'{100*x:.2f}%'
    def sec(x):return f'{x:,.3f}'
    def extext(xs):return '; '.join(f"`{x['name']}` ({x['commit'][:8]}, {x['kernel_ms']:.3f} ms)" for x in xs) or 'none'
    p=['# B2c: elaborated-interface cutoff and optimistic kernel reuse','',
       f"Across 19 incremental transitions, module cutoff could avoid **{pct(result['module_cutoff']['share_of_dependent_module_rebuild_elapsed'])}** of dependent-module rebuild seconds ({sec(sums['cutoff_avoidable_elapsed_seconds'])} / {sec(sums['dependent_rebuild_elapsed_seconds'])} s). Declaration reuse could optimistically avoid **{pct(result['optimistic_kernel_reuse']['share_of_rebuilt_kernel'])}** of measured kernel CPU in actually rebuilt modules.",'',
       '**DIAGNOSTIC ONLY. Declaration reuse is an OPTIMISTIC UPPER BOUND, not a sound cache design.** The key omits `LEAN_NAT_MAX_SIZE`, module-mode `Lean.reduceBool` axiom information, unit-like eta dependencies through constructor field counts, and implicit Bool/Nat dependencies. No optimization is implemented.','',
       '## Scope and denominators','',
       'The 20 first-parent commits end at `5018b95`; C1 is `62fa93f0`. This uses only the import cone of `FV.Backend.Proof.{DefGenTab,IselSzTab,IselCtlTry}` and `FV.Opt.Proof.RuleArith`, not all FV. C1 is a cold baseline and is excluded from transition shares. Primary savings count only modules Lake actually rebuilt in C2–C20. Full-cone replays also check unchanged modules, but those are not credited as incremental savings.','',
       '| Measure | Seconds | Share |','|---|---:|---:|',
       f"| Dependent-module cutoff / dependent rebuild elapsed | {sec(sums['cutoff_avoidable_elapsed_seconds'])} | {pct(result['module_cutoff']['share_of_dependent_module_rebuild_elapsed'])} |",
       f"| Module cutoff / total module build elapsed | {sec(sums['cutoff_avoidable_elapsed_seconds'])} | {pct(result['module_cutoff']['share_of_total_module_build_elapsed'])} |",
       f"| Module cutoff elapsed work / total build wall | {sec(sums['cutoff_avoidable_elapsed_seconds'])} | {pct(result['module_cutoff']['elapsed_work_over_total_build_wall'])} |",
       f"| Module cutoff / total build CPU | {sec(sums['cutoff_avoidable_build_cpu_seconds'])} | {pct(result['module_cutoff']['share_of_total_build_cpu'])} |",
       f"| Kernel in cutoff-skippable modules / rebuilt kernel CPU | {sec(sums['cutoff_kernel_ns']/1e9)} | {pct(result['module_cutoff']['share_of_rebuilt_kernel_cpu'])} |",
       f"| Optimistic declaration reuse / rebuilt kernel CPU | {sec(sums['optimistic_reusable_kernel_ns']/1e9)} | {pct(result['optimistic_kernel_reuse']['share_of_rebuilt_kernel'])} |",
       f"| Optimistic declaration CPU work / total build wall | {sec(sums['optimistic_reusable_kernel_ns']/1e9)} | {pct(result['optimistic_kernel_reuse']['kernel_cpu_over_total_build_wall'])} |",
       f"| Optimistic declaration reuse / total build CPU | {sec(sums['optimistic_reusable_kernel_ns']/1e9)} | {pct(result['optimistic_kernel_reuse']['share_of_build_cpu'])} |",'',
       f"Denominators: {sec(total/1e9)} s rebuilt-module kernel CPU; {sec(bc)} s module build CPU; {sec(be)} s summed module build elapsed; {sec(sums['build_wall_seconds'])} s total build wall. Summed concurrent module elapsed is work, not critical-path wall speedup. CPU shares use CPU in both numerator and denominator. CPU-work/build-wall ratios are normalization figures, not predicted wall speedups. The two avoidance mechanisms overlap and must not be added.",'',
       '## Method and checks','',
       'Lean v4.34.1 (`5045d0056413266e57c625dcd7c365b10e377c52`) extracts explicit tagged expression DAGs, structured names, ordered level parameters, and complete ConstantInfo metadata. The companion hashes canonical UTF-8 JSON with SHA-256 and collapses interface dependency SCCs. Theorem IF omits the proof; all other kinds include values, safety, hints, and inductive metadata. K includes the proof and dependency IFs. Module IF is the sorted multiset of constant IFs. FV uses legacy modules, whose stored constants are available to importers, including private kernel names.','',
       'A custom driver calls `Lean.Kernel.Environment.addDecl` in module import order, with dependency order within modules. Unsafe/partial recursive definitions use mutual kernel groups, including singleton recursion. Inductives are replayed as groups; generated constructors/recursors are compared with the stored metadata. Duplicate theorem bodies are rechecked under a fresh name rather than skipped. Every stored constant must map to a replayed group. Native `CLOCK_PROCESS_CPUTIME_ID` readings surround each kernel call; imports, reconstruction, traversal, output, and timers remain in separately reported overhead. All commits satisfy summed kernel CPU ≤ total replay CPU.','',
       'The three required fixtures pass, along with SCC propagation, row-order independence, and missing-dependency rejection. `Init.Prelude` replay covers 2,324 constants with 2,033 kernel calls; full `Init` validation covers 64,849 calls.','',
       '`LEAN_NUM_THREADS=4`, `FV_MEMCAP=16G`. Lake v4.34.1 rejects `-j4`; an isolated shim accepts it and enforces at most four active Lean module builds with file locks. The first cold build exceeded 16 GiB and was killed; its failed-attempt data is retained, and subsequent builds serialize module processes. The shim also passes `-j4` directly to Lean. C1 is excluded from all transition ratios. All builds run through `scripts/memcap.sh`. Module timers exclude semaphore waiting and include Lean elaboration/code generation. Artifact-cache restore is disabled. Shared toolchain files are unchanged.','',
       'Counterfactual cutoff propagates a rebuild only through imports whose elaborated IF changed, while preserving local source invalidations. Modules whose observed IF changed are never credited as avoidable; unexplained IF changes are recorded as additional invalidations. Any lakefile/manifest/toolchain change conservatively invalidates every module. Unchanged-source rebuilt modules form the dependent-rebuild denominator. Attribute/tactic/environment effects outside the requested constant interface are not modeled; this is not a proof that such a cutoff is safe for elaboration.','',
       '## Kernel reuse by kind (optimistic)','',
       '| Kind | Reusable kernel seconds | Share of kernel | Share of build CPU |','|---|---:|---:|---:|']
    for k,v in bykind.items():p.append(f"| {k} | {sec(v['kernel_seconds'])} | {pct(v['share_of_rebuilt_kernel'])} | {pct(v['share_of_build_cpu'])} |")
    p+=['']
    for k,v in bykind.items():p += [f"{k}: {extext(v['examples'])}.",'']
    p+=['## Kernel inside cutoff-skippable modules, by kind','',
         'Module build seconds cannot be apportioned to declaration kinds without inventing an allocation. The kind split below uses measured kernel CPU within modules the cutoff would skip.','',
         '| Kind | Kernel seconds | Share of rebuilt kernel |','|---|---:|---:|']
    for k,v in cutkind.items():p.append(f"| {k} | {sec(v['kernel_seconds'])} | {pct(v['share_of_rebuilt_kernel'])} |")
    p+=['']
    for k,v in cutkind.items():p += [f"{k}: {extext(v['examples'])}.",'']
    for title,items,key in [('Top 20 modules: optimistic kernel reuse',top_reuse,'optimistic_reusable_kernel_seconds'),
                            ('Top 20 modules: module cutoff',top_cut,'cutoff_avoidable_elapsed_seconds')]:
        p+=['## '+title,'','| Module | Avoidable seconds |','|---|---:|']
        for v in items:p.append(f"| `{v['module']}` | {sec(v.get(key,0))} |")
        p+=['']
        for v in items:
            if v.get(key,0)>0:
                xs=v['kernel_reuse_examples' if key.startswith('optimistic') else 'cutoff_examples']
                p += [f"`{v['module']}`: {extext(xs)}.",'']
    p+=['## Commit transitions','','| Commit | Built modules | Cutoff seconds | Optimistic reusable kernel seconds |','|---|---:|---:|---:|']
    for t in transitions:p.append(f"| `{t['commit'][:8]}` | {len(t['built_modules'])} | {sec(t['cutoff_avoidable_elapsed_seconds'])} | {sec(t['optimistic_reusable_kernel_ns']/1e9)} |")
    p+=['','## Artifacts and limits','',
         '`B2c.json` contains denominators, all module buckets, transitions, replay totals, and key-bearing examples. `b2c_data/<commit>/rows.jsonl.gz` stores name/kind/module/IF/K/kernel_ms, with group times charged once to the representative. `kernel_groups.jsonl.gz` retains every measured call; repeated K values retain their occurrence times. `replay.jsonl.gz`, source hashes, build logs, per-module CPU/elapsed timings, and coverage checks preserve the evidence. Each completed commit was pushed to `research/b2c-measurement` before advancing; no PR was opened.','',
         'Shared-host timing noise, interpreter/reconstruction overhead, and changed parallel scheduling limit wall-speedup inference. The report estimates avoidable work, not an implemented end-to-end speedup. Kernel times are replay measurements, not profiler samples of the original elaboration.']
    shortfalls=[]
    for label,bs in [('reuse kind',bykind),('cutoff kind',cutkind)]:
        for k,v in bs.items():
            if v['nonauxiliary_example_shortfall']:shortfalls.append(f'{label} {k}')
    for title,items,key in [('reuse module',top_reuse,'optimistic_reusable_kernel_seconds'),('cutoff module',top_cut,'cutoff_avoidable_elapsed_seconds')]:
        for v in items:
            if v.get(key,0)>0 and len(v['kernel_reuse_examples' if title.startswith('reuse') else 'cutoff_examples'])<3:
                shortfalls.append(title+' '+v['module'])
    result['example_shortfalls']=shortfalls
    (RESULTS/'research/B2c.json').write_text(json.dumps(result,indent=2)+'\n')
    if shortfalls:p+=['','Example coverage is incomplete for these nonzero buckets: '+', '.join(shortfalls)+'.']
    (RESULTS/'research/B2c.md').write_text('\n'.join(p)+'\n')
    print(json.dumps({'status':'analyzed','example_shortfalls':shortfalls,'transitions':len(transitions)}))
if __name__=='__main__':main()
