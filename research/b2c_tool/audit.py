#!/usr/bin/env python3
"""Read-only completion gates against stored builds, rows, replay, and Git history.

Run after report.py and the final research-only commit/push. This complements
manual inspection of key construction and the requested non-auxiliary examples;
it is not a soundness proof for the deliberately incomplete reuse key.
"""
import argparse, collections, gzip, hashlib, json, pathlib, re, statistics, subprocess
from run_experiment import CLIFV, DATA, RESULTS, TARGETS, H
from report import nonaux, frac
BASE='d6f9243a9e2148709875a2020622c95b0d9d2ccc'

def j(p):return json.loads(p.read_text())
def gz(p):
    with gzip.open(p,'rt') as f:
        for line in f:yield json.loads(line)
def git(args,cwd=RESULTS):return subprocess.check_output(['git',*args],cwd=cwd,text=True).strip()
def callkey(g):return (g['module'],tuple(g['names']),g['kind'],g['cpu_ns'],g['duplicate_rechecked'])
def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--commit',help='audit one complete pushed dataset by commit prefix; does not certify the final report')
    args=parser.parse_args()
    report=j(RESULTS/'research/B2c.json');md=(RESULTS/'research/B2c.md').read_text()
    commits=git(['rev-list','--first-parent','-n','20','--reverse','5018b95'],CLIFV).splitlines()
    assert len(commits)==20 and report['commits']==commits
    selected=[c for c in commits if args.commit is None or c.startswith(args.commit)]
    if args.commit:
        assert len(selected)==1,'commit prefix must select exactly one experiment commit'
    else:
        assert report['completed_commits']==commits and report['status']=='measured'
        assert not report['example_shortfalls']
    assert 'OPTIMISTIC UPPER BOUND' in md
    for missing in ('LEAN_NAT_MAX_SIZE','Lean.reduceBool','constructor field counts','Bool/Nat'):
        assert missing in md
    previous_keys=set();previous_sources={};previous_interfaces={}
    previous_push=None;observed=[];example_index={}
    sums=collections.Counter();module_work=collections.defaultdict(collections.Counter)
    kind_work={'reuse':collections.Counter(),'cutoff':collections.Counter()}
    eligible_examples={'reuse':set(),'cutoff':set()}
    cone_total=cone_reused=0
    for i,c in enumerate(commits):
        if c not in selected:continue
        d=DATA/c[:8];complete=j(d/'complete.json');pushed=j(d/'pushed.json')
        assert complete['commit']==c and complete['index']==i+1 and complete['targets']==TARGETS
        assert previous_push is None or complete['completed_unix']>=previous_push
        previous_push=pushed['pushed_unix']
        assert json.loads(git(['show',f"{pushed['results_commit']}:research/b2c_data/{c[:8]}/complete.json"]))['commit']==c
        subprocess.run(['git','merge-base','--is-ancestor',pushed['results_commit'],'HEAD'],cwd=RESULTS,check=True)
        build=j(d/'build.json');coverage=j(d/'coverage.json');total=j(d/'replay_total.json')
        assert build['exit_code']==0 and total['cpu_clock']=='CLOCK_PROCESS_CPUTIME_ID'
        assert total['cpu_scope']=='process startup through end of replay main'
        assert total['startup_cpu_ns']+total['replay_main_cpu_ns']==total['cpu_ns']
        assert total['kernel_cpu_ns']<=total['replay_main_cpu_ns']<=total['cpu_ns']
        assert total['kernel_cpu_ns']+total['overhead_cpu_ns']==total['cpu_ns']
        assert total['sum_le_total_cpu'] and coverage['all_constants_covered']
        assert 'Build completed successfully' in (d/'build.log').read_text()
        for b in build['modules']:assert b['exit_code']==0 and b['seconds']>=0 and b['cpu_seconds']>=0
        assert abs(sum(b['seconds'] for b in build['modules'])-build['module_elapsed_seconds'])<1e-6
        assert abs(sum(b['cpu_seconds'] for b in build['modules'])-build['module_cpu_seconds'])<1e-6
        modules=j(d/'rows.jsonl.gz.modules.json');mi={m['module']:m for m in modules}
        assert len(mi)==len(modules) and set(TARGETS)<=set(mi)
        # Full ConstantInfo rows represent exported legacy FV module contents.
        assert all(not m['is_module'] for m in modules if m['module'].startswith('FV.'))
        reach=set();todo=TARGETS[:]
        while todo:
            name=todo.pop()
            if name in reach:continue
            assert name in mi;reach.add(name);todo.extend(mi[name]['imports'])
        assert {m for m in mi if m.startswith('FV.')}=={m for m in reach if m.startswith('FV.')}
        if i==0:
            # The capped cold attempt and successful retry partition the cone.
            # The original wrapper encoded absolute paths in its module field.
            attempts=[]
            for p in (d/'attempt_1/build_modules.jsonl',d/'build_modules.jsonl'):
                rs=[json.loads(line) for line in p.read_text().splitlines()]
                assert all(r['exit_code']==0 for r in rs)
                names=[]
                for r in rs:
                    parts=pathlib.Path(r['source']).with_suffix('').parts
                    names.append('.'.join(parts[parts.index('FV'):]))
                assert len(names)==len(set(names));attempts.append(set(names))
            assert not attempts[0]&attempts[1]
            assert attempts[0]|attempts[1]=={m for m in mi if m.startswith('FV.')}
            baseline=j(d/'baseline_build_coverage.json')
            assert set(baseline['module_names'])==attempts[0]|attempts[1]
            assert baseline['total_successfully_timed_FV_modules']==len(attempts[0]|attempts[1])
        rows=list(gz(d/'rows.jsonl.gz'));byrow={};rowcounts=collections.Counter()
        for r in rows:
            assert r['serialization']=='Expr-v3-retained-nodes'
            assert r['interface_graph']=='IF-v2-canonical-lookups'
            ident=(r['module'],r['name']);assert ident not in byrow;byrow[ident]=r;rowcounts[r['module']]+=1
            for field in ('IF','K','constant_K'):assert re.fullmatch('[0-9a-f]{64}',r[field])
        assert len(rows)==coverage['rows']==sum(m['count'] for m in modules)
        if (d/'hash_validation.json').exists():
            logical=sorted((r['module'],r['name'],r['IF'],r['constant_K'],r['kind']) for r in rows)
            assert H(['b2c-logical-constant-rows-v1',logical])==j(d/'hash_validation.json')['constant_rows_digest']
        own_IFs=collections.defaultdict(list)
        for r in rows:own_IFs[r['module']].append(r['IF'])
        interfaces={m:H(['module-interface-multiset-v1',sorted(own_IFs[m])]) for m in mi}
        sources=j(d/'sources.json')
        resolution=j(d/'rows.jsonl.gz.name_resolution.json')
        assert resolution['interface_graph']=='IF-v2-canonical-lookups'
        assert resolution['constants_scanned']==len(rows) and resolution['modules_scanned']==len(modules)
        assert resolution['duplicate_names']==resolution['imported_bindings_verified']
        noncanonical={r['name'] for r in rows if not r['matches_imported_IF_input']}
        assert noncanonical==set(resolution['different_IF_input_names'])
        canonical_IFs={}
        for r in rows:
            if r['matches_imported_IF_input']:
                assert canonical_IFs.setdefault(r['name'],r['IF'])==r['IF']
        for name,mod in resolution['different_IF_input_names'].items():
            assert byrow[mod,name]['matches_imported_IF_input']
        assert all(rowcounts[m['module']]==m['count'] for m in modules)
        groups=list(gz(d/'kernel_groups.jsonl.gz'));bygroup={};keytimes=collections.defaultdict(list)
        for g in groups:
            key=H(['kernel-group-v1',sorted((n,byrow[g['module'],n]['constant_K']) for n in g['names'])])
            assert key==g['K'];keytimes[key].append(g['cpu_ns'])
            for name in g['names']:bygroup[g['module'],name]=g
            if g['module'].startswith('FV.'):
                for name in g['names']:example_index[c,g['module'],name]=g
        for r in rows:
            candidates=[bygroup[r['module'],n] for n in r['group_names'] if (r['module'],n) in bygroup]
            assert candidates and all(g['K']==r['K'] for g in candidates)
            g=candidates[0]
            expected=g['cpu_ns']/1e6 if r['name']==g['names'][0] else 0
            assert r['kernel_ms']==expected
        assert abs(sum(r['kernel_ms'] for r in rows)*1e6-total['kernel_cpu_ns'])<10
        replay=collections.Counter();module_replay={};rawtotal=None
        for r in gz(d/'replay.jsonl.gz'):
            if r['event']=='kernel':replay[callkey(r)]+=1
            elif r['event']=='module_replay':module_replay[r['module']]=r
            elif r['event']=='total':rawtotal=r
        assert replay==collections.Counter(callkey(g) for g in groups) and rawtotal==total
        assert set(module_replay)==set(mi)
        assert all(module_replay[m]['constants']==mi[m]['count'] for m in mi)
        module_ns=collections.Counter();module_calls=collections.Counter()
        for g in groups:module_ns[g['module']]+=g['cpu_ns'];module_calls[g['module']]+=1
        for m,r in module_replay.items():
            assert r['kernel_cpu_ns']==module_ns[m]<=r['cpu_ns']
            assert r['calls']==module_calls[m]
        assert sum(r['cpu_ns'] for r in module_replay.values())<=total['replay_main_cpu_ns']
        assert sum(g['cpu_ns'] for g in groups)==total['kernel_cpu_ns']==coverage['kernel_cpu_ns']
        assert len(groups)==coverage['kernel_calls'] and len(keytimes)==coverage['distinct_K']
        assert sum(g['duplicate_rechecked'] for g in groups)==coverage['duplicate_theorems_rechecked']
        kt=list(gz(d/'kernel_by_K.jsonl.gz'))
        assert len(kt)==len(keytimes) and len({t['K'] for t in kt})==len(kt)
        for t in kt:
            assert t['occurrences']==len(keytimes[t['K']])
            assert abs(t['total_kernel_ms']-sum(keytimes[t['K']])/1e6)<1e-6
            times=[ns/1e6 for ns in keytimes[t['K']]]
            assert t['kernel_ms']==statistics.median(times)
            assert t['mean_kernel_ms']==statistics.mean(times)
            assert t['min_kernel_ms']==min(times) and t['max_kernel_ms']==max(times)
        built={b['module'] for b in build['modules']}
        rebuilt=[g for g in groups if g['module'] in built and g['module'].startswith('FV.')]
        reused=[g for g in rebuilt if g['kind'] not in ('inductive','quotient') and g['K'] in previous_keys]
        if i and not args.commit:
            t=report['transitions'][i-1]
            assert t['commit']==c and set(t['built_modules'])==built
            changed_config=any(subprocess.check_output(['git','diff',commits[i-1],c,'--',p],cwd=CLIFV)
                               for p in ('lakefile.toml','lake-manifest.json','lean-toolchain'))
            dependent={m for m in built if sources.get(m)==previous_sources.get(m)}
            cut={m for m in dependent if not changed_config and interfaces[m]==previous_interfaces.get(m)
                 and all(interfaces.get(imp)==previous_interfaces.get(imp) for imp in mi[m]['imports'])}
            assert t['config_changed']==bool(changed_config)
            assert set(t['dependent_rebuilt_modules'])==dependent
            assert set(t['cutoff_avoidable_modules'])==cut
            bm={b['module']:b for b in build['modules']}
            for field,expected in (
                ('dependent_rebuild_elapsed_seconds',sum(bm[m]['seconds'] for m in dependent)),
                ('cutoff_avoidable_elapsed_seconds',sum(bm[m]['seconds'] for m in cut)),
                ('cutoff_avoidable_build_cpu_seconds',sum(bm[m]['cpu_seconds'] for m in cut))):
                assert abs(t[field]-expected)<1e-6,(c,field)
            assert t['build_cpu_seconds']==build['tree_cpu_seconds']
            assert t['module_build_cpu_seconds']==build['module_cpu_seconds']
            assert t['build_wall_seconds']==build['wall_seconds']
            assert t['rebuilt_kernel_ns']==sum(g['cpu_ns'] for g in rebuilt)
            assert t['optimistic_reusable_kernel_ns']==sum(g['cpu_ns'] for g in reused)
            assert t['cutoff_kernel_ns']==sum(g['cpu_ns'] for g in rebuilt if g['module'] in cut)
            for field in ('dependent_rebuild_elapsed_seconds','cutoff_avoidable_elapsed_seconds',
                          'cutoff_avoidable_build_cpu_seconds','rebuilt_kernel_ns',
                          'optimistic_reusable_kernel_ns','cutoff_kernel_ns'):
                sums[field]+=t[field]  # Each transition value was independently checked above.
            for field,build_field in (('build_cpu_seconds','tree_cpu_seconds'),
                                     ('module_build_cpu_seconds','module_cpu_seconds'),
                                     ('module_elapsed_seconds','module_elapsed_seconds'),
                                     ('build_wall_seconds','wall_seconds')):
                sums[field]+=build[build_field]
            for b in build['modules']:
                m=b['module'];v=module_work[m]
                v['build_elapsed_seconds']+=b['seconds'];v['build_cpu_seconds']+=b['cpu_seconds']
                v['rebuilt_transitions']+=1
                if m in dependent:v['dependent_rebuild_elapsed_seconds']+=b['seconds']
                if m in cut:
                    v['cutoff_avoidable_elapsed_seconds']+=b['seconds']
                    v['cutoff_avoidable_build_cpu_seconds']+=b['cpu_seconds']
            for g in rebuilt:module_work[g['module']]['kernel_seconds']+=g['cpu_ns']/1e9
            for label,gs,field in (('reuse',reused,'optimistic_reusable_kernel_seconds'),
                                   ('cutoff',[g for g in rebuilt if g['module'] in cut],'cutoff_kernel_seconds')):
                for g in gs:
                    module_work[g['module']][field]+=g['cpu_ns']/1e9
                    kind_work[label][g['kind']]+=g['cpu_ns']
                    eligible_examples[label].update((c,g['module'],n) for n in g['names'])
            cone=[g for g in groups if g['module'].startswith('FV.')]
            cone_total+=sum(g['cpu_ns'] for g in cone)
            cone_reused+=sum(g['cpu_ns'] for g in cone if g['kind'] not in ('inductive','quotient') and g['K'] in previous_keys)
        observed.append({'commit':c,'rows':len(rows),'calls':len(groups),'distinct_K':len(keytimes),
                         'kernel_cpu_ns':total['kernel_cpu_ns'],'total_cpu_ns':total['cpu_ns']})
        previous_keys=set(keytimes)
        previous_sources=sources;previous_interfaces=interfaces
    def close(actual,expected):
        if expected is None:assert actual is None
        else:assert abs(actual-expected)<=max(1e-6,abs(expected)*1e-12),(actual,expected)
    def examples(xs,positive,label,kind=None,module=None):
        if not positive:return
        assert len({x['name'] for x in xs})>=3
        for x in xs:
            assert nonaux(x['name'])
            assert (x['commit'],x['module'],x['name']) in eligible_examples[label]
            g=example_index[x['commit'],x['module'],x['name']]
            assert g['K']==x['K'] and x['kernel_ms']==g['cpu_ns']/1e6
            assert kind is None or g['kind']==kind
            assert module is None or g['module']==module
    if not args.commit:
        assert set(report['sums'])==set(sums)
        for field,value in sums.items():close(report['sums'][field],value)
        kernel=sums['rebuilt_kernel_ns'];cpu=sums['build_cpu_seconds'];elapsed=sums['module_elapsed_seconds']
        for label,bs in (('reuse',report['kernel_reuse_by_kind']),('cutoff',report['cutoff_kernel_by_kind'])):
            assert set(bs)==set(kind_work[label])
            for kind,v in bs.items():
                ns=kind_work[label][kind]
                close(v['kernel_seconds'],ns/1e9)
                close(v['share_of_rebuilt_kernel'],frac(ns,kernel))
                close(v['share_of_build_cpu'],frac(ns/1e9,cpu))
                close(v['share_of_summed_module_elapsed'],frac(ns/1e9,elapsed))
                examples(v['examples'],ns>0,label,kind=kind)
        actual_modules={v['module']:v for v in report['all_module_buckets']}
        assert len(actual_modules)==len(report['all_module_buckets']) and set(actual_modules)==set(module_work)
        for m,v in module_work.items():
            actual=actual_modules[m]
            for field,value in v.items():close(actual[field],value)
            for field,expected in (
                ('kernel_reuse_share_of_rebuilt_kernel',frac(v['optimistic_reusable_kernel_seconds'],kernel/1e9)),
                ('kernel_reuse_share_of_total_build_cpu',frac(v['optimistic_reusable_kernel_seconds'],cpu)),
                ('cutoff_share_of_dependent_rebuild_elapsed',frac(v['cutoff_avoidable_elapsed_seconds'],sums['dependent_rebuild_elapsed_seconds'])),
                ('cutoff_share_of_total_build_cpu',frac(v['cutoff_avoidable_build_cpu_seconds'],cpu)),
                ('cutoff_share_of_rebuilt_kernel',frac(v['cutoff_kernel_seconds'],kernel/1e9))):
                close(actual[field],expected)
        for field,expected in (
            ('share_of_dependent_module_rebuild_elapsed',frac(sums['cutoff_avoidable_elapsed_seconds'],sums['dependent_rebuild_elapsed_seconds'])),
            ('share_of_total_module_build_elapsed',frac(sums['cutoff_avoidable_elapsed_seconds'],elapsed)),
            ('share_of_total_build_cpu',frac(sums['cutoff_avoidable_build_cpu_seconds'],cpu)),
            ('elapsed_work_over_total_build_wall',frac(sums['cutoff_avoidable_elapsed_seconds'],sums['build_wall_seconds'])),
            ('share_of_rebuilt_kernel_cpu',frac(sums['cutoff_kernel_ns'],kernel))):
            close(report['module_cutoff'][field],expected)
        reuse=report['optimistic_kernel_reuse'];ns=sums['optimistic_reusable_kernel_ns']
        for field,expected in (('kernel_seconds',ns/1e9),('share_of_rebuilt_kernel',frac(ns,kernel)),
                               ('share_of_build_cpu',frac(ns/1e9,cpu)),
                               ('share_of_summed_module_elapsed',frac(ns/1e9,elapsed)),
                               ('kernel_cpu_over_total_build_wall',frac(ns/1e9,sums['build_wall_seconds']))):
            close(reuse[field],expected)
        examples(reuse['examples'],ns>0,'reuse')
        cone=report['all_cone_revisit_diagnostic']
        close(cone['kernel_seconds'],cone_total/1e9);close(cone['optimistically_reusable_seconds'],cone_reused/1e9)
        close(cone['share'],frac(cone_reused,cone_total))
        for table,metric in (('top_20_kernel_reuse_modules','optimistic_reusable_kernel_seconds'),
                             ('top_20_module_cutoff_modules','cutoff_avoidable_elapsed_seconds')):
            expected=sorted(module_work,key=lambda m:-module_work[m][metric])[:20]
            assert [v['module'] for v in report[table]]==expected
            assert all(v==actual_modules[v['module']] for v in report[table])
        for v in report['top_20_kernel_reuse_modules']:
            examples(v['kernel_reuse_examples'],v.get('optimistic_reusable_kernel_seconds',0)>0,'reuse',module=v['module'])
        for v in report['top_20_module_cutoff_modules']:
            examples(v['cutoff_examples'],v.get('cutoff_avoidable_elapsed_seconds',0)>0,'cutoff',module=v['module'])
    assert git(['branch','--show-current'])=='research/b2c-measurement'
    assert all(p.startswith('research/') for p in git(['diff','--name-only',BASE,'HEAD']).splitlines())
    assert git(['rev-parse','HEAD'])==git(['rev-parse','origin/research/b2c-measurement'])
    print(json.dumps({'artifact_audit':'passed','scope':'single dataset' if args.commit else 'final report and all datasets',
                     'commits':observed,'manual_example_and_method_review_still_required':True},indent=2))
if __name__=='__main__':main()
