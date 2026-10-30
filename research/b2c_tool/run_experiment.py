#!/usr/bin/env python3
"""Sequential, checkpointed twenty-commit experiment; stops on any failed step.

Run after sourcing env.sh and setup_build.sh. Completed commit data is signed and
pushed before advancing. Never creates a PR or changes files outside research/ in
the results repository. A failed build can be resumed with --retry-build.
"""
import argparse, gzip, hashlib, json, os, pathlib, resource, subprocess, sys, time
TOOL=pathlib.Path(__file__).resolve().parent
RESULTS=TOOL.parents[1]
ROOT=RESULTS.parent
CLIFV=ROOT/'clifv'
DATA=RESULTS/'research/b2c_data'
TARGETS=['FV.Backend.Proof.DefGenTab','FV.Backend.Proof.IselSzTab','FV.Backend.Proof.IselCtlTry','FV.Opt.Proof.RuleArith']
WORK=ROOT/'.b2c-work'

def command(args,cwd=CLIFV,**kwargs):
    print(time.strftime('%FT%TZ',time.gmtime()), 'RUN', ' '.join(map(str,args)),flush=True)
    return subprocess.run(list(map(str,args)),cwd=cwd,check=True,**kwargs)

def write(p,x):
    p.write_text(json.dumps(x,indent=2)+'\n')

def capture(args):
    return subprocess.check_output(args,cwd=CLIFV,text=True).strip()

def sources():
    return {str(p.relative_to(CLIFV)).removesuffix('.lean').replace('/','.'):
            hashlib.sha256(p.read_bytes()).hexdigest() for p in (CLIFV/'FV').rglob('*.lean')}

def normalize_build(p):
    rows=[]
    if p.exists():
        for line in p.read_text().splitlines():
            r=json.loads(line); source=pathlib.Path(r['source'])
            if source.is_absolute(): source=source.relative_to(CLIFV)
            r['module']=str(source).removesuffix('.lean').replace('/','.')
            rows.append(r)
    return rows

def measure_build(d):
    log=d/'build_modules.jsonl'
    os.environ['B2C_BUILD_LOG']=str(log)
    os.environ['FV_MEMCAP_STATS']=str(d/'build.mem')
    before=resource.getrusage(resource.RUSAGE_CHILDREN); start=time.monotonic()
    with open(d/'build.log','w') as f:
        result=subprocess.run(['scripts/memcap.sh','lake','-j4','build',*TARGETS],cwd=CLIFV,stdout=f,stderr=subprocess.STDOUT)
    after=resource.getrusage(resource.RUSAGE_CHILDREN)
    rows=normalize_build(log)
    meta={'wall_seconds':time.monotonic()-start,'tree_cpu_seconds':after.ru_utime+after.ru_stime-before.ru_utime-before.ru_stime,
          'exit_code':result.returncode,'max_active_builds':int(os.environ.get('B2C_MAX_ACTIVE','4')),'module_elapsed_seconds':sum(r['seconds'] for r in rows),
          'module_cpu_seconds':sum(r['cpu_seconds'] for r in rows),'modules':rows,
          'command':['scripts/memcap.sh','lake','-j4','build',*TARGETS]}
    write(d/'build.json',meta)
    if result.returncode: raise RuntimeError(f'build failed: {d}, rc={result.returncode}')
    assert all(r['exit_code']==0 for r in rows)

def attach_baseline(d,pid):
    proc=pathlib.Path(f'/proc/{pid}')
    assert (proc/'comm').read_text().strip()=='lake','baseline process identity mismatch'
    start=int((proc/'stat').read_text().split()[21])/os.sysconf('SC_CLK_TCK')
    write(d/'attached.json',{'pid':pid,'start_monotonic':start,'attached_unix':time.time()})
    while proc.exists():
        print(time.strftime('%FT%TZ',time.gmtime()),f'waiting for baseline lake pid {pid}',flush=True)
        time.sleep(30)
    text=(d/'build.log').read_text()
    if 'Build completed successfully' not in text:
        raise RuntimeError('baseline ended without authoritative success line; inspect original session')
    rows=normalize_build(d/'build_modules.jsonl')
    assert rows and all(r['exit_code']==0 for r in rows)
    write(d/'build.json',{'wall_seconds':time.monotonic()-start,'wall_measurement':'process start tick to first observation of process exit; ≤30s polling overestimate; baseline excluded from transition denominators',
       'exit_code':0,'module_elapsed_seconds':sum(r['seconds'] for r in rows),'module_cpu_seconds':sum(r['cpu_seconds'] for r in rows),
       'modules':rows,'command':['scripts/memcap.sh','lake','-j4','build',*TARGETS]})

def extract_and_replay(d):
    os.environ.pop('B2C_BUILD_LOG',None); os.environ.pop('FV_MEMCAP_STATS',None)
    raw=WORK/'raw.jsonl'; WORK.mkdir(exist_ok=True)
    with open(raw,'w') as f, open(d/'extract.stderr','w') as e:
        command(['scripts/memcap.sh','lake','env','lean','--run',TOOL/'Extract.lean',*TARGETS],stdout=f,stderr=e)
    with open(d/'hash.log','w') as f:
        command(['scripts/memcap.sh','python3',TOOL/'hash_rows.py',raw,d/'rows.jsonl.gz'],stdout=f,stderr=subprocess.STDOUT)
    raw.unlink()
    replay_raw=WORK/'replay.jsonl'
    with open(replay_raw,'w') as f, open(d/'replay.stderr','w') as e:
        command(['scripts/memcap.sh','lake','env','lean',f'--load-dynlib={ROOT/".b2c-clock.so"}',
                 '--run',TOOL/'Replay.lean',*TARGETS],stdout=f,stderr=e)
    lines=replay_raw.read_text().splitlines()
    total=json.loads(lines[-1]); assert total['event']=='total' and total['sum_le_total_cpu']
    assert total['kernel_cpu_ns'] <= total['cpu_ns']
    write(d/'replay_total.json',total)
    with gzip.open(d/'replay.jsonl.gz','wt',compresslevel=6) as f:
        for line in lines:f.write(line+'\n')
    replay_raw.unlink()
    merge_rows(d)

def merge_rows(d):
    # Every stored constant must be covered by a measured kernel group, including
    # constructors/recursors generated by inductive declarations.
    with gzip.open(d/'rows.jsonl.gz','rt') as f: rows=[json.loads(l) for l in f]
    bymod={}
    for r in rows: bymod.setdefault(r['module'],{})[r['name']]=r
    groups=[]; timing={}
    with gzip.open(d/'replay.jsonl.gz','rt') as f:
        for line in f:
            g=json.loads(line)
            if g['event']=='kernel':
                mod=g['module']; members=[bymod[mod][n] for n in g['names']]
                key=H(['kernel-group-v1',sorted((r['name'],r['K']) for r in members)])
                g['K']=key; groups.append(g)
                for n in g['names']: timing[(mod,n)]=g
    for r in rows:
        candidates=[timing[(r['module'],n)] for n in r['group_names'] if (r['module'],n) in timing]
        if not candidates: raise ValueError(f"constant not replay-covered: {r['module']}:{r['name']}")
        g=candidates[0]
        r['constant_K']=r['K']; r['K']=g['K']; r['group_names']=g['names']
        r['kernel_ms']=g['cpu_ns']/1e6 if r['name']==g['names'][0] else 0
        r['kernel_group_kind']=g['kind']
        r['kernel_representative']=r['name']==g['names'][0]
    tmp=d/'rows.tmp.jsonl.gz'
    with gzip.open(tmp,'wt',compresslevel=6) as f:
        for r in rows:f.write(json.dumps(r,separators=(',',':'))+'\n')
    tmp.replace(d/'rows.jsonl.gz')
    with gzip.open(d/'kernel_groups.jsonl.gz','wt') as f:
        for g in groups:f.write(json.dumps(g,separators=(',',':'))+'\n')
    measured=sum(g['cpu_ns'] for g in groups)
    assert measured==json.loads((d/'replay_total.json').read_text())['kernel_cpu_ns']
    write(d/'coverage.json',{'rows':len(rows),'kernel_calls':len(groups),'all_constants_covered':True,
       'kernel_cpu_ns':measured,'distinct_K':len({g['K'] for g in groups}),
       'duplicate_theorems_rechecked':sum(g['duplicate_rechecked'] for g in groups)})

def H(x):
    return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':'),ensure_ascii=False).encode()).hexdigest()

def checkpoint(commit):
    overview=RESULTS/'research/B2c.json'; obj=json.loads(overview.read_text())
    if commit not in obj['completed_commits']:obj['completed_commits'].append(commit)
    write(overview,obj)
    md=RESULTS/'research/B2c.md'; text=md.read_text()
    import re
    text=re.sub(r'No avoidance percentages are available yet\..*?\n',f"No avoidance percentages are available yet. Completed and preserved {len(obj['completed_commits'])} of 20 commits.\n",text)
    md.write_text(text)
    command(['git','add','research'],cwd=RESULTS)
    staged=subprocess.check_output(['git','diff','--cached','--name-only'],cwd=RESULTS,text=True).splitlines()
    assert staged and all(p.startswith('research/') for p in staged)
    command(['git','commit','-m',f'research: preserve B2c data for {commit[:8]}'],cwd=RESULTS)
    command(['git','push','origin','research/b2c-measurement'],cwd=RESULTS)
    write(DATA/commit[:8]/'pushed.json',{'results_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=RESULTS,text=True).strip(),'pushed_unix':time.time()})
    # Receipt is included with the next checkpoint; Git's pushed ref is the durable
    # evidence for the current commit even if this machine disappears immediately.

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--attach-baseline',type=int);ap.add_argument('--retry-build',action='store_true');a=ap.parse_args()
    assert subprocess.check_output(['git','branch','--show-current'],cwd=RESULTS,text=True).strip()=='research/b2c-measurement'
    commits=capture(['git','rev-list','--first-parent','-n','20','--reverse','5018b95']).split()
    for i,commit in enumerate(commits):
        d=DATA/commit[:8];d.mkdir(parents=True,exist_ok=True)
        if (d/'complete.json').exists():
            if not (d/'pushed.json').exists():checkpoint(commit)
            continue
        if i==0 and a.attach_baseline:
            assert capture(['git','rev-parse','HEAD'])==commit
            write(d/'sources.json',sources()); attach_baseline(d,a.attach_baseline)
        else:
            command(['git','checkout','--detach',commit])
            write(d/'sources.json',sources())
            if not (d/'build.json').exists() or a.retry_build:
                if (d/'build_modules.jsonl').exists():
                    stamp=int(time.time()); (d/'build_modules.jsonl').rename(d/f'build_modules_attempt_{stamp}.jsonl')
                measure_build(d)
            else: assert json.loads((d/'build.json').read_text())['exit_code']==0
        if not (d/'coverage.json').exists():extract_and_replay(d)
        write(d/'complete.json',{'commit':commit,'index':i+1,'targets':TARGETS,'completed_unix':time.time()})
        checkpoint(commit)
    print('ALL TWENTY COMMITS MEASURED AND PUSHED. Report analysis and final audit still required.',flush=True)
if __name__=='__main__':main()
