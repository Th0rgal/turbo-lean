#!/usr/bin/env python3
"""Reproduce stale imports and verify artifact reconstruction in isolated Lake state."""
import json, os, pathlib, subprocess, tempfile
from run_experiment import WORK

def main():
    real=pathlib.Path(os.environ['B2C_REAL_ROOT'])
    env=os.environ.copy()
    for key in ('LEAN_SYSROOT','LAKE_OVERRIDE_LEAN','B2C_BUILD_LOG','FV_MEMCAP_STATS','LEAN_PATH'):
        env.pop(key,None)
    env['PATH']=str(real/'bin')+os.pathsep+env.get('PATH','')
    WORK.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='recovery-probe-',dir=WORK) as tmp:
        project=pathlib.Path(tmp)
        (project/'lean-toolchain').write_text('leanprover/lean4:v4.34.1\n')
        (project/'lakefile.toml').write_text('name = "artifactProbe"\nversion = "0.1.0"\ndefaultTargets = ["Probe"]\n\n[[lean_lib]]\nname = "Probe"\n')
        source=project/'Probe.lean'
        query=project/'Inspect.lean'
        query.write_text('import Probe\n#check before\n#check after\n')
        def run(*args):
            p=subprocess.run([str(real/'bin/lake'),*args],cwd=project,env=env,text=True,
                             stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
            return {'exit_code':p.returncode,'output':p.stdout}
        def inspect():return run('env','lean','Inspect.lean')
        source.write_text('def before : Nat := 1\n')
        initial_build=run('build','Probe');assert initial_build['exit_code']==0,initial_build
        before=inspect()
        assert 'before : Nat' in before['output'] and 'Unknown identifier `after`' in before['output'],before
        source.write_text('def after : Nat := 2\n')
        stale=inspect()
        assert stale==before,stale
        reconstruction=run('build','Probe');assert reconstruction['exit_code']==0,reconstruction
        fresh=inspect()
        assert 'after : Nat' in fresh['output'] and 'Unknown identifier `before`' in fresh['output'],fresh
        noop=run('build','Probe');assert noop['exit_code']==0,noop
        assert 'Built Probe' not in noop['output'],noop
        print(json.dumps({'toolchain':(project/'lean-toolchain').read_text().strip(),
            'isolated_project':True,'initial_build':initial_build,'initial_import':before,
            'source_changed_without_build_import':stale,'reconstruction_build':reconstruction,
            'reconstructed_import':fresh,'intact_artifact_check':noop,
            'stale_artifact_trigger_reproduced':True,'reconstruction_verified':True},indent=2))

if __name__=='__main__':main()
