#!/usr/bin/env python3
"""Build a toolchain-matched lean-native without invoking a prebuilt lean-native.

Requires the manifest-pinned lean-sys checkout at lean/.lake/packages/lean-sys.
Uses turbo-lean for Lean artifacts, then sequential C compilation and shared
Lean runtime linking if the installed turbo-lean does not link executables.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--evidence', type=Path, required=True)
    parser.add_argument('--skip-lean-build', action='store_true')
    parser.add_argument('--target', choices=('lean-native', 'lean-native-core'), default='lean-native')
    args = parser.parse_args()
    repo = args.repo.resolve()
    project = repo / 'lean'
    evidence = args.evidence.resolve()
    evidence.mkdir(parents=True, exist_ok=True)
    env = {**os.environ, 'LEAN_NUM_THREADS': '1', 'TURBO_LEAN_JOBS': '1'}
    records = []

    def run(command, cwd=project):
        start = time.monotonic()
        p = subprocess.run(list(map(str, command)), cwd=cwd, env=env,
                           text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        records.append(dict(command=list(map(str, command)), cwd=str(cwd),
                            returncode=p.returncode, seconds=time.monotonic() - start,
                            output=p.stdout))
        (evidence / 'commands.json').write_text(json.dumps(records, indent=2) + '\n')
        if p.returncode:
            raise RuntimeError(p.stdout or f'command failed: {command}')
        return p.stdout.strip()

    sysroot = Path(run(['lean', '--print-prefix']))
    version = run([sysroot / 'bin/lean', '--version'])
    required = (project / 'lean-toolchain').read_text().strip().split(':v')[-1]
    if f'version {required},' not in version:
        raise RuntimeError(f'toolchain mismatch: require {required}, got {version}')
    if not args.skip_lean_build:
        run(['turbo-lean', 'build', args.target, '--max-memory-mb', '6144'])
    dep = (project / '.lake/packages/lean-sys').resolve()
    sources = sorted((project / '.lake/build/ir').rglob('*.c'))
    sources += sorted((dep / '.lake/build/ir').rglob('*.c'))
    entry = 'Main' if args.target == 'lean-native' else 'CoreMain'
    other_entry = 'CoreMain' if entry == 'Main' else 'Main'
    sources = [s for s in sources if s != project / f'.lake/build/ir/LeanNative/Driver/{other_entry}.c']
    main_c = project / f'.lake/build/ir/LeanNative/Driver/{entry}.c'
    if main_c not in sources:
        raise RuntimeError(f'missing compiler entrypoint: {main_c}')
    sources.append(dep / 'c/lean_sys_shim.c')
    binary = project / '.lake/build/bin' / args.target
    native_from_turbo = binary.is_file() and all(
        binary.stat().st_mtime_ns >= source.stat().st_mtime_ns for source in sources)
    if not native_from_turbo:
        objdir = evidence / 'objects'
        objdir.mkdir(exist_ok=True)
        objects = []
        for i, source in enumerate(sources):
            obj = objdir / f'{i:04d}.o'
            # No native CPU requirement; export symbols for the Lean interpreter.
            run(['/usr/bin/clang', '-O2', '-DNDEBUG', '-DLEAN_EXPORTING', '-fPIC',
                 '-I', sysroot / 'include', '-c', source, '-o', obj])
            objects.append(obj)
            print(f'C {i + 1}/{len(sources)} {source.name}', flush=True)
        binary.parent.mkdir(parents=True, exist_ok=True)
        pending = binary.with_suffix('.pending')
        run(['/usr/bin/clang', '-rdynamic', *objects, '-L', sysroot / 'lib/lean',
             '-Wl,-rpath,' + str(sysroot / 'lib/lean'), '-lleanshared', '-lpthread', '-ldl',
             '-lm', '-o', pending])
        pending.replace(binary)
    run([binary, '--help'])
    smoke = evidence / 'BootstrapSmoke.lean'
    smoke.write_text('@[export bootstrap_add]\ndef bootstrapAdd (a b : UInt64) : UInt64 := a + b\n')
    wire = evidence / 'bootstrap-smoke.lnir'
    run([binary, 'emit-lnir', smoke, '--wire', '-o', wire])
    values = json.loads(run([binary, 'eval-lnir', '--lnir', wire, '--batch-json',
                            '--args', 'bootstrap_add:7,5']))
    if not any(row['decl'] == 'bootstrap_add' and int(row['value_u64']) == 12 for row in values):
        raise RuntimeError(f'bootstrap source-ingestion smoke failed: {values}')
    manifest = dict(source=run(['git', 'rev-parse', 'HEAD'], repo),
                    lean_sys_source=run(['git', 'rev-parse', 'HEAD'], dep),
                    lean_version=version, sysroot=str(sysroot), binary=str(binary),
                    sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),
                    bytes=binary.stat().st_size, native_sources=len(sources),
                    native_linked_by_turbo=native_from_turbo, bootstrap_smoke=values,
                    linking=run(['ldd', binary]))
    (evidence / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(json.dumps(manifest, indent=2))


if __name__ == '__main__':
    main()
