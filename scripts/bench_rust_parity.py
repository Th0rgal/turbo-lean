#!/usr/bin/env python3
"""Same-process canonical LNIR/Rust benchmark. Python standard library only.

Build lean-native-core first. Generated sources live in a temporary directory.
Names and ABI support are taken from the pinned checkout, never downloaded.
"""
import argparse
import json
import math
import os
from pathlib import Path
import platform
import statistics
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
CORE = ROOT / 'lean/.lake/build/bin/lean-native-core'
TURBO = ROOT / 'target/release/turbo-lean'
ENV = {**os.environ, 'TURBO_LEAN_TELEMETRY': 'off', 'LEAN_NATIVE_CORE_BIN': str(CORE)}

RUST = r'''
use std::ffi::c_void;
extern "C" { fn malloc(n: usize) -> *mut c_void; }
#[no_mangle] pub extern "C" fn r_collatz_steps(mut x:u64,n:u64)->u64 {
    for _ in 0..n { x=x.wrapping_mul(3).wrapping_add(1)/2; } x
}
#[no_mangle] pub extern "C" fn r_tuple_accum_sum(n:u64,mut x:u64)->u64 {
    for i in 0..n { let t=(x.wrapping_add(i),i.wrapping_mul(2)); x=t.0.wrapping_add(t.1); } x
}
unsafe fn data<'a>(p:*mut u64)-> &'a mut [u64] {
    std::slice::from_raw_parts_mut(p.add(3),*p.add(1) as usize)
}
#[no_mangle] pub unsafe extern "C" fn r_sarray_scale_bias(a:*mut u64,s:u64,b:u64)->*mut u64 {
    for x in data(a) { *x=x.wrapping_mul(s).wrapping_add(b); } a
}
#[no_mangle] pub unsafe extern "C" fn r_dot_product_u64(a:*mut u64,b:*mut u64)->*mut u64 {
    let sum=data(a).iter().zip(data(b).iter()).fold(0u64,|s,(x,y)|s.wrapping_add(x.wrapping_mul(*y)));
    let p=malloc(32) as *mut u64; *p=1; *p.add(1)=1; *p.add(2)=1; *p.add(3)=sum; p
}
#[no_mangle] pub unsafe extern "C" fn r_saxpy_kernel(a:*mut u64,b:*mut u64)->*mut u64 {
    for (x,y) in data(a).iter_mut().zip(data(b).iter()) { *x=x.wrapping_mul(4).wrapping_add(*y); } a
}
#[no_mangle] pub unsafe extern "C" fn r_matmul_tiled_u64(a:*mut u64,b:*mut u64,c:*mut u64)->*mut u64 {
    for ((x,y),z) in data(a).iter_mut().zip(data(b).iter()).zip(data(c).iter()) { *x=x.wrapping_mul(*y).wrapping_add(*z); } a
}
type W=[u64;4];
#[no_mangle] pub extern "C" fn r_d5(seed:u64)->u64 { seed.wrapping_add(5).wrapping_add(7).wrapping_add(9) }
#[no_mangle] pub extern "C" fn r_d1(p:*mut u64)->*mut u64 { p }
#[no_mangle] pub unsafe extern "C" fn r_d2(p:*mut u64)->u64 { *p.add(1) }
fn sub(a:W,b:W)->(W,bool) { let mut o=[0;4]; let mut c=false; for i in 0..4 {
    let (x,c1)=a[i].overflowing_sub(b[i]); let (y,c2)=x.overflowing_sub(c as u64); o[i]=y;c=c1||c2;
} (o,c) }
fn add(a:W,b:W)->(W,bool) { let mut o=[0;4]; let mut c=false; for i in 0..4 {
    let (x,c1)=a[i].overflowing_add(b[i]); let (y,c2)=x.overflowing_add(c as u64); o[i]=y;c=c1||c2;
} (o,c) }
extern "C" { fn lean_native_evm_sload(m:*mut c_void,s:*const W,o:*mut W);
fn lean_native_evm_sstore(m:*mut c_void,s:*const W,v:*const W); }
#[no_mangle] pub unsafe extern "C" fn r_bench_erc20(o:*mut W,m:*mut c_void,s:*const W,r:*const W,a:*const W) {
    let mut x=[0;4];lean_native_evm_sload(m,s,&mut x);let (x,under)=sub(x,*a);assert!(!under);
    lean_native_evm_sstore(m,s,&x);let mut y=[0;4];lean_native_evm_sload(m,r,&mut y);
    let (y,over)=add(y,*a);assert!(!over);lean_native_evm_sstore(m,r,&y);*o=y;
}
#[no_mangle] pub unsafe extern "C" fn r_bench_muldiv(o:*mut W,a:*const W,b:*const W,d:*const W) {
    let mut p=[0u64;8]; for i in 0..4 { let mut carry=0u128;for j in 0..4 {
        let t=(*a)[i] as u128*(*b)[j] as u128+p[i+j] as u128+carry;p[i+j]=t as u64;carry=t>>64;
    } p[i+4]=carry as u64; }
    assert!(*d != [0;4]);let mut rem=[0u64;4];let mut q=[0u64;8];
    for bit in (0..512).rev() { let high=rem[3]>>63;for j in (1..4).rev(){rem[j]=(rem[j]<<1)|(rem[j-1]>>63);}
        rem[0]=(rem[0]<<1)|((p[bit/64]>>(bit%64))&1);let (diff,borrow)=sub(rem,*d);
        if high!=0 || !borrow {rem=diff;q[bit/64]|=1u64<<(bit%64);} }
    assert!(q[4..].iter().all(|x|*x==0));let low=[q[0],q[1],q[2],q[3]];
    let mut clz=0;for x in low.iter().rev(){clz+=x.leading_zeros() as u64;if *x!=0{break;}}
    *o=add(low,[clz+(rem!=[0;4]) as u64,0,0,0]).0;
}
'''


def run(args, **kw):
    return subprocess.check_output(list(map(str, args)), text=True, cwd=ROOT, env=ENV, **kw)


def build(tmp):
    run([CORE, 'calibrate-cost', '--emit-parity-harness', tmp])
    rs = tmp / 'kernels.rs'
    rs.write_text(RUST)
    lib = tmp / 'rust.a'
    run(['rustc', '-C', 'opt-level=3', '-C', 'target-cpu=native', '--crate-type=staticlib', rs, '-o', lib])
    exe = tmp / 'bench'
    run(['clang', '-O3', '-march=native', '-Wno-override-module', tmp / 'harness.c',
         *sorted(tmp.glob('*.ll')), lib, '-ldl', '-lpthread', '-lm', '-o', exe])
    return exe


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--trials', type=int, default=7)
    parser.add_argument('--json', type=Path)
    args = parser.parse_args()
    if args.trials < 7:
        parser.error('at least seven trials required')
    if not CORE.is_file() or not TURBO.is_file():
        parser.error('missing checkout binaries; run (cd lean && lake build lean-native-core) '
                     'and cargo build --release --bin turbo-lean')
    with tempfile.TemporaryDirectory(prefix='rust-parity-') as directory:
        exe = build(Path(directory))
        lines = run([exe, args.trials]).splitlines()
        names = json.loads((Path(directory) / 'names.json').read_text())
    samples = {(k, v): [] for k in range(len(names)) for v in range(3)}
    checksums = {}
    seen = set()
    for line in lines:
        t, k, v, ns, checksum = map(int, line.split())
        if not (0 <= t < args.trials and (k, v) in samples and ns > 0):
            raise RuntimeError('invalid timing row')
        if (t, k, v) in seen:
            raise RuntimeError('duplicate timing row')
        seen.add((t, k, v))
        if k in checksums and checksums[k] != checksum:
            raise RuntimeError(f'timed checksum mismatch: {names[k]}')
        checksums[k] = checksum
        samples[k, v].append(ns / 2000)
    if any(len(values) != args.trials for values in samples.values()):
        raise RuntimeError('incomplete timing output')
    rows = []
    for k, name in enumerate(names):
        row = {'kernel': name, 'checksum': checksums[k]}
        for v, label in enumerate(['rust', 'baseline', 'optimized']):
            values = samples[k, v]
            q = statistics.quantiles(values, n=4, method='inclusive')
            row[label] = {'median_ns': statistics.median(values), 'iqr_ns': q[2]-q[0],
                          'min_ns': min(values), 'max_ns': max(values), 'samples_ns': values}
            row[label]['calls_per_second'] = 1e9 / row[label]['median_ns']
        for label in ['baseline', 'optimized']:
            ratio = row[label]['median_ns'] / row['rust']['median_ns']
            row[label].update(ratio=ratio, speedup=1/ratio, relative_throughput_pct=100/ratio)
        rows.append(row)
    result = {'commit': run(['git', 'rev-parse', 'HEAD']).strip(), 'trials': args.trials,
              'kernel': platform.platform(), 'cpu': run(['lscpu']),
              'rustc': run(['rustc', '--version']).strip(), 'clang': run(['clang', '--version']).strip(),
              'lean': run(['lean', '--version']).strip(), 'rows': rows,
              'geomean_ratio': {label: math.exp(statistics.mean(math.log(r[label]['ratio']) for r in rows[:8]))
                                for label in ['baseline', 'optimized']}}
    result['calibration'] = json.loads(run([CORE, 'calibrate-cost', '--target', 'x86_64', '--json']))
    result['evolution'] = json.loads(run([TURBO, 'superopt-evolve',
                                        '--generations', '2', '--seed', '1', '--input', 'canonical',
                                        '--json', '--no-telemetry']))
    print(json.dumps(result, indent=2))
    if args.json:
        args.json.write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
