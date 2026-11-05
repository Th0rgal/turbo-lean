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
import re
import statistics
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
CORE = ROOT / 'lean/.lake/build/bin/lean-native-core'
NAMES = ['collatz_steps', 'tuple_accum_sum', 'sarray_scale_bias',
         'dot_product_u64', 'saxpy_kernel', 'matmul_tiled_u64',
         'evm_erc20_transfer_u256', 'evm_muldiv_wad_u256']

FEATURE_EMITTER = r'''
import LeanNative.Core
open LeanNative.IR LeanNative.Transform LeanNative.Backend
def decl (name : String) (body : LNIRCode) : LNIRDecl := {
  name, body, params := [{id := 0, name := "seed", ty := .i64, borrow := false}]
  retTy := .i64, assurance := .verifiedKernelProof }
def main (args : List String) : IO Unit := do
  let chain := lowerAsyncAwaitChain (mkThreeStepAsyncSpec 0 10 16 5 7 9)
  let heap := lowerHeapClosureAsync3 0 10 5 7 9
  let ex : LNIRCode := .letBind 1 (.sarray .i64) (.sarrayEnsureExclusive 0 .i64)
    (.letBind 2 (.sarray .i64) (.sarrayEnsureExclusive 1 .i64) (.ret 2))
  let rc : LNIRCode := .incRef 0 1 (.decRef 0 1
    (.letBind 1 .i64 (.sarrayLen 0) (.ret 1)))
  let ptrDecl := fun name body retTy => { (decl name body) with
    params := [{id := 0, name := "arr", ty := .sarray .i64, borrow := false}], retTy }
  let m : LNIRModule := { moduleName := "Wave3Features", decls := [
    decl "d5_stackless" (optimizeAsyncStateMachine chain),
    decl "d5_heap" heap,
    ptrDecl "d1_base" ex (.sarray .i64),
    ptrDecl "d1_opt" (LeanNative.Frontend.ProofRetention.dischargeLocalExclusivity ex) (.sarray .i64),
    ptrDecl "d2_base" rc .i64,
    ptrDecl "d2_opt" (elideBorrowedAndThreadLocalRC 0 rc) .i64] }
  IO.FS.writeFile (args.headD "/tmp/features.ll") (emitLLVMOptimized m .x86_64)
'''

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
    return subprocess.check_output(list(map(str, args)), text=True, cwd=ROOT, **kw)


def build(tmp):
    # Reuse the production calibration's storage ABI and i256 pointer adapters.
    source = (ROOT / 'lean/LeanNative/Driver/CostAutotuneCLI.lean').read_text()
    support = source.split('private def nativeHarnessCSource : String :=\n"', 1)[1].split('extern uint64_t collatz_steps', 1)[0]
    wrappers = source.split('let wrappers := "', 1)[1].split('"\n    let ir', 1)[0]
    objects = []
    emitter = tmp / 'Features.lean'
    emitter.write_text(FEATURE_EMITTER)
    features = tmp / 'features.ll'
    subprocess.check_call(['lake', 'env', 'lean', '--run', str(emitter), str(features)], cwd=ROOT / 'lean')
    feature_obj = tmp / 'features.o'
    run(['clang', '-O3', '-march=native', '-Wno-override-module', '-c', features, '-o', feature_obj])
    objects.append(feature_obj)
    for prefix, flags in [('b', ['--baseline']), ('o', [])]:
        ll = tmp / (prefix + '.ll')
        run([CORE, 'compile', '--canonical-benchmark', '--emit-llvm', *flags, '-o', ll])
        text = ll.read_text() + wrappers
        # Namespace every defined symbol (including helpers), leaving external ABI alone.
        symbols = re.findall(r'^define[^\n]*@([\w.]+)\(', text, re.M)
        for name in sorted(set(symbols), key=len, reverse=True):
            text = re.sub(r'@' + re.escape(name) + r'(?=\()', '@' + prefix + '_' + name, text)
        ll.write_text(text)
        obj = tmp / (prefix + '.o')
        run(['clang', '-O3', '-march=native', '-Wno-override-module', '-c', ll, '-o', obj])
        objects.append(obj)
    rs = tmp / 'kernels.rs'
    rs.write_text(RUST)
    lib = tmp / 'rust.a'
    run(['rustc', '-C', 'opt-level=3', '-C', 'target-cpu=native', '--crate-type=staticlib', rs, '-o', lib])
    c = support + '\nextern uint64_t d5_stackless(uint64_t), d5_heap(uint64_t), r_d5(uint64_t);\n'
    c += 'extern void *d1_base(void*), *d1_opt(void*), *r_d1(void*);\nextern uint64_t d2_base(void*), d2_opt(void*), r_d2(void*);\n'
    for p in ['b', 'o', 'r']:
        c += f'''
extern uint64_t {p}_collatz_steps(uint64_t,uint64_t), {p}_tuple_accum_sum(uint64_t,uint64_t);
extern void *{p}_sarray_scale_bias(void*,uint64_t,uint64_t), *{p}_dot_product_u64(void*,void*), *{p}_saxpy_kernel(void*,void*), *{p}_matmul_tiled_u64(void*,void*,void*);
extern void {p}_bench_erc20(void*,void*,const void*,const void*,const void*), {p}_bench_muldiv(void*,const void*,const void*,const void*);
static uint64_t {p}_run(int k,uint64_t seed) {{
 if(k==8) return {dict(b='d5_heap', o='d5_stackless', r='r_d5')[p]}(seed);
 if(k==9) {{ uint64_t a[4]={{1,1,1,seed}};void *out={dict(b='d1_base',o='d1_opt',r='r_d1')[p]}(a);uint64_t x=((uint64_t*)out)[3];if(out!=a)free(out);return x; }}
 if(k==10) {{ uint64_t a[4]={{{'0xffffffff' if p == 'b' else '1'},1,1,seed}};return {dict(b='d2_base',o='d2_opt',r='r_d2')[p]}(a); }}
 if(k==0) return {p}_collatz_steps(17+(seed&7),128);
 if(k==1) return {p}_tuple_accum_sum(128,seed+1);
 if(k<6) {{
 uint64_t a[259]={{1,256,256}}, b[259]={{1,256,256}}, c[259]={{1,256,256}};
 for(int i=0;i<256;i++){{a[i+3]=seed+i+1;b[i+3]=2*i+3;c[i+3]=i+1;}}
 void *out=k==2?{p}_sarray_scale_bias(a,3,5):k==3?{p}_dot_product_u64(a,b):k==4?{p}_saxpy_kernel(a,b):{p}_matmul_tiled_u64(a,b,c);
 uint64_t *v=out,h=14695981039346656037ULL;for(size_t i=0;i<v[1];i++)h=(h^v[i+3])*1099511628211ULL;
 if(out!=a && out!=b && out!=c)free(out);return h;
 }}
 u256_t out=0,a=1000+seed,b=3000,d=100,s=10,r=20,amt=5+(seed&3);
 if(k==6){{evm_map_t m={{.keys={{10,20}},.vals={{1000,250}},.len=2}};{p}_bench_erc20(&out,&m,&s,&r,&amt);
 return (uint64_t)out ^ (uint64_t)m.vals[0] ^ ((uint64_t)m.vals[1]<<32);}}
 {p}_bench_muldiv(&out,&a,&b,&d);return (uint64_t)out^(uint64_t)(out>>64)^(uint64_t)(out>>128)^(uint64_t)(out>>192);
}}
'''
    c += r'''
static uint64_t now(void){struct timespec t;clock_gettime(CLOCK_MONOTONIC,&t);return t.tv_sec*1000000000ULL+t.tv_nsec;}
int main(int argc,char **argv){
 int trials=atoi(argv[1]);uint64_t (*f[3])(int,uint64_t)={r_run,b_run,o_run};
 /* Fail closed across every kernel and seed BEFORE any timing. */
 for(int k=0;k<11;k++)for(int s=0;s<128;s++){uint64_t x=f[0](k,s);
 for(int v=1;v<3;v++)if(f[v](k,s)!=x){fprintf(stderr,"parity failure kernel=%d seed=%d variant=%d\n",k,s,v);return 2;}}
 for(int t=-1;t<trials;t++)for(int k=0;k<11;k++)for(int j=0;j<3;j++){
 int v=(j+t+3)%3;uint64_t h=0,start=now();
 for(int i=0;i<2000;i++)h=(h^f[v](k,i&127))*1099511628211ULL;
 uint64_t elapsed=now()-start;if(t>=0)printf("%d %d %d %llu %llu\n",t,k,v,(unsigned long long)elapsed,(unsigned long long)h);
 }return 0;}
'''
    src = tmp / 'harness.c'
    src.write_text(c)
    exe = tmp / 'bench'
    run(['clang', '-O3', '-march=native', src, *objects, lib, '-ldl', '-lpthread', '-lm', '-o', exe])
    return exe


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--trials', type=int, default=7)
    parser.add_argument('--json', type=Path)
    args = parser.parse_args()
    if args.trials < 7:
        parser.error('at least seven trials required')
    os.environ['TURBO_LEAN_TELEMETRY'] = 'off'
    with tempfile.TemporaryDirectory(prefix='rust-parity-') as directory:
        exe = build(Path(directory))
        lines = run([exe, args.trials]).splitlines()
    names = NAMES + ['d5_async_three_await', 'd1_local_exclusivity', 'd2_thread_local_rc']
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
    result['evolution'] = json.loads(run([ROOT / 'target/release/turbo-lean', 'superopt-evolve',
                                        '--generations', '2', '--seed', '1', '--input', 'canonical',
                                        '--json', '--no-telemetry']))
    print(json.dumps(result, indent=2))
    if args.json:
        args.json.write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
