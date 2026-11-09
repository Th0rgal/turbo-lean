#!/usr/bin/env python3
"""Stage 5 `HeapObj` & C-ABI Sanitizer Stress & Positive Trap Suite (`libleanrt.a` + `CAbiEmit`).

Executes two complementary verification layers against the stock Lean 4 `v4.35.0` C/C++ runtime
(`include/lean/lean.h`, `libleanrt.a`, `libInit.a`) and `LeanNative.Driver.CoreCLI`'s emitted C-ABI headers:

  1. **Unwrapped `libleanrt.a` ASan + LSan + UBSan Lifecycle, `HeapObj` Layout & Positive Trap Suite**:
     - Links directly against `libleanrt.a` (without `-Wl,--wrap` allocator hooks, preserving internal
       `LEAN_MIMALLOC` invariants during `lean_initialize_runtime_module()`).
     - Verifies compile-time C11 `_Static_assert`s and runtime offsets/sizes matching
       `HeapObjAbiProofs.lean` and `HeapObjMtAbiProofs.lean` (`lean_object`, `lean_ctor_object`,
       `lean_sarray_object`, `lean_string_object`, `lean_closure_object`, `lean_external_object`,
       `LEAN_RC_STICKY`, `LEAN_RC_STICKY_DROP`, `LEAN_LINEAR_MARK_MASK`, `lean_alloc_sarray_would_overflow`,
       and `lean_native_flat_slice_t` / `lean_native_mut_slice_t` from `CAbiEmit.lean`).
     - Exercises tagged immediates (`lean_box` / `lean_unbox`), constructor scalar/obj slots,
       `lean_alloc_sarray` + `lean_sarray_ensure_exclusive` COW + `lean_mark_linear_core`,
       `lean_alloc_closure` + partial/exact/over-application (`lean_apply_1`), and
       `lean_register_external_class` + `lean_alloc_external` finalizer reclamation (`0` LSan leaks).
     - When `--core-bin` (`lean-native-core`) is supplied or present, emits a real C-ABI header via
       `emit-cabi-bindings --canonical-benchmark --emit-header` and links & executes compiled LLVM IR
       from `compile-llvm --canonical-benchmark` against the sanitized runtime harness.
     - Runs mandatory **positive sanitizer traps** (`rc != 0` with explicit sanitizer diagnostics):
       * `trap_lsan_external_leak` -> `LeakSanitizer: detected memory leaks`
       * `trap_asan_external_uaf` -> `AddressSanitizer: heap-use-after-free`
       * `trap_asan_cabi_slice_oob` -> `AddressSanitizer: heap-buffer-overflow`
       * `trap_ubsan_signed_shift` -> `runtime error:` (UndefinedBehaviorSanitizer)

  2. **Multi-Threaded `lean_mark_mt` & COW Exclusivity ThreadSanitizer (`-fsanitize=thread -DLEAN_TSAN`) Gate**:
     - Compiles with `/usr/bin/clang++ -fsanitize=thread -DLEAN_TSAN` (matching `lean.h`'s
       `__has_feature(thread_sanitizer)` / `LEAN_TSAN` guard explicitly while probing host ASLR
       compatibility first; fails closed in CI if TSan cannot execute).
     - Verifies `0` data races across 4 concurrent pthreads performing `lean_inc_ref` / `lean_dec_ref`
       and `lean_sarray_ensure_exclusive` COW clones on a `lean_mark_mt`-promoted object graph.
     - Runs mandatory **positive TSan race traps** (`rc != 0` with `ThreadSanitizer: data race`):
       * `trap_tsan_unmarked_st_rc_race`: concurrent `lean_inc_ref` / `lean_dec_ref` without `lean_mark_mt`.
       * `trap_tsan_shared_sarray_mutation_race`: concurrent mutation of shared `lean_sarray_cptr` without COW.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import fuzz_lcnf_conformance as fuzz_san

ROOT = Path(__file__).resolve().parent.parent
DEFAULT_CORE_BIN = ROOT / "lean" / ".lake" / "build" / "bin" / "lean-native-core"


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def find_lean_prefix(override_lean: str | None = None) -> Path | None:
    candidates: list[str | None] = [
        override_lean,
        os.environ.get("LEAN_BIN"),
        shutil.which("lean"),
        str(Path.home() / ".elan/toolchains/leanprover--lean4---v4.35.0/bin/lean"),
        "/var/lib/sandboxed-node/caches/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean",
        "/var/lib/sandboxed-node/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean",
        "/opt/orb/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean",
    ]
    seen: set[str] = set()
    for raw in candidates:
        if not raw or raw in seen:
            continue
        seen.add(raw)
        p = Path(raw)
        if not (p.is_file() and os.access(p, os.X_OK)):
            continue
        try:
            cand_pref = p.resolve().parent.parent
            if not ((cand_pref / "include" / "lean" / "lean.h").is_file() and (cand_pref / "lib" / "lean" / "libleanrt.a").is_file()):
                # Avoid running `~/.elan/bin/lean` proxy shims that resolve to `.elan` root without `lean.h` / `libleanrt.a`
                env = dict(os.environ)
                ver = subprocess.run([str(p), "--version"], env=env, check=True, capture_output=True, text=True).stdout
                if "4.35.0" not in ver:
                    continue
                pref = Path(
                    subprocess.run([str(p), "--print-prefix"], env=env, check=True, capture_output=True, text=True).stdout.strip()
                )
                if (pref / "include" / "lean" / "lean.h").is_file() and (pref / "lib" / "lean" / "libleanrt.a").is_file():
                    return pref
                continue
            env = dict(os.environ)
            env["LEAN_SYSROOT"] = str(cand_pref)
            ver = subprocess.run([str(p), "--version"], env=env, check=True, capture_output=True, text=True).stdout
            if "4.35.0" in ver:
                return cand_pref
        except (OSError, subprocess.SubprocessError):
            continue
    return None


def find_host_clangxx() -> str | None:
    for cand in (
        os.environ.get("CLANGXX"),
        "/usr/bin/clang++",
        "/usr/bin/clang++-18",
        shutil.which("clang++"),
        shutil.which("clang++-18"),
    ):
        if not cand:
            continue
        # Exclude .elan's bundled clang because it ships without libclang_rt.{asan,ubsan,tsan}.
        if ".elan" in cand or "caches/elan" in cand:
            continue
        p = Path(cand)
        if p.is_file() and os.access(p, os.X_OK):
            return str(p)
    return None


def find_host_clang() -> str | None:
    for cand in (
        os.environ.get("CLANG"),
        "/usr/bin/clang",
        "/usr/bin/clang-18",
        shutil.which("clang"),
        shutil.which("clang-18"),
    ):
        if not cand:
            continue
        if ".elan" in cand or "caches/elan" in cand:
            continue
        p = Path(cand)
        if p.is_file() and os.access(p, os.X_OK):
            return str(p)
    return None


def lean_runtime_link_flags(lean_prefix: Path) -> list[str]:
    inc = str(lean_prefix / "include")
    lib_lean = str(lean_prefix / "lib" / "lean")
    lib_root = str(lean_prefix / "lib")
    return [
        "-fdata-sections",
        "-ffunction-sections",
        f"-I{inc}",
        f"-L{lib_lean}",
        f"-L{lib_root}",
        f"-Wl,-rpath,{lib_lean}",
        f"-Wl,-rpath,{lib_root}",
        "-Wl,--start-group",
        "-lInit",
        "-lleanrt",
        "-lleancpp",
        "-Wl,--end-group",
        "-Wl,-Bstatic",
        "-lc++",
        "-lc++abi",
        "-Wl,-Bdynamic",
        "-Wl,--as-needed",
        "-lgmp",
        "-luv",
        "-lpthread",
        "-ldl",
        "-lrt",
        "-Wl,--no-as-needed",
        "-Wl,--gc-sections",
        "-pthread",
        "-ldl",
        "-lm",
    ]


FALLBACK_CABI_SLICE_HEADER = """/* Fallback CAbiEmit LP64 slice header (used only when --core-bin is not built) */
#pragma once
#ifndef LEAN_NATIVE_GENERATED_C_ABI_H
#define LEAN_NATIVE_GENERATED_C_ABI_H
#include <stdint.h>
#include <stddef.h>
typedef struct { const void* data; size_t len; size_t stride_bytes; } lean_native_flat_slice_t;
typedef struct { void* data; size_t len; size_t cap; } lean_native_mut_slice_t;
#if defined(__STDC_VERSION__) && __STDC_VERSION__ >= 201112L
#if defined(__LP64__) || defined(_LP64)
_Static_assert(sizeof(lean_native_flat_slice_t) == 24, "lean_native_flat_slice_t size");
_Static_assert(_Alignof(lean_native_flat_slice_t) == 8, "lean_native_flat_slice_t align");
_Static_assert(offsetof(lean_native_flat_slice_t, data) == 0, "lean_native_flat_slice_t.data offset");
_Static_assert(offsetof(lean_native_flat_slice_t, len) == 8, "lean_native_flat_slice_t.len offset");
_Static_assert(offsetof(lean_native_flat_slice_t, stride_bytes) == 16, "lean_native_flat_slice_t.stride_bytes offset");
_Static_assert(sizeof(lean_native_mut_slice_t) == 24, "lean_native_mut_slice_t size");
_Static_assert(_Alignof(lean_native_mut_slice_t) == 8, "lean_native_mut_slice_t align");
_Static_assert(offsetof(lean_native_mut_slice_t, data) == 0, "lean_native_mut_slice_t.data offset");
_Static_assert(offsetof(lean_native_mut_slice_t, len) == 8, "lean_native_mut_slice_t.len offset");
_Static_assert(offsetof(lean_native_mut_slice_t, cap) == 16, "lean_native_mut_slice_t.cap offset");
#endif
#endif
#endif /* LEAN_NATIVE_GENERATED_C_ABI_H */
"""


ASAN_HARNESS_CPP = r"""
#include <lean/lean.h>
#include "generated_cabi.h"
#include <assert.h>
#include <limits.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern "C" {
void lean_initialize_runtime_module(void);
void lean_initialize_thread(void);
void lean_finalize_thread(void);
void lean_runtime_mark_multi_threaded(void);
}

#ifdef USE_COMPILED_LNIR_KERNEL
extern "C" uint64_t collatz_steps(uint64_t n, uint64_t steps);
extern "C" lean_object* lean_native_abi_collatz_steps(lean_object* n, lean_object* steps);
extern "C" void* sarray_scale_bias(void* xs, uint64_t a, uint64_t b);
extern "C" void lean_native_evm_sload(void* m_ptr, const void* slot_ptr, void* val_out) {
    (void)m_ptr;
    (void)slot_ptr;
    memset(val_out, 0, 32);
}
extern "C" void lean_native_evm_sstore(void* m_ptr, const void* slot_ptr, const void* val_ptr) {
    (void)m_ptr;
    (void)slot_ptr;
    (void)val_ptr;
}
extern "C" uint64_t lean_native_trm_matryoshka_parity_u64(uint64_t x) {
    return static_cast<uint64_t>(__builtin_popcountll(x) & 1);
}
#endif

static_assert(sizeof(lean_native_flat_slice_t) == 24, "lean_native_flat_slice_t 24-byte LP64 layout");
static_assert(alignof(lean_native_flat_slice_t) == 8, "lean_native_flat_slice_t 8-byte align");
static_assert(offsetof(lean_native_flat_slice_t, data) == 0, "flat_slice.data offset 0");
static_assert(offsetof(lean_native_flat_slice_t, len) == 8, "flat_slice.len offset 8");
static_assert(offsetof(lean_native_flat_slice_t, stride_bytes) == 16, "flat_slice.stride_bytes offset 16");
static_assert(sizeof(lean_native_mut_slice_t) == 24, "lean_native_mut_slice_t 24-byte LP64 layout");
static_assert(alignof(lean_native_mut_slice_t) == 8, "lean_native_mut_slice_t 8-byte align");
static_assert(offsetof(lean_native_mut_slice_t, data) == 0, "mut_slice.data offset 0");
static_assert(offsetof(lean_native_mut_slice_t, len) == 8, "mut_slice.len offset 8");
static_assert(offsetof(lean_native_mut_slice_t, cap) == 16, "mut_slice.cap offset 16");

static_assert(sizeof(lean_object) == 8, "lean_object 8-byte header");
static_assert(offsetof(lean_object, m_rc) == 0, "m_rc offset 0");

static_assert(sizeof(lean_sarray_object) == 24, "lean_sarray_object 24-byte LP64 prefix");
static_assert(offsetof(lean_sarray_object, m_size) == 8, "sarray m_size offset 8");
static_assert(offsetof(lean_sarray_object, m_capacity) == 16, "sarray m_capacity offset 16");
static_assert(offsetof(lean_sarray_object, m_data) == 24, "sarray m_data offset 24");

static_assert(sizeof(lean_string_object) == 32, "lean_string_object 32-byte LP64 prefix");
static_assert(offsetof(lean_string_object, m_size) == 8, "string m_size offset 8");
static_assert(offsetof(lean_string_object, m_capacity) == 16, "string m_capacity offset 16");
static_assert(offsetof(lean_string_object, m_length) == 24, "string m_length offset 24");
static_assert(offsetof(lean_string_object, m_data) == 32, "string m_data offset 32");

static_assert(offsetof(lean_closure_object, m_fun) == 8, "closure m_fun offset 8");
static_assert(offsetof(lean_closure_object, m_arity) == 16, "closure m_arity offset 16");
static_assert(offsetof(lean_closure_object, m_num_fixed) == 18, "closure m_num_fixed offset 18");
static_assert(offsetof(lean_closure_object, m_objs) == 24, "closure m_objs offset 24");

static_assert(sizeof(lean_external_object) == 24, "lean_external_object 24-byte LP64 layout");
static_assert(offsetof(lean_external_object, m_class) == 8, "external m_class offset 8");
static_assert(offsetof(lean_external_object, m_data) == 16, "external m_data offset 16");

static_assert(LEAN_RC_STICKY == (INT_MIN + 0x10000000), "LEAN_RC_STICKY constant");
static_assert(LEAN_RC_STICKY_DROP == (INT_MIN + 0x20000000), "LEAN_RC_STICKY_DROP constant");
static_assert(LEAN_LINEAR_MARK_MASK == 0x80u, "LEAN_LINEAR_MARK_MASK constant");
static_assert(LeanMaxCtorTag == 243 && LeanClosure == 245 && LeanScalarArray == 248 && LeanString == 249 && LeanExternal == 254, "Lean runtime tags");

static size_t g_ext_finalizer_calls = 0;

struct ExtPayload {
    uint64_t magic;
    uint64_t words[4];
};

static void ext_finalize(void* p) {
    ExtPayload* ep = static_cast<ExtPayload*>(p);
    assert(ep->magic == 0x4C45414E45585435ULL);
    g_ext_finalizer_calls++;
    free(ep);
}

static void ext_foreach(void*, b_lean_obj_arg) {}

extern "C" lean_obj_res boxed_affine3(lean_obj_arg a, lean_obj_arg b, lean_obj_arg c) {
    uint64_t va = lean_unbox(a);
    uint64_t vb = lean_unbox(b);
    uint64_t vc = lean_unbox(c);
    lean_dec(a);
    lean_dec(b);
    lean_dec(c);
    return lean_box((size_t)(va * vb + vc));
}

static int run_clean_suite(void) {
    // 0. Little-endian 64-bit `lean_object` bit-field byte layout matching `packHeaderU64` in `HeapObjAbiProofs.lean`
    lean_object raw_hdr;
    memset(&raw_hdr, 0, sizeof(raw_hdr));
    raw_hdr.m_rc = static_cast<int32_t>(0x11223344);
    raw_hdr.m_cs_sz = 0x5566u;
    raw_hdr.m_other = 0x77u;
    raw_hdr.m_tag = 0x88u;
    uint64_t packed_hdr = 0;
    memcpy(&packed_hdr, &raw_hdr, sizeof(uint64_t));
    if (packed_hdr != 0x8877556611223344ULL) return 9;

    // 1. Tagged immediates (`lean_box` / `lean_unbox`)
    size_t samples[] = {0u, 1u, 42u, 255u, 65535u, (1ull << 47) - 1ull, ((size_t)-1) >> 1};
    for (size_t s : samples) {
        lean_object* b = lean_box(s);
        if (!lean_is_scalar(b) || lean_unbox(b) != s) return 10;
        lean_inc(b);
        lean_dec(b);
    }

    // 2. Constructor object (`lean_alloc_ctor`) obj + scalar slot disjointness
    lean_object* child0 = lean_mk_string("stage5-child");
    lean_object* ctor = lean_alloc_ctor(3, 2, 16);
    lean_ctor_set(ctor, 0, child0);
    lean_ctor_set(ctor, 1, lean_box(99));
    lean_ctor_set_uint64(ctor, 2 * sizeof(void*), 0xCAFEBABE12345678ULL);
    lean_ctor_set_uint32(ctor, 2 * sizeof(void*) + 8, 0xA5A55A5AU);
    lean_ctor_set_uint8(ctor, 2 * sizeof(void*) + 12, 0x7FU);
    if (!lean_is_exclusive(ctor) || lean_ptr_tag(ctor) != 3) return 11;
    if (lean_ctor_get_uint64(ctor, 2 * sizeof(void*)) != 0xCAFEBABE12345678ULL) return 12;
    if (lean_ctor_get_uint32(ctor, 2 * sizeof(void*) + 8) != 0xA5A55A5AU) return 13;
    if (lean_ctor_get_uint8(ctor, 2 * sizeof(void*) + 12) != 0x7FU) return 14;
    if (strcmp(lean_string_cstr(lean_ctor_get(ctor, 0)), "stage5-child") != 0) return 15;
    lean_dec_ref(ctor);

    // 3. Scalar array (`lean_alloc_sarray`), COW (`lean_sarray_ensure_exclusive`), & linearity mark (`0x80u`)
    if (!lean_alloc_sarray_would_overflow(8, (SIZE_MAX / 8) + 1)) return 16;
    if (!lean_alloc_sarray_would_overflow(8, (SIZE_MAX - 16) / 8)) return 17;
    if (lean_alloc_sarray_would_overflow(8, 16)) return 18;

    lean_object* sarr = lean_alloc_sarray(sizeof(uint64_t), 4, 8);
    if (lean_sarray_elem_size(sarr) != 8 || lean_is_marked_linear_core(sarr)) return 19;
    lean_mark_linear_core(sarr);
    if (!lean_is_marked_linear_core(sarr) || lean_sarray_elem_size(sarr) != 8) return 20;
    uint64_t* base = reinterpret_cast<uint64_t*>(lean_sarray_cptr(sarr));
    for (size_t i = 0; i < 4; ++i) base[i] = (i + 1) * 11ULL;

    // Share `sarr` (`m_rc == 2`) and trigger `lean_sarray_ensure_exclusive` COW copy
    lean_inc_ref(sarr);
    lean_object* cow = lean_sarray_ensure_exclusive(sarr);
    if (cow == sarr || !lean_is_exclusive(cow) || !lean_is_exclusive(sarr)) return 21;
    reinterpret_cast<uint64_t*>(lean_sarray_cptr(cow))[0] = 999ULL;
    if (reinterpret_cast<uint64_t*>(lean_sarray_cptr(sarr))[0] != 11ULL) return 22;
    lean_dec_ref(cow);

    // 4. Sticky & MT predicate boundaries matching `HeapObjMtAbiProofs.lean`
    lean_object hdr_probe;
    hdr_probe.m_cs_sz = 0;
    hdr_probe.m_other = 8;
    hdr_probe.m_tag = LeanScalarArray;
    hdr_probe.m_rc = -1;
    if (!lean_is_mt(&hdr_probe) || !lean_is_unstuck_mt(&hdr_probe) || lean_is_never_freed(&hdr_probe)) return 23;
    hdr_probe.m_rc = LEAN_RC_STICKY;
    if (lean_is_unstuck_mt(&hdr_probe) || !lean_is_never_freed(&hdr_probe)) return 24;
    hdr_probe.m_rc = LEAN_RC_STICKY_DROP;
    if (!lean_is_never_freed(&hdr_probe)) return 25;
    hdr_probe.m_rc = LEAN_RC_STICKY_DROP + 1;
    if (lean_is_never_freed(&hdr_probe)) return 26;
    hdr_probe.m_rc = 0;
    if (!lean_is_persistent(&hdr_probe) || !lean_is_never_freed(&hdr_probe)) return 27;

    // 5. Closures: partial application + exact application (`lean_alloc_closure`, `lean_apply_1`)
    lean_object* clos1 = lean_alloc_closure(reinterpret_cast<void*>(&boxed_affine3), 3, 1);
    lean_closure_set(clos1, 0, lean_box(7));
    lean_object* clos2 = lean_apply_1(clos1, lean_box(6));
    lean_object* clos_res = lean_apply_1(clos2, lean_box(5));
    if (!lean_is_scalar(clos_res) || lean_unbox(clos_res) != 47u) return 28;

    // 6. External objects (`lean_register_external_class` + `lean_alloc_external` + finalizer reclamation)
    lean_external_class* cls = lean_register_external_class(&ext_finalize, &ext_foreach);
    ExtPayload* payload = static_cast<ExtPayload*>(malloc(sizeof(ExtPayload)));
    payload->magic = 0x4C45414E45585435ULL;
    for (int i = 0; i < 4; ++i) payload->words[i] = (uint64_t)(i + 10);
    lean_object* ext = lean_alloc_external(cls, payload);
    lean_inc_ref(ext);
    lean_dec_ref(ext);
    if (g_ext_finalizer_calls != 0) return 29;
    lean_dec_ref(ext);
    if (g_ext_finalizer_calls != 1) return 30;

    // 7. CAbiEmit slice view marshaling over `sarr`'s backing buffer
    lean_native_flat_slice_t view = { lean_sarray_cptr(sarr), lean_sarray_size(sarr), sizeof(uint64_t) };
    uint64_t acc = 0;
    const uint8_t* raw_bytes = static_cast<const uint8_t*>(view.data);
    for (size_t i = 0; i < view.len; ++i) {
        uint64_t elem = 0;
        memcpy(&elem, raw_bytes + i * view.stride_bytes, sizeof(uint64_t));
        acc += elem;
    }
    if (acc != (11ULL + 22ULL + 33ULL + 44ULL)) return 31;

    uint64_t kernel_out = 0;
#ifdef USE_COMPILED_LNIR_KERNEL
    uint64_t direct_collatz = collatz_steps(13ULL, 5ULL);
    lean_object* abi_collatz_boxed = lean_native_abi_collatz_steps(lean_box(13u), lean_box(5u));
    if (!lean_is_scalar(abi_collatz_boxed) || lean_unbox(abi_collatz_boxed) != direct_collatz) return 32;
    // Exercise `sarray_scale_bias` on an exclusive `lean_alloc_sarray` (`m_rc == 1`, zero clone malloc)
    lean_object* sarr_excl = lean_alloc_sarray(sizeof(uint64_t), 4, 4);
    uint64_t* dexcl = reinterpret_cast<uint64_t*>(lean_sarray_cptr(sarr_excl));
    for (size_t i = 0; i < 4; ++i) dexcl[i] = (i + 1) * 10ULL;
    lean_object* out_arr = static_cast<lean_object*>(sarray_scale_bias(sarr_excl, 3ULL, 5ULL));
    if (out_arr != sarr_excl) return 33;
    uint64_t* dout = reinterpret_cast<uint64_t*>(lean_sarray_cptr(out_arr));
    if (dout[0] != 35ULL || dout[3] != 125ULL) return 34;
    kernel_out = direct_collatz + dout[0] + dout[3];
    lean_dec_ref(out_arr);
#endif
    lean_dec_ref(sarr);

    printf("{\"ok\":true,\"finalizerCalls\":%zu,\"sliceSum\":%llu,\"kernelOut\":%llu}\n",
           g_ext_finalizer_calls, (unsigned long long)acc, (unsigned long long)kernel_out);
    return 0;
}

int main(int argc, char** argv) {
    lean_initialize_runtime_module();
    const char* mode = (argc > 1) ? argv[1] : "clean";

    if (strcmp(mode, "clean") == 0) {
        int rc = run_clean_suite();
        lean_finalize_thread();
        return rc;
    }
    if (strcmp(mode, "trap_lsan_external_leak") == 0) {
        lean_external_class* cls = lean_register_external_class(&ext_finalize, &ext_foreach);
        ExtPayload* leaked = static_cast<ExtPayload*>(malloc(sizeof(ExtPayload)));
        leaked->magic = 0x4C45414E45585435ULL;
        leaked->words[0] = 0xDEADULL;
        volatile uintptr_t hide = reinterpret_cast<uintptr_t>(lean_alloc_external(cls, leaked));
        (void)hide;
        // Deliberately omit `lean_dec_ref`: finalizer never runs and LSan must catch `leaked`.
        return 0;
    }
    if (strcmp(mode, "trap_asan_external_uaf") == 0) {
        lean_external_class* cls = lean_register_external_class(&ext_finalize, &ext_foreach);
        ExtPayload* ep = static_cast<ExtPayload*>(malloc(sizeof(ExtPayload)));
        ep->magic = 0x4C45414E45585435ULL;
        ep->words[0] = 77ULL;
        lean_object* ext = lean_alloc_external(cls, ep);
        lean_dec_ref(ext); // Frees `ep` via `ext_finalize`
        volatile uint64_t uaf = ep->words[0];
        printf("%llu\n", (unsigned long long)uaf);
        return 0;
    }
    if (strcmp(mode, "trap_asan_cabi_slice_oob") == 0) {
        uint64_t* buf = static_cast<uint64_t*>(malloc(4 * sizeof(uint64_t)));
        lean_native_mut_slice_t mslice = { buf, 4, 4 };
        volatile uint64_t* p = static_cast<uint64_t*>(mslice.data);
        p[mslice.cap] = 0xBAD00BULL; // One-past-end write caught by ASan
        free(buf);
        return 0;
    }
    if (strcmp(mode, "trap_ubsan_signed_shift") == 0) {
        volatile int sh = 35;
        volatile int base = 1;
        int bad = base << sh;
        printf("%d\n", bad);
        return 0;
    }
    fprintf(stderr, "Unknown mode: %s\n", mode);
    return 2;
}
"""


TSAN_HARNESS_CPP = r"""
#include <lean/lean.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern "C" {
void lean_initialize_runtime_module(void);
void lean_initialize_thread(void);
void lean_finalize_thread(void);
}

struct WorkerCtx {
    lean_object* shared_sarr;
    lean_object* out_clones[16];
    size_t num_clones;
    uint64_t out_sum;
    int iters;
};

static void* clean_mt_worker(void* arg) {
    lean_initialize_thread();
    WorkerCtx* ctx = static_cast<WorkerCtx*>(arg);
    uint64_t sum = 0;
    size_t clone_idx = 0;
    for (int i = 0; i < ctx->iters; ++i) {
        lean_object* ref = ctx->shared_sarr;
        lean_inc_ref(ref);
        if ((i & 31) == 0 && clone_idx < 16) {
            // Exclusive COW clone on an MT-marked shared array (`m_rc < 0` -> fresh `m_rc == 1` clone)
            lean_object* local = lean_sarray_ensure_exclusive(ref);
            uint64_t* p = reinterpret_cast<uint64_t*>(lean_sarray_cptr(local));
            p[0] += 1ULL;
            sum += p[0];
            ctx->out_clones[clone_idx++] = local;
        } else {
            const uint64_t* p = reinterpret_cast<const uint64_t*>(lean_sarray_cptr(ref));
            sum += p[0] + p[1];
            lean_dec_ref(ref);
        }
    }
    ctx->num_clones = clone_idx;
    ctx->out_sum = sum;
    lean_finalize_thread();
    return nullptr;
}

static __attribute__((noinline)) void st_inc_ref_fastpath(lean_object* obj) {
    obj->m_rc = static_cast<int>(static_cast<unsigned>(obj->m_rc) + 1u);
}

static __attribute__((noinline)) void st_dec_ref_fastpath(lean_object* obj) {
    obj->m_rc -= 1;
}

// Replicates the non-TSan single-threaded `m_rc` fast-path (`o->m_rc += 1; o->m_rc -= 1`)
// when a caller forgets `lean_mark_mt` (`m_rc > 0`).
static void* racy_unmarked_st_fastpath_worker(void* arg) {
    lean_object* obj = static_cast<lean_object*>(arg);
    for (int i = 0; i < 4000; ++i) {
        st_inc_ref_fastpath(obj);
        st_dec_ref_fastpath(obj);
    }
    return nullptr;
}

static void* racy_shared_sarray_write_worker(void* arg) {
    lean_object* sarr = static_cast<lean_object*>(arg);
    uint64_t* data = reinterpret_cast<uint64_t*>(lean_sarray_cptr(sarr));
    for (int i = 0; i < 4000; ++i) {
        data[0] += 1ULL; // BUG: mutating shared `lean_sarray_object` without `lean_sarray_ensure_exclusive`!
    }
    return nullptr;
}

int main(int argc, char** argv) {
    lean_initialize_runtime_module();
    const char* mode = (argc > 1) ? argv[1] : "clean_mt";

    if (strcmp(mode, "probe") == 0) {
        lean_finalize_thread();
        return 0;
    }

    if (strcmp(mode, "clean_mt") == 0) {
        lean_object* sarr = lean_alloc_sarray(sizeof(uint64_t), 4, 4);
        uint64_t* d = reinterpret_cast<uint64_t*>(lean_sarray_cptr(sarr));
        d[0] = 10ULL; d[1] = 20ULL; d[2] = 30ULL; d[3] = 40ULL;
        lean_object* pair = lean_alloc_ctor(0, 2, 0);
        lean_inc_ref(sarr);
        lean_ctor_set(pair, 0, sarr);
        lean_ctor_set(pair, 1, lean_box(7));
        // Promote transitive object graph (`pair` and `sarr`) to atomic multi-threaded `m_rc < 0`
        lean_mark_mt(pair);
        if (!lean_is_mt(pair) || !lean_is_mt(sarr)) return 10;

        constexpr int kThreads = 4;
        pthread_t tids[kThreads];
        WorkerCtx ctxs[kThreads];
        for (int t = 0; t < kThreads; ++t) {
            memset(&ctxs[t], 0, sizeof(WorkerCtx));
            ctxs[t].shared_sarr = sarr;
            ctxs[t].iters = 512;
            pthread_create(&tids[t], nullptr, &clean_mt_worker, &ctxs[t]);
        }
        uint64_t total = 0;
        for (int t = 0; t < kThreads; ++t) {
            pthread_join(tids[t], nullptr);
            total += ctxs[t].out_sum;
            for (size_t c = 0; c < ctxs[t].num_clones; ++c) {
                lean_dec_ref(ctxs[t].out_clones[c]);
            }
        }
        lean_dec_ref(pair);
        lean_dec_ref(sarr);
        lean_finalize_thread();
        printf("{\"ok\":true,\"threads\":%d,\"total\":%llu}\n", kThreads, (unsigned long long)total);
        return (total > 0) ? 0 : 11;
    }

    if (strcmp(mode, "trap_tsan_unmarked_st_rc_race") == 0) {
        lean_object* hdr = static_cast<lean_object*>(calloc(1, sizeof(lean_object)));
        hdr->m_rc = 2; // Unmarked single-threaded `m_rc > 0`
        hdr->m_tag = LeanScalarArray;
        pthread_t t1, t2;
        pthread_create(&t1, nullptr, &racy_unmarked_st_fastpath_worker, hdr);
        pthread_create(&t2, nullptr, &racy_unmarked_st_fastpath_worker, hdr);
        pthread_join(t1, nullptr);
        pthread_join(t2, nullptr);
        free(hdr);
        return 0;
    }

    if (strcmp(mode, "trap_tsan_shared_sarray_mutation_race") == 0) {
        lean_object* sarr = lean_alloc_sarray(sizeof(uint64_t), 2, 2);
        reinterpret_cast<uint64_t*>(lean_sarray_cptr(sarr))[0] = 0ULL;
        lean_mark_mt(sarr);
        pthread_t t1, t2;
        pthread_create(&t1, nullptr, &racy_shared_sarray_write_worker, sarr);
        pthread_create(&t2, nullptr, &racy_shared_sarray_write_worker, sarr);
        pthread_join(t1, nullptr);
        pthread_join(t2, nullptr);
        lean_dec_ref(sarr);
        return 0;
    }

    return 2;
}
"""


def run_sanitizer_suite(
    core_bin_arg: str | None = None,
    require_tsan: bool | None = None,
) -> dict[str, Any]:
    if require_tsan is None:
        require_tsan = os.environ.get("GITHUB_ACTIONS") == "true" or os.environ.get("CI") == "true"

    lean_prefix = find_lean_prefix()
    clangxx = find_host_clangxx()
    clang = find_host_clang()
    if lean_prefix is None or clangxx is None or clang is None:
        return {
            "schemaVersion": "turbo-lean-heapobj-sanitizers-v1",
            "ok": False,
            "status": "incomplete_missing_toolchain",
            "leanPrefix": str(lean_prefix) if lean_prefix else None,
            "clangxx": clangxx,
            "clang": clang,
        }

    core_path: Path | None = None
    if core_bin_arg:
        cand = Path(core_bin_arg)
        if not (cand.is_file() and os.access(cand, os.X_OK)):
            return {
                "schemaVersion": "turbo-lean-heapobj-sanitizers-v1",
                "ok": False,
                "status": "missing_requested_core_bin",
                "requestedCoreBin": str(cand),
            }
        core_path = cand.resolve()
    elif DEFAULT_CORE_BIN.is_file() and os.access(DEFAULT_CORE_BIN, os.X_OK):
        core_path = DEFAULT_CORE_BIN.resolve()

    link_flags = lean_runtime_link_flags(lean_prefix)

    with tempfile.TemporaryDirectory(prefix="turbo_stage5_heapobj_san_") as tmp:
        tmpdir = Path(tmp)
        hdr_path = tmpdir / "generated_cabi.h"
        extra_objs: list[str] = []
        extra_defs: list[str] = []
        core_artifacts: dict[str, Any] = {"usedCoreBin": str(core_path) if core_path else None}

        if core_path is not None:
            subprocess.run(
                [str(core_path), "emit-cabi-bindings", "--canonical-benchmark", "--arch", "x86_64", "--emit-header", str(hdr_path)],
                cwd=ROOT,
                check=True,
                capture_output=True,
                text=True,
            )
            ll_path = tmpdir / "canonical.ll"
            asan_ll_path = tmpdir / "canonical.asan.ll"
            obj_path = tmpdir / "canonical.asan.o"
            subprocess.run(
                [str(core_path), "compile-llvm", "--canonical-benchmark", "--arch", "x86_64", "-o", str(ll_path)],
                cwd=ROOT,
                check=True,
                capture_output=True,
                text=True,
            )
            raw_ll = ll_path.read_text(encoding="utf-8")
            asan_ll = fuzz_san.instrument_llvm_ir_for_asan(raw_ll)
            asan_ll_path.write_text(asan_ll, encoding="utf-8")
            subprocess.run(
                [
                    clang,
                    "-O1",
                    "-g",
                    "-fdata-sections",
                    "-ffunction-sections",
                    "-Wno-override-module",
                    "-fsanitize=address",
                    "-c",
                    str(asan_ll_path),
                    "-o",
                    str(obj_path),
                ],
                check=True,
                capture_output=True,
                text=True,
            )
            extra_objs.append(str(obj_path))
            extra_defs.append("-DUSE_COMPILED_LNIR_KERNEL=1")
            core_artifacts["headerSha256"] = sha256_bytes(hdr_path.read_bytes())
            core_artifacts["llvmIrSha256"] = sha256_bytes(ll_path.read_bytes())
            core_artifacts["asanInstrumentedLlvmIrSha256"] = sha256_bytes(asan_ll_path.read_bytes())
        else:
            hdr_path.write_text(FALLBACK_CABI_SLICE_HEADER, encoding="utf-8")
            core_artifacts["headerSha256"] = sha256_bytes(hdr_path.read_bytes())

        asan_cpp = tmpdir / "asan_harness.cpp"
        asan_bin = tmpdir / "asan_harness"
        asan_cpp.write_text(ASAN_HARNESS_CPP, encoding="utf-8")

        subprocess.run(
            [
                clangxx,
                "-std=c++17",
                "-O1",
                "-g",
                "-fno-omit-frame-pointer",
                "-fsanitize=address,undefined",
                "-fno-sanitize-recover=all",
                f"-I{tmpdir}",
                *extra_defs,
                str(asan_cpp),
                *extra_objs,
                *link_flags,
                "-o",
                str(asan_bin),
            ],
            check=True,
            capture_output=True,
            text=True,
        )

        base_asan_env = dict(os.environ)
        base_asan_env["ASAN_OPTIONS"] = "detect_leaks=1:halt_on_error=1:abort_on_error=0"
        base_asan_env["UBSAN_OPTIONS"] = "print_stacktrace=1:halt_on_error=1"

        clean_res = subprocess.run([str(asan_bin), "clean"], env=base_asan_env, capture_output=True, text=True)
        clean_payload: dict[str, Any] = {}
        if clean_res.returncode == 0 and clean_res.stdout.strip():
            clean_payload = json.loads(clean_res.stdout.strip().splitlines()[-1])

        positive_traps: list[tuple[str, str, dict[str, str]]] = [
            ("trap_lsan_external_leak", "LeakSanitizer", {}),
            ("trap_asan_external_uaf", "heap-use-after-free", {"ASAN_OPTIONS": "detect_leaks=0:halt_on_error=1"}),
            ("trap_asan_cabi_slice_oob", "heap-buffer-overflow", {"ASAN_OPTIONS": "detect_leaks=0:halt_on_error=1"}),
            ("trap_ubsan_signed_shift", "runtime error:", {"ASAN_OPTIONS": "detect_leaks=0:halt_on_error=1"}),
        ]
        trap_results: dict[str, Any] = {}
        traps_ok = True
        for trap_mode, expected_token, env_override in positive_traps:
            tenv = dict(base_asan_env)
            tenv.update(env_override)
            tres = subprocess.run([str(asan_bin), trap_mode], env=tenv, capture_output=True, text=True)
            combined = (tres.stdout or "") + "\n" + (tres.stderr or "")
            caught = tres.returncode != 0 and expected_token in combined
            if not caught:
                traps_ok = False
            trap_results[trap_mode] = {
                "caught": caught,
                "returncode": tres.returncode,
                "expectedToken": expected_token,
            }

        # Part 2: ThreadSanitizer (`-fsanitize=thread -DLEAN_TSAN`) multi-threaded RC & COW stress + positive race traps
        tsan_cpp = tmpdir / "tsan_harness.cpp"
        tsan_bin = tmpdir / "tsan_harness"
        tsan_cpp.write_text(TSAN_HARNESS_CPP, encoding="utf-8")
        tsan_report: dict[str, Any] = {}
        tsan_ok = False
        tsan_compile = subprocess.run(
            [
                clangxx,
                "-std=c++17",
                "-O1",
                "-g",
                "-fno-omit-frame-pointer",
                "-fsanitize=thread",
                "-DLEAN_TSAN",
                str(tsan_cpp),
                *link_flags,
                "-o",
                str(tsan_bin),
            ],
            capture_output=True,
            text=True,
        )
        if tsan_compile.returncode == 0:
            tsan_supp = tmpdir / "tsan_mimalloc.supp"
            # `libleanrt.a` embeds prebuilt un-instrumented `mimalloc` (`LEAN_MIMALLOC`), whose lock-free
            # thread-local arena metadata init (`_mi_theap_init` / `_mi_meta_free` / `_mi_*`) uses internal
            # C++ atomics invisible to TSan. Suppress only internal `_mi_*`/`mi_*` allocator internals so
            # any data race in `lean_*` RC headers, `lean_sarray_*` payloads, or C-ABI code fails closed.
            tsan_supp.write_text("race:^_mi_\nrace:^mi_\n", encoding="utf-8")
            tsan_env = dict(os.environ)
            tsan_env["TSAN_OPTIONS"] = f"halt_on_error=1:second_deadlock_stack=1:suppressions={tsan_supp}"
            probe_res = subprocess.run([str(tsan_bin), "probe"], env=tsan_env, capture_output=True, text=True)
            if probe_res.returncode == 0:
                mt_clean = subprocess.run([str(tsan_bin), "clean_mt"], env=tsan_env, capture_output=True, text=True)
                mt_clean_ok = mt_clean.returncode == 0 and "ThreadSanitizer" not in (mt_clean.stderr or "")
                race_traps: dict[str, Any] = {}
                races_caught = True
                for rmode in ("trap_tsan_unmarked_st_rc_race", "trap_tsan_shared_sarray_mutation_race"):
                    rres = subprocess.run([str(tsan_bin), rmode], env=tsan_env, capture_output=True, text=True)
                    rcomb = (rres.stdout or "") + "\n" + (rres.stderr or "")
                    rcaught = rres.returncode != 0 and "ThreadSanitizer: data race" in rcomb
                    if not rcaught:
                        races_caught = False
                    race_traps[rmode] = {
                        "caught": rcaught,
                        "returncode": rres.returncode,
                    }
                tsan_ok = mt_clean_ok and races_caught
                tsan_report = {
                    "executed": True,
                    "cleanMtOk": mt_clean_ok,
                    "cleanMtReturncode": mt_clean.returncode,
                    "positiveRaceTraps": race_traps,
                }
            else:
                tsan_ok = not require_tsan
                tsan_report = {
                    "executed": False,
                    "skippedReason": f"host ASLR/VM map incompatible with TSan runtime (rc={probe_res.returncode})",
                    "stderrTail": (probe_res.stderr or "")[-400:],
                }
        else:
            tsan_ok = not require_tsan
            tsan_report = {
                "executed": False,
                "skippedReason": "clang++ -fsanitize=thread link unavailable",
                "stderrTail": (tsan_compile.stderr or "")[-400:],
            }

        asan_clean_ok = clean_res.returncode == 0 and clean_payload.get("ok") is True
        overall_ok = asan_clean_ok and traps_ok and tsan_ok
        return {
            "schemaVersion": "turbo-lean-heapobj-sanitizers-v1",
            "ok": overall_ok,
            "status": "passed" if overall_ok else "failed",
            "leanPrefix": str(lean_prefix),
            "clangxx": clangxx,
            "coreArtifacts": core_artifacts,
            "asanLsnUbsanClean": {
                "ok": asan_clean_ok,
                "returncode": clean_res.returncode,
                "payload": clean_payload,
                "stderrTail": (clean_res.stderr or "")[-600:],
            },
            "positiveSanitizerTraps": trap_results,
            "tsan": tsan_report,
        }


class HeapObjSanitizerSelfTests(unittest.TestCase):
    def test_toolchain_and_link_flags_discovery(self) -> None:
        pref = find_lean_prefix()
        self.assertIsNotNone(pref, "Expected Lean v4.35.0 prefix with include/lean/lean.h and libleanrt.a")
        assert pref is not None
        flags = lean_runtime_link_flags(pref)
        self.assertIn("-lleanrt", flags)
        self.assertIn("-lInit", flags)
        # Never inject `--wrap` hooks over `LEAN_MIMALLOC` symbols.
        self.assertFalse(any("--wrap" in f for f in flags))

    def test_full_asan_lsan_ubsan_tsan_and_positive_traps(self) -> None:
        report = run_sanitizer_suite(core_bin_arg=None, require_tsan=False)
        self.assertTrue(report["ok"], json.dumps(report, indent=2))
        self.assertTrue(report["asanLsnUbsanClean"]["ok"])
        self.assertEqual(report["asanLsnUbsanClean"]["payload"]["finalizerCalls"], 1)
        for trap_name, meta in report["positiveSanitizerTraps"].items():
            self.assertTrue(meta["caught"], f"Positive trap {trap_name} failed: {meta}")
        if report["tsan"].get("executed"):
            self.assertTrue(report["tsan"]["cleanMtOk"])
            for rname, rmeta in report["tsan"]["positiveRaceTraps"].items():
                self.assertTrue(rmeta["caught"], f"Positive TSan race trap {rname} failed: {rmeta}")

    def test_missing_explicit_core_bin_fails_closed(self) -> None:
        bad = run_sanitizer_suite(core_bin_arg="/nonexistent/lean-native-core", require_tsan=False)
        self.assertFalse(bad["ok"])
        self.assertEqual(bad["status"], "missing_requested_core_bin")

    def test_compiled_lnir_kernel_cabi_header_link_and_exec(self) -> None:
        with tempfile.TemporaryDirectory(prefix="turbo_stage5_mock_core_") as tmp:
            mock_core = Path(tmp) / "mock-lean-native-core"
            mock_core.write_text(
                "#!/usr/bin/env python3\n"
                "import sys\n"
                "from pathlib import Path\n"
                "args = sys.argv[1:]\n"
                "if args[0] == 'emit-cabi-bindings':\n"
                "    out = Path(args[args.index('--emit-header') + 1])\n"
                "    out.write_text('''#pragma once\n"
                "#ifndef LEAN_NATIVE_GENERATED_C_ABI_H\n"
                "#define LEAN_NATIVE_GENERATED_C_ABI_H\n"
                "#include <stdint.h>\n"
                "#include <stddef.h>\n"
                "typedef struct { const void* data; size_t len; size_t stride_bytes; } lean_native_flat_slice_t;\n"
                "typedef struct { void* data; size_t len; size_t cap; } lean_native_mut_slice_t;\n"
                "#ifdef __cplusplus\n"
                "extern \"C\" {\n"
                "#endif\n"
                "uint64_t collatz_steps(uint64_t n, uint64_t steps);\n"
                "void* sarray_scale_bias(void* arr, uint64_t scale, uint64_t bias);\n"
                "const uint64_t* evm_erc20_transfer_u256(void* mapVar, const uint64_t* senderSlot, const uint64_t* receiverSlot, const uint64_t* amount);\n"
                "#ifdef __cplusplus\n"
                "}\n"
                "#endif\n"
                "#endif\n''', encoding='utf-8')\n"
                "elif args[0] == 'compile-llvm':\n"
                "    out = Path(args[args.index('-o') + 1])\n"
                "    out.write_text('''target datalayout = \"e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128\"\n"
                "target triple = \"x86_64-unknown-linux-gnu\"\n"
                "declare void @lean_native_evm_sload(ptr, ptr, ptr)\n"
                "declare void @lean_native_evm_sstore(ptr, ptr, ptr)\n"
                "declare i64 @lean_native_trm_matryoshka_parity_u64(i64)\n"
                "define dso_local i64 @collatz_steps(i64 %n, i64 %steps) #0 {\n"
                "entry:\n"
                "  %acc0 = add i64 %n, %steps\n"
                "  ret i64 %acc0\n"
                "}\n"
                "define dso_local ptr @lean_native_abi_collatz_steps(ptr %a0, ptr %a1) #0 {\n"
                "entry:\n"
                "  %r0 = ptrtoint ptr %a0 to i64\n"
                "  %u0 = lshr i64 %r0, 1\n"
                "  %r1 = ptrtoint ptr %a1 to i64\n"
                "  %u1 = lshr i64 %r1, 1\n"
                "  %c = call i64 @collatz_steps(i64 %u0, i64 %u1)\n"
                "  %sh = shl i64 %c, 1\n"
                "  %tg = or i64 %sh, 1\n"
                "  %bp = inttoptr i64 %tg to ptr\n"
                "  ret ptr %bp\n"
                "}\n"
                "define dso_local ptr @sarray_scale_bias(ptr %arr, i64 %scale, i64 %bias) #0 {\n"
                "entry:\n"
                "  %data = getelementptr inbounds i8, ptr %arr, i64 24\n"
                "  %v0 = load i64, ptr %data, align 8\n"
                "  %m0 = mul i64 %v0, %scale\n"
                "  %a0 = add i64 %m0, %bias\n"
                "  store i64 %a0, ptr %data, align 8\n"
                "  %p3 = getelementptr inbounds i64, ptr %data, i64 3\n"
                "  %v3 = load i64, ptr %p3, align 8\n"
                "  %m3 = mul i64 %v3, %scale\n"
                "  %a3 = add i64 %m3, %bias\n"
                "  store i64 %a3, ptr %p3, align 8\n"
                "  ret ptr %arr\n"
                "}\n"
                "define dso_local void @evm_erc20_transfer_u256(ptr %out, ptr %map, ptr %s, ptr %r, ptr %amt) #0 {\n"
                "entry:\n"
                "  call void @lean_native_evm_sload(ptr %map, ptr %s, ptr %out)\n"
                "  call void @lean_native_evm_sstore(ptr %map, ptr %r, ptr %amt)\n"
                "  %par = call i64 @lean_native_trm_matryoshka_parity_u64(i64 7)\n"
                "  ret void\n"
                "}\n"
                "attributes #0 = { nounwind uwtable \"target-cpu\"=\"x86-64-v2\" }\n''', encoding='utf-8')\n",
                encoding="utf-8",
            )
            mock_core.chmod(0o755)
            report = run_sanitizer_suite(core_bin_arg=str(mock_core), require_tsan=False)
            self.assertTrue(report["ok"], json.dumps(report, indent=2))
            self.assertGreater(report["asanLsnUbsanClean"]["payload"]["kernelOut"], 0)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true", help="Run unit & live sanitizer trap self-tests")
    parser.add_argument("--core-bin", default=None, help="Optional path to `lean-native-core` for live CAbiEmit + LLVM IR link")
    parser.add_argument("--require-tsan", action="store_true", help="Fail closed if TSan cannot run on host")
    parser.add_argument("--json", action="store_true", help="Emit JSON report")
    args = parser.parse_args()

    if args.self_test:
        suite = unittest.defaultTestLoader.loadTestsFromTestCase(HeapObjSanitizerSelfTests)
        res = unittest.TextTestRunner(verbosity=2).run(suite)
        return 0 if res.wasSuccessful() else 1

    report = run_sanitizer_suite(
        core_bin_arg=args.core_bin,
        require_tsan=args.require_tsan or None,
    )
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(
            f"[heapobj-sanitizers] status={report['status']} "
            f"asan_clean={report.get('asanLsnUbsanClean', {}).get('ok')} "
            f"tsan_executed={report.get('tsan', {}).get('executed')}"
        )
        if not report["ok"]:
            print(json.dumps(report, indent=2, sort_keys=True), file=sys.stderr)
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
