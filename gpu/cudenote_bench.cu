#include <cuda_runtime.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <chrono>

#define CHECK_CUDA(call) do { \
    cudaError_t err = call; \
    if (err != cudaSuccess) { \
        fprintf(stderr, "CUDA Error at %s:%d - %s\n", __FILE__, __LINE__, cudaGetErrorString(err)); \
        exit(1); \
    } \
} while(0)

// 256-bit EVM Word in registers (little-endian limbs: w[0] is lowest 64 bits, w[3] is highest 64 bits)
struct u256 {
    uint64_t w[4];
};

__host__ __device__ __forceinline__ u256 u256_zero() {
    return {{0ULL, 0ULL, 0ULL, 0ULL}};
}

__host__ __device__ __forceinline__ u256 u256_from_u64(uint64_t x) {
    return {{x, 0ULL, 0ULL, 0ULL}};
}

__host__ __device__ __forceinline__ u256 u256_max_u128() {
    return {{0xFFFFFFFFFFFFFFFFULL, 0xFFFFFFFFFFFFFFFFULL, 0ULL, 0ULL}};
}

__host__ __device__ __forceinline__ bool u256_is_zero(const u256& a) {
    return (a.w[0] | a.w[1] | a.w[2] | a.w[3]) == 0ULL;
}

__host__ __device__ __forceinline__ bool u256_eq(const u256& a, const u256& b) {
    return ((a.w[0] ^ b.w[0]) | (a.w[1] ^ b.w[1]) | (a.w[2] ^ b.w[2]) | (a.w[3] ^ b.w[3])) == 0ULL;
}

__host__ __device__ __forceinline__ bool u256_lt(const u256& a, const u256& b) {
    if (a.w[3] != b.w[3]) return a.w[3] < b.w[3];
    if (a.w[2] != b.w[2]) return a.w[2] < b.w[2];
    if (a.w[1] != b.w[1]) return a.w[1] < b.w[1];
    return a.w[0] < b.w[0];
}

__host__ __device__ __forceinline__ bool u256_gt(const u256& a, const u256& b) {
    return u256_lt(b, a);
}

// 256-bit checked add: returns true on overflow (Panic 0x11)
__host__ __device__ __forceinline__ bool u256_add_checked(const u256& a, const u256& b, u256& out) {
    uint64_t c = 0;
    #pragma unroll
    for (int i = 0; i < 4; i++) {
        uint64_t sum1 = a.w[i] + b.w[i];
        uint64_t c1 = (sum1 < a.w[i]);
        uint64_t sum2 = sum1 + c;
        uint64_t c2 = (sum2 < sum1);
        out.w[i] = sum2;
        c = c1 | c2;
    }
    return c != 0;
}

// 256-bit checked sub: returns true on underflow (Panic 0x11)
__host__ __device__ __forceinline__ bool u256_sub_checked(const u256& a, const u256& b, u256& out) {
    uint64_t borrow = 0;
    #pragma unroll
    for (int i = 0; i < 4; i++) {
        uint64_t diff1 = a.w[i] - b.w[i];
        uint64_t b1 = (a.w[i] < b.w[i]);
        uint64_t b2 = (diff1 < borrow);
        out.w[i] = diff1 - borrow;
        borrow = b1 | b2;
    }
    return borrow != 0;
}

// 256-bit wrapping sub
__host__ __device__ __forceinline__ u256 u256_sub_wrap(const u256& a, const u256& b) {
    u256 out;
    u256_sub_checked(a, b, out);
    return out;
}

// 64x64 -> 128 bit multiply helper
__host__ __device__ __forceinline__ void mul64(uint64_t a, uint64_t b, uint64_t& lo, uint64_t& hi) {
#ifdef __CUDA_ARCH__
    lo = a * b;
    hi = __umul64hi(a, b);
#else
    unsigned __int128 prod = (unsigned __int128)a * b;
    lo = (uint64_t)prod;
    hi = (uint64_t)(prod >> 64);
#endif
}

// 256-bit checked multiplication: returns true on 256-bit overflow
__host__ __device__ __forceinline__ bool u256_mul_checked(const u256& a, const u256& b, u256& out) {
    if (((a.w[2] | a.w[3] | b.w[2] | b.w[3]) == 0ULL)) {
        uint64_t p00_lo, p00_hi, p01_lo, p01_hi, p10_lo, p10_hi, p11_lo, p11_hi;
        mul64(a.w[0], b.w[0], p00_lo, p00_hi);
        mul64(a.w[0], b.w[1], p01_lo, p01_hi);
        mul64(a.w[1], b.w[0], p10_lo, p10_hi);
        mul64(a.w[1], b.w[1], p11_lo, p11_hi);

        out.w[0] = p00_lo;

        uint64_t s1 = p00_hi + p01_lo;
        uint64_t c1 = (s1 < p00_hi);
        uint64_t s2 = s1 + p10_lo;
        c1 += (s2 < s1);
        out.w[1] = s2;

        uint64_t s3 = p01_hi + p10_hi + c1;
        uint64_t s4 = s3 + p11_lo;
        uint64_t c2 = (s4 < s3);
        out.w[2] = s4;
        out.w[3] = p11_hi + c2;
        return false;
    }

    uint64_t acc[8] = {0};
    bool overflow = false;
    for (int i = 0; i < 4; i++) {
        if (a.w[i] == 0) continue;
        uint64_t carry = 0;
        for (int j = 0; j < 4; j++) {
            uint64_t lo, hi;
            mul64(a.w[i], b.w[j], lo, hi);
            uint64_t s1 = acc[i + j] + lo;
            uint64_t c1 = (s1 < acc[i + j]);
            uint64_t s2 = s1 + carry;
            uint64_t c2 = (s2 < s1);
            acc[i + j] = s2;
            carry = hi + c1 + c2;
        }
        acc[i + 4] += carry;
    }
    for (int k = 4; k < 8; k++) {
        if (acc[k] != 0) overflow = true;
    }
    out.w[0] = acc[0]; out.w[1] = acc[1]; out.w[2] = acc[2]; out.w[3] = acc[3];
    return overflow;
}

// 256-bit division: returns true on division by zero (Panic 0x12)
__host__ __device__ __forceinline__ bool u256_div_checked(const u256& num, const u256& den, u256& quot) {
    if (u256_is_zero(den)) return true;
    if ((num.w[2] | num.w[3] | den.w[1] | den.w[2] | den.w[3]) == 0ULL) {
        if (num.w[1] == 0ULL) {
            quot = {{num.w[0] / den.w[0], 0ULL, 0ULL, 0ULL}};
            return false;
        }
    }
    u256 q = u256_zero();
    u256 r = u256_zero();
    int highest_bit = 255;
    if (num.w[3] == 0) {
        if (num.w[2] == 0) {
            highest_bit = (num.w[1] == 0) ? 63 : 127;
        } else {
            highest_bit = 191;
        }
    }
    for (int i = highest_bit; i >= 0; i--) {
        r.w[3] = (r.w[3] << 1) | (r.w[2] >> 63);
        r.w[2] = (r.w[2] << 1) | (r.w[1] >> 63);
        r.w[1] = (r.w[1] << 1) | (r.w[0] >> 63);
        uint64_t bit = (num.w[i >> 6] >> (i & 63)) & 1ULL;
        r.w[0] = (r.w[0] << 1) | bit;
        if (!u256_lt(r, den)) {
            r = u256_sub_wrap(r, den);
            q.w[i >> 6] |= (1ULL << (i & 63));
        }
    }
    quot = q;
    return false;
}

// Packed 128-bit struct helpers matching `packHalves` and `structMember` in Verity Denote
__host__ __device__ __forceinline__ u256 packHalves(uint64_t lo0, uint64_t lo1, uint64_t hi0, uint64_t hi1) {
    return {{lo0, lo1, hi0, hi1}};
}

__host__ __device__ __forceinline__ u256 unpackLo128(const u256& slotWord) {
    return {{slotWord.w[0], slotWord.w[1], 0ULL, 0ULL}};
}

__host__ __device__ __forceinline__ u256 unpackHi128(const u256& slotWord) {
    return {{slotWord.w[2], slotWord.w[3], 0ULL, 0ULL}};
}

__host__ __device__ __forceinline__ u256 mask128(const u256& val) {
    return {{val.w[0], val.w[1], 0ULL, 0ULL}};
}

// mulDivDown(x, y, d) = (x * y) / d with Solidity 0.8.34 overflow & div-by-zero panic checks
__host__ __device__ __forceinline__ bool mulDivDown(const u256& x, const u256& y, const u256& d, u256& out) {
    u256 prod;
    if (u256_mul_checked(x, y, prod)) return true;
    if (u256_div_checked(prod, d, out)) return true;
    return false;
}

// mulDivUp(x, y, d) = (x * y + (d - 1)) / d with Solidity 0.8.34 overflow & div-by-zero panic checks
__host__ __device__ __forceinline__ bool mulDivUp(const u256& x, const u256& y, const u256& d, u256& out) {
    u256 prod, dm1, num;
    if (u256_mul_checked(x, y, prod)) return true;
    if (u256_sub_checked(d, u256_from_u64(1), dm1)) return true;
    if (u256_add_checked(prod, dm1, num)) return true;
    if (u256_div_checked(num, d, out)) return true;
    return false;
}

// Yul assembly L.min(x, y) := xor(x, mul(xor(x, y), lt(y, x)))
__host__ __device__ __forceinline__ u256 yul_min(const u256& x, const u256& y) {
    uint64_t cond = u256_lt(y, x) ? 0xFFFFFFFFFFFFFFFFULL : 0ULL;
    u256 out;
    out.w[0] = x.w[0] ^ ((x.w[0] ^ y.w[0]) & cond);
    out.w[1] = x.w[1] ^ ((x.w[1] ^ y.w[1]) & cond);
    out.w[2] = x.w[2] ^ ((x.w[2] ^ y.w[2]) & cond);
    out.w[3] = x.w[3] ^ ((x.w[3] ^ y.w[3]) & cond);
    return out;
}

struct DenoteResult {
    bool success;
    u256 ret0;
    u256 ret1;
    u256 ret2;
};

struct SliceTx {
    u256 slot5;      // packHalves(credit, pendingFee)
    u256 slot6;      // packHalves(lastLossFactor, lastAccrual)
    u256 slot3;      // packHalves(totalUnits, lossFactor)
    u256 timestamp;  // block.timestamp
    u256 maturity;   // m.maturity
};

// Execute `denoteFunction` on `Slice.sol` with mutant_id == 0 (baseline) or 1..293 (293 semantic mutants)
__host__ __device__ __forceinline__ DenoteResult denote_slice_f(const SliceTx& tx, int mutant_id) {
    DenoteResult res = {false, u256_zero(), u256_zero(), u256_zero()};

    // Group 0: Storage layout & packed bit-field extraction mutants (mutants 1..40)
    u256 slot5 = tx.slot5;
    u256 slot6 = tx.slot6;
    u256 slot3 = tx.slot3;
    if (mutant_id == 1) slot5 = tx.slot6; // import-scalar-slot / swap slot 5 and 6
    if (mutant_id == 2) slot6 = tx.slot5;
    if (mutant_id == 3) slot3 = tx.slot5;

    u256 credit      = (mutant_id == 4) ? unpackHi128(slot5) : unpackLo128(slot5); // swap_layout / change_field
    u256 pending     = (mutant_id == 5) ? unpackLo128(slot5) : unpackHi128(slot5);
    u256 lastLoss    = (mutant_id == 6) ? unpackHi128(slot6) : unpackLo128(slot6);
    u256 lastAccrual = (mutant_id == 7) ? unpackLo128(slot6) : unpackHi128(slot6);
    u256 lossFactor  = (mutant_id == 8) ? unpackLo128(slot3) : unpackHi128(slot3);

    // Mask width mutations (mutants 9..24: denote-packed-mask / sibling mask / offset)
    if (mutant_id >= 9 && mutant_id <= 16) {
        uint64_t bad_mask = ~(1ULL << (mutant_id - 9));
        credit.w[0] &= bad_mask;
    }
    if (mutant_id >= 17 && mutant_id <= 24) {
        uint64_t bad_mask = ~(1ULL << (mutant_id - 17));
        pending.w[0] &= bad_mask;
    }
    if (mutant_id >= 25 && mutant_id <= 32) {
        credit.w[0] >>= (mutant_id - 24);
    }
    if (mutant_id >= 33 && mutant_id <= 40) {
        lossFactor.w[0] ^= (uint64_t)(mutant_id - 32);
    }

    u256 u128_max = u256_max_u128();
    if (mutant_id == 41) u128_max.w[0] -= 1;

    // Step 1: post = lastLoss < type(uint128).max ? credit.mulDivDown(u128_max - lossFactor, u128_max - lastLoss) : 0
    bool cond1 = u256_lt(lastLoss, u128_max);
    if (mutant_id == 42) cond1 = !cond1; // import-if-root-swap
    if (mutant_id == 43) cond1 = u256_gt(lastLoss, u128_max); // import-comparison
    if (mutant_id == 44) cond1 = true;

    u256 post = u256_zero();
    if (cond1) {
        u256 num1, den1;
        if (u256_sub_checked(u128_max, lossFactor, num1)) return res;
        if (u256_sub_checked(u128_max, lastLoss, den1)) return res;
        if (mutant_id >= 45 && mutant_id <= 75) {
            u256 delta = u256_from_u64((uint64_t)(mutant_id - 44));
            u256_sub_checked(num1, delta, num1);
        }
        if (mutant_id >= 76 && mutant_id <= 95) {
            if (mulDivUp(credit, num1, den1, post)) return res;
            u256 extra = u256_from_u64((uint64_t)(mutant_id - 74));
            u256_div_checked(post, extra, post);
        } else {
            if (mulDivDown(credit, num1, den1, post)) return res;
        }
    }

    // Step 2: postFee = credit > 0 ? pending - pending.mulDivUp(credit - post, credit) : 0
    bool cond2 = u256_gt(credit, u256_zero());
    if (mutant_id == 96) cond2 = !cond2;
    if (mutant_id == 97) cond2 = u256_eq(credit, u256_zero());

    u256 postFee = u256_zero();
    if (cond2) {
        u256 diff_cp, fee_reduction;
        if (u256_sub_checked(credit, post, diff_cp)) return res;
        if (mutant_id >= 98 && mutant_id <= 130) {
            u256 perturbed = diff_cp;
            perturbed.w[0] += (uint64_t)(mutant_id - 97);
            if (mulDivDown(pending, perturbed, credit, fee_reduction)) return res;
        } else {
            if (mulDivUp(pending, diff_cp, credit, fee_reduction)) return res;
        }
        if (u256_sub_checked(pending, fee_reduction, postFee)) return res;
    }

    // Step 3: end = L.min(block.timestamp, m.maturity)
    u256 timestamp = tx.timestamp;
    u256 maturity = tx.maturity;
    if (mutant_id == 131) timestamp = maturity;
    if (mutant_id == 132) timestamp.w[0] += 1;
    if (mutant_id >= 133 && mutant_id <= 160) {
        maturity.w[0] += (uint64_t)(mutant_id - 132);
    }

    u256 end = yul_min(timestamp, maturity);
    if (mutant_id >= 161 && mutant_id <= 180) {
        end = u256_lt(timestamp, maturity) ? maturity : timestamp;
        end.w[0] ^= (uint64_t)(mutant_id - 160);
    }

    // Step 4: fee = lastAccrual < m.maturity ? uint128(postFee.mulDivDown(end - lastAccrual, m.maturity - lastAccrual)) : 0
    bool cond3 = u256_lt(lastAccrual, maturity);
    if (mutant_id == 181) cond3 = !cond3;
    if (mutant_id == 182) cond3 = u256_lt(maturity, lastAccrual);

    u256 fee = u256_zero();
    if (cond3) {
        u256 elapsed, total_dur, raw_fee;
        if (u256_sub_checked(end, lastAccrual, elapsed)) return res;
        if (u256_sub_checked(maturity, lastAccrual, total_dur)) return res;
        if (mutant_id >= 183 && mutant_id <= 230) {
            u256 boost = u256_from_u64((uint64_t)(mutant_id - 182));
            if (u256_add_checked(elapsed, boost, elapsed)) return res;
        }
        if (mutant_id >= 231 && mutant_id <= 260) {
            u256 boost = u256_from_u64((uint64_t)(mutant_id - 230));
            if (u256_add_checked(total_dur, boost, total_dur)) return res;
        }
        if (mulDivDown(postFee, elapsed, total_dur, raw_fee)) return res;
        fee = mask128(raw_fee);
        if (mutant_id >= 261 && mutant_id <= 275) {
            fee.w[0] ^= (uint64_t)(mutant_id - 260);
        }
    }

    // Step 5: return (uint128(post) - fee, uint128(postFee) - fee, fee)
    u256 post128 = mask128(post);
    u256 postFee128 = mask128(postFee);
    u256 ret0, ret1;
    if (u256_sub_checked(post128, fee, ret0)) return res;
    if (u256_sub_checked(postFee128, fee, ret1)) return res;
    u256 ret2 = fee;

    if (mutant_id == 276) { u256 tmp = ret0; ret0 = ret2; ret2 = tmp; }
    else if (mutant_id == 277) { u256 tmp = ret0; ret0 = ret1; ret1 = tmp; }
    else if (mutant_id == 278) { u256 tmp = ret1; ret1 = ret2; ret2 = tmp; }
    else if (mutant_id >= 279 && mutant_id <= 293) {
        ret0.w[0] ^= (uint64_t)(mutant_id - 278);
    }

    res.success = true;
    res.ret0 = ret0;
    res.ret1 = ret1;
    res.ret2 = ret2;
    return res;
}

// ============================================================================
// Benchmark 1a: Fast-Reject 256-bit Lemma Fuzzing Kernel
// Uses warp-level __ballot_sync + single per-warp atomicAdd to avoid atomic contention
// ============================================================================
__global__ void fast_reject_lemma_kernel(
    uint64_t n_states,
    uint64_t seed,
    unsigned int* __restrict__ valid_lemma_violations,
    unsigned int* __restrict__ buggy_rounding_violations,
    unsigned int* __restrict__ buggy_overflow_violations,
    uint64_t* __restrict__ first_counterexample_idx
) {
    uint64_t idx = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x;
    bool active = (idx < n_states);

    bool v_viol = false;
    bool r_viol = false;
    bool o_viol = false;

    if (active) {
        uint64_t z = idx + seed;
        z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
        z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
        uint64_t r0 = z ^ (z >> 31);

        z = (r0 + 0x9e3779b97f4a7c15ULL);
        z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
        z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
        uint64_t r1 = z ^ (z >> 31);

        uint64_t credit_lo  = (r0 & 0xFFFFFFFFFFFFULL) + 1ULL;
        uint64_t pending_lo = ((r0 >> 16) & 0xFFFFFFFFFFULL) + 1ULL;
        uint64_t lastLoss_lo = (r1 & 0xFFFFFFULL);
        uint64_t lossFactor_lo = lastLoss_lo + ((r1 >> 24) & 0xFFFFULL);
        uint64_t lastAccrual_lo = (r1 >> 40) & 0xFFFFULL;
        uint64_t maturity_lo = lastAccrual_lo + ((r0 >> 48) & 0xFFFFULL) + 1ULL;
        uint64_t timestamp_lo = lastAccrual_lo + ((r1 >> 48) & 0xFFFFULL);

        SliceTx tx;
        tx.slot5 = packHalves(credit_lo, 0ULL, pending_lo, 0ULL);
        tx.slot6 = packHalves(lastLoss_lo, 0ULL, lastAccrual_lo, 0ULL);
        tx.slot3 = packHalves(0ULL, 0ULL, lossFactor_lo, 0ULL);
        tx.timestamp = u256_from_u64(timestamp_lo);
        tx.maturity  = u256_from_u64(maturity_lo);

        DenoteResult res = denote_slice_f(tx, 0);

        if (res.success) {
            u256 sum_fee;
            bool ovf = u256_add_checked(res.ret1, res.ret2, sum_fee);
            if (ovf || u256_gt(sum_fee, u256_from_u64(pending_lo)) || u256_gt(res.ret0, u256_from_u64(credit_lo))) {
                v_viol = true;
            }

            DenoteResult buggy_round = denote_slice_f(tx, 98);
            if (!u256_eq(res.ret1, buggy_round.ret1)) {
                r_viol = true;
            }
        }

        SliceTx unguarded_tx = tx;
        unguarded_tx.timestamp = u256_from_u64(r0 & 0xFFFFULL);
        DenoteResult res_unguarded = denote_slice_f(unguarded_tx, 0);
        if (!res_unguarded.success) {
            o_viol = true;
        }
    }

    // Warp-aggregated reductions
    unsigned int mask_v = __ballot_sync(0xFFFFFFFFU, v_viol);
    unsigned int mask_r = __ballot_sync(0xFFFFFFFFU, r_viol);
    unsigned int mask_o = __ballot_sync(0xFFFFFFFFU, o_viol);
    int lane = threadIdx.x & 31;
    if (lane == 0) {
        if (mask_v) atomicAdd(valid_lemma_violations, __popc(mask_v));
        if (mask_r) {
            unsigned int old = atomicAdd(buggy_rounding_violations, __popc(mask_r));
            if (old == 0) {
                int first_lane = __ffs(mask_r) - 1;
                atomicMin((unsigned long long*)first_counterexample_idx, (unsigned long long)(idx + first_lane));
            }
        }
        if (mask_o) atomicAdd(buggy_overflow_violations, __popc(mask_o));
    }
}

// Pure Valid-Lemma Fast-Check Kernel (single Denote + invariant check per state)
__global__ void fast_check_valid_lemma_only_kernel(
    uint64_t n_states,
    uint64_t seed,
    unsigned int* __restrict__ valid_lemma_violations
) {
    uint64_t idx = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x;
    bool v_viol = false;
    if (idx < n_states) {
        uint64_t z = idx + seed;
        z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
        z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
        uint64_t r0 = z ^ (z >> 31);

        z = (r0 + 0x9e3779b97f4a7c15ULL);
        z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
        z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
        uint64_t r1 = z ^ (z >> 31);

        uint64_t credit_lo  = (r0 & 0xFFFFFFFFFFFFULL) + 1ULL;
        uint64_t pending_lo = ((r0 >> 16) & 0xFFFFFFFFFFULL) + 1ULL;
        uint64_t lastLoss_lo = (r1 & 0xFFFFFFULL);
        uint64_t lossFactor_lo = lastLoss_lo + ((r1 >> 24) & 0xFFFFULL);
        uint64_t lastAccrual_lo = (r1 >> 40) & 0xFFFFULL;
        uint64_t maturity_lo = lastAccrual_lo + ((r0 >> 48) & 0xFFFFULL) + 1ULL;
        uint64_t timestamp_lo = lastAccrual_lo + ((r1 >> 48) & 0xFFFFULL);

        SliceTx tx;
        tx.slot5 = packHalves(credit_lo, 0ULL, pending_lo, 0ULL);
        tx.slot6 = packHalves(lastLoss_lo, 0ULL, lastAccrual_lo, 0ULL);
        tx.slot3 = packHalves(0ULL, 0ULL, lossFactor_lo, 0ULL);
        tx.timestamp = u256_from_u64(timestamp_lo);
        tx.maturity  = u256_from_u64(maturity_lo);

        DenoteResult res = denote_slice_f(tx, 0);
        if (res.success) {
            u256 sum_fee;
            bool ovf = u256_add_checked(res.ret1, res.ret2, sum_fee);
            if (ovf || u256_gt(sum_fee, u256_from_u64(pending_lo)) || u256_gt(res.ret0, u256_from_u64(credit_lo))) {
                v_viol = true;
            }
        }
    }
    unsigned int mask_v = __ballot_sync(0xFFFFFFFFU, v_viol);
    if ((threadIdx.x & 31) == 0 && mask_v) {
        atomicAdd(valid_lemma_violations, __popc(mask_v));
    }
}

// ============================================================================
// Benchmark 1b: Parallel Mutation Campaign (`CuMutate`)
// ============================================================================
__global__ void cumutate_campaign_kernel(
    const SliceTx* __restrict__ txs,
    const DenoteResult* __restrict__ baseline_out,
    int num_txs,
    int num_mutants,
    unsigned int* __restrict__ mutant_killed_counts
) {
    int tx_idx = blockIdx.x * blockDim.x + threadIdx.x;
    int mutant_id = blockIdx.y + 1;
    bool diverged = false;
    if (tx_idx < num_txs && mutant_id <= num_mutants) {
        SliceTx tx = txs[tx_idx];
        DenoteResult base = baseline_out[tx_idx];
        DenoteResult mut_res = denote_slice_f(tx, mutant_id);

        diverged = (base.success != mut_res.success) ||
                   (base.success && (!u256_eq(base.ret0, mut_res.ret0) ||
                                     !u256_eq(base.ret1, mut_res.ret1) ||
                                     !u256_eq(base.ret2, mut_res.ret2)));
    }
    unsigned int mask = __ballot_sync(0xFFFFFFFFU, diverged);
    if ((threadIdx.x & 31) == 0 && mask) {
        atomicAdd(&mutant_killed_counts[mutant_id - 1], __popc(mask));
    }
}

int main() {
    cudaDeviceProp prop;
    CHECK_CUDA(cudaGetDeviceProperties(&prop, 0));
    printf("=== CuDenote GPU Benchmark on %s (Compute Capability %d.%d, %d SMs) ===\n",
           prop.name, prop.major, prop.minor, prop.multiProcessorCount);

    // 1. Verify exact golden witnesses from `scripts/solidity_import_mutations.py`:
    SliceTx wA = {
        packHalves(100, 0, 10, 0),
        packHalves(0, 0, 0, 0),
        packHalves(0, 0, 0, 0),
        u256_from_u64(50),
        u256_from_u64(100)
    };
    DenoteResult rA = denote_slice_f(wA, 0);
    printf("Witness A (expected success=1, [95, 5, 5]): success=%d, [%llu, %llu, %llu]\n",
           rA.success,
           (unsigned long long)rA.ret0.w[0],
           (unsigned long long)rA.ret1.w[0],
           (unsigned long long)rA.ret2.w[0]);

    SliceTx wB = {
        packHalves(1, 0, 2, 0),
        packHalves(0, 0, 0, 0),
        packHalves(0, 0, 0, 0),
        u256_from_u64(1),
        u256_from_u64(1)
    };
    DenoteResult rB = denote_slice_f(wB, 0);
    printf("Witness B (expected success=0 / Panic 0x11): success=%d\n", rB.success);

    unsigned int *d_valid_viol, *d_buggy_round, *d_buggy_ovf;
    uint64_t *d_first_ce;
    CHECK_CUDA(cudaMalloc(&d_valid_viol, sizeof(unsigned int)));
    CHECK_CUDA(cudaMalloc(&d_buggy_round, sizeof(unsigned int)));
    CHECK_CUDA(cudaMalloc(&d_buggy_ovf, sizeof(unsigned int)));
    CHECK_CUDA(cudaMalloc(&d_first_ce, sizeof(uint64_t)));

    cudaEvent_t start, stop;
    CHECK_CUDA(cudaEventCreate(&start));
    CHECK_CUDA(cudaEventCreate(&stop));

    // Warmup
    fast_reject_lemma_kernel<<<(1000000 + 255) / 256, 256>>>(
        1000000ULL, 42ULL, d_valid_viol, d_buggy_round, d_buggy_ovf, d_first_ce);
    CHECK_CUDA(cudaDeviceSynchronize());

    // Benchmark 1a: 1,000,000 and 10,000,000 states (both single-lemma fast-check and 3-lemma differential fuzzing)
    uint64_t counts[2] = {1000000ULL, 10000000ULL};
    for (int c = 0; c < 2; c++) {
        uint64_t N = counts[c];
        int threads = 256;
        int blocks = (int)((N + threads - 1) / threads);
        int iters = 20;

        // Single-lemma valid invariant check
        float single_total_ms = 0.0f;
        for (int it = 0; it < iters; it++) {
            CHECK_CUDA(cudaMemset(d_valid_viol, 0, sizeof(unsigned int)));
            CHECK_CUDA(cudaEventRecord(start));
            fast_check_valid_lemma_only_kernel<<<blocks, threads>>>(N, 1337ULL + it, d_valid_viol);
            CHECK_CUDA(cudaEventRecord(stop));
            CHECK_CUDA(cudaEventSynchronize(stop));
            float ms = 0.0f;
            CHECK_CUDA(cudaEventElapsedTime(&ms, start, stop));
            single_total_ms += ms;
        }
        float single_avg_ms = single_total_ms / iters;
        double single_mstates_s = (double)N / (single_avg_ms * 1e3);

        // 3-lemma suite (Valid Invariant + Buggy Rounding Counterexample + Buggy Underflow Counterexample)
        float total_ms = 0.0f;
        for (int it = 0; it < iters; it++) {
            CHECK_CUDA(cudaMemset(d_valid_viol, 0, sizeof(unsigned int)));
            CHECK_CUDA(cudaMemset(d_buggy_round, 0, sizeof(unsigned int)));
            CHECK_CUDA(cudaMemset(d_buggy_ovf, 0, sizeof(unsigned int)));
            CHECK_CUDA(cudaMemset(d_first_ce, 0xFF, sizeof(uint64_t)));

            CHECK_CUDA(cudaEventRecord(start));
            fast_reject_lemma_kernel<<<blocks, threads>>>(
                N, 1337ULL + it, d_valid_viol, d_buggy_round, d_buggy_ovf, d_first_ce);
            CHECK_CUDA(cudaEventRecord(stop));
            CHECK_CUDA(cudaEventSynchronize(stop));
            float ms = 0.0f;
            CHECK_CUDA(cudaEventElapsedTime(&ms, start, stop));
            total_ms += ms;
        }
        float avg_ms = total_ms / iters;
        unsigned int h_valid = 0, h_round = 0, h_ovf = 0;
        uint64_t h_ce = 0;
        CHECK_CUDA(cudaMemcpy(&h_valid, d_valid_viol, sizeof(unsigned int), cudaMemcpyDeviceToHost));
        CHECK_CUDA(cudaMemcpy(&h_round, d_buggy_round, sizeof(unsigned int), cudaMemcpyDeviceToHost));
        CHECK_CUDA(cudaMemcpy(&h_ovf, d_buggy_ovf, sizeof(unsigned int), cudaMemcpyDeviceToHost));
        CHECK_CUDA(cudaMemcpy(&h_ce, d_first_ce, sizeof(uint64_t), cudaMemcpyDeviceToHost));

        double mstates_per_sec = (double)N / (avg_ms * 1e3);
        printf("[Fast-Check Valid Lemma (%llu states)] Time: %.4f ms (%.1f us) | Throughput: %.2f M states/s (%.2f B states/s)\n",
               (unsigned long long)N, single_avg_ms, single_avg_ms * 1000.0f, single_mstates_s, single_mstates_s / 1000.0);
        printf("[Fast-Reject 3-Lemma Suite (%llu states)] Time: %.4f ms (%.1f us) | Throughput: %.2f M states/s (%.2f M Denote-evals/s)\n",
               (unsigned long long)N, avg_ms, avg_ms * 1000.0f, mstates_per_sec, mstates_per_sec * 3.0);
        printf("  -> Valid Lemma Violations: %u | Buggy Rounding Counterexamples: %u (first at idx=%llu) | Unguarded Underflow Counterexamples: %u\n",
               h_valid, h_round, (unsigned long long)h_ce, h_ovf);
    }

    // Benchmark 1b: Parallel Mutation Campaign (293 semantic mutants x 10,000 transactions = 2.93M executions)
    const int NUM_TXS = 10000;
    const int NUM_MUTANTS = 293;
    SliceTx* h_txs = (SliceTx*)malloc(NUM_TXS * sizeof(SliceTx));
    DenoteResult* h_base = (DenoteResult*)malloc(NUM_TXS * sizeof(DenoteResult));

    h_txs[0] = wA;
    h_txs[1] = wB;
    // Edge-case transaction 2: lastLoss == uint128.max (triggers mutant 41 & 44)
    h_txs[2] = {
        packHalves(1000, 0, 50, 0),
        packHalves(0xFFFFFFFFFFFFFFFFULL, 0xFFFFFFFFFFFFFFFFULL, 10, 0),
        packHalves(0, 0, 0, 0),
        u256_from_u64(50),
        u256_from_u64(100)
    };
    for (int i = 3; i < NUM_TXS; i++) {
        uint64_t z = (uint64_t)i * 0x9e3779b97f4a7c15ULL;
        z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
        z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
        uint64_t r0 = z ^ (z >> 31);

        uint64_t credit = (r0 & 0xFFFFFULL) + 100ULL;
        uint64_t pending = ((r0 >> 20) & 0xFFFFULL) + 10ULL;
        uint64_t lastLoss = ((r0 >> 36) & 0xFFFULL);
        uint64_t lossFactor = lastLoss + ((r0 >> 48) & 0xFFFULL);
        uint64_t lastAccrual = (i % 50);
        uint64_t maturity = lastAccrual + 100 + (i % 200);
        uint64_t timestamp = lastAccrual + (i % 150);

        h_txs[i].slot5 = packHalves(credit, 0, pending, 0);
        h_txs[i].slot6 = packHalves(lastLoss, 0, lastAccrual, 0);
        h_txs[i].slot3 = packHalves(0, 0, lossFactor, 0);
        h_txs[i].timestamp = u256_from_u64(timestamp);
        h_txs[i].maturity = u256_from_u64(maturity);
    }
    for (int i = 0; i < NUM_TXS; i++) {
        h_base[i] = denote_slice_f(h_txs[i], 0);
    }

    SliceTx* d_txs;
    DenoteResult* d_base;
    unsigned int* d_killed;
    CHECK_CUDA(cudaMalloc(&d_txs, NUM_TXS * sizeof(SliceTx)));
    CHECK_CUDA(cudaMalloc(&d_base, NUM_TXS * sizeof(DenoteResult)));
    CHECK_CUDA(cudaMalloc(&d_killed, NUM_MUTANTS * sizeof(unsigned int)));

    CHECK_CUDA(cudaMemcpy(d_txs, h_txs, NUM_TXS * sizeof(SliceTx), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_base, h_base, NUM_TXS * sizeof(DenoteResult), cudaMemcpyHostToDevice));

    dim3 threads(256, 1);
    dim3 grid((NUM_TXS + 255) / 256, NUM_MUTANTS);

    // Warmup
    CHECK_CUDA(cudaMemset(d_killed, 0, NUM_MUTANTS * sizeof(unsigned int)));
    cumutate_campaign_kernel<<<grid, threads>>>(d_txs, d_base, NUM_TXS, NUM_MUTANTS, d_killed);
    CHECK_CUDA(cudaDeviceSynchronize());

    float mut_total_ms = 0.0f;
    int mut_iters = 20;
    for (int it = 0; it < mut_iters; it++) {
        CHECK_CUDA(cudaMemset(d_killed, 0, NUM_MUTANTS * sizeof(unsigned int)));
        CHECK_CUDA(cudaEventRecord(start));
        cumutate_campaign_kernel<<<grid, threads>>>(d_txs, d_base, NUM_TXS, NUM_MUTANTS, d_killed);
        CHECK_CUDA(cudaEventRecord(stop));
        CHECK_CUDA(cudaEventSynchronize(stop));
        float ms = 0.0f;
        CHECK_CUDA(cudaEventElapsedTime(&ms, start, stop));
        mut_total_ms += ms;
    }
    float mut_avg_ms = mut_total_ms / mut_iters;

    unsigned int h_killed[NUM_MUTANTS];
    CHECK_CUDA(cudaMemcpy(h_killed, d_killed, NUM_MUTANTS * sizeof(unsigned int), cudaMemcpyDeviceToHost));
    int killed_mutants = 0;
    unsigned long long total_divergences = 0;
    for (int m = 0; m < NUM_MUTANTS; m++) {
        if (h_killed[m] > 0) killed_mutants++;
        total_divergences += h_killed[m];
    }

    double evals = (double)NUM_TXS * NUM_MUTANTS;
    double mut_throughput = evals / (mut_avg_ms * 1e3);
    printf("[CuMutate Campaign: %d mutants x %d txs = %d Denote evaluations]\n",
           NUM_MUTANTS, NUM_TXS, NUM_TXS * NUM_MUTANTS);
    printf("  -> Kernel Time: %.4f ms (%.1f us) | Throughput: %.2f M Denote-evals/s (%.2f B Denote-evals/s)\n",
           mut_avg_ms, mut_avg_ms * 1000.0f, mut_throughput, mut_throughput / 1000.0);
    printf("  -> Mutants Killed: %d / %d (%.1f%%) | Total diverging (mutant, tx) pairs: %llu\n",
           killed_mutants, NUM_MUTANTS, 100.0 * killed_mutants / NUM_MUTANTS, total_divergences);

    free(h_txs);
    free(h_base);
    cudaFree(d_txs);
    cudaFree(d_base);
    cudaFree(d_killed);
    cudaFree(d_valid_viol);
    cudaFree(d_buggy_round);
    cudaFree(d_buggy_ovf);
    cudaFree(d_first_ce);
    return 0;
}
