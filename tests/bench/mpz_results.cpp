/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kim Morrison
*/
#include <lean/lean.h>
#include <gmp.h>
#include <algorithm>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <memory>
#include <string>
#include <vector>

extern "C" void lean_initialize_runtime_module();
extern "C" lean_object * lean_alloc_mpz(mpz_t);
extern "C" void lean_extract_mpz_value(lean_object *, mpz_t);

using Clock = std::chrono::steady_clock;
static volatile size_t sink;
static size_t allocations, reallocations, frees, bytes;
static size_t live_bytes, retained_bytes, peak_bytes;
static bool counting;
static void * counted_alloc(size_t n) {
    if (counting) {
        ++allocations; bytes += n; live_bytes += n;
        peak_bytes = std::max(peak_bytes, live_bytes);
    }
    return std::malloc(n);
}
static void * counted_realloc(void * p, size_t old_n, size_t n) {
    if (counting) {
        if (old_n > live_bytes) std::abort();
        ++reallocations; bytes += n; live_bytes = live_bytes - old_n + n;
        peak_bytes = std::max(peak_bytes, live_bytes);
    }
    return std::realloc(p, n);
}
static void counted_free(void * p, size_t n) {
    if (counting) {
        if (n > live_bytes) std::abort();
        ++frees; live_bytes -= n;
    }
    std::free(p);
}

static lean_object * to_lean(mpz_t n, bool integer) {
    if (integer) {
        if (mpz_cmp_si(n, LEAN_MIN_SMALL_INT) >= 0 && mpz_cmp_si(n, LEAN_MAX_SMALL_INT) <= 0)
            return lean_int_to_int(static_cast<int>(mpz_get_si(n)));
    } else if (mpz_cmp_ui(n, LEAN_MAX_SMALL_NAT) <= 0) {
        return lean_box(mpz_get_ui(n));
    }
    return lean_alloc_mpz(n);
}

static void from_lean(mpz_t n, lean_object * o, bool integer) {
    if (!lean_is_scalar(o)) lean_extract_mpz_value(o, n);
    else if (integer) mpz_set_si(n, lean_scalar_to_int(o));
    else mpz_set_ui(n, lean_unbox(o));
}

enum Op { Bridge, IntAdd, IntCancel, IntMul, IntNeg, IntDiv, IntMod,
          NatAdd, NatSub, NatMul, NatDiv, NatMod, ParseInt };
static const char * names[] = {"bridge", "int_add", "int_cancel", "int_mul", "int_neg",
    "int_ediv", "int_emod", "nat_add_control", "nat_sub", "nat_mul_mixed",
    "nat_div", "nat_mod", "parse_int"};

struct Pair {
    mpz_t a, b, sum, dividend, negative, remainder;
    lean_object * ia, * ib, * na, * nb, * ns, * nd, * id, * minus_a;
    std::string decimal;
    Pair(gmp_randstate_t state, unsigned bits) {
        mpz_inits(a, b, sum, dividend, negative, remainder, nullptr);
        mpz_urandomb(a, state, bits); mpz_setbit(a, bits - 1);
        mpz_urandomb(b, state, bits); mpz_setbit(b, bits - 1);
        mpz_add(sum, a, b);
        mpz_fdiv_q_2exp(remainder, b, 1);
        mpz_mul(dividend, a, b); mpz_add(dividend, dividend, remainder);
        mpz_neg(negative, dividend);
        ia = to_lean(a, true); ib = to_lean(b, true);
        na = to_lean(a, false); nb = to_lean(b, false);
        ns = to_lean(sum, false); nd = to_lean(dividend, false); id = to_lean(negative, true);
        mpz_t tmp; mpz_init(tmp); mpz_neg(tmp, a); minus_a = to_lean(tmp, true); mpz_clear(tmp);
        std::vector<char> buffer(mpz_sizeinbase(a, 10) + 2);
        mpz_get_str(buffer.data(), 10, a); decimal = buffer.data();
    }
    ~Pair() {
        for (auto * o : {ia, ib, na, nb, ns, nd, id, minus_a}) lean_dec(o);
        mpz_clears(a, b, sum, dividend, negative, remainder, nullptr);
    }
};

static lean_object * run(Op op, Pair & p) {
    switch (op) {
    case Bridge: return lean_alloc_mpz(p.a);
    case IntAdd: return lean_int_add(p.ia, p.ib);
    case IntCancel: return lean_int_add(p.ia, p.minus_a);
    case IntMul: return lean_int_mul(p.ia, p.ib);
    case IntNeg: return lean_int_neg(p.ia);
    case IntDiv: return lean_int_ediv(p.id, p.ib);
    case IntMod: return lean_int_emod(p.id, p.ib);
    case NatAdd: return lean_nat_add(p.na, p.nb);
    case NatSub: return lean_nat_sub(p.ns, p.nb);
    case NatMul: return lean_nat_mul(p.na, lean_box(3));
    case NatDiv: return lean_nat_div(p.nd, p.nb);
    case NatMod: return lean_nat_mod(p.nd, p.nb);
    case ParseInt: return lean_cstr_to_int(p.decimal.c_str());
    }
    std::abort();
}

static void check(Op op, Pair & p) {
    mpz_t expected, actual; mpz_inits(expected, actual, nullptr);
    switch (op) {
    case Bridge: case NatSub: case NatDiv: case ParseInt: mpz_set(expected, p.a); break;
    case IntAdd: case NatAdd: mpz_set(expected, p.sum); break;
    case IntCancel: mpz_set_ui(expected, 0); break;
    case IntMul: mpz_mul(expected, p.a, p.b); break;
    case IntNeg: mpz_neg(expected, p.a); break;
    case IntDiv: mpz_fdiv_q(expected, p.negative, p.b); break;
    case IntMod: mpz_fdiv_r(expected, p.negative, p.b); break;
    case NatMul: mpz_mul_ui(expected, p.a, 3); break;
    case NatMod: mpz_set(expected, p.remainder); break;
    }
    auto * o = run(op, p);
    from_lean(actual, o, (op >= IntAdd && op <= IntMod) || op == ParseInt);
    if (mpz_cmp(expected, actual)) {
        std::fprintf(stderr, "incorrect result for %s\n", names[op]); std::abort();
    }
    lean_dec(o);
    // Check the borrowed inputs again after allocating and freeing the result.
    from_lean(actual, p.ia, true);
    if (mpz_cmp(actual, p.a)) std::abort();
    from_lean(actual, p.ib, true);
    if (mpz_cmp(actual, p.b)) std::abort();
    mpz_clears(expected, actual, nullptr);
}

static double timed(Op op, std::vector<std::unique_ptr<Pair>> & pairs, size_t rounds) {
    size_t checksum = 0;
    auto start = Clock::now();
    for (size_t i = 0; i < rounds; ++i) {
        for (auto & p : pairs) {
            auto * o = run(op, *p);
            if (counting) retained_bytes += live_bytes;
            checksum += lean_is_scalar(o) ? lean_unbox(o) : lean_ptr_tag(o);
            lean_dec(o);
        }
    }
    sink = checksum;
    return std::chrono::duration<double>(Clock::now() - start).count();
}

static void capacity_cases() {
    mpz_t huge, small, near, dividend, ga, gb;
    mpz_inits(huge, small, near, dividend, ga, gb, nullptr);
    mpz_setbit(huge, 4096); mpz_add_ui(huge, huge, 1);
    mpz_setbit(small, 64);
    mpz_add(near, huge, small);
    mpz_mul(dividend, huge, huge); mpz_add(dividend, dividend, small);
    mpz_mul(ga, huge, small);
    mpz_add_ui(gb, huge, 2); mpz_mul(gb, gb, small);
    auto * a = to_lean(huge, false);
    auto * b = to_lean(near, false);
    auto * d = to_lean(dividend, false);
    auto * x = to_lean(ga, false);
    auto * y = to_lean(gb, false);
    std::puts("op,retained_bytes");
    auto measure = [&](char const * name, lean_object * lhs, lean_object * rhs,
            lean_object * (*f)(lean_object *, lean_object *)) {
        live_bytes = peak_bytes = 0;
        counting = true;
        auto * result = f(lhs, rhs);
        counting = false;
        std::printf("%s,%zu\n", name, live_bytes);
        mpz_t actual; mpz_init(actual);
        from_lean(actual, result, false);
        if (mpz_cmp(actual, small)) std::abort();
        mpz_clear(actual);
        counting = true; lean_dec(result); counting = false;
        if (live_bytes) std::abort();
    };
    measure("int_small_sub", b, a, lean_int_sub);
    measure("nat_small_sub", b, a, lean_nat_sub);
    measure("int_small_emod", d, a, lean_int_emod);
    measure("nat_small_mod", d, a, lean_nat_mod);
    measure("nat_small_gcd", x, y, lean_nat_gcd);
    for (auto * o : {a, b, d, x, y}) lean_dec(o);
    mpz_clears(huge, small, near, dividend, ga, gb, nullptr);
}

int main(int argc, char ** argv) {
    bool capacity = argc > 1 && std::string(argv[1]) == "--capacity";
    bool count = capacity || (argc > 1 && std::string(argv[1]) == "--allocations");
    if (count) mp_set_memory_functions(counted_alloc, counted_realloc, counted_free);
    lean_initialize_runtime_module();
    if (capacity) { capacity_cases(); return 0; }
    gmp_randstate_t state; gmp_randinit_mt(state); gmp_randseed_ui(state, 15160);
    std::puts(count ? "op,bits,allocs,reallocs,frees,requested_bytes,retained_bytes,peak_bytes" : "op,bits,ns");
    for (unsigned bits : {16, 32, 64, 256, 1024, 4096}) {
        std::vector<std::unique_ptr<Pair>> pairs;
        for (unsigned i = 0; i < 16; ++i) pairs.push_back(std::make_unique<Pair>(state, bits));
        for (unsigned code = 0; code <= ParseInt; ++code) {
            Op op = static_cast<Op>(code);
            for (auto & p : pairs) check(op, *p);
            if (count) {
                allocations = reallocations = frees = bytes = 0;
                live_bytes = retained_bytes = peak_bytes = 0;
                counting = true;
                timed(op, pairs, 1);
                counting = false;
                if (live_bytes != 0) std::abort();
                std::printf("%s,%u,%.4f,%.4f,%.4f,%.4f,%.4f,%zu\n", names[op], bits,
                    allocations / 16.0, reallocations / 16.0, frees / 16.0, bytes / 16.0,
                    retained_bytes / 16.0, peak_bytes);
            } else {
                size_t rounds = 1;
                double seconds;
                do {
                    seconds = timed(op, pairs, rounds);
                    if (seconds < 0.003) rounds *= 2;
                } while (seconds < 0.003);
                rounds = std::max<size_t>(1, static_cast<size_t>(rounds * 0.025 / seconds));
                seconds = timed(op, pairs, rounds);
                std::printf("%s,%u,%.4f\n", names[op], bits, seconds * 1e9 / (rounds * pairs.size()));
            }
        }
    }
    gmp_randclear(state);
}
