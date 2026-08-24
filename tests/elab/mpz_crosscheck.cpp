// Cross-check harness for the `mpz` layer of `mpn_model.lean`: runs the real
// `src/runtime/mpz.cpp` on the same pseudorandom operands as `Mpn.Test.emitNum`
// and prints the results in decimal, so the two can be diffed. Companion to
// `mpn_model_crosscheck.cpp`, which covers `mpn.cpp` itself.
//
//   clang++ -O1 -std=c++17 -include mutex -I src -I src/include \
//     -I build/release/stage1/include -o /tmp/mpz_crosscheck \
//     tests/elab/mpz_crosscheck.cpp tests/elab/mpz_crosscheck_stubs.cpp \
//     src/runtime/mpz.cpp src/runtime/mpn.cpp src/runtime/debug.cpp \
//     src/runtime/exception.cpp
//   /tmp/mpz_crosscheck <trials> <max-digits> <seed>
#include <cstdio>
#include <cstdint>
#include <cstdlib>
#include <sstream>
#include <vector>
#include "runtime/mpz.h"

using namespace lean;

static uint64_t next_rand(uint64_t s) {
    s ^= s << 13; s ^= s >> 7; return s ^ (s << 17);
}

static uint32_t draw_digit(uint64_t & s) {
    s = next_rand(s);
    uint64_t sel = (s >> 59) % 8;
    if (sel == 0) return 0;
    if (sel == 1) return 0xFFFFFFFFu;
    if (sel == 2) return 1;
    return (uint32_t)s;
}

// little-endian digits to an `mpz`, built from the top down
static mpz from_digits(std::vector<uint32_t> const & ds) {
    mpz v(0u);
    mpz b = mpz::of_size_t((size_t)4294967296ull);
    for (size_t i = ds.size(); i-- > 0;) {
        v *= b;
        v += mpz(ds[i]);
    }
    return v;
}

static void emit(char const * tag, mpz const & v) {
    std::ostringstream out;
    out << v;
    printf("%s %s\n", tag, out.str().c_str());
}

int main(int argc, char ** argv) {
    unsigned trials = (unsigned)atoi(argv[1]);
    size_t max_len = (size_t)atoi(argv[2]);
    uint64_t s = strtoull(argv[3], nullptr, 0);
    for (unsigned t = 0; t < trials; t++) {
        s = next_rand(s);
        size_t la = ((s >> 33) % max_len) + 1;
        s = next_rand(s);
        size_t lb = ((s >> 33) % max_len) + 1;
        std::vector<uint32_t> a(la), b(lb);
        for (size_t i = 0; i < la; i++) a[i] = draw_digit(s);
        for (size_t i = 0; i < lb; i++) b[i] = draw_digit(s);
        s = next_rand(s);
        unsigned k = (unsigned)((s >> 33) % 100);

        mpz A = from_digits(a), B = from_digits(b);
        printf("case %u\n", t);
        emit("a", A);
        emit("b", B);
        emit("add", A + B);
        if (A >= B) emit("sub", A - B);
        else emit("sub", mpz(0u));
        emit("mul", A * B);
        emit("pow", A.pow(k % 5));
        if (!(B == mpz(0u))) {
            emit("div", A / B);
            emit("mod", A % B);
        }
        { mpz g; gcd(g, A, B); emit("gcd", g); }
        { mpz r(A); r &= B; emit("and", r); }
        { mpz r(A); r |= B; emit("or", r); }
        { mpz r(A); r ^= B; emit("xor", r); }
        { mpz r; mul2k(r, A, k); emit("shl", r); }
        { mpz r; div2k(r, A, k); emit("shr", r); }
        printf("k %u\n", k);
    }
    return 0;
}
