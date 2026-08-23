// Cross-check harness for `mpn_model.lean`: runs the real `src/runtime/mpn.cpp`
// on the same pseudorandom operands as the Lean transliteration and prints the
// results, so that the two outputs can be diffed. This is what keeps the model
// honest; without it the transliteration is just a hand-copy that can drift.
//
// It is not wired into CTest because it links runtime sources directly rather
// than against a built Lean. To run it:
//
//   clang++ -O1 -std=c++17 -include mutex -I src -I src/include \
//     -I build/release/stage1/include -o /tmp/mpn_crosscheck \
//     tests/elab/mpn_model_crosscheck.cpp \
//     src/runtime/mpn.cpp src/runtime/debug.cpp src/runtime/exception.cpp
//   /tmp/mpn_crosscheck <trials> <max-digits> <seed>   # e.g. 3000 6 0x2545F4914F6CDD1D
//
// and compare against `Mpn.Test.emit` with the same arguments, which prints the
// identical format from the model.
#include <cstdio>
#include <cstdint>
#include <cstdlib>
#include <vector>
#include "runtime/mpn.h"

using namespace lean;

static uint64_t next_rand(uint64_t s) {
    s ^= s << 13; s ^= s >> 7; return s ^ (s << 17);
}

static mpn_digit draw_digit(uint64_t & s) {
    s = next_rand(s);
    uint64_t sel = (s >> 59) % 8;
    if (sel == 0) return 0;
    if (sel == 1) return 0xFFFFFFFFu;
    if (sel == 2) return 1;
    return (mpn_digit)s;
}

static void print_vec(char const * tag, mpn_digit const * v, size_t n) {
    printf("%s", tag);
    for (size_t i = 0; i < n; i++) printf(" %u", v[i]);
    printf("\n");
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
        std::vector<mpn_digit> a(la), b(lb);
        for (size_t i = 0; i < la; i++) a[i] = draw_digit(s);
        for (size_t i = 0; i < lb; i++) b[i] = draw_digit(s);
        size_t len = la > lb ? la : lb;

        printf("case %u\n", t);
        print_vec("a", a.data(), la);
        print_vec("b", b.data(), lb);
        printf("compare %d\n", mpn_compare(a.data(), la, b.data(), lb));

        std::vector<mpn_digit> c(len + 1, 0);
        size_t lc;
        mpn_add(a.data(), la, b.data(), lb, c.data(), len + 1, &lc);
        print_vec("add", c.data(), lc);

        std::vector<mpn_digit> d(len, 0);
        mpn_digit borrow;
        mpn_sub(a.data(), la, b.data(), lb, d.data(), &borrow);
        print_vec("sub", d.data(), len);
        printf("borrow %u\n", borrow);

        std::vector<mpn_digit> p(la + lb, 0);
        mpn_mul(a.data(), la, b.data(), lb, p.data());
        print_vec("mul", p.data(), la + lb);

        if (lb <= la && b[lb - 1] != 0) {
            std::vector<mpn_digit> q(la - lb + 1, 0), r(lb, 0);
            mpn_div(a.data(), la, b.data(), lb, q.data(), r.data());
            print_vec("quot", q.data(), la - lb + 1);
            print_vec("rem", r.data(), lb);
        }

        std::vector<char> buf(la * 12 + 4, 0);
        printf("str %s\n", mpn_to_string(a.data(), la, buf.data(), buf.size()));
    }
    return 0;
}
