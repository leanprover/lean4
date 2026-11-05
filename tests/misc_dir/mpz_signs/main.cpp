/* Check the built-in mpz helpers directly, including contracts that Lean's Nat callers cannot expose. */
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <utility>
#include "runtime/mpz.h"

// Standalone arithmetic tests need only the runtime's fatal-error hooks.
extern "C" void lean_internal_panic(char const * message) {
    std::cerr << message << '\n';
    std::abort();
}
extern "C" void lean_internal_panic_out_of_memory() { lean_internal_panic("out of memory"); }
extern "C" void lean_internal_panic_overflow() { lean_internal_panic("size overflow"); }
extern "C" void lean_internal_panic_unreachable() { lean_internal_panic("unreachable"); }
extern "C"
#if defined(__GLIBC__) && (defined(__GNUC__) || defined(__clang__))
__attribute__((nothrow))
#endif
void free_sized(void * ptr, size_t) { std::free(ptr); }

using lean::mpz;
static unsigned failures = 0;

static void check(bool condition, char const * message) {
    if (!condition) {
        if (failures < 10) std::cerr << message << '\n';
        ++failures;
    }
}

template<typename F> static void check_rejected(F const & action) {
    bool rejected = false;
    try {
        action();
    } catch (lean::exception const &) {
        rejected = true;
    }
    check(rejected, "unsupported negative operand was not rejected");
}

int main() {
    mpz value(-1);
    mpz positive(2);
    value = positive;
    check(value == 2, "copy assignment retained the destination sign");
    value = mpz(-3);
    positive = value;
    check(positive == -3, "copy assignment lost the source sign");
    mpz large_positive("1099511627776"), large_negative("-1099511627776");
    value = large_positive;
    check(value == large_positive && value.is_pos(), "copy assignment lost a positive sign across sizes");
    value = large_negative;
    check(value == large_negative && value.is_neg(), "copy assignment lost a negative sign");
    positive = large_negative;
    check(positive == large_negative && positive.is_neg(), "copy assignment lost a negative sign across sizes");
    value = value;
    check(value.is_neg(), "self-assignment changed the sign");

    value = -1;
    mul2k(value, mpz(2), 0);
    check(value == 2, "zero-bit left shift retained the destination sign");
    value = -1;
    div2k(value, mpz(6), 0);
    check(value == 6, "zero-bit right shift retained the destination sign");
    value = -1;
    mul2k(value, mpz(0), 3);
    check(value.is_zero() && !value.is_neg(), "left shift produced negative zero");
    value = -1;
    div2k(value, mpz(0), 3);
    check(value.is_zero() && !value.is_neg(), "right shift produced negative zero");

    check(mpz(-8).log2() == 0, "log2 of a negative number did not return zero");
    check(mpz("-1099511627776").log2() == 0, "log2 of a negative multi-digit number did not return zero");
    check(mpz(0).log2() == 0, "log2 of zero changed");
    check(mpz(8).log2() == 3, "log2 of a positive number changed");
    check(mpz("1099511627776").log2() == 40, "log2 of a positive multi-digit number changed");

    check(mpz(-2).powm(mpz(1), mpz(5)) == 3, "powm returned a negative residue");
    check(mpz(3).powm(mpz(0), mpz(-1)) == 0, "powm modulo minus one did not return zero");
    for (int b = -8; b <= 8; ++b) {
        for (int m = -13; m <= 13; ++m) {
            if (m == 0) continue;
            int modulus = m < 0 ? -m : m;
            int base = b % modulus;
            if (base < 0) base += modulus;
            int expected = 1 % modulus;
            for (int e = 0; e <= 12; ++e) {
                check(mpz(b).powm(mpz(e), mpz(m)) == expected, "powm residue mismatch");
                expected = expected * base % modulus;
            }
        }
    }
    check(mpz(-2).powm(mpz("4294967297"), mpz(-5)) == 3, "powm failed with a multi-digit exponent");
    check_rejected([] { mpz(2).powm(mpz(-1), mpz(5)); });

    using bitop = mpz & (mpz::*)(mpz const &);
    std::array<bitop, 3> operations = {&mpz::operator&=, &mpz::operator|=, &mpz::operator^=};
    std::array<std::uint64_t, 8> values = {0, 1, 2, 3, 0xffffffffULL, 0x100000000ULL,
                                         0x100000001ULL, 0xffffffffffffffffULL};
    for (size_t i = 0; i < operations.size(); ++i) {
        auto op = operations[i];
        for (auto a : values) {
            for (auto b : values) {
                mpz left(static_cast<lean::uint64>(a));
                mpz right(static_cast<lean::uint64>(b));
                (left.*op)(right);
                auto expected = i == 0 ? a & b : i == 1 ? a | b : a ^ b;
                check(left == mpz(static_cast<lean::uint64>(expected)), "nonnegative bitwise result changed");
            }
            mpz alias(static_cast<lean::uint64>(a));
            (alias.*op)(alias);
            check(alias == mpz(static_cast<lean::uint64>(i == 2 ? 0 : a)), "bitwise aliasing changed");
        }
        for (auto signs : {std::pair{-5, 3}, std::pair{5, -3}, std::pair{-5, -3}}) {
            mpz left(signs.first), right(signs.second);
            check_rejected([&] { (left.*op)(right); });
            check(left == signs.first && right == signs.second, "rejected bitwise operation changed its operands");
        }
    }
    if (failures) {
        std::cerr << failures << " mpz sign checks failed\n";
        return 1;
    }
    std::cout << "mpz sign checks passed\n";
    return 0;
}
