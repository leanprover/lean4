#include "runtime/object.h"
#include <cstdlib>
#include <sstream>
#include <utility>

extern "C" void lean_initialize_runtime_module();

static void require(bool condition) {
    if (!condition) std::abort();
}

static void expect(lean_object * result, lean::mpz const & value, bool integer = true) {
    lean::mpz actual = lean_is_scalar(result)
        ? (integer ? lean::mpz(lean_scalar_to_int(result)) : lean::mpz::of_size_t(lean_unbox(result)))
        : lean::mpz(lean::mpz_value(result));
    require(actual == value);
    if (!lean_is_scalar(result) && !value.is_zero())
        require(!lean::mpz_value(result).has_excess_capacity());
    lean_dec(result);
}

int main() {
    lean_initialize_runtime_module();
    {
        lean::mpz huge = lean::mpz(2).pow(4096) + 1;
        lean::mpz small = lean::mpz(2).pow(64);
        lean::mpz near = huge + small;
        lean::mpz dividend = huge * huge + small;
        auto * a = lean::alloc_mpz(huge);
        auto * b = lean::alloc_mpz(near);
        auto * d = lean::alloc_mpz(dividend);
        expect(lean_nat_sub(b, a), small, false);
        expect(lean_int_add(a, b), huge + near);
        expect(lean_int_sub(b, a), small);
        expect(lean_int_ediv(d, a), huge);
        expect(lean_int_emod(d, a), small);
        expect(lean_nat_mod(d, a), small, false);
        require(lean::mpz_value(a) == huge && lean::mpz_value(b) == near && lean::mpz_value(d) == dividend);
        lean_dec(a); lean_dec(b); lean_dec(d);
    }
    for (char const * text : {"0", "1", "-1", "2147483648", "-2147483649",
            "18446744073709551616", "-18446744073709551617",
            "340282366920938463463374607431768211457",
            "-340282366920938463463374607431768211457"}) {
        for (unsigned shift : {0, 64, 1024}) {
            lean::mpz expected = lean::mpz(text) * lean::mpz(2).pow(shift);
            std::ostringstream decimal;
            decimal << expected;
            expect(lean_cstr_to_int(decimal.str().c_str()), expected);
            lean_object * copied;
            lean_object * moved;
            {
                lean::mpz source(expected);
                copied = lean::alloc_mpz(source);
                require(source == expected);
                moved = lean::alloc_mpz(std::move(source));
            }
            lean_inc(moved);
            lean_object * shared = moved;
            lean_dec(moved);
            for (unsigned i = 0; i < 1024; ++i) {
                lean_object * temporary = lean::alloc_mpz(lean::mpz(i) * expected);
                require(lean::mpz_value(copied) == expected);
                require(lean::mpz_value(shared) == expected);
                require(lean_ptr_tag(copied) == LeanMPZ && lean_ptr_tag(shared) == LeanMPZ);
                lean_dec(temporary);
            }
            lean_object * copy = lean::alloc_mpz(lean::mpz_value(shared));
            lean_dec(shared);
            require(lean::mpz_value(copy) == expected);
            lean_dec(copy);
            lean_dec(copied);
        }
    }
}
