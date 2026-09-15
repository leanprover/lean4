#include "runtime/object.h"
#include <cstdlib>
#include <utility>

extern "C" void lean_initialize_runtime_module();

static void require(bool condition) {
    if (!condition) std::abort();
}

int main() {
    lean_initialize_runtime_module();
    for (char const * text : {"0", "1", "-1", "2147483648", "-2147483649",
            "18446744073709551616", "-18446744073709551617",
            "340282366920938463463374607431768211457",
            "-340282366920938463463374607431768211457"}) {
        for (unsigned shift : {0, 64, 1024}) {
            lean::mpz expected = lean::mpz(text) * lean::mpz(2).pow(shift);
            lean_object * copied;
            lean_object * moved;
            {
                lean::mpz source(expected);
                copied = lean::alloc_mpz(source);
                require(source == expected);
                moved = lean::alloc_mpz(std::move(source));
                // Reassign the moved-from value before destroying it.
                source = 7;
                require(source == 7);
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
