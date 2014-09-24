/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/test.h"
#include "util/init_module.h"
#include "util/numerics/init_module.h"
#include "util/numerics/mpq.h"
#include "util/numerics/mpz.h"
#include "util/numerics/mpbq.h"
#include "util/numerics/double.h"
#include "util/numerics/float.h"
#include "util/numerics/mpfp.h"
using namespace lean;

template<typename T>
void tst_num(T const & a) {
    std::cout << "value:           " << a << "\n";
    std::cout << "is value zero:   " << std::boolalpha << numeric_traits<T>::is_zero(a) << "\n";
    std::cout << "zero:            " << numeric_traits<T>::zero() << "\n";
    std::cout << "is type precise: " << std::boolalpha << numeric_traits<T>::precise() << "\n";
    std::cout << "typeid:          " << typeid(T).name() << "\n";
    lean_assert(numeric_traits<T>::is_zero(numeric_traits<T>::zero()));
    std::cout << "\n";
}

static void tst1() {
    tst_num(mpq(1, 2));
    tst_num(mpq(0));
    tst_num(mpz(3));
    tst_num(mpz(0));
    tst_num(mpfp(2.0));
    tst_num(mpfp(0.0));
    tst_num(mpfp(0.0, 512));
    tst_num(mpbq(3));
    tst_num(1.0);
    tst_num(static_cast<float>(1.0));
}

int main() {
    initialize_util_module();
    initialize_numerics_module();
    tst1();
    finalize_numerics_module();
    finalize_util_module();
    return has_violations() ? 1 : 0;
}
