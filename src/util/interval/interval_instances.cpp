/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/thread.h"
#include "util/numerics/mpq.h"
#include "util/numerics/double.h"
#include "util/numerics/float.h"
#include "util/numerics/mpfp.h"
#include "util/interval/interval.cpp"

namespace lean {
template class interval<mpq>;
template void interval<mpq>::neg<true, false>(interval_deps &);
template void interval<mpq>::neg<false, true>(interval_deps &);
template void interval<mpq>::inv<true, false>(interval_deps &);
template void interval<mpq>::power<true, false>(unsigned, interval_deps &);

template class interval<double>;
template void interval<double>::neg<true, false>(interval_deps &);
template void interval<double>::inv<true, false>(interval_deps &);
template void interval<double>::power<true, false>(unsigned, interval_deps &);
template void interval<double>::exp<true, false>(interval_deps &);
template void interval<double>::exp2<true, false>(interval_deps &);
template void interval<double>::exp10<true, false>(interval_deps &);
template void interval<double>::log<true, false>(interval_deps &);
template void interval<double>::log2<true, false>(interval_deps &);
template void interval<double>::log10<true, false>(interval_deps &);
template void interval<double>::sin<true, false>(interval_deps &);
template void interval<double>::cos<true, false>(interval_deps &);
template void interval<double>::tan<true, false>(interval_deps &);
template void interval<double>::asin<true, false>(interval_deps &);
template void interval<double>::acos<true, false>(interval_deps &);
template void interval<double>::atan<true, false>(interval_deps &);
template void interval<double>::sinh<true, false>(interval_deps &);
template void interval<double>::cosh<true, false>(interval_deps &);
template void interval<double>::tanh<true, false>(interval_deps &);
template void interval<double>::csc<true, false>(interval_deps &);
template void interval<double>::sec<true, false>(interval_deps &);
template void interval<double>::cot<true, false>(interval_deps &);
template void interval<double>::asinh<true, false>(interval_deps &);
template void interval<double>::acosh<true, false>(interval_deps &);
template void interval<double>::atanh<true, false>(interval_deps &);

template class interval<float>;
template void interval<float>::neg<true, false>(interval_deps &);
template void interval<float>::inv<true, false>(interval_deps &);
template void interval<float>::power<true, false>(unsigned, interval_deps &);
template void interval<float>::exp<true, false>(interval_deps &);
template void interval<float>::exp2<true, false>(interval_deps &);
template void interval<float>::exp10<true, false>(interval_deps &);
template void interval<float>::log<true, false>(interval_deps &);
template void interval<float>::log2<true, false>(interval_deps &);
template void interval<float>::log10<true, false>(interval_deps &);
template void interval<float>::sin<true, false>(interval_deps &);
template void interval<float>::cos<true, false>(interval_deps &);
template void interval<float>::tan<true, false>(interval_deps &);
template void interval<float>::asin<true, false>(interval_deps &);
template void interval<float>::acos<true, false>(interval_deps &);
template void interval<float>::atan<true, false>(interval_deps &);
template void interval<float>::sinh<true, false>(interval_deps &);
template void interval<float>::cosh<true, false>(interval_deps &);
template void interval<float>::tanh<true, false>(interval_deps &);
template void interval<float>::csc<true, false>(interval_deps &);
template void interval<float>::sec<true, false>(interval_deps &);
template void interval<float>::cot<true, false>(interval_deps &);
template void interval<float>::asinh<true, false>(interval_deps &);
template void interval<float>::acosh<true, false>(interval_deps &);
template void interval<float>::atanh<true, false>(interval_deps &);

template class interval<mpfp>;
template void interval<mpfp>::neg<true, false>(interval_deps &);
template void interval<mpfp>::inv<true, false>(interval_deps &);
template void interval<mpfp>::power<true, false>(unsigned, interval_deps &);
template void interval<mpfp>::exp<true, false>(interval_deps &);
template void interval<mpfp>::exp2<true, false>(interval_deps &);
template void interval<mpfp>::exp10<true, false>(interval_deps &);
template void interval<mpfp>::log<true, false>(interval_deps &);
template void interval<mpfp>::log2<true, false>(interval_deps &);
template void interval<mpfp>::log10<true, false>(interval_deps &);
template void interval<mpfp>::sin<true, false>(interval_deps &);
template void interval<mpfp>::cos<true, false>(interval_deps &);
template void interval<mpfp>::tan<true, false>(interval_deps &);
template void interval<mpfp>::asin<true, false>(interval_deps &);
template void interval<mpfp>::acos<true, false>(interval_deps &);
template void interval<mpfp>::atan<true, false>(interval_deps &);
template void interval<mpfp>::sinh<true, false>(interval_deps &);
template void interval<mpfp>::cosh<true, false>(interval_deps &);
template void interval<mpfp>::tanh<true, false>(interval_deps &);
template void interval<mpfp>::csc<true, false>(interval_deps &);
template void interval<mpfp>::sec<true, false>(interval_deps &);
template void interval<mpfp>::cot<true, false>(interval_deps &);
template void interval<mpfp>::asinh<true, false>(interval_deps &);
template void interval<mpfp>::acosh<true, false>(interval_deps &);
template void interval<mpfp>::atanh<true, false>(interval_deps &);
}

void print(lean::interval<lean::mpq> const & i) { std::cout << i << std::endl; }
void print(lean::interval<double> const & i) { std::cout << i << std::endl; }
