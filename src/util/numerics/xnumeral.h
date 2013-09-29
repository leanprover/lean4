/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once

#include <iostream>
#include "util/debug.h"
#include "util/numerics/numeric_traits.h"

namespace lean {

// Goodies (templates) for computing with extended numeral.
// Given a numeric set S, the extended set S+ is S union {-oo, +oo},
// where -oo is a new number smaller than any number in S, and +oo is a number bigger than
// any number in S.
//
// We do not provide a class extended numeral, since we do not want to commit
// with any particular representation.
// We just provide functions for computing with them.

enum xnumeral_kind { XN_MINUS_INFINITY, XN_NUMERAL, XN_PLUS_INFINITY };

template<typename T>
bool is_zero(T const & a, xnumeral_kind ak) {
    return ak == XN_NUMERAL && numeric_traits<T>::is_zero(a);
}

template<typename T>
bool is_pos(T const & a, xnumeral_kind ak) {
    return ak == XN_PLUS_INFINITY || (ak == XN_NUMERAL && numeric_traits<T>::is_pos(a));
}

template<typename T>
bool is_neg(T const & a, xnumeral_kind ak) {
    return ak == XN_MINUS_INFINITY || (ak == XN_NUMERAL && numeric_traits<T>::is_neg(a));
}

inline bool is_infinite(xnumeral_kind ak) {
    return ak != XN_NUMERAL;
}

template<typename T>
void set(T & a, xnumeral_kind & ak, T const & b, xnumeral_kind bk) {
    a  = b;
    ak = bk;
}

template<typename T>
void reset(T & a, xnumeral_kind & ak) {
    numeric_traits<T>::reset(a);
    ak = XN_NUMERAL;
}

template<typename T>
void neg(T & a, xnumeral_kind & ak) {
    switch (ak) {
    case XN_MINUS_INFINITY:
        ak = XN_PLUS_INFINITY;
        break;
    case XN_NUMERAL:
        numeric_traits<T>::neg(a);
        break;
    case XN_PLUS_INFINITY:
        ak = XN_MINUS_INFINITY;
        break;
    }
}

template<typename T>
void inv(T & a, xnumeral_kind & ak) {
    switch (ak) {
    case XN_MINUS_INFINITY:
        ak = XN_NUMERAL;
        numeric_traits<T>::reset(a);
        break;
    case XN_NUMERAL:
        lean_assert(!numeric_traits<T>::is_zero(a));
        numeric_traits<T>::inv(a);
        break;
    case XN_PLUS_INFINITY:
        ak = XN_NUMERAL;
        numeric_traits<T>::reset(a);
        break;
    }
}

template<typename T>
void add(T & r, xnumeral_kind & rk, T const & a, xnumeral_kind ak, T const & b, xnumeral_kind bk) {
    lean_assert(!(ak == XN_MINUS_INFINITY && bk == XN_PLUS_INFINITY));  // result is undefined
    lean_assert(!(ak == XN_PLUS_INFINITY  && bk == XN_MINUS_INFINITY)); // result is undefined
    if (ak != XN_NUMERAL) {
        numeric_traits<T>::reset(r);
        rk = ak;
    } else if (bk != XN_NUMERAL) {
        numeric_traits<T>::reset(r);
        rk = bk;
    } else {
        r = a + b;
        rk = XN_NUMERAL;
    }
}

template<typename T>
void sub(T & r, xnumeral_kind & rk, T const & a, xnumeral_kind ak, T const & b, xnumeral_kind bk) {
    lean_assert(!(ak == XN_MINUS_INFINITY && bk == XN_MINUS_INFINITY));  // result is undefined
    lean_assert(!(ak == XN_PLUS_INFINITY  && bk == XN_PLUS_INFINITY));   // result is undefined
    if (ak != XN_NUMERAL) {
        lean_assert(bk != ak);
        numeric_traits<T>::reset(r);
        rk = ak;
    } else {
        switch (bk) {
        case XN_MINUS_INFINITY:
            numeric_traits<T>::reset(r);
            rk = XN_PLUS_INFINITY;
            break;
        case XN_NUMERAL:
            r = a - b;
            rk = XN_NUMERAL;
            break;
        case XN_PLUS_INFINITY:
            numeric_traits<T>::reset(r);
            rk = XN_MINUS_INFINITY;
            break;
        }
    }
}

template<typename T>
void mul(T & r, xnumeral_kind & rk, T const & a, xnumeral_kind ak, T const & b, xnumeral_kind bk) {
    if (is_zero(a, ak) || is_zero(b, bk)) {
        numeric_traits<T>::reset(r);
        rk = XN_NUMERAL;
    } else if (is_infinite(ak) || is_infinite(bk)) {
        if (is_pos(a, ak) == is_pos(b, bk))
            rk = XN_PLUS_INFINITY;
        else
            rk = XN_MINUS_INFINITY;
        numeric_traits<T>::reset(r);
    } else {
        rk = XN_NUMERAL;
        r = a * b;
    }
}

template<typename T>
void div(T & r, xnumeral_kind & rk, T const & a, xnumeral_kind ak, T const & b, xnumeral_kind bk) {
    lean_assert(!is_zero(b, bk));
    if (is_zero(a, ak)) {
        lean_assert(!is_zero(b, bk));
        numeric_traits<T>::reset(r);
        rk = XN_NUMERAL;
    } else if (is_infinite(ak)) {
        lean_assert(!is_infinite(bk));
        if (is_pos(a, ak) == is_pos(b, bk))
            rk = XN_PLUS_INFINITY;
        else
            rk = XN_MINUS_INFINITY;
        numeric_traits<T>::reset(r);
    } else if (is_infinite(bk)) {
        lean_assert(!is_infinite(ak));
        numeric_traits<T>::reset(r);
        rk = XN_NUMERAL;
    } else {
        rk = XN_NUMERAL;
        r = a / b;
    }
}

template<typename T>
void power(T & a, xnumeral_kind & ak, unsigned n) {
    switch (ak) {
    case XN_MINUS_INFINITY:
        if (n % 2 == 0)
            ak = XN_PLUS_INFINITY;
        break;
    case XN_NUMERAL:
        numeric_traits<T>::power(a, n);
        break;
    case XN_PLUS_INFINITY:
        break; // do nothing
    }
}

/**
   \brief Return true if (a, ak) == (b, bk).
*/
template<typename T>
bool eq(T const & a, xnumeral_kind ak, T const & b, xnumeral_kind bk) {
    if (ak == XN_NUMERAL) {
        return bk == XN_NUMERAL && a == b;
    } else {
        return ak == bk;
    }
}

template<typename T>
bool neq(T const & a, xnumeral_kind ak, T const & b, xnumeral_kind bk) {
    return !eq(a, ak, b, bk);
}

template<typename T>
bool lt(T const & a, xnumeral_kind ak, T const & b, xnumeral_kind bk) {
    switch (ak) {
    case XN_MINUS_INFINITY:
        return bk != XN_MINUS_INFINITY;
    case XN_NUMERAL:
        switch (bk) {
        case XN_MINUS_INFINITY:
            return false;
        case XN_NUMERAL:
            return a < b;
        case XN_PLUS_INFINITY:
            return true;
        }
    case XN_PLUS_INFINITY:
        return false;
    }
    lean_unreachable(); // LCOV_EXEC_LINE
}

template<typename T>
bool gt(T const & a, xnumeral_kind ak, T const & b, xnumeral_kind bk) {
    return lt(b, bk, a, ak);
}

template<typename T>
bool le(T const & a, xnumeral_kind ak, T const & b, xnumeral_kind bk) {
    return !gt(a, ak, b, bk);
}

template<typename T>
bool ge(T const & a, xnumeral_kind ak, T const & b, xnumeral_kind bk) {
    return !lt(a, ak, b, bk);
}

template<typename T>
void display(std::ostream & out, T const & a, xnumeral_kind ak) {
    switch (ak) {
    case XN_MINUS_INFINITY: out << "-oo"; break;
    case XN_NUMERAL:        out << a; break;
    case XN_PLUS_INFINITY:  out << "+oo"; break;
    }
}

}
