/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
        Soonho Kong
*/
#pragma once
#include <cstddef>
#include <gmp.h>
#include <mpfr.h>
#include <utility>
#include <algorithm>
#include "util/numerics/mpz.h"
#include "util/interval/interval.h"

namespace lean {

template<typename T>
interval_deps interval<T>::dummy;

template<typename T>
void interval<T>::set_closed_endpoints() {
    m_lower_open = false;
    m_upper_open = false;
    m_lower_inf  = false;
    m_upper_inf  = false;
}

template<typename T>
interval<T> & interval<T>::operator=(interval const & n) {
    m_lower = n.m_lower;
    m_upper = n.m_upper;
    m_lower_open = n.m_lower_open;
    m_upper_open = n.m_upper_open;
    m_lower_inf  = n.m_lower_inf;
    m_upper_inf  = n.m_upper_inf;
    return *this;
}

template<typename T>
interval<T> & interval<T>::operator=(interval && n) {
    m_lower = std::move(n.m_lower);
    m_upper = std::move(n.m_upper);
    m_lower_open = n.m_lower_open;
    m_upper_open = n.m_upper_open;
    m_lower_inf  = n.m_lower_inf;
    m_upper_inf  = n.m_upper_inf;
    return *this;
}

template<typename T>
interval<T>::interval():
    m_lower(),
    m_upper() {
    numeric_traits<T>::reset(m_lower);
    numeric_traits<T>::reset(m_upper);
    m_lower_inf  = true;
    m_lower_open = true;
    m_upper_inf  = true;
    m_upper_open = true;
    lean_assert(check_invariant());
}

template<typename T>
interval<T>::interval(interval<T> const & n):
    m_lower(n.m_lower),
    m_upper(n.m_upper),
    m_lower_open(n.m_lower_open),
    m_upper_open(n.m_upper_open),
    m_lower_inf(n.m_lower_inf),
    m_upper_inf(n.m_upper_inf) {
    lean_assert(check_invariant());
}

template<typename T>
interval<T>::interval(interval<T> && n):
    m_lower(std::move(n.m_lower)),
    m_upper(std::move(n.m_upper)),
    m_lower_open(n.m_lower_open),
    m_upper_open(n.m_upper_open),
    m_lower_inf(n.m_lower_inf),
    m_upper_inf(n.m_upper_inf) {
    lean_assert(check_invariant());
}

template<typename T>
interval<T>::~interval() {
}

template<typename T>
void interval<T>::_swap(interval<T> & b) {
    using std::swap;
    swap(m_lower, b.m_lower);
    swap(m_upper, b.m_upper);
    unsigned tmp;
    tmp = m_lower_inf;  m_lower_inf  = b.m_lower_inf;  b.m_lower_inf = tmp;
    tmp = m_upper_inf;  m_upper_inf  = b.m_upper_inf;  b.m_upper_inf = tmp;
    tmp = m_lower_open; m_lower_open = b.m_lower_open; b.m_lower_open = tmp;
    tmp = m_upper_open; m_upper_open = b.m_upper_open; b.m_upper_open = tmp;
}

template<typename T>
bool interval<T>::contains_zero() const {
    return
        (is_lower_neg() || (is_lower_zero() && !is_lower_open())) &&
        (is_upper_pos() || (is_upper_zero() && !is_upper_open()));
}

template<typename T>
bool interval<T>::contains(interval<T> const & b) const {
    if (!m_lower_inf) {
        if (b.m_lower_inf)
            return false;
        if (m_lower > b.m_lower)
            return false;
        if (m_lower == b.m_lower && m_lower_open && !b.m_lower_open)
            return false;
    }
    if (!m_upper_inf) {
        if (b.m_upper_inf)
            return false;
        if (m_upper < b.m_upper)
            return false;
        if (m_upper == b.m_upper && m_upper_open && !b.m_upper_open)
            return false;
    }
    return true;
}

template<typename T>
bool interval<T>::is_empty() const {
    return
        (m_lower == m_upper && (m_lower_open || m_upper_open) && !m_lower_inf && !m_upper_inf) ||
        (m_lower > m_upper && !m_lower_inf && !m_upper_inf);
}

template<typename T>
void interval<T>::set_empty() {
    numeric_traits<T>::reset(m_lower);
    numeric_traits<T>::reset(m_upper);
    m_lower_open = m_upper_open = true;
    m_lower_inf  = m_upper_inf  = false;
}

template<typename T>
bool interval<T>::is_singleton() const {
    return !m_lower_inf && !m_upper_inf && !m_lower_open && !m_upper_open && m_lower == m_upper;
}

template<typename T>
bool interval<T>::_eq(interval<T> const & b) const {
    return
        m_lower_open == b.m_lower_open &&
        m_upper_open == b.m_upper_open &&
        eq(m_lower, lower_kind(), b.m_lower, b.lower_kind()) &&
        eq(m_upper, upper_kind(), b.m_upper, b.upper_kind());
}

template<typename T>
bool interval<T>::before(interval<T> const & b) const {
    if (is_upper_inf() || b.is_lower_inf())
        return false;
    return m_upper < b.m_lower || (is_upper_open() && m_upper == b.m_lower);
}

template<typename T>
template<bool compute_intv, bool compute_deps>
void interval<T>::neg(interval_deps & deps) {
    using std::swap;
    if (is_lower_inf()) {
        if (is_upper_inf()) {
            // (-oo, oo) case
            // do nothing
            if (compute_deps) {
                deps.m_lower_deps = 0;
                deps.m_upper_deps = 0;
            }
        } else {
            // (-oo, a| --> |-a, oo)
            if (compute_intv) {
                swap(m_lower, m_upper);
                neg(m_lower);
                m_lower_inf  = false;
                m_lower_open = m_upper_open;
                reset(m_upper);
                m_upper_inf  = true;
                m_upper_open = true;
            }
            if (compute_deps) {
                deps.m_lower_deps = DEP_IN_UPPER1;
                deps.m_upper_deps = 0;
            }
        }
    } else {
        if (is_upper_inf()) {
            // |a, oo) --> (-oo, -a|
            if (compute_intv) {
                swap(m_upper, m_lower);
                neg(m_upper);
                m_upper_inf  = false;
                m_upper_open = m_lower_open;

                reset(m_lower);
                m_lower_inf  = true;
                m_lower_open = true;
            }
            if (compute_deps) {
                deps.m_lower_deps = 0;
                deps.m_upper_deps = DEP_IN_LOWER1;
            }
        } else {
            // |a, b| --> |-b, -a|
            if (compute_intv) {
                swap(m_lower, m_upper);
                neg(m_lower);
                neg(m_upper);

                unsigned lo  = m_lower_open;
                unsigned li  = m_lower_inf;
                m_lower_open = m_upper_open;
                m_lower_inf  = m_upper_inf;
                m_upper_open = lo;
                m_upper_inf  = li;
            }
            if (compute_deps) {
                deps.m_upper_deps = DEP_IN_LOWER1;
                deps.m_lower_deps = DEP_IN_UPPER1;
            }
        }
    }
    if (compute_intv) {
        lean_assert(check_invariant());
    }
}

template<typename T>
interval<T> & interval<T>::operator+=(interval<T> const & o) {
    return add(o);
}

template<typename T>
interval<T> & interval<T>::operator-=(interval<T> const & o) {
    return sub(o);
}

template<typename T>
interval<T> & interval<T>::operator*=(interval<T> const & o) {
    return mul(o);
}

template<typename T>
interval<T> & interval<T>::operator/=(interval<T> const & o) {
    return div(o);
}

template<typename T>
template<bool compute_intv, bool compute_deps>
interval<T> & interval<T>::add(interval<T> const & o, interval_deps & deps) {
    if (compute_intv) {
        xnumeral_kind new_l_kind, new_u_kind;
        round_to_minus_inf();
        lean::add(m_lower, new_l_kind, m_lower, lower_kind(), o.m_lower, o.lower_kind());
        round_to_plus_inf();
        lean::add(m_upper, new_u_kind, m_upper, upper_kind(), o.m_upper, o.upper_kind());
        m_lower_inf = new_l_kind == XN_MINUS_INFINITY;
        m_upper_inf = new_u_kind == XN_PLUS_INFINITY;
        m_lower_open = m_lower_open || o.m_lower_open;
        m_upper_open = m_upper_open || o.m_upper_open;
        lean_assert(check_invariant());
    }
    if (compute_deps) {
        deps.m_lower_deps = DEP_IN_LOWER1 | DEP_IN_LOWER2;
        deps.m_upper_deps = DEP_IN_UPPER1 | DEP_IN_UPPER2;
    }
    return *this;
}
template<typename T>
template<bool compute_intv, bool compute_deps>
interval<T> & interval<T>::sub(interval<T> const & o, interval_deps & deps) {
    if (compute_intv) {
        using std::swap;
        T new_l_val;
        T new_u_val;
        xnumeral_kind new_l_kind, new_u_kind;
        round_to_minus_inf();
        lean::sub(new_l_val, new_l_kind, m_lower, lower_kind(), o.m_upper, o.upper_kind());
        round_to_plus_inf();
        lean::sub(new_u_val, new_u_kind, m_upper, upper_kind(), o.m_lower, o.lower_kind());
        swap(new_l_val, m_lower);
        swap(new_u_val, m_upper);
        m_lower_inf = new_l_kind == XN_MINUS_INFINITY;
        m_upper_inf = new_u_kind == XN_PLUS_INFINITY;
        bool o_l = o.m_lower_open;
        m_lower_open = m_lower_open || o.m_upper_open;
        m_upper_open = m_upper_open || o_l;
        lean_assert(check_invariant());
    }
    if (compute_deps) {
        deps.m_lower_deps = DEP_IN_LOWER1 | DEP_IN_UPPER2;
        deps.m_upper_deps = DEP_IN_UPPER1 | DEP_IN_LOWER2;
    }
    return *this;
}
template<typename T>
template<bool compute_intv, bool compute_deps>
interval<T> & interval<T>::mul(interval<T> const & o, interval_deps & deps) {
    using std::swap;
    interval<T> const & i1 = *this;
    interval<T> const & i2 = o;
#if defined(LEAN_DEBUG) || defined(LEAN_TRACE)
    bool i1_contains_zero = i1.contains_zero();
    bool i2_contains_zero = i2.contains_zero();
#endif
    if (i1.is_zero()) {
        if (compute_deps) {
            deps.m_lower_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
            deps.m_upper_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
        }
        return *this;
    }
    if (i2.is_zero()) {
        if (compute_intv) {
            *this = i2;
        }
        if (compute_deps) {
            deps.m_lower_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
            deps.m_upper_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
        }
        return *this;
    }

    T const & a = i1.m_lower; xnumeral_kind a_k = i1.lower_kind();
    T const & b = i1.m_upper; xnumeral_kind b_k = i1.upper_kind();
    T const & c = i2.m_lower; xnumeral_kind c_k = i2.lower_kind();
    T const & d = i2.m_upper; xnumeral_kind d_k = i2.upper_kind();

    bool a_o = i1.is_lower_open();
    bool b_o = i1.is_upper_open();
    bool c_o = i2.is_lower_open();
    bool d_o = i2.is_upper_open();

    T new_l_val;
    T new_u_val;
    xnumeral_kind new_l_kind, new_u_kind;

    if (i1.is_N()) {
        if (i2.is_N()) {
            // x <= b <= 0, y <= d <= 0 --> b*d <= x*y
            // a <= x <= b <= 0, c <= y <= d <= 0 --> x*y <= a*c  (we
            // can use the fact that x or y is always negative (i.e.,
            // b is neg or d is neg))
            if (compute_intv) {
                set_is_lower_open((i1.is_N0() || i2.is_N0()) ? false : (b_o || d_o));
                set_is_upper_open(a_o || c_o);
                // if b = 0 (and the interval is closed), then the lower bound is closed

                round_to_minus_inf();
                lean::mul(new_l_val, new_l_kind, b, b_k, d, d_k);
                round_to_plus_inf();
                lean::mul(new_u_val, new_u_kind, a, a_k, c, c_k);
            }
            if (compute_deps) {
                deps.m_lower_deps = DEP_IN_UPPER1 | DEP_IN_UPPER2;
                deps.m_upper_deps = DEP_IN_LOWER1 | DEP_IN_LOWER2 | DEP_IN_UPPER1; // we can replace DEP_IN_UPPER1 with DEP_IN_UPPER2
            }
        } else if (i2.is_M()) {
            // a <= x <= b <= 0,  y <= d, d > 0 --> a*d <= x*y (uses the fact that b is not positive)
            // a <= x <= b <= 0,  c <= y, c < 0 --> x*y <= a*c (uses
            // the fact that b is not positive)
            if (compute_intv) {
                set_is_lower_open(a_o || d_o);
                set_is_upper_open(a_o || c_o);

                round_to_minus_inf();
                lean::mul(new_l_val, new_l_kind, a, a_k, d, d_k);
                round_to_plus_inf();
                lean::mul(new_u_val, new_u_kind, a, a_k, c, c_k);
            }
            if (compute_deps) {
                deps.m_lower_deps = DEP_IN_LOWER1 | DEP_IN_UPPER2 | DEP_IN_UPPER1;
                deps.m_upper_deps = DEP_IN_LOWER1 | DEP_IN_LOWER2 | DEP_IN_UPPER1;
            }
        } else {
            // a <= x <= b <= 0, 0 <= c <= y <= d --> a*d <= x*y (uses the fact that x is neg (b is not positive) or y is pos (c is not negative))
            // x <= b <= 0,  0 <= c <= y --> x*y <= b*c
            lean_assert(i2.is_P());

            // must update upper_is_open first, since value of is_N0(i1) and is_P0(i2) may be affected by update
            if (compute_intv) {
                set_is_upper_open((i1.is_N0() || i2.is_P0()) ? false : (b_o || c_o));
                set_is_lower_open(a_o || d_o);

                round_to_minus_inf();
                lean::mul(new_l_val, new_l_kind, a, a_k, d, d_k);
                round_to_plus_inf();
                lean::mul(new_u_val, new_u_kind, b, b_k, c, c_k);
            }
            if (compute_deps) {
                deps.m_lower_deps = DEP_IN_LOWER1 | DEP_IN_UPPER2 | DEP_IN_UPPER1; // we can replace DEP_IN_UPPER1 with DEP_IN_UPPER2
                deps.m_upper_deps = DEP_IN_UPPER1 | DEP_IN_LOWER2;
            }
        }
    } else if (i1.is_M()) {
        if (i2.is_N()) {
            // b > 0, x <= b,  c <= y <= d <= 0 --> b*c <= x*y (uses the fact that d is not positive)
            // a < 0, a <= x,  c <= y <= d <= 0 --> x*y <= a*c (uses
            // the fact that d is not positive)
            if (compute_intv) {
                set_is_lower_open(b_o || c_o);
                set_is_upper_open(a_o || c_o);

                round_to_minus_inf();
                lean::mul(new_l_val, new_l_kind, b, b_k, c, c_k);
                round_to_plus_inf();
                lean::mul(new_u_val, new_u_kind, a, a_k, c, c_k);
            }
            if (compute_deps) {
                deps.m_lower_deps = DEP_IN_UPPER1 | DEP_IN_LOWER2 | DEP_IN_UPPER2;
                deps.m_upper_deps = DEP_IN_LOWER1 | DEP_IN_LOWER2 | DEP_IN_UPPER2;
            }
        } else if (i2.is_M()) {
            T ad; xnumeral_kind ad_k = XN_NUMERAL;
            T bc; xnumeral_kind bc_k = XN_NUMERAL;
            T ac; xnumeral_kind ac_k = XN_NUMERAL;
            T bd; xnumeral_kind bd_k = XN_NUMERAL;

            bool  ad_o = a_o || d_o;
            bool  bc_o = b_o || c_o;
            bool  ac_o = a_o || c_o;
            bool  bd_o = b_o || d_o;

            if (compute_intv) {
                round_to_minus_inf();
                lean::mul(ad, ad_k, a, a_k, d, d_k);
                lean::mul(bc, bc_k, b, b_k, c, c_k);
                round_to_plus_inf();
                lean::mul(ac, ac_k, a, a_k, c, c_k);
                lean::mul(bd, bd_k, b, b_k, d, d_k);
            }
            if (lt(ad, ad_k, bc, bc_k) || (eq(ad, ad_k, bc, bc_k) && !ad_o && bc_o)) {
                if (compute_intv) {
                    swap(new_l_val, ad);
                    new_l_kind = ad_k;
                    set_is_lower_open(ad_o);
                }
            } else {
                if (compute_intv) {
                    swap(new_l_val, bc);
                    new_l_kind = bc_k;
                    set_is_lower_open(bc_o);
                }
            }
            if (gt(ac, ac_k, bd, bd_k) || (eq(ac, ac_k, bd, bd_k) && !ac_o && bd_o)) {
                if (compute_intv) {
                    swap(new_u_val, ac);
                    new_u_kind = ac_k;
                    set_is_upper_open(ac_o);
                }
            } else {
                if (compute_intv) {
                    swap(new_u_val, bd);
                    new_u_kind = bd_k;
                    set_is_upper_open(bd_o);
                }
            }
            if (compute_deps) {
                deps.m_lower_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1 | DEP_IN_LOWER2 | DEP_IN_UPPER2;
                deps.m_upper_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1 | DEP_IN_LOWER2 | DEP_IN_UPPER2;
            }
        } else {
            // a < 0, a <= x, 0 <= c <= y <= d --> a*d <= x*y (uses the fact that c is not negative)
            // b > 0, x <= b, 0 <= c <= y <= d --> x*y <= b*d (uses the fact that c is not negative)
            lean_assert(i2.is_P());

            if (compute_intv) {
                set_is_lower_open(a_o || d_o);
                set_is_upper_open(b_o || d_o);

                round_to_minus_inf();
                lean::mul(new_l_val, new_l_kind, a, a_k, d, d_k);
                round_to_plus_inf();
                lean::mul(new_u_val, new_u_kind, b, b_k, d, d_k);
            }
            if (compute_deps) {
                deps.m_lower_deps = DEP_IN_LOWER1 | DEP_IN_UPPER2 | DEP_IN_LOWER2;
                deps.m_upper_deps = DEP_IN_UPPER1 | DEP_IN_UPPER2 | DEP_IN_LOWER2;
            }
        }
    } else {
        lean_assert(i1.is_P());
        if (i2.is_N()) {
            // 0 <= a <= x <= b,   c <= y <= d <= 0  -->  x*y <= b*c (uses the fact that x is pos (a is not neg) or y is neg (d is not pos))
            // 0 <= a <= x,  y <= d <= 0  --> a*d <= x*y

            // must update upper_is_open first, since value of is_P0(i1) and is_N0(i2) may be affected by update
            if (compute_intv) {
                set_is_upper_open((i1.is_P0() || i2.is_N0()) ? false : a_o || d_o);
                set_is_lower_open(b_o || c_o);

                round_to_minus_inf();
                lean::mul(new_l_val, new_l_kind, b, b_k, c, c_k);
                round_to_plus_inf();
                lean::mul(new_u_val, new_u_kind, a, a_k, d, d_k);
            }
            if (compute_deps) {
                deps.m_lower_deps = DEP_IN_UPPER1 | DEP_IN_LOWER2 | DEP_IN_LOWER1; // we can replace DEP_IN_LOWER1 with DEP_IN_UPPER2
                deps.m_upper_deps = DEP_IN_LOWER1 | DEP_IN_UPPER2;
            }
        } else if (i2.is_M()) {
            // 0 <= a <= x <= b,  c <= y --> b*c <= x*y (uses the fact that a is not negative)
            // 0 <= a <= x <= b,  y <= d --> x*y <= b*d (uses the fact
            // that a is not negative)
            if (compute_intv) {
                set_is_lower_open(b_o || c_o);
                set_is_upper_open(b_o || d_o);

                round_to_minus_inf();
                lean::mul(new_l_val, new_l_kind, b, b_k, c, c_k);
                round_to_plus_inf();
                lean::mul(new_u_val, new_u_kind, b, b_k, d, d_k);
            }
            if (compute_deps) {
                deps.m_lower_deps = DEP_IN_UPPER1 | DEP_IN_LOWER2 | DEP_IN_LOWER1;
                deps.m_upper_deps = DEP_IN_UPPER1 | DEP_IN_UPPER2 | DEP_IN_LOWER1;
            }
        } else {
            lean_assert(i2.is_P());
            // 0 n<= a <= x, 0 <= c <= y --> a*c <= x*y
            // x <= b, y <= d --> x*y <= b*d (uses the fact that x is pos (a is not negative) or y is pos (c is not negative))
            if (compute_intv) {
                set_is_lower_open((i1.is_P0() || i2.is_P0()) ? false : a_o || c_o);
                set_is_upper_open(b_o || d_o);

                round_to_minus_inf();
                lean::mul(new_l_val, new_l_kind, a, a_k, c, c_k);
                round_to_plus_inf();
                lean::mul(new_u_val, new_u_kind, b, b_k, d, d_k);
            }
            if (compute_deps) {
                deps.m_lower_deps = DEP_IN_LOWER1 | DEP_IN_LOWER2;
                deps.m_upper_deps = DEP_IN_UPPER1 | DEP_IN_UPPER2 | DEP_IN_LOWER1;
            }
        }
    }
    if (compute_intv) {
        swap(m_lower, new_l_val);
        swap(m_upper, new_u_val);
        set_is_lower_inf(new_l_kind == XN_MINUS_INFINITY);
        set_is_upper_inf(new_u_kind == XN_PLUS_INFINITY);
        lean_assert(!(i1_contains_zero || i2_contains_zero) || contains_zero());
        lean_assert(check_invariant());
    }
    return *this;
}
template<typename T>
template<bool compute_intv, bool compute_deps>
interval<T> & interval<T>::div(interval<T> const & o, interval_deps & deps) {
    using std::swap;
    interval<T> const & i1 = *this;
    interval<T> const & i2 = o;
    lean_assert(!i2.contains_zero());

    if (i1.is_zero()) {
        // 0/other = 0 if other != 0
        // do nothing
        if (compute_deps) {
            if (i2.is_P1()) {
                deps.m_lower_deps = DEP_IN_LOWER1 | DEP_IN_LOWER2;
                deps.m_upper_deps = DEP_IN_UPPER1 | DEP_IN_LOWER2;
            } else {
                deps.m_lower_deps = DEP_IN_UPPER1 | DEP_IN_UPPER2;
                deps.m_upper_deps = DEP_IN_LOWER1 | DEP_IN_UPPER2;
            }
        }
    } else {
        T const & a = i1.m_lower; xnumeral_kind a_k = i1.lower_kind();
        T const & b = i1.m_upper; xnumeral_kind b_k = i1.upper_kind();
        T const & c = i2.m_lower; xnumeral_kind c_k = i2.lower_kind();
        T const & d = i2.m_upper; xnumeral_kind d_k = i2.upper_kind();

        bool a_o = i1.m_lower_open;
        bool b_o = i1.m_upper_open;
        bool c_o = i2.m_lower_open;
        bool d_o = i2.m_upper_open;

        T new_l_val;
        T new_u_val;
        xnumeral_kind new_l_kind, new_u_kind;

        if (i1.is_N()) {
            if (i2.is_N1()) {
                // x <= b <= 0,      c <= y <= d < 0 --> b/c <= x/y
                // a <= x <= b <= 0,      y <= d < 0 -->        x/y <= a/d

                if (compute_intv) {
                    set_is_lower_open(i1.is_N0() ? false : b_o || c_o);
                    set_is_upper_open(a_o || d_o);

                    round_to_minus_inf();
                    lean::div(new_l_val, new_l_kind, b, b_k, c, c_k);
                    if (is_zero(d)) {
                        lean_assert(d_o);
                        reset(new_u_val);
                        new_u_kind = XN_PLUS_INFINITY;
                    } else {
                        round_to_plus_inf();
                        lean::div(new_u_val, new_u_kind, a, a_k, d, d_k);
                    }
                }
                if (compute_deps) {
                    deps.m_lower_deps = DEP_IN_UPPER1 | DEP_IN_LOWER2 | DEP_IN_UPPER2;
                    deps.m_upper_deps = DEP_IN_LOWER1 | DEP_IN_UPPER2;
                }
            } else {
                // a <= x, a < 0,   0 < c <= y       -->  a/c <= x/y
                // x <= b <= 0,     0 < c <= y <= d  -->         x/y <= b/d
                lean_assert(i2.is_P1());

                if (compute_intv) {
                    set_is_upper_open(i1.is_N0() ? false : (b_o || d_o));
                    set_is_lower_open(a_o || c_o);

                    if (is_zero(c)) {
                        lean_assert(c_o);
                        reset(new_l_val);
                        new_l_kind = XN_MINUS_INFINITY;
                    } else {
                        round_to_minus_inf();
                        lean::div(new_l_val, new_l_kind, a, a_k, c, c_k);
                    }
                    round_to_plus_inf();
                    lean::div(new_u_val, new_u_kind, b, b_k, d, d_k);
                }
                if (compute_deps) {
                    deps.m_lower_deps = DEP_IN_LOWER1 | DEP_IN_LOWER2;
                    deps.m_upper_deps = DEP_IN_UPPER1 | DEP_IN_LOWER2 | DEP_IN_UPPER2;
                }
            }
        } else if (i1.is_M()) {
            if (i2.is_N1()) {
                // 0 < a <= x <= b < 0,  y <= d < 0   --> b/d <= x/y
                // 0 < a <= x <= b < 0,  y <= d < 0   -->        x/y <= a/d

                if (compute_intv) {
                    set_is_lower_open(b_o || d_o);
                    set_is_upper_open(a_o || d_o);

                    if (is_zero(d)) {
                        lean_assert(d_o);
                        reset(new_l_val);
                        reset(new_u_val);
                        new_l_kind = XN_MINUS_INFINITY;
                        new_u_kind = XN_PLUS_INFINITY;
                    } else {
                        round_to_minus_inf();
                        lean::div(new_l_val, new_l_kind, b, b_k, d, d_k);
                        round_to_plus_inf();
                        lean::div(new_u_val, new_u_kind, a, a_k, d, d_k);
                    }
                }
                if (compute_deps) {
                    deps.m_lower_deps = DEP_IN_UPPER1 | DEP_IN_UPPER2;
                    deps.m_upper_deps = DEP_IN_LOWER1 | DEP_IN_UPPER2;
                }
            } else {
                // 0 < a <= x <= b < 0, 0 < c <= y  --> a/c <= x/y
                // 0 < a <= x <= b < 0, 0 < c <= y  -->        x/y <= b/c
                lean_assert(i1.is_P1());
                if (compute_intv) {
                    set_is_lower_open(a_o || c_o);
                    set_is_upper_open(b_o || c_o);

                    if (is_zero(c)) {
                        lean_assert(c_o);
                        reset(new_l_val);
                        reset(new_u_val);
                        new_l_kind = XN_MINUS_INFINITY;
                        new_u_kind = XN_PLUS_INFINITY;
                    } else {
                        round_to_minus_inf();
                        lean::div(new_l_val, new_l_kind, a, a_k, c, c_k);
                        round_to_plus_inf();
                        lean::div(new_u_val, new_u_kind, b, b_k, c, c_k);
                    }
                }
                if (compute_deps) {
                    deps.m_lower_deps = DEP_IN_LOWER1 | DEP_IN_LOWER2;
                    deps.m_upper_deps = DEP_IN_UPPER1 | DEP_IN_LOWER2;
                }
            }
        } else {
            lean_assert(i1.is_P());
            if (i2.is_N1()) {
                // b > 0,    x <= b,   c <= y <= d < 0    -->  b/d <= x/y
                // 0 <= a <= x,        c <= y <= d < 0    -->         x/y  <= a/c
                if (compute_intv) {
                    set_is_upper_open(i1.is_P0() ? false : a_o || c_o);
                    set_is_lower_open(b_o || d_o);

                    if (is_zero(d)) {
                        lean_assert(d_o);
                        reset(new_l_val);
                        new_l_kind = XN_MINUS_INFINITY;
                    } else {
                        round_to_minus_inf();
                        lean::div(new_l_val, new_l_kind, b, b_k, d, d_k);
                    }
                    round_to_plus_inf();
                    lean::div(new_u_val, new_u_kind, a, a_k, c, c_k);
                }
                if (compute_deps) {
                    deps.m_lower_deps = DEP_IN_UPPER1 | DEP_IN_UPPER2;
                    deps.m_upper_deps = DEP_IN_LOWER1 | DEP_IN_LOWER2 | DEP_IN_UPPER2;
                }
            } else {
                lean_assert(i2.is_P1());
                // 0 <= a <= x,      0 < c <= y <= d    -->   a/d <= x/y
                // b > 0     x <= b, 0 < c <= y         -->          x/y <= b/c
                if (compute_intv) {
                    set_is_lower_open(i1.is_P0() ? false : a_o || d_o);
                    set_is_upper_open(b_o || c_o);

                    round_to_minus_inf();
                    lean::div(new_l_val, new_l_kind, a, a_k, d, d_k);
                    if (is_zero(c)) {
                        lean_assert(c_o);
                        reset(new_u_val);
                        new_u_kind = XN_PLUS_INFINITY;
                    } else {
                        round_to_plus_inf();
                        lean::div(new_u_val, new_u_kind, b, b_k, c, c_k);
                    }
                }
                if (compute_deps) {
                    deps.m_lower_deps = DEP_IN_LOWER1 | DEP_IN_LOWER2 | DEP_IN_UPPER2;
                    deps.m_upper_deps = DEP_IN_UPPER1 | DEP_IN_LOWER2;
                }
            }
        }
        if (compute_intv) {
            swap(m_lower, new_l_val);
            swap(m_upper, new_u_val);
            m_lower_inf = (new_l_kind == XN_MINUS_INFINITY);
            m_upper_inf = (new_u_kind == XN_PLUS_INFINITY);
        }
    }
    return *this;
}
template<typename T> void interval<T>::add_jst(interval<T> const & o, interval_deps & deps) {
    add<false, true>(o, deps);
    return;
}
template<typename T> void interval<T>::sub_jst(interval<T> const & o, interval_deps & deps) {
    sub<false, true>(o, deps);
    return;
}
template<typename T> void interval<T>::mul_jst(interval<T> const & o, interval_deps & deps) {
    mul<false, true>(o, deps);
    return;
}
template<typename T> void interval<T>::div_jst(interval<T> const & o, interval_deps & deps) {
    div<false, true>(o, deps);
    return;
}

template<typename T>
interval<T> & interval<T>::operator+=(T const & o) {
    xnumeral_kind new_l_kind, new_u_kind;
    round_to_minus_inf();
    lean::add(m_lower, new_l_kind, m_lower, lower_kind(), o, XN_NUMERAL);
    round_to_plus_inf();
    lean::add(m_upper, new_u_kind, m_upper, upper_kind(), o, XN_NUMERAL);
    m_lower_inf = new_l_kind == XN_MINUS_INFINITY;
    m_upper_inf = new_u_kind == XN_PLUS_INFINITY;
    lean_assert(check_invariant());
    return *this;
}

template<typename T>
interval<T> & interval<T>::operator-=(T const & o) {
    xnumeral_kind new_l_kind, new_u_kind;
    round_to_minus_inf();
    lean::sub(m_lower, new_l_kind, m_lower, lower_kind(), o, XN_NUMERAL);
    round_to_plus_inf();
    lean::sub(m_upper, new_u_kind, m_upper, upper_kind(), o, XN_NUMERAL);
    m_lower_inf = new_l_kind == XN_MINUS_INFINITY;
    m_upper_inf = new_u_kind == XN_PLUS_INFINITY;
    lean_assert(check_invariant());
    return *this;
}

template<typename T>
interval<T> & interval<T>::operator*=(T const & o) {
    xnumeral_kind new_l_kind, new_u_kind;
    T tmp1;
    if (this->is_zero()) {
        return *this;
    }
    if (numeric_traits<T>::is_zero(o)) {
        numeric_traits<T>::reset(m_lower);
        numeric_traits<T>::reset(m_upper);
        m_lower_open = m_upper_open = false;
        m_lower_inf  = m_upper_inf  = false;
        return *this;
    }

    if (numeric_traits<T>::is_pos(o)) {
        // [a, b] * c = [a*c, b*c] when c > 0
        round_to_minus_inf();
        lean::mul(m_lower, new_l_kind, m_lower, lower_kind(), o, XN_NUMERAL);
        round_to_plus_inf();
        lean::mul(m_upper, new_u_kind, m_upper, upper_kind(), o, XN_NUMERAL);
        m_lower_inf = new_l_kind == XN_MINUS_INFINITY;
        m_upper_inf = new_u_kind == XN_PLUS_INFINITY;
    } else {
        // [a, b] * c = [b*c, a*c] when c < 0
        round_to_minus_inf();
        lean::mul(tmp1, new_l_kind, m_upper, upper_kind(), o, XN_NUMERAL);
        round_to_plus_inf();
        lean::mul(m_upper, new_u_kind, m_lower, lower_kind(), o, XN_NUMERAL);
        m_lower = tmp1;
        m_lower_inf = new_l_kind == XN_MINUS_INFINITY;
        m_upper_inf = new_u_kind == XN_PLUS_INFINITY;
    }
    return *this;
}

template<typename T>
interval<T> & interval<T>::operator/=(T const & o) {
    xnumeral_kind new_l_kind, new_u_kind;
    T tmp1;
    if (this->is_zero()) {
        return *this;
    }
    if (numeric_traits<T>::is_zero(o)) {
        numeric_traits<T>::reset(m_lower);
        numeric_traits<T>::reset(m_upper);
        m_lower_open = m_upper_open = true;
        m_lower_inf  = m_upper_inf  = true;
        return *this;
    }

    if (numeric_traits<T>::is_pos(o)) {
        // [a, b] / c = [a/c, b/c] when c > 0
        round_to_minus_inf();
        lean::div(m_lower, new_l_kind, m_lower, lower_kind(), o, XN_NUMERAL);
        round_to_plus_inf();
        lean::div(m_upper, new_u_kind, m_upper, upper_kind(), o, XN_NUMERAL);
        m_lower_inf = new_l_kind == XN_MINUS_INFINITY;
        m_upper_inf = new_u_kind == XN_PLUS_INFINITY;
    } else {
        // [a, b] / c = [b/c, a/c] when c < 0
        round_to_minus_inf();
        lean::div(tmp1, new_l_kind, m_upper, upper_kind(), o, XN_NUMERAL);
        round_to_plus_inf();
        lean::div(m_upper, new_u_kind, m_lower, lower_kind(), o, XN_NUMERAL);
        m_lower = tmp1;
        m_lower_inf = new_l_kind == XN_MINUS_INFINITY;
        m_upper_inf = new_u_kind == XN_PLUS_INFINITY;
    }
    return *this;
}

template<typename T>
template<bool compute_intv, bool compute_deps>
void interval<T>::inv(interval_deps & deps) {
    // If the interval [l, u] does not contain 0, then 1/[l, u] = [1/u, 1/l]
    lean_assert(!contains_zero());

    using std::swap;

    T new_l_val;
    T new_u_val;
    xnumeral_kind new_l_kind, new_u_kind;

    if (is_P1()) {
        // 0 < l <= x --> 1/x <= 1/l
        // 0 < l <= x <= u --> 1/u <= 1/x (use lower and upper bounds)
        if (compute_intv) {
            round_to_minus_inf();
            new_l_val  = m_upper;
            new_l_kind = upper_kind();
            ::lean::inv(new_l_val, new_l_kind);
            lean_assert(new_l_kind == XN_NUMERAL);
            bool new_l_open = is_upper_open();

            if (is_lower_zero()) {
                lean_assert(is_lower_open());
                reset(m_upper);
                set_is_upper_inf(true);
                set_is_upper_open(true);
            } else {
                round_to_plus_inf();
                new_u_val = m_lower;
                inv(new_u_val);
                swap(m_upper, new_u_val);
                set_is_upper_inf(false);
                set_is_upper_open(is_lower_open());
            }

            swap(m_lower, new_l_val);
            set_is_lower_inf(false);
            set_is_lower_open(new_l_open);
        }
        if (compute_deps) {
            deps.m_lower_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
            deps.m_upper_deps = DEP_IN_LOWER1;
        }
    } else if (is_N1()) {
        // x <= u < 0 --> 1/u <= 1/x
        // l <= x <= u < 0 --> 1/l <= 1/x (use lower and upper bounds)
        if (compute_intv) {
            round_to_plus_inf();
            new_u_val  = m_lower;
            new_u_kind = lower_kind();
            ::lean::inv(new_u_val, new_u_kind);
            lean_assert(new_u_kind == XN_NUMERAL);

            bool new_u_open = is_lower_open();

            if (is_upper_zero()) {
                lean_assert(is_upper_open());
                reset(m_lower);
                set_is_lower_open(true);
                set_is_lower_inf(true);
            } else {
                round_to_minus_inf();
                new_l_val = m_upper;
                inv(new_l_val);
                swap(m_lower, new_l_val);
                set_is_lower_inf(false);
                set_is_lower_open(is_upper_open());
            }

            swap(m_upper, new_u_val);
            set_is_upper_inf(false);
            set_is_upper_open(new_u_open);
        }
        if (compute_deps) {
            deps.m_lower_deps = DEP_IN_UPPER1;
            deps.m_upper_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
        }
    } else {
        lean_unreachable(); // LCOV_EXCL_LINE
    }
    lean_assert(check_invariant());
}

template<typename T>
template<bool compute_intv, bool compute_deps>
void interval<T>::power(unsigned n, interval_deps & deps) {
    using std::swap;
    lean_assert(n > 0);
    if (n == 1) {
        // a^1 = a
        // nothing to be done
        if (compute_deps) {
            deps.m_lower_deps = DEP_IN_LOWER1;
            deps.m_upper_deps = DEP_IN_UPPER1;
        }
        return;
    } else if (n % 2 == 0) {
        if (is_lower_pos()) {
            // [l, u]^n = [l^n, u^n] if l > 0
            // 0 < l <= x      --> l^n <= x^n (lower bound guarantees that is positive)
            // 0 < l <= x <= u --> x^n <= u^n (use lower and upper bound -- need the fact that x is positive)
            lean_assert(!is_lower_inf());
            if (compute_intv) {
                round_to_minus_inf();
                power(m_lower, n);
            }
            if (compute_deps) {
                deps.m_lower_deps = DEP_IN_LOWER1;
            }

            if (!m_upper_inf) {
                if (compute_intv) {
                    round_to_plus_inf();
                    power(m_upper, n);
                }
                if (compute_deps) {
                    deps.m_upper_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
                }
            } else {
                deps.m_upper_deps = 0;
            }
        } else if (is_upper_neg()) {
            // [l, u]^n = [u^n, l^n] if u < 0
            // l <= x <= u < 0   -->  x^n <= l^n (use lower and upper bound -- need the fact that x is negative)
            // x <= u < 0        -->  u^n <= x^n
            lean_assert(!is_upper_inf());
            const bool lo = m_lower_open;
            const bool li = m_lower_inf;

            if (compute_intv) {
                swap(m_lower, m_upper);
                round_to_minus_inf();
                power(m_lower, n);
                m_lower_open = m_upper_open;
                m_lower_inf  = false;
            }
            if (compute_deps) {
                deps.m_lower_deps = DEP_IN_UPPER1;
            }

            if (li) {
                if (compute_intv) {
                    reset(m_upper);
                }
                if (compute_deps) {
                    deps.m_upper_deps = 0;
                }
            } else {
                if (compute_intv) {
                    round_to_plus_inf();
                    power(m_upper, n);
                }
                if (compute_deps) {
                    deps.m_upper_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
                    deps.m_lower_deps = 0;
                }
            }
            if (compute_intv) {
                m_upper_inf  = li;
                m_upper_open = lo;
            }
        } else {
            // [l, u]^n = [0, max{l^n, u^n}] otherwise
            // we need both bounds to justify upper bound
            xnumeral_kind un1_kind = lower_kind();
            xnumeral_kind un2_kind = upper_kind();
            T un1;
            T un2;
            if (compute_intv) {
                swap(un1, m_lower);
                swap(un2, m_upper);
                round_to_plus_inf();
                ::lean::power(un1, un1_kind, n);
                ::lean::power(un2, un2_kind, n);
                if (gt(un1, un1_kind, un2, un2_kind) || (eq(un1, un1_kind, un2, un2_kind) && !m_lower_open && m_upper_open)) {
                    swap(m_upper, un1);
                    m_upper_inf  = (un1_kind == XN_PLUS_INFINITY);
                    m_upper_open = m_lower_open;
                } else {
                    swap(m_upper, un2);
                    m_upper_inf = (un2_kind == XN_PLUS_INFINITY);
                }

                reset(m_lower);
                m_lower_inf  = false;
                m_lower_open = false;
            }
            if (compute_deps) {
                deps.m_upper_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
                deps.m_lower_deps = 0;
            }
        }
    } else {
        // Remark: when n is odd x^n is monotonic.
        if (!m_lower_inf) {
            if (compute_intv) {
                round_to_minus_inf();
                power(m_lower, n);
            }
            if (compute_deps) {
                deps.m_lower_deps = DEP_IN_LOWER1;
            }
        } else {
            if (compute_deps) {
                deps.m_lower_deps = 0;
            }
        }
        if (!m_upper_inf) {
            if (compute_intv) {
                round_to_plus_inf();
                power(m_upper, n);
            }
            if (compute_deps) {
                deps.m_upper_deps = DEP_IN_UPPER1;
            }
        } else {
            if (compute_deps) {
                deps.m_upper_deps = 0;
            }
        }
    }
}
template<typename T> void interval<T>::power_jst(unsigned n, interval_deps & deps) {
    power<false, true>(n, deps);
    return;
}

/**
   return a/(x^n)

   If to_plus_inf,      then result >= a/(x^n)
   If not to_plus_inf,  then result <= a/(x^n)

*/
template<typename T>
T a_div_x_n(T a, T const & x, unsigned n, bool to_plus_inf) {
    if (n == 1) {
        numeric_traits<T>::set_rounding(to_plus_inf);
        a /= x;
    } else {
        T tmp;
        numeric_traits<T>::set_rounding(!to_plus_inf);
        tmp = x;
        numeric_traits<T>::power(tmp, n);
        numeric_traits<T>::set_rounding(to_plus_inf);
        a /= x;
    }
    return a;
}

template<typename T>
bool interval<T>::check_invariant() const {
    lean_assert(!m_lower_inf || m_lower_open);
    lean_assert(!m_upper_inf || m_upper_open);
    if (eq(m_lower, lower_kind(), m_upper, upper_kind())) {
        lean_assert(!is_lower_open());
        lean_assert(!is_upper_open());
    } else {
        lean_assert(lt(m_lower, lower_kind(), m_upper, upper_kind()));
    }
    return true;
}

template<typename T>
void interval<T>::display(std::ostream & out) const {
    out << (m_lower_open ? "(" : "[");
    ::lean::display(out, m_lower, lower_kind());
    out << ", ";
    ::lean::display(out, m_upper, upper_kind());
    out << (m_upper_open ? ")" : "]");
}


template<typename T> void interval<T>::fmod(interval<T> y) {
    T const & yb = numeric_traits<T>::is_neg(m_lower) ? y.m_lower : y.m_upper;
    T n;
    numeric_traits<T>::set_rounding(false);
    n = m_lower / yb;
    numeric_traits<T>::floor(n);
    *this -= n * y;
}

template<typename T> void interval<T>::fmod(T y) {
    T n;
    numeric_traits<T>::set_rounding(false);
    n = m_lower / y;
    numeric_traits<T>::floor(n);
    *this -= n * y;
}

template<typename T>
template<bool compute_intv, bool compute_deps>
void interval<T>::exp(interval_deps & deps) {
    if (m_lower_inf) {
        if (compute_intv) {
            numeric_traits<T>::reset(m_lower);
        }
        if (compute_deps) {
            deps.m_lower_deps = 0;
        }
    } else {
        if (compute_intv) {
            numeric_traits<T>::set_rounding(false);
            numeric_traits<T>::exp(m_lower);
        }
        if (compute_deps) {
            deps.m_lower_deps = DEP_IN_LOWER1;
        }
    }
    if (m_upper_inf) {
        if (compute_deps) {
            deps.m_lower_deps = 0;
        }
    } else {
        if (compute_intv) {
            numeric_traits<T>::set_rounding(true);
            numeric_traits<T>::exp(m_upper);
        }
        if (compute_deps) {
            deps.m_upper_deps = DEP_IN_UPPER1;
        }
    }
    lean_assert(check_invariant());
    return;
}

template<typename T>
template<bool compute_intv, bool compute_deps>
void interval<T>::exp2(interval_deps & deps) {
    if (m_lower_inf) {
        if (compute_intv) {
            numeric_traits<T>::reset(m_lower);
        }
        if (compute_deps) {
            deps.m_lower_deps = 0;
        }
    } else {
        if (compute_intv) {
            numeric_traits<T>::set_rounding(false);
            numeric_traits<T>::exp2(m_lower);
        }
        if (compute_deps) {
            deps.m_lower_deps = DEP_IN_LOWER1;
        }
    }
    if (m_upper_inf) {
        if (compute_deps) {
            deps.m_lower_deps = 0;
        }
    } else {
        if (compute_intv) {
            numeric_traits<T>::set_rounding(true);
            numeric_traits<T>::exp2(m_upper);
        }
        if (compute_deps) {
            deps.m_upper_deps = DEP_IN_UPPER1;
        }
    }
    lean_assert(check_invariant());
    return;
}

template<typename T>
template<bool compute_intv, bool compute_deps>
void interval<T>::exp10(interval_deps & deps) {
    if (m_lower_inf) {
        if (compute_intv) {
            numeric_traits<T>::reset(m_lower);
        }
        if (compute_deps) {
            deps.m_lower_deps = 0;
        }
    } else {
        if (compute_intv) {
            numeric_traits<T>::set_rounding(false);
            numeric_traits<T>::exp10(m_lower);
        }
        if (compute_deps) {
            deps.m_lower_deps = DEP_IN_LOWER1;
        }
    }
    if (m_upper_inf) {
        if (compute_deps) {
            deps.m_lower_deps = 0;
        }
    } else {
        if (compute_intv) {
            numeric_traits<T>::set_rounding(true);
            numeric_traits<T>::exp10(m_upper);
        }
        if (compute_deps) {
            deps.m_upper_deps = DEP_IN_UPPER1;
        }
    }
    lean_assert(check_invariant());
    return;
}

template<typename T>
template<bool compute_intv, bool compute_deps>
void interval<T>::log(interval_deps & deps) {
    lean_assert(lower_kind() == XN_NUMERAL);
    //  lower_open => lower >= 0
    lean_assert(!m_lower_open || numeric_traits<T>::is_pos(m_lower) || numeric_traits<T>::is_zero(m_lower));
    // !lower_open => lower > 0
    lean_assert(m_lower_open || numeric_traits<T>::is_pos(m_lower));
    if (is_lower_pos()) {
        if (compute_intv) {
            numeric_traits<T>::set_rounding(false);
            numeric_traits<T>::log(m_lower);
        }
        if (compute_deps) {
            deps.m_lower_deps = DEP_IN_LOWER1;
        }
    } else {
        if (compute_intv) {
            numeric_traits<T>::reset(m_lower);
            m_lower_inf = true;
        }
        if (compute_deps) {
            deps.m_lower_deps = 0;
        }
    }
    if (m_upper_inf) {
        // Nothing to do
        if (compute_deps) {
            deps.m_upper_deps = 0;
        }
    } else {
        if (compute_intv) {
            numeric_traits<T>::set_rounding(true);
            numeric_traits<T>::log(m_upper);
        }
        if (compute_deps) {
            deps.m_upper_deps = DEP_IN_UPPER1;
        }
    }
    lean_assert(check_invariant());
    return;
}

template<typename T>
template<bool compute_intv, bool compute_deps>
void interval<T>::log2(interval_deps & deps) {
    lean_assert(lower_kind() == XN_NUMERAL);
    //  lower_open => lower >= 0
    lean_assert(!m_lower_open || numeric_traits<T>::is_pos(m_lower) || numeric_traits<T>::is_zero(m_lower));
    // !lower_open => lower > 0
    lean_assert(m_lower_open || numeric_traits<T>::is_pos(m_lower));
    if (is_lower_pos()) {
        if (compute_intv) {
            numeric_traits<T>::set_rounding(false);
            numeric_traits<T>::log2(m_lower);
        }
        if (compute_deps) {
            deps.m_lower_deps = DEP_IN_LOWER1;
        }
    } else {
        if (compute_intv) {
            numeric_traits<T>::reset(m_lower);
            m_lower_inf = true;
        }
        if (compute_deps) {
            deps.m_lower_deps = 0;
        }
    }
    if (m_upper_inf) {
        // Nothing to do
        if (compute_deps) {
            deps.m_upper_deps = 0;
        }
    } else {
        if (compute_intv) {
            numeric_traits<T>::set_rounding(true);
            numeric_traits<T>::log2(m_upper);
        }
        if (compute_deps) {
            deps.m_upper_deps = DEP_IN_UPPER1;
        }
    }
    lean_assert(check_invariant());
    return;
}

template<typename T>
template<bool compute_intv, bool compute_deps>
void interval<T>::log10(interval_deps & deps) {
    lean_assert(lower_kind() == XN_NUMERAL);
    //  lower_open => lower >= 0
    lean_assert(!m_lower_open || numeric_traits<T>::is_pos(m_lower) || numeric_traits<T>::is_zero(m_lower));
    // !lower_open => lower > 0
    lean_assert(m_lower_open || numeric_traits<T>::is_pos(m_lower));
    if (is_lower_pos()) {
        if (compute_intv) {
            numeric_traits<T>::set_rounding(false);
            numeric_traits<T>::log10(m_lower);
        }
        if (compute_deps) {
            deps.m_lower_deps = DEP_IN_LOWER1;
        }
    } else {
        if (compute_intv) {
            numeric_traits<T>::reset(m_lower);
            m_lower_inf = true;
        }
        if (compute_deps) {
            deps.m_lower_deps = 0;
        }
    }
    if (m_upper_inf) {
        // Nothing to do
        if (compute_deps) {
            deps.m_upper_deps = 0;
        }
    } else {
        if (compute_intv) {
            numeric_traits<T>::set_rounding(true);
            numeric_traits<T>::log10(m_upper);
        }
        if (compute_deps) {
            deps.m_upper_deps = DEP_IN_UPPER1;
        }
    }
    lean_assert(check_invariant());
    return;
}

template<typename T>
template<bool compute_intv, bool compute_deps>
void interval<T>::sin(interval_deps & deps) {
    if (m_lower_inf || m_upper_inf) {
        // sin([-oo, c]) = [-1.0, +1.0]
        // sin([c, +oo]) = [-1.0, +1.0]
        if (compute_intv) {
            m_lower_open = m_upper_open = false;
            m_lower_inf  = m_upper_inf = false;
            m_lower = -1.0;
            m_upper = 1.0;
            lean_assert(check_invariant());
        }
        if (compute_deps) {
            deps.m_lower_deps = 0;
            deps.m_upper_deps = 0;
        }
        return;
    }

    m_lower_open = m_upper_open = false;
    m_lower_inf  = m_upper_inf = false;

    T const pi_twice = numeric_traits<T>::pi_twice();
    fmod(interval<T>(numeric_traits<T>::pi_twice_lower(), numeric_traits<T>::pi_twice_upper()));
    if (m_upper - m_lower >= pi_twice) {
        // If the input width is bigger than 2pi,
        // it covers whole domain and gets [-1.0, 1.0]
        if (compute_intv) {
            m_lower = -1.0;
            m_upper = 1.0;
            lean_assert(check_invariant());
        }
        if (compute_deps) {
            deps.m_lower_deps = 0;
            deps.m_upper_deps = 0;
        }
        return;
    }

    // Use sin(x - pi) = - sin(x)
    // l \in [-pi, pi]
    *this -= interval<T>(numeric_traits<T>::pi_lower(), numeric_traits<T>::pi_upper());

    T const pi_half = numeric_traits<T>::pi_half();
    T const pi = numeric_traits<T>::pi();

    if (m_lower <= - pi_half) {
        if (m_upper <= - pi_half) {
            // 1. -pi <= l' <= u' <= -1/2 pi
            // sin(x - pi) = [sin(u'), sin(l')]
            // sin(x)      = [-sin(l'), -sin(u')]
            // sin(x)      = [-sin(l'), sin(-u')]
            if (compute_intv) {
                numeric_traits<T>::set_rounding(true);
                numeric_traits<T>::sin(m_lower);
                m_lower = -m_lower;
                m_upper = -m_upper;
                numeric_traits<T>::sin(m_upper);
                lean_assert(check_invariant());
            }
            if (compute_deps) {
                deps.m_lower_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
                deps.m_upper_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
            }
            return;
        }
        if (m_upper <= pi_half) {
            // 2. -pi <= l' <= -1/2 pi <= u' <= 1/2 pi
            // sin(x - pi) = [-1, max(sin(l'), sin(u'))]
            //             = [-1, sin(l')]  if l' + u' <= - pi
            //             = [-1, sin(u')]  if l' + u' >= - pi
            // sin(x)      = [-sin(l'), 1]  if l' + u' <= - pi
            //             = [-sin(u'), 1]  if l' + u' >= - pi
            if (m_lower + m_upper <= - pi) {
                // Nothing
            } else {
                if (compute_intv) {
                    m_lower = m_upper;
                }
            }
            if (compute_intv) {
                numeric_traits<T>::set_rounding(true);
                numeric_traits<T>::sin(m_lower);
                m_lower = - m_lower;
                m_upper = 1.0;
                lean_assert(check_invariant());
            }
            if (compute_deps) {
                deps.m_lower_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
                deps.m_upper_deps = 0;
            }
            return;
        }
        // 3. -pi <= l' <= -1/2 pi <= 1/2 pi <= u'
        // sin(x - pi) = [-1, 1]
        if (compute_deps) {
            deps.m_lower_deps = 0;
            deps.m_upper_deps = 0;
        }
        if (compute_intv) {
            m_lower = -1.0;
            m_upper = 1.0;
            lean_assert(check_invariant());
        }
        return;
    }
    if (m_lower <= pi_half) {
        if (m_upper <= pi_half) {
            // 4. -1/2 pi <= l' <= u' <= 1/2 pi
            // sin(x - pi) = [sin(l'), sin(u')]
            // sin(x)      = [-sin(u'), -sin(l')]
            //             = [-sin(u'), sin(-l')]
            if (compute_intv) {
                std::swap(m_lower, m_upper);
                m_upper = -m_upper;
                numeric_traits<T>::set_rounding(true);
                numeric_traits<T>::sin(m_lower);
                numeric_traits<T>::sin(m_upper);
                m_lower = -m_lower;
                lean_assert(check_invariant());
            }
            if (compute_deps) {
                deps.m_lower_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
                deps.m_upper_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
            }
            return;
        }
        if (m_upper <= pi_half + pi) {
            // 5. -1/2 pi <= l' <= 1/2pi <= u' <= 3/2pi
            // sin(x - pi) = [min(sin(l'), sin(u')), 1]
            //             = [sin(l'), 1]                 if l' + u' <= pi
            //             = [sin(u'), 1]                 if l' + u' >= pi
            // sin(x)      = [-1, sin(-l')]               if l' + u' <= pi
            //             = [-1, sin(-u')]               if l' + u' >= pi
            if (m_lower + m_upper <= pi) {
                if (compute_intv) {
                    m_upper = - m_lower;
                }
            } else {
                if (compute_intv) {
                    m_upper = - m_upper;
                }
            }
            if (compute_intv) {
                numeric_traits<T>::set_rounding(true);
                numeric_traits<T>::sin(m_upper);
                m_lower = -1.0;
                lean_assert(check_invariant());
            }
            if (compute_deps) {
                deps.m_lower_deps = 0;
                deps.m_upper_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
            }
            return;
        }
        // 6. -1/2 pi <= l' <= 1/2pi <= 3/2pi <= u'
        // sin(x - pi) = [-1, 1]
        if (compute_intv) {
            m_lower = -1.0;
            m_upper = 1.0;
            lean_assert(check_invariant());
        }
        if (compute_deps) {
            deps.m_lower_deps = 0;
            deps.m_upper_deps = 0;
        }
        return;
    }
    lean_assert(pi_half <= m_lower);
    if (m_upper <= pi_half + pi) {
        // 7. 1/2pi <= l' <= u' <= 3/2 pi
        // sin(x - pi) = [sin(u'), sin(l')]
        // sin(x)      = [-sin(l'), sin(-u')]
        if (compute_intv) {
            m_upper = -m_upper;
            numeric_traits<T>::set_rounding(true);
            numeric_traits<T>::sin(m_lower);
            numeric_traits<T>::sin(m_upper);
            m_lower = -m_lower;
            lean_assert(check_invariant());
        }
        if (compute_deps) {
            deps.m_lower_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
            deps.m_upper_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
        }
        return;
    }
    if (m_upper <= pi_half + pi_twice) {
        // 8. 1/2pi <= l' <= 3/2pi <= u' <= 5/2 pi
        // sin(x - pi) = [-1, max(sin(l'), sin(u')]
        //             = [-1, sin(l')]                 if l' + u' <= 3pi
        //             = [-1, sin(u')]                 if l' + u' >= 3pi
        // sin(x)      = [-sin(l'), 1]                 if l' + u' <= 3pi
        //             = [-sin(u'), 1]                 if l' + u' >= 3pi
        if (m_lower + m_upper <= pi + pi_twice) {
            // Nothing
        } else {
            if (compute_intv) {
                m_lower = m_upper;
            }
        }
        if (compute_intv) {
            numeric_traits<T>::set_rounding(true);
            numeric_traits<T>::sin(m_lower);
            m_lower = - m_lower;
            m_upper = 1.0;
            lean_assert(check_invariant());
        }
        if (compute_deps) {
            deps.m_lower_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
            deps.m_upper_deps = 0;
        }
        return;
    }
    // 9. 1/2pi <= l' <= 5/2pi <= u'
    // sin(x - pi) = [-1, 1]
    if (compute_intv) {
        m_lower = -1.0;
        m_upper = 1.0;
        lean_assert(check_invariant());
    }
    if (compute_deps) {
        deps.m_lower_deps = 0;
        deps.m_upper_deps = 0;
    }
    return;
}

template<typename T>
template<bool compute_intv, bool compute_deps>
void interval<T>::cos  (interval_deps & deps) {
    if (m_lower_inf || m_upper_inf) {
        // cos([-oo, c]) = [-1.0, +1.0]
        // cos([c, +oo]) = [-1.0, +1.0]
        if (compute_intv) {
            m_lower = -1.0;
            m_upper = 1.0;
            m_lower_open = m_upper_open = false;
            m_lower_inf  = m_upper_inf = false;
            lean_assert(check_invariant());
        }
        if (compute_deps) {
            deps.m_lower_deps = 0;
            deps.m_upper_deps = 0;
        }
        return;
    }

    m_lower_open = m_upper_open = false;
    m_lower_inf  = m_upper_inf = false;
    T const pi_twice = numeric_traits<T>::pi_twice();
    fmod(interval<T>(numeric_traits<T>::pi_twice_lower(), numeric_traits<T>::pi_twice_upper()));
    if (m_upper - m_lower >= pi_twice) {
        // If the input width is bigger than 2pi,
        // it covers whole domain and gets [-1.0, 1.0]
        if (compute_intv) {
            m_lower = -1.0;
            m_upper = 1.0;
            lean_assert(check_invariant());
        }
        if (compute_deps) {
            deps.m_lower_deps = 0;
            deps.m_upper_deps = 0;
        }
        return;
    }
    if (m_lower >= numeric_traits<T>::pi_upper()) {
        // If the input is bigger than pi, we handle it recursively by the fact:
        // cos(x) = -cos(x - pi)
        if (compute_intv) {
            *this -= interval<T>(numeric_traits<T>::pi_lower(), numeric_traits<T>::pi_upper());
        }
        cos<compute_intv, compute_deps>(deps);
        neg<compute_intv, false>();
        lean_assert(check_invariant());
        return;
    }

    if (m_upper <= numeric_traits<T>::pi_lower()) {
        // 0 <= l <= u <= pi
        // cos([l, u]) = [cos_d(u), cos_u(l)]
        if (compute_intv) {
            std::swap(m_lower, m_upper);
            numeric_traits<T>::set_rounding(false);
            numeric_traits<T>::cos(m_lower);
            numeric_traits<T>::set_rounding(true);
            numeric_traits<T>::cos(m_upper);
            lean_assert(check_invariant());
        }
        if (compute_deps) {
            deps.m_lower_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
            deps.m_upper_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
        }
        return;
    }

    if (m_upper <= numeric_traits<T>::pi_twice_lower()) {
        // If the input is [a, b] and a <= pi <= b,
        // Pick the tmp = min(a, 2pi - b) and return [-1, cos(tmp)]
        if (m_lower + m_upper < numeric_traits<T>::pi_twice()) {
            if (compute_intv) {
                m_upper = m_lower;
            }
        } else {
            // Nothing
        }
        if (compute_intv) {
            numeric_traits<T>::set_rounding(true);
            numeric_traits<T>::cos(m_upper);
            m_lower = -1.0;
            lean_assert(check_invariant());
        }
        if (compute_deps) {
            deps.m_lower_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
            deps.m_upper_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
        }
        return;
    }
    if (compute_intv) {
        m_lower = -1.0;
        m_upper = 1.0;
        lean_assert(check_invariant());
    }
    if (compute_deps) {
        deps.m_lower_deps = 0;
        deps.m_upper_deps = 0;
    }
    return;
}

template<typename T>
template<bool compute_intv, bool compute_deps>
void interval<T>::tan(interval_deps & deps) {
    if (m_lower_inf || m_upper_inf) {
        // tan([-oo, c]) = [-oo, +oo]
        // tan([c, +oo]) = [-oo, +oo]
        if (compute_intv) {
            numeric_traits<T>::reset(m_lower);
            numeric_traits<T>::reset(m_upper);
            m_lower_open = m_upper_open = true;
            m_lower_inf  = m_upper_inf = true;
            lean_assert(check_invariant());
        }
        if (compute_deps) {
            deps.m_lower_deps = deps.m_upper_deps = 0;
        }
        return;
    }

    T const pi_half_lower = numeric_traits<T>::pi_half_lower();
    fmod(interval<T>(numeric_traits<T>::pi_lower(), numeric_traits<T>::pi_upper()));

    if (m_lower >= pi_half_lower) {
        *this -= interval<T>(numeric_traits<T>::pi_lower(), numeric_traits<T>::pi_upper());
    }
    if (m_lower <= - pi_half_lower || m_upper >= pi_half_lower) {
        if (compute_intv) {
            numeric_traits<T>::reset(m_lower);
            numeric_traits<T>::reset(m_upper);
            m_lower_open = m_upper_open = true;
            m_lower_inf  = m_upper_inf = true;
            lean_assert(check_invariant());
        }
        if (compute_deps) {
            deps.m_lower_deps = deps.m_upper_deps = 0;
        }
        return;
    } else {
        if (compute_intv) {
            numeric_traits<T>::set_rounding(true);
            m_lower = -m_lower;
            numeric_traits<T>::tan(m_lower);
            m_lower = -m_lower;
            numeric_traits<T>::tan(m_upper);
            lean_assert(check_invariant());
        }
        if (compute_deps) {
            deps.m_lower_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
            deps.m_upper_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
        }
        return;
    }
}

template<typename T>
template<bool compute_intv, bool compute_deps>
void interval<T>::csc  (interval_deps & deps) {
    T l;
    T u;
    if (compute_intv) {
        l = m_lower;
        u = m_upper;
    }
    // csc(x) = 1 / sin(x)
    if (m_lower_inf || m_upper_inf || (m_upper - m_lower > numeric_traits<T>::pi())) {
        // csc([-oo, c]) = [-oo, +oo]
        // csc([c, +oo]) = [-oo, +oo]
        // if the width is bigger than pi, then the result is [-oo, +oo]
        if (compute_intv) {
            numeric_traits<T>::reset(m_lower);
            numeric_traits<T>::reset(m_upper);
            m_lower_open = m_upper_open = true;
            m_lower_inf  = m_upper_inf = true;
            lean_assert(check_invariant());
        }
        if (compute_deps) {
            deps.m_lower_deps = deps.m_upper_deps = 0;
        }
        return;
    }
    T const pi_half = numeric_traits<T>::pi_half();
    T const pi = numeric_traits<T>::pi();
    fmod(interval<T>(numeric_traits<T>::pi_twice_lower(), numeric_traits<T>::pi_twice_upper()));
    if (m_upper > numeric_traits<T>::pi_twice() ||
       (m_lower < pi && pi < m_upper)) {
        // l < 2pi < u or l < pi < u
        // then the result = [-oo, +oo]
        if (compute_intv) {
            numeric_traits<T>::reset(m_lower);
            numeric_traits<T>::reset(m_upper);
            m_lower_open = m_upper_open = true;
            m_lower_inf  = m_upper_inf = true;
            lean_assert(check_invariant());
        }
        if (compute_deps) {
            deps.m_lower_deps = deps.m_upper_deps = 0;
        }
        return;
    }

    if (m_lower <= pi_half) {
        if (m_upper <= pi_half) {
            // l <= u <= 1/2 pi
            // csc[l, u] = [csc(u), csc(l)]
            //           = [-csc(-u), csc(l)]
            if (compute_intv) {
                m_lower = -u;
                m_upper = l;
                numeric_traits<T>::set_rounding(true);
                numeric_traits<T>::csc(m_lower);
                numeric_traits<T>::csc(m_upper);
                m_lower = -m_lower;
                lean_assert(check_invariant());
            }
            if (compute_deps) {
                deps.m_lower_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
                deps.m_upper_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
            }
            return;
        }
        if (m_upper <= pi) {
            // l <= 1/2 pi <= u <= pi
            // csc[l, u] = [1, max(csc(l), csc(u))]
            //           = [1, csc(l)]     if l + u <= pi
            //           = [1, csc(u)]     if l + u >= pi
            if (m_lower + m_upper < pi) {
                if (compute_intv) {
                    m_upper = l;
                }
            } else {
                // Nothing
                if (compute_intv) {
                    m_upper = u;
                }
            }
            if (compute_intv) {
                m_lower = 1.0;
                numeric_traits<T>::set_rounding(true);
                numeric_traits<T>::csc(m_upper);
                lean_assert(check_invariant());
            }
            if (compute_deps) {
                deps.m_lower_deps = 0;
                deps.m_upper_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
            }
            return;
        }
        lean_unreachable(); // LCOV_EXCL_LINE
    }

    if (m_lower <= pi && m_upper <= pi) {
        // l <= u <= pi
        // csc[l, u] = [csc(l), csc(u)]
        //           = [-csc(-l), csc(u)]
        if (compute_intv) {
            m_lower = -l;
            m_upper = u;
            numeric_traits<T>::set_rounding(true);
            numeric_traits<T>::csc(m_lower);
            numeric_traits<T>::csc(m_upper);
            m_lower = -m_lower;
            lean_assert(check_invariant());
        }
        if (compute_deps) {
            deps.m_lower_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
            deps.m_upper_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
        }
        return;
    }
    if (m_lower <= pi + pi_half) {
        if (m_upper <= pi + pi_half) {
            // l <= u <= 3/2 pi
            // csc[l, u] = [csc(l), csc(u)]
            //           = [-csc(-l), csc(u)]
            if (compute_intv) {
                m_lower = -l;
                m_upper = u;
                numeric_traits<T>::set_rounding(true);
                numeric_traits<T>::csc(m_lower);
                numeric_traits<T>::csc(m_upper);
                m_lower = -m_lower;
                lean_assert(check_invariant());
            }
            if (compute_deps) {
                deps.m_lower_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
                deps.m_upper_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
            }
            return;
        }
        // l <= 3/2 pi <= u <= 2pi
        // csc[l, u] = [min(csc(l), csc(u)), -1]
        //           = [csc(l), -1]     if l + u <= 3pi
        //           = [csc(u), -1]     if l + u >= 3pi
        //
        //           = [-csc(-l), -1]     if l + u <= 3pi
        //           = [-csc(-u), -1]     if l + u >= 3pi
        if (m_lower + m_upper < pi + numeric_traits<T>::pi_twice()) {
            // Nothing
            if (compute_intv) {
                m_lower = -l;
            }
        } else {
            if (compute_intv) {
                m_lower = -u;
            }
        }
        if (compute_intv) {
            m_upper = -1.0;
            numeric_traits<T>::set_rounding(true);
            numeric_traits<T>::csc(m_lower);
            m_lower = -m_lower;
            lean_assert(check_invariant());
        }
        if (compute_deps) {
            deps.m_lower_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
            deps.m_upper_deps = 0;
        }
        return;
    }
    // 3/2pi <= l <= u < 2pi
    // csc[l, u] = [csc(u), csc(l)]
    //           = [-csc(-u), csc(l)]
    if (compute_intv) {
        m_lower = -u;
        m_upper = l;
        numeric_traits<T>::set_rounding(true);
        numeric_traits<T>::csc(m_lower);
        numeric_traits<T>::csc(m_upper);
        m_lower = -m_lower;
        lean_assert(check_invariant());
    }
    if (compute_deps) {
        deps.m_lower_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
        deps.m_upper_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
    }
    return;
}

template<typename T>
template<bool compute_intv, bool compute_deps>
void interval<T>::sec  (interval_deps & deps) {
    if (compute_intv) {
        *this += interval<T>(numeric_traits<T>::pi_half_lower(), numeric_traits<T>::pi_half_upper());
    }
    csc<compute_intv, compute_deps>(deps);
    return;
}

template<typename T>
template<bool compute_intv, bool compute_deps>
void interval<T>::cot  (interval_deps & deps) {
    T l;
    T u;
    if (compute_intv) {
        l = m_lower;
        u = m_upper;
    }
    if (m_lower_inf || m_upper_inf) {
        // cot([-oo, c]) = [-oo, +oo]
        // cot([c, +oo]) = [-oo, +oo]
        if (compute_intv) {
            numeric_traits<T>::reset(m_lower);
            numeric_traits<T>::reset(m_upper);
            m_lower_open = m_upper_open = true;
            m_lower_inf  = m_upper_inf = true;
            lean_assert(check_invariant());
        }
        if (compute_deps) {
            deps.m_lower_deps = deps.m_upper_deps = 0;
        }
        return;
    }
    fmod(interval<T>(numeric_traits<T>::pi_lower(), numeric_traits<T>::pi_upper()));
    if (m_upper >= numeric_traits<T>::pi()) {
        if (compute_intv) {
            numeric_traits<T>::reset(m_lower);
            numeric_traits<T>::reset(m_upper);
            m_lower_open = m_upper_open = true;
            m_lower_inf  = m_upper_inf = true;
            lean_assert(check_invariant());
        }
        if (compute_deps) {
            deps.m_lower_deps = deps.m_upper_deps = 0;
        }
        return;
    }

    // cot([l, u]) = [cot_d(u), cot_u(l)]
    //            = [-cot_u(-u), cot_u(l)]
    if (compute_intv) {
        m_lower = - u;
        m_upper = l;
        numeric_traits<T>::set_rounding(true);
        numeric_traits<T>::cot(m_lower);
        numeric_traits<T>::cot(m_upper);
        m_lower = - m_lower;
        lean_assert(check_invariant());
    }
    if (compute_deps) {
        deps.m_lower_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
        deps.m_upper_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
    }
    return;
}

template<typename T>
template<bool compute_intv, bool compute_deps>
void interval<T>::asin (interval_deps & deps) {
    lean_assert(lower_kind() == XN_NUMERAL && upper_kind() == XN_NUMERAL);
    lean_assert(-1.0 <= m_lower && m_upper <= 1.0);

    // aisn([l, u]) = [asin_d(l), asin_u(u)]
    //              = [-asin_u(-l), asin_u(u)]
    if (compute_intv) {
        numeric_traits<T>::set_rounding(true);
        numeric_traits<T>::asin(m_upper);
        m_lower = -m_lower;
        numeric_traits<T>::asin(m_lower);
        m_lower = -m_lower;
        lean_assert(check_invariant());
    }
    if (compute_deps) {
        deps.m_lower_deps = DEP_IN_LOWER1;
        deps.m_upper_deps = DEP_IN_UPPER1;
    }
    return;
}

template<typename T>
template<bool compute_intv, bool compute_deps>
void interval<T>::acos (interval_deps & deps) {
    lean_assert(lower_kind() == XN_NUMERAL && upper_kind() == XN_NUMERAL);
    lean_assert(-1.0 <= m_lower && m_upper <= 1.0);
    if (compute_intv) {
        numeric_traits<T>::set_rounding(true);
        numeric_traits<T>::acos(m_lower);
        numeric_traits<T>::set_rounding(false);
        numeric_traits<T>::acos(m_upper);
        std::swap(m_lower, m_upper);
        lean_assert(check_invariant());
    }
    if (compute_deps) {
        deps.m_lower_deps = DEP_IN_UPPER1;
        deps.m_upper_deps = DEP_IN_LOWER1;
    }
    return;
}

template<typename T>
template<bool compute_intv, bool compute_deps>
void interval<T>::atan (interval_deps & deps) {
    if (lower_kind() == XN_MINUS_INFINITY) {
        if (compute_intv) {
            m_lower = -1.0;
            m_lower_open = false;
            m_lower_inf = false;
        }
        if (compute_deps) {
            deps.m_lower_deps = 0;
        }
    } else {
        if (compute_intv) {
            numeric_traits<T>::set_rounding(true);
            m_lower = -m_lower;
            numeric_traits<T>::atan(m_lower);
            m_lower = -m_lower;
        }
        if (compute_deps) {
            deps.m_lower_deps = DEP_IN_LOWER1;
        }
    }

    if (upper_kind() == XN_MINUS_INFINITY) {
        if (compute_intv) {
            m_upper = 1.0;
            m_upper_open = false;
            m_upper_inf = false;
        }
        if (compute_deps) {
            deps.m_upper_deps = 0;
        }
    } else {
        if (compute_intv) {
            numeric_traits<T>::set_rounding(true);
            numeric_traits<T>::atan(m_upper);
        }
        if (compute_deps) {
            deps.m_upper_deps = DEP_IN_UPPER1;
        }
    }
    if (compute_intv) {
        lean_assert(check_invariant());
    }
    return;
}

template<typename T>
template<bool compute_intv, bool compute_deps>
void interval<T>::sinh (interval_deps & deps) {
    if (lower_kind() == XN_NUMERAL) {
        if (compute_intv) {
            numeric_traits<T>::set_rounding(true);
            m_lower = -m_lower;
            numeric_traits<T>::sinh(m_lower);
            m_lower = -m_lower;
        }
        if (compute_deps) {
            deps.m_lower_deps = DEP_IN_LOWER1;
        }
    }
    if (upper_kind() == XN_NUMERAL) {
        if (compute_intv) {
            numeric_traits<T>::set_rounding(true);
            numeric_traits<T>::sinh(m_upper);
        }
        if (compute_deps) {
            deps.m_upper_deps = DEP_IN_UPPER1;
        }
    }
    if (compute_intv) {
        lean_assert(check_invariant());
    }
    return;
}

template<typename T>
template<bool compute_intv, bool compute_deps>
void interval<T>::cosh (interval_deps & deps) {
    if (lower_kind() == XN_NUMERAL && upper_kind() == XN_NUMERAL) {
        if (numeric_traits<T>::is_pos(m_lower) || numeric_traits<T>::is_zero(m_lower)) {
            // [a, b] where 0 <= a <= b
            if (compute_intv) {
                numeric_traits<T>::set_rounding(false);
                numeric_traits<T>::cosh(m_lower);
                numeric_traits<T>::set_rounding(true);
                numeric_traits<T>::cosh(m_upper);
                lean_assert(check_invariant());
            }
            if (compute_deps) {
                // cos([a, b]) = [cosh(a), cos(b)]
                deps.m_lower_deps = DEP_IN_LOWER1;
                deps.m_upper_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
            }
            return;
        }
        if (numeric_traits<T>::is_neg(m_upper) || numeric_traits<T>::is_zero(m_upper)) {
            // [a, b] where a <= b < 0
            if (compute_intv) {
                std::swap(m_lower, m_upper);
                numeric_traits<T>::set_rounding(false);
                numeric_traits<T>::cosh(m_lower);
                numeric_traits<T>::set_rounding(true);
                numeric_traits<T>::cosh(m_upper);
                lean_assert(check_invariant());
            }
            if (compute_deps) {
                deps.m_lower_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
                deps.m_upper_deps = DEP_IN_LOWER1;
            }
            return;
        }
        // [a, b] where a < 0 < b
        if (m_lower + m_upper < 0.0) {
            if (compute_intv) {
                m_upper = m_lower;
            }
        } else {
            // Nothing
        }
        if (compute_intv) {
            m_lower = 1.0;
            m_lower_open = false;
            numeric_traits<T>::set_rounding(true);
            numeric_traits<T>::cosh(m_upper);
            lean_assert(check_invariant());
        }
        if (compute_deps) {
            deps.m_upper_deps = 0;
            deps.m_upper_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
        }
        return;
    }
    if (lower_kind() == XN_NUMERAL) {
        // [c, +oo]
        lean_assert(upper_kind() == XN_PLUS_INFINITY);
        if (numeric_traits<T>::is_pos(m_lower)) {
            // [c, +oo] where 0 < c < +oo
            if (compute_intv) {
                numeric_traits<T>::set_rounding(false);
                numeric_traits<T>::cosh(m_lower);
                lean_assert(check_invariant());
            }
            if (compute_deps) {
                deps.m_lower_deps = DEP_IN_LOWER1;
                deps.m_upper_deps = 0;
            }
            return;
        } else {
            // [c, +oo] where c <= 0 < +oo
            if (compute_intv) {
                m_lower = 1.0;
                m_lower_open = false;
                lean_assert(check_invariant());
            }
            if (compute_deps) {
                deps.m_lower_deps = deps.m_upper_deps = 0;
            }
            return;
        }
    }
    if (upper_kind() == XN_NUMERAL) {
        // [-oo, c]
        lean_assert(lower_kind() == XN_MINUS_INFINITY);
        if (compute_intv) {
            m_upper_inf = true;
            m_upper_open = true;
        }
        if (numeric_traits<T>::is_pos(m_upper)) {
            // [-oo, c] where -oo < 0 < c
            if (compute_intv) {
                m_lower = 1.0;
                m_lower_open = false;
                lean_assert(check_invariant());
            }
            if (compute_deps) {
                deps.m_lower_deps = deps.m_upper_deps = 0;
            }
            return;
        } else {
            // [-oo, c] where -oo < c <= 0
            if (compute_intv) {
                m_lower = m_upper;
                numeric_traits<T>::set_rounding(false);
                numeric_traits<T>::cosh(m_lower);
                lean_assert(check_invariant());
            }
            if (compute_deps) {
                deps.m_lower_deps = DEP_IN_UPPER1;
                deps.m_upper_deps = 0;
            }
            return;
        }
    }
    lean_assert(lower_kind() == XN_MINUS_INFINITY && upper_kind() == XN_PLUS_INFINITY);
    // cosh((-oo, +oo)) = [1.0, +oo)
    if (compute_intv) {
        m_upper_open = true;
        m_upper_inf = true;
        m_lower = 1.0;
        m_lower_open = false;
        m_lower_inf = false;
        lean_assert(check_invariant());
    }
    if (compute_deps) {
        deps.m_lower_deps = 0;
        deps.m_upper_deps = 0;
    }
    return;
}

template<typename T>
template<bool compute_intv, bool compute_deps>
void interval<T>::tanh (interval_deps & deps) {
    if (compute_deps) {
        deps.m_lower_deps = deps.m_upper_deps = 0;
    }

    if (lower_kind() == XN_NUMERAL) {
        if (compute_intv) {
            numeric_traits<T>::set_rounding(true);
            m_lower = -m_lower;
            numeric_traits<T>::tanh(m_lower);
            m_lower = -m_lower;
        }
        if (compute_deps) {
            deps.m_lower_deps = DEP_IN_LOWER1;
        }
    }
    if (upper_kind() == XN_NUMERAL) {
        if (compute_intv) {
            numeric_traits<T>::set_rounding(true);
            numeric_traits<T>::tanh(m_upper);
        }
        if (compute_deps) {
            deps.m_upper_deps = DEP_IN_UPPER1;
        }
    }
    if (compute_intv) {
        lean_assert(check_invariant());
    }
    return;
}

template<typename T>
template<bool compute_intv, bool compute_deps>
void interval<T>::asinh(interval_deps & deps) {
    if (compute_deps) {
        deps.m_lower_deps = deps.m_upper_deps = 0;
    }
    if (lower_kind() == XN_NUMERAL) {
        if (compute_intv) {
            numeric_traits<T>::set_rounding(true);
            m_lower = -m_lower;
            numeric_traits<T>::asinh(m_lower);
            m_lower = -m_lower;
        }
        if (compute_deps) {
            deps.m_lower_deps = DEP_IN_LOWER1;
        }
    }
    if (upper_kind() == XN_NUMERAL) {
        if (compute_intv) {
            numeric_traits<T>::set_rounding(true);
            numeric_traits<T>::asinh(m_upper);
        }
        if (compute_deps) {
            deps.m_upper_deps = DEP_IN_UPPER1;
        }
    }
    if (compute_intv) {
        lean_assert(check_invariant());
    }
    return;
}

template<typename T>
template<bool compute_intv, bool compute_deps>
void interval<T>::acosh(interval_deps & deps) {
    lean_assert(lower_kind() == XN_NUMERAL && m_lower >= 1.0);
    if (compute_intv) {
        numeric_traits<T>::set_rounding(false);
        numeric_traits<T>::acosh(m_lower);
    }
    if (compute_deps) {
        deps.m_lower_deps = DEP_IN_LOWER1;
    }
    if (upper_kind() == XN_NUMERAL) {
        if (compute_intv) {
            numeric_traits<T>::set_rounding(true);
            numeric_traits<T>::acosh(m_upper);
        }
        if (compute_deps) {
            deps.m_upper_deps = DEP_IN_UPPER1;
        }
    } else {
        // upper_kind() == +oo
        if (compute_deps) {
            deps.m_upper_deps = 0;
        }
    }
    if (compute_intv) {
        lean_assert(check_invariant());
    }
    return;
}

template<typename T>
template<bool compute_intv, bool compute_deps>
void interval<T>::atanh(interval_deps & deps) {
    lean_assert(lower_kind() == XN_NUMERAL && m_lower >= -1.0);
    lean_assert(upper_kind() == XN_NUMERAL && m_upper <= 1.0);

    if (compute_intv) {
        numeric_traits<T>::set_rounding(true);
        m_lower = -m_lower;
        numeric_traits<T>::atanh(m_lower);
        m_lower = -m_lower;
        numeric_traits<T>::set_rounding(true);
        numeric_traits<T>::atanh(m_upper);
        lean_assert(check_invariant());
    }
    if (compute_deps) {
        deps.m_lower_deps = DEP_IN_LOWER1;
        deps.m_upper_deps = DEP_IN_UPPER1;
    }
    return;
}

template<typename T> void interval<T>::exp_jst(interval_deps & deps) {
    exp<false, true>(deps);
    return;
}
template<typename T> void interval<T>::exp2_jst(interval_deps & deps) {
    exp2<false, true>(deps);
    return;
}
template<typename T> void interval<T>::exp10_jst(interval_deps & deps) {
    exp10<false, true>(deps);
    return;
}
template<typename T> void interval<T>::log_jst(interval_deps & deps) {
    log<false, true>(deps);
    return;
}
template<typename T> void interval<T>::log2_jst(interval_deps & deps) {
    log2<false, true>(deps);
    return;
}
template<typename T> void interval<T>::log10_jst(interval_deps & deps) {
    log10<false, true>(deps);
    return;
}
template<typename T> void interval<T>::sin_jst(interval_deps & deps) {
    sin<false, true>(deps);
    return;
}
template<typename T> void interval<T>::cos_jst(interval_deps & deps) {
    cos<false, true>(deps);
    return;
}
template<typename T> void interval<T>::tan_jst(interval_deps & deps) {
    tan<false, true>(deps);
    return;
}
template<typename T> void interval<T>::csc_jst(interval_deps & deps) {
    csc<false, true>(deps);
    return;
}
template<typename T> void interval<T>::sec_jst(interval_deps & deps) {
    sec<false, true>(deps);
    return;
}
template<typename T> void interval<T>::cot_jst(interval_deps & deps) {
    cot<false, true>(deps);
    return;
}
template<typename T> void interval<T>::asin_jst(interval_deps & deps) {
    asin<false, true>(deps);
    return;
}
template<typename T> void interval<T>::acos_jst(interval_deps & deps) {
    acos<false, true>(deps);
    return;
}
template<typename T> void interval<T>::atan_jst(interval_deps & deps) {
    atan<false, true>(deps);
    return;
}
template<typename T> void interval<T>::sinh_jst(interval_deps & deps) {
    sinh<false, true>(deps);
    return;
}
template<typename T> void interval<T>::cosh_jst(interval_deps & deps) {
    cosh<false, true>(deps);
    return;
}
template<typename T> void interval<T>::tanh_jst(interval_deps & deps) {
    tanh<false, true>(deps);
    return;
}
template<typename T> void interval<T>::asinh_jst(interval_deps & deps) {
    asinh<false, true>(deps);
    return;
}
template<typename T> void interval<T>::acosh_jst(interval_deps & deps) {
    acosh<false, true>(deps);
    return;
}
template<typename T> void interval<T>::atanh_jst(interval_deps & deps) {
    atanh<false, true>(deps);
    return;
}
}
