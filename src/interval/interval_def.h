/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include "interval.h"

namespace lean {

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
    m_lower(0),
    m_upper(0) {
    set_closed_endpoints();
}

template<typename T>
interval<T>::interval(interval const & n):
    m_lower(n.m_lower),
    m_upper(n.m_upper),
    m_lower_open(n.m_lower_open),
    m_upper_open(n.m_upper_open),
    m_lower_inf(n.m_lower_inf),
    m_upper_inf(n.m_upper_inf) {
}

template<typename T>
interval<T>::interval(interval && n):
    m_lower(std::move(n.m_lower)),
    m_upper(std::move(n.m_upper)),
    m_lower_open(n.m_lower_open),
    m_upper_open(n.m_upper_open),
    m_lower_inf(n.m_lower_inf),
    m_upper_inf(n.m_upper_inf) {
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
bool interval<T>::_eq(interval<T> const & b) const {
    return
        m_lower_open == b.m_lower_open &&
        m_upper_open == b.m_upper_open &&
        eq(m_lower, lower_kind(), b.m_lower, b.lower_kind()) &&
        eq(m_upper, upper_kind(), b.m_upper, b.upper_kind());
}

template<typename T>
bool interval<T>::before(interval<T> const & b) const {
    // TODO
    //if (is_upper_inf() || b.lower_is_inf())
    //    return false;
    // return m_upper < b.m_lower || (is_upper_open() &&
    return true;
}

template<typename T>
interval<T> & interval<T>::operator+=(interval<T> const & o) {
    xnumeral_kind new_l_kind, new_u_kind;
    round_to_minus_inf();
    add(m_lower, new_l_kind, m_lower, lower_kind(), o.m_lower, o.lower_kind());
    round_to_plus_inf();
    add(m_upper, new_u_kind, m_upper, upper_kind(), o.m_upper, o.upper_kind());
    m_lower_inf = new_l_kind == XN_MINUS_INFINITY;
    m_upper_inf = new_u_kind == XN_PLUS_INFINITY;
    m_lower_open = m_lower_open || o.m_lower_open;
    m_upper_open = m_upper_open || o.m_upper_open;
    lean_assert(check_invariant());
    return *this;
}

template<typename T>
interval<T> & interval<T>::operator-=(interval<T> const & o) {
    xnumeral_kind new_l_kind, new_u_kind;
    round_to_minus_inf();
    sub(m_lower, new_l_kind, m_lower, lower_kind(), o.m_upper, o.upper_kind());
    round_to_plus_inf();
    add(m_upper, new_u_kind, m_upper, upper_kind(), o.m_lower, o.lower_kind());
    m_lower_inf = new_l_kind == XN_MINUS_INFINITY;
    m_upper_inf = new_u_kind == XN_PLUS_INFINITY;
    m_lower_open = m_lower_open || o.m_upper_open;
    m_upper_open = m_upper_open || o.m_lower_open;
    lean_assert(check_invariant());
    return *this;
}

template<typename T>
interval<T> & interval<T>::operator*=(interval<T> const & o) {
    using std::swap;
    interval<T> const & i1 = *this;
    interval<T> const & i2 = o;
#if LEAN_DEBUG || LEAN_TRACE
    bool i1_contains_zero = i1.contains_zero();
    bool i2_contains_zero = i2.contains_zero();
#endif
    if (i1.is_zero()) {
        return *this;
    }
    if (i2.is_zero()) {
        *this = i2;
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

    static thread_local T new_l_val;
    static thread_local T new_u_val;
    xnumeral_kind new_l_kind, new_u_kind;

    if (i1.is_N()) {
        if (i2.is_N()) {
            // x <= b <= 0, y <= d <= 0 --> b*d <= x*y
            // a <= x <= b <= 0, c <= y <= d <= 0 --> x*y <= a*c  (we can use the fact that x or y is always negative (i.e., b is neg or d is neg))
            set_is_lower_open((i1.is_N0() || i2.is_N0()) ? false : (b_o || d_o));
            set_is_upper_open(a_o || c_o);
            // if b = 0 (and the interval is closed), then the lower bound is closed

            round_to_minus_inf();
            mul(new_l_val, new_l_kind, b, b_k, d, d_k);
            round_to_plus_inf();
            mul(new_u_val, new_u_kind, a, a_k, c, c_k);
        }
        else if (i2.is_M()) {
            // a <= x <= b <= 0,  y <= d, d > 0 --> a*d <= x*y (uses the fact that b is not positive)
            // a <= x <= b <= 0,  c <= y, c < 0 --> x*y <= a*c (uses the fact that b is not positive)
            set_is_lower_open(a_o || d_o);
            set_is_upper_open(a_o || c_o);

            round_to_minus_inf();
            mul(new_l_val, new_l_kind, a, a_k, d, d_k);
            round_to_plus_inf();
            mul(new_u_val, new_u_kind, a, a_k, c, c_k);
        }
        else {
            // a <= x <= b <= 0, 0 <= c <= y <= d --> a*d <= x*y (uses the fact that x is neg (b is not positive) or y is pos (c is not negative))
            // x <= b <= 0,  0 <= c <= y --> x*y <= b*c
            lean_assert(i2.is_P());

            // must update upper_is_open first, since value of is_N0(i1) and is_P0(i2) may be affected by update
            set_is_upper_open((i1.is_N0() || i2.is_P0()) ? false : (b_o || c_o));
            set_is_lower_open(a_o || d_o);

            round_to_minus_inf();
            mul(new_l_val, new_l_kind, a, a_k, d, d_k);
            round_to_plus_inf();
            mul(new_u_val, new_u_kind, b, b_k, c, c_k);
        }
    }
    else if (i1.is_M()) {
        if (i2.is_N()) {
            // b > 0, x <= b,  c <= y <= d <= 0 --> b*c <= x*y (uses the fact that d is not positive)
            // a < 0, a <= x,  c <= y <= d <= 0 --> x*y <= a*c (uses the fact that d is not positive)
            set_is_lower_open(b_o || c_o);
            set_is_upper_open(a_o || c_o);

            round_to_minus_inf();
            mul(new_l_val, new_l_kind, b, b_k, c, c_k);
            round_to_plus_inf();
            mul(new_u_val, new_u_kind, a, a_k, c, c_k);
        }
        else if (i2.is_M()) {
            static thread_local T ad; xnumeral_kind ad_k;
            static thread_local T bc; xnumeral_kind bc_k;
            static thread_local T ac; xnumeral_kind ac_k;
            static thread_local T bd; xnumeral_kind bd_k;

            bool  ad_o = a_o || d_o;
            bool  bc_o = b_o || c_o;
            bool  ac_o = a_o || c_o;
            bool  bd_o = b_o || d_o;

            round_to_minus_inf();
            mul(ad, ad_k, a, a_k, d, d_k);
            mul(bc, bc_k, b, b_k, c, c_k);
            round_to_plus_inf();
            mul(ac, ac_k, a, a_k, c, c_k);
            mul(bd, bd_k, b, b_k, d, d_k);

            if (lt(ad, ad_k, bc, bc_k) || (eq(ad, ad_k, bc, bc_k) && !ad_o && bc_o)) {
                swap(new_l_val, ad);
                new_l_kind = ad_k;
                set_is_lower_open(ad_o);
            }
            else {
                swap(new_l_val, bc);
                new_l_kind = bc_k;
                set_is_lower_open(bc_o);
            }


            if (gt(ac, ac_k, bd, bd_k) || (eq(ac, ac_k, bd, bd_k) && !ac_o && bd_o)) {
                swap(new_u_val, ac);
                new_u_kind = ac_k;
                set_is_upper_open(ac_o);
            }
            else {
                swap(new_u_val, bd);
                new_u_kind = bd_k;
                set_is_upper_open(bd_o);
            }
        }
        else {
            // a < 0, a <= x, 0 <= c <= y <= d --> a*d <= x*y (uses the fact that c is not negative)
            // b > 0, x <= b, 0 <= c <= y <= d --> x*y <= b*d (uses the fact that c is not negative)
            lean_assert(i2.is_P());

            set_is_lower_open(a_o || d_o);
            set_is_upper_open(b_o || d_o);

            round_to_minus_inf();
            mul(new_l_val, new_l_kind, a, a_k, d, d_k);
            round_to_plus_inf();
            mul(new_u_val, new_u_kind, b, b_k, d, d_k);
        }
    }
    else {
        lean_assert(i1.is_P());
        if (i2.is_N()) {
            // 0 <= a <= x <= b,   c <= y <= d <= 0  -->  x*y <= b*c (uses the fact that x is pos (a is not neg) or y is neg (d is not pos))
            // 0 <= a <= x,  y <= d <= 0  --> a*d <= x*y

            // must update upper_is_open first, since value of is_P0(i1) and is_N0(i2) may be affected by update
            set_is_upper_open((i1.is_P0() || i2.is_N0()) ? false : a_o || d_o);
            set_is_lower_open(b_o || c_o);

            round_to_minus_inf();
            mul(new_l_val, new_l_kind, b, b_k, c, c_k);
            round_to_plus_inf();
            mul(new_u_val, new_u_kind, a, a_k, d, d_k);
        }
        else if (i2.is_M()) {
            // 0 <= a <= x <= b,  c <= y --> b*c <= x*y (uses the fact that a is not negative)
            // 0 <= a <= x <= b,  y <= d --> x*y <= b*d (uses the fact that a is not negative)
            set_is_lower_open(b_o || c_o);
            set_is_upper_open(b_o || d_o);

            round_to_minus_inf();
            mul(new_l_val, new_l_kind, b, b_k, c, c_k);
            round_to_plus_inf();
            mul(new_u_val, new_u_kind, b, b_k, d, d_k);
        }
        else {
            lean_assert(i2.is_P());
            // 0 <= a <= x, 0 <= c <= y --> a*c <= x*y
            // x <= b, y <= d --> x*y <= b*d (uses the fact that x is pos (a is not negative) or y is pos (c is not negative))

            set_is_lower_open((i1.is_P0() || i2.is_P0()) ? false : a_o || c_o);
            set_is_upper_open(b_o || d_o);

            round_to_minus_inf();
            mul(new_l_val, new_l_kind, a, a_k, c, c_k);
            round_to_plus_inf();
            mul(new_u_val, new_u_kind, b, b_k, d, d_k);
        }
    }

    swap(m_lower, new_l_val);
    swap(m_upper, new_u_val);
    set_is_lower_inf(new_l_kind == XN_MINUS_INFINITY);
    set_is_upper_inf(new_u_kind == XN_PLUS_INFINITY);
    lean_assert(!(i1_contains_zero || i2_contains_zero) || contains_zero());
    return *this;
}

template<typename T>
interval<T> & interval<T>::operator/=(interval<T> const & o) {
    // TODO
    return *this;
}

template<typename T>
void interval<T>::inv() {
    // If the interval [l,u] does not contain 0, then 1/[l,u] = [1/u, 1/l]
    lean_assert(!contains_zero());

    using std::swap;

    static thread_local T new_l_val;
    static thread_local T new_u_val;
    xnumeral_kind new_l_kind, new_u_kind;

    if (is_P1()) {
        // 0 < l <= x --> 1/x <= 1/l
        // 0 < l <= x <= u --> 1/u <= 1/x (use lower and upper bounds)

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
        }
        else {
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
    else if (is_N1()) {
        // x <= u < 0 --> 1/u <= 1/x
        // l <= x <= u < 0 --> 1/l <= 1/x (use lower and upper bounds)
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
        }
        else {
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
    else {
        lean_unreachable();
    }
}

template<typename T>
bool interval<T>::check_invariant() const {
    lean_assert(!m_lower_inf || m_lower_open);
    lean_assert(!m_upper_inf || m_upper_open);
    if (eq(m_lower, lower_kind(), m_upper, upper_kind())) {
        lean_assert(!is_lower_open());
        lean_assert(!is_upper_open());
    }
    else {
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


}
