/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include "interval.h"
#include "trace.h"

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
bool interval<T>::contains(interval<T> & b) const {
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
    return m_lower == m_upper && m_lower_open && m_upper_open && !m_lower_inf && !m_upper_inf;
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
void interval<T>::neg() {
    using std::swap;
    if (is_lower_inf()) {
        if (is_upper_inf()) {
            // (-oo, oo) case
            // do nothing
        } else {
            // (-oo, a| --> |-a, oo)
            swap(m_lower, m_upper);
            neg(m_lower);
            m_lower_inf  = false;
            m_lower_open = m_upper_open;

            reset(m_upper);
            m_upper_inf  = true;
            m_upper_open = true;
        }
    } else {
        if (is_upper_inf()) {
            // |a, oo) --> (-oo, -a|
            swap(m_upper, m_lower);
            neg(m_upper);
            m_upper_inf  = false;
            m_upper_open = m_lower_open;

            reset(m_lower);
            m_lower_inf  = true;
            m_lower_open = true;
        } else {
            // |a, b| --> |-b, -a|
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
    }
    lean_assert(check_invariant());
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
    using std::swap;
    static thread_local T new_l_val;
    static thread_local T new_u_val;
    xnumeral_kind new_l_kind, new_u_kind;
    lean_trace("numerics", tout << "this: " << *this << " o: " << o << "\n";);
    round_to_minus_inf();
    sub(new_l_val, new_l_kind, m_lower, lower_kind(), o.m_upper, o.upper_kind());
    round_to_plus_inf();
    sub(new_u_val, new_u_kind, m_upper, upper_kind(), o.m_lower, o.lower_kind());
    lean_trace("numerics", tout << "new: " << new_l_val << " " << new_u_val << "\n";);
    swap(new_l_val, m_lower);
    swap(new_u_val, m_upper);
    m_lower_inf = new_l_kind == XN_MINUS_INFINITY;
    m_upper_inf = new_u_kind == XN_PLUS_INFINITY;
    bool o_l = o.m_lower_open;
    m_lower_open = m_lower_open || o.m_upper_open;
    m_upper_open = m_upper_open || o_l;
    lean_assert(check_invariant());
    return *this;
}

template<typename T>
interval<T> & interval<T>::operator*=(interval<T> const & o) {
    using std::swap;
    interval<T> const & i1 = *this;
    interval<T> const & i2 = o;
#if defined(LEAN_DEBUG) || defined(LEAN_TRACE)
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
        } else if (i2.is_M()) {
            // a <= x <= b <= 0,  y <= d, d > 0 --> a*d <= x*y (uses the fact that b is not positive)
            // a <= x <= b <= 0,  c <= y, c < 0 --> x*y <= a*c (uses the fact that b is not positive)
            set_is_lower_open(a_o || d_o);
            set_is_upper_open(a_o || c_o);

            round_to_minus_inf();
            mul(new_l_val, new_l_kind, a, a_k, d, d_k);
            round_to_plus_inf();
            mul(new_u_val, new_u_kind, a, a_k, c, c_k);
        } else {
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
    } else if (i1.is_M()) {
        if (i2.is_N()) {
            // b > 0, x <= b,  c <= y <= d <= 0 --> b*c <= x*y (uses the fact that d is not positive)
            // a < 0, a <= x,  c <= y <= d <= 0 --> x*y <= a*c (uses the fact that d is not positive)
            set_is_lower_open(b_o || c_o);
            set_is_upper_open(a_o || c_o);

            round_to_minus_inf();
            mul(new_l_val, new_l_kind, b, b_k, c, c_k);
            round_to_plus_inf();
            mul(new_u_val, new_u_kind, a, a_k, c, c_k);
        } else if (i2.is_M()) {
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
            } else {
                swap(new_l_val, bc);
                new_l_kind = bc_k;
                set_is_lower_open(bc_o);
            }


            if (gt(ac, ac_k, bd, bd_k) || (eq(ac, ac_k, bd, bd_k) && !ac_o && bd_o)) {
                swap(new_u_val, ac);
                new_u_kind = ac_k;
                set_is_upper_open(ac_o);
            } else {
                swap(new_u_val, bd);
                new_u_kind = bd_k;
                set_is_upper_open(bd_o);
            }
        } else {
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
    } else {
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
        } else if (i2.is_M()) {
            // 0 <= a <= x <= b,  c <= y --> b*c <= x*y (uses the fact that a is not negative)
            // 0 <= a <= x <= b,  y <= d --> x*y <= b*d (uses the fact that a is not negative)
            set_is_lower_open(b_o || c_o);
            set_is_upper_open(b_o || d_o);

            round_to_minus_inf();
            mul(new_l_val, new_l_kind, b, b_k, c, c_k);
            round_to_plus_inf();
            mul(new_u_val, new_u_kind, b, b_k, d, d_k);
        } else {
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
    lean_assert(check_invariant());
    return *this;
}

template<typename T>
interval<T> & interval<T>::operator/=(interval<T> const & o) {
    using std::swap;
    interval<T> const & i1 = *this;
    interval<T> const & i2 = o;
    lean_assert(!i2.contains_zero());

    if (i1.is_zero()) {
        // 0/other = 0 if other != 0
        // do nothing
    } else {
        T const & a = i1.m_lower; xnumeral_kind a_k = i1.lower_kind();
        T const & b = i1.m_upper; xnumeral_kind b_k = i1.upper_kind();
        T const & c = i2.m_lower; xnumeral_kind c_k = i2.lower_kind();
        T const & d = i2.m_upper; xnumeral_kind d_k = i2.upper_kind();

        bool a_o = i1.m_lower_open;
        bool b_o = i1.m_upper_open;
        bool c_o = i2.m_lower_open;
        bool d_o = i2.m_upper_open;

        static thread_local T new_l_val;
        static thread_local T new_u_val;
        xnumeral_kind new_l_kind, new_u_kind;

        if (i1.is_N()) {
            if (i2.is_N1()) {
                // x <= b <= 0,      c <= y <= d < 0 --> b/c <= x/y
                // a <= x <= b <= 0,      y <= d < 0 -->        x/y <= a/d
                set_is_lower_open(i1.is_N0() ? false : b_o || c_o);
                set_is_upper_open(a_o || d_o);

                round_to_minus_inf();
                div(new_l_val, new_l_kind, b, b_k, c, c_k);
                if (is_zero(d)) {
                    lean_assert(d_o);
                    reset(new_u_val);
                    new_u_kind = XN_PLUS_INFINITY;
                } else {
                    round_to_plus_inf();
                    div(new_u_val, new_u_kind, a, a_k, d, d_k);
                }
            } else {
                // a <= x, a < 0,   0 < c <= y       -->  a/c <= x/y
                // x <= b <= 0,     0 < c <= y <= d  -->         x/y <= b/d
                lean_assert(i2.is_P1());

                set_is_upper_open(i1.is_N0() ? false : (b_o || d_o));
                set_is_lower_open(a_o || c_o);

                if (is_zero(c)) {
                    lean_assert(c_o);
                    reset(new_l_val);
                    new_l_kind = XN_MINUS_INFINITY;
                } else {
                    round_to_minus_inf();
                    div(new_l_val, new_l_kind, a, a_k, c, c_k);
                }
                round_to_plus_inf();
                div(new_u_val, new_u_kind, b, b_k, d, d_k);
            }
        } else if (i1.is_M()) {
            if (i2.is_N1()) {
                // 0 < a <= x <= b < 0,  y <= d < 0   --> b/d <= x/y
                // 0 < a <= x <= b < 0,  y <= d < 0   -->        x/y <= a/d
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
                    div(new_l_val, new_l_kind, b, b_k, d, d_k);
                    round_to_plus_inf();
                    div(new_u_val, new_u_kind, a, a_k, d, d_k);
                }
            } else {
                // 0 < a <= x <= b < 0, 0 < c <= y  --> a/c <= x/y
                // 0 < a <= x <= b < 0, 0 < c <= y  -->        x/y <= b/c
                lean_assert(i1.is_P1());

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
                    div(new_l_val, new_l_kind, a, a_k, c, c_k);
                    round_to_plus_inf();
                    div(new_u_val, new_u_kind, b, b_k, c, c_k);
                }
            }
        } else {
            lean_assert(i1.is_P());
            if (i2.is_N1()) {
                // b > 0,    x <= b,   c <= y <= d < 0    -->  b/d <= x/y
                // 0 <= a <= x,        c <= y <= d < 0    -->         x/y  <= a/c
                set_is_upper_open(i1.is_P0() ? false : a_o || c_o);
                set_is_lower_open(b_o || d_o);

                if (is_zero(d)) {
                    lean_assert(d_o);
                    reset(new_l_val);
                    new_l_kind = XN_MINUS_INFINITY;
                } else {
                    round_to_minus_inf();
                    div(new_l_val, new_l_kind, b, b_k, d, d_k);
                }
                round_to_plus_inf();
                div(new_u_val, new_u_kind, a, a_k, c, c_k);
            } else {
                lean_assert(i2.is_P1());
                // 0 <= a <= x,      0 < c <= y <= d    -->   a/d <= x/y
                // b > 0     x <= b, 0 < c <= y         -->          x/y <= b/c
                set_is_lower_open(i1.is_P0() ? false : a_o || d_o);
                set_is_upper_open(b_o || c_o);

                round_to_minus_inf();
                div(new_l_val, new_l_kind, a, a_k, d, d_k);
                if (is_zero(c)) {
                    lean_assert(c_o);
                    reset(new_u_val);
                    new_u_kind = XN_PLUS_INFINITY;
                } else {
                    round_to_plus_inf();
                    div(new_u_val, new_u_kind, b, b_k, c, c_k);
                }
            }
        }
        swap(m_lower, new_l_val);
        swap(m_upper, new_u_val);
        m_lower_inf = (new_l_kind == XN_MINUS_INFINITY);
        m_upper_inf = (new_u_kind == XN_PLUS_INFINITY);
    }
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
    } else if (is_N1()) {
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
    } else {
        lean_unreachable();
    }
    lean_assert(check_invariant());
}

template<typename T>
void interval<T>::power(unsigned n) {
    using std::swap;
    lean_assert(n > 0);
    if (n == 1) {
        // a^1 = a
        // nothing to be done
        return;
    } else if (n % 2 == 0) {
        if (is_lower_pos()) {
            // [l, u]^n = [l^n, u^n] if l > 0
            // 0 < l <= x      --> l^n <= x^n (lower bound guarantees that is positive)
            // 0 < l <= x <= u --> x^n <= u^n (use lower and upper bound -- need the fact that x is positive)
            lean_assert(!is_lower_inf());
            round_to_minus_inf();
            power(m_lower, n);

            if (!m_upper_inf) {
                round_to_plus_inf();
                power(m_upper, n);
            }
        } else if (is_upper_neg()) {
            // [l, u]^n = [u^n, l^n] if u < 0
            // l <= x <= u < 0   -->  x^n <= l^n (use lower and upper bound -- need the fact that x is negative)
            // x <= u < 0        -->  u^n <= x^n
            lean_assert(!is_upper_inf());
            bool lo = m_lower_open;
            bool li = m_lower_inf;

            swap(m_lower, m_upper);
            round_to_minus_inf();
            power(m_lower, n);
            m_lower_open = m_upper_open;
            m_lower_inf  = false;

            if (li) {
                reset(m_upper);
            } else {
                round_to_plus_inf();
                power(m_upper, n);
            }
            m_upper_inf  = li;
            m_upper_open = lo;
        } else {
            // [l, u]^n = [0, max{l^n, u^n}] otherwise
            // we need both bounds to justify upper bound
            xnumeral_kind un1_kind = lower_kind();
            xnumeral_kind un2_kind = upper_kind();
            static thread_local T un1;
            static thread_local T un2;
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
    } else {
        // Remark: when n is odd x^n is monotonic.
        if (!m_lower_inf)
            power(m_lower, n);
        if (!m_upper_inf)
            power(m_upper, n);
    }
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
        static thread_local T tmp;
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

template<typename T> void interval<T>::exp  () {
    if(is_empty())
        return;
    if(m_lower_inf) {
        numeric_traits<T>::reset(m_lower);
    } else {
        numeric_traits<T>::set_rounding(false);
        numeric_traits<T>::exp(m_lower);
    }
    if(m_upper_inf) {
        // Nothing to do
    } else {
        numeric_traits<T>::set_rounding(true);
        numeric_traits<T>::exp(m_upper);
    }
    lean_assert(check_invariant());
    return;
}
template<typename T> void interval<T>::exp2 () {
    if(is_empty())
        return;
    if(m_lower_inf) {
        numeric_traits<T>::reset(m_lower);
    } else {
        numeric_traits<T>::set_rounding(false);
        numeric_traits<T>::exp2(m_lower);
    }
    if(m_upper_inf) {
        // Nothing to do
    } else {
        numeric_traits<T>::set_rounding(true);
        numeric_traits<T>::exp2(m_upper);
    }
    lean_assert(check_invariant());
    return;
}
template<typename T> void interval<T>::exp10() {
    if(is_empty())
        return;
    if(m_lower_inf) {
        numeric_traits<T>::reset(m_lower);
    } else {
        numeric_traits<T>::set_rounding(false);
        numeric_traits<T>::exp10(m_lower);
    }
    if(m_upper_inf) {
        // Nothing to do
    } else {
        numeric_traits<T>::set_rounding(true);
        numeric_traits<T>::exp10(m_upper);
    }
    lean_assert(check_invariant());
    return;
}
template<typename T> void interval<T>::log  () {
    if(is_empty())
        return;
    if(is_N0()) {
        set_empty();
        return;
    }
    if(is_lower_pos()) {
        numeric_traits<T>::set_rounding(false);
        numeric_traits<T>::log(m_lower);
    } else {
        numeric_traits<T>::reset(m_lower);
        m_lower_inf = true;
    }
    if(m_upper_inf) {
        // Nothing to do
    } else {
        numeric_traits<T>::set_rounding(true);
        numeric_traits<T>::log(m_upper);
    }
    lean_assert(check_invariant());
    return;
}
template<typename T> void interval<T>::log2 () {
    if(is_empty())
        return;
    if(is_N0()) {
        set_empty();
        return;
    }
    if(is_lower_pos()) {
        numeric_traits<T>::set_rounding(false);
        numeric_traits<T>::log2(m_lower);
    } else {
        numeric_traits<T>::reset(m_lower);
        m_lower_inf = true;
    }
    if(m_upper_inf) {
        // Nothing to do
    } else {
        numeric_traits<T>::set_rounding(true);
        numeric_traits<T>::log2(m_upper);
    }
    lean_assert(check_invariant());
    return;
}
template<typename T> void interval<T>::log10() {
    if(is_empty())
        return;
    if(is_N0()) {
        set_empty();
        return;
    }
    if(is_lower_pos()) {
        numeric_traits<T>::set_rounding(false);
        numeric_traits<T>::log10(m_lower);
    } else {
        numeric_traits<T>::reset(m_lower);
        m_lower_inf = true;
    }
    if(m_upper_inf) {
        // Nothing to do
    } else {
        numeric_traits<T>::set_rounding(true);
        numeric_traits<T>::log10(m_upper);
    }
    lean_assert(check_invariant());
    return;
}
template<typename T> void interval<T>::sin  () {
    *this -= numeric_traits<T>::pi_half_lower();
    cos();
}
template<typename T> void interval<T>::cos  () { /* TODO */ lean_unreachable(); return; }
template<typename T> void interval<T>::tan  () { /* TODO */ lean_unreachable(); return; }
template<typename T> void interval<T>::sec  () { /* TODO */ lean_unreachable(); return; }
template<typename T> void interval<T>::csc  () { /* TODO */ lean_unreachable(); return; }
template<typename T> void interval<T>::cot  () { /* TODO */ lean_unreachable(); return; }
template<typename T> void interval<T>::asin () { /* TODO */ lean_unreachable(); return; }
template<typename T> void interval<T>::acos () { /* TODO */ lean_unreachable(); return; }
template<typename T> void interval<T>::atan () { /* TODO */ lean_unreachable(); return; }
template<typename T> void interval<T>::sinh () { /* TODO */ lean_unreachable(); return; }
template<typename T> void interval<T>::cosh () { /* TODO */ lean_unreachable(); return; }
template<typename T> void interval<T>::tanh () { /* TODO */ lean_unreachable(); return; }
template<typename T> void interval<T>::asinh() { /* TODO */ lean_unreachable(); return; }
template<typename T> void interval<T>::acosh() { /* TODO */ lean_unreachable(); return; }
template<typename T> void interval<T>::atanh() { /* TODO */ lean_unreachable(); return; }

}
