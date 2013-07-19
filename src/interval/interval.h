/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "numeric_traits.h"
#include "xnumeral.h"

namespace lean {

template<typename T>
class interval {
    T         m_lower;
    T         m_upper;
    unsigned  m_lower_open:1;
    unsigned  m_upper_open:1;
    unsigned  m_lower_inf:1;
    unsigned  m_upper_inf:1;

    xnumeral_kind lower_kind() const { return m_lower_inf ? XN_MINUS_INFINITY : XN_NUMERAL; }
    xnumeral_kind upper_kind() const { return m_upper_inf ? XN_PLUS_INFINITY  : XN_NUMERAL; }
    void set_closed_endpoints();

    static void round_to_plus_inf() { numeric_traits<T>::set_rounding(true); }
    static void round_to_minus_inf() { numeric_traits<T>::set_rounding(false); }
    static void reset(T & v) { numeric_traits<T>::reset(v); }
    static void inv(T & v) { numeric_traits<T>::inv(v); }
    void _swap(interval & b);
    bool _eq(interval const & b) const;

public:
    template<typename T2> interval & operator=(T2 const & n) { m_lower = n; m_upper = n; set_closed_endpoints(); return *this; }
    interval & operator=(T const & n);
    interval & operator=(interval const & n);
    interval & operator=(interval && n);

    interval();
    template<typename T2> interval(T2 const & n):m_lower(n), m_upper(n) { set_closed_endpoints();}
    interval(interval const & n);
    interval(interval && n);
    template<typename T2> interval(T2 const & l, T2 const & u, bool l_open = false, bool u_open = false):m_lower(l), m_upper(u) {
        m_lower_open = l_open; m_upper_open = u_open; m_lower_inf  = false; m_upper_inf  = false;
    }
    template<typename T2> interval(bool l_open, T2 const & l, T2 const & u, bool u_open):interval(l, u, l_open, u_open) {}

    ~interval();

    friend void swap(interval<T> & a, interval<T> & b) { a._swap(b); }

    bool is_lower_neg() const { return  ::lean::is_neg(m_lower,  lower_kind()); }
    bool is_lower_pos() const { return  ::lean::is_pos(m_lower,  lower_kind()); }
    bool is_lower_zero() const { return ::lean::is_zero(m_lower, lower_kind()); }

    bool is_upper_neg() const { return  ::lean::is_neg(m_upper,  upper_kind()); }
    bool is_upper_pos() const { return  ::lean::is_pos(m_upper,  upper_kind()); }
    bool is_upper_zero() const { return ::lean::is_zero(m_upper, upper_kind()); }

    bool is_lower_open() const { return m_lower_open; }
    bool is_upper_open() const { return m_upper_open; }
    bool is_lower_inf() const { return m_lower_inf; }
    bool is_upper_inf() const { return m_upper_inf; }

    bool is_P() const { return is_lower_pos() || is_lower_zero(); }
    bool is_P0() const { return is_lower_zero() && !is_lower_open(); }
    bool is_P1() const { return is_lower_pos() || (is_lower_zero() && is_lower_open()); }
    bool is_N() const { return is_upper_neg() || is_upper_zero(); }
    bool is_N0() const { return is_upper_zero() && !is_upper_open(); }
    bool is_N1() const { return is_upper_neg() || (is_upper_zero() && is_upper_open()); }
    bool is_M() const { return is_lower_neg() && is_upper_pos(); }
    bool is_zero() const { return is_lower_zero() && is_upper_zero(); }

    bool contains_zero() const;

    friend bool operator==(interval<T> const & a, interval<T> const & b) { return a._eq(b); }
    friend bool operator!=(interval<T> const & a, interval<T> const & b) { return !operator==(a, b); }

    /**
       \brief Return true if all values in this are less than all values in 'b'.
    */
    bool before(interval const & b) const;

    template<typename T2> void set_lower(T2 const & n) { m_lower = n; }
    template<typename T2> void set_upper(T2 const & n) { m_upper = n; }
    void set_is_lower_open(bool v) { m_lower_open = v; }
    void set_is_upper_open(bool v) { m_upper_open = v; }
    void set_is_lower_inf(bool v) { m_lower_inf = v; }
    void set_is_upper_inf(bool v) { m_upper_inf = v; }

    interval & operator+=(interval const & o);
    interval & operator-=(interval const & o);
    interval & operator*=(interval const & o);
    interval & operator/=(interval const & o);

    void inv();
    friend interval<T> inv(interval<T> o) { o.inv(); return o; }

    friend interval operator+(interval a, interval const & b) { return a += b; }
    friend interval operator-(interval a, interval const & b) { return a -= b; }
    friend interval operator*(interval a, interval const & b) { return a *= b; }
    friend interval operator/(interval a, interval const & b) { return a /= b; }

    bool check_invariant() const;

    void display(std::ostream & out) const;

    friend std::ostream & operator<<(std::ostream & out, interval const & n) {
        n.display(out);
        return out;
    }
};

}
