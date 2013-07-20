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
    static void neg(T & v) { numeric_traits<T>::neg(v); }
    static bool is_zero(T const & v) { return numeric_traits<T>::is_zero(v); }
    static void power(T & v, unsigned k) { return numeric_traits<T>::power(v, k); }
    void _swap(interval & b);
    bool _eq(interval const & b) const;

public:
    template<typename T2> interval & operator=(T2 const & n) { m_lower = n; m_upper = n; set_closed_endpoints(); return *this; }
    interval & operator=(T const & n);
    interval & operator=(interval const & n);
    interval & operator=(interval && n);

    // (-oo, oo)
    interval();
    // [n,n]
    template<typename T2> interval(T2 const & n):m_lower(n), m_upper(n) { set_closed_endpoints();}
    // copy constructor
    interval(interval const & n);
    // move constructor
    interval(interval && src);
    // [l,u], (l,u], [l,u), (l,u)
    template<typename T2> interval(T2 const & l, T2 const & u, bool l_open = false, bool u_open = false):m_lower(l), m_upper(u) {
        m_lower_open = l_open; m_upper_open = u_open; m_lower_inf  = false; m_upper_inf  = false;
    }
    // [l,u], (l,u], [l,u), (l,u)
    template<typename T2> interval(bool l_open, T2 const & l, T2 const & u, bool u_open):interval(l, u, l_open, u_open) {}
    // (-oo, u], (-oo, u]
    template<typename T2> interval(T2 const & u, bool u_open):m_upper(u) {
        m_lower_open = true; m_upper_open = u_open; m_lower_inf  = true; m_upper_inf  = false;
    }
    // [u, +oo), (u, +oo)
    template<typename T2> interval(bool l_open, T2 const & l):m_lower(l) {
        m_lower_open = l_open; m_upper_open = true; m_lower_inf  = false; m_upper_inf  = true;
    }

    ~interval();

    friend void swap(interval<T> & a, interval<T> & b) { a._swap(b); }

    T const & lower() const { return m_lower; }
    T const & upper() const { return m_upper; }

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

    // all values in the interval are non-negative
    bool is_P() const { return is_lower_pos() || is_lower_zero(); }
    // interval of the form [0, ...
    bool is_P0() const { return is_lower_zero() && !is_lower_open(); }
    // all values in the interval are positive
    bool is_P1() const { return is_lower_pos() || (is_lower_zero() && is_lower_open()); }
    // all values in the interval are non-positive
    bool is_N() const { return is_upper_neg() || is_upper_zero(); }
    // interval of the form ..., 0]
    bool is_N0() const { return is_upper_zero() && !is_upper_open(); }
    // all values in the interval are negative
    bool is_N1() const { return is_upper_neg() || (is_upper_zero() && is_upper_open()); }
    // lower is negative and upper is positive
    bool is_M() const { return is_lower_neg() && is_upper_pos(); }
    // [0,0]
    bool is_zero() const { return is_lower_zero() && is_upper_zero(); }

    // Interval contains the value zero
    bool contains_zero() const;
    /**
       \brief Return true iff this contains b.
       That is, every value in b is a value of this.
    */
    bool contains(interval<T> & b) const;

    /**
       \brief Return true is the interval contains only one value.
    */
    bool is_singleton() const;
    /**
       \brief Return true is the interval contains only v.
    */
    template<typename T2> bool is_singleton(T2 const & v) const { return is_singleton() && m_lower == v; }


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

    void neg();
    friend interval<T> neg(interval<T> o) { o.neg(); return o; }

    interval & operator+=(interval const & o);
    interval & operator-=(interval const & o);
    interval & operator*=(interval const & o);
    interval & operator/=(interval const & o);

    void inv();
    friend interval<T> inv(interval<T> o) { o.inv(); return o; }

    void power(unsigned n);
    friend interval<T> power(interval<T> o, unsigned k) { o.power(k); return o; }

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
