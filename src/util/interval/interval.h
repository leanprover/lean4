/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
        Soonho Kong
*/
#pragma once
#include "util/numerics/numeric_traits.h"
#include "util/numerics/xnumeral.h"

namespace lean {

#define DEP_IN_LOWER1 1
#define DEP_IN_UPPER1 2
#define DEP_IN_LOWER2 4
#define DEP_IN_UPPER2 8

typedef unsigned short bound_deps;
inline bool dep_in_lower1(bound_deps d) { return (d & DEP_IN_LOWER1) != 0; }
inline bool dep_in_lower2(bound_deps d) { return (d & DEP_IN_LOWER2) != 0; }
inline bool dep_in_upper1(bound_deps d) { return (d & DEP_IN_UPPER1) != 0; }
inline bool dep_in_upper2(bound_deps d) { return (d & DEP_IN_UPPER2) != 0; }
inline bound_deps dep1_to_dep2(bound_deps d) {
    lean_assert(!dep_in_lower2(d) && !dep_in_upper2(d));
    bound_deps r = d << 2;
    lean_assert(dep_in_lower1(d) == dep_in_lower2(r));
    lean_assert(dep_in_upper1(d) == dep_in_upper2(r));
    lean_assert(!dep_in_lower1(r) && !dep_in_upper1(r));
    return r;
}

/**
   \brief Interval dependencies for unary and binary operations on intervals.
   It contains the dependencies for the output lower and upper bounds
   for the resultant interval.
*/
struct interval_deps {
    bound_deps m_lower_deps;
    bound_deps m_upper_deps;
};


template<typename T>
class interval {
    T         m_lower;
    T         m_upper;
    unsigned  m_lower_open:1;
    unsigned  m_upper_open:1;
    unsigned  m_lower_inf:1;
    unsigned  m_upper_inf:1;
    static interval_deps dummy;

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
    // [n, n]
    template<typename T2> interval(T2 const & n):m_lower(n), m_upper(n) { set_closed_endpoints();}
    // copy constructor
    interval(interval const & n);
    // move constructor
    interval(interval && src);

    // [l, u], (l, u], [l, u), (l, u)
    template<typename T2> interval(T2 const & l, T2 const & u, bool l_open = false, bool u_open = false):m_lower(l), m_upper(u) {
        m_lower_open = l_open; m_upper_open = u_open; m_lower_inf  = false; m_upper_inf  = false;
    }
    // [l, u], (l, u], [l, u), (l, u)
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

    friend void swap(interval & a, interval & b) { a._swap(b); }

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
    // [0, 0]
    bool is_zero() const { return is_lower_zero() && is_upper_zero(); }

    // Interval contains the value zero
    bool contains_zero() const;
    /**
       \brief Return true iff this contains b.
       That is, every value in b is a value of this.
    */
    bool contains(interval const & b) const;

    bool is_empty() const;
    void set_empty();

    /**
       \brief Return true is the interval contains only one value.
    */
    bool is_singleton() const;
    /**
       \brief Return true is the interval contains only v.
    */
    template<typename T2> bool is_singleton(T2 const & v) const { return is_singleton() && m_lower == v; }


    friend bool operator==(interval const & a, interval const & b) { return a._eq(b); }
    friend bool operator!=(interval const & a, interval const & b) { return !operator==(a, b); }

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

    template<bool compute_intv = true, bool compute_deps = false> void neg(interval_deps & deps = dummy);
    void neg_jst(interval_deps & deps) { neg<false, true>(deps); }
    friend interval neg(interval o) { o.neg(); return o; }
    friend interval neg_jst(interval o, interval_deps & deps) { o.neg(deps); return o; }

    interval & operator+=(interval const & o);
    interval & operator-=(interval const & o);
    interval & operator*=(interval const & o);
    interval & operator/=(interval const & o);

    template<bool compute_intv = true, bool compute_deps = false>
    interval & add(interval const & o, interval_deps & deps = dummy);
    template<bool compute_intv = true, bool compute_deps = false>
    interval & sub(interval const & o, interval_deps & deps = dummy);
    template<bool compute_intv = true, bool compute_deps = false>
    interval & mul(interval const & o, interval_deps & deps = dummy);
    template<bool compute_intv = true, bool compute_deps = false>
    interval & div(interval const & o, interval_deps & deps = dummy);

    void add_jst (interval const & o, interval_deps & deps);
    void sub_jst (interval const & o, interval_deps & deps);
    void mul_jst (interval const & o, interval_deps & deps);
    void div_jst (interval const & o, interval_deps & deps);

    interval & operator+=(T const & o);
    interval & operator-=(T const & o);
    interval & operator*=(T const & o);
    interval & operator/=(T const & o);

    template<bool compute_intv = true, bool compute_deps = false> void inv(interval_deps & deps = dummy);
    void inv_jst (interval_deps & deps) { inv<false, true>(deps); }
    friend interval inv(interval o) { o.inv(); return o; }
    friend interval inv_jst(interval o, interval_deps & deps) { o.inv(deps); return o; }

    void fmod(interval y);
    void fmod(T y);
    friend interval fmod(interval o, interval y) { o.fmod(y); return o; }
    friend interval fmod(interval o, T y) { o.fmod(y); return o; }

    template<bool compute_intv = true, bool compute_deps = false>
    void power(unsigned n, interval_deps & deps = dummy);
    void power_jst(unsigned n, interval_deps & deps);
    friend interval power(interval o, unsigned k) { o.power(k); return o; }

    template<bool compute_intv = true, bool compute_deps = false> void exp(interval_deps & deps = dummy);
    template<bool compute_intv = true, bool compute_deps = false> void exp2(interval_deps & deps = dummy);
    template<bool compute_intv = true, bool compute_deps = false> void exp10(interval_deps & deps = dummy);
    template<bool compute_intv = true, bool compute_deps = false> void log(interval_deps & deps = dummy);
    template<bool compute_intv = true, bool compute_deps = false> void log2(interval_deps & deps = dummy);
    template<bool compute_intv = true, bool compute_deps = false> void log10(interval_deps & deps = dummy);
    template<bool compute_intv = true, bool compute_deps = false> void sin(interval_deps & deps = dummy);
    template<bool compute_intv = true, bool compute_deps = false> void cos(interval_deps & deps = dummy);
    template<bool compute_intv = true, bool compute_deps = false> void tan(interval_deps & deps = dummy);
    template<bool compute_intv = true, bool compute_deps = false> void csc(interval_deps & deps = dummy);
    template<bool compute_intv = true, bool compute_deps = false> void sec(interval_deps & deps = dummy);
    template<bool compute_intv = true, bool compute_deps = false> void cot(interval_deps & deps = dummy);
    template<bool compute_intv = true, bool compute_deps = false> void asin(interval_deps & deps = dummy);
    template<bool compute_intv = true, bool compute_deps = false> void acos(interval_deps & deps = dummy);
    template<bool compute_intv = true, bool compute_deps = false> void atan(interval_deps & deps = dummy);
    template<bool compute_intv = true, bool compute_deps = false> void sinh(interval_deps & deps = dummy);
    template<bool compute_intv = true, bool compute_deps = false> void cosh(interval_deps & deps = dummy);
    template<bool compute_intv = true, bool compute_deps = false> void tanh(interval_deps & deps = dummy);
    template<bool compute_intv = true, bool compute_deps = false> void asinh(interval_deps & deps = dummy);
    template<bool compute_intv = true, bool compute_deps = false> void acosh(interval_deps & deps = dummy);
    template<bool compute_intv = true, bool compute_deps = false> void atanh(interval_deps & deps = dummy);

    void exp_jst (interval_deps & deps);
    void exp2_jst (interval_deps & deps);
    void exp10_jst(interval_deps & deps);
    void log_jst  (interval_deps & deps);
    void log2_jst (interval_deps & deps);
    void log10_jst(interval_deps & deps);
    void sin_jst(interval_deps & deps);
    void cos_jst(interval_deps & deps);
    void tan_jst(interval_deps & deps);
    void csc_jst(interval_deps & deps);
    void sec_jst(interval_deps & deps);
    void cot_jst(interval_deps & deps);
    void asin_jst(interval_deps & deps);
    void acos_jst(interval_deps & deps);
    void atan_jst(interval_deps & deps);
    void sinh_jst(interval_deps & deps);
    void cosh_jst(interval_deps & deps);
    void tanh_jst(interval_deps & deps);
    void asinh_jst(interval_deps & deps);
    void acosh_jst(interval_deps & deps);
    void atanh_jst(interval_deps & deps);

    friend interval exp  (interval o) { o.exp();   return o; }
    friend interval exp  (interval o, interval_deps & deps) { o.exp(deps);   return o; }
    friend interval exp_jst(interval o, interval_deps & deps) { o.exp_jst(deps); return o; }

    friend interval exp2 (interval o) { o.exp2();  return o; }
    friend interval exp2 (interval o, interval_deps & deps) { o.exp2(deps);  return o; }
    friend interval exp2_jst(interval o, interval_deps & deps) { o.exp2_jst(deps); return o; }

    friend interval exp10(interval o) { o.exp10(); return o; }
    friend interval exp10(interval o, interval_deps & deps) { o.exp10(deps); return o; }
    friend interval exp10_jst(interval o, interval_deps & deps) { o.exp10(deps); return o; }

    friend interval log  (interval o) { o.log();   return o; }
    friend interval log  (interval o, interval_deps & deps) { o.log(deps);   return o; }
    friend interval log_jst(interval o, interval_deps & deps) { o.log_jst(deps); return o; }

    friend interval log2 (interval o) { o.log2();  return o; }
    friend interval log2 (interval o, interval_deps & deps) { o.log2(deps);  return o; }
    friend interval log2_jst(interval o, interval_deps & deps) { o.log2_jst(deps); return o; }

    friend interval log10(interval o) { o.log10(); return o; }
    friend interval log10(interval o, interval_deps & deps) { o.log10(deps); return o; }
    friend interval log10_jst(interval o, interval_deps & deps) { o.log10_jst(deps); return o; }

    friend interval sin  (interval o) { o.sin();   return o; }
    friend interval sin  (interval o, interval_deps & deps) { o.sin(deps);   return o; }
    friend interval sin_jst(interval o, interval_deps & deps) { o.sin_jst(deps); return o; }

    friend interval cos  (interval o) { o.cos();   return o; }
    friend interval cos  (interval o, interval_deps & deps) { o.cos(deps);   return o; }
    friend interval cos_jst(interval o, interval_deps & deps) { o.cos_jst(deps); return o; }

    friend interval tan  (interval o) { o.tan();   return o; }
    friend interval tan  (interval o, interval_deps & deps) { o.tan(deps);   return o; }
    friend interval tan_jst(interval o, interval_deps & deps) { o.tan_jst(deps); return o; }

    friend interval csc  (interval o) { o.csc();   return o; }
    friend interval csc  (interval o, interval_deps & deps) { o.csc(deps);   return o; }
    friend interval csc_jst(interval o, interval_deps & deps) { o.csc_jst(deps); return o; }

    friend interval sec  (interval o) { o.sec();   return o; }
    friend interval sec  (interval o, interval_deps & deps) { o.sec(deps);   return o; }
    friend interval sec_jst(interval o, interval_deps & deps) { o.sec_jst(deps); return o; }

    friend interval cot  (interval o) { o.cot();   return o; }
    friend interval cot  (interval o, interval_deps & deps) { o.cot(deps);   return o; }
    friend interval cot_jst(interval o, interval_deps & deps) { o.cot_jst(deps); return o; }

    friend interval asin (interval o) { o.asin();  return o; }
    friend interval asin (interval o, interval_deps & deps) { o.asin(deps);  return o; }
    friend interval asin_jst(interval o, interval_deps & deps) { o.asin_jst(deps); return o; }

    friend interval acos (interval o) { o.acos();  return o; }
    friend interval acos (interval o, interval_deps & deps) { o.acos(deps);  return o; }
    friend interval acos_jst(interval o, interval_deps & deps) { o.acos_jst(deps); return o; }

    friend interval atan (interval o) { o.atan();  return o; }
    friend interval atan (interval o, interval_deps & deps) { o.atan(deps);  return o; }
    friend interval atan_jst(interval o, interval_deps & deps) { o.atan_jst(deps); return o; }

    friend interval sinh (interval o) { o.sinh();  return o; }
    friend interval sinh (interval o, interval_deps & deps) { o.sinh(deps);  return o; }
    friend interval sinh_jst(interval o, interval_deps & deps) { o.sinh_jst(deps); return o; }

    friend interval cosh (interval o) { o.cosh();  return o; }
    friend interval cosh (interval o, interval_deps & deps) { o.cosh(deps);  return o; }
    friend interval cosh_jst(interval o, interval_deps & deps) { o.cosh_jst(deps);  return o; }

    friend interval tanh (interval o) { o.tanh();  return o; }
    friend interval tanh (interval o, interval_deps & deps) { o.tanh(deps);  return o; }
    friend interval tanh_jst(interval o, interval_deps & deps) { o.tanh_jst(deps); return o; }

    friend interval asinh(interval o) { o.asinh(); return o; }
    friend interval asinh(interval o, interval_deps & deps) { o.asinh(deps); return o; }
    friend interval asinh_jst(interval o, interval_deps & deps) { o.asinh_jst(deps); return o; }

    friend interval acosh(interval o) { o.acosh(); return o; }
    friend interval acosh(interval o, interval_deps & deps) { o.acosh(deps); return o; }
    friend interval acosh_jst(interval o, interval_deps & deps) { o.acosh_jst(deps); return o; }

    friend interval atanh(interval o) { o.atanh(); return o; }
    friend interval atanh(interval o, interval_deps & deps) { o.atanh(deps); return o; }
    friend interval atanh_jst(interval o, interval_deps & deps) { o.atanh_jst(deps); return o; }

    friend interval operator+(interval a, interval const & b) { return a += b; }
    friend interval operator-(interval a, interval const & b) { return a -= b; }
    friend interval operator*(interval a, interval const & b) { return a *= b; }
    friend interval operator/(interval a, interval const & b) { return a /= b; }

    friend interval operator+(interval a, T const & b) { return a += b; }
    friend interval operator-(interval a, T const & b) { return a -= b; }
    friend interval operator*(interval a, T const & b) { return a *= b; }
    friend interval operator/(interval a, T const & b) { return a /= b; }

    friend interval operator+(T const & a, interval b) { return b += a; }
    friend interval operator-(T const & a, interval b) { b.neg(); return b += a; }
    friend interval operator*(T const & a, interval b) { return b *= a; }
    friend interval operator/(T const & a, interval b) { b.inv(); return b *= a; }


    bool check_invariant() const;

    void display(std::ostream & out) const;

    friend std::ostream & operator<<(std::ostream & out, interval const & n) {
        n.display(out);
        return out;
    }
};

}
