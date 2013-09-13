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

typedef short bound_deps;
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
    interval(interval<T> const & n);
    // move constructor
    interval(interval<T> && src);

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
    // [0, 0]
    bool is_zero() const { return is_lower_zero() && is_upper_zero(); }

    // Interval contains the value zero
    bool contains_zero() const;
    /**
       \brief Return true iff this contains b.
       That is, every value in b is a value of this.
    */
    bool contains(interval<T> const & b) const;

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

    template<bool compute_intv = true, bool compute_deps = false> void neg(interval_deps & deps = dummy);
    void neg_jst(interval_deps & deps);
    friend interval<T> neg(interval<T> o) { o.neg(); return o; }
    friend interval<T> neg_jst(interval<T> o, interval_deps & deps) { o.neg(deps); return o; }

    interval & operator+=(interval<T> const & o);
    interval & operator-=(interval<T> const & o);
    interval & operator*=(interval<T> const & o);
    interval & operator/=(interval<T> const & o);

    template<bool compute_intv = true, bool compute_deps = false>
    interval & add(interval<T> const & o, interval_deps & deps = dummy);
    template<bool compute_intv = true, bool compute_deps = false>
    interval & sub(interval<T> const & o, interval_deps & deps = dummy);
    template<bool compute_intv = true, bool compute_deps = false>
    interval & mul(interval<T> const & o, interval_deps & deps = dummy);
    template<bool compute_intv = true, bool compute_deps = false>
    interval & div(interval<T> const & o, interval_deps & deps = dummy);

    void add_jst (interval<T> const & o, interval_deps & deps);
    void sub_jst (interval<T> const & o, interval_deps & deps);
    void mul_jst (interval<T> const & o, interval_deps & deps);
    void div_jst (interval<T> const & o, interval_deps & deps);

    interval & operator+=(T const & o);
    interval & operator-=(T const & o);
    interval & operator*=(T const & o);
    interval & operator/=(T const & o);

    template<bool compute_intv = true, bool compute_deps = false> void inv(interval_deps & deps = dummy);
    void inv_jst (interval_deps & deps);
    friend interval<T> inv(interval<T> o) { o.inv(); return o; }

    void fmod(interval<T> y);
    void fmod(T y);
    friend interval<T> fmod(interval<T> o, interval<T> y) { o.fmod(y); return o; }
    friend interval<T> fmod(interval<T> o, T y) { o.fmod(y); return o; }

    template<bool compute_intv = true, bool compute_deps = false>
    void power(unsigned n, interval_deps & deps = dummy);
    void power_jst(unsigned n, interval_deps & deps);
    friend interval<T> power(interval<T> o, unsigned k) { o.power(k); return o; }

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

    friend interval<T> exp  (interval<T> o) { o.exp();   return o; }
    friend interval<T> exp  (interval<T> o, interval_deps & deps) { o.exp(deps);   return o; }
    friend interval<T> exp_jst(interval<T> o, interval_deps & deps) { o.exp_jst(deps); return o; }

    friend interval<T> exp2 (interval<T> o) { o.exp2();  return o; }
    friend interval<T> exp2 (interval<T> o, interval_deps & deps) { o.exp2(deps);  return o; }
    friend interval<T> exp2_jst(interval<T> o, interval_deps & deps) { o.exp2_jst(deps); return o; }

    friend interval<T> exp10(interval<T> o) { o.exp10(); return o; }
    friend interval<T> exp10(interval<T> o, interval_deps & deps) { o.exp10(deps); return o; }
    friend interval<T> exp10_jst(interval<T> o, interval_deps & deps) { o.exp10(deps); return o; }

    friend interval<T> log  (interval<T> o) { o.log();   return o; }
    friend interval<T> log  (interval<T> o, interval_deps & deps) { o.log(deps);   return o; }
    friend interval<T> log_jst(interval<T> o, interval_deps & deps) { o.log_jst(deps); return o; }

    friend interval<T> log2 (interval<T> o) { o.log2();  return o; }
    friend interval<T> log2 (interval<T> o, interval_deps & deps) { o.log2(deps);  return o; }
    friend interval<T> log2_jst(interval<T> o, interval_deps & deps) { o.log2_jst(deps); return o; }

    friend interval<T> log10(interval<T> o) { o.log10(); return o; }
    friend interval<T> log10(interval<T> o, interval_deps & deps) { o.log10(deps); return o; }
    friend interval<T> log10_jst(interval<T> o, interval_deps & deps) { o.log10_jst(deps); return o; }

    friend interval<T> sin  (interval<T> o) { o.sin();   return o; }
    friend interval<T> sin  (interval<T> o, interval_deps & deps) { o.sin(deps);   return o; }
    friend interval<T> sin_jst(interval<T> o, interval_deps & deps) { o.sin_jst(deps); return o; }

    friend interval<T> cos  (interval<T> o) { o.cos();   return o; }
    friend interval<T> cos  (interval<T> o, interval_deps & deps) { o.cos(deps);   return o; }
    friend interval<T> cos_jst(interval<T> o, interval_deps & deps) { o.cos_jst(deps); return o; }

    friend interval<T> tan  (interval<T> o) { o.tan();   return o; }
    friend interval<T> tan  (interval<T> o, interval_deps & deps) { o.tan(deps);   return o; }
    friend interval<T> tan_jst(interval<T> o, interval_deps & deps) { o.tan_jst(deps); return o; }

    friend interval<T> csc  (interval<T> o) { o.csc();   return o; }
    friend interval<T> csc  (interval<T> o, interval_deps & deps) { o.csc(deps);   return o; }
    friend interval<T> csc_jst(interval<T> o, interval_deps & deps) { o.csc_jst(deps); return o; }

    friend interval<T> sec  (interval<T> o) { o.sec();   return o; }
    friend interval<T> sec  (interval<T> o, interval_deps & deps) { o.sec(deps);   return o; }
    friend interval<T> sec_jst(interval<T> o, interval_deps & deps) { o.sec_jst(deps); return o; }

    friend interval<T> cot  (interval<T> o) { o.cot();   return o; }
    friend interval<T> cot  (interval<T> o, interval_deps & deps) { o.cot(deps);   return o; }
    friend interval<T> cot_jst(interval<T> o, interval_deps & deps) { o.cot_jst(deps); return o; }

    friend interval<T> asin (interval<T> o) { o.asin();  return o; }
    friend interval<T> asin (interval<T> o, interval_deps & deps) { o.asin(deps);  return o; }
    friend interval<T> asin_jst(interval<T> o, interval_deps & deps) { o.asin_jst(deps); return o; }

    friend interval<T> acos (interval<T> o) { o.acos();  return o; }
    friend interval<T> acos (interval<T> o, interval_deps & deps) { o.acos(deps);  return o; }
    friend interval<T> acos_jst(interval<T> o, interval_deps & deps) { o.acos_jst(deps); return o; }

    friend interval<T> atan (interval<T> o) { o.atan();  return o; }
    friend interval<T> atan (interval<T> o, interval_deps & deps) { o.atan(deps);  return o; }
    friend interval<T> atan_jst(interval<T> o, interval_deps & deps) { o.atan_jst(deps); return o; }

    friend interval<T> sinh (interval<T> o) { o.sinh();  return o; }
    friend interval<T> sinh (interval<T> o, interval_deps & deps) { o.sinh(deps);  return o; }
    friend interval<T> sinh_jst(interval<T> o, interval_deps & deps) { o.sinh_jst(deps); return o; }

    friend interval<T> cosh (interval<T> o) { o.cosh();  return o; }
    friend interval<T> cosh (interval<T> o, interval_deps & deps) { o.cosh(deps);  return o; }
    friend interval<T> cosh_jst(interval<T> o, interval_deps & deps) { o.cosh();  return o; }

    friend interval<T> tanh (interval<T> o) { o.tanh();  return o; }
    friend interval<T> tanh (interval<T> o, interval_deps & deps) { o.tanh(deps);  return o; }
    friend interval<T> tanh_jst(interval<T> o, interval_deps & deps) { o.tanh_jst(deps); return o; }

    friend interval<T> asinh(interval<T> o) { o.asinh(); return o; }
    friend interval<T> asinh(interval<T> o, interval_deps & deps) { o.asinh(deps); return o; }
    friend interval<T> asinh_jst(interval<T> o, interval_deps & deps) { o.asinh_jst(deps); return o; }

    friend interval<T> acosh(interval<T> o) { o.acosh(); return o; }
    friend interval<T> acosh(interval<T> o, interval_deps & deps) { o.acosh(deps); return o; }
    friend interval<T> acosh_jst(interval<T> o, interval_deps & deps) { o.acosh_jst(deps); return o; }

    friend interval<T> atanh(interval<T> o) { o.atanh(); return o; }
    friend interval<T> atanh(interval<T> o, interval_deps & deps) { o.atanh(deps); return o; }
    friend interval<T> atanh_jst(interval<T> o, interval_deps & deps) { o.atanh_jst(deps); return o; }

    friend interval<T> operator+(interval<T> a, interval<T> const & b) { return a += b; }
    friend interval<T> operator-(interval<T> a, interval<T> const & b) { return a -= b; }
    friend interval<T> operator*(interval<T> a, interval<T> const & b) { return a *= b; }
    friend interval<T> operator/(interval<T> a, interval<T> const & b) { return a /= b; }

    friend interval<T> operator+(interval<T> a, T const & b) { return a += b; }
    friend interval<T> operator-(interval<T> a, T const & b) { return a -= b; }
    friend interval<T> operator*(interval<T> a, T const & b) { return a *= b; }
    friend interval<T> operator/(interval<T> a, T const & b) { return a /= b; }

    friend interval<T> operator+(T const & a, interval<T> b) { return b += a; }
    friend interval<T> operator-(T const & a, interval<T> b) { b.neg(); return b += a; }
    friend interval<T> operator*(T const & a, interval<T> b) { return b *= a; }
    friend interval<T> operator/(T const & a, interval<T> b) { b.inv(); return b *= a; }


    bool check_invariant() const;

    void display(std::ostream & out) const;

    friend std::ostream & operator<<(std::ostream & out, interval const & n) {
        n.display(out);
        return out;
    }
};

}
