/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <iostream>
#include <limits>
#include "rc.h"
#include "name.h"
#include "level.h"
#include "hash.h"
#include "buffer.h"
#include "format.h"

namespace lean {
class value;
/* =======================================
   Expressions
   expr ::=   Var           idx
          |   Constant      name
          |   Value         value
          |   App           [expr]
          |   Lambda        name expr expr
          |   Pi            name expr expr
          |   Type          universe
          |   Eq            expr expr         (heterogeneous equality)
          |   Let           name expr expr

TODO: add meta-variables, and match expressions.

The main API is divided in the following sections
- Testers
- Constructors
- Accessors
- Miscellaneous
======================================= */
enum class expr_kind { Var, Constant, Value, App, Lambda, Pi, Type, Eq, Let };

/**
    \brief Base class used to represent expressions.

    In principle, the expr_cell class and subclasses should be located in the .cpp file.
    However, this is performance critical code, and we want to be able to have
    inline definitions.
*/
class expr_cell {
protected:
    unsigned short     m_kind;
    std::atomic_ushort m_flags;
    unsigned m_hash;
    MK_LEAN_RC(); // Declare m_rc counter
    void dealloc();

    bool max_shared() const { return (m_flags & 1) != 0; }
    void set_max_shared() { m_flags |= 1; }
    friend class max_sharing_fn;

    bool is_closed() const { return (m_flags & 2) != 0; }
    void set_closed() { m_flags |= 2; }
    friend class has_free_var_fn;
public:
    expr_cell(expr_kind k, unsigned h);
    expr_kind kind() const { return static_cast<expr_kind>(m_kind); }
    unsigned  hash() const { return m_hash; }
};

/**
   \brief Exprs for encoding formulas/expressions, types and proofs.
*/
class expr {
private:
    expr_cell * m_ptr;
    explicit expr(expr_cell * ptr):m_ptr(ptr) {}
public:
    expr():m_ptr(nullptr) {}
    expr(expr const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
    expr(expr && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
    ~expr() { if (m_ptr) m_ptr->dec_ref(); }

    static expr const & null();

    friend void swap(expr & a, expr & b) { std::swap(a.m_ptr, b.m_ptr); }

    void release() { if (m_ptr) m_ptr->dec_ref(); m_ptr = nullptr; }

    expr & operator=(expr const & s) { LEAN_COPY_REF(expr, s); }
    expr & operator=(expr && s) { LEAN_MOVE_REF(expr, s); }

    expr_kind kind() const { return m_ptr->kind(); }
    unsigned  hash() const { return m_ptr ? m_ptr->hash() : 23; }

    expr_cell * raw() const { return m_ptr; }

    operator bool() const { return m_ptr != nullptr; }

    friend expr mk_var(unsigned idx);
    friend expr mk_constant(name const & n);
    friend expr mk_value(value & v);
    friend expr mk_app(unsigned num_args, expr const * args);
    friend expr mk_eq(expr const & l, expr const & r);
    friend expr mk_lambda(name const & n, expr const & t, expr const & e);
    friend expr mk_pi(name const & n, expr const & t, expr const & e);
    friend expr mk_type(level const & l);
    friend expr mk_let(name const & n, expr const & v, expr const & e);

    friend bool is_eqp(expr const & a, expr const & b) { return a.m_ptr == b.m_ptr; }

    // Overloaded operator() can be used to create applications
    expr operator()(expr const & a1) const;
    expr operator()(expr const & a1, expr const & a2) const;
    expr operator()(expr const & a1, expr const & a2, expr const & a3) const;
    expr operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4) const;
    expr operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4, expr const & a5) const;
    expr operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4, expr const & a5, expr const & a6) const;
    expr operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4, expr const & a5, expr const & a6, expr const & a7) const;
};

// =======================================
// Expr (internal) Representation
/** \brief Free variables. They are encoded using de Bruijn's indices. */
class expr_var : public expr_cell {
    unsigned m_vidx; // de Bruijn index
public:
    expr_var(unsigned idx);
    unsigned get_vidx() const { return m_vidx; }
};
/** \brief Constants. */
class expr_const : public expr_cell {
    name     m_name;
public:
    expr_const(name const & n);
    name const & get_name() const { return m_name; }
};
/** \brief Function Applications */
class expr_app : public expr_cell {
    unsigned m_num_args;
    expr     m_args[0];
    friend expr mk_app(unsigned num_args, expr const * args);
public:
    expr_app(unsigned size);
    ~expr_app();
    unsigned     get_num_args() const        { return m_num_args; }
    expr const & get_arg(unsigned idx) const { lean_assert(idx < m_num_args); return m_args[idx]; }
    expr const * begin_args() const          { return m_args; }
    expr const * end_args() const            { return m_args + m_num_args; }
};
/** \brief Heterogeneous equality */
class expr_eq : public expr_cell {
    expr m_lhs;
    expr m_rhs;
public:
    expr_eq(expr const & lhs, expr const & rhs);
    ~expr_eq();
    expr const & get_lhs() const { return m_lhs; }
    expr const & get_rhs() const { return m_rhs; }
};
/** \brief Super class for lambda abstraction and pi (functional spaces). */
class expr_abstraction : public expr_cell {
    name     m_name;
    expr     m_domain;
    expr     m_body;
public:
    expr_abstraction(expr_kind k, name const & n, expr const & t, expr const & e);
    name const & get_name() const   { return m_name; }
    expr const & get_domain() const { return m_domain; }
    expr const & get_body() const   { return m_body; }
};
/** \brief Lambda abstractions */
class expr_lambda : public expr_abstraction {
public:
    expr_lambda(name const & n, expr const & t, expr const & e);
};
/** \brief (dependent) Functional spaces */
class expr_pi : public expr_abstraction {
public:
    expr_pi(name const & n, expr const & t, expr const & e);
};
/** \brief Let expressions */
class expr_let : public expr_cell {
    name     m_name;
    expr     m_value;
    expr     m_body;
public:
    expr_let(name const & n, expr const & v, expr const & b);
    ~expr_let();
    name const & get_name() const  { return m_name; }
    expr const & get_value() const { return m_value; }
    expr const & get_body() const  { return m_body; }
};
/** \brief Type */
class expr_type : public expr_cell {
    level    m_level;
public:
    expr_type(level const & l);
    ~expr_type();
    level const & get_level() const { return m_level; }
};
/**
   \brief Base class for semantic attachment cells.
*/
class value {
    void dealloc() { delete this; }
    MK_LEAN_RC();
public:
    value():m_rc(0) {}
    virtual ~value() {}
    virtual char const * kind() const = 0;
    virtual expr get_type() const = 0;
    virtual bool normalize(unsigned num_args, expr const * args, expr & r) const = 0;
    virtual bool operator==(value const & other) const = 0;
    virtual void display(std::ostream & out) const = 0;
    virtual format pp() const = 0;
    virtual unsigned hash() const = 0;
};

/** \brief Semantic attachments */
class expr_value : public expr_cell {
    value & m_val;
    friend expr copy(expr const & a);
public:
    expr_value(value & v);
    ~expr_value();

    value const & get_value() const { return m_val; }
};
// =======================================


// =======================================
// Testers
inline bool is_var(expr_cell * e)         { return e->kind() == expr_kind::Var; }
inline bool is_constant(expr_cell * e)    { return e->kind() == expr_kind::Constant; }
inline bool is_value(expr_cell * e)       { return e->kind() == expr_kind::Value; }
inline bool is_app(expr_cell * e)         { return e->kind() == expr_kind::App; }
inline bool is_eq(expr_cell * e)          { return e->kind() == expr_kind::Eq; }
inline bool is_lambda(expr_cell * e)      { return e->kind() == expr_kind::Lambda; }
inline bool is_pi(expr_cell * e)          { return e->kind() == expr_kind::Pi; }
inline bool is_type(expr_cell * e)        { return e->kind() == expr_kind::Type; }
inline bool is_let(expr_cell * e)         { return e->kind() == expr_kind::Let; }
inline bool is_abstraction(expr_cell * e) { return is_lambda(e) || is_pi(e); }

inline bool is_var(expr const & e)         { return e.kind() == expr_kind::Var; }
inline bool is_constant(expr const & e)    { return e.kind() == expr_kind::Constant; }
inline bool is_value(expr const & e)       { return e.kind() == expr_kind::Value; }
inline bool is_app(expr const & e)         { return e.kind() == expr_kind::App; }
inline bool is_eq(expr const & e)          { return e.kind() == expr_kind::Eq; }
inline bool is_lambda(expr const & e)      { return e.kind() == expr_kind::Lambda; }
inline bool is_pi(expr const & e)          { return e.kind() == expr_kind::Pi; }
       bool is_arrow(expr const & e);
inline bool is_type(expr const & e)        { return e.kind() == expr_kind::Type; }
inline bool is_let(expr const & e)         { return e.kind() == expr_kind::Let; }
inline bool is_abstraction(expr const & e) { return is_lambda(e) || is_pi(e); }
// =======================================

// =======================================
// Constructors
inline expr mk_var(unsigned idx) { return expr(new expr_var(idx)); }
inline expr Var(unsigned idx) { return mk_var(idx); }
inline expr mk_constant(name const & n) { return expr(new expr_const(n)); }
inline expr Const(name const & n) { return mk_constant(n); }
inline expr mk_value(value & v) { return expr(new expr_value(v)); }
inline expr to_expr(value & v) { return mk_value(v); }
       expr mk_app(unsigned num_args, expr const * args);
inline expr mk_app(std::initializer_list<expr> const & l) { return mk_app(l.size(), l.begin()); }
inline expr mk_app(expr const & e1, expr const & e2) { return mk_app({e1, e2}); }
inline expr mk_app(expr const & e1, expr const & e2, expr const & e3) { return mk_app({e1, e2, e3}); }
inline expr mk_app(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({e1, e2, e3, e4}); }
inline expr mk_app(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5) { return mk_app({e1, e2, e3, e4, e5}); }
inline expr mk_eq(expr const & l, expr const & r) { return expr(new expr_eq(l, r)); }
inline expr Eq(expr const & l, expr const & r) { return mk_eq(l, r); }
inline expr mk_lambda(name const & n, expr const & t, expr const & e) { return expr(new expr_lambda(n, t, e)); }
inline expr mk_pi(name const & n, expr const & t, expr const & e) { return expr(new expr_pi(n, t, e)); }
inline expr arrow(expr const & t, expr const & e) { return mk_pi(name("_"), t, e); }
inline expr operator>>(expr const & t, expr const & e) { return arrow(t, e); }
inline expr mk_let(name const & n, expr const & v, expr const & e) { return expr(new expr_let(n, v, e)); }
inline expr Let(name const & n, expr const & v, expr const & e) { return mk_let(n, v, e); }
inline expr mk_type(level const & l) { return expr(new expr_type(l)); }
       expr mk_type();
inline expr Type(level const & l) { return mk_type(l); }
inline expr Type() { return mk_type(); }

inline expr expr::operator()(expr const & a1) const { return mk_app({*this, a1}); }
inline expr expr::operator()(expr const & a1, expr const & a2) const { return mk_app({*this, a1, a2}); }
inline expr expr::operator()(expr const & a1, expr const & a2, expr const & a3) const { return mk_app({*this, a1, a2, a3}); }
inline expr expr::operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4) const { return mk_app({*this, a1, a2, a3, a4}); }
inline expr expr::operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4, expr const & a5) const { return mk_app({*this, a1, a2, a3, a4, a5}); }
inline expr expr::operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4, expr const & a5, expr const & a6) const { return mk_app({*this, a1, a2, a3, a4, a5, a6}); }
inline expr expr::operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4, expr const & a5, expr const & a6, expr const & a7) const { return mk_app({*this, a1, a2, a3, a4, a5, a6, a7}); }
// =======================================

// =======================================
// Casting (these functions are only needed for low-level code)
inline expr_var *         to_var(expr_cell * e)         { lean_assert(is_var(e));         return static_cast<expr_var*>(e); }
inline expr_const *       to_constant(expr_cell * e)    { lean_assert(is_constant(e));    return static_cast<expr_const*>(e); }
inline expr_app *         to_app(expr_cell * e)         { lean_assert(is_app(e));         return static_cast<expr_app*>(e); }
inline expr_eq *          to_eq(expr_cell * e)          { lean_assert(is_eq(e));          return static_cast<expr_eq*>(e); }
inline expr_abstraction * to_abstraction(expr_cell * e) { lean_assert(is_abstraction(e)); return static_cast<expr_abstraction*>(e); }
inline expr_lambda *      to_lambda(expr_cell * e)      { lean_assert(is_lambda(e));      return static_cast<expr_lambda*>(e); }
inline expr_pi *          to_pi(expr_cell * e)          { lean_assert(is_pi(e));          return static_cast<expr_pi*>(e); }
inline expr_type *        to_type(expr_cell * e)        { lean_assert(is_type(e));        return static_cast<expr_type*>(e); }
inline expr_let *         to_let(expr_cell * e)         { lean_assert(is_let(e));         return static_cast<expr_let*>(e); }

inline expr_var *         to_var(expr const & e)         { return to_var(e.raw()); }
inline expr_const *       to_constant(expr const & e)    { return to_constant(e.raw()); }
inline expr_app *         to_app(expr const & e)         { return to_app(e.raw()); }
inline expr_eq *          to_eq(expr const & e)          { return to_eq(e.raw()); }
inline expr_abstraction * to_abstraction(expr const & e) { return to_abstraction(e.raw()); }
inline expr_lambda *      to_lambda(expr const & e)      { return to_lambda(e.raw()); }
inline expr_pi *          to_pi(expr const & e)          { return to_pi(e.raw()); }
inline expr_let *         to_let(expr const & e)         { return to_let(e.raw()); }
inline expr_type *        to_type(expr const & e)        { return to_type(e.raw()); }
// =======================================

// =======================================
// Accessors
inline unsigned      get_rc(expr_cell * e)               { return e->get_rc(); }
inline bool          is_shared(expr_cell * e)            { return get_rc(e) > 1; }
inline unsigned      var_idx(expr_cell * e)              { return to_var(e)->get_vidx(); }
inline bool          is_var(expr_cell * e, unsigned i)   { return is_var(e) && var_idx(e) == i; }
inline name const &  const_name(expr_cell * e)           { return to_constant(e)->get_name(); }
inline value const & to_value(expr_cell * e)             { lean_assert(is_value(e)); return static_cast<expr_value*>(e)->get_value(); }
inline unsigned      num_args(expr_cell * e)             { return to_app(e)->get_num_args(); }
inline expr const &  arg(expr_cell * e, unsigned idx)    { return to_app(e)->get_arg(idx); }
inline expr const &  eq_lhs(expr_cell * e)               { return to_eq(e)->get_lhs(); }
inline expr const &  eq_rhs(expr_cell * e)               { return to_eq(e)->get_rhs(); }
inline name const &  abst_name(expr_cell * e)            { return to_abstraction(e)->get_name(); }
inline expr const &  abst_domain(expr_cell * e)          { return to_abstraction(e)->get_domain(); }
inline expr const &  abst_body(expr_cell * e)            { return to_abstraction(e)->get_body(); }
inline level const & ty_level(expr_cell * e)             { return to_type(e)->get_level(); }
inline name const &  let_name(expr_cell * e)             { return to_let(e)->get_name(); }
inline expr const &  let_value(expr_cell * e)            { return to_let(e)->get_value(); }
inline expr const &  let_body(expr_cell * e)             { return to_let(e)->get_body(); }

inline unsigned      get_rc(expr const &  e)              { return e.raw()->get_rc(); }
inline bool          is_shared(expr const & e)            { return get_rc(e) > 1; }
inline unsigned      var_idx(expr const & e)              { return to_var(e)->get_vidx(); }
inline bool          is_var(expr const & e, unsigned i)   { return is_var(e) && var_idx(e) == i; }
inline name const &  const_name(expr const & e)           { return to_constant(e)->get_name(); }
inline value const & to_value(expr const & e)             { return to_value(e.raw()); }
inline unsigned      num_args(expr const & e)             { return to_app(e)->get_num_args(); }
inline expr const &  arg(expr const & e, unsigned idx)    { return to_app(e)->get_arg(idx); }
inline expr const *  begin_args(expr const & e)           { return to_app(e)->begin_args(); }
inline expr const *  end_args(expr const & e)             { return to_app(e)->end_args(); }
inline expr const &  eq_lhs(expr const & e)               { return to_eq(e)->get_lhs(); }
inline expr const &  eq_rhs(expr const & e)               { return to_eq(e)->get_rhs(); }
inline name const &  abst_name(expr const & e)            { return to_abstraction(e)->get_name(); }
inline expr const &  abst_domain(expr const & e)          { return to_abstraction(e)->get_domain(); }
inline expr const &  abst_body(expr const & e)            { return to_abstraction(e)->get_body(); }
inline level const & ty_level(expr const & e)             { return to_type(e)->get_level(); }
inline name const &  let_name(expr const & e)             { return to_let(e)->get_name(); }
inline expr const &  let_value(expr const & e)            { return to_let(e)->get_value(); }
inline expr const &  let_body(expr const & e)             { return to_let(e)->get_body(); }
// =======================================

// =======================================
// Structural equality
       bool operator==(expr const & a, expr const & b);
inline bool operator!=(expr const & a, expr const & b) { return !operator==(a, b); }
// =======================================

// =======================================
// Expression+Offset
typedef std::pair<expr, unsigned>       expr_offset;
typedef std::pair<expr_cell*, unsigned> expr_cell_offset;
// =======================================

// =======================================
// Auxiliary functionals
/** \brief Functional object for hashing kernel expressions. */
struct expr_hash { unsigned operator()(expr const & e) const { return e.hash(); } };
/** \brief Functional object for testing pointer equality between kernel expressions. */
struct expr_eqp { bool operator()(expr const & e1, expr const & e2) const { return is_eqp(e1, e2); } };
/** \brief Functional object for hashing kernel expression cells. */
struct expr_cell_hash { unsigned operator()(expr_cell * e) const { return e->hash(); } };
/** \brief Functional object for testing pointer equality between kernel cell expressions. */
struct expr_cell_eqp { bool operator()(expr_cell * e1, expr_cell * e2) const { return e1 == e2; } };
/** \brief Functional object for hashing a pair (n,k) where n is a kernel expressions, and k is an offset. */
struct expr_offset_hash { unsigned operator()(expr_offset const & p) const { return hash(p.first.hash(), p.second); } };
/** \brief Functional object for comparing pairs (expression, offset). */
struct expr_offset_eqp { unsigned operator()(expr_offset const & p1, expr_offset const & p2) const { return is_eqp(p1.first, p2.first) && p1.second == p2.second; } };
/** \brief Functional object for hashing a pair (n,k) where n is a kernel cell expressions, and k is an offset. */
struct expr_cell_offset_hash { unsigned operator()(expr_cell_offset const & p) const { return hash(p.first->hash(), p.second); } };
/** \brief Functional object for comparing pairs (expression cell, offset). */
struct expr_cell_offset_eqp { unsigned operator()(expr_cell_offset const & p1, expr_cell_offset const & p2) const { return p1 == p2; } };
// =======================================

// =======================================
// Miscellaneous
std::ostream & operator<<(std::ostream & out, expr const & a);
/**
   \brief Wrapper for iterating over application arguments.

   If \c n is an application, it allows us to write

   \code
   for (expr const & arg : app_args(n)) {
   ... do something with argument
   }
   \endcode
*/
struct args {
    expr const & m_app;
    args(expr const & a):m_app(a) { lean_assert(is_app(a)); }
    expr const * begin() const { return &arg(m_app, 0); }
    expr const * end() const { return begin() + num_args(m_app); }
};
/**
   \brief Return a shallow copy of \c e
*/
expr copy(expr const & e);
// =======================================

// =======================================
// Update
template<typename F> expr update_app(expr const & e, F f) {
    static_assert(std::is_same<typename std::result_of<F(expr const &)>::type, expr>::value,
                  "update_app: return type of f is not expr");
    buffer<expr> new_args;
    bool modified = false;
    for (expr const & a : args(e)) {
        new_args.push_back(f(a));
        if (!is_eqp(a, new_args.back()))
            modified = true;
    }
    if (modified)
        return mk_app(new_args.size(), new_args.data());
    else
        return e;
}
template<typename F> expr update_abst(expr const & e, F f) {
    static_assert(std::is_same<typename std::result_of<F(expr const &, expr const &)>::type,
                  std::pair<expr, expr>>::value,
                  "update_abst: return type of f is not pair<expr, expr>");
    expr const & old_t = abst_domain(e);
    expr const & old_b = abst_body(e);
    std::pair<expr, expr> p = f(old_t, old_b);
    if (!is_eqp(p.first, old_t) || !is_eqp(p.second, old_b)) {
        name const & n = abst_name(e);
        return is_pi(e) ? mk_pi(n, p.first, p.second) : mk_lambda(n, p.first, p.second);
    } else {
        return e;
    }
}
template<typename F> expr update_let(expr const & e, F f) {
    static_assert(std::is_same<typename std::result_of<F(expr const &, expr const &)>::type,
                  std::pair<expr, expr>>::value,
                  "update_let: return type of f is not pair<expr, expr>");
    expr const & old_v = let_value(e);
    expr const & old_b = let_body(e);
    std::pair<expr, expr> p = f(old_v, old_b);
    if (!is_eqp(p.first, old_v) || !is_eqp(p.second, old_b))
        return mk_let(let_name(e), p.first, p.second);
    else
        return e;
}
template<typename F> expr update_eq(expr const & e, F f) {
    static_assert(std::is_same<typename std::result_of<F(expr const &, expr const &)>::type,
                  std::pair<expr, expr>>::value,
                  "update_eq: return type of f is not pair<expr, expr>");
    expr const & old_l = eq_lhs(e);
    expr const & old_r = eq_rhs(e);
    std::pair<expr, expr> p = f(old_l, old_r);
    if (!is_eqp(p.first, old_l) || !is_eqp(p.second, old_r))
        return mk_eq(p.first, p.second);
    else
        return e;
}
// =======================================
}
void print(lean::expr const & a);
