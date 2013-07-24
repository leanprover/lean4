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
#include "mpz.h"
#include "hash.h"

namespace lean {
/* =======================================
   Expressions
   expr ::=   Var      idx
          |   Constant name
          |   App      [expr]
          |   Lambda   name expr expr
          |   Pi       name expr expr
          |   Prop
          |   Type     universe
          |   Numeral  value

TODO: add meta-variables, let, constructor references and match.

The main API is divided in the following sections
- Testers
- Constructors
- Accessors
- Miscellaneous
======================================= */
enum class expr_kind { Var, Constant, App, Lambda, Pi, Prop, Type, Numeral };

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
   \brief Instead of fixed universes, we use universe variables with
   explicit user-declared constraints between universe variables.

   Each universe variable is associated with a name.

   If the Boolean in the following pair is true, then we are taking
   the successor of the universe variable.

   For additional information, see:
   Explicit universes for the calculus of constructions, Courant J (2002).
*/
typedef std::pair<bool, name> universe_variable;
typedef universe_variable uvar;

/**
   \brief Exprs for encoding formulas/expressions, types and proofs.
*/
class expr {
private:
    expr_cell * m_ptr;
    explicit expr(expr_cell * ptr):m_ptr(ptr) {}
public:
    expr():m_ptr(0) {}
    expr(expr const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
    expr(expr && s):m_ptr(s.m_ptr) { s.m_ptr = 0; }
    ~expr() { if (m_ptr) m_ptr->dec_ref(); }

    friend void swap(expr & a, expr & b) { std::swap(a.m_ptr, b.m_ptr); }

    expr & operator=(expr const & s) {
        if (s.m_ptr)
            s.m_ptr->inc_ref();
        if (m_ptr)
            m_ptr->dec_ref();
        m_ptr = s.m_ptr;
        return *this;
    }
    expr & operator=(expr && s) {
        if (m_ptr)
            m_ptr->dec_ref();
        m_ptr = s.m_ptr;
        s.m_ptr = 0;
        return *this;
    }

    expr_kind kind() const { return m_ptr->kind(); }
    unsigned  hash() const { return m_ptr->hash(); }

    expr_cell * raw() const { return m_ptr; }

    friend expr var(unsigned idx);
    friend expr constant(name const & n);
    friend expr constant(name const & n, unsigned pos);
    friend expr app(unsigned num_args, expr const * args);
    friend expr app(std::initializer_list<expr> const & l);
    friend expr lambda(name const & n, expr const & t, expr const & e);
    friend expr pi(name const & n, expr const & t, expr const & e);
    friend expr prop();
    friend expr type(unsigned size, uvar const * vars);
    friend expr type(std::initializer_list<uvar> const & l);
    friend expr numeral(mpz const & n);

    friend bool eqp(expr const & a, expr const & b) { return a.m_ptr == b.m_ptr; }

    // Overloaded operator() can be used to create applications
    expr operator()(expr const & a1) const;
    expr operator()(expr const & a1, expr const & a2) const;
    expr operator()(expr const & a1, expr const & a2, expr const & a3) const;
    expr operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4) const;
};

// =======================================
// Expr (internal) Representation
// 1. Free variables
class expr_var : public expr_cell {
    unsigned m_vidx; // de Bruijn index
public:
    expr_var(unsigned idx);
    unsigned get_vidx() const { return m_vidx; }
};
// 2. Constants
class expr_const : public expr_cell {
    name     m_name;
    unsigned m_pos;  // position in the environment.
public:
    expr_const(name const & n, unsigned pos = std::numeric_limits<unsigned>::max());
    name const & get_name() const { return m_name; }
    unsigned     get_pos() const { return m_pos; }
};
// 3. Applications
class expr_app : public expr_cell {
    unsigned m_num_args;
    expr     m_args[0];
    friend expr app(unsigned num_args, expr const * args);
public:
    expr_app(unsigned size);
    ~expr_app();
    unsigned     get_num_args() const        { return m_num_args; }
    expr const & get_arg(unsigned idx) const { lean_assert(idx < m_num_args); return m_args[idx]; }
    expr const * begin_args() const          { return m_args; }
    expr const * end_args() const            { return m_args + m_num_args; }
};
// 4. Abstraction
class expr_abstraction : public expr_cell {
    name     m_name;
    expr     m_type;
    expr     m_body;
public:
    expr_abstraction(expr_kind k, name const & n, expr const & t, expr const & e);
    name const & get_name() const { return m_name; }
    expr const & get_type() const { return m_type; }
    expr const & get_body() const { return m_body; }
};
// 5. Lambda
class expr_lambda : public expr_abstraction {
public:
    expr_lambda(name const & n, expr const & t, expr const & e);
};
// 6. Pi
class expr_pi : public expr_abstraction {
public:
    expr_pi(name const & n, expr const & t, expr const & e);
};
// 7. Prop
class expr_prop : public expr_cell {
public:
    expr_prop():expr_cell(expr_kind::Prop, 17) {}
};
// 8. Type lvl
class expr_type : public expr_cell {
    unsigned m_size;
    uvar     m_vars[0];
public:
    expr_type(unsigned size, uvar const * vars);
    ~expr_type();
    unsigned size() const { return m_size; }
    uvar const & get_var(unsigned idx) const { lean_assert(idx < m_size); return m_vars[idx]; }
    uvar const * get_vars() const { return m_vars; }
};
// 9. Numerals
class expr_numeral : public expr_cell {
    mpz   m_numeral;
public:
    expr_numeral(mpz const & n);
    mpz const & get_num() const { return m_numeral; }
};
// =======================================

// =======================================
// Testers
inline bool is_var(expr_cell * e)         { return e->kind() == expr_kind::Var; }
inline bool is_constant(expr_cell * e)    { return e->kind() == expr_kind::Constant; }
inline bool is_app(expr_cell * e)         { return e->kind() == expr_kind::App; }
inline bool is_lambda(expr_cell * e)      { return e->kind() == expr_kind::Lambda; }
inline bool is_pi(expr_cell * e)          { return e->kind() == expr_kind::Pi; }
inline bool is_prop(expr_cell * e)        { return e->kind() == expr_kind::Prop; }
inline bool is_type(expr_cell * e)        { return e->kind() == expr_kind::Type; }
inline bool is_numeral(expr_cell * e)     { return e->kind() == expr_kind::Numeral; }
inline bool is_abstraction(expr_cell * e) { return is_lambda(e) || is_pi(e); }
inline bool is_sort(expr_cell * e)        { return is_prop(e) || is_type(e); }

inline bool is_var(expr const & e)         { return e.kind() == expr_kind::Var; }
inline bool is_constant(expr const & e)    { return e.kind() == expr_kind::Constant; }
inline bool is_app(expr const & e)         { return e.kind() == expr_kind::App; }
inline bool is_lambda(expr const & e)      { return e.kind() == expr_kind::Lambda; }
inline bool is_pi(expr const & e)          { return e.kind() == expr_kind::Pi; }
inline bool is_prop(expr const & e)        { return e.kind() == expr_kind::Prop; }
inline bool is_type(expr const & e)        { return e.kind() == expr_kind::Type; }
inline bool is_numeral(expr const & e)     { return e.kind() == expr_kind::Numeral; }
inline bool is_abstraction(expr const & e) { return is_lambda(e) || is_pi(e); }
inline bool is_sort(expr const & e)        { return is_prop(e) || is_type(e); }
// =======================================

// =======================================
// Constructors
inline expr var(unsigned idx) { return expr(new expr_var(idx)); }
inline expr constant(name const & n) { return expr(new expr_const(n)); }
inline expr constant(char const * n) { return constant(name(n)); }
inline expr constant(name const & n, unsigned pos) { return expr(new expr_const(n, pos)); }
       expr app(unsigned num_args, expr const * args);
inline expr app(expr const & e1, expr const & e2) { expr args[2] = {e1, e2}; return app(2, args); }
inline expr app(expr const & e1, expr const & e2, expr const & e3) { expr args[3] = {e1, e2, e3}; return app(3, args); }
inline expr app(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { expr args[4] = {e1, e2, e3, e4}; return app(4, args); }
inline expr app(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5) { expr args[5] = {e1, e2, e3, e4, e5}; return app(5, args); }
inline expr lambda(name const & n, expr const & t, expr const & e) { return expr(new expr_lambda(n, t, e)); }
inline expr lambda(char const * n, expr const & t, expr const & e) { return lambda(name(n), t, e); }
inline expr pi(name const & n, expr const & t, expr const & e) { return expr(new expr_pi(n, t, e)); }
inline expr pi(char const * n, expr const & t, expr const & e) { return pi(name(n), t, e); }
inline expr prop() { return expr(new expr_prop()); }
       expr type(unsigned size, uvar const * vars);
inline expr type(uvar const & uv) { return type(1, &uv); }
inline expr type(std::initializer_list<uvar> const & l) { return type(l.size(), l.begin()); }
inline expr numeral(mpz const & n) { return expr(new expr_numeral(n)); }
inline expr numeral(int n) { return numeral(mpz(n)); }

inline expr expr::operator()(expr const & a1) const { return app(*this, a1); }
inline expr expr::operator()(expr const & a1, expr const & a2) const { return app(*this, a1, a2); }
inline expr expr::operator()(expr const & a1, expr const & a2, expr const & a3) const { return app(*this, a1, a2, a3); }
inline expr expr::operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4) const { return app(*this, a1, a2, a3, a4); }
// =======================================

// =======================================
// Casting (these functions are only needed for low-level code)
inline expr_var *         to_var(expr_cell * e)         { lean_assert(is_var(e));         return static_cast<expr_var*>(e); }
inline expr_const *       to_constant(expr_cell * e)    { lean_assert(is_constant(e));    return static_cast<expr_const*>(e); }
inline expr_app *         to_app(expr_cell * e)         { lean_assert(is_app(e));         return static_cast<expr_app*>(e); }
inline expr_abstraction * to_abstraction(expr_cell * e) { lean_assert(is_abstraction(e)); return static_cast<expr_abstraction*>(e); }
inline expr_lambda *      to_lambda(expr_cell * e)      { lean_assert(is_lambda(e));      return static_cast<expr_lambda*>(e); }
inline expr_pi *          to_pi(expr_cell * e)          { lean_assert(is_pi(e));          return static_cast<expr_pi*>(e); }
inline expr_prop *        to_prop(expr_cell * e)        { lean_assert(is_prop(e));        return static_cast<expr_prop*>(e); }
inline expr_type *        to_type(expr_cell * e)        { lean_assert(is_type(e));        return static_cast<expr_type*>(e); }
inline expr_numeral *     to_numeral(expr_cell * e)     { lean_assert(is_numeral(e));     return static_cast<expr_numeral*>(e); }

inline expr_var *         to_var(expr const & e)         { return to_var(e.raw()); }
inline expr_const *       to_constant(expr const & e)    { return to_constant(e.raw()); }
inline expr_app *         to_app(expr const & e)         { return to_app(e.raw()); }
inline expr_abstraction * to_abstraction(expr const & e) { return to_abstraction(e.raw()); }
inline expr_lambda *      to_lambda(expr const & e)      { return to_lambda(e.raw()); }
inline expr_pi *          to_pi(expr const & e)          { return to_pi(e.raw()); }
inline expr_prop *        to_prop(expr const & e)        { return to_prop(e.raw()); }
inline expr_type *        to_type(expr const & e)        { return to_type(e.raw()); }
inline expr_numeral *     to_numeral(expr const & e)     { return to_numeral(e.raw()); }
// =======================================

// =======================================
// Accessors
inline unsigned     get_rc(expr_cell * e)               { return e->get_rc(); }
inline bool         is_shared(expr_cell * e)            { return get_rc(e) > 1; }
inline unsigned     var_idx(expr_cell * e)              { return to_var(e)->get_vidx(); }
inline name const & const_name(expr_cell * e)           { return to_constant(e)->get_name(); }
inline unsigned     const_pos(expr_cell * e)            { return to_constant(e)->get_pos(); }
inline unsigned     num_args(expr_cell * e)             { return to_app(e)->get_num_args(); }
inline expr const & arg(expr_cell * e, unsigned idx)    { return to_app(e)->get_arg(idx); }
inline name const & abst_name(expr_cell * e)            { return to_abstraction(e)->get_name(); }
inline expr const & abst_type(expr_cell * e)            { return to_abstraction(e)->get_type(); }
inline expr const & abst_body(expr_cell * e)            { return to_abstraction(e)->get_body(); }
inline unsigned     ty_num_vars(expr_cell * e)          { return to_type(e)->size(); }
inline uvar const & ty_var(expr_cell * e, unsigned idx) { return to_type(e)->get_var(idx); }
inline mpz const &  num_value(expr_cell * e)            { return to_numeral(e)->get_num(); }

inline unsigned     get_rc(expr const &  e)              { return e.raw()->get_rc(); }
inline bool         is_shared(expr const & e)            { return get_rc(e) > 1; }
inline unsigned     var_idx(expr const & e)              { return to_var(e)->get_vidx(); }
inline name const & const_name(expr const & e)           { return to_constant(e)->get_name(); }
inline unsigned     const_pos(expr const & e)            { return to_constant(e)->get_pos(); }
inline unsigned     num_args(expr const & e)             { return to_app(e)->get_num_args(); }
inline expr const & arg(expr const & e, unsigned idx)    { return to_app(e)->get_arg(idx); }
inline expr const * begin_args(expr const & e)           { return to_app(e)->begin_args(); }
inline expr const * end_args(expr const & e)             { return to_app(e)->end_args(); }
inline name const & abst_name(expr const & e)            { return to_abstraction(e)->get_name(); }
inline expr const & abst_type(expr const & e)            { return to_abstraction(e)->get_type(); }
inline expr const & abst_body(expr const & e)            { return to_abstraction(e)->get_body(); }
inline unsigned     ty_num_vars(expr const & e)          { return to_type(e)->size(); }
inline uvar const & ty_var(expr const & e, unsigned idx) { return to_type(e)->get_var(idx); }
inline uvar const * begin_ty_vars(expr const & e)        { return to_type(e)->get_vars(); }
inline uvar const * end_ty_vars(expr const & e)          { return begin_ty_vars(e) + ty_num_vars(e); }
inline mpz const &  num_value(expr const & e)            { return to_numeral(e)->get_num(); }
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
struct expr_hash { unsigned operator()(expr const & e) const { return e.hash(); } };
struct expr_eqp { bool operator()(expr const & e1, expr const & e2) const { return eqp(e1, e2); } };
struct expr_cell_hash { unsigned operator()(expr_cell * e) const { return e->hash(); } };
struct expr_cell_eqp { bool operator()(expr_cell * e1, expr_cell * e2) const { return e1 == e2; } };
struct expr_offset_hash { unsigned operator()(expr_offset const & p) const { return hash(p.first.hash(), p.second); } };
struct expr_offset_eqp { unsigned operator()(expr_offset const & p1, expr_offset const & p2) const { return eqp(p1.first, p2.first) && p1.second == p2.second; } };
struct expr_cell_offset_hash { unsigned operator()(expr_cell_offset const & p) const { return hash(p.first->hash(), p.second); } };
struct expr_cell_offset_eqp { unsigned operator()(expr_cell_offset const & p1, expr_cell_offset const & p2) const { return p1 == p2; } };
// =======================================

// =======================================
// Miscellaneous
std::ostream & operator<<(std::ostream & out, expr const & a);
/**
   \brief Wrapper for iterating over application arguments.
   If n is an application, it allows us to write
   for (expr const & arg : app_args(n)) {
   ... do something with argument
   }
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

}
