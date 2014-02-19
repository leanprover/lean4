/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <algorithm>
#include <iostream>
#include <limits>
#include <utility>
#include <tuple>
#include <string>
#include "util/thread.h"
#include "util/lua.h"
#include "util/rc.h"
#include "util/name.h"
#include "util/hash.h"
#include "util/buffer.h"
#include "util/list_fn.h"
#include "util/optional.h"
#include "util/serializer.h"
#include "util/sexpr/format.h"
#include "kernel/level.h"

namespace lean {
class expr;
typedef list<level> levels;
/* =======================================
   Expressions
   expr ::=   Var           idx
          |   Sort          level
          |   Constant      name [levels]
          |   Meta          name expr
          |   Local         name expr
          |   App           expr expr
          |   Pair          expr expr expr
          |   Fst           expr
          |   Snd           expr
          |   Lambda        name expr expr
          |   Pi            name expr expr
          |   Sigma         name expr expr
          |   Let           name expr expr expr

          |   Macro         macro
*/
enum class expr_kind { Var, Sort, Constant, Meta, Local, App, Pair, Fst, Snd, Lambda, Pi, Sigma, Let, Macro };
class expr_cell {
protected:
    unsigned short     m_kind;
    // The bits of the following field mean:
    //    0    - term is maximally shared
    //    1    - term is closed
    //    2    - term contains metavariables
    //    3-4  - term is an arrow (0 - not initialized, 1 - is arrow, 2 - is not arrow)
    atomic_ushort      m_flags;
    unsigned m_hash;       // hash based on the structure of the expression (this is a good hash for structural equality)
    unsigned m_hash_alloc; // hash based on 'time' of allocation (this is a good hash for pointer-based equality)
    MK_LEAN_RC(); // Declare m_rc counter
    void dealloc();

    bool max_shared() const { return (m_flags & 1) != 0; }
    void set_max_shared() { m_flags |= 1; }
    friend class max_sharing_fn;

    bool is_closed() const { return (m_flags & 2) != 0; }
    void set_closed() { m_flags |= 2; }

    optional<bool> is_arrow() const;
    void set_is_arrow(bool flag);
    friend bool is_arrow(expr const & e);

    friend class has_free_var_fn;
    static void dec_ref(expr & c, buffer<expr_cell*> & todelete);
public:
    expr_cell(expr_kind k, unsigned h, bool has_mv);
    expr_kind kind() const { return static_cast<expr_kind>(m_kind); }
    unsigned  hash() const { return m_hash; }
    unsigned  hash_alloc() const { return m_hash_alloc; }
    bool has_metavar() const { return (m_flags & 4) != 0; }
};

class macro;

/**
   \brief Exprs for encoding formulas/expressions, types and proofs.
*/
class expr {
private:
    expr_cell * m_ptr;
    explicit expr(expr_cell * ptr):m_ptr(ptr) { if (m_ptr) m_ptr->inc_ref(); }
    friend class expr_cell;
    expr_cell * steal_ptr() { expr_cell * r = m_ptr; m_ptr = nullptr; return r; }
    friend class optional<expr>;
public:
    /**
      \brief The default constructor creates a reference to a "dummy"
      expression.  The actual "dummy" expression is not relevant, and
      no procedure should rely on the kind of expression used.

      We have a default constructor because some collections only work
      with types that have a default constructor.
    */
    expr();
    expr(expr const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
    expr(expr && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
    ~expr() { if (m_ptr) m_ptr->dec_ref(); }

    friend void swap(expr & a, expr & b) { std::swap(a.m_ptr, b.m_ptr); }

    expr & operator=(expr const & s) { LEAN_COPY_REF(s); }
    expr & operator=(expr && s) { LEAN_MOVE_REF(s); }

    expr_kind kind() const { return m_ptr->kind(); }
    unsigned  hash() const { return m_ptr ? m_ptr->hash() : 23; }
    unsigned  hash_alloc() const { return m_ptr ? m_ptr->hash_alloc() : 23; }
    bool has_metavar() const { return m_ptr->has_metavar(); }

    expr_cell * raw() const { return m_ptr; }

    friend expr mk_var(unsigned idx);
    friend expr mk_sort(level const & l);
    friend expr mk_constant(name const & n, levels const & ls);
    friend expr mk_mlocal(bool is_meta, name const & n, expr const & t);
    friend expr mk_app(expr const & f, expr const & a);
    friend expr mk_pair(expr const & f, expr const & s, expr const & t);
    friend expr mk_proj(bool fst, expr const & p);
    friend expr mk_binder(expr_kind k, name const & n, expr const & t, expr const & e);
    friend expr mk_let(name const & n, expr const & t, expr const & v, expr const & e);
    friend expr mk_macro(macro * m);

    friend bool is_eqp(expr const & a, expr const & b) { return a.m_ptr == b.m_ptr; }
    // Overloaded operator() can be used to create applications
    expr operator()(expr const & a1) const;
    expr operator()(expr const & a1, expr const & a2) const;
    expr operator()(expr const & a1, expr const & a2, expr const & a3) const;
    expr operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4) const;
    expr operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4, expr const & a5) const;
    expr operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4, expr const & a5, expr const & a6) const;
    expr operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4, expr const & a5, expr const & a6,
                    expr const & a7) const;
    expr operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4, expr const & a5, expr const & a6,
                    expr const & a7, expr const & a8) const;
};

// =======================================
// Structural equality
       bool operator==(expr const & a, expr const & b);
inline bool operator!=(expr const & a, expr const & b) { return !operator==(a, b); }
// =======================================

SPECIALIZE_OPTIONAL_FOR_SMART_PTR(expr)

inline optional<expr> none_expr() { return optional<expr>(); }
inline optional<expr> some_expr(expr const & e) { return optional<expr>(e); }
inline optional<expr> some_expr(expr && e) { return optional<expr>(std::forward<expr>(e)); }

inline bool is_eqp(optional<expr> const & a, optional<expr> const & b) {
    return static_cast<bool>(a) == static_cast<bool>(b) && (!a || is_eqp(*a, *b));
}

/** \brief Bounded variables. They are encoded using de Bruijn's indices. */
class expr_var : public expr_cell {
    unsigned m_vidx; // de Bruijn index
public:
    expr_var(unsigned idx);
    unsigned get_vidx() const { return m_vidx; }
};

/** \brief (parametric) Constants. */
class expr_const : public expr_cell {
    name       m_name;
    levels     m_levels;
public:
    expr_const(name const & n, levels const & ls);
    name const & get_name() const { return m_name; }
    levels const & get_level_params() const { return m_levels; }
};

/** \brief Metavariables and local constants */
class expr_mlocal : public expr_cell {
    name   m_name;
    expr   m_type;
    friend expr_cell;
    void dealloc(buffer<expr_cell*> & todelete);
public:
    expr_mlocal(bool is_meta, name const & n, expr const & t);
    name const & get_name() const { return m_name; }
    expr const & get_type() const { return m_type; }
};

/** \brief Composite expressions */
class expr_composite : public expr_cell {
    unsigned m_depth;
    friend unsigned get_depth(expr const & e);
public:
    expr_composite(expr_kind k, unsigned h, bool has_mv, unsigned d);
};

/** \brief Applications */
class expr_app : public expr_composite {
    expr     m_fn;
    expr     m_arg;
    friend expr_cell;
    void dealloc(buffer<expr_cell*> & todelete);
public:
    expr_app(expr const & fn, expr const & arg);
    expr const & get_fn() const { return m_fn; }
    expr const & get_arg() const { return m_arg; }
};

/** \brief dependent pairs */
class expr_dep_pair : public expr_composite {
    expr     m_first;
    expr     m_second;
    expr     m_type;
    friend expr mk_pair(expr const & f, expr const & s, expr const & t);
    friend expr_cell;
    void dealloc(buffer<expr_cell*> & todelete);
public:
    expr_dep_pair(expr const & f, expr const & s, expr const & t);
    expr const & get_first() const { return m_first; }
    expr const & get_second() const { return m_second; }
    expr const & get_type() const { return m_type; }
};

/** \brief dependent pair projection */
class expr_proj : public expr_composite {
    expr     m_expr;
    friend expr_cell;
    friend expr mk_proj(unsigned idx, expr const & t);
    void dealloc(buffer<expr_cell*> & todelete);
public:
    expr_proj(bool first, expr const & e);
    expr const & get_arg() const { return m_expr; }
};

/** \brief Super class for lambda, pi and sigma */
class expr_binder : public expr_composite {
    name     m_name;
    expr     m_domain;
    expr     m_body;
    friend class expr_cell;
    void dealloc(buffer<expr_cell*> & todelete);
public:
    expr_binder(expr_kind k, name const & n, expr const & t, expr const & e);
    name const & get_name() const   { return m_name; }
    expr const & get_domain() const { return m_domain; }
    expr const & get_body() const   { return m_body; }
};

/** \brief Let expressions */
class expr_let : public expr_composite {
    name    m_name;
    expr    m_type;
    expr    m_value;
    expr    m_body;
    friend class expr_cell;
    void dealloc(buffer<expr_cell*> & todelete);
public:
    expr_let(name const & n, expr const & t, expr const & v, expr const & b);
    ~expr_let();
    name const & get_name() const   { return m_name; }
    expr const & get_type() const   { return m_type; }
    expr const & get_value() const  { return m_value; }
    expr const & get_body() const   { return m_body; }
};

/** \brief Sort */
class expr_sort : public expr_cell {
    level    m_level;
public:
    expr_sort(level const & l);
    ~expr_sort();
    level const & get_level() const { return m_level; }
};

class formatter;

/** \brief Base class for macro attachments */
class macro {
    void dealloc() { delete this; }
    MK_LEAN_RC();
protected:
    /**
        \brief Auxiliary method used for implementing a total order on macro
        attachments. It is invoked by operator<, and it is only invoked when
        <tt>get_name() == other.get_name()</tt>
    */
    virtual bool lt(macro const &) const { return false; }
public:
    macro():m_rc(0) {}
    virtual ~macro() {}
    virtual name get_name() const = 0;
    virtual expr get_type(buffer<expr> const & arg_types) const = 0;
    virtual expr expand1(buffer<expr> const & args) const = 0;
    virtual expr expand(buffer<expr> const & args) const = 0;
    virtual int push_lua(lua_State * L) const;
    virtual bool operator==(macro const & other) const;
    bool operator<(macro const & other) const;
    virtual void display(std::ostream & out) const;
    virtual format pp(formatter const & fmt, options const & opts) const;
    virtual bool is_atomic_pp(bool unicode, bool coercion) const;
    virtual unsigned hash() const;
    virtual void write(serializer & s) const = 0;
    typedef std::function<expr(deserializer&)> reader;
    static void register_deserializer(std::string const & k, reader rd);
    struct register_deserializer_fn {
        register_deserializer_fn(std::string const & k, macro::reader rd) { macro::register_deserializer(k, rd); }
    };
};

/** \brief Macro attachments */
class expr_macro : public expr_cell {
    macro * m_macro;
    friend expr copy(expr const & a);
public:
    expr_macro(macro * v);
    ~expr_macro();

    macro const & get_macro() const { return *m_macro; }
};

// =======================================
// Testers
inline bool is_var(expr_cell * e)         { return e->kind() == expr_kind::Var; }
inline bool is_constant(expr_cell * e)    { return e->kind() == expr_kind::Constant; }
inline bool is_local(expr_cell * e)       { return e->kind() == expr_kind::Local; }
inline bool is_metavar(expr_cell * e)     { return e->kind() == expr_kind::Meta; }
inline bool is_macro(expr_cell * e)       { return e->kind() == expr_kind::Macro; }
inline bool is_dep_pair(expr_cell * e)    { return e->kind() == expr_kind::Pair; }
inline bool is_fst(expr_cell * e)         { return e->kind() == expr_kind::Fst; }
inline bool is_snd(expr_cell * e)         { return e->kind() == expr_kind::Snd; }
inline bool is_app(expr_cell * e)         { return e->kind() == expr_kind::App; }
inline bool is_lambda(expr_cell * e)      { return e->kind() == expr_kind::Lambda; }
inline bool is_pi(expr_cell * e)          { return e->kind() == expr_kind::Pi; }
inline bool is_sigma(expr_cell * e)       { return e->kind() == expr_kind::Sigma; }
inline bool is_sort(expr_cell * e)        { return e->kind() == expr_kind::Sort; }
inline bool is_let(expr_cell * e)         { return e->kind() == expr_kind::Let; }
inline bool is_binder(expr_cell * e)      { return is_lambda(e) || is_pi(e) || is_sigma(e); }
inline bool is_proj(expr_cell * e)        { return is_fst(e) || is_snd(e); }
inline bool is_mlocal(expr_cell * e)      { return is_metavar(e) || is_local(e); }

inline bool is_var(expr const & e)        { return e.kind() == expr_kind::Var; }
inline bool is_constant(expr const & e)   { return e.kind() == expr_kind::Constant; }
inline bool is_local(expr const & e)      { return e.kind() == expr_kind::Local; }
inline bool is_metavar(expr const & e)    { return e.kind() == expr_kind::Meta; }
inline bool is_macro(expr const & e)      { return e.kind() == expr_kind::Macro; }
inline bool is_dep_pair(expr const & e)   { return e.kind() == expr_kind::Pair; }
inline bool is_fst(expr const & e)        { return e.kind() == expr_kind::Fst; }
inline bool is_snd(expr const & e)        { return e.kind() == expr_kind::Snd; }
inline bool is_app(expr const & e)        { return e.kind() == expr_kind::App; }
inline bool is_lambda(expr const & e)     { return e.kind() == expr_kind::Lambda; }
inline bool is_pi(expr const & e)         { return e.kind() == expr_kind::Pi; }
inline bool is_sigma(expr const & e)      { return e.kind() == expr_kind::Sigma; }
inline bool is_sort(expr const & e)       { return e.kind() == expr_kind::Sort; }
inline bool is_let(expr const & e)        { return e.kind() == expr_kind::Let; }
inline bool is_binder(expr const & e)     { return is_lambda(e) || is_pi(e) || is_sigma(e); }
inline bool is_proj(expr const & e)       { return is_fst(e) || is_snd(e); }
inline bool is_mlocal(expr const & e)     { return is_metavar(e) || is_local(e); }

bool is_atomic(expr const & e);
bool is_arrow(expr const & t);
bool is_cartesian(expr const & t);
// =======================================

// =======================================
// Constructors
inline expr mk_var(unsigned idx) { return expr(new expr_var(idx)); }
inline expr Var(unsigned idx) { return mk_var(idx); }
inline expr mk_constant(name const & n, levels const & ls) { return expr(new expr_const(n, ls)); }
inline expr mk_constant(name const & n) { return mk_constant(n, levels()); }
inline expr Const(name const & n) { return mk_constant(n); }
inline expr mk_macro(macro * m) { return expr(new expr_macro(m)); }
inline expr mk_mlocal(bool is_meta, name const & n, expr const & t) { return expr(new expr_mlocal(is_meta, n, t)); }
inline expr mk_metavar(name const & n, expr const & t) { return mk_mlocal(true, n, t); }
inline expr mk_local(name const & n, expr const & t) { return mk_mlocal(false, n, t); }
inline expr mk_pair(expr const & f, expr const & s, expr const & t) { return expr(new expr_dep_pair(f, s, t)); }
inline expr mk_proj(bool first, expr const & a) { return expr(new expr_proj(first, a)); }
inline expr mk_fst(expr const & a) { return mk_proj(true, a); }
inline expr mk_snd(expr const & a) { return mk_proj(false, a); }
inline expr mk_app(expr const & f, expr const & a) { return expr(new expr_app(f, a)); }
       expr mk_app(unsigned num_args, expr const * args);
inline expr mk_app(std::initializer_list<expr> const & l) { return mk_app(l.size(), l.begin()); }
template<typename T> expr mk_app(T const & args) { return mk_app(args.size(), args.data()); }
inline expr mk_binder(expr_kind k, name const & n, expr const & t, expr const & e) { return expr(new expr_binder(k, n, t, e)); }
inline expr mk_lambda(name const & n, expr const & t, expr const & e) { return mk_binder(expr_kind::Lambda, n, t, e); }
inline expr mk_pi(name const & n, expr const & t, expr const & e) { return mk_binder(expr_kind::Pi, n, t, e); }
inline expr mk_sigma(name const & n, expr const & t, expr const & e) { return mk_binder(expr_kind::Sigma, n, t, e); }
inline expr mk_let(name const & n, expr const & t, expr const & v, expr const & e) { return expr(new expr_let(n, t, v, e)); }
inline expr mk_sort(level const & l) { return expr(new expr_sort(l)); }

expr mk_Bool();
expr mk_Type();
extern expr Type;
extern expr Bool;

bool is_default_var_name(name const & n);
expr mk_arrow(expr const & t, expr const & e);
expr mk_cartesian_product(expr const & t, expr const & e);
inline expr operator>>(expr const & t, expr const & e) { return mk_arrow(t, e); }

// Auxiliary
inline expr mk_app(expr const & e1, expr const & e2, expr const & e3) { return mk_app({e1, e2, e3}); }
inline expr mk_app(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({e1, e2, e3, e4}); }
inline expr mk_app(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5) {
    return mk_app({e1, e2, e3, e4, e5});
}
inline expr expr::operator()(expr const & a1) const { return mk_app({*this, a1}); }
inline expr expr::operator()(expr const & a1, expr const & a2) const { return mk_app({*this, a1, a2}); }
inline expr expr::operator()(expr const & a1, expr const & a2, expr const & a3) const { return mk_app({*this, a1, a2, a3}); }
inline expr expr::operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4) const {
    return mk_app({*this, a1, a2, a3, a4});
}
inline expr expr::operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4, expr const & a5) const {
    return mk_app({*this, a1, a2, a3, a4, a5});
}
inline expr expr::operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4, expr const & a5,
                             expr const & a6) const {
    return mk_app({*this, a1, a2, a3, a4, a5, a6});
}
inline expr expr::operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4, expr const & a5,
                             expr const & a6, expr const & a7) const {
    return mk_app({*this, a1, a2, a3, a4, a5, a6, a7});
}
inline expr expr::operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4, expr const & a5,
                             expr const & a6, expr const & a7, expr const & a8) const {
    return mk_app({*this, a1, a2, a3, a4, a5, a6, a7, a8});
}
// =======================================

// =======================================
// Casting (these functions are only needed for low-level code)
inline expr_var *         to_var(expr_cell * e)        { lean_assert(is_var(e));         return static_cast<expr_var*>(e); }
inline expr_const *       to_constant(expr_cell * e)   { lean_assert(is_constant(e));    return static_cast<expr_const*>(e); }
inline expr_dep_pair *    to_pair(expr_cell * e)       { lean_assert(is_dep_pair(e));    return static_cast<expr_dep_pair*>(e); }
inline expr_proj *        to_proj(expr_cell * e)       { lean_assert(is_proj(e));        return static_cast<expr_proj*>(e); }
inline expr_app *         to_app(expr_cell * e)        { lean_assert(is_app(e));         return static_cast<expr_app*>(e); }
inline expr_binder *      to_binder(expr_cell * e)     { lean_assert(is_binder(e));      return static_cast<expr_binder*>(e); }
inline expr_let *         to_let(expr_cell * e)        { lean_assert(is_let(e));         return static_cast<expr_let*>(e); }
inline expr_sort *        to_sort(expr_cell * e)       { lean_assert(is_sort(e));        return static_cast<expr_sort*>(e); }
inline expr_mlocal *      to_mlocal(expr_cell * e)     { lean_assert(is_mlocal(e));      return static_cast<expr_mlocal*>(e); }
inline expr_mlocal *      to_local(expr_cell * e)      { lean_assert(is_local(e));       return static_cast<expr_mlocal*>(e); }
inline expr_mlocal *      to_metavar(expr_cell * e)    { lean_assert(is_metavar(e));     return static_cast<expr_mlocal*>(e); }

inline expr_var *         to_var(expr const & e)         { return to_var(e.raw()); }
inline expr_const *       to_constant(expr const & e)    { return to_constant(e.raw()); }
inline expr_dep_pair *    to_pair(expr const & e)        { return to_pair(e.raw()); }
inline expr_proj *        to_proj(expr const & e)        { return to_proj(e.raw()); }
inline expr_app *         to_app(expr const & e)         { return to_app(e.raw()); }
inline expr_binder *      to_binder(expr const & e)      { return to_binder(e.raw()); }
inline expr_let *         to_let(expr const & e)         { return to_let(e.raw()); }
inline expr_sort *        to_sort(expr const & e)        { return to_sort(e.raw()); }
inline expr_mlocal *      to_mlocal(expr const & e)      { return to_mlocal(e.raw()); }
inline expr_mlocal *      to_metavar(expr const & e)     { return to_metavar(e.raw()); }
inline expr_mlocal *      to_local(expr const & e)       { return to_local(e.raw()); }
// =======================================


// =======================================
// Accessors
inline unsigned       get_rc(expr_cell * e)               { return e->get_rc(); }
inline bool           is_shared(expr_cell * e)            { return get_rc(e) > 1; }
inline unsigned       var_idx(expr_cell * e)              { return to_var(e)->get_vidx(); }
inline bool           is_var(expr_cell * e, unsigned i)   { return is_var(e) && var_idx(e) == i; }
inline name const &   const_name(expr_cell * e)           { return to_constant(e)->get_name(); }
inline levels const & const_level_params(expr_cell * e)   { return to_constant(e)->get_level_params(); }
inline expr const &   pair_first(expr_cell * e)           { return to_pair(e)->get_first(); }
inline expr const &   pair_second(expr_cell * e)          { return to_pair(e)->get_second(); }
inline expr const &   pair_type(expr_cell * e)            { return to_pair(e)->get_type(); }
inline expr const &   proj_arg(expr_cell * e)             { return to_proj(e)->get_arg(); }
inline macro const &  to_macro(expr_cell * e)             {
    lean_assert(is_macro(e)); return static_cast<expr_macro*>(e)->get_macro(); }
inline expr const &   app_fn(expr_cell * e)               { return to_app(e)->get_fn(); }
inline expr const &   app_arg(expr_cell * e)              { return to_app(e)->get_arg(); }
inline name const &   binder_name(expr_cell * e)          { return to_binder(e)->get_name(); }
inline expr const &   binder_domain(expr_cell * e)        { return to_binder(e)->get_domain(); }
inline expr const &   binder_body(expr_cell * e)          { return to_binder(e)->get_body(); }
inline level const &  sort_level(expr_cell * e)           { return to_sort(e)->get_level(); }
inline name const &   let_name(expr_cell * e)             { return to_let(e)->get_name(); }
inline expr const &   let_value(expr_cell * e)            { return to_let(e)->get_value(); }
inline expr const &   let_type(expr_cell * e)             { return to_let(e)->get_type(); }
inline expr const &   let_body(expr_cell * e)             { return to_let(e)->get_body(); }
inline name const &   mlocal_name(expr_cell * e)          { return to_mlocal(e)->get_name(); }
inline expr const &   mlocal_type(expr_cell * e)          { return to_mlocal(e)->get_type(); }

inline unsigned       get_rc(expr const & e)               { return e.raw()->get_rc(); }
inline bool           is_shared(expr const & e)            { return get_rc(e) > 1; }
inline unsigned       var_idx(expr const & e)              { return to_var(e)->get_vidx(); }
inline bool           is_var(expr const & e, unsigned i)   { return is_var(e) && var_idx(e) == i; }
inline name const &   const_name(expr const & e)           { return to_constant(e)->get_name(); }
inline levels const & const_level_params(expr const & e)   { return to_constant(e)->get_level_params(); }
inline expr const &   pair_first(expr const & e)           { return to_pair(e)->get_first(); }
inline expr const &   pair_second(expr const & e)          { return to_pair(e)->get_second(); }
inline expr const &   pair_type(expr const & e)            { return to_pair(e)->get_type(); }
inline expr const &   proj_arg(expr const & e)             { return to_proj(e)->get_arg(); }
inline macro const &  to_macro(expr const & e)             { return to_macro(e.raw()); }
inline expr const &   app_fn(expr const & e)               { return to_app(e)->get_fn(); }
inline expr const &   app_arg(expr const & e)              { return to_app(e)->get_arg(); }
inline name const &   binder_name(expr const & e)          { return to_binder(e)->get_name(); }
inline expr const &   binder_domain(expr const & e)        { return to_binder(e)->get_domain(); }
inline expr const &   binder_body(expr const & e)          { return to_binder(e)->get_body(); }
inline level const &  sort_level(expr const & e)           { return to_sort(e)->get_level(); }
inline name const &   let_name(expr const & e)             { return to_let(e)->get_name(); }
inline expr const &   let_value(expr const & e)            { return to_let(e)->get_value(); }
inline expr const &   let_type(expr const & e)             { return to_let(e)->get_type(); }
inline expr const &   let_body(expr const & e)             { return to_let(e)->get_body(); }
inline name const &   mlocal_name(expr const & e)          { return to_mlocal(e)->get_name(); }
inline expr const &   mlocal_type(expr const & e)          { return to_mlocal(e)->get_type(); }

inline bool is_constant(expr const & e, name const & n) { return is_constant(e) && const_name(e) == n; }
inline bool has_metavar(expr const & e) { return e.has_metavar(); }
unsigned get_depth(expr const & e);
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
/**
    \brief Functional object for hashing (based on allocation time) kernel expressions.

    This hash is compatible with pointer equality.
    \warning This hash is incompatible with structural equality (i.e., std::equal_to<expr>)
*/
struct expr_hash_alloc { unsigned operator()(expr const & e) const { return e.hash_alloc(); } };
/** \brief Functional object for testing pointer equality between kernel expressions. */
struct expr_eqp { bool operator()(expr const & e1, expr const & e2) const { return is_eqp(e1, e2); } };
/** \brief Functional object for hashing kernel expression cells. */
struct expr_cell_hash { unsigned operator()(expr_cell * e) const { return e->hash_alloc(); } };
/** \brief Functional object for testing pointer equality between kernel cell expressions. */
struct expr_cell_eqp { bool operator()(expr_cell * e1, expr_cell * e2) const { return e1 == e2; } };
/** \brief Functional object for hashing a pair (n, k) where n is a kernel expressions, and k is an offset. */
struct expr_offset_hash { unsigned operator()(expr_offset const & p) const { return hash(p.first.hash_alloc(), p.second); } };
/** \brief Functional object for comparing pairs (expression, offset). */
struct expr_offset_eqp { unsigned operator()(expr_offset const & p1, expr_offset const & p2) const { return is_eqp(p1.first, p2.first) && p1.second == p2.second; } };
/** \brief Functional object for hashing a pair (n, k) where n is a kernel cell expressions, and k is an offset. */
struct expr_cell_offset_hash { unsigned operator()(expr_cell_offset const & p) const { return hash(p.first->hash_alloc(), p.second); } };
/** \brief Functional object for comparing pairs (expression cell, offset). */
struct expr_cell_offset_eqp { unsigned operator()(expr_cell_offset const & p1, expr_cell_offset const & p2) const { return p1 == p2; } };
// =======================================

/**
   \brief Return a shallow copy of \c e
*/
expr copy(expr const & e);

// =======================================
// Update
expr update_app(expr const & e, expr const & new_fn, expr const & new_arg);
expr update_proj(expr const & e, expr const & new_arg);
expr update_pair(expr const & e, expr const & new_first, expr const & new_second, expr const & new_type);
expr update_binder(expr const & e, expr const & new_domain, expr const & new_body);
expr update_let(expr const & e, expr const & new_type, expr const & new_val, expr const & new_body);
expr update_mlocal(expr const & e, expr const & new_type);
// =======================================

// =======================================
// Serializer/Deserializer
serializer & operator<<(serializer & s, expr const & e);
expr read_expr(deserializer & d);
inline deserializer & operator>>(deserializer & d, expr & e) { e = read_expr(d); return d; }
// =======================================

std::ostream & operator<<(std::ostream & out, expr const & e);
}
