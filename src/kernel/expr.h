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
class value;
/* =======================================
   Expressions
   expr ::=   Var           idx
          |   Constant      name
          |   Value         value
          |   App           [expr]
          |   Pair          expr expr expr
          |   Proj          bool expr         The Boolean flag indicates whether is the first/second projection
          |   Lambda        name expr expr
          |   Pi            name expr expr
          |   Sigma         name expr expr
          |   Type          universe
          |   Let           name expr expr expr
          |   Metavar       name local_context

   local_context ::= [local_entry]

   local_entry ::=  lift  idx idx
                 |  inst  idx expr

TODO(Leo): match expressions.

The main API is divided in the following sections
- Testers
- Constructors
- Accessors
- Miscellaneous
======================================= */
class expr;
enum class expr_kind { Value, Var, Constant, App, Pair, Proj, Lambda, Pi, Sigma, Type, Let, MetaVar };
class local_entry;
/**
   \brief A metavariable local context is just a list of local_entries.
   \see local_entry
*/
typedef list<local_entry> local_context;

/**
    \brief Base class used to represent expressions.

    In principle, the expr_cell class and subclasses should be located in the .cpp file.
    However, this is performance critical code, and we want to be able to have
    inline definitions.
*/
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
    static void dec_ref(optional<expr> & c, buffer<expr_cell*> & todelete);
public:
    expr_cell(expr_kind k, unsigned h, bool has_mv);
    expr_kind kind() const { return static_cast<expr_kind>(m_kind); }
    unsigned  hash() const { return m_hash; }
    unsigned  hash_alloc() const { return m_hash_alloc; }
    bool has_metavar() const { return (m_flags & 4) != 0; }
};
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
    friend expr mk_constant(name const & n, optional<expr> const & t);
    friend expr mk_value(value & v);
    friend expr mk_pair(expr const & f, expr const & s, expr const & t);
    friend expr mk_proj(bool f, expr const & t);
    friend expr mk_app(unsigned num_args, expr const * args);
    friend expr mk_lambda(name const & n, expr const & t, expr const & e);
    friend expr mk_pi(name const & n, expr const & t, expr const & e);
    friend expr mk_sigma(name const & n, expr const & t, expr const & e);
    friend expr mk_type(level const & l);
    friend expr mk_let(name const & n, optional<expr> const & t, expr const & v, expr const & e);
    friend expr mk_metavar(name const & n, local_context const & ctx);

    friend bool is_eqp(expr const & a, expr const & b) { return a.m_ptr == b.m_ptr; }
    // Overloaded operator() can be used to create applications
    expr operator()(expr const & a1) const;
    expr operator()(expr const & a1, expr const & a2) const;
    expr operator()(expr const & a1, expr const & a2, expr const & a3) const;
    expr operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4) const;
    expr operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4, expr const & a5) const;
    expr operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4, expr const & a5, expr const & a6) const;
    expr operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4, expr const & a5, expr const & a6, expr const & a7) const;
    expr operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4, expr const & a5, expr const & a6, expr const & a7, expr const & a8) const;
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
    name           m_name;
    optional<expr> m_type;
    // Remark: we do *not* perform destructive updates on m_type
    // This field is used to efficiently implement the tactic framework
    friend class expr_cell;
    void dealloc(buffer<expr_cell*> & to_delete);
public:
    expr_const(name const & n, optional<expr> const & type);
    name const & get_name() const { return m_name; }
    optional<expr> const & get_type() const { return m_type; }
};
/** \brief Function Applications */
class expr_app : public expr_cell {
    unsigned m_depth;
    unsigned m_num_args;
    expr     m_args[0];
    friend expr mk_app(unsigned num_args, expr const * args);
    friend expr_cell;
    void dealloc(buffer<expr_cell*> & todelete);
    friend unsigned get_depth(expr const & e);
public:
    expr_app(unsigned size, bool has_mv);
    unsigned     get_num_args() const        { return m_num_args; }
    expr const & get_arg(unsigned idx) const { lean_assert(idx < m_num_args); return m_args[idx]; }
    expr const * begin_args() const          { return m_args; }
    expr const * end_args() const            { return m_args + m_num_args; }
};
/** \brief dependent pairs */
class expr_dep_pair : public expr_cell {
    expr     m_first;
    expr     m_second;
    expr     m_type;
    unsigned m_depth;
    friend expr_cell;
    friend expr mk_pair(expr const & f, expr const & s, expr const & t);
    void dealloc(buffer<expr_cell*> & todelete);
    friend unsigned get_depth(expr const & e);
public:
    expr_dep_pair(expr const & f, expr const & s, expr const & t);
    expr const & get_first() const { return m_first; }
    expr const & get_second() const { return m_second; }
    expr const & get_type() const { return m_type; }
};
/** \brief dependent pair projection */
class expr_proj : public expr_cell {
    bool     m_first;   // first/second projection
    unsigned m_depth;
    expr     m_expr;
    friend expr_cell;
    friend expr mk_proj(unsigned idx, expr const & t);
    void dealloc(buffer<expr_cell*> & todelete);
    friend unsigned get_depth(expr const & e);
public:
    expr_proj(bool first, expr const & e);
    bool first() const { return m_first; }
    bool second() const { return !m_first; }
    expr const & get_arg() const { return m_expr; }
};
/** \brief Super class for lambda abstraction and pi (functional spaces). */
class expr_abstraction : public expr_cell {
    unsigned m_depth;
    name     m_name;
    expr     m_domain;
    expr     m_body;
    friend class expr_cell;
    void dealloc(buffer<expr_cell*> & todelete);
    friend unsigned get_depth(expr const & e);
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
/** \brief Sigma types (aka the type of dependent pairs) */
class expr_sigma : public expr_abstraction {
public:
    expr_sigma(name const & n, expr const & t, expr const & e);
};
/** \brief Let expressions */
class expr_let : public expr_cell {
    unsigned       m_depth;
    name           m_name;
    optional<expr> m_type;
    expr           m_value;
    expr           m_body;
    friend class expr_cell;
    void dealloc(buffer<expr_cell*> & todelete);
    friend unsigned get_depth(expr const & e);
public:
    expr_let(name const & n, optional<expr> const & t, expr const & v, expr const & b);
    ~expr_let();
    name const & get_name() const           { return m_name; }
    optional<expr> const & get_type() const { return m_type; }
    expr const & get_value() const          { return m_value; }
    expr const & get_body() const           { return m_body; }
};
/** \brief Type */
class expr_type : public expr_cell {
    level    m_level;
public:
    expr_type(level const & l);
    ~expr_type();
    level const & get_level() const { return m_level; }
};
/** \brief Base class for semantic attachment cells. */
class value {
    void dealloc() { delete this; }
    MK_LEAN_RC();
protected:
    /**
        \brief Auxiliary method used for implementing a total order on semantic
        attachments. It is invoked by operator<, and it is only invoked when
        <tt>get_name() == other.get_name()</tt>
    */
    virtual bool lt(value const &) const { return false; }
public:
    value():m_rc(0) {}
    virtual ~value() {}
    virtual expr get_type() const = 0;
    virtual name get_name() const = 0;
    virtual name get_unicode_name() const;
    virtual optional<expr> normalize(unsigned num_args, expr const * args) const;
    virtual bool operator==(value const & other) const;
    bool operator<(value const & other) const;
    virtual void display(std::ostream & out) const;
    virtual format pp() const;
    virtual format pp(bool unicode, bool coercion) const;
    virtual int push_lua(lua_State * L) const;
    virtual unsigned hash() const;
    virtual void write(serializer & s) const = 0;
    typedef std::function<expr(deserializer&)> reader;
    static void register_deserializer(std::string const & k, reader rd);
    struct register_deserializer_fn {
        register_deserializer_fn(std::string const & k, value::reader rd) { value::register_deserializer(k, rd); }
    };
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
/**
   \see local_entry
*/
enum class local_entry_kind { Lift, Inst };
/**
    \brief An entry in a metavariable context.
    It represents objects of the form:
    <code>
           | Lift s n
           | Inst s v
    </code>
    where \c s and \c n are unsigned integers, and
    \c v is an expression

    The meaning of <tt>Lift s n</tt> is: lift the free variables greater than or equal to \c s by \c n.
    The meaning of <tt>Inst s v</tt> is: instantiate free variable \c s with the expression \c v, and
                                         lower free variables greater than \c s.

    The metavariable context records operations that must be applied
    whenever we substitute a metavariable with an actual expression.
    For example, let ?M be a metavariable with context
    <code>
       [ Inst 0 a, Lift 1 2 ]
    </code>
    Now, assume we want to instantiate \c ?M with <tt>f #0 (g #2)</tt>.
    Then, we apply the metavariable entries from right to left.
    Thus, first we apply <tt>(Lift 1 2)</tt> and obtain the term
    <code>
       f #0 (g #4)
    </code>
    Then, we apply <tt>(Inst 0 a)</tt> and produce
    <code>
       f a (g #3)
    </code>
*/
class local_entry {
    local_entry_kind m_kind;
    unsigned         m_s;
    unsigned         m_n;
    optional<expr>   m_v;
    local_entry(unsigned s, unsigned n);
    local_entry(unsigned s, expr const & v);
public:
    ~local_entry();
    friend local_entry mk_lift(unsigned s, unsigned n);
    friend local_entry mk_inst(unsigned s, expr const & v);
    local_entry_kind kind() const { return m_kind; }
    bool is_inst() const { return kind() == local_entry_kind::Inst; }
    bool is_lift() const { return kind() == local_entry_kind::Lift; }
    unsigned s() const { return m_s; }
    unsigned n() const { lean_assert(is_lift()); return m_n; }
    bool operator==(local_entry const & e) const;
    bool operator!=(local_entry const & e) const { return !operator==(e); }
    expr const & v() const { lean_assert(is_inst()); return *m_v; }
};
inline local_entry mk_lift(unsigned s, unsigned n) { return local_entry(s, n); }
inline local_entry mk_inst(unsigned s, expr const & v) { return local_entry(s, v); }

/** \brief Metavariables */
class expr_metavar : public expr_cell {
    name          m_name;
    local_context m_lctx;
public:
    expr_metavar(name const & n, local_context const & lctx);
    ~expr_metavar();
    name const & get_name() const { return m_name; }
    local_context const & get_lctx() const { return m_lctx; }
};
// =======================================

// =======================================
// Testers
inline bool is_var(expr_cell * e)         { return e->kind() == expr_kind::Var; }
inline bool is_constant(expr_cell * e)    { return e->kind() == expr_kind::Constant; }
inline bool is_value(expr_cell * e)       { return e->kind() == expr_kind::Value; }
inline bool is_pair(expr_cell * e)        { return e->kind() == expr_kind::Pair; }
inline bool is_proj(expr_cell * e)        { return e->kind() == expr_kind::Proj; }
inline bool is_app(expr_cell * e)         { return e->kind() == expr_kind::App; }
inline bool is_lambda(expr_cell * e)      { return e->kind() == expr_kind::Lambda; }
inline bool is_pi(expr_cell * e)          { return e->kind() == expr_kind::Pi; }
inline bool is_sigma(expr_cell * e)       { return e->kind() == expr_kind::Sigma; }
inline bool is_type(expr_cell * e)        { return e->kind() == expr_kind::Type; }
inline bool is_let(expr_cell * e)         { return e->kind() == expr_kind::Let; }
inline bool is_metavar(expr_cell * e)     { return e->kind() == expr_kind::MetaVar; }
inline bool is_abstraction(expr_cell * e) { return is_lambda(e) || is_pi(e) || is_sigma(e); }

inline bool is_var(expr const & e)         { return e.kind() == expr_kind::Var; }
inline bool is_constant(expr const & e)    { return e.kind() == expr_kind::Constant; }
inline bool is_value(expr const & e)       { return e.kind() == expr_kind::Value; }
inline bool is_pair(expr const & e)        { return e.kind() == expr_kind::Pair; }
inline bool is_proj(expr const & e)        { return e.kind() == expr_kind::Proj; }
inline bool is_app(expr const & e)         { return e.kind() == expr_kind::App; }
inline bool is_lambda(expr const & e)      { return e.kind() == expr_kind::Lambda; }
inline bool is_pi(expr const & e)          { return e.kind() == expr_kind::Pi; }
       bool is_arrow(expr const & e);
       bool is_cartesian(expr const & e);
inline bool is_sigma(expr const & e)       { return e.kind() == expr_kind::Sigma; }
inline bool is_type(expr const & e)        { return e.kind() == expr_kind::Type; }
inline bool is_let(expr const & e)         { return e.kind() == expr_kind::Let; }
inline bool is_metavar(expr const & e)     { return e.kind() == expr_kind::MetaVar; }
inline bool is_abstraction(expr const & e) { return is_lambda(e) || is_pi(e) || is_sigma(e); }
// =======================================

// =======================================
// Constructors
inline expr mk_var(unsigned idx) { return expr(new expr_var(idx)); }
inline expr Var(unsigned idx) { return mk_var(idx); }
inline expr mk_constant(name const & n, optional<expr> const & t) { return expr(new expr_const(n, t)); }
inline expr mk_constant(name const & n, expr const & t) { return mk_constant(n, some_expr(t)); }
inline expr mk_constant(name const & n) { return mk_constant(n, none_expr()); }
inline expr Const(name const & n) { return mk_constant(n); }
inline expr mk_value(value & v) { return expr(new expr_value(v)); }
inline expr to_expr(value & v) { return mk_value(v); }
inline expr mk_pair(expr const & f, expr const & s, expr const & t) { return expr(new expr_dep_pair(f, s, t)); }
inline expr mk_proj(bool f, expr const & e) { return expr(new expr_proj(f, e)); }
inline expr mk_proj1(expr const & e) { return mk_proj(true, e); }
inline expr mk_proj2(expr const & e) { return mk_proj(false, e); }
       expr mk_app(unsigned num_args, expr const * args);
inline expr mk_app(std::initializer_list<expr> const & l) { return mk_app(l.size(), l.begin()); }
template<typename T> expr mk_app(T const & args) { return mk_app(args.size(), args.data()); }
inline expr mk_app(expr const & e1, expr const & e2) { return mk_app({e1, e2}); }
inline expr mk_app(expr const & e1, expr const & e2, expr const & e3) { return mk_app({e1, e2, e3}); }
inline expr mk_app(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({e1, e2, e3, e4}); }
inline expr mk_app(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5) { return mk_app({e1, e2, e3, e4, e5}); }
inline expr mk_lambda(name const & n, expr const & t, expr const & e) { return expr(new expr_lambda(n, t, e)); }
inline expr mk_pi(name const & n, expr const & t, expr const & e) { return expr(new expr_pi(n, t, e)); }
inline expr mk_sigma(name const & n, expr const & t, expr const & e) { return expr(new expr_sigma(n, t, e)); }
inline bool is_default_arrow_var_name(name const & n) { return n == "a"; }
inline expr mk_arrow(expr const & t, expr const & e) { return mk_pi(name("a"), t, e); }
inline expr mk_cartesian_product(expr const & t, expr const & e) { return mk_sigma(name("a"), t, e); }
inline expr operator>>(expr const & t, expr const & e) { return mk_arrow(t, e); }
inline expr mk_let(name const & n, optional<expr> const & t, expr const & v, expr const & e) { return expr(new expr_let(n, t, v, e)); }
inline expr mk_let(name const & n, expr const & t, expr const & v, expr const & e) { return mk_let(n, some_expr(t), v, e); }
inline expr mk_let(name const & n, expr const & v, expr const & e) { return mk_let(n, none_expr(), v, e); }
inline expr mk_type(level const & l) { return expr(new expr_type(l)); }
       expr mk_type();
inline expr Type(level const & l) { return mk_type(l); }
inline expr Type() { return mk_type(); }
inline expr mk_metavar(name const & n, local_context const & ctx = local_context()) {
    return expr(new expr_metavar(n, ctx));
}

inline expr expr::operator()(expr const & a1) const { return mk_app({*this, a1}); }
inline expr expr::operator()(expr const & a1, expr const & a2) const { return mk_app({*this, a1, a2}); }
inline expr expr::operator()(expr const & a1, expr const & a2, expr const & a3) const { return mk_app({*this, a1, a2, a3}); }
inline expr expr::operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4) const { return mk_app({*this, a1, a2, a3, a4}); }
inline expr expr::operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4, expr const & a5) const { return mk_app({*this, a1, a2, a3, a4, a5}); }
inline expr expr::operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4, expr const & a5, expr const & a6) const { return mk_app({*this, a1, a2, a3, a4, a5, a6}); }
inline expr expr::operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4, expr const & a5, expr const & a6, expr const & a7) const { return mk_app({*this, a1, a2, a3, a4, a5, a6, a7}); }
inline expr expr::operator()(expr const & a1, expr const & a2, expr const & a3, expr const & a4, expr const & a5, expr const & a6, expr const & a7, expr const & a8) const { return mk_app({*this, a1, a2, a3, a4, a5, a6, a7, a8}); }
// =======================================

// =======================================
// Casting (these functions are only needed for low-level code)
inline expr_var *         to_var(expr_cell * e)         { lean_assert(is_var(e));         return static_cast<expr_var*>(e); }
inline expr_const *       to_constant(expr_cell * e)    { lean_assert(is_constant(e));    return static_cast<expr_const*>(e); }
inline expr_dep_pair *    to_pair(expr_cell * e)        { lean_assert(is_pair(e));        return static_cast<expr_dep_pair*>(e); }
inline expr_proj *        to_proj(expr_cell * e)        { lean_assert(is_proj(e));        return static_cast<expr_proj*>(e); }
inline expr_app *         to_app(expr_cell * e)         { lean_assert(is_app(e));         return static_cast<expr_app*>(e); }
inline expr_abstraction * to_abstraction(expr_cell * e) { lean_assert(is_abstraction(e)); return static_cast<expr_abstraction*>(e); }
inline expr_lambda *      to_lambda(expr_cell * e)      { lean_assert(is_lambda(e));      return static_cast<expr_lambda*>(e); }
inline expr_pi *          to_pi(expr_cell * e)          { lean_assert(is_pi(e));          return static_cast<expr_pi*>(e); }
inline expr_sigma *       to_sigma(expr_cell * e)       { lean_assert(is_sigma(e));       return static_cast<expr_sigma*>(e); }
inline expr_type *        to_type(expr_cell * e)        { lean_assert(is_type(e));        return static_cast<expr_type*>(e); }
inline expr_let *         to_let(expr_cell * e)         { lean_assert(is_let(e));         return static_cast<expr_let*>(e); }
inline expr_metavar *     to_metavar(expr_cell * e)     { lean_assert(is_metavar(e));     return static_cast<expr_metavar*>(e); }

inline expr_var *         to_var(expr const & e)         { return to_var(e.raw()); }
inline expr_const *       to_constant(expr const & e)    { return to_constant(e.raw()); }
inline expr_dep_pair *    to_pair(expr const & e)        { return to_pair(e.raw()); }
inline expr_proj *        to_proj(expr const & e)        { return to_proj(e.raw()); }
inline expr_app *         to_app(expr const & e)         { return to_app(e.raw()); }
inline expr_abstraction * to_abstraction(expr const & e) { return to_abstraction(e.raw()); }
inline expr_lambda *      to_lambda(expr const & e)      { return to_lambda(e.raw()); }
inline expr_pi *          to_pi(expr const & e)          { return to_pi(e.raw()); }
inline expr_sigma *       to_sigma(expr const & e)       { return to_sigma(e.raw()); }
inline expr_let *         to_let(expr const & e)         { return to_let(e.raw()); }
inline expr_type *        to_type(expr const & e)        { return to_type(e.raw()); }
inline expr_metavar *     to_metavar(expr const & e)     { return to_metavar(e.raw()); }

// =======================================

// =======================================
// Accessors
inline unsigned      get_rc(expr_cell * e)               { return e->get_rc(); }
inline bool          is_shared(expr_cell * e)            { return get_rc(e) > 1; }
inline unsigned      var_idx(expr_cell * e)              { return to_var(e)->get_vidx(); }
inline bool          is_var(expr_cell * e, unsigned i)   { return is_var(e) && var_idx(e) == i; }
inline name const &  const_name(expr_cell * e)           { return to_constant(e)->get_name(); }
// Remark: the following function should not be exposed in the internal API.
inline optional<expr> const &  const_type(expr_cell * e) { return to_constant(e)->get_type(); }
inline expr const &  pair_first(expr_cell * e)           { return to_pair(e)->get_first(); }
inline expr const &  pair_second(expr_cell * e)          { return to_pair(e)->get_second(); }
inline expr const &  pair_type(expr_cell * e)            { return to_pair(e)->get_type(); }
inline bool          proj_first(expr_cell * e)           { return to_proj(e)->first(); }
inline expr const &  proj_arg(expr_cell * e)             { return to_proj(e)->get_arg(); }
inline value const & to_value(expr_cell * e)             { lean_assert(is_value(e)); return static_cast<expr_value*>(e)->get_value(); }
inline unsigned      num_args(expr_cell * e)             { return to_app(e)->get_num_args(); }
inline expr const &  arg(expr_cell * e, unsigned idx)    { return to_app(e)->get_arg(idx); }
inline name const &  abst_name(expr_cell * e)            { return to_abstraction(e)->get_name(); }
inline expr const &  abst_domain(expr_cell * e)          { return to_abstraction(e)->get_domain(); }
inline expr const &  abst_body(expr_cell * e)            { return to_abstraction(e)->get_body(); }
inline level const & ty_level(expr_cell * e)             { return to_type(e)->get_level(); }
inline name const &  let_name(expr_cell * e)             { return to_let(e)->get_name(); }
inline expr const &  let_value(expr_cell * e)            { return to_let(e)->get_value(); }
inline optional<expr> const &  let_type(expr_cell * e)   { return to_let(e)->get_type(); }
inline expr const &  let_body(expr_cell * e)             { return to_let(e)->get_body(); }
inline name const &  metavar_name(expr_cell * e)         { return to_metavar(e)->get_name(); }
inline local_context const & metavar_lctx(expr_cell * e) { return to_metavar(e)->get_lctx(); }

/** \brief Return the reference counter of the given expression. */
inline unsigned      get_rc(expr const &  e)              { return e.raw()->get_rc(); }
/** \brief Return true iff the reference counter of the given expression is greater than 1. */
inline bool          is_shared(expr const & e)            { return get_rc(e) > 1; }
/** \brief Return the de Bruijn index of the given expression. \pre is_var(e) */
inline unsigned      var_idx(expr const & e)              { return to_var(e)->get_vidx(); }
/** \brief Return true iff the given expression is a variable with de Bruijn index equal to \c i. */
inline bool          is_var(expr const & e, unsigned i)   { return is_var(e) && var_idx(e) == i; }
inline name const &  const_name(expr const & e)           { return to_constant(e)->get_name(); }
// Remark: the following function should not be exposed in the internal API.
inline optional<expr> const &  const_type(expr const & e) { return to_constant(e)->get_type(); }
/** \brief Return true iff the given expression is a constant with name \c n. */
inline bool          is_constant(expr const & e, name const & n) {
    return is_constant(e) && const_name(e) == n;
}
inline value const & to_value(expr const & e)             { return to_value(e.raw()); }
inline expr const &  pair_first(expr const & e)           { return to_pair(e)->get_first(); }
inline expr const &  pair_second(expr const & e)          { return to_pair(e)->get_second(); }
inline expr const &  pair_type(expr const & e)            { return to_pair(e)->get_type(); }
inline bool          proj_first(expr const & e)           { return to_proj(e)->first(); }
inline expr const &  proj_arg(expr const & e)             { return to_proj(e)->get_arg(); }
inline unsigned      num_args(expr const & e)             { return to_app(e)->get_num_args(); }
inline expr const &  arg(expr const & e, unsigned idx)    { return to_app(e)->get_arg(idx); }
inline expr const *  begin_args(expr const & e)           { return to_app(e)->begin_args(); }
inline expr const *  end_args(expr const & e)             { return to_app(e)->end_args(); }
inline name const &  abst_name(expr const & e)            { return to_abstraction(e)->get_name(); }
inline expr const &  abst_domain(expr const & e)          { return to_abstraction(e)->get_domain(); }
inline expr const &  abst_body(expr const & e)            { return to_abstraction(e)->get_body(); }
inline level const & ty_level(expr const & e)             { return to_type(e)->get_level(); }
inline name const &  let_name(expr const & e)             { return to_let(e)->get_name(); }
inline optional<expr> const &  let_type(expr const & e)   { return to_let(e)->get_type(); }
inline expr const &  let_value(expr const & e)            { return to_let(e)->get_value(); }
inline expr const &  let_body(expr const & e)             { return to_let(e)->get_body(); }
inline name const &  metavar_name(expr const & e)         { return to_metavar(e)->get_name(); }
inline local_context const & metavar_lctx(expr const & e) { return to_metavar(e)->get_lctx(); }
/** \brief Return the depth of the given expression */
unsigned get_depth(expr const & e);

inline bool has_metavar(expr const & e) { return e.has_metavar(); }
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

// =======================================
// Miscellaneous
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
        switch (e.kind()) {
        case expr_kind::Pi:     return mk_pi(n, p.first, p.second);
        case expr_kind::Lambda: return mk_lambda(n, p.first, p.second);
        case expr_kind::Sigma:  return mk_sigma(n, p.first, p.second);
        default: lean_unreachable();
        }
    } else {
        return e;
    }
}
template<typename F> expr update_let(expr const & e, F f) {
    static_assert(std::is_same<typename std::result_of<F(optional<expr> const &, expr const &, expr const &)>::type,
                  std::tuple<optional<expr>, expr, expr>>::value,
                  "update_let: return type of f is not tuple<optional<expr>, expr, expr>");
    optional<expr> const & old_t = let_type(e);
    expr const & old_v           = let_value(e);
    expr const & old_b           = let_body(e);
    std::tuple<optional<expr>, expr, expr> r = f(old_t, old_v, old_b);
    if (!is_eqp(std::get<0>(r), old_t) || !is_eqp(std::get<1>(r), old_v) || !is_eqp(std::get<2>(r), old_b))
        return mk_let(let_name(e), std::get<0>(r), std::get<1>(r), std::get<2>(r));
    else
        return e;
}
template<typename F> expr update_metavar(expr const & e, name const & n, F f) {
    static_assert(std::is_same<typename std::result_of<F(local_entry const &)>::type, local_entry>::value,
                  "update_metavar: return type of f(local_entry) is not local_entry");
    buffer<local_entry> new_entries;
    bool modified = n != metavar_name(e);
    for (local_entry const & me : metavar_lctx(e)) {
        local_entry new_me = f(me);
        if (new_me.kind() != me.kind() || new_me.s() != me.s()) {
            modified = true;
        } else if (new_me.is_inst()) {
            if (!is_eqp(new_me.v(), me.v()))
                modified = true;
        } else if (new_me.n() != me.n()) {
            modified = true;
        }
        new_entries.push_back(new_me);
    }
    if (modified)
        return mk_metavar(n, to_list(new_entries.begin(), new_entries.end()));
    else
        return e;
}
template<typename F> expr update_metavar(expr const & e, F f) {
    static_assert(std::is_same<typename std::result_of<F(local_entry const &)>::type, local_entry>::value,
                  "update_metavar: return type of f(local_entry) is not local_entry");
    return update_metavar(e, metavar_name(e), f);
}
inline expr update_metavar(expr const & e, local_context const & lctx) {
    if (metavar_lctx(e) != lctx)
        return mk_metavar(metavar_name(e), lctx);
    else
        return e;
}
inline expr update_const(expr const & e, optional<expr> const & t) {
    if (!is_eqp(const_type(e), t))
        return mk_constant(const_name(e), t);
    else
        return e;
}
template<typename F> expr update_pair(expr const & e, F f) {
    expr const & old_f  = pair_first(e);
    expr const & old_s  = pair_second(e);
    expr const & old_t  = pair_type(e);
    auto r = f(old_f, old_s, old_t);
    if (!is_eqp(std::get<0>(r), old_t) || !is_eqp(std::get<1>(r), old_s) || !is_eqp(std::get<2>(r), old_t))
        return mk_pair(std::get<0>(r), std::get<1>(r), std::get<2>(r));
    else
        return e;
}
inline expr update_pair(expr const & e, expr const & new_f, expr const & new_s, expr const & new_t) {
    return update_pair(e, [&](expr const &, expr const &, expr const &) { return std::make_tuple(new_f, new_s, new_t); });
}
inline expr update_proj(expr const & e, expr const & new_arg) {
    if (!is_eqp(proj_arg(e), new_arg))
        return mk_proj(proj_first(e), new_arg);
    else
        return e;
}
// =======================================


// =======================================
// Serializer/Deserializer
serializer & operator<<(serializer & s, expr const & e);
expr read_expr(deserializer & d);
inline deserializer & operator>>(deserializer & d, expr & e) { e = read_expr(d); return d; }
// =======================================

std::ostream & operator<<(std::ostream & out, expr const & e);
}
