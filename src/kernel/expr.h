/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
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
#include "util/rc.h"
#include "util/name.h"
#include "util/hash.h"
#include "util/buffer.h"
#include "util/list_fn.h"
#include "util/optional.h"
#include "util/serializer.h"
#include "util/sexpr/format.h"
#include "kernel/level.h"
#include "kernel/formatter.h"
#include "kernel/expr_eq_fn.h"

namespace lean {
class abstract_type_context;

// Tags are used by frontends to mark expressions. They are automatically propagated by
// procedures such as update_app, update_binder, etc.
typedef unsigned tag;
constexpr tag nulltag = std::numeric_limits<unsigned>::max();
class expr;
/* =======================================
   Expressions
   expr ::=   Var           idx
          |   Sort          level
          |   Constant      name [levels]
          |   Meta          name expr
          |   Local         name expr
          |   App           expr expr
          |   Lambda        name expr expr
          |   Pi            name expr expr
          |   Let           name expr expr expr
          |   Macro         macro
*/
enum class expr_kind { Var, Sort, Constant, Meta, Local, App, Lambda, Pi, Let, Macro };
class expr_cell {
protected:
    // The bits of the following field mean:
    //    0-1  - term is an arrow (0 - not initialized, 1 - is arrow, 2 - is not arrow)
    // Remark: we use atomic_uchar because these flags are computed lazily (i.e., after the expression is created)
    atomic_uchar       m_flags;
    unsigned           m_kind:8;
    unsigned           m_has_expr_mv:1;    // term contains expression metavariables
    unsigned           m_has_univ_mv:1;    // term contains universe metavariables
    unsigned           m_has_local:1;      // term contains local constants
    unsigned           m_has_param_univ:1; // term constains parametric universe levels
    unsigned           m_hash;             // hash based on the structure of the expression (this is a good hash for structural equality)
    atomic_uint        m_tag;
    MK_LEAN_RC(); // Declare m_rc counter
    void dealloc();

    optional<bool> is_arrow() const;
    void set_is_arrow(bool flag);
    friend bool is_arrow(expr const & e);

    static void dec_ref(expr & c, buffer<expr_cell*> & todelete);
    expr_cell(expr_cell const & src); // for hash_consing
public:
    expr_cell(expr_kind k, unsigned h, bool has_expr_mv, bool has_univ_mv, bool has_local, bool has_param_univ, tag g);
    expr_kind kind() const { return static_cast<expr_kind>(m_kind); }
    unsigned  hash() const { return m_hash; }
    bool has_expr_metavar() const { return m_has_expr_mv; }
    bool has_univ_metavar() const { return m_has_univ_mv; }
    bool has_local() const { return m_has_local; }
    bool has_param_univ() const { return m_has_param_univ; }
    void set_tag(tag t);
    tag get_tag() const { return m_tag; }
};

typedef expr_cell * expr_ptr;

class macro_definition;
class binder_info;

/**
   \brief Exprs for encoding formulas/expressions, types and proofs.
*/
class expr {
private:
    expr_cell * m_ptr;
    explicit expr(expr_cell * ptr):m_ptr(ptr) { if (m_ptr) m_ptr->inc_ref(); }
    friend class expr_cell;
    friend struct cache_expr_insert_fn;
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
    bool has_expr_metavar() const { return m_ptr->has_expr_metavar(); }
    bool has_univ_metavar() const { return m_ptr->has_univ_metavar(); }
    bool has_metavar() const { return has_expr_metavar() || has_univ_metavar(); }
    bool has_local() const { return m_ptr->has_local(); }
    bool has_param_univ() const { return m_ptr->has_param_univ(); }

    expr set_tag(tag t) { m_ptr->set_tag(t); return *this; }
    tag get_tag() const { return m_ptr->get_tag(); }

    operator expr_ptr() const { return m_ptr; }
    expr_cell * raw() const { return m_ptr; }

    friend expr mk_var(unsigned idx, tag g);
    friend expr mk_sort(level const & l, tag g);
    friend expr mk_constant(name const & n, levels const & ls, tag g);
    friend expr mk_metavar(name const & n, name const & pp_n, expr const & t, tag g);
    friend expr mk_local(name const & n, name const & pp_n, expr const & t, binder_info const & bi,
                         tag g);
    friend expr mk_app(expr const & f, expr const & a, tag g);
    friend expr mk_binding(expr_kind k, name const & n, expr const & t, expr const & e, binder_info const & i,
                           tag g);
    friend expr mk_let(name const & n, expr const & t, expr const & v, expr const & b, tag g);
    friend expr mk_macro(macro_definition const & m, unsigned num, expr const * args, tag g);
    friend bool is_eqp(expr const & a, expr const & b) { return a.m_ptr == b.m_ptr; }
};

expr copy_tag(expr const & e, expr && new_e);

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
    friend expr_cell;
    void dealloc();
public:
    expr_var(unsigned idx, tag g);
    unsigned get_vidx() const { return m_vidx; }
};

/** \brief (parametric) Constants. */
class expr_const : public expr_cell {
    name       m_name;
    levels     m_levels;
    friend expr_cell;
    void dealloc();
    friend struct cache_expr_insert_fn;
    expr_const(expr_const const &, levels const & new_levels); // for hash_consing
public:
    expr_const(name const & n, levels const & ls, tag g);
    name const & get_name() const { return m_name; }
    levels const & get_levels() const { return m_levels; }
};

/** \brief Composite expressions */
class expr_composite : public expr_cell {
protected:
    unsigned m_weight;
    unsigned m_depth;
    unsigned m_free_var_range;
    friend unsigned get_weight(expr const & e);
    friend unsigned get_depth(expr const & e);
    friend unsigned get_free_var_range(expr const & e);
    expr_composite(expr_composite const & src); // for hash_consing
public:
    expr_composite(expr_kind k, unsigned h, bool has_expr_mv, bool has_univ_mv, bool has_local,
                   bool has_param_univ, unsigned w, unsigned fv_range, tag g);
};

/** \brief Metavariables and local constants */
class expr_mlocal : public expr_composite {
protected:
    name   m_name;
    name   m_pp_name; // user facing name
    expr   m_type;
    friend expr_cell;
    void dealloc(buffer<expr_cell*> & todelete);
    friend struct cache_expr_insert_fn;
    expr_mlocal(expr_mlocal const &, expr const & new_type); // for hash_consing
public:
    expr_mlocal(bool is_meta, name const & n, name const & pp_n, expr const & t, tag g);
    name const & get_name() const { return m_name; }
    name const & get_pp_name() const { return m_pp_name; }
    expr const & get_type() const { return m_type; }
};

/**
   \brief Auxiliary annotation for binders (Lambda and Pi). This information
   is only used for elaboration.
*/
class binder_info {
    unsigned m_implicit:1;        //! if true, binder argument is an implicit argument
    unsigned m_strict_implicit:1; //! if true, binder argument is assumed to be a strict implicit argument
    /** \brief if m_inst_implicit is true, binder argument is an implicit argument, and should be
        inferred by class-instance resolution. */
    unsigned m_inst_implicit:1;
    /** \brief Auxiliary internal attribute used to mark local constants representing recursive functions
        in recursive equations. TODO(Leo): rename to eqn_decl since we also mark non recursive equations
        (e.g., `match ... with ... end`) with this flag. */
    unsigned m_rec:1;
public:
    binder_info(bool implicit = false, bool strict_implicit = false, bool inst_implicit = false, bool rec = false):
        m_implicit(implicit), m_strict_implicit(strict_implicit), m_inst_implicit(inst_implicit), m_rec(rec) {}
    bool is_implicit() const { return m_implicit; }
    bool is_strict_implicit() const { return m_strict_implicit; }
    bool is_inst_implicit() const { return m_inst_implicit; }
    bool is_rec() const { return m_rec; }
    unsigned hash() const;
};

inline binder_info mk_implicit_binder_info()        { return binder_info(true); }
inline binder_info mk_strict_implicit_binder_info() { return binder_info(false, true); }
inline binder_info mk_inst_implicit_binder_info()   { return binder_info(false, false, true); }
inline binder_info mk_rec_info(bool f)              { return binder_info(false, false, false, f); }

inline bool is_explicit(binder_info const & bi) {
    return !bi.is_implicit() && !bi.is_strict_implicit() && !bi.is_inst_implicit();
}

bool operator==(binder_info const & i1, binder_info const & i2);
inline bool operator!=(binder_info const & i1, binder_info const & i2) { return !(i1 == i2); }

/** \brief Compute a hash code that takes binder_info into account.
    \remark This information is not cached like hash(). */
unsigned hash_bi(expr const & e);

/** \brief expr_mlocal subclass for local constants. */
class expr_local : public expr_mlocal {
    binder_info m_bi;
    friend expr_cell;
    void dealloc(buffer<expr_cell*> & todelete);
    friend struct cache_expr_insert_fn;
    expr_local(expr_local const &, expr const & new_type); // for hash_consing
public:
    expr_local(name const & n, name const & pp_name, expr const & t, binder_info const & bi, tag g);
    binder_info const & get_info() const { return m_bi; }
};

/** \brief Applications */
class expr_app : public expr_composite {
    expr     m_fn;
    expr     m_arg;
    friend expr_cell;
    void dealloc(buffer<expr_cell*> & todelete);
    friend struct cache_expr_insert_fn;
    expr_app(expr_app const &, expr const & new_fn, expr const & new_arg); // for hash_consing
public:
    expr_app(expr const & fn, expr const & arg, tag g);
    expr const & get_fn() const { return m_fn; }
    expr const & get_arg() const { return m_arg; }
};

class binder {
    friend class expr_binding;
    name             m_name;
    expr             m_type;
    binder_info      m_info;
    binder(binder const & src, expr const & new_type): // for hash_consing
        m_name(src.m_name), m_type(new_type), m_info(src.m_info) {}
public:
    binder(name const & n, expr const & t, binder_info const & bi):
        m_name(n), m_type(t), m_info(bi) {}
    name const & get_name() const { return m_name; }
    expr const & get_type() const { return m_type; }
    binder_info const & get_info() const { return m_info; }
    binder update_type(expr const & t) const { return binder(m_name, t, m_info); }
};

/** \brief Lambda and Pi expressions */
class expr_binding : public expr_composite {
    binder           m_binder;
    expr             m_body;
    friend class expr_cell;
    void dealloc(buffer<expr_cell*> & todelete);
    friend struct cache_expr_insert_fn;
    expr_binding(expr_binding const &, expr const & new_domain, expr const & new_body); // for hash_consing
public:
    expr_binding(expr_kind k, name const & n, expr const & t, expr const & e,
                 binder_info const & i, tag g);
    name const & get_name() const   { return m_binder.get_name(); }
    expr const & get_domain() const { return m_binder.get_type(); }
    expr const & get_body() const   { return m_body; }
    binder_info const & get_info() const { return m_binder.get_info(); }
    binder const & get_binder() const { return m_binder; }
};

/** \brief Let-expressions */
class expr_let : public expr_composite {
    name m_name;
    expr m_type;
    expr m_value;
    expr m_body;
    friend class expr_cell;
    void dealloc(buffer<expr_cell*> & todelete);
    friend struct cache_expr_insert_fn;
    expr_let(expr_let const &, expr const & new_type, expr const & new_value, expr const & new_body); // for hash_consing
public:
    expr_let(name const & n, expr const & t, expr const & v, expr const & b, tag g);
    name const & get_name() const { return m_name; }
    expr const & get_type() const { return m_type; }
    expr const & get_value() const { return m_value; }
    expr const & get_body() const   { return m_body; }
};

/** \brief Sort */
class expr_sort : public expr_cell {
    level    m_level;
    friend expr_cell;
    void dealloc();
    friend struct cache_expr_insert_fn;
    expr_sort(expr_sort const &, level const & new_level); // for hash_consing
public:
    expr_sort(level const & l, tag g);
    ~expr_sort();
    level const & get_level() const { return m_level; }
};

/** \brief Abstract class for macro_definitions */
class macro_definition_cell {
protected:
    void dealloc() { delete this; }
    MK_LEAN_RC();
    /**
       \brief Auxiliary method used for implementing a total order on macro
       attachments. It is invoked by operator<, and it is only invoked when
       <tt>get_name() == other.get_name()</tt>
    */
    virtual bool lt(macro_definition_cell const &) const;
public:
    macro_definition_cell():m_rc(0) {}
    virtual ~macro_definition_cell() {}
    virtual name get_name() const = 0;
    virtual expr check_type(expr const & m, abstract_type_context & ctx, bool infer_only) const = 0;
    virtual optional<expr> expand(expr const & m, abstract_type_context & ctx) const = 0;
    virtual optional<expr> expand1(expr const & m, abstract_type_context & ctx) const { return expand(m, ctx); }
    virtual unsigned trust_level() const;
    virtual bool operator==(macro_definition_cell const & other) const;
    virtual void display(std::ostream & out) const;
    virtual unsigned hash() const;
    virtual void write(serializer & s) const = 0;
    typedef std::function<expr(deserializer&, unsigned, expr const *)> reader;
};

/** \brief Smart pointer for macro definitions */
class macro_definition {
public:
    macro_definition_cell * m_ptr;
public:
    explicit macro_definition(macro_definition_cell * ptr);
    macro_definition(macro_definition const & s);
    macro_definition(macro_definition && s);
    ~macro_definition();

    macro_definition & operator=(macro_definition const & s);
    macro_definition & operator=(macro_definition && s);

    name get_name() const { return m_ptr->get_name(); }
    expr check_type(expr const & m, abstract_type_context & ctx, bool infer_only) const {
        return m_ptr->check_type(m, ctx, infer_only);
    }
    optional<expr> expand(expr const & m, abstract_type_context & ctx) const { return m_ptr->expand(m, ctx); }
    optional<expr> expand1(expr const & m, abstract_type_context & ctx) const { return m_ptr->expand1(m, ctx); }
    unsigned trust_level() const { return m_ptr->trust_level(); }
    bool operator==(macro_definition const & other) const { return m_ptr->operator==(*other.m_ptr); }
    bool operator!=(macro_definition const & other) const { return !operator==(other); }
    bool operator<(macro_definition const & other) const;
    void display(std::ostream & out) const { return m_ptr->display(out); }
    unsigned hash() const { return m_ptr->hash(); }
    void write(serializer & s) const { return m_ptr->write(s); }
    macro_definition_cell const * raw() const { return m_ptr; }

    friend bool is_eqp(macro_definition const & d1, macro_definition const & d2) {
        return d1.m_ptr == d2.m_ptr;
    }
};

/** \brief Macro attachments */
class expr_macro : public expr_composite {
    macro_definition m_definition;
    unsigned         m_num_args;
    friend class expr_cell;
    friend expr copy(expr const & a);
    friend expr update_macro(expr const & e, unsigned num, expr const * args);
    void dealloc(buffer<expr_cell*> & todelete);
    expr * get_args_ptr() {
        return reinterpret_cast<expr *>(reinterpret_cast<char *>(this)+sizeof(expr_macro));
    }
    expr const * get_args_ptr() const {
        return reinterpret_cast<expr const *>(reinterpret_cast<char const *>(this)+sizeof(expr_macro));
    }
    friend struct cache_expr_insert_fn;
    expr_macro(expr_macro const & src, expr const * new_args); // for hash_consing
public:
    expr_macro(macro_definition const & v, unsigned num, expr const * args, tag g);
    ~expr_macro();

    macro_definition const & get_def() const { return m_definition; }
    expr const * get_args() const { return get_args_ptr(); }
    expr const & get_arg(unsigned idx) const { lean_assert(idx < m_num_args); return get_args_ptr()[idx]; }
    unsigned get_num_args() const { return m_num_args; }
};

// =======================================
// Testers
inline bool is_var(expr_ptr e)         { return e->kind() == expr_kind::Var; }
inline bool is_constant(expr_ptr e)    { return e->kind() == expr_kind::Constant; }
inline bool is_local(expr_ptr e)       { return e->kind() == expr_kind::Local; }
inline bool is_metavar(expr_ptr e)     { return e->kind() == expr_kind::Meta; }
inline bool is_macro(expr_ptr e)       { return e->kind() == expr_kind::Macro; }
inline bool is_app(expr_ptr e)         { return e->kind() == expr_kind::App; }
inline bool is_lambda(expr_ptr e)      { return e->kind() == expr_kind::Lambda; }
inline bool is_pi(expr_ptr e)          { return e->kind() == expr_kind::Pi; }
inline bool is_let(expr_ptr e)         { return e->kind() == expr_kind::Let; }
inline bool is_sort(expr_ptr e)        { return e->kind() == expr_kind::Sort; }
inline bool is_binding(expr_ptr e)     { return is_lambda(e) || is_pi(e); }
inline bool is_mlocal(expr_ptr e)      { return is_metavar(e) || is_local(e); }

bool is_atomic(expr const & e);
bool is_arrow(expr const & t);
/** \brief Return true iff \c e is a metavariable or an application of a metavariable */
bool is_meta(expr const & e);
// =======================================

// =======================================
// Constructors
expr mk_var(unsigned idx, tag g = nulltag);
inline expr Var(unsigned idx) { return mk_var(idx); }
expr mk_constant(name const & n, levels const & ls, tag g = nulltag);
inline expr mk_constant(name const & n) { return mk_constant(n, levels()); }
inline expr Const(name const & n) { return mk_constant(n); }
expr mk_macro(macro_definition const & m, unsigned num = 0, expr const * args = nullptr, tag g = nulltag);
expr mk_metavar(name const & n, expr const & t, tag g = nulltag);
expr mk_metavar(name const & n, name const & pp_n, expr const & t, tag g = nulltag);
expr mk_local(name const & n, name const & pp_n, expr const & t, binder_info const & bi, tag g = nulltag);
inline expr mk_local(name const & n, expr const & t, tag g = nulltag) { return mk_local(n, n, t, binder_info(), g); }
inline expr mk_local(name const & n, expr const & t, binder_info const & bi, tag g = nulltag) {
    return mk_local(n, n, t, bi, g);
}
inline expr Local(name const & n, expr const & t, binder_info const & bi = binder_info(), tag g = nulltag) {
    return mk_local(n, t, bi, g);
}
expr mk_app(expr const & f, expr const & a, tag g = nulltag);
expr mk_app(expr const & f, unsigned num_args, expr const * args, tag g = nulltag);
expr mk_app(unsigned num_args, expr const * args, tag g = nulltag);
inline expr mk_app(std::initializer_list<expr> const & l, tag g = nulltag) {
    return mk_app(l.size(), l.begin(), g);
}
inline expr mk_app(buffer<expr> const & args, tag g = nulltag) { return mk_app(args.size(), args.data(), g); }
inline expr mk_app(expr const & f, buffer<expr> const & args, tag g = nulltag) {
    return mk_app(f, args.size(), args.data(), g);
}
expr mk_app(expr const & f, list<expr> const & args, tag g = nulltag);
expr mk_rev_app(expr const & f, unsigned num_args, expr const * args, tag g = nulltag);
expr mk_rev_app(unsigned num_args, expr const * args, tag g = nulltag);
inline expr mk_rev_app(buffer<expr> const & args, tag g = nulltag) { return mk_rev_app(args.size(), args.data(), g); }
inline expr mk_rev_app(expr const & f, buffer<expr> const & args, tag g = nulltag) {
    return mk_rev_app(f, args.size(), args.data(), g);
}
expr mk_binding(expr_kind k, name const & n, expr const & t, expr const & e,
                binder_info const & i = binder_info(), tag g = nulltag);
inline expr mk_lambda(name const & n, expr const & t, expr const & e,
                      binder_info const & i = binder_info(), tag g = nulltag) {
    return mk_binding(expr_kind::Lambda, n, t, e, i, g);
}
inline expr mk_pi(name const & n, expr const & t, expr const & e, binder_info const & i = binder_info(), tag g = nulltag) {
    return mk_binding(expr_kind::Pi, n, t, e, i, g);
}
expr mk_let(name const & n, expr const & t, expr const & v, expr const & b, tag g = nulltag);
expr mk_sort(level const & l, tag g = nulltag);

expr mk_Prop();
expr mk_Type();

bool is_default_var_name(name const & n);
expr mk_arrow(expr const & t, expr const & e, tag g = nulltag);
inline expr operator>>(expr const & t, expr const & e) { return mk_arrow(t, e); }

// Auxiliary
inline expr mk_app(expr const & e1, expr const & e2, expr const & e3, tag g = nulltag) {
    return mk_app({e1, e2, e3}, g);
}
inline expr mk_app(expr const & e1, expr const & e2, expr const & e3, expr const & e4, tag g = nulltag) {
    return mk_app({e1, e2, e3, e4}, g);
}
inline expr mk_app(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5,
                   tag g = nulltag) {
    return mk_app({e1, e2, e3, e4, e5}, g);
}

/** \brief Return application (...((f x_{n-1}) x_{n-2}) ... x_0) */
expr mk_app_vars(expr const & f, unsigned n, tag g = nulltag);

/** \brief Enable hash-consing (caching) for expressions (and universe levels) */
bool enable_expr_caching(bool f);
/** \brief Helper class for temporarily enabling/disabling expression caching */
struct scoped_expr_caching {
    bool m_old;
    scoped_expr_caching(bool f) { m_old = enable_expr_caching(f); }
    ~scoped_expr_caching() { enable_expr_caching(m_old); }
};
/** \brief Return true iff \c e is in the cache */
bool is_cached(expr const & e);
void flush_expr_cache();
// =======================================

// =======================================
// Casting (these functions are only needed for low-level code)
inline expr_var *         to_var(expr_ptr e)        { lean_assert(is_var(e));         return static_cast<expr_var*>(e); }
inline expr_const *       to_constant(expr_ptr e)   { lean_assert(is_constant(e));    return static_cast<expr_const*>(e); }
inline expr_app *         to_app(expr_ptr e)        { lean_assert(is_app(e));         return static_cast<expr_app*>(e); }
inline expr_binding *     to_binding(expr_ptr e)    { lean_assert(is_binding(e));     return static_cast<expr_binding*>(e); }
inline expr_sort *        to_sort(expr_ptr e)       { lean_assert(is_sort(e));        return static_cast<expr_sort*>(e); }
inline expr_mlocal *      to_mlocal(expr_ptr e)     { lean_assert(is_mlocal(e));      return static_cast<expr_mlocal*>(e); }
inline expr_local *       to_local(expr_ptr e)      { lean_assert(is_local(e));       return static_cast<expr_local*>(e); }
inline expr_mlocal *      to_metavar(expr_ptr e)    { lean_assert(is_metavar(e));     return static_cast<expr_mlocal*>(e); }
inline expr_let *         to_let(expr_ptr e)        { lean_assert(is_let(e));         return static_cast<expr_let*>(e); }
inline expr_macro *       to_macro(expr_ptr e)      { lean_assert(is_macro(e));       return static_cast<expr_macro*>(e); }
// =======================================


// =======================================
// Accessors
inline unsigned       get_rc(expr_ptr e)                { return e->get_rc(); }
inline bool           is_shared(expr_ptr e)             { return get_rc(e) > 1; }
inline unsigned       var_idx(expr_ptr e)               { return to_var(e)->get_vidx(); }
inline bool           is_var(expr_ptr e, unsigned i)    { return is_var(e) && var_idx(e) == i; }
inline name const &   const_name(expr_ptr e)            { return to_constant(e)->get_name(); }
inline levels const & const_levels(expr_ptr e)          { return to_constant(e)->get_levels(); }
inline macro_definition const & macro_def(expr_ptr e)   { return to_macro(e)->get_def(); }
inline expr const *   macro_args(expr_ptr e)            { return to_macro(e)->get_args(); }
inline expr const &   macro_arg(expr_ptr e, unsigned i) { return to_macro(e)->get_arg(i); }
inline unsigned       macro_num_args(expr_ptr e)        { return to_macro(e)->get_num_args(); }
inline expr const &   app_fn(expr_ptr e)                { return to_app(e)->get_fn(); }
inline expr const &   app_arg(expr_ptr e)               { return to_app(e)->get_arg(); }
inline name const &   binding_name(expr_ptr e)          { return to_binding(e)->get_name(); }
inline expr const &   binding_domain(expr_ptr e)        { return to_binding(e)->get_domain(); }
inline expr const &   binding_body(expr_ptr e)          { return to_binding(e)->get_body(); }
inline binder_info const & binding_info(expr_ptr e)     { return to_binding(e)->get_info(); }
inline binder const & binding_binder(expr_ptr e)        { return to_binding(e)->get_binder(); }
inline level const &  sort_level(expr_ptr e)            { return to_sort(e)->get_level(); }
inline name const &   mlocal_name(expr_ptr e)           { return to_mlocal(e)->get_name(); }
inline expr const &   mlocal_type(expr_ptr e)           { return to_mlocal(e)->get_type(); }
inline name const &   mlocal_pp_name(expr_ptr e)        { return to_mlocal(e)->get_pp_name(); }
inline binder_info const & local_info(expr_ptr e)       { return to_local(e)->get_info(); }
inline name const &   let_name(expr_ptr e)              { return to_let(e)->get_name(); }
inline expr const &   let_type(expr_ptr e)              { return to_let(e)->get_type(); }
inline expr const &   let_value(expr_ptr e)             { return to_let(e)->get_value(); }
inline expr const &   let_body(expr_ptr e)              { return to_let(e)->get_body(); }


inline bool is_constant(expr const & e, name const & n) { return is_constant(e) && const_name(e) == n; }
inline bool has_metavar(expr const & e) { return e.has_metavar(); }
inline bool has_expr_metavar(expr const & e) { return e.has_expr_metavar(); }
inline bool has_univ_metavar(expr const & e) { return e.has_univ_metavar(); }
/** \brief Similar to \c has_expr_metavar, but ignores metavariables occurring in local constant types.
    It also returns the meta-variable application found in \c e.
*/
optional<expr> has_expr_metavar_strict(expr const & e);
inline bool has_local(expr const & e) { return e.has_local(); }
inline bool has_param_univ(expr const & e) { return e.has_param_univ(); }
unsigned get_weight(expr const & e);
unsigned get_depth(expr const & e);
/**
   \brief Return \c R s.t. the de Bruijn index of all free variables
   occurring in \c e is in the interval <tt>[0, R)</tt>.
*/
inline unsigned get_free_var_range(expr const & e) {
    switch (e.kind()) {
    case expr_kind::Var:                            return var_idx(e) + 1;
    case expr_kind::Constant: case expr_kind::Sort: return 0;
    default:                                        return static_cast<expr_composite*>(e.raw())->m_free_var_range;
    }
}
/** \brief Return true iff the given expression has free variables. */
inline bool has_free_vars(expr const & e) { return get_free_var_range(e) > 0; }
/** \brief Return true iff the given expression does not have free variables. */
inline bool closed(expr const & e) { return !has_free_vars(e); }
/**
    \brief Given \c e of the form <tt>(...(f a1) ... an)</tt>, store a1 ... an in args.
    If \c e is not an application, then nothing is stored in args.

    It returns the f.
*/
expr const & get_app_args(expr const & e, buffer<expr> & args);
/** \brief Similar to \c get_app_args, but stores at most num args.
    Examples:
    1) get_app_args_at_most(f a b c, 2, args);
    stores {b, c} in args and returns (f a)

    2) get_app_args_at_most(f a b c, 4, args);
    stores {a, b, c} in args and returns f
*/
expr const & get_app_args_at_most(expr const & e, unsigned num, buffer<expr> & args);

/**
   \brief Similar to \c get_app_args, but arguments are stored in reverse order in \c args.
   If e is of the form <tt>(...(f a1) ... an)</tt>, then the procedure stores [an, ..., a1] in \c args.
*/
expr const & get_app_rev_args(expr const & e, buffer<expr> & args);
/** \brief Given \c e of the form <tt>(...(f a_1) ... a_n)</tt>, return \c f. If \c e is not an application, then return \c e. */
expr const & get_app_fn(expr const & e);
/** \brief Given \c e of the form <tt>(...(f a_1) ... a_n)</tt>, return \c n. If \c e is not an application, then return 0. */
unsigned get_app_num_args(expr const & e);
// =======================================

// =======================================
// Auxiliary functionals
/** \brief Functional object for hashing kernel expressions. */
struct expr_hash { unsigned operator()(expr const & e) const { return e.hash(); } };
// =======================================

// =======================================
// Update
expr update_app(expr const & e, expr const & new_fn, expr const & new_arg);
expr update_binding(expr const & e, expr const & new_domain, expr const & new_body);
expr update_binding(expr const & e, expr const & new_domain, expr const & new_body, binder_info const & bi);
expr update_mlocal(expr const & e, expr const & new_type);
expr update_local(expr const & e, expr const & new_type, binder_info const & bi);
expr update_local(expr const & e, binder_info const & bi);
expr update_sort(expr const & e, level const & new_level);
expr update_constant(expr const & e, levels const & new_levels);
expr update_macro(expr const & e, unsigned num, expr const * args);
expr update_let(expr const & e, expr const & new_type, expr const & new_value, expr const & new_body);

// =======================================

// =======================================
// Implicit argument inference
/**
   \brief Given \c t of the form <tt>Pi (x_1 : A_1) ... (x_k : A_k), B</tt>,
   mark the first \c num_params as implicit if they are not already marked, and
   they occur in the remaining arguments. If \c strict is false, then we
   also mark it implicit if it occurs in \c B.
*/
expr infer_implicit(expr const & t, unsigned num_params, bool strict);
expr infer_implicit(expr const & t, bool strict);
// =======================================

std::ostream & operator<<(std::ostream & out, expr_kind const & k);
std::ostream & operator<<(std::ostream & out, expr const & e);

#ifdef LEAN_TRACK_LIVE_EXPRS
unsigned get_num_live_exprs();
#endif

void initialize_expr();
void finalize_expr();
}
