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
#include "runtime/optional.h"
#include "runtime/thread.h"
#include "runtime/serializer.h"
#include "util/rc.h"
#include "util/name.h"
#include "util/nat.h"
#include "util/hash.h"
#include "util/buffer.h"
#include "util/kvmap.h"
#include "util/list_fn.h"
#include "util/sexpr/format.h"
#include "kernel/level.h"
#include "kernel/expr_eq_fn.h"

namespace lean {
/* Binder annotations for Pi/lambda expressions */
enum class binder_info { Default, Implicit, StrictImplicit, InstImplicit, Rec };

inline binder_info mk_binder_info() { return binder_info::Default; }
inline binder_info mk_implicit_binder_info() { return binder_info::Implicit; }
inline binder_info mk_strict_implicit_binder_info() { return binder_info::StrictImplicit; }
inline binder_info mk_inst_implicit_binder_info() { return binder_info::InstImplicit; }
inline binder_info mk_rec_info() { return binder_info::Rec; }

inline bool is_default(binder_info bi) { return bi == binder_info::Default; }
inline bool is_implicit(binder_info bi) { return bi == binder_info::Implicit; }
inline bool is_strict_implicit(binder_info bi) { return bi == binder_info::StrictImplicit; }
inline bool is_inst_implicit(binder_info bi) { return bi == binder_info::InstImplicit; }
inline bool is_explicit(binder_info bi) { return !is_implicit(bi) && !is_strict_implicit(bi) && !is_inst_implicit(bi); }
inline bool is_rec(binder_info bi) { return bi == binder_info::Rec; }

/* =======================================
   Expressions
   expr ::=   BVar          idx
          |   FVar          name
          |   Sort          level
          |   Constant      name [levels]
          |   MVar          name expr
          |   App           expr expr
          |   Lambda        name expr expr
          |   Pi            name expr expr
          |   Let           name expr expr expr
          |   Lit           literal
          |   MData         kvmap expr
          |   Proj          nat expr

          The following constructors will be deleted in the future

          |   Quote         bool expr
*/
class expr;
enum class expr_kind { BVar, FVar, Sort, Constant, MVar, App, Lambda, Pi, Let, Lit, MData, Proj, Quote };
class expr_cell {
protected:
    // The bits of the following field mean:
    //    0-1  - term is an arrow (0 - not initialized, 1 - is arrow, 2 - is not arrow)
    // Remark: we use atomic_uchar because these flags are computed lazily (i.e., after the expression is created)
    atomic_uchar       m_flags;
    unsigned           m_kind:8;
    unsigned           m_has_expr_mv:1;    // term contains expression metavariables
    unsigned           m_has_univ_mv:1;    // term contains universe metavariables
    unsigned           m_has_fvar:1;       // term contains free variables
    unsigned           m_has_param_univ:1; // term constains parametric universe levels
    unsigned           m_hash;             // hash based on the structure of the expression (this is a good hash for structural equality)
    MK_LEAN_RC(); // Declare m_rc counter
    void dealloc();

    optional<bool> is_arrow() const;
    void set_is_arrow(bool flag);
    friend bool is_arrow(expr const & e);

    static void dec_ref(expr & c, buffer<expr_cell*> & todelete);
    expr_cell(expr_cell const & src); // for hash_consing
public:
    expr_cell(expr_kind k, unsigned h, bool has_expr_mv, bool has_univ_mv, bool has_fvar, bool has_param_univ);
    expr_kind kind() const { return static_cast<expr_kind>(m_kind); }
    unsigned  hash() const { return m_hash; }
    bool has_expr_metavar() const { return m_has_expr_mv; }
    bool has_univ_metavar() const { return m_has_univ_mv; }
    bool has_fvar() const { return m_has_fvar; }
    bool has_param_univ() const { return m_has_param_univ; }
};

typedef expr_cell * expr_ptr;

class literal;

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
    bool has_expr_metavar() const { return m_ptr->has_expr_metavar(); }
    bool has_univ_metavar() const { return m_ptr->has_univ_metavar(); }
    bool has_metavar() const { return has_expr_metavar() || has_univ_metavar(); }
    bool has_fvar() const { return m_ptr->has_fvar(); }
    bool has_param_univ() const { return m_ptr->has_param_univ(); }

    operator expr_ptr() const { return m_ptr; }
    expr_cell * raw() const { return m_ptr; }

    friend expr mk_bvar(unsigned idx);
    friend expr mk_fvar(name const & n);
    friend expr mk_sort(level const & l);
    friend expr mk_constant(name const & n, levels const & ls);
    friend expr mk_metavar(name const & n, name const & pp_n, expr const & t);
    friend expr mk_app(expr const & f, expr const & a);
    friend expr mk_binding(expr_kind k, name const & n, expr const & t, expr const & e, binder_info i);
    friend expr mk_let(name const & n, expr const & t, expr const & v, expr const & b);
    friend expr mk_lit(literal const & lit);
    friend expr mk_mdata(kvmap const & m, expr const & e);
    friend expr mk_proj(nat const & idx, expr const & e);
    friend bool is_eqp(expr const & a, expr const & b) { return a.m_ptr == b.m_ptr; }
    // TODO(Leo): delete
    friend expr mk_local(name const & n, name const & pp_n, expr const & t, binder_info bi);
    friend expr mk_quote(bool reflected, expr const & val);
};

SPECIALIZE_OPTIONAL_FOR_SMART_PTR(expr)

inline optional<expr> none_expr() { return optional<expr>(); }
inline optional<expr> some_expr(expr const & e) { return optional<expr>(e); }
inline optional<expr> some_expr(expr && e) { return optional<expr>(std::forward<expr>(e)); }

inline bool is_eqp(optional<expr> const & a, optional<expr> const & b) {
    return static_cast<bool>(a) == static_cast<bool>(b) && (!a || is_eqp(*a, *b));
}

/** \brief Bounded variables. They are encoded using de Bruijn's indices. */
class expr_bvar : public expr_cell {
    unsigned m_vidx; // de Bruijn index
    friend expr_cell;
    void dealloc();
public:
    expr_bvar(unsigned idx);
    unsigned get_vidx() const { return m_vidx; }
};

/** \brief (parametric) Constants. */
class expr_const : public expr_cell {
    name       m_name;
    levels     m_levels;
    friend expr_cell;
    void dealloc();
    expr_const(expr_const const &, levels const & new_levels); // for hash_consing
public:
    expr_const(name const & n, levels const & ls);
    name const & get_name() const { return m_name; }
    levels const & get_levels() const { return m_levels; }
};

/** \brief Composite expressions */
class expr_composite : public expr_cell {
protected:
    unsigned m_weight;
    unsigned m_depth;
    unsigned m_loose_bvar_range; /* dangling bound variables */
    friend unsigned get_weight(expr const & e);
    friend unsigned get_depth(expr const & e);
    friend unsigned get_loose_bvar_range(expr const & e);
    expr_composite(expr_composite const & src); // for hash_consing
public:
    expr_composite(expr_kind k, unsigned h, bool has_expr_mv, bool has_univ_mv, bool has_fvar,
                   bool has_param_univ, unsigned w, unsigned fv_range);
};

/** \brief Metavariables and local constants */
class expr_mlocal : public expr_composite {
protected:
    name   m_name;
    name   m_pp_name; // user facing name
    expr   m_type;
    friend expr_cell;
    void dealloc(buffer<expr_cell*> & todelete);
    expr_mlocal(expr_mlocal const &, expr const & new_type); // for hash_consing
public:
    expr_mlocal(bool is_meta, name const & n, name const & pp_n, expr const & t);
    name const & get_name() const { return m_name; }
    name const & get_pp_name() const { return m_pp_name; }
    expr const & get_type() const { return m_type; }
};

/** \brief expr_mlocal subclass for local constants. */
class expr_fvar : public expr_mlocal {
    binder_info m_bi;
    friend expr_cell;
    void dealloc(buffer<expr_cell*> & todelete);
    expr_fvar(expr_fvar const &, expr const & new_type); // for hash_consing
public:
    expr_fvar(name const & n, name const & pp_name, expr const & t, binder_info bi);
    binder_info get_info() const { return m_bi; }
};

/** \brief Applications */
class expr_app : public expr_composite {
    expr     m_fn;
    expr     m_arg;
    friend expr_cell;
    void dealloc(buffer<expr_cell*> & todelete);
    expr_app(expr_app const &, expr const & new_fn, expr const & new_arg); // for hash_consing
public:
    expr_app(expr const & fn, expr const & arg);
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
    binder(name const & n, expr const & t, binder_info bi):
        m_name(n), m_type(t), m_info(bi) {}
    name const & get_name() const { return m_name; }
    expr const & get_type() const { return m_type; }
    binder_info get_info() const { return m_info; }
    binder update_type(expr const & t) const { return binder(m_name, t, m_info); }
};

/** \brief Lambda and Pi expressions */
class expr_binding : public expr_composite {
    binder           m_binder;
    expr             m_body;
    friend class expr_cell;
    void dealloc(buffer<expr_cell*> & todelete);
    expr_binding(expr_binding const &, expr const & new_domain, expr const & new_body); // for hash_consing
public:
    expr_binding(expr_kind k, name const & n, expr const & t, expr const & e,
                 binder_info i);
    name const & get_name() const   { return m_binder.get_name(); }
    expr const & get_domain() const { return m_binder.get_type(); }
    expr const & get_body() const   { return m_body; }
    binder_info get_info() const { return m_binder.get_info(); }
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
    expr_let(expr_let const &, expr const & new_type, expr const & new_value, expr const & new_body); // for hash_consing
public:
    expr_let(name const & n, expr const & t, expr const & v, expr const & b);
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
    expr_sort(expr_sort const &, level const & new_level); // for hash_consing
public:
    expr_sort(level const & l);
    ~expr_sort();
    level const & get_level() const { return m_level; }
};

enum class literal_kind { Nat, String };

class literal : public object_ref {
    explicit literal(object * o):object_ref(o) { inc(o); }
public:
    explicit literal(char const * v);
    explicit literal(unsigned v);
    explicit literal(mpz const & v);
    literal(literal const & other):object_ref(other) {}
    literal(literal && other):object_ref(other) {}
    literal & operator=(literal const & other) { object_ref::operator=(other); return *this; }
    literal & operator=(literal && other) { object_ref::operator=(other); return *this; }

    literal_kind kind() const { return static_cast<literal_kind>(cnstr_tag(raw())); }
    string_ref const & get_string() const { lean_assert(kind() == literal_kind::String); return static_cast<string_ref const &>(cnstr_obj_ref(*this, 0)); }
    nat const & get_nat() const { lean_assert(kind() == literal_kind::Nat); return static_cast<nat const &>(cnstr_obj_ref(*this, 0)); }
    friend bool operator==(literal const & a, literal const & b);
    friend bool operator<(literal const & a, literal const & b);

    void serialize(serializer & s) const { s.write_object(raw()); }
    static literal deserialize(deserializer & d) { return literal(d.read_object()); }
};

inline bool operator!=(literal const & a, literal const & b) { return !(a == b); }
inline serializer & operator<<(serializer & s, literal const & l) { l.serialize(s); return s; }
inline literal read_literal(deserializer & d) { return literal::deserialize(d); }
inline deserializer & operator>>(deserializer & d, literal & l) { l = read_literal(d); return d; }

class expr_lit : public expr_cell {
    literal m_lit;
    friend expr_cell;
    void dealloc();
public:
    expr_lit(literal const & lit);
    ~expr_lit();
    literal const & get_literal() const { return m_lit; }
};

class expr_mdata : public expr_composite {
    kvmap m_data;
    expr  m_expr;
    friend expr_cell;
    void dealloc(buffer<expr_cell*> & todelete);
public:
    expr_mdata(kvmap const & m, expr const & e);
    ~expr_mdata() {}
    kvmap const & get_data() const { return m_data; }
    expr const & get_expr() const { return m_expr; }
};

class expr_proj : public expr_composite {
    nat  m_idx;
    expr m_expr;
    friend expr_cell;
    void dealloc(buffer<expr_cell*> & todelete);
public:
    expr_proj(nat const & idx, expr const & e);
    ~expr_proj() {}
    nat const & get_idx() const { return m_idx; }
    expr const & get_expr() const { return m_expr; }
};

// =======================================
// Testers
inline bool is_bvar(expr_ptr e)        { return e->kind() == expr_kind::BVar; }
inline bool is_fvar(expr_ptr e)        { return e->kind() == expr_kind::FVar; }
inline bool is_constant(expr_ptr e)    { return e->kind() == expr_kind::Constant; }
inline bool is_metavar(expr_ptr e)     { return e->kind() == expr_kind::MVar; }
inline bool is_app(expr_ptr e)         { return e->kind() == expr_kind::App; }
inline bool is_lambda(expr_ptr e)      { return e->kind() == expr_kind::Lambda; }
inline bool is_pi(expr_ptr e)          { return e->kind() == expr_kind::Pi; }
inline bool is_let(expr_ptr e)         { return e->kind() == expr_kind::Let; }
inline bool is_sort(expr_ptr e)        { return e->kind() == expr_kind::Sort; }
inline bool is_lit(expr_ptr e)         { return e->kind() == expr_kind::Lit; }
inline bool is_mdata(expr_ptr e)       { return e->kind() == expr_kind::MData; }
inline bool is_proj(expr_ptr e)        { return e->kind() == expr_kind::Proj; }
inline bool is_binding(expr_ptr e)     { return is_lambda(e) || is_pi(e); }

bool is_atomic(expr const & e);
bool is_arrow(expr const & t);
/** \brief Return true iff \c e is a metavariable or an application of a metavariable */
bool is_metavar_app(expr const & e);
// =======================================

// =======================================
// Constructors
expr mk_lit(literal const & lit);
expr mk_mdata(kvmap const & d, expr const & e);
expr mk_proj(nat const & idx, expr const & e);
inline expr mk_proj(unsigned idx, expr const & e) { return mk_proj(nat(idx), e); }
expr mk_bvar(unsigned idx);
expr mk_fvar(name const & n);
inline expr BVar(unsigned idx) { return mk_bvar(idx); }
expr mk_constant(name const & n, levels const & ls);
inline expr mk_constant(name const & n) { return mk_constant(n, levels()); }
inline expr Const(name const & n) { return mk_constant(n); }
expr mk_metavar(name const & n, expr const & t);
expr mk_metavar(name const & n, name const & pp_n, expr const & t);
expr mk_app(expr const & f, expr const & a);
expr mk_app(expr const & f, unsigned num_args, expr const * args);
expr mk_app(unsigned num_args, expr const * args);
inline expr mk_app(std::initializer_list<expr> const & l) {
    return mk_app(l.size(), l.begin());
}
inline expr mk_app(buffer<expr> const & args) { return mk_app(args.size(), args.data()); }
inline expr mk_app(expr const & f, buffer<expr> const & args) {
    return mk_app(f, args.size(), args.data());
}
expr mk_app(expr const & f, list<expr> const & args);
expr mk_rev_app(expr const & f, unsigned num_args, expr const * args);
expr mk_rev_app(unsigned num_args, expr const * args);
inline expr mk_rev_app(buffer<expr> const & args) { return mk_rev_app(args.size(), args.data()); }
inline expr mk_rev_app(expr const & f, buffer<expr> const & args) {
    return mk_rev_app(f, args.size(), args.data());
}
expr mk_binding(expr_kind k, name const & n, expr const & t, expr const & e, binder_info i = mk_binder_info());
inline expr mk_lambda(name const & n, expr const & t, expr const & e, binder_info i = mk_binder_info()) {
    return mk_binding(expr_kind::Lambda, n, t, e, i);
}
inline expr mk_pi(name const & n, expr const & t, expr const & e, binder_info i = mk_binder_info()) {
    return mk_binding(expr_kind::Pi, n, t, e, i);
}
expr mk_let(name const & n, expr const & t, expr const & v, expr const & b);
expr mk_sort(level const & l);

expr mk_Prop();
expr mk_Type();

bool is_default_var_name(name const & n);
expr mk_arrow(expr const & t, expr const & e);
inline expr operator>>(expr const & t, expr const & e) { return mk_arrow(t, e); }

// Auxiliary
inline expr mk_app(expr const & e1, expr const & e2, expr const & e3) {
    return mk_app({e1, e2, e3});
}
inline expr mk_app(expr const & e1, expr const & e2, expr const & e3, expr const & e4) {
    return mk_app({e1, e2, e3, e4});
}
inline expr mk_app(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5) {
    return mk_app({e1, e2, e3, e4, e5});
}

// =======================================

// =======================================
// Casting (these functions are only needed for low-level code)
inline expr_lit *         to_lit(expr_ptr e)        { lean_assert(is_lit(e));         return static_cast<expr_lit*>(e); }
inline expr_mdata *       to_mdata(expr_ptr e)      { lean_assert(is_mdata(e));       return static_cast<expr_mdata*>(e); }
inline expr_proj *        to_proj(expr_ptr e)       { lean_assert(is_proj(e));        return static_cast<expr_proj*>(e); }
inline expr_bvar *        to_bvar(expr_ptr e)       { lean_assert(is_bvar(e));        return static_cast<expr_bvar*>(e); }
inline expr_fvar *        to_fvar(expr_ptr e)       { lean_assert(is_fvar(e));        return static_cast<expr_fvar*>(e); }
inline expr_const *       to_constant(expr_ptr e)   { lean_assert(is_constant(e));    return static_cast<expr_const*>(e); }
inline expr_app *         to_app(expr_ptr e)        { lean_assert(is_app(e));         return static_cast<expr_app*>(e); }
inline expr_binding *     to_binding(expr_ptr e)    { lean_assert(is_binding(e));     return static_cast<expr_binding*>(e); }
inline expr_sort *        to_sort(expr_ptr e)       { lean_assert(is_sort(e));        return static_cast<expr_sort*>(e); }
inline expr_mlocal *      to_metavar(expr_ptr e)    { lean_assert(is_metavar(e));     return static_cast<expr_mlocal*>(e); }
inline expr_let *         to_let(expr_ptr e)        { lean_assert(is_let(e));         return static_cast<expr_let*>(e); }
// =======================================


// =======================================
// Accessors
inline unsigned        get_rc(expr_ptr e)                { return e->get_rc(); }
inline bool            is_shared(expr_ptr e)             { return get_rc(e) > 1; }
inline literal const & lit_value(expr_ptr e)             { return to_lit(e)->get_literal(); }
expr lit_type(expr_ptr e);
inline expr const &    mdata_expr(expr_ptr e)            { return to_mdata(e)->get_expr(); }
inline kvmap const &   mdata_data(expr_ptr e)            { return to_mdata(e)->get_data(); }
inline expr const &    proj_expr(expr_ptr e)             { return to_proj(e)->get_expr(); }
inline nat const &     proj_idx(expr_ptr e)              { return to_proj(e)->get_idx(); }
inline unsigned        bvar_idx(expr_ptr e)              { return to_bvar(e)->get_vidx(); }
inline bool            is_bvar(expr_ptr e, unsigned i)   { return is_bvar(e) && bvar_idx(e) == i; }
inline name const &    fvar_name(expr_ptr e)             { return to_fvar(e)->get_name(); }
inline level const &   sort_level(expr_ptr e)            { return to_sort(e)->get_level(); }
inline name const &    const_name(expr_ptr e)            { return to_constant(e)->get_name(); }
inline levels const &  const_levels(expr_ptr e)          { return to_constant(e)->get_levels(); }
inline expr const &    app_fn(expr_ptr e)                { return to_app(e)->get_fn(); }
inline expr const &    app_arg(expr_ptr e)               { return to_app(e)->get_arg(); }
inline name const &    binding_name(expr_ptr e)          { return to_binding(e)->get_name(); }
inline expr const &    binding_domain(expr_ptr e)        { return to_binding(e)->get_domain(); }
inline expr const &    binding_body(expr_ptr e)          { return to_binding(e)->get_body(); }
inline binder_info binding_info(expr_ptr e)      { return to_binding(e)->get_info(); }
inline binder const &  binding_binder(expr_ptr e)        { return to_binding(e)->get_binder(); }
inline name const &    let_name(expr_ptr e)              { return to_let(e)->get_name(); }
inline expr const &    let_type(expr_ptr e)              { return to_let(e)->get_type(); }
inline expr const &    let_value(expr_ptr e)             { return to_let(e)->get_value(); }
inline expr const &    let_body(expr_ptr e)              { return to_let(e)->get_body(); }


inline bool is_constant(expr const & e, name const & n) { return is_constant(e) && const_name(e) == n; }
inline bool has_metavar(expr const & e) { return e.has_metavar(); }
inline bool has_expr_metavar(expr const & e) { return e.has_expr_metavar(); }
inline bool has_univ_metavar(expr const & e) { return e.has_univ_metavar(); }
/** \brief Similar to \c has_expr_metavar, but ignores metavariables occurring in local constant types.
    It also returns the meta-variable application found in \c e.
*/
optional<expr> has_expr_metavar_strict(expr const & e);
inline bool has_fvar(expr const & e) { return e.has_fvar(); }
inline bool has_param_univ(expr const & e) { return e.has_param_univ(); }
unsigned get_weight(expr const & e);
unsigned get_depth(expr const & e);
/** \brief Return \c R s.t. the de Bruijn index of all loose bound variables
     occurring in \c e is in the interval <tt>[0, R)</tt>. */
inline unsigned get_loose_bvar_range(expr const & e) {
    switch (e.kind()) {
    case expr_kind::BVar:                           return bvar_idx(e) + 1;
    case expr_kind::Constant: case expr_kind::Sort: return 0;
    case expr_kind::Quote:                          return 0;
    case expr_kind::Lit:                            return 0;
    default:                                        return static_cast<expr_composite*>(e.raw())->m_loose_bvar_range;
    }
}
/** \brief Return true iff the given expression has loose bound variables. */
inline bool has_loose_bvars(expr const & e) { return get_loose_bvar_range(e) > 0; }
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
expr update_binding(expr const & e, expr const & new_domain, expr const & new_body, binder_info bi);
expr update_mlocal(expr const & e, expr const & new_type);
expr update_local(expr const & e, expr const & new_type, binder_info bi);
expr update_local(expr const & e, binder_info bi);
expr update_sort(expr const & e, level const & new_level);
expr update_constant(expr const & e, levels const & new_levels);
expr update_let(expr const & e, expr const & new_type, expr const & new_value, expr const & new_body);
expr update_mdata(expr const & e, expr const & t);
expr update_proj(expr const & e, expr const & t);
// =======================================


// =======================================
// Loose bound variable management

/** \brief Return true iff \c e contains the loose bound variable <tt>(var i)</tt>. */
bool has_loose_bvar(expr const & e, unsigned i);

/**
   \brief Lower the loose bound variables >= s in \c e by \c d. That is, a loose bound variable <tt>(var i)</tt> s.t.
   <tt>i >= s</tt> is mapped into <tt>(var i-d)</tt>.

   \pre s >= d */
expr lower_loose_bvars(expr const & e, unsigned s, unsigned d);
expr lower_loose_bvars(expr const & e, unsigned d);

/** \brief Lift loose bound variables >= s in \c e by d. */
expr lift_loose_bvars(expr const & e, unsigned s, unsigned d);
expr lift_loose_bvars(expr const & e, unsigned d);
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



/* ------ LEGACY CODE -------------
   The following API is to support legacy code
   -------------------------------- */

// TODO(Leo): delete
class expr_quote : public expr_cell {
    bool m_reflected;
    expr m_value;
    friend class expr_cell;
    void dealloc(buffer<expr_cell*> & todelete);
public:
    expr_quote(bool r, expr const & v);
    ~expr_quote() {}
    bool is_reflected() const { return m_reflected; }
    expr const & get_value() const { return m_value; }
};

inline bool is_var(expr_ptr e) { return is_bvar(e); }
inline bool is_local(expr_ptr e) { return is_fvar(e); }
inline bool is_mlocal(expr_ptr e) { return is_metavar(e) || is_local(e); }
inline bool is_quote(expr_ptr e)       { return e->kind() == expr_kind::Quote; }
inline unsigned var_idx(expr_ptr e) { return bvar_idx(e); }
inline bool is_var(expr_ptr e, unsigned i) { return is_bvar(e, i); }
inline expr_bvar *        to_var(expr_ptr e)        { return to_bvar(e); }
inline expr_mlocal *      to_mlocal(expr_ptr e)     { lean_assert(is_mlocal(e));      return static_cast<expr_mlocal*>(e); }
inline expr_fvar *      to_local(expr_ptr e)     { return to_fvar(e); }
inline expr_quote *       to_quote(expr_ptr e)      { lean_assert(is_quote(e));       return static_cast<expr_quote*>(e); }

inline name const &   mlocal_name(expr_ptr e)  { return to_mlocal(e)->get_name(); }
inline expr const &   mlocal_type(expr_ptr e)  { return to_mlocal(e)->get_type(); }
inline name const &   mlocal_pp_name(expr_ptr e) { return to_mlocal(e)->get_pp_name(); }
inline binder_info local_info(expr_ptr e) { return to_local(e)->get_info(); }
inline expr mk_var(unsigned idx) { return mk_bvar(idx); }
inline expr Var(unsigned idx) { return mk_bvar(idx); }
expr mk_quote(bool reflected, expr const & val);
expr mk_local(name const & n, name const & pp_n, expr const & t, binder_info bi);
inline expr mk_local(name const & n, expr const & t) { return mk_local(n, n, t, mk_binder_info()); }
inline expr mk_local(name const & n, expr const & t, binder_info bi) {
    return mk_local(n, n, t, bi);
}
inline expr Local(name const & n, expr const & t, binder_info bi = mk_binder_info()) {
    return mk_local(n, t, bi);
}
inline bool has_local(expr const & e) { return has_fvar(e); }

inline bool quote_is_reflected(expr const & e) { return to_quote(e)->is_reflected(); }
inline expr const & quote_value(expr const & e) { return to_quote(e)->get_value(); }

}
