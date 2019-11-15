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
#include "runtime/hash.h"
#include "util/name.h"
#include "util/nat.h"
#include "util/buffer.h"
#include "util/kvmap.h"
#include "util/list_fn.h"
#include "util/format.h"
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

/* Expression literal values */
enum class literal_kind { Nat, String };
class literal : public object_ref {
    explicit literal(b_obj_arg o, bool b):object_ref(o, b) {}
public:
    explicit literal(char const * v);
    explicit literal(unsigned v);
    explicit literal(mpz const & v);
    explicit literal(nat const & v);
    literal():literal(0u) {}
    literal(literal const & other):object_ref(other) {}
    literal(literal && other):object_ref(other) {}
    literal & operator=(literal const & other) { object_ref::operator=(other); return *this; }
    literal & operator=(literal && other) { object_ref::operator=(other); return *this; }

    static literal_kind kind(object * o) { return static_cast<literal_kind>(cnstr_tag(o)); }
    literal_kind kind() const { return kind(raw()); }
    string_ref const & get_string() const { lean_assert(kind() == literal_kind::String); return static_cast<string_ref const &>(cnstr_get_ref(*this, 0)); }
    nat const & get_nat() const { lean_assert(kind() == literal_kind::Nat); return static_cast<nat const &>(cnstr_get_ref(*this, 0)); }
    friend bool operator==(literal const & a, literal const & b);
    friend bool operator<(literal const & a, literal const & b);

    void serialize(serializer & s) const { s.write_object(raw()); }
    static literal deserialize(deserializer & d) { return literal(d.read_object(), true); }
};
inline bool operator!=(literal const & a, literal const & b) { return !(a == b); }
inline serializer & operator<<(serializer & s, literal const & l) { l.serialize(s); return s; }
inline literal read_literal(deserializer & d) { return literal::deserialize(d); }
inline deserializer & operator>>(deserializer & d, literal & l) { l = read_literal(d); return d; }

/* =======================================
   Expressions

inductive expr
| bvar  : nat → expr          -- bound variables
| fvar  : name → expr         -- free variables
| mvar  : name → expr         -- meta variables
| sort  : level → expr
| const : name → list level → expr
| app   : expr → expr → expr
| lam   : name → binder_info → expr → expr → expr
| pi    : name → binder_info → expr → expr → expr
| elet  : name → expr → expr → expr → expr
| lit   : literal → expr
| mdata : kvmap → expr → expr
| proj  : name → nat → expr → expr
*/
enum class expr_kind { BVar, FVar, MVar, Sort, Const, App, Lambda, Pi, Let, Lit, MData, Proj };
class expr : public object_ref {
    explicit expr(object_ref && o):object_ref(o) {}

    friend expr mk_lit(literal const & lit);
    friend expr mk_mdata(kvmap const & d, expr const & e);
    friend expr mk_proj(name const & s, nat const & idx, expr const & e);
    friend expr mk_bvar(nat const & idx);
    friend expr mk_mvar(name const & n);
    friend expr mk_const(name const & n, levels const & ls);
    friend expr mk_app(expr const & f, expr const & a);
    friend expr mk_sort(level const & l);
    friend expr mk_lambda(name const & n, expr const & t, expr const & e, binder_info bi);
    friend expr mk_pi(name const & n, expr const & t, expr const & e, binder_info bi);
    friend expr mk_let(name const & n, expr const & t, expr const & v, expr const & b);
    /* legacy constructors */
    friend expr mk_local(name const & n, name const & pp_n, expr const & t, binder_info bi);
public:
    expr();
    expr(expr const & other):object_ref(other) {}
    expr(expr && other):object_ref(other) {}
    explicit expr(b_obj_arg o, bool b):object_ref(o, b) {}
    explicit expr(obj_arg o):object_ref(o) {}
    static expr_kind kind(object * o) { return static_cast<expr_kind>(cnstr_tag(o)); }
    expr_kind kind() const { return kind(raw()); }

    expr & operator=(expr const & other) { object_ref::operator=(other); return *this; }
    expr & operator=(expr && other) { object_ref::operator=(other); return *this; }

    friend bool is_eqp(expr const & e1, expr const & e2) { return e1.raw() == e2.raw(); }
    void serialize(serializer & s) const { s.write_object(raw()); }
    static expr deserialize(deserializer & d) { return expr(d.read_object(), true); }
};

typedef list_ref<expr> exprs;
typedef pair<expr, expr> expr_pair;

inline serializer & operator<<(serializer & s, expr const & e) { e.serialize(s); return s; }
inline serializer & operator<<(serializer & s, exprs const & es) { es.serialize(s); return s; }
inline expr read_expr(deserializer & d) { return expr::deserialize(d); }
inline exprs read_exprs(deserializer & d) { return read_list_ref<expr>(d); }
inline deserializer & operator>>(deserializer & d, expr & e) { e = read_expr(d); return d; }

inline optional<expr> none_expr() { return optional<expr>(); }
inline optional<expr> some_expr(expr const & e) { return optional<expr>(e); }
inline optional<expr> some_expr(expr && e) { return optional<expr>(std::forward<expr>(e)); }

inline bool is_eqp(optional<expr> const & a, optional<expr> const & b) {
    return static_cast<bool>(a) == static_cast<bool>(b) && (!a || is_eqp(*a, *b));
}

unsigned hash(expr const & e);
bool has_expr_mvar(expr const & e);
bool has_univ_mvar(expr const & e);
inline bool has_mvar(expr const & e) { return has_expr_mvar(e) || has_univ_mvar(e); }
bool has_fvar(expr const & e);
bool has_univ_param(expr const & e);
unsigned expr_get_loose_bvar_range(object * e);
inline unsigned get_loose_bvar_range(expr const & e) { return expr_get_loose_bvar_range(e.raw()); }

struct expr_hash { unsigned operator()(expr const & e) const { return hash(e); } };
struct expr_pair_hash {
    unsigned operator()(expr_pair const & p) const { return hash(hash(p.first), hash(p.second)); }
};
struct expr_pair_eq {
    bool operator()(expr_pair const & p1, expr_pair const & p2) const { return p1.first == p2.first && p1.second == p2.second; }
};

// =======================================
// Testers
static expr_kind expr_kind_core(object * o) { return static_cast<expr_kind>(cnstr_tag(o)); }
inline bool is_bvar(expr const & e)        { return e.kind() == expr_kind::BVar; }
inline bool is_fvar_core(object * o)       { return expr_kind_core(o) == expr_kind::FVar; }
inline bool is_fvar(expr const & e)        { return e.kind() == expr_kind::FVar; }
inline bool is_const(expr const & e)       { return e.kind() == expr_kind::Const; }
inline bool is_mvar(expr const & e)        { return e.kind() == expr_kind::MVar; }
inline bool is_app(expr const & e)         { return e.kind() == expr_kind::App; }
inline bool is_lambda(expr const & e)      { return e.kind() == expr_kind::Lambda; }
inline bool is_pi(expr const & e)          { return e.kind() == expr_kind::Pi; }
inline bool is_let(expr const & e)         { return e.kind() == expr_kind::Let; }
inline bool is_sort(expr const & e)        { return e.kind() == expr_kind::Sort; }
inline bool is_lit(expr const & e)         { return e.kind() == expr_kind::Lit; }
inline bool is_mdata(expr const & e)       { return e.kind() == expr_kind::MData; }
inline bool is_proj(expr const & e)        { return e.kind() == expr_kind::Proj; }
inline bool is_binding(expr const & e)     { return is_lambda(e) || is_pi(e); }

bool is_atomic(expr const & e);
bool is_arrow(expr const & t);
bool is_default_var_name(name const & n);
// =======================================

// =======================================
// Constructors
expr mk_lit(literal const & lit);
expr mk_mdata(kvmap const & d, expr const & e);
expr mk_proj(name const & s, nat const & idx, expr const & e);
inline expr mk_proj(name const & s, unsigned idx, expr const & e) { return mk_proj(s, nat(idx), e); }
expr mk_bvar(nat const & idx);
inline expr mk_bvar(unsigned idx) { return mk_bvar(nat(idx)); }
expr mk_fvar(name const & n);
expr mk_const(name const & n, levels const & ls);
inline expr mk_const(name const & n) { return mk_const(n, levels()); }
expr mk_mvar(name const & n);
expr mk_app(expr const & f, expr const & a);
expr mk_app(expr const & f, unsigned num_args, expr const * args);
expr mk_app(unsigned num_args, expr const * args);
inline expr mk_app(std::initializer_list<expr> const & l) { return mk_app(l.size(), l.begin()); }
inline expr mk_app(buffer<expr> const & args) { return mk_app(args.size(), args.data()); }
inline expr mk_app(expr const & f, buffer<expr> const & args) { return mk_app(f, args.size(), args.data()); }
expr mk_app(expr const & f, list<expr> const & args);
inline expr mk_app(expr const & e1, expr const & e2, expr const & e3) { return mk_app({e1, e2, e3}); }
inline expr mk_app(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({e1, e2, e3, e4}); }
inline expr mk_app(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5) { return mk_app({e1, e2, e3, e4, e5}); }
expr mk_rev_app(expr const & f, unsigned num_args, expr const * args);
expr mk_rev_app(unsigned num_args, expr const * args);
inline expr mk_rev_app(buffer<expr> const & args) { return mk_rev_app(args.size(), args.data()); }
inline expr mk_rev_app(expr const & f, buffer<expr> const & args) { return mk_rev_app(f, args.size(), args.data()); }
expr mk_lambda(name const & n, expr const & t, expr const & e, binder_info bi = mk_binder_info());
expr mk_pi(name const & n, expr const & t, expr const & e, binder_info bi = mk_binder_info());
inline expr mk_binding(expr_kind k, name const & n, expr const & t, expr const & e, binder_info bi = mk_binder_info()) {
    return k == expr_kind::Pi ? mk_pi(n, t, e, bi) : mk_lambda(n, t, e, bi);
}
expr mk_arrow(expr const & t, expr const & e);
expr mk_let(name const & n, expr const & t, expr const & v, expr const & b);
expr mk_sort(level const & l);
expr mk_Prop();
expr mk_Type();
// =======================================

// =======================================
// Accessors
inline literal const & lit_value(expr const & e)             { lean_assert(is_lit(e)); return static_cast<literal const &>(cnstr_get_ref(e, 0)); }
inline bool is_nat_lit(expr const & e)                       { return is_lit(e) && lit_value(e).kind() == literal_kind::Nat; }
inline bool is_string_lit(expr const & e)                    { return is_lit(e) && lit_value(e).kind() == literal_kind::String; }
expr const & lit_type(expr const & e);
inline kvmap const &   mdata_data(expr const & e)            { lean_assert(is_mdata(e)); return static_cast<kvmap const &>(cnstr_get_ref(e, 0)); }
inline expr const &    mdata_expr(expr const & e)            { lean_assert(is_mdata(e)); return static_cast<expr const &>(cnstr_get_ref(e, 1)); }
inline name const &    proj_sname(expr const & e)            { lean_assert(is_proj(e)); return static_cast<name const &>(cnstr_get_ref(e, 0)); }
inline nat const &     proj_idx(expr const & e)              { lean_assert(is_proj(e)); return static_cast<nat const &>(cnstr_get_ref(e, 1)); }
inline expr const &    proj_expr(expr const & e)             { lean_assert(is_proj(e)); return static_cast<expr const &>(cnstr_get_ref(e, 2)); }
inline nat const &     bvar_idx(expr const & e)              { lean_assert(is_bvar(e)); return static_cast<nat const &>(cnstr_get_ref(e, 0)); }
inline bool            is_bvar(expr const & e, unsigned i)   { return is_bvar(e) && bvar_idx(e) == i; }
inline name const &    fvar_name_core(object * o)            { lean_assert(is_fvar_core(o)); return static_cast<name const &>(cnstr_get_ref(o, 0)); }
inline name const &    fvar_name(expr const & e)             { lean_assert(is_fvar(e)); return static_cast<name const &>(cnstr_get_ref(e, 0)); }
inline level const &   sort_level(expr const & e)            { lean_assert(is_sort(e)); return static_cast<level const &>(cnstr_get_ref(e, 0)); }
inline name const &    mvar_name(expr const & e)             { lean_assert(is_mvar(e)); return static_cast<name const &>(cnstr_get_ref(e, 0)); }
inline name const &    const_name(expr const & e)            { lean_assert(is_const(e)); return static_cast<name const &>(cnstr_get_ref(e, 0)); }
inline levels const &  const_levels(expr const & e)          { lean_assert(is_const(e)); return static_cast<levels const &>(cnstr_get_ref(e, 1)); }
inline bool is_const(expr const & e, name const & n)         { return is_const(e) && const_name(e) == n; }
inline expr const &    app_fn(expr const & e)                { lean_assert(is_app(e));   return static_cast<expr const &>(cnstr_get_ref(e, 0)); }
inline expr const &    app_arg(expr const & e)               { lean_assert(is_app(e));   return static_cast<expr const &>(cnstr_get_ref(e, 1)); }
inline name const &    binding_name(expr const & e)          { lean_assert(is_binding(e)); return static_cast<name const &>(cnstr_get_ref(e, 0)); }
inline expr const &    binding_domain(expr const & e)        { lean_assert(is_binding(e)); return static_cast<expr const &>(cnstr_get_ref(e, 1)); }
inline expr const &    binding_body(expr const & e)          { lean_assert(is_binding(e)); return static_cast<expr const &>(cnstr_get_ref(e, 2)); }
binder_info binding_info(expr const & e);
inline name const &    let_name(expr const & e)              { lean_assert(is_let(e)); return static_cast<name const &>(cnstr_get_ref(e, 0)); }
inline expr const &    let_type(expr const & e)              { lean_assert(is_let(e)); return static_cast<expr const &>(cnstr_get_ref(e, 1)); }
inline expr const &    let_value(expr const & e)             { lean_assert(is_let(e)); return static_cast<expr const &>(cnstr_get_ref(e, 2)); }
inline expr const &    let_body(expr const & e)              { lean_assert(is_let(e)); return static_cast<expr const &>(cnstr_get_ref(e, 3)); }
inline bool            is_shared(expr const & e)             { return !is_exclusive(e.raw()); }
//

// =======================================
// Update
expr update_app(expr const & e, expr const & new_fn, expr const & new_arg);
expr update_binding(expr const & e, expr const & new_domain, expr const & new_body);
expr update_binding(expr const & e, expr const & new_domain, expr const & new_body, binder_info bi);
expr update_sort(expr const & e, level const & new_level);
expr update_const(expr const & e, levels const & new_levels);
expr update_let(expr const & e, expr const & new_type, expr const & new_value, expr const & new_body);
expr update_mdata(expr const & e, expr const & new_e);
expr update_proj(expr const & e, expr const & new_e);
// =======================================


/** \brief Given \c e of the form <tt>(...(f a1) ... an)</tt>, store a1 ... an in args.
    If \c e is not an application, then nothing is stored in args.

    It returns the f. */
expr const & get_app_args(expr const & e, buffer<expr> & args);
/** \brief Similar to \c get_app_args, but stores at most num args.
    Examples:
    1) get_app_args_at_most(f a b c, 2, args);
    stores {b, c} in args and returns (f a)

    2) get_app_args_at_most(f a b c, 4, args);
    stores {a, b, c} in args and returns f */
expr const & get_app_args_at_most(expr const & e, unsigned num, buffer<expr> & args);

/** \brief Similar to \c get_app_args, but arguments are stored in reverse order in \c args.
    If e is of the form <tt>(...(f a1) ... an)</tt>, then the procedure stores [an, ..., a1] in \c args. */
expr const & get_app_rev_args(expr const & e, buffer<expr> & args);
/** \brief Given \c e of the form <tt>(...(f a_1) ... a_n)</tt>, return \c f. If \c e is not an application, then return \c e. */
expr const & get_app_fn(expr const & e);
/** \brief Given \c e of the form <tt>(...(f a_1) ... a_n)</tt>, return \c n. If \c e is not an application, then return 0. */
unsigned get_app_num_args(expr const & e);

/** \brief Return true iff \c e is a metavariable or an application of a metavariable */
inline bool is_mvar_app(expr const & e) { return is_mvar(get_app_fn(e)); }


// =======================================
// Loose bound variable management

/** \brief Return true iff the given expression has loose bound variables. */
inline bool has_loose_bvars(expr const & e) { return get_loose_bvar_range(e) > 0; }

/** \brief Return true iff \c e contains the loose bound variable <tt>(var i)</tt>. */
bool has_loose_bvar(expr const & e, unsigned i);

/** \brief Lower the loose bound variables >= s in \c e by \c d. That is, a loose bound variable <tt>(var i)</tt> s.t.
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

// =======================================
// Low level (raw) printing
std::ostream & operator<<(std::ostream & out, expr const & e);
// =======================================

void initialize_expr();
void finalize_expr();

/* ================= LEGACY ============== */
inline bool has_expr_metavar(expr const & e) { return has_expr_mvar(e); }
inline bool has_univ_metavar(expr const & e) { return has_univ_mvar(e); }
inline bool has_metavar(expr const & e) { return has_mvar(e); }
inline bool has_param_univ(expr const & e) { return has_univ_param(e); }
inline bool is_var(expr const & e) { return is_bvar(e); }
inline bool is_var(expr const & e, unsigned idx) { return is_bvar(e, idx); }
inline bool is_metavar(expr const & e) { return is_mvar(e); }
inline bool is_metavar_app(expr const & e) { return is_mvar_app(e); }
inline expr mk_metavar(name const & n) { return mk_mvar(n); }
expr mk_local(name const & n, name const & pp_n, expr const & t, binder_info bi);
inline expr mk_local(name const & n, expr const & t) { return mk_local(n, n, t, mk_binder_info()); }
inline expr mk_local(name const & n, expr const & t, binder_info bi) { return mk_local(n, n, t, bi); }
inline bool is_local(expr const & e) { return is_fvar(e); }
inline name const & local_name(expr const & e) { lean_assert(is_local(e)); return static_cast<name const &>(cnstr_get_ref(e, 0)); }
inline name const & local_pp_name(expr const & e) { lean_assert(is_local(e)); return static_cast<name const &>(cnstr_get_ref(e, 1)); }
inline expr const & local_type(expr const & e) { lean_assert(is_local(e)); return static_cast<expr const &>(cnstr_get_ref(e, 2)); }
inline expr mk_constant(name const & n, levels const & ls) { return mk_const(n, ls); }
inline expr mk_constant(name const & n) { return mk_constant(n, levels()); }
inline bool is_constant(expr const & e) { return is_const(e); }
expr update_local(expr const & e, expr const & new_type, binder_info bi);
expr update_local(expr const & e, expr const & new_type);
expr update_local(expr const & e, binder_info bi);
binder_info local_info(expr const & e);
inline expr update_constant(expr const & e, levels const & new_levels) { return update_const(e, new_levels); }
/** \brief Similar to \c has_expr_metavar, but ignores metavariables occurring in local constant types.
    It also returns the meta-variable application found in \c e. */
optional<expr> has_expr_metavar_strict(expr const & e);
inline bool is_constant(expr const & e, name const & n) { return is_const(e, n); }
inline bool is_mlocal(expr const & e) { return is_local(e) || is_metavar(e); }
inline bool has_local(expr const & e) { return has_fvar(e); }
}
