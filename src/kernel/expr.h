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
#include "runtime/hash.h"
#include "runtime/buffer.h"
#include "util/name.h"
#include "util/nat.h"
#include "util/kvmap.h"
#include "util/list_fn.h"
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
    literal(literal && other):object_ref(std::move(other)) {}
    literal & operator=(literal const & other) { object_ref::operator=(other); return *this; }
    literal & operator=(literal && other) { object_ref::operator=(std::move(other)); return *this; }

    static literal_kind kind(object * o) { return static_cast<literal_kind>(cnstr_tag(o)); }
    literal_kind kind() const { return kind(raw()); }
    string_ref const & get_string() const { lean_assert(kind() == literal_kind::String); return static_cast<string_ref const &>(cnstr_get_ref(*this, 0)); }
    nat const & get_nat() const { lean_assert(kind() == literal_kind::Nat); return static_cast<nat const &>(cnstr_get_ref(*this, 0)); }
    bool is_zero() const { return kind() == literal_kind::Nat && get_nat().is_zero(); }
    friend bool operator==(literal const & a, literal const & b);
    friend bool operator<(literal const & a, literal const & b);
};
inline bool operator!=(literal const & a, literal const & b) { return !(a == b); }

/* =======================================
   Expressions

inductive Expr
| bvar    : Nat → Expr                                -- bound variables
| fvar    : Name → Expr                               -- free variables
| mvar    : Name → Expr                               -- meta variables
| sort    : Level → Expr                              -- Sort
| const   : Name → List Level → Expr                  -- constants
| app     : Expr → Expr → Expr                        -- application
| lam     : Name → BinderInfo → Expr → Expr → Expr    -- lambda abstraction
| forallE : Name → BinderInfo → Expr → Expr → Expr    -- (dependent) arrow
| letE    : Name → Expr → Expr → Expr → Expr          -- let expressions
| lit     : Literal → Expr                            -- literals
| mdata   : MData → Expr → Expr                       -- metadata
| proj    : Name → Nat → Expr → Expr                  -- projection
*/
enum class expr_kind { BVar, FVar, MVar, Sort, Const, App, Lambda, Pi, Let, Lit, MData, Proj };
class expr : public object_ref {
    explicit expr(object_ref && o):object_ref(o) {}

    friend expr mk_lit(literal const & lit);
    friend expr mk_mdata(kvmap const & d, expr const & e);
    friend expr mk_proj(name const & s, nat const & idx, expr const & e);
    friend expr mk_bvar(nat const & idx);
    friend expr mk_mvar(name const & n);
    friend expr mk_fvar(name const & n);
    friend expr mk_const(name const & n, levels const & ls);
    friend expr mk_app(expr const & f, expr const & a);
    friend expr mk_sort(level const & l);
    friend expr mk_lambda(name const & n, expr const & t, expr const & e, binder_info bi);
    friend expr mk_pi(name const & n, expr const & t, expr const & e, binder_info bi);
    friend expr mk_let(name const & n, expr const & t, expr const & v, expr const & b);
public:
    expr();
    expr(expr const & other):object_ref(other) {}
    expr(expr && other):object_ref(std::move(other)) {}
    explicit expr(b_obj_arg o, bool b):object_ref(o, b) {}
    explicit expr(obj_arg o):object_ref(o) {}
    static expr_kind kind(object * o) { return static_cast<expr_kind>(cnstr_tag(o)); }
    expr_kind kind() const { return kind(raw()); }

    expr & operator=(expr const & other) { object_ref::operator=(other); return *this; }
    expr & operator=(expr && other) { object_ref::operator=(std::move(other)); return *this; }

    friend bool is_eqp(expr const & e1, expr const & e2) { return e1.raw() == e2.raw(); }
};

typedef list_ref<expr> exprs;
typedef pair<expr, expr> expr_pair;

inline optional<expr> none_expr() { return optional<expr>(); }
inline optional<expr> some_expr(expr const & e) { return optional<expr>(e); }
inline optional<expr> some_expr(expr && e) { return optional<expr>(std::forward<expr>(e)); }

inline bool is_eqp(optional<expr> const & a, optional<expr> const & b) {
    return static_cast<bool>(a) == static_cast<bool>(b) && (!a || is_eqp(*a, *b));
}

inline uint64_t get_data(expr const & e) {
    return lean_ctor_get_uint64(e.raw(), lean_ctor_num_objs(e.raw())*sizeof(object*));
}
/* This is the implementation in Lean */
unsigned hash_core(expr const & e);
inline unsigned hash(expr const & e) {
    unsigned r = static_cast<unsigned>(get_data(e));
    lean_assert(r == hash_core(e));
    return r;
}
/* This is the implementation in Lean */
bool has_expr_mvar_core(expr const & e);
inline bool has_expr_mvar(expr const & e) {
    bool r = ((get_data(e) >> 41) & 1) == 1;
    lean_assert(r == has_expr_mvar_core(e)); // ensure the C++ implementation matches the Lean one.
    return r;
}
bool has_univ_mvar_core(expr const & e);
inline bool has_univ_mvar(expr const & e) {
    bool r = ((get_data(e) >> 42) & 1) == 1;
    lean_assert(r == has_univ_mvar_core(e)); // ensure the C++ implementation matches the Lean one.
    return r;
}
inline bool has_mvar(expr const & e) { return has_expr_mvar(e) || has_univ_mvar(e); }
/* This is the implementation in Lean */
bool has_fvar_core(expr const & e);
inline bool has_fvar(expr const & e) {
    bool r = ((get_data(e) >> 40) & 1) == 1;
    lean_assert(r == has_fvar_core(e)); // ensure the C++ implementation matches the Lean one.
    return r;
}
bool has_univ_param(expr const & e);
unsigned get_loose_bvar_range(expr const & e);

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
inline bool is_mvar_core(object * o)       { return expr_kind_core(o) == expr_kind::MVar; }
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
expr lit_type(literal const & e);
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
inline name const &    mvar_name_core(object * o)            { lean_assert(is_mvar_core(o)); return static_cast<name const &>(cnstr_get_ref(o, 0)); }
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

expr consume_type_annotations(expr const & e);

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
inline expr mk_constant(name const & n, levels const & ls) { return mk_const(n, ls); }
inline expr mk_constant(name const & n) { return mk_constant(n, levels()); }
inline bool is_constant(expr const & e) { return is_const(e); }
inline expr update_constant(expr const & e, levels const & new_levels) { return update_const(e, new_levels); }
/** \brief Similar to \c has_expr_metavar, but ignores metavariables occurring in local constant types.
    It also returns the meta-variable application found in \c e. */
optional<expr> has_expr_metavar_strict(expr const & e);
inline bool is_constant(expr const & e, name const & n) { return is_const(e, n); }

/* Like `is_exclusive`, but also consider unique MT references as unshared, which ensures we get
 * similar performance on the cmdline and server (more precisely, for either option value of
 * `internal.cmdlineSnapshots`). Note that as `e` is merely *borrowed* (e.g. from the mctx in
 * the case of `instantiate_mvars` where the performance issue resolved here manifested, #5614),
 * it is in fact possible that another thread could simultaneously add a new direct reference to
 * `e`, so it is not definitely unshared in all cases if the below check is true.
 *
 * However, as we use this predicate merely as a conservative heuristic for detecting
 * expressions that are unshared *within the expression tree* at hand, the approximation is
 * still correct in this case. Furthermore, as we only use it for deciding when to cache
 * results, it ultimately does not affect the correctness of the overall procedure in any case.
 * This should however be kept in mind if we start using `is_likely_unshared` in other contexts.
 */
inline bool is_likely_unshared(expr const & e) {
    return e.raw()->m_rc == 1 || e.raw()->m_rc == -1;
}

}
