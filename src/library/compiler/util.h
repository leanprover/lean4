/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/pair_ref.h"
#include "util/list_ref.h"
#include "kernel/expr.h"
#include "kernel/type_checker.h"
#include "library/constants.h"
#include "library/util.h"

namespace lean {
/* A "compiler" declaration `x := e` */
typedef pair_ref<name, expr> comp_decl;
typedef list_ref<comp_decl> comp_decls;

/* If `e` is of the form `(fun x, t) a` return `head_beta_const_fn(t)` if `t` does not depend on `x`,
   and `e` otherwise. We also reduce `(fun x_1 ... x_n, x_i) a_1 ... a_n` into `a_[n-i-1]` */
expr cheap_beta_reduce(expr const & e);

bool is_lcnf_atom(expr const & e);

expr elim_trivial_let_decls(expr const & e);

bool has_inline_attribute(environment const & env, name const & n);
bool has_noinline_attribute(environment const & env, name const & n);

expr unfold_macro_defs(environment const & env, expr const & e);

/* Return true if the given argument is mdata relevant to the compiler

   Remark: we currently don't keep any metadata in the compiler. */
inline bool is_lc_mdata(expr const &) { return false; }

bool is_cases_on_recursor(environment const & env, name const & n);
/* We defined the "arity" of a cases_on application as the sum:
   ```
     number of inductive parameters +
     1 +    // motive
     number of inductive indices +
     1 +    // major premise
     number of constructors // cases_on has a minor premise for each constructor
   ```
   \pre is_cases_on_recursor(env, c) */
unsigned get_cases_on_arity(environment const & env, name const & c, bool before_erasure = true);
/* Return the `inductive_val` for the cases_on constant `c`. */
inline inductive_val get_cases_on_inductive_val(environment const & env, name const & c) {
    lean_assert(is_cases_on_recursor(env, c));
    return env.get(c.get_prefix()).to_inductive_val();
}
inline inductive_val get_cases_on_inductive_val(environment const & env, expr const & c) {
    lean_assert(is_constant(c));
    return get_cases_on_inductive_val(env, const_name(c));
}
inline bool is_cases_on_app(environment const & env, expr const & e) {
    expr const & fn = get_app_fn(e);
    return is_constant(fn) && is_cases_on_recursor(env, const_name(fn));
}
/* Return the major premise of a cases_on-application.
   \pre is_cases_on_app(env, c) */
expr get_cases_on_app_major(environment const & env, expr const & c, bool before_erasure = true);
unsigned get_cases_on_major_idx(environment const & env, name const & c, bool before_erasure = true);
/* Return the pair `(b, e)` such that `i in [b, e)` is argument `i` in a `c` cases_on
   application is a minor premise.
   \pre is_cases_on_recursor(env, c) */
pair<unsigned, unsigned> get_cases_on_minors_range(environment const & env, name const & c, bool before_erasure = true);

inline bool is_quot_primitive(environment const & env, name const & n) {
    optional<constant_info> info = env.find(n);
    return info && info->is_quot();
}

inline bool is_lc_unreachable_app(expr const & e) { return is_app_of(e, get_lc_unreachable_name(), 1); }
inline bool is_lc_proof_app(expr const & e) { return is_app_of(e, get_lc_proof_name(), 1); }

expr mk_lc_unreachable(type_checker::state & s, local_ctx const & lctx, expr const & type);

inline name mk_join_point_name(name const & n) { return name(n, "_join"); }
bool is_join_point_name(name const & n);

/* Create an auxiliary names for a declaration that saves the result of the compilation
   after step simplification. */
inline name mk_cstage1_name(name const & decl_name) {
    return name(decl_name, "_cstage1");
}

/* Set `used[i] = true` if `fvars[i]` occurs in `e` */
void mark_used_fvars(expr const & e, buffer<expr> const & fvars, buffer<bool> & used);

/* Return true if `e` contains the free variable `fvar` */
bool has_fvar(expr const & e, expr const & fvar);

expr replace_fvar(expr const & e, expr const & fvar, expr const & new_fvar);

/* Return the "code" size for `e` */
unsigned get_lcnf_size(environment const & env, expr e);

// =======================================
// Auxiliary expressions for erasure.
// We use them after we have erased proofs and unnecessary type information.
// `enf` stands for "erasure normal form". It is LCNF after erasure.

/* Create a neutral expression used at ENF */
expr mk_enf_neutral();
/* Create an unreachable expression used at ENF */
expr mk_enf_unreachable();
expr mk_enf_object_type();

bool is_enf_neutral(expr const & e);
bool is_enf_unreachable(expr const & e);
bool is_enf_object_type(expr const & e);

// =======================================

/* Return true if `n` is the name of a type with builtin support in the code generator. */
bool is_runtime_builtin_type(name const & n);

/* Return true if `n` is the name of a type that is treated as a scalar type by the code generator. */
bool is_runtime_scalar_type(name const & n);

void initialize_compiler_util();
void finalize_compiler_util();
}
