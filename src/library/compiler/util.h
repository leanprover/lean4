/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "runtime/pair_ref.h"
#include "runtime/list_ref.h"
#include "util/name_hash_set.h"
#include "kernel/expr.h"
#include "kernel/type_checker.h"
#include "library/constants.h"
#include "library/util.h"
#include "library/elab_environment.h"

namespace lean {
/* Return the `some(n)` if `I` is the name of an inductive datatype that contains only constructors with 0-arguments,
   and `n` is `1`, `2` or `4`, i.e., the number of bytes that should be used to store a value of this type.
   Otherwise, it return `none`.
   Remark: if the inductive datatype `I` has more than `2^32` constructors (very unlikely), the result is also `none`. */
optional<unsigned> is_enum_type(environment const & env, name const & I);

optional<expr> to_uint_type(unsigned nbytes);

/* A "compiler" declaration `x := e` */
typedef pair_ref<name, expr> comp_decl;
typedef list_ref<comp_decl> comp_decls;

void trace_comp_decl(comp_decl const & d);
void trace_comp_decls(comp_decls const & ds);

unsigned get_num_nested_lambdas(expr e);

bool is_lcnf_atom(expr const & e);

expr elim_trivial_let_decls(expr const & e);

bool has_inline_attribute(elab_environment const & env, name const & n);
bool has_noinline_attribute(elab_environment const & env, name const & n);
bool has_inline_if_reduce_attribute(elab_environment const & env, name const & n);
bool has_never_extract_attribute(elab_environment const & env, name const & n);

expr unfold_macro_defs(elab_environment const & env, expr const & e);

/* Return true if the given argument is mdata relevant to the compiler

   Remark: we currently don't keep any metadata in the compiler. */
inline bool is_lc_mdata(expr const &) { return false; }

bool is_cases_on_recursor(elab_environment const & env, name const & n);
/* We defined the "arity" of a cases_on application as the sum:
   ```
     number of inductive parameters +
     1 +    // motive
     number of inductive indices +
     1 +    // major premise
     number of constructors // cases_on has a minor premise for each constructor
   ```
   \pre is_cases_on_recursor(env, c) */
unsigned get_cases_on_arity(elab_environment const & env, name const & c, bool before_erasure = true);
/* Return the `inductive_val` for the cases_on constant `c`. */
inline inductive_val get_cases_on_inductive_val(elab_environment const & env, name const & c) {
    lean_assert(is_cases_on_recursor(env, c));
    return env.get(c.get_prefix()).to_inductive_val();
}
inline inductive_val get_cases_on_inductive_val(elab_environment const & env, expr const & c) {
    lean_assert(is_constant(c));
    return get_cases_on_inductive_val(env, const_name(c));
}
inline bool is_cases_on_app(elab_environment const & env, expr const & e) {
    expr const & fn = get_app_fn(e);
    return is_constant(fn) && is_cases_on_recursor(env, const_name(fn));
}
/* Return the major premise of a cases_on-application.
   \pre is_cases_on_app(env, c) */
expr get_cases_on_app_major(elab_environment const & env, expr const & c, bool before_erasure = true);
unsigned get_cases_on_major_idx(elab_environment const & env, name const & c, bool before_erasure = true);
/* Return the pair `(b, e)` such that `i in [b, e)` is argument `i` in a `c` cases_on
   application is a minor premise.
   \pre is_cases_on_recursor(env, c) */
pair<unsigned, unsigned> get_cases_on_minors_range(elab_environment const & env, name const & c, bool before_erasure = true);

inline bool is_quot_primitive(elab_environment const & env, name const & n) {
    optional<constant_info> info = env.find(n);
    return info && info->is_quot();
}

inline bool is_lc_unreachable_app(expr const & e) { return is_app_of(e, get_lc_unreachable_name(), 1); }
inline bool is_lc_proof_app(expr const & e) { return is_app_of(e, get_lc_proof_name(), 1); }

expr mk_lc_unreachable(type_checker::state & s, local_ctx const & lctx, expr const & type);

inline name mk_join_point_name(name const & n) { return name(n, "_join"); }
bool is_join_point_name(name const & n);
/* Pseudo "do" joinpoints are used to implement a temporary HACK. See `visit_let` method at `lcnf.cpp` */
inline name mk_pseudo_do_join_point_name(name const & n) { return name(n, "__do_jp"); }
bool is_pseudo_do_join_point_name(name const & n);

/* Create an auxiliary names for a declaration that saves the result of the compilation
   after step simplification. */
inline name mk_cstage1_name(name const & decl_name) {
    return name(decl_name, "_cstage1");
}

/* Create an auxiliary names for a declaration that saves the result of the compilation
   after step erasure. */
inline name mk_cstage2_name(name const & decl_name) {
    return name(decl_name, "_cstage2");
}

/* Set `used[i] = true` if `fvars[i]` occurs in `e` */
void mark_used_fvars(expr const & e, buffer<expr> const & fvars, buffer<bool> & used);

/* Return true if `e` contains the free variable `fvar` */
bool has_fvar(expr const & e, expr const & fvar);

expr replace_fvar(expr const & e, expr const & fvar, expr const & new_term);

void sort_fvars(local_ctx const & lctx, buffer<expr> & fvars);

/* Return the "code" size for `e` */
unsigned get_lcnf_size(elab_environment const & env, expr e);

// =======================================
// Auxiliary expressions for erasure.
// We use them after we have erased proofs and unnecessary type information.
// `enf` stands for "erasure normal form". It is LCNF after erasure.

/* Create a neutral expression used at ENF */
expr mk_enf_neutral();
/* Create an unreachable expression used at ENF */
expr mk_enf_unreachable();
expr mk_enf_object_type();
expr mk_enf_neutral_type();
/* "Void" type used in LLNF. Remark: the ENF types neutral and object are also used in LLNF. */
expr mk_llnf_void_type();

bool is_enf_neutral(expr const & e);
bool is_enf_unreachable(expr const & e);
bool is_enf_object_type(expr const & e);
bool is_llnf_void_type(expr const & e);
bool is_llnf_unboxed_type(expr const & type);

/* Return (some idx) iff inductive datatype `I_name` is safe, has only one constructor,
   and this constructor has only one relevant field, `idx` is the field position. */
optional<unsigned> has_trivial_structure(environment const & env, name const & I_name);

expr mk_runtime_type(type_checker::state & st, local_ctx const & lctx, expr e);

// =======================================

/* Return true if `n` is the name of a type with builtin support in the code generator. */
bool is_runtime_builtin_type(name const & n);
inline bool is_runtime_builtin_type(expr const & e) {
    return is_constant(e) && is_runtime_builtin_type(const_name(e));
}

/* Return true if `n` is the name of a type that is treated as a scalar type by the code generator. */
bool is_runtime_scalar_type(name const & n);

bool is_irrelevant_type(type_checker::state & st, local_ctx lctx, expr const & type);
bool is_irrelevant_type(environment const & env, expr const & type);

void collect_used(expr const & e, name_hash_set & S);
/* Return true iff `e` contains a free variable in `s` */
bool depends_on(expr const & e, name_hash_set const & s);

bool is_stage2_decl(elab_environment const & env, name const & n);
elab_environment register_stage1_decl(elab_environment const & env, name const & n, names const & ls, expr const & t, expr const & v);
elab_environment register_stage2_decl(elab_environment const & env, name const & n, expr const & t, expr const & v);

/* Return `some n` iff `e` is of the forms `expr.lit (literal.nat n)` or `uint*.of_nat (expr.lit (literal.nat n))` */
optional<nat> get_num_lit_ext(expr const & e);
inline bool is_morally_num_lit(expr const & e) { return static_cast<bool>(get_num_lit_ext(e)); }

/* Return `some n` if `c` is of the form `fix_core_n` where `n in [1, 6]`.
   Remark: this function is assuming the core library contains `fix_core_1` ... `fix_core_6` definitions. */
optional<unsigned> is_fix_core(name const & c);
/* Return the `fix_core_n` constant, and `none` if `n` is not in `[1, 6]`.
   Remark: this function is assuming the core library contains `fix_core_1` ... `fix_core_6` definitions.
   Remark: this function assumes universe levels have already been erased. */
optional<expr> mk_enf_fix_core(unsigned n);

bool lcnf_check_let_decls(elab_environment const & env, comp_decl const & d);
bool lcnf_check_let_decls(elab_environment const & env, comp_decls const & ds);

// =======================================
/* Similar to `type_checker::eta_expand`, but preserves LCNF */
expr lcnf_eta_expand(type_checker::state & st, local_ctx lctx, expr e);

// =======================================
// UInt and USize helper functions

expr mk_usize_type();
bool is_usize_type(expr const & e);
optional<unsigned> is_builtin_scalar(expr const & type);
optional<unsigned> is_enum_type(environment const & env, expr const & type);

// =======================================

extern "C" uint8 lean_is_matcher(object* env, object* n);

inline bool is_matcher(elab_environment const & env, name const & n) {
    return lean_is_matcher(env.to_obj_arg(), n.to_obj_arg());
}

inline bool is_matcher_app(elab_environment const & env, expr const & e) {
  expr const & f = get_app_fn(e);
  return is_constant(f) && is_matcher(env, const_name(f));
}

/*
  Return true if the given expression must be in eta-expanded form during compilation.
  Example: constructors, `casesOn` applications must always be in eta-expanded form.
*/
bool must_be_eta_expanded(elab_environment const & env, expr const & e);

void initialize_compiler_util();
void finalize_compiler_util();
}
