/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "kernel/environment.h"
#include "library/expr_pair.h"

namespace lean {
/* If \c n is not in \c env, then return \c. Otherwise, find the first j >= idx s.t.
   n.append_after(j) is not in \c env. */
name mk_unused_name(environment const & env, name const & n, unsigned & idx);

/* If \c n is not in \c env, then return \c. Otherwise, find the first j >= 1 s.t.
   n.append_after(j) is not in \c env. */
name mk_unused_name(environment const & env, name const & n);

/** \brief Return the "arity" of the given type. The arity is the number of nested pi-expressions. */
unsigned get_arity(expr type);

optional<expr> is_optional_param(expr const & e);

optional<expr_pair> is_auto_param(expr const & e);

/** brief Return a name that does not appear in `lp_names`. */
name mk_fresh_lp_name(names const & lp_names);

/** \brief Return true iff \c n occurs in \c m */
bool occurs(expr const & n, expr const & m);
/** \brief Return true iff there is a constant named \c n in \c m. */
bool occurs(name const & n, expr const & m);

/** \brief Return true iff t is a constant named f_name or an application of the form (f_name a_1 ... a_k) */
bool is_app_of(expr const & t, name const & f_name);
/** \brief Return true iff t is a constant named f_name or an application of the form (f_name a_1 ... a_nargs) */
bool is_app_of(expr const & t, name const & f_name, unsigned nargs);

/** \brief If type is of the form (auto_param A p) or (opt_param A v), return A. Otherwise, return type. */
expr consume_auto_opt_param(expr const & type);

/** \brief Unfold constant \c e or constant application (i.e., \c e is of the form (f ....),
    where \c f is a constant */
optional<expr> unfold_term(environment const & env, expr const & e);
/** \brief If \c e is of the form <tt>(f a_1 ... a_n)</tt>, where \c f is
    a non-opaque definition, then unfold \c f, and beta reduce.
    Otherwise, return none. */
optional<expr> unfold_app(environment const & env, expr const & e);

/** \brief Reduce (if possible) universe level by 1.
    \pre is_not_zero(l) */
optional<level> dec_level(level const & l);

bool has_punit_decls(environment const & env);
bool has_pprod_decls(environment const & env);
bool has_eq_decls(environment const & env);
bool has_heq_decls(environment const & env);
bool has_and_decls(environment const & env);

/** \brief Return true iff \c n is an inductive predicate, i.e., an inductive datatype that is in Prop.

    \remark If \c env does not have Prop (i.e., Type.{0} is not impredicative), then this method always return false. */
bool is_inductive_predicate(environment const & env, name const & n);

/** \brief Return true iff \c n is an inductive type with a recursor with an extra level parameter. */
bool can_elim_to_type(environment const & env, name const & n);

/** \brief Store in `result` the constructors of the given inductive datatype.
    \remark this procedure does nothing if `n` is not an inductive datatype. */
void get_constructor_names(environment const & env, name const & n, buffer<name> & result);

/** \brief If \c e is a constructor application, or a definition that wraps a
    constructor application, then return the name of the constructor.
    Otherwise, return none. */
optional<name> is_constructor_app_ext(environment const & env, expr const & e);

/** \brief Store in \c result a bit-vector indicating which fields of the constructor \c n are
    (computationally) relevant.
    \pre inductive::is_intro_rule(env, n) */
void get_constructor_relevant_fields(environment const & env, name const & n, buffer<bool> & result);

/** Return the number of constructors of the given inductive datatype */
unsigned get_num_constructors(environment const & env, name const & n);

/** \brief Return the index (position) of the given constructor in the inductive datatype declaration.
    \pre inductive::is_intro_rule(env, n) */
unsigned get_constructor_idx(environment const & env, name const & n);

/** \brief Given a constructor name, return the associated inductive type name.

    \pre inductive::is_intro_rule(env, ctor_name) */
name get_constructor_inductive_type(environment const & env, name const & ctor_name);

/** \brief Return the universe where inductive datatype resides
    \pre \c ind_type is of the form <tt>Pi (a_1 : A_1) (a_2 : A_2[a_1]) ..., Type.{lvl}</tt> */
level get_datatype_level(environment const & env, expr const & ind_type);

/** \brief "Consume" Pi-type `type`. This procedure creates free variables based on the domain of `type` using `lctx`,
    and store them in telescope and updates  . If `binfo` is provided, then the free variables are annotated with
    the given `binder_info`, otherwise the procedure uses the one attached in the domain.
    The procedure returns the "body" of type. */
expr to_telescope(local_ctx & lctx, name_generator & ngen, expr const & type, buffer<expr> & telescope, optional<binder_info> const & binfo = optional<binder_info>());

/** \brief Similar to previous procedure, but uses whnf to check whether `type` reduces to `Pi` or not. */
expr to_telescope(environment const & env, local_ctx & lctx, name_generator & ngen, expr type, buffer<expr> & telescope, optional<binder_info> const & binfo = optional<binder_info>());

/** \brief Update the result sort of the given type */
expr update_result_sort(expr t, level const & l);

expr instantiate_lparam (expr const & e, name const & p, level const & l);

expr mk_true();
bool is_true(expr const & e);
expr mk_true_intro();

bool is_and(expr const & e, expr & arg1, expr & arg2);
bool is_and(expr const & e);
expr mk_and(expr const & a, expr const & b);

expr mk_unit(level const & l);
expr mk_unit_mk(level const & l);
expr mk_unit();
expr mk_unit_mk();

expr mk_unit(level const & l, bool prop);
expr mk_unit_mk(level const & l, bool prop);

expr mk_nat_type();
bool is_nat_type(expr const & e);
expr mk_nat_zero();
expr mk_nat_one();
expr mk_nat_bit0(expr const & e);
expr mk_nat_bit1(expr const & e);
expr mk_nat_add(expr const & e1, expr const & e2);

expr mk_int_type();
bool is_int_type(expr const & e);

expr mk_char_type();

bool is_ite(expr const & e, expr & c, expr & H, expr & A, expr & t, expr & f);
bool is_ite(expr const & e);

bool is_iff(expr const & e);
bool is_iff(expr const & e, expr & lhs, expr & rhs);
expr mk_iff(expr const & lhs, expr const & rhs);
expr mk_iff_refl(expr const & a);

expr mk_propext(expr const & lhs, expr const & rhs, expr const & iff_pr);

/** \brief Return true iff \c e is a term of the form (eq.rec ....) */
bool is_eq_rec_core(expr const & e);
/** \brief Return true iff \c e is a term of the form (eq.rec ....) */
bool is_eq_rec(expr const & e);
/** \brief Return true iff \c e is a term of the form (eq.drec ....) */
bool is_eq_drec(expr const & e);

bool is_eq(expr const & e);
bool is_eq(expr const & e, expr & lhs, expr & rhs);
bool is_eq(expr const & e, expr & A, expr & lhs, expr & rhs);
/** \brief Return true iff \c e is of the form (eq A a a) */
bool is_eq_a_a(expr const & e);

bool is_heq(expr const & e);
bool is_heq(expr const & e, expr & lhs, expr & rhs);
bool is_heq(expr const & e, expr & A, expr & lhs, expr & B, expr & rhs);

expr mk_false();
expr mk_empty();

bool is_false(expr const & e);
bool is_empty(expr const & e);

bool is_or(expr const & e);
bool is_or(expr const & e, expr & A, expr & B);

/** \brief Return true if \c e is of the form <tt>(not arg)</tt> or <tt>arg -> false</tt>, and store \c arg in \c a.
     Return false otherwise */
bool is_not(expr const & e, expr & a);
inline bool is_not(expr const & e) { expr a; return is_not(e, a); }
/** \brief Extends is_not to handle (lhs ≠ rhs). In the new case, it stores (lhs = rhs) in \c a. */
bool is_not_or_ne(expr const & e, expr & a);
expr mk_not(expr const & e);

/** \brief Returns none if \c e is not an application with at least two arguments.
    Otherwise it returns <tt>app_fn(app_fn(e))</tt>. */
optional<expr> get_binary_op(expr const & e);
optional<expr> get_binary_op(expr const & e, expr & arg1, expr & arg2);

/** \brief Makes n-ary (right-associative) application. */
expr mk_nary_app(expr const & op, buffer<expr> const & nary_args);
expr mk_nary_app(expr const & op, unsigned num_nary_args, expr const * nary_args);

expr mk_bool();
expr mk_bool_true();
expr mk_bool_false();
expr to_bool_expr(bool b);

/* Similar to is_head_beta, but ignores annotations around the function. */
bool is_annotated_head_beta(expr const & t);
/* Similar to head_beta_reduce, but also reduces annotations around the function. */
expr annotated_head_beta_reduce(expr const & t);

bool is_exists(expr const & e, expr & A, expr & p);
bool is_exists(expr const & e);

expr try_eta(expr const & e);
expr beta_reduce(expr t);
expr eta_reduce(expr t);
expr beta_eta_reduce(expr t);

enum class implicit_infer_kind { Implicit, RelaxedImplicit };

/** \brief Infer implicit parameter annotations for the first \c nparams using mode
    specified by \c k. */
expr infer_implicit_params(expr const & type, unsigned nparams, implicit_infer_kind k);


/** Given an inductive datatype named \c n, return a recursor for \c n that supports dependent elimination
    even if \c n is an inductive predicate. */
name get_dep_recursor(environment const & env, name const & n);

/** Given an inductive datatype named \c n, return a cases_on recursor \c n that supports dependent elimination
    even if \c n is an inductive predicate. */
name get_dep_cases_on(environment const & env, name const & n);

/** We generate auxiliary unsafe definitions for regular recursive definitions.
    The auxiliary unsafe definition has a clear runtime cost execution model, and
    we use it in the VM and code generators. This function returns an auxiliary unsafe definition for the given name. */
name mk_unsafe_rec_name(name const & n);

/** Return some(n') if \c n is a name created using mk_unsafe_rec_name(n') */
optional<name> is_unsafe_rec_name(name const & n);

LEAN_EXPORT std::string const & get_version_string();

expr const & extract_mdata(expr const &);

optional<expr> to_optional_expr(obj_arg o);

void initialize_library_util();
void finalize_library_util();
}
