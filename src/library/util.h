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

/** \brief Return the universe level of the type of \c A.
    Throws an exception if the (relaxed) whnf of the type
    of A is not a sort. */
level get_level(abstract_type_context & ctx, expr const & A);

/** brief Return a name that does not appear in `lp_names`. */
name mk_fresh_lp_name(level_param_names const & lp_names);

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

/** \brief Return true iff \c n is the name of a recursive datatype in \c env.
    That is, it must be an inductive datatype AND contain a recursive constructor.

    \remark Records are inductive datatypes, but they are not recursive.

    \remark For mutually indutive datatypes, \c n is considered recursive
    if there is a constructor taking \c n. */
bool is_recursive_datatype(environment const & env, name const & n);

/** \brief Return true if \c n is a recursive *and* reflexive datatype.

    We say an inductive type T is reflexive if it contains at least one constructor that
    takes as an argument a function returning T. */
bool is_reflexive_datatype(abstract_type_context & tc, name const & n);

/** \brief Return true iff \c n is an inductive predicate, i.e., an inductive datatype that is in Prop.

    \remark If \c env does not have Prop (i.e., Type.{0} is not impredicative), then this method always return false. */
bool is_inductive_predicate(environment const & env, name const & n);

/** \brief Return true iff \c n is an inductive type with a recursor with an extra level parameter. */
bool can_elim_to_type(environment const & env, name const & n);

/** \brief Store in \c result the introduction rules of the given inductive datatype.
    \remark this procedure does nothing if \c n is not an inductive datatype. */
void get_intro_rule_names(environment const & env, name const & n, buffer<name> & result);

/** \brief If \c e is a constructor application, then return the name of the constructor.
    Otherwise, return none. */
optional<name> is_constructor_app(environment const & env, expr const & e);

/** \brief If \c e is a constructor application, or a definition that wraps a
    constructor application, then return the name of the constructor.
    Otherwise, return none. */
optional<name> is_constructor_app_ext(environment const & env, expr const & e);

/** \brief Store in \c result a bit-vector indicating which fields of the constructor \c n are
    (computationally) relevant.
    \pre inductive::is_intro_rule(env, n) */
void get_constructor_relevant_fields(environment const & env, name const & n, buffer<bool> & result);

/** \brief Return the index (position) of the given constructor in the inductive datatype declaration.
    \pre inductive::is_intro_rule(env, n) */
unsigned get_constructor_idx(environment const & env, name const & n);

/** Given a C.rec, each minor premise has n arguments, and some of these arguments are inductive
    hypotheses. This function return then number of inductive hypotheses for the minor premise associated with
    the constructor named \c n. */
unsigned get_num_inductive_hypotheses_for(environment const & env, name const & n);
/** Given a constructor \c n, store in the bitmask rec_mask[i] = true iff the i-th argument
    of \c n is recursive.

    \pre is_intro_rule(n) && rec_mask.empty() */
void get_constructor_rec_arg_mask(environment const & env, name const & n, buffer<bool> & rec_mask);
/** Combines get_num_inductive_hypotheses_for and get_constructor_rec_arg_mask */
unsigned get_num_inductive_hypotheses_for(environment const & env, name const & n, buffer<bool> & rec_mask);

/* Store in `rec_args` the recursive arguments of constructor application \c `e`.
   The result is false if `e` is not a constructor application.
   The unsigned value at rec_args represents the arity of the recursive argument.
   The value is only greater than zero for reflexive inductive datatypes such as:

      inductive inftree (A : Type)
      | leaf : A → inftree
      | node : (nat → inftree) → inftree
*/
bool get_constructor_rec_args(environment const & env, expr const & e, buffer<pair<expr, unsigned>> & rec_args);

/** \brief Given an expression \c e, return the number of arguments expected arguments.

    \remark This function computes the type of \c e, and then counts the number of nested
    Pi's. Weak-head-normal-forms are computed for the type of \c e.
    \remark The type and whnf are computed using \c tc. */
unsigned get_expect_num_args(abstract_type_context & ctx, expr e);

/** \brief "Consume" Pi-type \c type. This procedure creates local constants based on the domain of \c type
    and store them in telescope. If \c binfo is provided, then the local constants are annoted with the given
    binder_info, otherwise the procedure uses the one attached in the domain.
    The procedure returns the "body" of type. */
expr to_telescope(expr const & type, buffer<expr> & telescope,
                  optional<binder_info> const & binfo = optional<binder_info>());

/** \brief "Consume" fun/lambda. This procedure creates local constants based on the arguments of \c e
    and store them in telescope. If \c binfo is provided, then the local constants are annoted with the given
    binder_info, otherwise the procedure uses the one attached to the arguments.
    The procedure returns the "body" of function. */
expr fun_to_telescope(expr const & e, buffer<expr> & telescope, optional<binder_info> const & binfo);

/** \brief Similar to previous procedure, but puts \c type in whnf */
expr to_telescope(type_checker & ctx, expr type, buffer<expr> & telescope,
                  optional<binder_info> const & binfo = optional<binder_info>());

/** \brief Return the universe where inductive datatype resides
    \pre \c ind_type is of the form <tt>Pi (a_1 : A_1) (a_2 : A_2[a_1]) ..., Type.{lvl}</tt> */
level get_datatype_level(environment const & env, expr const & ind_type);

/** \brief Update the result sort of the given type */
expr update_result_sort(expr t, level const & l);

expr instantiate_univ_param (expr const & e, name const & p, level const & l);

expr mk_true();
bool is_true(expr const & e);
expr mk_true_intro();

bool is_and(expr const & e, expr & arg1, expr & arg2);
bool is_and(expr const & e);
expr mk_and(expr const & a, expr const & b);
expr mk_and_intro(abstract_type_context & ctx, expr const & Ha, expr const & Hb);
expr mk_and_elim_left(abstract_type_context & ctx, expr const & H);
expr mk_and_elim_right(abstract_type_context & ctx, expr const & H);

expr mk_unit(level const & l);
expr mk_unit_mk(level const & l);

expr mk_pprod(abstract_type_context & ctx, expr const & A, expr const & B);
expr mk_pprod_mk(abstract_type_context & ctx, expr const & a, expr const & b);
expr mk_pprod_fst(abstract_type_context & ctx, expr const & p);
expr mk_pprod_snd(abstract_type_context & ctx, expr const & p);

expr mk_unit(level const & l, bool prop);
expr mk_unit_mk(level const & l, bool prop);

expr mk_pprod(abstract_type_context & ctx, expr const & a, expr const & b, bool prop);
expr mk_pprod_mk(abstract_type_context & ctx, expr const & a, expr const & b, bool prop);
expr mk_pprod_fst(abstract_type_context & ctx, expr const & p, bool prop);
expr mk_pprod_snd(abstract_type_context & ctx, expr const & p, bool prop);

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

expr mk_eq(abstract_type_context & ctx, expr const & lhs, expr const & rhs);
expr mk_eq_refl(abstract_type_context & ctx, expr const & a);
expr mk_eq_symm(abstract_type_context & ctx, expr const & H);
expr mk_eq_trans(abstract_type_context & ctx, expr const & H1, expr const & H2);
expr mk_eq_subst(abstract_type_context & ctx, expr const & motive,
                 expr const & x, expr const & y, expr const & xeqy, expr const & h);
expr mk_eq_subst(abstract_type_context & ctx, expr const & motive, expr const & xeqy, expr const & h);

expr mk_congr_arg(abstract_type_context & ctx, expr const & f, expr const & H);

/** \brief Create an proof for x = y using subsingleton.elim (in standard mode) */
expr mk_subsingleton_elim(abstract_type_context & ctx, expr const & h, expr const & x, expr const & y);

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
/** \brief Return true iff \c e is of the form (eq A a a') where \c a and \c a' are definitionally equal */
bool is_eq_a_a(abstract_type_context & ctx, expr const & e);

expr mk_heq(abstract_type_context & ctx, expr const & lhs, expr const & rhs);
bool is_heq(expr const & e);
bool is_heq(expr const & e, expr & lhs, expr & rhs);
bool is_heq(expr const & e, expr & A, expr & lhs, expr & B, expr & rhs);

expr mk_cast(abstract_type_context & ctx, expr const & H, expr const & e);

expr mk_false();
expr mk_empty();

bool is_false(expr const & e);
bool is_empty(expr const & e);
/** \brief Return an element of type t given an element \c f : false */
expr mk_false_rec(abstract_type_context & ctx, expr const & f, expr const & t);

bool is_or(expr const & e);
bool is_or(expr const & e, expr & A, expr & B);

/** \brief Return true if \c e is of the form <tt>(not arg)</tt> or <tt>arg -> false</tt>, and store \c arg in \c a.
     Return false otherwise */
bool is_not(expr const & e, expr & a);
inline bool is_not(expr const & e) { expr a; return is_not(e, a); }
/** \brief Extends is_not to handle (lhs ≠ rhs). In the new case, it stores (lhs = rhs) in \c a. */
bool is_not_or_ne(expr const & e, expr & a);
expr mk_not(expr const & e);

/** \brief Create the term <tt>absurd e not_e : t</tt>. */
expr mk_absurd(abstract_type_context & ctx, expr const & t, expr const & e, expr const & not_e);

/** \brief Returns none if \c e is not an application with at least two arguments.
    Otherwise it returns <tt>app_fn(app_fn(e))</tt>. */
optional<expr> get_binary_op(expr const & e);
optional<expr> get_binary_op(expr const & e, expr & arg1, expr & arg2);

/** \brief Makes n-ary (right-associative) application. */
expr mk_nary_app(expr const & op, buffer<expr> const & nary_args);
expr mk_nary_app(expr const & op, unsigned num_nary_args, expr const * nary_args);

expr mk_bool();
expr mk_bool_tt();
expr mk_bool_ff();
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

enum class implicit_infer_kind { Implicit, RelaxedImplicit, None };

/** \brief Infer implicit parameter annotations for the first \c nparams using mode
    specified by \c k. */
expr infer_implicit_params(expr const & type, unsigned nparams, implicit_infer_kind k);


/** Given an inductive datatype named \c n, return a recursor for \c n that supports dependent elimination
    even if \c n is an inductive predicate. */
name get_dep_recursor(environment const & env, name const & n);

/** Given an inductive datatype named \c n, return a cases_on recursor \c n that supports dependent elimination
    even if \c n is an inductive predicate. */
name get_dep_cases_on(environment const & env, name const & n);

/** We generate auxiliary meta definitions for regular recursive definitions.
    The auxiliary meta definition has a clear runtime cost execution model, and
    we use it in the VM. This function returns an auxiliary meta definition for the given name. */
name mk_aux_meta_rec_name(name const & n);

/** Return some(n') if \c n is a name created using mk_aux_meta_rec_name(n') */
optional<name> is_aux_meta_rec_name(name const & n);

/** Convert an expression representing a `name` literal into a `name` object. */
optional<name> name_lit_to_name(expr const & name_lit);

/** Return (tactic unit) type */
expr mk_tactic_unit();

std::string const & get_version_string();

void initialize_library_util();
void finalize_library_util();
}
