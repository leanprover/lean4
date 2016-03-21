/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
/** \brief Return true iff t is a constant named f_name or an application of the form (f_name a_1 ... a_k) */
bool is_app_of(expr const & t, name const & f_name);
/** \brief Return true iff t is a constant named f_name or an application of the form (f_name a_1 ... a_nargs) */
bool is_app_of(expr const & t, name const & f_name, unsigned nargs);

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

/** \brief Return true iff \c env has been configured with an impredicative and proof irrelevant Prop. */
bool is_standard(environment const & env);

bool has_poly_unit_decls(environment const & env);
bool has_eq_decls(environment const & env);
bool has_heq_decls(environment const & env);
bool has_prod_decls(environment const & env);
bool has_lift_decls(environment const & env);

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

    \remark If \c env does not have Prop (i.e., Type.{0} is not impredicative), then this method always return false.
*/
bool is_inductive_predicate(environment const & env, name const & n);

/** \brief Store in \c result the introduction rules of the given inductive datatype.
    \remark this procedure does nothing if \c n is not an inductive datatype.
*/
void get_intro_rule_names(environment const & env, name const & n, buffer<name> & result);

/** \brief If \c e is a constructor application, then return the name of the constructor.
    Otherwise, return none.
*/
optional<name> is_constructor_app(environment const & env, expr const & e);

/** \brief If \c e is a constructor application, or a definition that wraps a
    constructor application, then return the name of the constructor.
    Otherwise, return none.
*/
optional<name> is_constructor_app_ext(environment const & env, expr const & e);

/** \brief "Consume" Pi-type \c type. This procedure creates local constants based on the domain of \c type
    and store them in telescope. If \c binfo is provided, then the local constants are annoted with the given
    binder_info, otherwise the procedure uses the one attached in the domain.
    The procedure returns the "body" of type.
*/
expr to_telescope(expr const & type, buffer<expr> & telescope,
                  optional<binder_info> const & binfo = optional<binder_info>());

/** \brief "Consume" fun/lambda. This procedure creates local constants based on the arguments of \c e
    and store them in telescope. If \c binfo is provided, then the local constants are annoted with the given
    binder_info, otherwise the procedure uses the one attached to the arguments.
    The procedure returns the "body" of function.
*/
expr fun_to_telescope(expr const & e, buffer<expr> & telescope, optional<binder_info> const & binfo);

/** \brief Return the universe where inductive datatype resides
    \pre \c ind_type is of the form <tt>Pi (a_1 : A_1) (a_2 : A_2[a_1]) ..., Type.{lvl}</tt>
*/
level get_datatype_level(expr ind_type);

expr instantiate_univ_param (expr const & e, name const & p, level const & l);

/** \brief Create a format object for a type mismatch where typeof(v) (i.e., v_type) does not match
    expected type \c t. */
format pp_type_mismatch(formatter const & fmt, expr const & v, expr const & v_type, expr const & t);

void initialize_library_util();
void finalize_library_util();
}
