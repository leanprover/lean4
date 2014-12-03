/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
bool has_unit_decls(environment const & env);
bool has_eq_decls(environment const & env);
bool has_heq_decls(environment const & env);
bool has_prod_decls(environment const & env);
/** \brief Return true iff \c n is the name of a recursive datatype in \c env.
    That is, it must be an inductive datatype AND contain a recursive constructor.

    \remark Records are inductive datatypes, but they are not recursive.

    \remark For mutually indutive datatypes, \c n is considered recursive
    if there is a constructor taking \c n.
*/
bool is_recursive_datatype(environment const & env, name const & n);

/** \brief Return true if \c n is a recursive *and* reflexive datatype.

    We say an inductive type T is reflexive if it contains at least one constructor that
    takes as an argument a function returning T.
*/
bool is_reflexive_datatype(type_checker & tc, name const & n);

/** \brief Return true iff \c n is an inductive predicate, i.e., an inductive datatype that is in Prop.

    \remark If \c env does not have Prop (i.e., Type.{0} is not impredicative), then this method always return false.
*/
bool is_inductive_predicate(environment const & env, name const & n);

/** \brief "Consume" Pi-type \c type. This method creates local constants based on the domain of \c type
    and store them in telescope. If \c binfo is provided, then the local constants are annoted with the given
    binder_info, otherwise the procedure uses the one attached in the domain.
    The procedure returns the "body" of type.
*/
expr to_telescope(name_generator & ngen, expr type, buffer<expr> & telescope,
                  optional<binder_info> const & binfo = optional<binder_info>());
/** \brief Similar to previous method, but puts \c type in whnf */
expr to_telescope(type_checker & tc, expr type, buffer<expr> & telescope,
                  optional<binder_info> const & binfo = optional<binder_info>());

/** \brief Return the universe where inductive datatype resides
    \pre \c ind_type is of the form <tt>Pi (a_1 : A_1) (a_2 : A_2[a_1]) ..., Type.{lvl}</tt>
*/
level get_datatype_level(expr ind_type);

expr instantiate_univ_param (expr const & e, name const & p, level const & l);

expr mk_true();
expr mk_and(expr const & a, expr const & b);
expr mk_and_intro(type_checker & tc, expr const & Ha, expr const & Hb);
expr mk_and_elim_left(type_checker & tc, expr const & H);
expr mk_and_elim_right(type_checker & tc, expr const & H);

expr mk_unit(level const & l);
expr mk_prod(type_checker & tc, expr const & A, expr const & B);
expr mk_pair(type_checker & tc, expr const & a, expr const & b);
expr mk_pr1(type_checker & tc, expr const & p);
expr mk_pr2(type_checker & tc, expr const & p);

expr mk_unit(level const & l, bool prop);
expr mk_prod(type_checker & tc, expr const & a, expr const & b, bool prop);
expr mk_pair(type_checker & tc, expr const & a, expr const & b, bool prop);
expr mk_pr1(type_checker & tc, expr const & p, bool prop);
expr mk_pr2(type_checker & tc, expr const & p, bool prop);

void initialize_definitional_util();
void finalize_definitional_util();
}
