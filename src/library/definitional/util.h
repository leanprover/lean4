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

/** \brief Return the universe where inductive datatype resides
    \pre \c ind_type is of the form <tt>Pi (a_1 : A_1) (a_2 : A_2[a_1]) ..., Type.{lvl}</tt>
*/
level get_datatype_level(expr ind_type);

expr instantiate_univ_param (expr const & e, name const & p, level const & l);
}
