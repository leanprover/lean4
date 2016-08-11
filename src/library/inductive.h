/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#pragma once
#include "kernel/environment.h"

/* This file presents a unified interface to all (user-facing) inductive types,
   which include the basic inductive types understood by the kernel, as well as
   mutual inductive types and nested inductive types that are compiled to basic
   inductive types behind the scenes.

   For every inductive type \e ind_name with intro rule \e ir_name recognized
   by this module, the following are guaranteed to be in the environment:

   1. <ind_name>.cases_on
   2. <ind_name>.size_of
   3. <ind_name>.has_size_of [instance]
   4. <ind_name>.<ir_name>.size_of_spec
   5. <ind_name>.<ir_name>.injective

   Suppose <ind_name> has parameters (A : Type) and <ir_name> has non-recursive arguments X
   and recursive arguments Y1 ... Yn.

   Then <ir_name>.size_of_spec is a proof of:

     forall C A x y1 ... yn,
       let k := size_of (<ir_name> A x y1 ... yn) in
         (k > size_of y1 -> ... -> k > size_of yn -> C) -> C


   and <ir_name>.injective is a proof of:

     forall C A x y x' y',
       <ir_name> A x y = <ir_name> A x' y' -> (x = x' -> y = y' -> C) -> C
*/

namespace lean {

/* \brief Returns true if \e ind_name is the name of a (user-facing) inductive type,
   whether it is basic, mutual, or nested. */
bool is_inductive(environment const & env, name const & ind_name);

/* \brief Returns the names of the introduction rules for the inductive type \e ind_name. */
list<name> get_intro_rule_names(environment const & env, name const & ind_name);

/* \brief Returns the name of the inductive type if \e ir_name is indeed an introduction rule. */
optional<name> is_intro_rule_name(environment const & env, name const & ir_name);

/* \brief Given the names of two introduction rules for the same inductive type, returns a
   proof that they are disjoint.

   \example For an inductive type \e I with parameters (A : Type) and two introduction rules
   c1 : X1 -> I and c2 : X2 -> I, returns a proof of the following theorem:

   forall (A : Type), forall (x1 : X1) (x2 : X2), @c1 A x1 = @c2 A x2 -> false.

   \remark When there are indices, the equality will need to be heterogenous.
*/
expr prove_intro_rules_disjoint(environment const & env, name const & ir_name1, name const & ir_name2);

/* \brief Returns the number of parameters for the given inductive type \e ind_name. */
unsigned get_inductive_num_params(environment const & env, name const & ind_name);

void initialize_library_inductive();
void finalize_library_inductive();
}
