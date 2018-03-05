/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#pragma once
#include "kernel/environment.h"
#include "kernel/find_fn.h"
#include "library/inductive_compiler/ginductive_decl.h"

namespace lean {

enum class ginductive_kind { BASIC, MUTUAL, NESTED };

environment register_ginductive_decl(environment const & env, ginductive_decl const & decl, ginductive_kind k);

optional<ginductive_kind> is_ginductive(environment const & env, name const & ind_name);

/* \brief Returns the names of the introduction rules for the inductive type \e ind_name. */
list<name> get_ginductive_intro_rules(environment const & env, name const & ind_name);

/* \brief Returns the name of the inductive type if \e ir_name is indeed an introduction rule. */
optional<name> is_ginductive_intro_rule(environment const & env, name const & ir_name);

/* \brief Returns the number of parameters for the given inductive type \e ind_name. */
unsigned get_ginductive_num_params(environment const & env, name const & ind_name);

/* \brief Returns the number of indices for the given inductive type \e ind_name. */
unsigned get_ginductive_num_indices(environment const & env, name const & ind_name);

/* \brief Returns the names of all types that are mutually inductive with \e ind_name */
list<name> get_ginductive_mut_ind_names(environment const & env, name const & ind_name);

/* Normalize \c e until it is in weak head normal form OR the head is a ginductive datatype. */
expr whnf_ginductive(type_context_old & ctx, expr const & e);

/* Normalize \c e until it is in weak head normal form OR the head is a ginductive intro rule (aka constructor) */
expr whnf_gintro_rule(type_context_old & ctx, expr const & e);

/* Normalize \c e until it is in weak head normal form OR the head is a ginductive intro rule (aka constructor)
   or generalized inductive datatype. */
expr whnf_ginductive_gintro_rule(type_context_old & ctx, expr const & e);

/* Similar to is_constructor_app, but takes generalized introduction rules into account. */
optional<name> is_gintro_rule_app(environment const & env, expr const & e);

/* \brief Returns the offset of a simulated introduction rule.

Example:

inductive foo
| mk1 : list foo -> foo
| mk2 : foo

0. foo.basic.foo_mk1
1. foo.basic.foo_mk2
2. foo.basic.list_nil  ==> list.nil
3. foo.basic.list_cons  ==> list.cons

ir_to_simulated_ir_offset("list.nil") = 0
ir_to_simulated_ir_offset("list.cons") = 0
ir_to_simulated_ir_offset("foo.basic.foo_mk1") = 0
ir_to_simulated_ir_offset("foo.basic.foo_mk2") = 0
ir_to_simulated_ir_offset("foo.basic.list_nil") = 2
ir_to_simulated_ir_offset("foo.basic.list_cons") = 2
*/
unsigned ir_to_simulated_ir_offset(environment const & env, name basic_ir_name);

/* \brief Returns the range, i.e. (start, number), of the simulated inductive name corresponding to the idxs.
Example:

inductive foo
| mk1 : list foo -> foo
| mk2 : foo

0. foo.basic.foo_mk1
1. foo.basic.foo_mk2
2. foo.basic.list_nil  ==> list.nil
3. foo.basic.list_cons  ==> list.cons

ind_indices_to_ir_range("list", {}) = (0, 2)
ind_indices_to_ir_range("foo.basic", {sum.inl ()}) = (0, 2)
ind_indices_to_ir_range("foo.basic", {sum.inr ()}) = (2, 2)
*/
pair<unsigned, unsigned> ind_indices_to_ir_range(environment const & env, name const & basic_ind_name, buffer<expr> const & idxs);

/* \brief A ginductive type is "inner" if it was not entered directly by the user. */
bool is_ginductive_inner_ind(environment const & env, name const & ind_name);

/* \brief A ginductive introduction rule is "inner" if it introduces an "inner" ginductive tye. */
bool is_ginductive_inner_ir(environment const & env, name const & ir_name);

bool is_ginductive_pack(environment const & env, name const & n);
bool is_ginductive_unpack(environment const & env, name const & n);

/* \brief Returns the names of all mutual ginductive types */
list<name> get_ginductive_all_mutual_inds(environment const & env);

/* \brief Returns the names of all nested ginductive types */
list<name> get_ginductive_all_nested_inds(environment const & env);

void initialize_inductive_compiler_ginductive();
void finalize_inductive_compiler_ginductive();
}
