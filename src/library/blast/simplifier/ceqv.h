/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/tmp_type_context.h"
#include "library/expr_pair.h"

namespace lean {
bool is_simp_relation(environment const & env, expr const & e, expr & rel, expr & lhs, expr & rhs);
/** \brief Given (H : e), return a list of (h_i : e_i) where e_i can be viewed as
    a "conditional" rewriting rule. Any equivalence relation registered using
    the relation_manager is considered.
*/
list<expr_pair> to_ceqvs(tmp_type_context & tctx, expr const & e, expr const & H);
bool is_ceqv(tmp_type_context & tctx, expr e);
bool is_permutation_ceqv(environment const & env, expr e);
}
