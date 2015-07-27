/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/type_checker.h"
#include "library/expr_pair.h"

namespace lean {
bool is_simp_relation(environment const & env, expr const & e, expr & rel, expr & lhs, expr & rhs);
/** \brief Given (H : e), return a list of (h_i : e_i) where e_i can be viewed as
    a "conditional" rewriting rule. Any equivalence relation registered using
    the relation_manager is considered.
*/
list<expr_pair> to_ceqvs(type_checker & tc, expr const & e, expr const & H);
bool is_ceqv(type_checker & tc, expr e);
bool is_permutation_ceqv(environment const & env, expr e);
}
