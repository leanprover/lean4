/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
namespace lean {
/**
   \brief Add an new coercion in the given environment.

   There are three kinds of coercions supported
   1- From type C to type D
        type of f must have the form:
        {l1 ... lk} Pi (x1 : A1) ... (xn : An) (y: C.{l1 ... lk} x1 ... xn), D.{L1 ... Lr} t1 ... tm
            - C and D are constants.
            - l1 ... lk are universe level parameters
            - L1 ... Lr are universe level expressions
            - t1 ... tm are level expressions

   2- From type to sort
        type of f must have the form:
        {l1 ... lk}  Pi (x1 : A1) ... (xn : An) (y: C.{l1 ... lk} x1 ... xn) (x : A), B

   3- From type to function type
        type of f must have the form:
        {l1 ... lk}  Pi (x1 : A1) ... (xn : An) (y: C.{l1 ... lk} x1 ... xn), Type.{L}

   \pre \c f is a constant defined in \c env.
*/
environment add_coercion(environment const & env, expr const & f);
bool is_coercion(environment const & env, expr const & f);
list<expr_pair> get_coercions(environment const & env, expr const & from, expr const & from_type);
optional<expr> get_coercion(environment const & env, expr const & from, expr const & from_type, expr const & to_type);
optional<expr> get_coercion_to_sort(environment const & env, expr const & from, expr const & from_type);
optional<expr> get_coercion_to_fun(environment const & env, expr const & from, expr const & from_type);
}
