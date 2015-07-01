/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include "util/lua.h"
#include "kernel/environment.h"
#include "library/expr_pair.h"
#include "library/io_state.h"

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

   \remark \c ios is used to report warning messages.

   \remark if persistent == true, then coercion is saved in .olean files
*/
environment add_coercion(environment const & env, io_state const & ios, name const & f, bool persistent = true);
/** \brief If \c f is a coercion, then return the name of the 'from-class' and the number of
    class parameters.
*/
optional<pair<name, unsigned>> is_coercion(environment const & env, name const & f);
optional<pair<name, unsigned>> is_coercion(environment const & env, expr const & f);
/** \brief Return true iff the given environment has coercions from a user-class named \c C. */
bool has_coercions_from(environment const & env, name const & C);
/** \brief Return true iff the given environment has coercions to a user-class named \c D. */
bool has_coercions_to(environment const & env, name const & D);
bool has_coercions_to_sort(environment const & env);
bool has_coercions_to_fun(environment const & env);
/**
   \brief Return a coercion (if it exists) from (C_name.{l1 lk} t_1 ... t_n) to the class named D.
   The coercion is a unary function that takes a term of type (C_name.{l1 lk} t_1 ... t_n) and returns
   and element of type (D.{L_1  L_o} s_1 ... s_m)
*/
list<expr> get_coercions(environment const & env, expr const & C, name const & D);
list<expr> get_coercions_to_sort(environment const & env, expr const & C);
list<expr> get_coercions_to_fun(environment const & env, expr const & C);
/**
   \brief Return all coercions C >-> D for the type C of the form (C_name.{l1 ... lk} t_1 ... t_n)
   The coercions are stored in result.
   The Boolean result is true if at least one coercion is added to \c result.

   \remark The most recent coercions occur first.
*/
bool get_coercions_from(environment const & env, expr const & C, buffer<expr> & result);

typedef std::function<void(name const &, name const &, name const &)> coercion_user_fn;
typedef std::function<void(name const &, name const &)> coercion_sort_fn;
typedef std::function<void(name const &, name const &)> coercion_fun_fn;
void for_each_coercion_user(environment const & env, coercion_user_fn const & f);
void for_each_coercion_sort(environment const & env, coercion_sort_fn const & f);
void for_each_coercion_fun(environment const & env, coercion_fun_fn const & f);
void initialize_coercion();
void finalize_coercion();
}
