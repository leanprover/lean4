/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

namespace lean {
/**
    \brief Create a choice expression for the given expressions.
    The elaborator decides which one should be used based on the type of the arguments.

    \remark if num_fs == 1, then return fs[0]

    \pre num_fs >= 1
*/
expr mk_choice(unsigned num_es, expr const * es);
/** \brief Return true iff \c e is an expression created using \c mk_choice. */
bool is_choice(expr const & e);
/**
   \brief Return the number of alternatives in a choice expression.
   We have that <tt>get_num_choices(mk_choice(n, es)) == n</tt> whenever <tt>n >= 2</tt>.

   \pre is_choice(e)
*/
unsigned get_num_choices(expr const & e);
/**
   \brief Return the (i+1)-th alternative of a choice expression.

   \pre is_choice(e)
   \pre i < get_num_choices(e)
*/
expr const & get_choice(expr const & e, unsigned i);

/**
   \brief Collect "choices" occurring in \c e.
   For example, if \c e contains [choice (f a) (g a)] where f and g are constants,
   the result contains the list [f, g]. This function is only used for producing nicer
   error messages.
*/
list<list<name>> collect_choice_symbols(expr const & e);
/** \brief Format the result produced by collect_choice_symbols. */
format pp_choice_symbols(expr const & e);

void initialize_choice();
void finalize_choice();
}
