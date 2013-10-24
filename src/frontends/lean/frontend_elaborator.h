/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include <utility>
#include "kernel/environment.h"
#include "kernel/formatter.h"

namespace lean {
class frontend;
/**
   \brief Expression elaborator for the Lean default frontend, it is responsible for "filling" holes
   in terms left by the user. This is the main module resposible for computing
   the value of implicit arguments. It is based on the general purpose elaborator defined at
   library/elaborator/elaborator.h
*/
class frontend_elaborator {
    class imp;
    std::shared_ptr<imp> m_ptr;
    static void print(imp * ptr);
public:
    explicit frontend_elaborator(frontend const & fe);
    ~frontend_elaborator();

    /**
       \brief Elaborate the given expression.
    */
    expr operator()(expr const & e);
    /**
       \brief Elaborate the given type and expression. The typeof(e) == t.
       This information is used by the elaborator. The result is a new
       elaborated type and expression.
    */
    std::pair<expr, expr> operator()(name const & n, expr const & t, expr const & e);

    /**
        \brief If \c e is an expression instantiated by the elaborator, then it
        returns the expression (the one with "holes") used to generate \c e.
        Otherwise, it just returns \c e.
    */
    expr const & get_original(expr const & e) const;

    void set_interrupt(bool flag);
    void interrupt() { set_interrupt(true); }
    void reset_interrupt() { set_interrupt(false); }

    void clear();

    environment const & get_environment() const;
};

/**
    \brief Create a choice expression for the given functions.
    It is used to mark which functions can be used in a particular application.
    The elaborator decides which one should be used based on the type of the arguments.

    \pre num_fs >= 2
*/
expr mk_choice(unsigned num_fs, expr const * fs);
/**
    \brief Return true iff \c e is an expression created using \c mk_choice.
*/
bool is_choice(expr const & e);
/**
   \brief Return the number of alternatives in a choice expression.
   We have that <tt>get_num_choices(mk_choice(n, fs)) == n</tt>.

   \pre is_choice(e)
*/
unsigned get_num_choices(expr const & e);
/**
   \brief Return the (i+1)-th alternative of a choice expression.

   \pre is_choice(e)
   \pre i < get_num_choices(e)
*/
expr const & get_choice(expr const & e, unsigned i);
}
