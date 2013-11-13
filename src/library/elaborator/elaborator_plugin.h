/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include <utility>
#include "util/list.h"
#include "kernel/environment.h"
#include "kernel/context.h"
#include "kernel/unification_constraint.h"

namespace lean {
class elaborator_plugin {
public:
    virtual ~elaborator_plugin() {}

    /** \brief The plugin produces a "result" object that can generates the sequence of possible solutions. */
    class result {
    public:
        virtual ~result() {}
        /**
            \brief Return the next possible solution. An elaborator_exception is throw in case of failure.

            Each result is represented by a pair: the new metavariable
            environment and a new list of constraints to be solved.
        */
        virtual std::pair<metavar_env, list<unification_constraint>> next(justification const & assumption) = 0;
        /** \brief Interrupt the computation for the next solution. */
    };

    /**
       \brief Ask plugin to solve the constraint \c cnstr in the given
       environment and metavar environment.
    */
    virtual std::unique_ptr<result> operator()(environment const & env, metavar_env const & menv, unification_constraint const & cnstr) = 0;
};
}
