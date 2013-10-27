/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/sexpr/options.h"
#include "kernel/expr.h"
#include "kernel/environment.h"
#include "kernel/metavar.h"
#include "kernel/unification_constraint.h"
#include "library/elaborator/elaborator_plugin.h"
#include "library/elaborator/synthesizer.h"

namespace lean {
/**
   \brief Elaborator is the main object used to fill "holes" in Lean.
   Each hole is represented using a metavariable. This object is
   responsible for solving the easy "holes" and invoking external
   plugins/synthesizers for filling the other ones. It is also
   responsible for managing the search space (i.e., managing the
   backtracking search).

   The elaborator can be customized using:

   1) Elaborator plugins. They are invoked whenever the elaborator
   does not know how to solve a unification constraint.

   2) Synthesizers. They are invoked whenever the elaborator does not
   have unification constraints for inferring a particular hole.

   The result is a sequence of substitutions. Each substitution
   represents a different way of filling the holes.
*/
class elaborator {
public:
    class imp;
    std::shared_ptr<imp> m_ptr;
public:
    elaborator(environment const & env,
               metavar_env const & menv,
               unsigned num_cnstrs,
               unification_constraint const * cnstrs,
               options const & opts = options(),
               std::shared_ptr<synthesizer> const & s = std::shared_ptr<synthesizer>(),
               std::shared_ptr<elaborator_plugin> const & p = std::shared_ptr<elaborator_plugin>());

    elaborator(environment const & env,
               metavar_env const & menv,
               std::initializer_list<unification_constraint> const & cnstrs,
               options const & opts = options(),
               std::shared_ptr<synthesizer> const & s = std::shared_ptr<synthesizer>(),
               std::shared_ptr<elaborator_plugin> const & p = std::shared_ptr<elaborator_plugin>()):
        elaborator(env, menv, cnstrs.size(), cnstrs.begin(), opts, s, p) {}

    elaborator(environment const & env,
               metavar_env const & menv,
               context const & ctx, expr const & lhs, expr const & rhs);

    ~elaborator();

    metavar_env next();
    void interrupt();
    void set_interrupt(bool ) { interrupt(); }
};
}
