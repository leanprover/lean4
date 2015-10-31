/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
#include "library/io_state.h"
#include "library/blast/state.h"

namespace lean {
struct projection_info;
class goal;
namespace blast {
/** \brief Return the thread local environment being used by the blast tactic. */
environment const & env();
/** \brief Return the thread local io_state being used by the blast tactic. */
io_state const & ios();
/** \brief Return the thread local current state begin processed by the blast tactic. */
state & curr_state();
/** \brief Return a thread local fresh name meant to be used to name local constants. */
name mk_fresh_local_name();
expr mk_fresh_local(expr const & type, binder_info const & bi = binder_info());
/** \brief Return true iff the given constant name is marked as reducible in env() */
bool is_reducible(name const & n);
/** \brief Return a nonnull projection_info object if \c n is the name of a projection in env() */
projection_info const * get_projection_info(name const & n);
/** \brief Put the given expression in weak-head-normal-form with respect to the
    current state being processed by the blast tactic. */
expr whnf(expr const & e);
/** \brief Return the type of the given expression with respect to the current state being
    processed by the blast tactic.

    \remark: (potential side-effect) this procedure may update the meta-variable assignment
    associated with the current state. */
expr infer_type(expr const & e);
/** \brief Return true if \c e is a Proposition */
bool is_prop(expr const & e);
/** \brief Return true iff the two expressions are definitionally equal in the
    current state being processed by the blast tactic.

    \remark: (potential side-effect) this procedure may update the meta-variable assignment
    associated with the current state. */
bool is_def_eq(expr const & e1, expr const & e2);
/** \brief Try to synthesize an element of the given type class with respect to the blast local context. */
optional<expr> mk_class_instance(expr const & e);

/** \brief Display the current state of the blast tactic in the diagnostic channel. */
void display_curr_state();
/** \brief Display message in the blast tactic diagnostic channel. */
void display(char const * msg);
void display(sstream const & msg);
/**
    \brief Create a local scope for saving the assignment and
    metavariable declarations at curr_state() */
class scope {
    bool m_keep;
public:
    scope();
    ~scope();
    void commit();
};
}
optional<expr> blast_goal(environment const & env, io_state const & ios, list<name> const & ls, list<name> const & ds,
                          goal const & g);
void initialize_blast();
void finalize_blast();
}
