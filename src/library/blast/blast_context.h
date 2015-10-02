/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura

API for accessing the thread local context used by the blast tactic.
These procedures can only be invoked while the blast tactic is being executed.

Remark: the API is implemented in the file blast.cpp
*/
#pragma once
#include "util/sstream.h"
#include "library/projection.h"
#include "library/blast/state.h"

namespace lean {
namespace blast {
/** \brief Return the thread local environment being used by the blast tactic. */
environment const & env();
/** \brief Return the thread local io_state being used by the blast tactic. */
io_state const & ios();
/** \brief Return the thread local current state begin processed by the blast tactic. */
state & curr_state();
/** \brief Return the thead local extension context associated with the blast tactic. */
extension_context & ext_ctx();
/** \brief Return a thread local fresh name meant to be used to name local constants. */
name mk_fresh_local_name();
/** \brief Return true iff the given constant name is marked as reducible in env() */
bool is_reducible(name const & n);
/** \brief Return a nonnull projection_info object if \c n is the name of a projection in env() */
projection_info const * get_projection_info(name const & n);

/** \brief Display the current state of the blast tactic in the diagnostic channel. */
void display_curr_state();
/** \brief Display message in the blast tactic diagnostic channel. */
void display(char const * msg);
void display(sstream const & msg);
}}
