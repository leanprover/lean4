/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "library/tactic/tactic.h"

namespace lean {
/** \brief Return a tactic that just returns the input state, and display the given message in the diagnostic channel. */
tactic trace_tactic(char const * msg);
class sstream;
tactic trace_tactic(sstream const & msg);
tactic trace_tactic(std::string const & msg);
/** \brief Return a tactic that just displays the input state in the diagnostic channel. */
tactic trace_state_tactic(std::string const & fname, pair<unsigned, unsigned> const & pos);
tactic trace_state_tactic();
/** \brief Create a tactic that applies \c t, but suppressing diagnostic messages. */
tactic suppress_trace(tactic const & t);

void initialize_trace_tactic();
void finalize_trace_tactic();
}
