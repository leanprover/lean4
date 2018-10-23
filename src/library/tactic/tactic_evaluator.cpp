/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/module.h"
#include "library/trace.h"
#include "library/annotation.h"
#include "library/util.h"
#include "library/constants.h"
#include "library/tactic/elaborator_exception.h"
#include "library/tactic/tactic_evaluator.h"

namespace lean {
format mk_tactic_error_msg(tactic_state const & ts, format const & fmt) {
    return fmt + line() + format("state:") + line() + ts.pp();
}

elaborator_exception unsolved_tactic_state(tactic_state const & ts, format const & fmt, expr const & ref) {
    return elaborator_exception(ref, mk_tactic_error_msg(ts, fmt));
}

elaborator_exception unsolved_tactic_state(tactic_state const & ts, char const * msg, expr const & ref) {
    return unsolved_tactic_state(ts, format(msg), ref);
}

[[noreturn]] void throw_unsolved_tactic_state(tactic_state const & ts, format const & fmt, expr const & ref) {
    throw unsolved_tactic_state(ts, fmt, ref);
}

[[noreturn]] void throw_unsolved_tactic_state(tactic_state const & ts, char const * msg, expr const & ref) {
    throw_unsolved_tactic_state(ts, format(msg), ref);
}
}
