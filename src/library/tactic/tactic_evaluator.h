/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/tactic/tactic_state.h"
#include "library/tactic/elaborator_exception.h"
#include "library/vm/interaction_state.h"

namespace lean {
elaborator_exception unsolved_tactic_state(tactic_state const & ts, format const & fmt, expr const & ref);
elaborator_exception unsolved_tactic_state(tactic_state const & ts, char const * msg, expr const & ref);
[[noreturn]] void throw_unsolved_tactic_state(tactic_state const & ts, format const & fmt, expr const & ref);
[[noreturn]] void throw_unsolved_tactic_state(tactic_state const & ts, char const * msg, expr const & ref);

class tactic_evaluator : public tactic::evaluator {
private:
    expr m_ref;
protected:
    virtual void process_failure(vm_state & S, vm_obj const & r) override;
public:
    tactic_evaluator(type_context & ctx, options const & opts, expr const & ref):
            tactic::evaluator(ctx, opts), m_ref(ref) {}
    virtual vm_obj operator()(expr const & tactic, buffer<vm_obj> const & args, tactic_state const & s) override;
    vm_obj operator()(expr const & tactic, tactic_state const & s) {
        return tactic::evaluator::operator()(tactic, s);
    }
};
}
