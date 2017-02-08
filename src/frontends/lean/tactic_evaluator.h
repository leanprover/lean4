/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/tactic/tactic_state.h"
#include "frontends/lean/info_manager.h"

namespace lean {
elaborator_exception unsolved_tactic_state(tactic_state const & ts, format const & fmt, expr const & ref);
elaborator_exception unsolved_tactic_state(tactic_state const & ts, char const * msg, expr const & ref);
[[noreturn]] void throw_unsolved_tactic_state(tactic_state const & ts, format const & fmt, expr const & ref);
[[noreturn]] void throw_unsolved_tactic_state(tactic_state const & ts, char const * msg, expr const & ref);

class tactic_evaluator {
    type_context &  m_ctx;
    options const & m_opts;

    environment compile_tactic(name const & tactic_name, expr const & tactic);
    vm_obj invoke_tactic(vm_state & S, name const & tactic_name, std::initializer_list<vm_obj> const & args);

    optional<tactic_state> execute_tactic(expr const & tactic, tactic_state const & s, expr const & ref);
    optional<tactic_state> execute_atomic(tactic_state const & s, expr const & tactic, expr const & ref);
public:
    tactic_evaluator(type_context & ctx, options const & opts);

    optional<tactic_state> operator()(tactic_state const & s, expr const & tactic, expr const & ref);
};
}
