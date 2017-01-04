/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/tactic/tactic_state.h"
#include "frontends/lean/info_manager.h"

namespace lean {
[[noreturn]] void throw_unsolved_tactic_state(tactic_state const & ts, format const & fmt, expr const & ref);
[[noreturn]] void throw_unsolved_tactic_state(tactic_state const & ts, char const * msg, expr const & ref);

class tactic_evaluator {
    type_context &  m_ctx;
    info_manager &  m_info;
    options const & m_opts;

    environment compile_tactic(name const & tactic_name, expr const & tactic);
    vm_obj invoke_tactic(vm_state & S, name const & tactic_name, std::initializer_list<vm_obj> const & args);

    void add_tactic_state_info(tactic_state const & s, expr const & ref);
    void add_smt_tactic_state_info(vm_obj const & ss, tactic_state const & ts, expr const & ref);

    tactic_state execute_tactic(expr const & tactic, tactic_state const & s, expr const & ref);
    pair<vm_obj, tactic_state> execute_smt_tactic(expr const & tactic, vm_obj const & ss, tactic_state const & ts, expr const & ref);

    tactic_state execute_begin_end(tactic_state const & s, buffer<expr> const & tactics, expr const & ref);
    tactic_state execute_atomic(tactic_state const & s, expr const & tactic, expr const & ref);
    pair<vm_obj, tactic_state> execute_smt_begin_end_core(vm_obj const & ss, tactic_state const & ts, buffer<expr> const & tactics, expr const & ref);
    pair<vm_obj, tactic_state> mk_smt_state(tactic_state const & s, expr const & smt_cfg, expr const & ref);
    tactic_state execute_smt_begin_end(tactic_state s, expr tactic, expr const & ref);

public:
    tactic_evaluator(type_context & ctx, info_manager & info, options const & opts);

    tactic_state operator()(tactic_state const & s, expr const & tactic, expr const & ref);
};
}
