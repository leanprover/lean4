/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/type_checker.h"
#include "library/module.h"
#include "library/trace.h"
#include "library/annotation.h"
#include "library/util.h"
#include "library/constants.h"
#include "library/scope_pos_info_provider.h"
#include "library/vm/vm_list.h"
#include "library/compiler/vm_compiler.h"
#include "library/tactic/smt/smt_state.h"
#include "frontends/lean/elaborator_exception.h"
#include "frontends/lean/tactic_evaluator.h"
#include "frontends/lean/tactic_notation.h"

namespace lean {
elaborator_exception unsolved_tactic_state(tactic_state const & ts, format const & fmt, expr const & ref) {
    format msg = fmt + line() + format("state:") + line() + ts.pp();
    return elaborator_exception(ref, msg);
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

[[noreturn]] void throw_unsolved_smt_tactic_state(vm_obj const & ss, tactic_state const & ts, format const & fmt, expr const & ref) {
    format msg = fmt + line() + format("state:") + line() + smt_state_pp(ss, ts);
    throw elaborator_exception(ref, msg);
}

[[noreturn]] void throw_unsolved_smt_tactic_state(vm_obj const & ss, tactic_state const & ts, char const * msg, expr const & ref) {
    throw_unsolved_smt_tactic_state(ss, ts, format(msg), ref);
}

/* Compile tactic into bytecode */
environment tactic_evaluator::compile_tactic(name const & tactic_name, expr const & tactic) {
    pos_info_provider * provider = get_pos_info_provider();
    expr tactic_type     = m_ctx.infer(tactic);
    environment new_env  = m_ctx.env();
    bool use_conv_opt    = true;
    bool is_trusted      = false;
    auto cd = check(new_env, mk_definition(new_env, tactic_name, {}, tactic_type, tactic, use_conv_opt, is_trusted));
    new_env = new_env.add(cd);
    if (auto pos = provider->get_pos_info(tactic))
        new_env = add_transient_decl_pos_info(new_env, tactic_name, *pos);
    try {
        return vm_compile(new_env, new_env.get(tactic_name));
    } catch (exception & ex) {
        throw elaborator_exception(tactic, ex.what());
    }
}

vm_obj tactic_evaluator::invoke_tactic(vm_state & S, name const & tactic_name, std::initializer_list<vm_obj> const & args) {
    vm_state::profiler prof(S, m_opts);
    vm_obj r = S.invoke(tactic_name, args);
    if (prof.enabled())
        prof.get_snapshots().display(get_global_ios().get_regular_stream());
    return r;
}

static void process_failure(vm_state & S, vm_obj const & r, expr const & ref) {
    pos_info_provider * provider = get_pos_info_provider();
    if (optional<tactic_exception_info> ex = is_tactic_exception(S, r)) {
        format fmt          = std::get<0>(*ex);
        optional<expr> ref1 = std::get<1>(*ex);
        tactic_state s1     = std::get<2>(*ex);
        if (ref1 && provider && provider->get_pos_info(*ref1))
            throw elaborator_exception(*ref1, fmt);
        else
            throw_unsolved_tactic_state(s1, fmt, ref);
    }
    /* Do nothing if it is a silent failure */
    lean_assert(is_tactic_silent_exception(r));
}

optional<tactic_state> tactic_evaluator::execute_tactic(expr const & tactic, tactic_state const & s, expr const & ref) {
    name tactic_name("_tactic");
    environment new_env = compile_tactic(tactic_name, tactic);
    vm_state S(new_env, m_opts);
    vm_obj r = invoke_tactic(S, tactic_name, {to_obj(s)});

    if (optional<tactic_state> new_s = is_tactic_success(r)) {
        return new_s;
    }
    process_failure(S, r, ref);
    return optional<tactic_state>();
}

optional<tactic_state> tactic_evaluator::execute_atomic(tactic_state const & s, expr const & tactic, expr const & ref) {
    optional<tactic_state> new_s = execute_tactic(tactic, s, ref);
    if (new_s && new_s->goals())
        throw_unsolved_tactic_state(*new_s, "tactic failed, there are unsolved goals", ref);
    return new_s;
}

optional<tactic_state> tactic_evaluator::operator()(tactic_state const & s, expr const & tactic, expr const & ref) {
    return execute_atomic(s, tactic, ref);
}

tactic_evaluator::tactic_evaluator(type_context & ctx, options const & opts):
    m_ctx(ctx), m_opts(opts) {
}
}
