/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/type_checker.h"
#include "library/module.h"
#include "library/trace.h"
#include "library/annotation.h"
#include "library/scope_pos_info_provider.h"
#include "library/vm/vm_list.h"
#include "library/compiler/vm_compiler.h"
#include "library/tactic/smt/smt_state.h"
#include "frontends/lean/elaborator_exception.h"
#include "frontends/lean/tactic_evaluator.h"
#include "frontends/lean/tactic_notation.h"

namespace lean {
[[noreturn]] void throw_unsolved_tactic_state(tactic_state const & ts, format const & fmt, expr const & ref) {
    format msg = fmt + line() + format("state:") + line() + ts.pp();
    throw elaborator_exception(ref, msg);
}

[[noreturn]] void throw_unsolved_tactic_state(tactic_state const & ts, char const * msg, expr const & ref) {
    throw_unsolved_tactic_state(ts, format(msg), ref);
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
    return vm_compile(new_env, new_env.get(tactic_name));
}

vm_obj tactic_evaluator::invoke_tactic(vm_state & S, name const & tactic_name, std::initializer_list<vm_obj> const & args) {
    vm_state::profiler prof(S, m_opts);
    vm_obj r = S.invoke(tactic_name, args);
    if (prof.enabled())
        prof.get_snapshots().display(get_global_ios().get_regular_stream());
    return r;
}

void tactic_evaluator::add_tactic_state_info(tactic_state const & s, expr const & ref) {
    if (!get_global_info_manager()) return;
    pos_info_provider * pip = get_pos_info_provider();
    if (!pip) return;
    if (auto p = pip->get_pos_info(ref))
        m_info.add_tactic_state_info(p->first, p->second, s);
}

static list<smt_goal> to_smt_state(vm_obj const & ss) {
    return to_list<smt_goal>(ss, to_smt_goal);
}

void tactic_evaluator::add_smt_tactic_state_info(vm_obj const & ss, tactic_state const & /* ts */, expr const & ref) {
    if (!get_global_info_manager()) return;
    pos_info_provider * pip = get_pos_info_provider();
    if (!pip) return;
    if (auto p = pip->get_pos_info(ref)) {
        list<smt_goal> _ss = to_smt_state(ss);
        // m_info.add_smt_tactic_state_info(p->first, p->second, _ss, ts);
    }
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
}

tactic_state tactic_evaluator::execute_tactic(expr const & tactic, tactic_state const & s, expr const & ref) {
    pos_info_provider * provider = get_pos_info_provider();
    scope_traces_as_messages traces_as_messages(provider, ref);

    name tactic_name("_tactic");
    environment new_env = compile_tactic(tactic_name, tactic);

    vm_state S(new_env, m_opts);
    vm_obj r = invoke_tactic(S, tactic_name, {to_obj(s)});

    if (optional<tactic_state> new_s = is_tactic_success(r)) {
        return *new_s;
    }
    process_failure(S, r, ref);
    lean_unreachable();
}

pair<vm_obj, tactic_state> tactic_evaluator::excute_smt_tactic(expr const & tactic, vm_obj const & ss, tactic_state const & ts, expr const & ref) {
    pos_info_provider * provider = get_pos_info_provider();
    scope_traces_as_messages traces_as_messages(provider, ref);

    name tactic_name("_smt_tactic");
    environment new_env = compile_tactic(tactic_name, tactic);

    vm_state S(new_env, m_opts);
    vm_obj r = invoke_tactic(S, tactic_name, {ss, to_obj(ts)});

    if (is_tactic_result_success(r)) {
        vm_obj new_ss       = cfield(get_tactic_result_value(r), 1);
        tactic_state new_ts = to_tactic_state(get_tactic_result_state(r));
        return mk_pair(new_ss, new_ts);
    }
    process_failure(S, r, ref);
    lean_unreachable();
}

tactic_state tactic_evaluator::execute_begin_end(tactic_state const & s, buffer<expr> const & tactics, expr const & ref) {
    /* TODO(Leo): check if it is a begin[smt] ... end block */
    lean_assert(!tactics.empty());
    list<expr> gs = s.goals();
    if (!gs) throw elaborator_exception(ref, "tactic failed, there are no goals to be solved");
    tactic_state new_s = set_goals(s, to_list(head(gs)));
    for (expr const & tactic : tactics) {
        expr const & curr_ref = tactic;
        if (is_begin_end_element(tactic)) {
            add_tactic_state_info(new_s, curr_ref);
            new_s = execute_tactic(get_annotation_arg(tactic), new_s, curr_ref);
        } else if (is_begin_end_block(tactic)) {
            buffer<expr> nested_tactics;
            get_begin_end_block_elements(tactic, nested_tactics);
            new_s = execute_begin_end(new_s, nested_tactics, curr_ref);
        } else {
            throw elaborator_exception(curr_ref, "ill-formed 'begin ... end' tactic block");
        }
    }
    add_tactic_state_info(new_s, ref);
    if (new_s.goals()) throw_unsolved_tactic_state(new_s, "tactic failed, there are unsolved goals", ref);
    return set_goals(new_s, tail(gs));
}

tactic_state tactic_evaluator::execute_atomic(tactic_state const & s, expr const & tactic, expr const & ref) {
    add_tactic_state_info(s, ref);
    /* Save information using tactic's position, ref is usually the `by` token position */
    add_tactic_state_info(s, tactic);
    tactic_state new_s = execute_tactic(tactic, s, ref);
    if (new_s.goals())
        throw_unsolved_tactic_state(new_s, "tactic failed, there are unsolved goals", ref);
    return new_s;
}

tactic_state tactic_evaluator::operator()(tactic_state const & s, expr const & tactic, expr const & ref) {
    if (is_begin_end_block(tactic)) {
        buffer<expr> tactics;
        get_begin_end_block_elements(tactic, tactics);
        return execute_begin_end(s, tactics, ref);
    } else {
        return execute_atomic(s, tactic, ref);
    }
}

tactic_evaluator::tactic_evaluator(type_context & ctx, info_manager & info, options const & opts):
    m_ctx(ctx), m_info(info), m_opts(opts) {
}
}
