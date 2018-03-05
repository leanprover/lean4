/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura, Sebastian Ullrich
*/
#pragma once
#include "util/sstream.h"
#include "util/fresh_name.h"
#include "kernel/type_checker.h"
#include "kernel/instantiate.h"
#include "library/profiling.h"
#include "library/constants.h"
#include "library/message_builder.h"
#include "library/time_task.h"
#include "library/vm/interaction_state.h"
#include "library/vm/vm_environment.h"
#include "library/vm/vm_exceptional.h"
#include "library/vm/vm_format.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_options.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_level.h"
#include "library/vm/vm_declaration.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_option.h"
#include "library/vm/vm_pos_info.h"
#include "library/compiler/vm_compiler.h"

namespace lean {
template<typename State>
interaction_monad<State>::vm_State::vm_State(State const & v) : m_val(v) {}

template<typename State>
interaction_monad<State>::vm_State::~vm_State() {}

template<typename State>
void interaction_monad<State>::vm_State::dealloc() {
    this->~vm_State();
    get_vm_allocator().deallocate(sizeof(vm_State), this);
}

template<typename State>
vm_external * interaction_monad<State>::vm_State::ts_clone(vm_clone_fn const &) {
    if (!is_ts_safe(m_val)) {
        throw exception("Failed to copy state to another thread");
    }
    return new vm_State(m_val);
}

template<typename State>
vm_external * interaction_monad<State>::vm_State::clone(vm_clone_fn const &) {
    if (!is_ts_safe(m_val)) {
        throw exception("Failed to copy state to another thread");
    }
    return new(get_vm_allocator().allocate(sizeof(vm_State))) vm_State(m_val);
}

template<typename State>
bool interaction_monad<State>::is_state(vm_obj const & o) {
    return is_external(o) && dynamic_cast<vm_State *>(to_external(o));
}

template<typename State>
auto interaction_monad<State>::to_state(vm_obj const & o) -> State const & {
    lean_vm_check(dynamic_cast<vm_State*>(to_external(o)));
    return static_cast<vm_State *>(to_external(o))->m_val;
}

template<typename State>
vm_obj interaction_monad<State>::to_obj(State const & s) {
    return mk_vm_external(new(get_vm_allocator().allocate(sizeof(vm_State))) vm_State(s));
}

template<typename State>
bool interaction_monad<State>::is_silent_exception(vm_obj const & ex) {
    return is_constructor(ex) && cidx(ex) == 1 && is_none(cfield(ex, 0));
}

template<typename State>
vm_obj interaction_monad<State>::mk_success(vm_obj const & a, vm_obj const & s) {
    lean_assert(is_state(s));
    return mk_vm_constructor(0, a, s);
}

template<typename State>
bool interaction_monad<State>::is_result_exception(vm_obj const & r) {
    return is_constructor(r) && cidx(r) == 1;
}

template<typename State>
vm_obj interaction_monad<State>::get_exception_message(vm_obj const & r) {
    lean_assert(is_result_exception(r));
    return cfield(r, 0);
}

template<typename State>
vm_obj interaction_monad<State>::get_exception_pos(vm_obj const & r) {
    lean_assert(is_result_exception(r));
    return cfield(r, 1);
}

template<typename State>
vm_obj interaction_monad<State>::get_exception_state(vm_obj const & r) {
    lean_assert(is_result_exception(r));
    return cfield(r, 2);
}

template<typename State>
bool interaction_monad<State>::is_result_success(vm_obj const & r) {
    return is_constructor(r) && cidx(r) == 0;
}

template<typename State>
vm_obj interaction_monad<State>::get_success_value(vm_obj const & r) {
    lean_assert(is_result_success(r));
    return cfield(r, 0);
}

template<typename State>
vm_obj interaction_monad<State>::get_success_state(vm_obj const & r) {
    lean_assert(is_result_success(r));
    return cfield(r, 1);
}

template<typename State>
vm_obj interaction_monad<State>::mk_success(vm_obj const & a, State const & s) {
    return mk_vm_constructor(0, a, to_obj(s));
}

template<typename State>
vm_obj interaction_monad<State>::mk_success(State const & s) {
    return mk_success(mk_vm_unit(), s);
}

template<typename State>
vm_obj interaction_monad<State>::mk_exception(vm_obj const & fn, State const & s) {
    return mk_vm_constructor(1, mk_vm_some(fn), mk_vm_none(), to_obj(s));
}

template<typename State>
vm_obj interaction_monad<State>::mk_silent_exception(State const & s) {
    return mk_vm_constructor(1, mk_vm_none(), mk_vm_none(), to_obj(s));
}

template<typename State>
vm_obj interaction_monad<State>::mk_exception(vm_obj const & fn, vm_obj const & pos, State const & s) {
    return mk_vm_constructor(1, mk_vm_some(fn), pos, to_obj(s));
}

template<typename State>
vm_obj interaction_monad<State>::update_exception_state(vm_obj const & ex, State const & s) {
    lean_assert(is_result_exception(ex));
    return mk_exception(get_exception_message(ex), get_exception_pos(ex), s);
}

template<typename State>
vm_obj interaction_monad<State>::mk_exception(throwable const & ex, State const & s) {
    vm_obj _ex = lean::to_obj(ex);
    vm_obj fn = mk_vm_closure(get_throwable_to_format_fun_idx(), 1, &_ex);
    optional<pos_info> pos;
    if (auto kex = dynamic_cast<exception_with_pos const *>(&ex))
        pos = kex->get_pos();
    vm_obj _pos = pos ? mk_vm_some(mk_vm_pair(mk_vm_nat(pos->first), mk_vm_nat(pos->second))) : mk_vm_none();
    return mk_exception(fn, _pos, s);
}

template<typename State>
vm_obj interaction_monad<State>::mk_exception(format const & fmt, State const & s) {
    vm_state const & S = get_vm_state();
    if (optional<vm_decl> K = S.get_decl(get_combinator_K_name())) {
        return mk_exception(mk_vm_closure(K->get_idx(), lean::to_obj(fmt), mk_vm_unit(), mk_vm_unit()), s);
    } else {
        throw exception("failed to create tactic exceptional result, combinator.K is not in the environment, "
                        "this can happen when users are hacking the init folder");
    }
}

template<typename State>
vm_obj interaction_monad<State>::mk_exception(char const * msg, State const & s) {
    return mk_exception(format(msg), s);
}

template<typename State>
vm_obj interaction_monad<State>::mk_exception(sstream const & strm, State const & s) {
    return mk_exception(strm.str().c_str(), s);
}

template<typename State>
vm_obj interaction_monad<State>::mk_exception(std::function<format()> const & thunk, State const & s) {
    return mk_exception(mk_vm_format_thunk(thunk), s);
}

template<typename State>
void interaction_monad<State>::report_exception(vm_state & S, vm_obj const & r) {
    if (optional<exception_info> ex = is_exception(S, r)) {
        format fmt = std::get<0>(*ex);
        optional<pos_info> pos = std::get<1>(*ex);
        throw formatted_exception(pos, fmt);
    }
}

template<typename State>
auto interaction_monad<State>::is_success(vm_obj const & r) -> optional<State> {
    if (is_result_success(r))
        return some(to_state(get_success_state(r)));
    return {};
}

template<typename State>
auto interaction_monad<State>::is_exception(vm_state & S, vm_obj const & ex) -> optional<exception_info> {
    if (is_result_exception(ex) && !is_none(get_exception_message(ex))) {
        vm_obj fmt = S.invoke(get_some_value(get_exception_message(ex)), mk_vm_unit());
        optional<pos_info> p;
        if (!is_none(get_exception_pos(ex))) {
            auto vm_p = get_some_value(get_exception_pos(ex));
            p = some(to_pos_info(vm_p));
        }
        return optional<exception_info>(to_format(fmt), p, to_state(get_exception_state(ex)));
    } else {
        return {};
    }
}

template<typename State>
void interaction_monad<State>::evaluator::process_failure(vm_state & S, vm_obj const & r) {
    report_exception(S, r);
    /* Do nothing if it is a silent failure */
    lean_assert(is_silent_exception(r));
}

template<typename State>
environment interaction_monad<State>::evaluator::compile(name const & interaction_name, expr const & interaction) {
    pos_info_provider * provider = get_pos_info_provider();
    expr interaction_type = m_ctx.infer(interaction);
    environment new_env = m_ctx.env();
    bool use_conv_opt = true;
    bool is_trusted = false;
    auto cd = check(new_env,
                    mk_definition(new_env, interaction_name, {}, interaction_type, interaction, use_conv_opt,
                                  is_trusted));
    new_env = new_env.add(cd);
    if (provider) {
        if (auto pos = provider->get_pos_info(interaction))
            new_env = add_transient_decl_pos_info(new_env, interaction_name, *pos);
    }
    try {
        bool optimize_bytecode = false;
        if (provider) {
            auto out = message_builder(environment(), get_global_ios(),
                                       get_pos_info_provider()->get_file_name(),
                                       get_pos_info_provider()->get_pos_info_or_some(interaction),
                                       INFORMATION);
            time_task _("elaboration: tactic compilation", out, m_opts);
            return vm_compile(new_env, new_env.get(interaction_name), optimize_bytecode);
        } else {
            return vm_compile(new_env, new_env.get(interaction_name), optimize_bytecode);
        }
    } catch (exception & ex) {
        throw formatted_exception(some(interaction), format(ex.what()));
    }
}

template<typename State>
vm_obj interaction_monad<State>::evaluator::invoke(vm_state & S, name const & interaction_name, std::initializer_list<vm_obj> const & args) {
    vm_state::profiler prof(S, m_opts);
    vm_obj r = S.invoke(interaction_name, args);
    if (prof.enabled()) {
        prof.get_snapshots().display("tactic", m_opts, get_global_ios().get_regular_stream());
    }
    return r;
}

template<typename State>
interaction_monad<State>::evaluator::evaluator(type_context_old & ctx, options const & opts, bool allow_profiler):
    m_ctx(ctx), m_opts(opts) {
    if (!allow_profiler)
        // do not bother to invoke the profiler for most trivial calls into Lean
        m_opts = m_opts.update("profiler", false);
}

template<typename State>
vm_obj interaction_monad<State>::evaluator::operator()(expr const & interaction, buffer<vm_obj> const & args, State const & s) {
    name interaction_name("_interaction");
    environment new_env = compile(interaction_name, interaction);
    vm_state S(new_env, m_opts);
    scope_vm_state scope(S);
    vm_state::profiler prof(S, m_opts);
    buffer<vm_obj> args_s;
    args_s.append(args);
    args_s.push_back(to_obj(s));
    vm_obj r = S.invoke(S.get_constant(interaction_name), args_s.size(), args_s.data());
    if (prof.enabled() && get_pos_info_provider()) {
        auto out = message_builder(environment(), get_global_ios(),
                                   get_pos_info_provider()->get_file_name(),
                                   get_pos_info_provider()->get_pos_info_or_some(interaction),
                                   INFORMATION);
        out.set_caption("tactic profile data");
        if (prof.get_snapshots().display("elaboration: tactic", m_opts, out.get_text_stream().get_stream()))
            out.report();
    }

    if (!is_success(r))
        process_failure(S, r);
    return r;
}

template<typename State>
vm_obj interaction_monad<State>::evaluator::operator()(expr const & interaction, State const & s) {
    buffer<vm_obj> args;
    return operator()(interaction, args, s);
}
}
