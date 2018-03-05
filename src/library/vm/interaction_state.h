/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura, Sebastian Ullrich
*/
#pragma once
#include <algorithm>
#include "kernel/environment.h"
#include "kernel/scope_pos_info_provider.h"
#include "library/type_context.h"
#include "library/vm/vm.h"

namespace lean {
template<typename State>
struct interaction_monad {
    struct vm_State : public vm_external {
        State m_val;

        vm_State(State const & v);

        virtual ~vm_State();
        virtual void dealloc() override;
        /* The methods ts_clone and close assume there is function

              bool is_ts_safe(State const &)

           This function should return true if the object can be safely
           cloned between threads. */
        virtual vm_external * ts_clone(vm_clone_fn const &) override;
        virtual vm_external * clone(vm_clone_fn const &) override;
    };

    typedef std::tuple<format, optional<pos_info>, State> exception_info;

    static bool is_state(vm_obj const & o);
    static State const & to_state(vm_obj const & o);
    static vm_obj to_obj(State const & s);
    static bool is_silent_exception(vm_obj const & ex);
    static bool is_result_exception(vm_obj const & r);
    static vm_obj get_exception_message(vm_obj const & r);
    static vm_obj get_exception_pos(vm_obj const & r);
    static vm_obj get_exception_state(vm_obj const & r);
    static bool is_result_success(vm_obj const & r);
    static vm_obj get_success_value(vm_obj const & r);
    static vm_obj get_success_state(vm_obj const & r);
    static vm_obj mk_success(vm_obj const & a, vm_obj const & s);
    static vm_obj mk_success(vm_obj const & a, State const & s);
    static vm_obj mk_success(State const & s);
    static vm_obj mk_exception(vm_obj const & fn, State const & s);
    static vm_obj mk_silent_exception(State const & s);
    static vm_obj mk_exception(vm_obj const & fn, vm_obj const & pos, State const & s);
    static vm_obj mk_exception(throwable const & ex, State const & s);
    static vm_obj mk_exception(format const & fmt, State const & s);
    static vm_obj mk_exception(char const * msg, State const & s);
    static vm_obj mk_exception(sstream const & strm, State const & s);
    static vm_obj mk_exception(std::function<format()> const & thunk, State const & s);
    static vm_obj update_exception_state(vm_obj const & ex, State const & s);
    static void report_exception(vm_state & S, vm_obj const & r);
    static optional<State> is_success(vm_obj const & r);
    static optional<exception_info> is_exception(vm_state & S, vm_obj const & ex);

    class evaluator {
        type_context_old & m_ctx;
        options m_opts;
    protected:
        virtual void process_failure(vm_state & S, vm_obj const & r);
    public:
        evaluator(type_context_old & ctx, options const & opts, bool allow_profiler = false);
        environment compile(name const & interaction_name, expr const & interaction);
        vm_obj invoke(vm_state & S, name const & interaction_name,
                      std::initializer_list<vm_obj> const & args);
        virtual vm_obj operator()(expr const & interaction, buffer<vm_obj> const & args, State const & s);
        vm_obj operator()(expr const & interaction, State const & s);
    };
};
}
