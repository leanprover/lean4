/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once
#include "util/task.h"
#include "util/unit.h"
#include "util/list.h"
#include "util/cancellable.h"
#include <vector>
#include <type_traits>

namespace lean {

template <class Res> task<Res> mk_pure_task(Res && res) { return std::make_shared<task_cell<Res>>(res); }
template <class Res> task<Res> mk_pure_task(Res const & res) { return std::make_shared<task_cell<Res>>(res); }

struct delegating_task_imp : public gtask_imp {
    std::unique_ptr<gtask_imp> m_base;

    delegating_task_imp(std::unique_ptr<gtask_imp> && base) : m_base(std::forward<std::unique_ptr<gtask_imp>>(base)) {}

    void get_dependencies(buffer<gtask> & deps) override { m_base->get_dependencies(deps); }
    void execute(void * result) override { return m_base->execute(result); }
};

struct cancellation_support {
    cancellation_token m_ctok;
    cancellation_support(cancellation_token const & ctok) : m_ctok(ctok) {}
    std::unique_ptr<gtask_imp> operator()(std::unique_ptr<gtask_imp> &&);
};

template <class Fn>
struct depends_on_fn_wrapper : public delegating_task_imp {
    Fn m_fn;

    depends_on_fn_wrapper(std::unique_ptr<gtask_imp> && base, Fn && fn) :
        delegating_task_imp(std::forward<std::unique_ptr<gtask_imp>>(base)), m_fn(std::forward<Fn>(fn)) {}

    void get_dependencies(buffer<gtask> & deps) override {
        m_fn(deps);
        delegating_task_imp::get_dependencies(deps);
    }
};

template <class Res>
class task_builder {
    std::unique_ptr<gtask_imp> m_imp;
    task_flags m_flags;
    cancellation_token m_cancel_tok;

    template <class Fn>
    struct base_task_imp : public gtask_imp {
        Fn m_fn;

        base_task_imp(Fn && fn) : m_fn(fn) {}

        void execute(void * result) override {
            *static_cast<Res *>(result) = m_fn();
        }
    };

public:
    task_builder() : task_builder([] { return Res(); }) {}
    template <class Fn> task_builder(Fn && fn) :
            m_imp(new base_task_imp<Fn>(std::forward<Fn>(fn))),
            m_cancel_tok(global_cancellation_token()) {}

    task_builder<Res> does_not_require_own_thread() {
        lean_assert(m_imp);
        m_flags.m_needs_separate_thread = false;
        return std::move(*this);
    }

    template <class Wrapper>
    task_builder<Res> wrap(Wrapper && wrapper) {
        lean_assert(m_imp);
        m_imp = wrapper(std::move(m_imp));
        lean_assert(m_imp);
        return std::move(*this);
    }

    task_builder<Res> set_cancellation_token(cancellation_token const & ctok) {
        lean_assert(m_imp);
        m_cancel_tok = ctok;
        return std::move(*this);
    }

    template <class Fn>
    task_builder<Res> depends_on_fn(Fn && fn) {
        lean_assert(m_imp);
        m_imp.reset(new depends_on_fn_wrapper<Fn>(std::move(m_imp), std::forward<Fn>(fn)));
        lean_assert(m_imp);
        return std::move(*this);
    }

    task_builder<Res> depends_on(gtask const & t) {
        lean_assert(m_imp);
        return depends_on_fn([t] (buffer<gtask> & deps) { deps.push_back(t); });
    }

    template <class Task>
    task_builder<Res> depends_on(std::vector<Task> && ts) {
        lean_assert(m_imp);
        return depends_on_fn([ts] (buffer<gtask> & deps) {
            for (auto & t : ts) deps.push_back(t);
        });
    }

    template <class Task>
    task_builder<Res> depends_on(std::vector<Task> const & ts) {
        lean_assert(m_imp);
        std::vector<Task> ts_ = ts;
        return depends_on(std::move(ts_));
    }

    template <class Task>
    task_builder<Res> depends_on(list<Task> const & ts) {
        lean_assert(m_imp);
        return depends_on_fn([ts] (buffer<gtask> & deps) {
            for (auto & t : ts) deps.push_back(t);
        });
    }

    gtask build_dep_task() {
        m_flags.m_eager_execution = true;
        return mk_task<unit>(std::move(m_imp), m_flags);
    }

    task<Res> build() {
        auto ctok = mk_cancellation_token(m_cancel_tok);
        auto cancellable = wrap(cancellation_support(ctok));
        auto task = mk_task<Res>(std::move(cancellable.m_imp), cancellable.m_flags);
        ctok->add_child(task);
        return task;
    }
};

template <class Res, class Fn, class Arg>
task_builder<Res> map(task<Arg> const & arg, Fn && fn) {
    return std::move(task_builder<Res>([arg, fn] { return fn(get(arg)); }).depends_on(arg));
};

template <class Res>
task<std::vector<Res>> traverse(std::vector<task<Res>> const & ts) {
    return task_builder<std::vector<Res>>([ts] {
        std::vector<Res> vs;
        for (auto &t : ts) vs.push_back(get(t));
        return std::move(vs);
    }).depends_on_fn([ts](buffer<gtask> & deps) {
        for (auto &t : ts) deps.push_back(t);
    }).does_not_require_own_thread().build();
}

template <class Res>
task<list<Res>> reverse_traverse(list<task<Res>> const & ts) {
    return task_builder<list<Res>>([ts] {
        list<Res> vs;
        for (auto & t : ts) vs = cons(get(t), vs);
        return std::move(vs);
    }).depends_on_fn([ts](buffer<gtask> & deps) {
        for (auto & t : ts) deps.push_back(t);
    }).does_not_require_own_thread().build();
}

template <class Fn>
gtask mk_dependency_task(Fn && fn) {
    return task_builder<unit>().depends_on_fn(std::forward<Fn>(fn)).build_dep_task();
}

template <class Arg, class Fn>
gtask mk_deep_dependency(task<Arg> const & arg, Fn && fn) {
    return mk_dependency_task([fn, arg] (buffer<gtask> & deps) {
        deps.push_back(arg);
        if (auto v = peek(arg)) {
            fn(deps, *v);
        }
    });
};

}
