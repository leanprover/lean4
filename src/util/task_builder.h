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
#include <algorithm>
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

    task_builder<Res> execute_eagerly() {
        m_flags.m_eager_execution = true;
        return std::move(*this);
    }

    template <class Wrapper>
    task_builder<Res> wrap(Wrapper && wrapper) {
        m_imp = wrapper(std::move(m_imp));
        lean_assert(m_imp);
        return std::move(*this);
    }

    task_builder<Res> set_cancellation_token(cancellation_token const & ctok) {
        m_cancel_tok = ctok;
        return std::move(*this);
    }

    template <class Fn>
    task_builder<Res> depends_on_fn(Fn && fn) {
        m_imp.reset(new depends_on_fn_wrapper<Fn>(std::move(m_imp), std::forward<Fn>(fn)));
        return std::move(*this);
    }

    task_builder<Res> depends_on(gtask const & t) {
        return depends_on_fn([t] (buffer<gtask> & deps) { deps.push_back(t); });
    }

    template <class Task>
    task_builder<Res> depends_on(std::vector<Task> && ts) {
        return depends_on_fn([ts] (buffer<gtask> & deps) {
            for (auto & t : ts) deps.push_back(t);
        });
    }

    template <class Task>
    task_builder<Res> depends_on(std::vector<Task> const & ts) {
        std::vector<Task> ts_ = ts;
        return depends_on(std::move(ts_));
    }

    template <class Task>
    task_builder<Res> depends_on(list<Task> const & ts) {
        return depends_on_fn([ts] (buffer<gtask> & deps) {
            for (auto & t : ts) deps.push_back(t);
        });
    }

    task<Res> build_without_cancellation() {
        return mk_task<Res>(std::move(m_imp), m_flags);
    }

    gtask build_dep_task() {
        return execute_eagerly().build_without_cancellation();
    }

    task<Res> build() {
        auto ctok = mk_cancellation_token(m_cancel_tok);
        auto task = wrap(cancellation_support(ctok)).build_without_cancellation();
        ctok->add_child(task);
        return std::move(task);
    }
};

template <class Res, class Fn, class Arg>
task_builder<Res> map(task<Arg> const & arg, Fn && fn) {
    return std::move(task_builder<Res>([arg, fn] { return fn(get(arg)); }).depends_on(arg));
};

template <class Res>
task<std::vector<Res>> traverse(std::vector<task<Res>> const & ts) {
    auto to_do = std::make_shared<std::vector<gtask>>();
    for (gtask const & t : ts) {
        if (!t->peek_is_finished()) {
            to_do->push_back(t);
        }
    }

    if (to_do->empty()) {
        std::vector<Res> vs;
        for (auto & t : ts) vs.push_back(get(t));
        return mk_pure_task<std::vector<Res>>(vs);
    }

    return task_builder<std::vector<Res>>([ts] {
        std::vector<Res> vs;
        for (auto & t : ts) vs.push_back(get(t));
        return std::move(vs);
    }).depends_on_fn([to_do] (buffer<gtask> & deps) {
        to_do->erase(std::remove_if(to_do->begin(), to_do->end(),
                [] (gtask & t) { return t->peek_is_finished(); }),
            to_do->end());
        for (auto & t : *to_do) deps.push_back(t);
    }).execute_eagerly().build();
}

template <class Fn, class T>
task<bool> any(std::vector<task<T>> const & ts, Fn && fn) {
    std::vector<task<T>> unknown;
    for (auto & t : ts) {
        if (auto res = peek(t)) {
            if (fn(*res))
                return mk_pure_task(true);
        } else {
            unknown.push_back(t);
        }
    }
    if (unknown.empty()) {
        return mk_pure_task(false);
    } else {
        return map<bool>(traverse<T>(unknown), [=] (std::vector<T> ress) {
           for (auto res : ress)
               if (fn(res))
                   return true;
            return false;
        }).execute_eagerly().build();
    }
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
