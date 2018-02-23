/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once
#include <memory>
#include "util/buffer.h"
#include "util/thread.h"
#include "util/cancellable.h"

namespace lean {

class gtask_cell;
using gtask = std::shared_ptr<gtask_cell>;
using weak_gtask = std::weak_ptr<gtask_cell>;
template <class Res> class task_cell;
template <class Res> using task = std::shared_ptr<task_cell<Res>>;
class task_queue;

struct scheduling_info {
    virtual ~scheduling_info() {}
};

struct task_flags {
    bool m_eager_execution = false;
};

using task_dep_fn = std::function<void(buffer<gtask>&)>;

struct gtask_imp {
    gtask_imp() {}
    virtual ~gtask_imp() {}

    virtual void get_dependencies(buffer<gtask> &) {}
    virtual void execute(void * result) = 0;
};

struct gtask_data {
    std::unique_ptr<gtask_imp> m_imp;
    std::unique_ptr<scheduling_info> m_sched_info;
    task_flags m_flags;

    gtask_data(gtask_imp * imp, task_flags flags) : m_imp(imp), m_flags(flags) {}
};

enum class task_state {
    Created = 0,
    Waiting = 1,
    Queued = 2,
    Running = 3,
    Failed = 4,
    Success = 5,
};

class gtask_cell : public cancellable {
    friend class task_queue;
    template <class Res> friend class task_cell;
    template <class Res> friend task<Res> mk_task(std::unique_ptr<gtask_imp> &&, task_flags);

    virtual void execute() {};

    atomic<task_state>          m_state;
    std::unique_ptr<gtask_data> m_data;
    std::exception_ptr          m_exception;

    gtask_cell(task_state state) :
        m_state(state) {
    }

    gtask_cell(gtask_imp * imp, task_flags flags) :
        m_state(task_state::Created) {
        m_data.reset(new gtask_data(imp, flags));
    }

    struct called_from_friend {};

public:
    void cancel(std::shared_ptr<cancellable> const & self) override;

    bool peek_is_finished() const { return m_state.load() > task_state::Running; }
    std::exception_ptr peek_exception() const;

    virtual ~gtask_cell() {}
};

template <class Res>
class task_cell : public gtask_cell {
    friend class task_queue;

    optional<Res> m_result;

    void execute() override {
        m_result = optional<Res>(Res());
        m_data->m_imp->execute(&*m_result);
    }

public:
    task_cell(called_from_friend, gtask_imp * imp, task_flags flags) : gtask_cell(imp, flags) {}

    task_cell(Res const & res) : gtask_cell(task_state::Success), m_result(res) {}
    task_cell(Res && res) : gtask_cell(task_state::Success), m_result(res) {}
    task_cell(std::exception_ptr const & ex) : gtask_cell(task_state::Failed) { m_exception = ex; }

    optional<Res> peek() {
        if (m_state.load() == task_state::Success) {
            return m_result;
        } else {
            return optional<Res>();
        }
    }
};

template <class Res>
task<Res> mk_task(std::unique_ptr<gtask_imp> && imp, task_flags flags) {
    return std::make_shared<task_cell<Res>>(gtask_cell::called_from_friend(), imp.release(), flags);
}

struct cancellation_exception {};

class task_queue {
protected:
    atomic<task_state> & get_state(gtask const & t) const { return t->m_state; }
    gtask_data * get_data(gtask const & t) const { return t->m_data.get(); }

    void clear(gtask const & t) const { t->m_data.reset(nullptr); }

    void execute(gtask const & t);
    void fail(gtask const & t, std::exception_ptr const & ex);
    void fail(gtask const & t, gtask const & failed);

public:
    virtual ~task_queue() {}

    virtual void wait_for_finish(gtask const &) = 0;

    void wait_for_success(gtask const & t);

    template <class Res>
    Res const & get(task<Res> const & t) {
        wait_for_success(t);
        return *t->m_result;
    }

    virtual void fail_and_dispose(gtask const &) = 0;
    virtual void evacuate() = 0;
    virtual void join() = 0;

    virtual void submit(gtask const &) = 0;
    virtual void submit(gtask const &, unsigned prio);
};

void set_task_queue(task_queue *); // NOLINT
task_queue & taskq();

template <class Res>
Res const & get(task<Res> const & t) {
    return taskq().get(t);
}

template <class Res>
optional<Res> peek(task<Res> const & t) {
    return t->peek();
}

}
