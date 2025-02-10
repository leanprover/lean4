/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/
#include <string>
#include <map>
#include "library/time_task.h"
#include "kernel/trace.h"

namespace lean {

static std::map<std::string, second_duration> * g_cum_times;
static mutex * g_cum_times_mutex;
LEAN_THREAD_PTR(time_task, g_current_time_task);

bool has_profiling_task() {
    return g_current_time_task != nullptr;
}
void report_profiling_time(std::string const & category, second_duration time) {
    lock_guard<mutex> _(*g_cum_times_mutex);
    (*g_cum_times)[category] += time;
}
void exclude_profiling_time_from_current_task(second_duration time) {
    if (g_current_time_task)
        g_current_time_task->exclude_duration(time);
}

void display_cumulative_profiling_times(std::ostream & out) {
    if (g_cum_times->empty())
        return;
    sstream ss;
    ss << "cumulative profiling times:\n";
    for (auto const & p : *g_cum_times)
        ss << "\t" << p.first << " " << display_profiling_time{p.second} << "\n";
    // output atomically, like IO.print
    out << ss.str();
}

void initialize_time_task() {
    g_cum_times_mutex = new mutex;
    g_cum_times = new std::map<std::string, second_duration>;
}

void finalize_time_task() {
    delete g_cum_times;
    delete g_cum_times_mutex;
}

time_task::time_task(std::string const & category, options const & opts, name decl) :
        m_category(category) {
    if (get_profiler(opts)) {
        m_timeit = optional<xtimeit>(get_profiling_threshold(opts), [=](second_duration duration) mutable {
            sstream ss;
            ss << m_category;
            if (decl)
                ss << " of " << decl;
            ss << " took " << display_profiling_time{duration} << "\n";
            // output atomically, like IO.print
            tout() << ss.str();
        });
        m_parent_task = g_current_time_task;
        g_current_time_task = this;
    }
}

time_task::~time_task() {
    if (m_timeit) {
        g_current_time_task = m_parent_task;
        report_profiling_time(m_category, m_timeit->get_elapsed());
        if (m_parent_task && m_parent_task->m_timeit)
            // report exclusive times
            m_parent_task->m_timeit->exclude_duration(m_timeit->get_elapsed_inclusive());
    }
}

/* profileit {α : Type} (category : String) (opts : Options) (fn : Unit → α) (decl : Name) : α */
extern "C" LEAN_EXPORT obj_res lean_profileit(b_obj_arg category, b_obj_arg opts, obj_arg fn, obj_arg decl) {
    time_task t(string_to_std(category),
                TO_REF(options, opts),
                name(decl));
    return apply_1(fn, box(0));
}
}
