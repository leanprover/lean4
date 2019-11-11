/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/
#include <string>
#include <map>
#include "library/time_task.h"

namespace lean {

static std::map<std::string, second_duration> * g_cum_times;
static mutex * g_cum_times_mutex;
LEAN_THREAD_PTR(time_task, g_current_time_task);

void report_profiling_time(std::string const & category, second_duration time) {
    lock_guard<mutex> _(*g_cum_times_mutex);
    (*g_cum_times)[category] += time;
}

void display_cumulative_profiling_times(std::ostream & out) {
    if (g_cum_times->empty())
        return;
    out << "cumulative profiling times:\n";
    for (auto const & p : *g_cum_times)
        out << "\t" << p.first << " " << display_profiling_time{p.second} << "\n";
}

void initialize_time_task() {
    g_cum_times_mutex = new mutex;
    g_cum_times = new std::map<std::string, second_duration>;
}

void finalize_time_task() {
    delete g_cum_times;
    delete g_cum_times_mutex;
}

time_task::time_task(std::string const & category, message_builder builder, name decl) :
        m_category(category) {
    auto const & opts = builder.get_text_stream().get_options();
    if (get_profiler(opts)) {
        m_timeit = optional<xtimeit>(get_profiling_threshold(opts), [=](second_duration duration) mutable {
            builder.get_text_stream().get_stream() << m_category;
            if (decl)
                builder.get_text_stream().get_stream() << " of " << decl;
            builder.get_text_stream().get_stream() << " took " << display_profiling_time{duration} << "\n";
            builder.report();
        });
        m_parent_task = g_current_time_task;
        g_current_time_task = this;
    }
}

time_task::~time_task() {
    if (m_timeit) {
        g_current_time_task = m_parent_task;
        auto time = m_timeit->get_elapsed();
        report_profiling_time(m_category, time);
        if (m_parent_task)
            // do not report inclusive times
            report_profiling_time(m_parent_task->m_category, -time);
    }
}

/* profileit {α : Type} (category : string) (pos : position) (act : io α) : io α */
extern "C" obj_res lean_lean_profileit(obj_arg, b_obj_arg category, b_obj_arg pos, obj_arg fn, obj_arg w) {
    time_task t(string_to_std(category),
                message_builder(environment(), get_global_ios(), get_pos_info_provider()->get_file_name(),
                        pos_info(nat(cnstr_get(pos, 0), true).get_small_value(),
                                 nat(cnstr_get(pos, 1), true).get_small_value()),
                        message_severity::INFORMATION));
    return apply_1(fn, w);
}
}
