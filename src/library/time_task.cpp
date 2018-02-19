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
}
