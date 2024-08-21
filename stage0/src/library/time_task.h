/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/
#pragma once
#include <string>
#include "library/profiling.h"
#include "util/timeit.h"
#include "util/message_definitions.h"

namespace lean {
LEAN_EXPORT void report_profiling_time(std::string const & category, second_duration time);
LEAN_EXPORT void display_cumulative_profiling_times(std::ostream & out);

/** Measure time of some task and report it for the final cumulative profile. */
class LEAN_EXPORT time_task {
    std::string     m_category;
    optional<xtimeit> m_timeit;
    time_task *     m_parent_task;
public:
    time_task(std::string const & category, options const & opts, name decl = name());
    ~time_task();
};

void initialize_time_task();
void finalize_time_task();
}
