/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/
#pragma once
#include <string>
#include "library/message_builder.h"
#include "library/profiling.h"
#include "util/timeit.h"

namespace lean {
void report_profiling_time(std::string const & category, second_duration time);
void display_cumulative_profiling_times(std::ostream & out);

/** Measure time of some task and report it for the final cumulative profile. */
class time_task {
    std::string     m_category;
    optional<xtimeit> m_timeit;
public:
    time_task(std::string const & category, message_builder builder, options const & opts, name decl = name()):
            m_category(category) {
        if (get_profiler(opts)) {
            m_timeit = optional<xtimeit>(get_profiling_threshold(opts), [=](second_duration duration) mutable {
                builder.get_text_stream().get_stream() << m_category;
                if (decl)
                    builder.get_text_stream().get_stream() << " of " << decl;
                builder.get_text_stream().get_stream() << " took " << display_profiling_time{duration} << "\n";
                builder.report();
            });
        }
    }

    ~time_task() {
        if (m_timeit)
            report_profiling_time(m_category, m_timeit->get_elapsed());
    }
};

void initialize_time_task();
void finalize_time_task();
}
