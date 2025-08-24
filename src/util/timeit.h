/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <functional>
#include <string>
#include <iostream>
#include <chrono>

namespace lean {
using second_duration = std::chrono::duration<double>;

struct display_profiling_time {
    second_duration m_time;
};

std::ostream & operator<<(std::ostream & out, display_profiling_time const & time);

/** \brief Low tech timer. */
class xtimeit {
    second_duration m_threshold;
    second_duration m_excluded {0};
    std::chrono::steady_clock::time_point m_start;
    std::function<void(second_duration)> m_fn; // NOLINT
public:
    xtimeit(second_duration threshold, std::function<void(second_duration)> const & fn);
    xtimeit(std::function<void(second_duration)> const & fn) : xtimeit(second_duration(0), fn) {} // NOLINT
    xtimeit(xtimeit const &) = delete;
    xtimeit(xtimeit &&) = default;
    ~xtimeit() {
        auto diff = get_elapsed();
        if (diff >= m_threshold && m_fn) {
            m_fn(diff);
        }
    }

    second_duration get_elapsed_inclusive() const;

    second_duration get_elapsed() const {
        return get_elapsed_inclusive() - m_excluded;
    }

    void exclude_duration(second_duration d) {
        m_excluded += d;
    }
};

void initialize_timeit();
void finalize_timeit();

}
