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
#include "library/profiling.h"

namespace lean {
using second_duration = std::chrono::duration<double>;

struct display_profiling_time {
    second_duration m_time;
};

/** \brief Low tech timer. */
class xtimeit {
    prof_clock::duration m_threshold;
    prof_clock::duration m_excluded {0};
    prof_clock::time_point m_start;
    std::function<void(prof_clock::duration)> m_fn; // NOLINT
public:
    xtimeit(prof_clock::duration threshold, std::function<void(prof_clock::duration)> const & fn): // NOLINT
        m_threshold(threshold), m_fn(fn) {
        m_start = prof_clock::now();
    }
    xtimeit(std::function<void(prof_clock::duration)> const & fn) : xtimeit(prof_clock::duration(0), fn) {} // NOLINT
    xtimeit(xtimeit const &) = delete;
    xtimeit(xtimeit &&) = default;
    ~xtimeit() {
        auto diff = get_elapsed();
        if (diff >= m_threshold && m_fn) {
            m_fn(diff);
        }
    }

    prof_clock::duration get_elapsed_inclusive() const {
        auto end = prof_clock::now();
        return end - m_start;
    }

    prof_clock::duration get_elapsed() const {
        return get_elapsed_inclusive() - m_excluded;
    }

    void exclude_duration(prof_clock::duration d) {
        m_excluded += d;
    }

    void ignore(xtimeit const & ignored) {
        // propagate nested times as usual,
        exclude_duration(ignored.m_excluded);
        // but exclude this block's time from the directly surrounding task only by adjusting its start time
        m_start += ignored.get_elapsed();
        // For example, if elaboration calls an interpreted tactic (without its own category) that calls `simp`,
        // we subtract the `simp` time from both surrounding categories as usual.
        // However, if the tactic also spends some time in uncategorized native code,
        // we subtract it from the interpretation category only by adjusting `m_start`,
        // which effectively adds the time to the surrounding `elaboration` category instead.
    }
};

std::ostream & operator<<(std::ostream & out, display_profiling_time const & time);
}
