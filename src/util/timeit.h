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
class timeit {
    second_duration m_threshold;
    std::chrono::steady_clock::time_point m_start;
    std::ostream & m_out;
    std::string    m_msg;
public:
    timeit(std::ostream & out, char const * msg, second_duration threshold):
        m_threshold(threshold), m_out(out), m_msg(msg) {
        m_start = std::chrono::steady_clock::now();
    }
    timeit(std::ostream & out, char const * msg) : timeit(out, msg, second_duration(0)) {}
    ~timeit() {
        auto end = std::chrono::steady_clock::now();
        auto diff = second_duration(end - m_start);
        if (diff >= m_threshold) {
            m_out << m_msg << " " << display_profiling_time{diff} << "\n";
        }
    }
};

/** \brief Low tech timer. */
class xtimeit {
    second_duration m_threshold;
    std::chrono::steady_clock::time_point m_start;
    std::function<void(second_duration)> m_fn; // NOLINT
public:
    xtimeit(second_duration threshold, std::function<void(second_duration)> const & fn): // NOLINT
        m_threshold(threshold), m_fn(fn) {
        m_start = std::chrono::steady_clock::now();
    }
    xtimeit(std::function<void(second_duration)> const & fn) : xtimeit(second_duration(0), fn) {} // NOLINT
    xtimeit(xtimeit const &) = delete;
    xtimeit(xtimeit &&) = default;
    ~xtimeit() {
        auto diff = get_elapsed();
        if (diff >= m_threshold && m_fn) {
            m_fn(diff);
        }
    }

    second_duration get_elapsed() const {
        auto end = std::chrono::steady_clock::now();
        return second_duration(end - m_start);
    }
};

}
