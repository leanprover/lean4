/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <time.h>
#include <functional>
#include <string>
#include <iostream>
#include <iomanip>

namespace lean {
/** \brief Low tech timer. */
class timeit {
    double         m_threshold; // we only display the result if time > m_threshold
    clock_t        m_start;
    std::ostream & m_out;
    std::string    m_msg;
public:
    timeit(std::ostream & out, char const * msg, double threshold):
        m_threshold(threshold), m_out(out), m_msg(msg) {
        m_start = clock();
    }
    timeit(std::ostream & out, char const * msg):timeit(out, msg, -0.1) {}
    ~timeit() {
        clock_t end = clock();
        double result = ((static_cast<double>(end) - static_cast<double>(m_start)) / CLOCKS_PER_SEC);
        if (result > m_threshold) {
            m_out << m_msg << " " << std::fixed << std::setprecision(5) << result << " secs\n";
        }
    }
};

/** \brief Low tech timer. */
class xtimeit {
    double     m_threshold; // we only display the result if time > m_threshold
    clock_t    m_start;
    std::function<void(double)> m_fn;
public:
    xtimeit(double threshold, std::function<void(double)> const & fn):
        m_threshold(threshold), m_fn(fn) {
        m_start = clock();
    }
    xtimeit(std::function<void(double)> const & fn):xtimeit(-0.1, fn) {}
    ~xtimeit() {
        clock_t end = clock();
        double result = ((static_cast<double>(end) - static_cast<double>(m_start)) / CLOCKS_PER_SEC);
        if (result > m_threshold) {
            m_fn(result);
        }
    }
};
}
