/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include "util/timeit.h"
#include <iomanip>

namespace lean {

std::ostream & operator<<(std::ostream & out, display_profiling_time const & time) {
    out << std::setprecision(3);
    if (time.m_time < second_duration(1)) {
        out << std::chrono::duration<double, std::milli>(time.m_time).count() << "ms";
    } else {
        out << time.m_time.count() << "s";
    }
    return out;
}

}
