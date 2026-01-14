/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include "library/profiling.h"
#include "util/option_declarations.h"

namespace lean {

extern "C" uint8_t lean_get_profiler(obj_arg opts);
bool get_profiler(options const & opts) {
    return lean_get_profiler(opts.to_obj_arg());
}

extern "C" double lean_get_profiler_threshold(obj_arg opts);
second_duration get_profiling_threshold(options const & opts) {
    double ms = lean_get_profiler_threshold(opts.to_obj_arg());
    return second_duration(ms);
}

void initialize_profiling() {
}

void finalize_profiling() {
}

}
