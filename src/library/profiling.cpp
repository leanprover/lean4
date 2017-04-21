/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include "library/profiling.h"
#include "util/sexpr/option_declarations.h"

#ifndef LEAN_DEFAULT_PROFILER
#define LEAN_DEFAULT_PROFILER false
#endif

#ifndef LEAN_DEFAULT_PROFILER_THRESHOLD
#define LEAN_DEFAULT_PROFILER_THRESHOLD 0
#endif

namespace lean {

static name * g_profiler           = nullptr;
static name * g_profiler_threshold = nullptr;

bool get_profiler(options const & opts) {
    return opts.get_bool(*g_profiler, LEAN_DEFAULT_PROFILER);
}

second_duration get_profiling_threshold(options const & opts) {
    return second_duration(opts.get_double(*g_profiler_threshold, LEAN_DEFAULT_PROFILER_THRESHOLD));
}

void initialize_profiling() {
    g_profiler           = new name{"profiler"};
    g_profiler_threshold = new name{"profiler", "threshold"};
    register_bool_option(*g_profiler, LEAN_DEFAULT_PROFILER, "(profiler) profile tactics and vm_eval command");
    register_double_option(*g_profiler_threshold, LEAN_DEFAULT_PROFILER_THRESHOLD,
                           "(profiler) threshold in seconds, profiling times under threshold will not be reported");
}

void finalize_profiling() {
    delete g_profiler;
    delete g_profiler_threshold;
}

}
