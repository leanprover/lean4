/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once
#include <chrono>
#include <util/options.h>

namespace lean {

using second_duration = std::chrono::duration<double>;

LEAN_EXPORT bool get_profiler(options const &);
LEAN_EXPORT second_duration get_profiling_threshold(options const &);

void initialize_profiling();
void finalize_profiling();

}
