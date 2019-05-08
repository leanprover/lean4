/*
Copyright (c) 2018 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Sebastian Ullrich

Lean interface to the kernel environment type and extensions
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
environment const & to_environment(b_obj_arg o);
obj_res to_lean_environment(environment const & env);
void initialize_lean_environment();
void finalize_lean_environment();
}
