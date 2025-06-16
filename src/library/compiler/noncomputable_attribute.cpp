/*
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Cameron Zwarich
*/
#include "library/elab_environment.h"
namespace lean {
extern "C" bool lean_is_noncomputable(object*, object*);

bool has_noncomputable_attribute(elab_environment const & env, name const & n) {
    return lean_is_noncomputable(env.to_obj_arg(), n.to_obj_arg());
}
}
