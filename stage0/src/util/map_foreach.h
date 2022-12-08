/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <functional>
#include "runtime/object.h"

namespace lean {
/* Helper functions for iterating over Lean maps. */
void rbmap_foreach(b_obj_arg m, std::function<void(b_obj_arg, b_obj_arg)> const & fn);
void phashmap_foreach(b_obj_arg m, std::function<void(b_obj_arg, b_obj_arg)> const & fn);
void hashmap_foreach(b_obj_arg m, std::function<void(b_obj_arg, b_obj_arg)> const & fn);
void smap_foreach(b_obj_arg m, std::function<void(b_obj_arg, b_obj_arg)> const & fn);
}
