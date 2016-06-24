/*
Copyright (c) 2016 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#pragma once
#include "kernel/expr_pair.h"
#include "library/head_map.h"
#include "library/type_context.h"

namespace lean {

environment add_simp_extension(environment const & env, io_state const & ios, name const & head, name const & ext_name, unsigned prio, name const & ns, bool persistent);

format pp_simp_extensions(environment const & env);

void initialize_simp_extensions();
void finalize_simp_extensions();

}
