/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam, Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {

environment mk_injective_lemmas(environment const & env, name const & ind_name);

environment mk_injective_arrow(environment const & env, name const & ir_name);

expr mk_injective_type(environment const & env, name const & ir_name, expr const & ir_type, unsigned num_params, level_param_names const & lp_names);

name mk_injective_name(name const & ir_name);
name mk_injective_arrow_name(name const & ir_name);

void initialize_injective();
void finalize_injective();
}
