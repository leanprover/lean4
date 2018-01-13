/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam, Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {

/* Generate injectivity lemmas `*.inj`, `*.inj_arrow` and `*.inj_eq`.
   If `gen_inj_eq` is false, then `*.inj_eq` lemma is not generated.
   The `*.inj_eq` lemma is used by the simplifier.
   We don't generate it for classes because they can be expensive to generate and are rarely used in this case.
*/
environment mk_injective_lemmas(environment const & env, name const & ind_name, bool gen_inj_eq = true);

environment mk_injective_arrow(environment const & env, name const & ir_name);

expr mk_injective_type(environment const & env, name const & ir_name, expr const & ir_type, unsigned num_params, level_param_names const & lp_names);
expr mk_injective_eq_type(environment const & env, name const & ir_name, expr const & ir_type, unsigned num_params, level_param_names const & lp_names);
expr prove_injective_eq(environment const & env, expr const & inj_eq_type, name const & inj_eq_name);

name mk_injective_name(name const & ir_name);
name mk_injective_eq_name(name const & ir_name);
name mk_injective_arrow_name(name const & ir_name);

void initialize_injective();
void finalize_injective();
}
