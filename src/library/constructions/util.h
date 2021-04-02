/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/name_generator.h"
#include "kernel/type_checker.h"

namespace lean {
environment completion_add_to_black_list(environment const & env, name const & decl_name);

expr mk_pprod(type_checker & ctx, expr const & a, expr const & b, bool prop);
expr mk_pprod_mk(type_checker & ctx, expr const & a, expr const & b, bool prop);
expr mk_pprod_fst(type_checker & ctx, expr const & p, bool prop);
expr mk_pprod_snd(type_checker & ctx, expr const & p, bool prop);

name_generator mk_constructions_name_generator();
void initialize_constructions_util();
void finalize_constructions_util();
}
