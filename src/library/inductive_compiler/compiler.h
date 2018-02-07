/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#pragma once
#include "kernel/environment.h"
#include "frontends/lean/type_util.h"
#include "library/util.h"
#include "library/inductive_compiler/ginductive_decl.h"

namespace lean {
environment add_inner_inductive_declaration(environment const & env, name_generator & ngen, options const & opts,
                                            name_map<implicit_infer_kind> implicit_infer_map,
                                            ginductive_decl & decl, bool is_trusted);

void initialize_inductive_compiler();
void finalize_inductive_compiler();

}
