/*
Copyright (c) 2018 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Sebastian Ullrich

Lean interface to the kernel environment type and extensions
*/

#include <string>
#include <iostream>
#include "library/replace_visitor.h"
#include "library/placeholder.h"
#include "library/explicit.h"
#include "library/annotation.h"
#include "util/timeit.h"
#include "library/locals.h"
#include "library/trace.h"
#include "frontends/lean/elaborator.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/decl_cmds.h"
#include "frontends/lean/definition_cmds.h"
#include "frontends/lean/brackets.h"
#include "frontends/lean/choice.h"
#include "frontends/lean/inductive_cmds.h"
#include "frontends/lean/structure_cmd.h"
#include "frontends/lean/util.h"
#include "frontends/lean/pp.h"
#include "frontends/lean/simple_pos_info_provider.h"

namespace lean {
void env_finalizer(void * env) {
    delete static_cast<environment*>(env);
}

void env_foreach(void * /* env */, b_obj_arg /* fn */) {
    // TODO(leo, kha)
    throw exception("unimplemented: sharing `environment` across threads");
}

static external_object_class * g_env_class = nullptr;

environment const & to_environment(b_obj_arg o) {
    lean_assert(external_class(o) == g_env_class);
    return *static_cast<environment *>(external_data(o));
}

obj_res to_lean_environment(environment const & env) {
    return alloc_external(g_env_class, new environment(env));
}

extern "C" obj_res lean_environment_mk_empty(b_obj_arg) {
    return to_lean_environment(environment());
}

extern "C" uint8 lean_environment_contains(b_obj_arg lean_environment, b_obj_arg vm_n) {
    return static_cast<uint8>(static_cast<bool>(to_environment(lean_environment).find(name(vm_n, true))));
}

void initialize_lean_environment() {
    g_env_class = register_external_object_class(env_finalizer, env_foreach);
}
void finalize_lean_environment() {
}
}
