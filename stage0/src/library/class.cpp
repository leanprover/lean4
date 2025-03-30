/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/io.h"
#include "library/class.h"

namespace lean {
extern "C" uint8 lean_is_class(object* env, object* n);
extern "C" uint8 lean_is_instance(object* env, object* n);
extern "C" uint8 lean_is_out_param(object* e);
extern "C" uint8 lean_has_out_params(object* env, object* n);

bool is_class_out_param(expr const & e) { return lean_is_out_param(e.to_obj_arg()); }
bool has_class_out_params(elab_environment const & env, name const & c) { return lean_has_out_params(env.to_obj_arg(), c.to_obj_arg()); }
bool is_class(elab_environment const & env, name const & c) { return lean_is_class(env.to_obj_arg(), c.to_obj_arg()); }
bool is_instance(elab_environment const & env, name const & i) { return lean_is_instance(env.to_obj_arg(), i.to_obj_arg()); }

static name * g_anonymous_inst_name_prefix = nullptr;

name const & get_anonymous_instance_prefix() {
    return *g_anonymous_inst_name_prefix;
}

name mk_anonymous_inst_name(unsigned idx) {
    return g_anonymous_inst_name_prefix->append_after(idx);
}

bool is_anonymous_inst_name(name const & n) {
    // remove mangled macro scopes
    auto n2 = n.get_root();
    if (!n2.is_string()) return false;
    return strncmp(n2.get_string().data(),
                   g_anonymous_inst_name_prefix->get_string().data(),
                   strlen(g_anonymous_inst_name_prefix->get_string().data())) == 0;
}


void initialize_class() {
    g_anonymous_inst_name_prefix = new name("_inst");
    mark_persistent(g_anonymous_inst_name_prefix->raw());
}

void finalize_class() {
    delete g_anonymous_inst_name_prefix;
}
}
