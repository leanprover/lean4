/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "library/class.h"

namespace lean {
uint8 is_class_core(object* env, object* n);
uint8 is_instance_core(object* env, object* n);
object* get_class_instances_core(object* env, object* n);
uint8 is_out_param_core(object* e);
uint8 has_out_params_core(object* env, object* n);
object* add_instance_core(object* env, object* n);

bool is_class_out_param(expr const & e) { return is_out_param_core(e.to_obj_arg()); }
bool has_class_out_params(environment const & env, name const & c) { return has_out_params_core(env.to_obj_arg(), c.to_obj_arg()); }
bool is_class(environment const & env, name const & c) { return is_class_core(env.to_obj_arg(), c.to_obj_arg()); }
bool is_instance(environment const & env, name const & i) { return is_instance_core(env.to_obj_arg(), i.to_obj_arg()); }
names get_class_instances(environment const & env, name const & c) { return names(get_class_instances_core(env.to_obj_arg(), c.to_obj_arg())); }

environment add_instance(environment const & env, name const & n, bool persistent) {
    if (!persistent) throw exception("local instances have been disabled");
    return get_except_value<environment>(add_instance_core(env.to_obj_arg(), n.to_obj_arg()));
}

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
}

void finalize_class() {
    delete g_anonymous_inst_name_prefix;
}
}
