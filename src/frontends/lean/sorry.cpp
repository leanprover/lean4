/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/type_checker.h"
#include "kernel/environment.h"
#include "library/module.h"

namespace lean {
static name g_sorry_name("sorry");
static expr g_sorry(mk_constant(g_sorry_name));
static name  g_l("l");
static expr  g_sorry_type(mk_pi("A", mk_sort(mk_param_univ(g_l)), mk_var(0), binder_info(true)));

bool has_sorry(environment const & env) {
    auto decl = env.find(g_sorry_name);
    return decl && decl->get_type() == g_sorry_type;
}

environment declare_sorry(environment const & env) {
    if (auto decl = env.find(g_sorry_name)) {
        if (decl->get_type() != g_sorry_type)
            throw exception("failed to declare 'sorry', environment already has an object named 'sorry'");
        return env;
    } else {
        return module::add(env, check(env, mk_var_decl(g_sorry_name, list<name>(g_l), g_sorry_type)));
    }
}

expr const & get_sorry_constant() {
    return g_sorry;
}
}
