/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/module.h"
#include "library/util.h"

namespace lean {
/*
@[export lean.cache_closed_term_name_core]
def cacheClosedTermName (env : Environment) (e : Expr) (n : Name) : Environment :=

@[export lean.get_closed_term_name]
def getClosedTermName (env : Environment) (e : Expr) : Option Name :=
*/
object * cache_closed_term_name_core(object * env, object * e, object * n);
object * get_closed_term_name_core(object * env, object * e);

optional<name> get_closed_term_name(environment const & env, expr const & e) {
    return to_optional<name>(get_closed_term_name_core(env.get_obj_arg(), e.get_obj_arg()));
}

environment cache_closed_term_name(environment const & env, expr const & e, name const & n) {
    return environment(cache_closed_term_name_core(env.get_obj_arg(), e.get_obj_arg(), n.get_obj_arg()));
}
}
