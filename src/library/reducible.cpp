/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/sstream.h"
#include "kernel/environment.h"
#include "kernel/type_checker.h"
#include "library/kernel_serializer.h"
#include "library/scoped_ext.h"
#include "library/reducible.h"
#include "library/attribute_manager.h"

namespace lean {
void initialize_reducible() {
    register_no_params_attribute("reducible", "reducible");
    register_no_params_attribute("semireducible", "semireducible");
    register_no_params_attribute("irreducible", "irreducible");

    register_incompatible("reducible", "semireducible");
    register_incompatible("reducible", "irreducible");
    register_incompatible("semireducible", "irreducible");
}

void finalize_reducible() {
}

static void check_declaration(environment const & env, name const & n) {
    declaration const & d = env.get(n);
    if (!d.is_definition())
        throw exception(sstream() << "invalid reducible command, '" << n << "' is not a definition");
}

environment set_reducible(environment const & env, name const & n, reducible_status s, bool persistent) {
    check_declaration(env, n);
    return set_attribute(env, get_dummy_ios(),
                         s == reducible_status::Reducible ? "reducible" :
                         s == reducible_status::Irreducible ? "irreducible" :
                         "semireducible", n, persistent);
}

reducible_status get_reducible_status(environment const & env, name const & n) {
    if (has_attribute(env, "reducible", n))
        return reducible_status::Reducible;
    else if (has_attribute(env, "irreducible", n))
        return reducible_status::Irreducible;
    else
        return reducible_status::Semireducible;
}

name_predicate mk_not_reducible_pred(environment const & env) {
    return [=](name const & n) { // NOLINT
        return !has_attribute(env, "reducible", n);
    };
}

name_predicate mk_irreducible_pred(environment const & env) {
    return [=](name const & n) { // NOLINT
        return has_attribute(env, "irreducible", n);
    };
}

old_type_checker_ptr mk_type_checker(environment const & env, reducible_behavior rb) {
    switch (rb) {
    case UnfoldReducible:
        return mk_type_checker(env, mk_not_reducible_pred(env));
    case UnfoldSemireducible:
        return mk_type_checker(env, mk_irreducible_pred(env));
    }
    lean_unreachable();
}

old_type_checker_ptr mk_opaque_type_checker(environment const & env) {
    return mk_type_checker(env, [](name const &) { return true; });
}
}
