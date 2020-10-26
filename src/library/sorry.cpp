/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "kernel/find_fn.h"
#include "kernel/for_each_fn.h"
#include "kernel/environment.h"
#include "library/sorry.h"
#include "library/constants.h"
#include "library/util.h"

namespace lean {
bool is_sorry(expr const & e) {
    return is_app_of(e, get_sorry_ax_name()) && get_app_num_args(e) >= 2;
}

bool is_synthetic_sorry(expr const & e) {
    if (!is_sorry(e)) return false;
    buffer<expr> args;
    get_app_args(e, args);
    return is_constant(args[1], get_bool_true_name());
}

bool has_synthetic_sorry(expr const & ex) {
    return static_cast<bool>(find(ex, [] (expr const & e, unsigned) { return is_synthetic_sorry(e); }));
}

bool has_sorry(expr const & ex) {
    return static_cast<bool>(find(ex, [] (expr const & e, unsigned) { return is_sorry(e); }));
}

bool has_sorry(declaration const & decl) {
    switch (decl.kind()) {
    case declaration_kind::Axiom:            return has_sorry(decl.to_axiom_val().get_type());
    case declaration_kind::Definition:       return has_sorry(decl.to_definition_val().get_type()) || has_sorry(decl.to_definition_val().get_value());
    case declaration_kind::Theorem:          return has_sorry(decl.to_theorem_val().get_type()) || has_sorry(decl.to_theorem_val().get_value());
    case declaration_kind::Opaque:           return has_sorry(decl.to_opaque_val().get_type()) || has_sorry(decl.to_opaque_val().get_value());
    case declaration_kind::Quot:             return false;
    case declaration_kind::Inductive:        return false; // TODO(Leo):
    case declaration_kind::MutualDefinition: return false; // TODO(Leo):
    }
    lean_unreachable();
}

bool has_sorry(constant_info const & info) {
    return has_sorry(info.get_type()) || (info.has_value() && has_sorry(info.get_value()));
}

expr const & sorry_type(expr const & sry) {
    lean_assert(is_sorry(sry));
    buffer<expr> args;
    get_app_args(sry, args);
    return args[0];
}

bool has_sorry(environment const & env) {
    bool found_sorry = false;
    env.for_each_constant([&] (constant_info const & info) {
            if (!found_sorry && has_sorry(info)) found_sorry = true;
        });
    return found_sorry;
}
}
