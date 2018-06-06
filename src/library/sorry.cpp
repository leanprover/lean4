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
expr mk_sorry(abstract_type_context & ctx, expr const & ty, bool synthetic) {
    level u = get_level(ctx, ty);
    return mk_app(mk_constant(get_sorry_ax_name(), levels(u)), ty, synthetic ? mk_bool_tt() : mk_bool_ff());
}

bool is_sorry(expr const & e) {
    return is_app_of(e, get_sorry_ax_name()) && get_app_num_args(e) >= 2;
}

bool is_synthetic_sorry(expr const & e) {
    if (!is_sorry(e)) return false;
    buffer<expr> args;
    get_app_args(e, args);
    return is_constant(args[1], get_bool_tt_name());
}

bool has_synthetic_sorry(expr const & ex) {
    return static_cast<bool>(find(ex, [] (expr const & e, unsigned) { return is_synthetic_sorry(e); }));
}

bool has_sorry(expr const & ex) {
    return static_cast<bool>(find(ex, [] (expr const & e, unsigned) { return is_sorry(e); }));
}

bool has_sorry(declaration const & decl) {
    return has_sorry(decl.get_type()) || (decl.is_definition() && has_sorry(decl.get_value()));
}

expr const & sorry_type(expr const & sry) {
    lean_assert(is_sorry(sry));
    buffer<expr> args;
    get_app_args(sry, args);
    return args[0];
}

bool has_sorry(environment const & env) {
    bool found_sorry = false;
    env.for_each_declaration([&] (declaration const & decl) {
            if (!found_sorry && has_sorry(decl)) found_sorry = true;
        });
    return found_sorry;
}
}
