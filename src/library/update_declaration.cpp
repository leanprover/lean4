/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/update_declaration.h"

namespace lean {
static declaration update_declaration(declaration d, optional<level_param_names> const & ps,
                                      optional<expr> const & type, optional<expr> const & value) {
    level_param_names _ps = ps ? *ps : d.get_univ_params();
    expr _type = type ? *type : d.get_type();
    expr _value;
    if (d.has_value()) {
        _value = value ? *value : d.get_value();
    } else {
        lean_assert(!value);
    }
    if (d.is_axiom()) {
        if (is_eqp(d.get_type(), _type) && is_eqp(d.get_univ_params(), _ps))
            return d;
        return mk_axiom(d.get_name(), _ps, _type, d.is_meta());
    } else {
        if (is_eqp(d.get_type(), _type) && is_eqp(d.get_value(), _value) && is_eqp(d.get_univ_params(), _ps))
            return d;
        if (d.is_theorem())
            return mk_theorem(d.get_name(), _ps, _type, _value);
        else
            return mk_definition(d.get_name(), _ps, _type, _value, d.get_hints(), d.is_meta());
    }
}

declaration update_declaration_univ_params(declaration const & d, level_param_names const & ps) {
    return update_declaration(d, optional<level_param_names>(ps), none_expr(), none_expr());
}

declaration update_declaration_type(declaration const & d, expr const & type) {
    return update_declaration(d, optional<level_param_names>(), some_expr(type), none_expr());
}

declaration update_declaration_value(declaration const & d, expr const & value) {
    return update_declaration(d, optional<level_param_names>(), none_expr(), some_expr(value));
}

declaration update_declaration(declaration const & d, level_param_names const & ps, expr const & type, expr const & value) {
    return update_declaration(d, optional<level_param_names>(ps), some_expr(type), some_expr(value));
}
declaration update_declaration(declaration const & d, level_param_names const & ps, expr const & type) {
    return update_declaration(d, optional<level_param_names>(ps), some_expr(type), none_expr());
}
}
