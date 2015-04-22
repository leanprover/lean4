/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/aliases.h"
#include "frontends/lean/type_util.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/util.h"

namespace lean {
void type_modifiers::parse(parser & p) {
    while (true) {
        if (p.curr_is_token(get_class_tk())) {
            m_is_class = true;
            p.next();
        } else {
            break;
        }
    }
}

environment add_alias(parser & p, environment env, bool composite,
                      name const & full_id, levels const & ctx_levels, buffer<expr> const & ctx_params) {
    name id;
    if (composite)
        id = name(name(full_id.get_prefix().get_string()), full_id.get_string());
    else
        id = name(full_id.get_string());
    if (!empty(ctx_levels) || !ctx_params.empty()) {
        expr r = mk_local_ref(full_id, ctx_levels, ctx_params);
        env = p.add_local_ref(env, id, r);
    }
    if (full_id != id)
        env = add_expr_alias_rec(env, id, full_id);
    return env;
}

implicit_infer_kind parse_implicit_infer_modifier(parser & p) {
    if (p.curr_is_token(get_lcurly_tk())) {
        p.next();
        p.check_token_next(get_rcurly_tk(), "invalid introduction rule, '}' expected");
        return implicit_infer_kind::RelaxedImplicit;
    } else if (p.curr_is_token(get_lparen_tk())) {
        p.next();
        p.check_token_next(get_rparen_tk(), "invalid introduction rule, ')' expected");
        return implicit_infer_kind::None;
    } else {
        return implicit_infer_kind::Implicit;
    }
}
}
