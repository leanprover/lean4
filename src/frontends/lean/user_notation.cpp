/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/
#include "kernel/abstract.h"
#include "library/constants.h"
#include "library/attribute_manager.h"
#include "library/tactic/elaborator_exception.h"
#include "library/string.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_parser.h"
#include "library/quote.h"
#include "frontends/lean/elaborator.h"

namespace lean {
static environment add_user_notation(environment const & env, name const & d, unsigned prio, bool persistent) {
    auto type = env.get(d).get_type();
    bool is_nud = true;
    name tk;
    if (is_app_of(binding_domain(type), get_interactive_parse_name(), 3)) {
        auto const & parser = app_arg(binding_domain(type));
        if (is_app_of(parser, get_lean_parser_qexpr_name(), 1)) {
            is_nud = false;
            type = binding_body(type);
        }
    }
    if (is_app_of(binding_domain(type), get_interactive_parse_name(), 3)) {
        auto const & parser = app_arg(binding_domain(type));
        if (is_app_of(parser, get_lean_parser_tk_name(), 1)) {
            if (auto lit = to_string(app_arg(parser))) {
                tk = *lit;
                type = binding_body(type);
            } else {
                throw elaborator_exception(app_arg(parser),
                                           "invalid user-defined notation, token must be a name literal");
            }
        }
    }
    if (!tk) {
        throw exception("invalid user-defined notation, must start with `interactive.parse (lean.parser.tk c)` "
                                "parameter, optionally preceded by `interactive.parse lean.parser.qexpr` parameter");
    }
    expr dummy = mk_true();
    return add_notation(env, notation_entry(is_nud, {notation::transition(tk, notation::mk_ext_action(
            [=](parser & p, unsigned num, expr const * args, pos_info const &) -> expr {
                lean_assert(num == (is_nud ? 0 : 1));
                expr tactic = mk_constant(d);
                if (!is_nud)
                    tactic = mk_app(tactic, mk_pexpr_quote(args[0]));
                // `parse (tk c)` arg
                tactic = mk_app(tactic, mk_constant(get_unit_star_name()));
                for (expr t = type; is_pi(t); t = binding_body(t)) {
                    expr arg_type = binding_domain(t);
                    if (is_app_of(arg_type, get_interactive_parse_name())) {
                        tactic = mk_app(tactic, parse_interactive_param(p, arg_type));
                    } else {
                        tactic = mk_app(tactic, p.parse_expr(get_max_prec()));
                    }
                }
                tactic = p.elaborate("_user_notation", {}, tactic).first;
                tactic_state s = mk_tactic_state_for(p.env(), p.get_options(), "_user_notation", local_context(), dummy);
                type_context ctx(p.env());
                auto result = tactic::evaluator(ctx, p.get_options())(tactic, s);
                return to_expr(tactic::get_result_value(result));
            }))}, Var(0), /* overload */ persistent, prio, notation_entry_group::Main, /* parse_only */ true));
}

void initialize_user_notation() {
    register_system_attribute(basic_attribute(
            "user_notation", "user-defined notation",
            [](environment const & env, io_state const &, name const & d, unsigned prio, bool persistent) {
                return add_user_notation(env, d, prio, persistent);
            }));
}
void finalize_user_notation() {
}
}
