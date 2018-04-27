/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/
#include "kernel/abstract.h"
#include "library/constants.h"
#include "library/attribute_manager.h"
#include "library/scoped_ext.h"
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
    if (is_binding(type) && is_app_of(binding_domain(type), get_interactive_parse_name(), 3)) {
        auto const & parser = app_arg(binding_domain(type));
        if (is_app_of(parser, get_lean3_parser_pexpr_name(), 1)) {
            is_nud = false;
            type = binding_body(type);
        }
    }
    if (is_binding(type) && is_app_of(binding_domain(type), get_interactive_parse_name(), 3)) {
        auto const & parser = app_arg(binding_domain(type));
        if (is_app_of(parser, get_lean3_parser_tk_name(), 1)) {
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
                                "parameter, optionally preceded by `interactive.parse lean.parser.pexpr` parameter");
    }

    expr t = type;
    while (is_pi(t)) { t = binding_body(t); }
    if (!is_app_of(t, get_lean3_parser_name(), 1)) {
        throw exception("invalid user-defined notation, must return type `lean.parser p`");
    }

    expr dummy = mk_true();
    persistence persist = persistent ? persistence::file : persistence::scope;

    return add_notation(env, notation_entry(is_nud, {notation::transition(tk, notation::mk_ext_action(
            [=](parser & p, unsigned num, expr const * args, pos_info const & pos) -> expr {
                lean_always_assert(num == (is_nud ? 0 : 1));
                expr parser = mk_constant(d);
                if (!is_nud)
                    parser = mk_app(parser, mk_pexpr_quote(args[0]));
                // `parse (tk c)` arg
                parser = mk_app(parser, mk_constant(get_unit_star_name()));
                for (expr t = type; is_pi(t); t = binding_body(t)) {
                    expr arg_type = binding_domain(t);
                    if (is_app_of(arg_type, get_interactive_parse_name())) {
                        parser = mk_app(parser, parse_interactive_param(p, arg_type));
                    } else {
                        expr e = p.parse_expr(get_max_prec());
                        if (!closed(e) || has_local(e)) {
                            throw elaborator_exception(e, "invalid argument to user-defined notation, must be closed term");
                        }
                        parser = mk_app(parser, e);
                    }
                }
                parser = p.elaborate("_user_notation", {}, parser).first;
                try {
                    return to_expr(run_parser(p, parser));
                } catch (formatted_exception const & ex) {
                    if (ex.get_pos() && *ex.get_pos() >= pos) {
                        throw;
                    } else {
                        throw formatted_exception(some(pos), ex.pp());
                    }
                }
            }))}, Var(0), /* overload */ persistent, prio, notation_entry_group::Main, /* parse_only */ true), persist);
}

struct user_notation_modification : public modification {
    LEAN_MODIFICATION("USR_NOTATION")

    name m_name;

    user_notation_modification() {}
    user_notation_modification(name const & name) : m_name(name) {}

    void perform(environment & env) const override {
        unsigned prio = get_attribute(env, "user_notation").get_prio(env, m_name);
        env = add_user_notation(env, m_name, prio, /* persistent */ true);
    }

    void serialize(serializer & s) const override {
        s << m_name;
    }

    static std::shared_ptr<modification const> deserialize(deserializer & d) {
        return std::make_shared<user_notation_modification>(read_name(d));
    }
};
void initialize_user_notation() {
    user_notation_modification::init();
    register_system_attribute(basic_attribute(
            "user_notation", "user-defined notation",
            [](environment const & env, io_state const &, name const & d, unsigned prio, bool persistent) {
                if (persistent) {
                    return module::add_and_perform(env, std::make_shared<user_notation_modification>(d));
                } else {
                    return add_user_notation(env, d, prio, persistent);
                }
            }));
}
void finalize_user_notation() {
    user_notation_modification::finalize();
}
}
