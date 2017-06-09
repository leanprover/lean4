/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/
#include <string>
#include "kernel/abstract.h"
#include "library/constants.h"
#include "library/attribute_manager.h"
#include "library/scoped_ext.h"
#include "library/tactic/elaborator_exception.h"
#include "library/string.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_parser.h"
#include "library/quote.h"
#include "library/placeholder.h"
#include "frontends/lean/elaborator.h"

namespace lean {
static environment add_user_command(environment const & env, name const & d) {
    auto type = env.get(d).get_type();
    bool takes_meta_infos = false;
    if (is_binding(type) && is_constant(binding_domain(type), {"interactive", "decl_meta_info"})) {
        takes_meta_infos = true;
        type = binding_body(type);
    }
    std::string tk;
    if (is_binding(type) && is_app_of(binding_domain(type), get_interactive_parse_name(), 3)) {
        auto const & parser = app_arg(binding_domain(type));
        if (is_app_of(parser, get_lean_parser_tk_name(), 1)) {
            if (auto lit = to_string(app_arg(parser))) {
                tk = *lit;
                type = binding_body(type);
            } else {
                throw elaborator_exception(app_arg(parser),
                                           "invalid user-defined command, token must be a name literal");
            }
        }
    } else {
        throw exception("invalid user-defined command, must take `interactive.parse (lean.parser.tk c)` parameter, "
                        "optionally preceded by `interactive.decl_meta_info` parameter");
    }

    if (!(is_app_of(type, get_lean_parser_name(), 1) && is_constant(app_arg(type), get_unit_name()))) {
        throw exception("invalid user-defined command, must return type `lean.parser unit`");
    }

    expr dummy = mk_true();

    auto run = [=](parser & p, cmd_meta const & meta) {
        expr parser = mk_constant(d);
        // we don't want to reflect `meta` into an expr, so abstract the parameter and pass it as a vm_obj arg
        if (takes_meta_infos) {
            parser = mk_app(parser, mk_var(0));
        }
        // `parse (tk c)` arg
        parser = mk_app(parser, mk_constant(get_unit_star_name()));
        for (expr t = type; is_pi(t); t = binding_body(t)) {
            expr arg_type = binding_domain(t);
            if (is_app_of(arg_type, get_interactive_parse_name())) {
                parser = mk_app(parser, parse_interactive_param(p, arg_type));
            } else {
                expr e = p.parse_expr(get_max_prec());
                if (!closed(e) || has_local(e)) {
                    throw elaborator_exception(e, "invalid argument to user-defined command, must be closed term");
                }
                parser = mk_app(parser, e);
            }
        }
        buffer<vm_obj> args;
        if (takes_meta_infos) {
            parser = mk_lambda("a", mk_expr_placeholder(), parser);
            args.push_back(to_obj(meta));
        }
        parser = p.elaborate("_user_command", {}, parser).first;
        run_parser(p, parser, args);
        return p.env();
    };

    if (takes_meta_infos) {
        return add_command(env, tk, cmd_info(tk, "description", run));
    } else {
        return add_command(env, tk, cmd_info(tk, "description", [=](parser & p) { return run(p, {}); }));
    }
}

struct user_command_modification : public modification {
    LEAN_MODIFICATION("USR_CMD")

    name m_name;

    user_command_modification() {}
    user_command_modification(name const & name) : m_name(name) {}

    void perform(environment & env) const override {
        env = add_user_command(env, m_name);
    }

    void serialize(serializer & s) const override {
        s << m_name;
    }

    static std::shared_ptr<modification const> deserialize(deserializer & d) {
        return std::make_shared<user_command_modification>(read_name(d));
    }
};
void initialize_user_command() {
    user_command_modification::init();
    register_system_attribute(basic_attribute(
            "user_command", "user-defined command",
            [](environment const & env, io_state const &, name const & d, unsigned, bool persistent) {
                if (persistent) {
                    return module::add_and_perform(env, std::make_shared<user_command_modification>(d));
                } else {
                    throw exception("[user_command] cannot be used locally");
                }
            }));
}
void finalize_user_command() {
    user_command_modification::finalize();
}
}
