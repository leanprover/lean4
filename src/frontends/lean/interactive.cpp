/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/
#include "library/attribute_manager.h"
#include "library/tactic/tactic_state.h"
#include "frontends/lean/pp.h"

namespace lean {
format interactive_format_type(environment const & env, options const & opts, expr const & e) {
    buffer<name> instances;
    get_system_attribute({"interactive", "type_formatter"}).get_instances(env, instances);
    vm_state vm(env, options());
    type_context tc(env);

    for (name const & inst : instances) {
        tactic_state s(env, opts, "_interactive_format_type", {}, {}, mk_true(), {});

        vm_obj r = vm.invoke(inst, {to_obj(s), to_obj(e)});
        if (tactic::is_result_success(r))
            return to_format(tactic::get_result_value(r));
    }
    auto fmter = mk_pretty_formatter_factory()(env, opts, tc);
    return fmter(e);
}

void initialize_interactive() {
    register_system_attribute(basic_attribute::with_check(
            {"interactive", "type_formatter"},
            "register a definition of type `expr → tactic format` for interactive pretty printing",
            [](environment const & env, name const & n, bool) {
                auto const & ty = env.get(n).get_type();
                if (!(is_pi(ty) && is_constant(binding_domain(ty), get_expr_name())
                                && is_app_of(binding_body(ty), get_tactic_name(), 1)
                                && is_constant(app_arg(binding_body(ty)), get_format_name())))
                    throw exception("invalid [interactive.type_formatter], must be applied to definition of type "
                                    "`expr → tactic format`");
            }));
}

void finalize_interactive() {
}
}
