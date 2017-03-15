/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/
#include <string>
#include <vector>
#include "util/utf8.h"
#include "util/lean_path.h"
#include "library/module_mgr.h"
#include "library/versioned_msg_buf.h"
#include "library/attribute_manager.h"
#include "frontends/lean/pp.h"
#include "shell/completion.h"

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

void report_completions(environment const & env, options const & opts, pos_info const & pos, bool skip_completions,
                        char const * mod_path, break_at_pos_exception const & e, json & j) {
    unsigned offset = pos.second - e.m_token_info.m_pos.second;
    std::string prefix = e.m_token_info.m_token.to_string();
    if (auto stop = utf8_char_pos(prefix.c_str(), offset))
        prefix = prefix.substr(0, *stop);
    switch (e.m_token_info.m_context) {
        case break_at_pos_exception::token_context::expr:
            // no empty prefix completion for declarations
            if (!prefix.size())
                return;
            if (!skip_completions)
                j["completions"] = get_decl_completions(prefix, env, opts);
            break;
        case break_at_pos_exception::token_context::field:
            if (!skip_completions)
                j["completions"] = get_field_completions(e.m_token_info.m_struct, prefix, env, opts);
            break;
        case break_at_pos_exception::token_context::option:
            if (!skip_completions)
                j["completions"] = get_option_completions(prefix, opts);
            break;
        case break_at_pos_exception::token_context::import:
            if (!skip_completions)
                j["completions"] = get_import_completions(prefix, dirname(mod_path),
                                                          opts);
            break;
        case break_at_pos_exception::token_context::interactive_tactic:
            if (!skip_completions)
                j["completions"] = get_interactive_tactic_completions(
                        prefix, e.m_token_info.m_tac_class, env, opts);
            break;
        case break_at_pos_exception::token_context::attribute:
            if (!skip_completions)
                j["completions"] = get_attribute_completions(prefix, env, opts);
            break;
        case break_at_pos_exception::token_context::namespc:
            if (!skip_completions)
                j["completions"] = get_namespace_completions(prefix, env, opts);
            break;
        case break_at_pos_exception::token_context::none:
        case break_at_pos_exception::token_context::notation:
            return;
    }
    j["prefix"] = prefix;
}

void report_info(environment const & env, options const & opts, io_state const & ios, module_info const & m_mod_info,
                 std::vector<info_manager> const & info_managers, break_at_pos_exception const & e, json & j) {
    json record;

    // info data not dependent on elaboration/info_manager
    auto const & tk = e.m_token_info.m_token;
    if (tk.size()) {
        switch (e.m_token_info.m_context) {
            case break_at_pos_exception::token_context::attribute:
                record["doc"] = get_attribute(env, tk).get_description();
                add_source_info(env, tk, record);
                break;
            case break_at_pos_exception::token_context::import: {
                auto parsed = parse_import(tk.to_string());
                try {
                    auto f = find_file(m_mod_info.m_mod, parsed.first, string_to_name(parsed.second),
                                       ".lean");
                    record["source"]["file"] = f;
                    record["source"]["line"] = 1;
                    record["source"]["column"] = 0;
                } catch (file_not_found_exception) {}
                break;
            }
            case break_at_pos_exception::token_context::option:
                if (auto it = get_option_declarations().find(tk))
                    record["doc"] = it->get_description();
                break;
            default:
                break;
        }
    }

    for (auto & infom : info_managers) {
        if (infom.get_file_name() == m_mod_info.m_mod) {
            if (e.m_goal_pos) {
                infom.get_info_record(env, opts, ios, e.m_goal_pos->first,
                                      e.m_goal_pos->second, record, [](info_data const & d) {
                            return dynamic_cast<vm_obj_format_info const *>(d.raw());
                        });
            }
            infom.get_info_record(env, opts, ios, e.m_token_info.m_pos.first,
                                  e.m_token_info.m_pos.second, record);
        }
    }

    if (!record.is_null())
        j["record"] = record;
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
