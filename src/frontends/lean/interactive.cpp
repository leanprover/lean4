/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/
#include <string>
#include <vector>
#include "util/utf8.h"
#include "util/lean_path.h"
#include "util/sexpr/option_declarations.h"
#include "library/module_mgr.h"
#include "library/constants.h"
#include "library/documentation.h"
#include "library/attribute_manager.h"
#include "library/vm/vm.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_format.h"
#include "frontends/lean/completion.h"
#include "frontends/lean/interactive.h"
#include "frontends/lean/pp.h"
#include "frontends/lean/tactic_notation.h"

namespace lean {
LEAN_THREAD_VALUE(break_at_pos_exception::token_context, g_context, break_at_pos_exception::token_context::none);

void interactive_report_type(environment const & env, options const & opts, expr const & e, json & j) {
    type_context tc(env);
    if (g_context == break_at_pos_exception::token_context::interactive_tactic) {
        vm_state vm(env, options());
        tactic_state s = mk_tactic_state_for(env, opts, "_interactive_report_type", local_context(), mk_true());
        std::vector<std::string> params;

        for (expr d = e; is_pi(d); d = binding_body(d)) {
            vm_obj r = vm.invoke(get_interactive_param_desc_name(), {to_obj(s), to_obj(binding_domain(d))});
            format f;
            if (tactic::is_result_success(r))
                f = to_format(tactic::get_result_value(r));
            else
                f = format("<error while executing ") + format(get_interactive_param_desc_name()) + format(": ") +
                    std::get<0>(*tactic::is_exception(vm, r)) + format(">");
            sstream ss;
            ss << mk_pair(flatten(f), opts);
            params.push_back(ss.str());
        }
        j["tactic_params"] = params;
    }
    format f = mk_pretty_formatter_factory()(env, opts, tc)(e);
    sstream ss;
    ss << mk_pair(flatten(f), opts);
    j["type"] = ss.str();
}

void report_completions(environment const & env, options const & opts, pos_info const & pos, bool skip_completions,
                        search_path const & path, char const * mod_path, break_at_pos_exception const & e, json & j) {
    g_context = e.m_token_info.m_context;
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
                j["completions"] = get_field_completions(e.m_token_info.m_param, prefix, env, opts);
            break;
        case break_at_pos_exception::token_context::option:
            if (!skip_completions)
                j["completions"] = get_option_completions(prefix, opts);
            break;
        case break_at_pos_exception::token_context::import:
            if (!skip_completions)
                j["completions"] = get_import_completions(prefix, dirname(mod_path), path, opts);
            break;
        case break_at_pos_exception::token_context::interactive_tactic:
            if (!skip_completions)
                j["completions"] = get_interactive_tactic_completions(prefix, e.m_token_info.m_param, env, opts);
            break;
        case break_at_pos_exception::token_context::attribute:
            if (!skip_completions)
                j["completions"] = get_attribute_completions(prefix, env, opts);
            break;
        case break_at_pos_exception::token_context::namespc:
            if (!skip_completions)
                j["completions"] = get_namespace_completions(prefix, env, opts);
            break;
        case break_at_pos_exception::token_context::single_completion:
            if (!skip_completions) {
                json completion;
                completion["text"] = e.m_token_info.m_param.to_string();
                j["completions"] = std::vector<json>{completion};
            }
            break;
        case break_at_pos_exception::token_context::none:
        case break_at_pos_exception::token_context::notation:
            return;
    }
    j["prefix"] = prefix;
}

void report_info(environment const & env, options const & opts, io_state const & ios,
                 search_path const & path, module_info const & m_mod_info,
                 std::vector<info_manager> const & info_managers, pos_info const & pos,
                 break_at_pos_exception const & e, json & j) {
    g_context = e.m_token_info.m_context;
    json record;

    // info data not dependent on elaboration/info_manager
    bool has_token_info = false;
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
                    auto f = find_file(path, m_mod_info.m_mod, parsed.first, string_to_name(parsed.second),
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
            case break_at_pos_exception::token_context::interactive_tactic: {
                auto n = get_interactive_tactic_full_name(e.m_token_info.m_param, e.m_token_info.m_token);
                if (env.find(n)) {
                    record = serialize_decl(e.m_token_info.m_token, n, env, opts);
                    if (auto idx = e.m_token_info.m_tac_param_idx)
                        record["tactic_param_idx"] = *idx;
                    has_token_info = true;
                }
                break;
            } case break_at_pos_exception::token_context::field: {
                auto name = e.m_token_info.m_param + e.m_token_info.m_token;
                record["full-id"] = name.to_string();
                add_source_info(env, name, record);
                if (auto doc = get_doc_string(env, name))
                    record["doc"] = *doc;
                interactive_report_type(env, opts, env.get(name).get_type(), record);
            } default:
                break;
        }
    }

    for (auto & infom : info_managers) {
        if (infom.get_file_name() == m_mod_info.m_mod) {
            if (e.m_goal_pos) {
                infom.get_info_record(env, opts, ios, *e.m_goal_pos, record, [](info_data const & d) {
                            return dynamic_cast<vm_obj_format_info const *>(d.raw());
                        });
            }
            // first check for field infos inside token
            for (name pre = tk.get_prefix(); !has_token_info && pre; pre = pre.get_prefix()) {
                auto field_pos = e.m_token_info.m_pos;
                field_pos.second += pre.utf8_size();
                if (pos.second >= field_pos.second &&
                    infom.get_line_info_set(field_pos.first).find(field_pos.second)) {
                    infom.get_info_record(env, opts, ios, field_pos, record);
                    has_token_info = true;
                }
            }
            if (!has_token_info)
                infom.get_info_record(env, opts, ios, e.m_token_info.m_pos, record);
        }
    }

    if (!record.is_null())
        j["record"] = record;
}

void initialize_interactive() {
}
void finalize_interactive() {
}
}
