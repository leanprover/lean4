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
#include "library/pp_options.h"
#include "library/exception.h"
#include "library/documentation.h"
#include "library/attribute_manager.h"
#include "library/vm/vm.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_format.h"
#include "library/tactic/hole_command.h"
#include "library/tactic/tactic_evaluator.h"
#include "frontends/lean/completion.h"
#include "frontends/lean/interactive.h"
#include "frontends/lean/pp.h"
#include "frontends/lean/tactic_notation.h"

namespace lean {
LEAN_THREAD_VALUE(break_at_pos_exception::token_context, g_context, break_at_pos_exception::token_context::none);

void interactive_report_type(environment const & env, options const & opts, expr const & e, json & j) {
    type_context_old tc(env);
    if (g_context == break_at_pos_exception::token_context::interactive_tactic) {
        vm_state vm(env, options());
        tactic_state s = mk_tactic_state_for(env, opts, "_interactive_report_type", local_context(), mk_true());
        std::vector<std::string> params;

        for (expr d = e; is_pi(d); d = binding_body(d)) {
            vm_obj r = vm.invoke(get_interactive_param_desc_name(), {to_obj(s), to_obj(binding_domain(d))});
            format f;
            if (tactic::is_result_success(r))
                f = to_format(tactic::get_success_value(r));
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
    // TODO(gabriel): this is broken with french quotes
    std::string prefix = e.m_token_info.m_token == name("") ? "" : e.m_token_info.m_token.to_string();
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
                    auto base_dir = dirname(m_mod_info.m_id);
                    auto f = find_file(path, base_dir, parsed.first, string_to_name(parsed.second),
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
        if (infom.get_file_name() == m_mod_info.m_id) {
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

optional<info_data> find_hole(module_info const & m_mod_info,
                              std::vector<info_manager> const & info_managers,
                              pos_info const & pos) {
    optional<info_data> r;
    for (auto & infom : info_managers) {
        if (infom.get_file_name() == m_mod_info.m_id) {
            unsigned line = pos.first;
            while (true) {
                line_info_data_set S = infom.get_line_info_set(line);
                S.for_each([&](unsigned, list<info_data> const & info_list) {
                        if (r) return;
                        for (info_data const & info : info_list) {
                            if (hole_info_data const * hole = is_hole_info_data(info)) {
                                pos_info const & begin = hole->get_begin_pos();
                                pos_info const & end   = hole->get_end_pos();
                                if ((pos.first > begin.first || (pos.first == begin.first && pos.second >= begin.second)) &&
                                    (pos.first < end.first || (pos.first == end.first && pos.second <= end.second))) {
                                    r = info;
                                }
                            }
                        }
                    });
                if (r) break;
                if (line == 0) break;
                line--;
            }
        }
    }
    return r;
}

bool execute_hole_command(tactic_state s, name const & cmd_decl_name, expr const & args, json & j) {
    type_context_old ctx = mk_type_context_for(s);
    options opts     = s.get_options();
    opts = opts.update_if_undef(get_pp_use_holes_name(), true);
    s = set_options(s, opts);
    scope_trace_env _(s.env(), opts, ctx);
    scope_traces_as_string msgs;
    expr const & ref = args;
    tactic_evaluator evaluator(ctx, opts, ref);
    name args_name("_args");
    environment new_env = evaluator.compile(args_name, args);
    vm_state S(new_env, opts);
    vm_obj decl_obj = S.get_constant(cmd_decl_name);
    vm_obj tac  = cfield(decl_obj, 2);
    S.push(to_obj(s));
    S.push(S.get_constant(args_name));
    S.push(tac);
    S.apply(2);
    vm_obj r = S.top();
    if (optional<tactic::exception_info> ex = tactic::is_exception(S, r)) {
        format msg = mk_tactic_error_msg(std::get<2>(*ex), std::get<0>(*ex));
        j["message"] = (sstream() << msg).str();
        return false;
    } else {
        std::string msg = msgs.get_string();
        if (!msg.empty())
            j["message"] = msgs.get_string();
        std::vector<json> as;
        vm_obj l     = tactic::get_success_value(r);
        while (cidx(l) != 0) {
            lean_assert(cidx(l) == 1);
            vm_obj p = cfield(l, 0);
            json a;
            a["code"]        = to_string(cfield(p, 0));
            a["description"] = to_string(cfield(p, 1));
            as.push_back(a);
            l = cfield(l, 1);
        }
        if (as.empty()) {
            return false;
        } else {
            j["replacements"]["alternatives"] = as;
            return true;
        }
    }
}

bool json_of_hole(hole_info_data const & hole, std::string const & file, json & j) {
    tactic_state const & s = hole.get_tactic_state();
    buffer<pair<name, std::string>> cmd_descrs;
    get_hole_commands(s.env(), cmd_descrs);
    if (cmd_descrs.empty()) return false;
    std::vector<json> ds;
    for (auto const & p : cmd_descrs) {
        json d;
        d["name"] = p.first.to_string();
        d["description"] = p.second;
        ds.push_back(d);
    }
    j["results"] = ds;
    j["file"] = file;
    j["start"]["line"]   = hole.get_begin_pos().first;
    j["start"]["column"] = hole.get_begin_pos().second;
    j["end"]["line"]     = hole.get_end_pos().first;
    j["end"]["column"]   = hole.get_end_pos().second;
    return true;
}

void get_hole_commands(module_info const & m_mod_info,
                       std::vector<info_manager> const & info_managers,
                       pos_info const & pos, json & j) {
    optional<info_data> info = find_hole(m_mod_info, info_managers, pos);
    if (!info) {
        j["message"] = "hole not found";
        return;
    }
    hole_info_data const & hole = to_hole_info_data(*info);
    if (!json_of_hole(hole, m_mod_info.m_id, j)) {
        j["message"] = "hole commands are not available";
        return;
    }
}

void get_all_hole_commands(module_info const & m_mod_info,
                           std::vector<info_manager> const & info_managers,
                           json & j) {
    std::vector<json> holes;
    for (auto & infom : info_managers) {
        if (infom.get_file_name() == m_mod_info.m_id) {
            infom.get_line_info_sets().for_each([&](unsigned, line_info_data_set const & S) {
                S.for_each([&](unsigned, list<info_data> const & info_list) {
                    for (info_data const & info : info_list) {
                        if (hole_info_data const * hole = is_hole_info_data(info)) {
                            json j;
                            if (json_of_hole(*hole, m_mod_info.m_id, j)) {
                                holes.push_back(j);
                            }
                        }
                    }
                });
            });
        }
    }
    j["holes"] = holes;
}

void execute_hole_command(module_info const & m_mod_info,
                          std::vector<info_manager> const & info_managers,
                          pos_info const & pos, std::string const & action, json & j) {
    optional<info_data> info = find_hole(m_mod_info, info_managers, pos);
    if (!info) {
        j["message"] = "hole not found";
        return;
    }
    hole_info_data const & hole = to_hole_info_data(*info);
    tactic_state const & s = hole.get_tactic_state();
    optional<name> cmd_decl_name = is_hole_command(s.env(), name(action));
    if (!cmd_decl_name) {
        j["message"] = (sstream() << "unknown hole command '" << action << "'").str();
        return;
    }
    if (execute_hole_command(s, *cmd_decl_name, hole.get_args(), j)) {
        j["replacements"]["file"] = m_mod_info.m_id;
        j["replacements"]["start"]["line"]   = hole.get_begin_pos().first;
        j["replacements"]["start"]["column"] = hole.get_begin_pos().second;
        j["replacements"]["end"]["line"]     = hole.get_end_pos().first;
        j["replacements"]["end"]["column"]   = hole.get_end_pos().second;
    }
}

void initialize_interactive() {
}
void finalize_interactive() {
}
}
