/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include <utility>
#include <string>
#include <vector>
#include <algorithm>
#include "runtime/utf8.h"
#include "util/lean_path.h"
#include "util/file_lock.h"
#include "library/module_mgr.h"
#include "library/module.h"
#include "frontends/lean/pp.h"
#include "frontends/lean/parser.h"

namespace lean {
static module_loader mk_loader(module_id const & cur_mod, std::vector<module_info::dependency> const & deps) {
    auto deps_per_mod_ptr = std::make_shared<std::unordered_map<module_id, std::vector<module_info::dependency>>>();
    auto & deps_per_mod = *deps_per_mod_ptr;

    buffer<module_info const *> to_process;
    for (auto & d : deps) {
        if (d.m_mod_info) {
            deps_per_mod[cur_mod].push_back(d);
            to_process.push_back(d.m_mod_info.get());
        }
    }
    while (!to_process.empty()) {
        module_info const & m = *to_process.back();
        to_process.pop_back();
        if (deps_per_mod.count(m.m_id)) continue;

        for (auto & d : m.m_deps) {
            if (d.m_mod_info) {
                deps_per_mod[m.m_id].push_back(d);
                if (!deps_per_mod.count(d.m_mod_info->m_id))
                    to_process.push_back(d.m_mod_info.get());
            }
        }
    }

    return[deps_per_mod_ptr] (std::string const & current_module, module_name const & import) -> std::shared_ptr<loaded_module const> {
        try {
            for (auto & d : deps_per_mod_ptr->at(current_module)) {
                if (d.m_import_name.m_name == import.m_name && d.m_import_name.m_relative == import.m_relative) {
                    return d.m_mod_info->m_result.m_loaded_module;
                }
            }
        } catch (std::out_of_range) {
            // In files with syntax errors, it can happen that the
            // initial dependency scan does not find all dependencies.
        }
        throw exception(sstream() << "could not resolve import: " << import.m_name);
    };
}

static std::shared_ptr<module_info> load_module(module_id const & id, bool can_use_olean) {
    auto lean_fn = id;
    auto lean_mtime = get_mtime(lean_fn);

    try {
        auto olean_fn = olean_of_lean(lean_fn);
        shared_file_lock olean_lock(olean_fn);
        auto olean_mtime = get_mtime(olean_fn);
        if (olean_mtime != -1 && olean_mtime >= lean_mtime &&
            can_use_olean &&
            is_candidate_olean_file(olean_fn)) {
            return std::make_shared<module_info>(id, read_file(olean_fn, std::ios_base::binary), module_src::OLEAN, olean_mtime);
        }
    } catch (exception) {}

    return std::make_shared<module_info>(id, read_file(lean_fn), module_src::LEAN, lean_mtime);
}

static void compile_olean(std::shared_ptr<module_info> const & mod) {
    if (mod->m_compiled_olean)
        return;
    mod->m_compiled_olean = true;
    for (auto & dep : mod->m_deps)
        if (dep.m_mod_info)
            compile_olean(dep.m_mod_info);

    if (mod->m_source != module_src::LEAN || mod->m_log.has_errors())
        return;
    auto res = mod->m_result;

    auto olean_fn = olean_of_lean(mod->m_id);
    exclusive_file_lock output_lock(olean_fn);
    std::ofstream out(olean_fn, std::ios_base::binary);
    write_module(*res.m_loaded_module, out);
    out.close();
    if (!out) throw exception("failed to write olean file");
}

static module_id resolve(search_path const & path,
                         module_id const & module_file_name,
                         module_name const & ref) {
    auto base_dir = dirname(module_file_name);
    try {
        return find_file(path, base_dir, ref.m_relative, ref.m_name, ".lean");
    } catch (lean_file_not_found_exception) {
        return olean_file_to_lean_file(find_file(path, base_dir, ref.m_relative, ref.m_name, ".olean"));
    }
}

void module_mgr::build_module(module_id const & id, bool can_use_olean, name_set module_stack) {
    if (auto & existing_mod = m_modules[id])
        return;

    auto orig_module_stack = module_stack;
    if (module_stack.contains(name(id))) {
        throw exception(sstream() << "cyclic import: " << id);
    }
    module_stack.insert(name(id));

    scope_global_ios scope_ios(m_ios);
    scope_traces_as_messages scope_trace_msgs(id, {1, 0});

    auto mod = load_module(id, can_use_olean);
    scope_message_log scope_log(mod->m_log);

        if (mod->m_source == module_src::OLEAN) {
            std::istringstream in2(mod->m_contents, std::ios_base::binary);
            auto olean_fn = olean_of_lean(id);
            bool check_hash = false;
            auto parsed_olean = parse_olean(in2, olean_fn, check_hash);
            // we never need to re-parse .olean files, so discard content
            mod->m_contents.clear();
            mod->m_trans_mtime = mod->m_mtime;

            for (auto & d : parsed_olean.m_imports) {
                auto d_id = resolve(m_path, id, d);
                build_module(d_id, true, module_stack);

                auto & d_mod = m_modules[d_id];
                mod->m_deps.push_back({ d_id, d, d_mod });
                mod->m_trans_mtime = std::max(mod->m_trans_mtime, d_mod->m_trans_mtime);
            }

            if (mod->m_trans_mtime > mod->m_mtime)
                return build_module(id, false, orig_module_stack);

            mod->m_compiled_olean = true;
            module_info::parse_result res;

            auto deps = mod->m_deps;
            loaded_module lm {
                    id, parsed_olean.m_imports,
                    parse_olean_modifications(parsed_olean.m_serialized_modifications, id) };
            res.m_loaded_module = std::make_shared<loaded_module const>(lm);

            mod->m_result = res;
            m_modules[id] = mod;
        } else if (mod->m_source == module_src::LEAN) {
            build_lean(mod, module_stack);
            m_modules[id] = mod;
        } else {
            throw exception("unknown module source");
        }
}

void module_mgr::build_lean(std::shared_ptr<module_info> const & mod, name_set const & module_stack) {
    auto id = mod->m_id;
    auto imports = get_direct_imports(id, mod->m_contents);
    mod->m_trans_mtime = mod->m_mtime;
    for (auto & d : imports) {
        module_id d_id;
        std::shared_ptr<module_info> d_mod;
        try {
            d_id = resolve(m_path, id, d);
            build_module(d_id, true, module_stack);
            d_mod = m_modules[d_id];
            mod->m_trans_mtime = std::max(mod->m_trans_mtime, d_mod->m_trans_mtime);
        } catch (throwable & ex) {
            message_builder(m_initial_env, m_ios, id, {1, 0}, ERROR).set_exception(ex).report();
        }
        mod->m_deps.push_back(module_info::dependency { d_id, d, d_mod });
        build_module(d_id, true, module_stack);
    }

    auto ldr = mk_loader(id, mod->m_deps);
    std::istringstream in(mod->m_contents);
    parser p(m_initial_env, m_ios, ldr, in, id);

    bool done = false;
    while (!done) {
        try {
            check_system("module_parser::parse_next_command_like");
            done = p.parse_command_like();
        } catch (parser_exception & ex) {
            report_message(ex);
            p.sync_command();
        } catch (throwable & ex) {
            p.mk_message(p.m_last_cmd_pos, ERROR).set_exception(ex).report();
            p.sync_command();
        } catch (interrupt_parser) {
            // this exception is thrown by the exit command
            done = true;
        }
    }

    mod->m_result = module_info::parse_result {
        p.get_options(), std::make_shared<loaded_module const>(export_module(p.mk_snapshot()->m_env, id)) };

    if (m_save_olean) {
        compile_olean(mod);
    }
}

std::shared_ptr<module_info const> module_mgr::get_module(module_id const & id) {
    name_set module_stack;
    build_module(id, true, module_stack);
    return m_modules.at(id);
}

std::vector<module_name> module_mgr::get_direct_imports(module_id const & id, std::string const & contents) {
    std::vector<module_name> imports;
    try {
        std::istringstream in(contents);
        bool use_exceptions = true;
        parser p(get_initial_env(), m_ios, nullptr, in, id, use_exceptions);
        try {
            p.init_scanner();
        } catch (...) {}
        p.get_imports(imports);
    } catch (...) {}

    return imports;
}

}
