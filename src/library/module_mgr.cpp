/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Gabriel Ebner, Sebastian Ullrich
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
module_loader module_mgr::mk_loader() {
    return [this](module_name const & n) { return get_module(n)->m_result.m_loaded_module; }; // NOLINT
}

static std::pair<std::string, std::shared_ptr<module_info>>
load_module(search_path const & path, module_name const & mod_name, bool can_use_olean) {
    auto lean_fn = find_file(path, mod_name, {".lean"});
    auto lean_mtime = get_mtime(lean_fn);

    try {
        auto olean_fn = olean_of_lean(lean_fn);
        shared_file_lock olean_lock(olean_fn);
        auto olean_mtime = get_mtime(olean_fn);
        if (olean_mtime != -1 && olean_mtime >= lean_mtime &&
            can_use_olean &&
            is_candidate_olean_file(olean_fn)) {
            auto mod = std::make_shared<module_info>(mod_name,
                    read_file(olean_fn, std::ios_base::binary), module_src::OLEAN, olean_mtime);
            return std::make_pair(olean_fn, mod);
        }
    } catch (exception) {}

    return std::make_pair(lean_fn, std::make_shared<module_info>(mod_name, read_file(lean_fn), module_src::LEAN, lean_mtime));
}

static void compile_olean(search_path const & path, std::shared_ptr<module_info> const & mod) {
    if (mod->m_compiled_olean)
        return;
    mod->m_compiled_olean = true;
    for (auto & dep : mod->m_deps)
        if (dep.m_mod_info)
            compile_olean(path, dep.m_mod_info);

    if (mod->m_source != module_src::LEAN || mod->m_log.has_errors())
        return;
    auto res = mod->m_result;

    auto olean_fn = olean_of_lean(find_file(path, mod->m_name, {".lean"}));
    exclusive_file_lock output_lock(olean_fn);
    std::ofstream out(olean_fn, std::ios_base::binary);
    write_module(*res.m_loaded_module, out);
    out.close();
    if (!out) throw exception("failed to write olean file");
}

void module_mgr::build_module(module_name const & mod_name, bool can_use_olean, name_set module_stack) {
    if (auto const & existing_mod = m_modules.find(mod_name))
        return;

    auto orig_module_stack = module_stack;
    if (module_stack.contains(mod_name)) {
        throw exception(sstream() << "cyclic import: " << mod_name);
    }
    module_stack.insert(mod_name);

    scope_global_ios scope_ios(m_ios);
    scope_traces_as_messages scope_trace_msgs(mod_name.to_string(), {1, 0});

    std::string file_name; std::shared_ptr<module_info> mod;
    std::tie(file_name, mod) = load_module(m_path, mod_name, can_use_olean);
    scope_message_log scope_log(mod->m_log);

        if (mod->m_source == module_src::OLEAN) {
            std::istringstream in2(mod->m_contents, std::ios_base::binary);
            bool check_hash = false;
            auto parsed_olean = parse_olean(in2, file_name, check_hash);
            // we never need to re-parse .olean files, so discard content
            mod->m_contents.clear();
            mod->m_trans_mtime = mod->m_mtime;

            for (auto & d : parsed_olean.m_imports) {
                build_module(d, true, module_stack);

                auto const & d_mod = *m_modules.find(d);
                mod->m_deps.push_back({ d, d_mod });
                mod->m_trans_mtime = std::max(mod->m_trans_mtime, d_mod->m_trans_mtime);
            }

            if (mod->m_trans_mtime > mod->m_mtime)
                return build_module(mod_name, false, orig_module_stack);

            mod->m_compiled_olean = true;
            module_info::parse_result res;

            auto deps = mod->m_deps;
            loaded_module lm {
                    mod_name, parsed_olean.m_imports,
                    parse_olean_modifications(parsed_olean.m_serialized_modifications, file_name) };
            res.m_loaded_module = std::make_shared<loaded_module const>(lm);

            mod->m_result = res;
            m_modules[mod_name] = mod;
        } else if (mod->m_source == module_src::LEAN) {
            build_lean(mod, file_name, module_stack);
            m_modules[mod_name] = mod;
        } else {
            throw exception("unknown module source");
        }
}

void module_mgr::build_lean(std::shared_ptr<module_info> const & mod, std::string const & file_name, name_set const & module_stack) {
    auto mod_name = mod->m_name;
    auto imports = get_direct_imports(file_name, mod->m_contents);
    mod->m_trans_mtime = mod->m_mtime;
    for (auto & d : imports) {
        std::shared_ptr<module_info> d_mod;
        try {
            build_module(d, true, module_stack);
            d_mod = m_modules[d];
            mod->m_trans_mtime = std::max(mod->m_trans_mtime, d_mod->m_trans_mtime);
        } catch (throwable & ex) {
            message_builder(m_initial_env, m_ios, file_name, {1, 0}, ERROR).set_exception(ex).report();
        }
        mod->m_deps.push_back(module_info::dependency { d, d_mod });
        build_module(d, true, module_stack);
    }

    std::istringstream in(mod->m_contents);
    auto env = import_modules(m_initial_env, imports, mk_loader());
    parser p(env, m_ios, in, file_name);

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
        p.get_options(), std::make_shared<loaded_module const>(export_module(p.mk_snapshot()->m_env, mod_name)) };

    if (m_save_olean) {
        compile_olean(m_path, mod);
    }
}

std::shared_ptr<module_info const> module_mgr::get_module(module_name const & mod_name) {
    name_set module_stack;
    build_module(mod_name, true, module_stack);
    return *m_modules.find(mod_name);
}

std::vector<module_name> module_mgr::get_direct_imports(std::string const & file_name, std::string const & contents) {
    std::vector<rel_module_name> rel_imports;
    try {
        std::istringstream in(contents);
        bool use_exceptions = true;
        parser p(get_initial_env(), m_ios, in, file_name, use_exceptions);
        try {
            p.init_scanner();
        } catch (...) {}
        p.parse_imports(rel_imports);
    } catch (...) {}

    std::vector<module_name> imports;
    auto dir = dirname(file_name);
    for (auto const & rel : rel_imports)
        imports.push_back(absolutize_module_name(m_path, dir, rel));
    return imports;
}

}
