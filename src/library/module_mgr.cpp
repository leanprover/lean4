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
    return [this](module_name const & n) { return get_module(n)->m_loaded_module; }; // NOLINT
}

static std::shared_ptr<module_info>
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
            return std::make_shared<module_info>(mod_name, olean_fn, module_src::OLEAN, olean_mtime);
        }
    } catch (exception) {}

    return std::make_shared<module_info>(mod_name, lean_fn, module_src::LEAN, lean_mtime);
}

static void compile_olean(search_path const & path, std::shared_ptr<module_info> const & mod) {
    lean_assert(mod->m_source == module_src::LEAN);
    if (mod->m_log.has_errors())
        return;

    auto olean_fn = olean_of_lean(find_file(path, mod->m_name, {".lean"}));
    exclusive_file_lock output_lock(olean_fn);
    std::ofstream out(olean_fn, std::ios_base::binary);
    write_module(*mod->m_loaded_module, out);
    out.close();
    if (!out) throw exception("failed to write olean file");
}

time_t module_mgr::build_module(module_name const & mod_name, bool can_use_olean, name_set module_stack) {
    if (auto const & existing_mod = m_modules.find(mod_name))
        return (*existing_mod)->m_mtime;

    auto orig_module_stack = module_stack;
    if (module_stack.contains(mod_name)) {
        throw exception(sstream() << "cyclic import: " << mod_name);
    }
    module_stack.insert(mod_name);

    scope_global_ios scope_ios(m_ios);
    scope_traces_as_messages scope_trace_msgs(mod_name.to_string(), {1, 0});

    auto mod = load_module(m_path, mod_name, can_use_olean);
    scope_message_log scope_log(mod->m_log);

    if (mod->m_source == module_src::OLEAN) {
        std::ifstream in2(mod->m_filename, std::ios_base::binary);
        bool check_hash = false;
        auto parsed_olean = parse_olean(in2, mod->m_filename, check_hash);
        auto max_mtime = mod->m_mtime;

        for (auto & d : parsed_olean.m_imports) {
            max_mtime = std::max(max_mtime, build_module(d, true, module_stack));

            auto const & d_mod = *m_modules.find(d);
            mod->m_deps.push_back({ d, d_mod });
        }

        if (max_mtime > mod->m_mtime) {
            // .olean file out of date, try again with .lean file
            return build_module(mod_name, false, orig_module_stack);
        }

        auto deps = mod->m_deps;
        loaded_module lm {
                mod_name, parsed_olean.m_imports,
                parse_olean_modifications(parsed_olean.m_serialized_modifications, mod->m_filename) };

        mod->m_loaded_module = std::make_shared<loaded_module const>(lm);
        m_modules[mod_name] = mod;
        return max_mtime;
    } else if (mod->m_source == module_src::LEAN) {
        auto max_mtime = build_lean(mod, module_stack);
        m_modules[mod_name] = mod;
        return max_mtime;
    } else {
        throw exception("unknown module source");
    }
}

time_t module_mgr::build_lean(std::shared_ptr<module_info> const & mod, name_set const & module_stack) {
    auto mod_name = mod->m_name;
    auto contents = read_file(mod->m_filename);
    auto imports = get_direct_imports(mod->m_filename, contents);
    auto max_mtime = mod->m_mtime;
    for (auto & d : imports) {
        std::shared_ptr<module_info> d_mod;
        try {
            max_mtime = std::max(max_mtime, build_module(d, true, module_stack));
            d_mod = m_modules[d];
        } catch (throwable & ex) {
            message_builder(m_initial_env, m_ios, mod->m_filename, {1, 0}, ERROR).set_exception(ex).report();
        }
        mod->m_deps.push_back(module_info::dependency { d, d_mod });
        build_module(d, true, module_stack);
    }

    std::istringstream in(contents);
    auto env = import_modules(m_initial_env, imports, mk_loader());
    parser p(env, m_ios, in, mod->m_filename);
    p.parse_commands();
    mod->m_loaded_module = std::make_shared<loaded_module const>(export_module(p.env(), mod_name));

    if (m_save_olean) {
        compile_olean(m_path, mod);
    }

    return max_mtime;
}

std::shared_ptr<module_info const> module_mgr::get_module(module_name const & mod_name) {
    name_set module_stack;
    build_module(mod_name, true, module_stack);
    return *m_modules.find(mod_name);
}

std::vector<module_name> module_mgr::get_direct_imports(std::string const & file_name, std::string const & contents) {
    std::vector<rel_module_name> rel_imports;
    std::istringstream in(contents);
    bool use_exceptions = true;
    parser p(get_initial_env(), m_ios, in, file_name, use_exceptions);
    p.parse_imports(rel_imports);

    std::vector<module_name> imports;
    auto dir = dirname(file_name);
    for (auto const & rel : rel_imports)
        imports.push_back(absolutize_module_name(m_path, dir, rel));
    return imports;
}

}
