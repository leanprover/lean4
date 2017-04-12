/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include <utility>
#include <string>
#include <vector>
#include <algorithm>
#include "util/utf8.h"
#include "util/lean_path.h"
#include "util/file_lock.h"
#include "library/module_mgr.h"
#include "library/module.h"
#include "frontends/lean/pp.h"
#include "frontends/lean/parser.h"
#include "library/library_task_builder.h"

namespace lean {

void module_mgr::mark_out_of_date(module_id const & id) {
    for (auto & mod : m_modules) {
        if (!mod.second || mod.second->m_out_of_date) continue;
        for (auto & dep : mod.second->m_deps) {
            if (dep.m_id == id) {
                mod.second->m_out_of_date = true;
                mark_out_of_date(mod.first);
                break;
            }
        }
    }
}

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
        if (deps_per_mod.count(m.m_mod)) continue;

        for (auto & d : m.m_deps) {
            if (d.m_mod_info) {
                deps_per_mod[m.m_mod].push_back(d);
                if (!deps_per_mod.count(d.m_mod_info->m_mod))
                    to_process.push_back(d.m_mod_info.get());
            }
        }
    }

    return[deps_per_mod_ptr] (std::string const & current_module, module_name const & import) -> std::shared_ptr<loaded_module const> {
        try {
            for (auto & d : deps_per_mod_ptr->at(current_module)) {
                if (d.m_import_name.m_name == import.m_name && d.m_import_name.m_relative == import.m_relative) {
                    return get(d.m_mod_info->m_result).m_loaded_module;
                }
            }
        } catch (std::out_of_range) {
            // In files with syntax errors, it can happen that the
            // initial dependency scan does not find all dependencies.
        }
        throw exception(sstream() << "could not resolve import: " << import.m_name);
    };
}

static gtask compile_olean(std::shared_ptr<module_info const> const & mod, log_tree::node const & parsing_lt) {
    auto errs = has_errors(parsing_lt);

    gtask mod_dep = mk_deep_dependency(mod->m_result, [] (buffer<gtask> & deps, module_info::parse_result const & res) {
        for (auto & mdf : res.m_loaded_module->m_modifications)
            mdf->get_task_dependencies(deps);
        deps.push_back(res.m_loaded_module->m_uses_sorry);
    });

    std::vector<gtask> olean_deps;
    for (auto & dep : mod->m_deps)
        if (dep.m_mod_info)
            olean_deps.push_back(dep.m_mod_info->m_olean_task);

    return add_library_task(task_builder<unit>([mod, errs] {
        if (mod->m_source != module_src::LEAN)
            throw exception("cannot build olean from olean");
        auto res = get(mod->m_result);

        if (get(errs)) throw exception("not creating olean file because of errors");

        auto olean_fn = olean_of_lean(mod->m_mod);
        exclusive_file_lock output_lock(olean_fn);
        std::ofstream out(olean_fn, std::ios_base::binary);
        write_module(*res.m_loaded_module, out);
        return unit();
    }).depends_on(mod_dep).depends_on(olean_deps).depends_on(errs), std::string("saving olean"));
}

// TODO(gabriel): adapt to vfs
static module_id resolve(search_path const & path,
                         module_id const & module_file_name,
                         module_name const & ref) {
    auto base_dir = dirname(module_file_name.c_str());
    try {
        return find_file(path, base_dir, ref.m_relative, ref.m_name, ".lean");
    } catch (file_not_found_exception) {
        return olean_file_to_lean_file(find_file(path, base_dir, ref.m_relative, ref.m_name, ".olean"));
    }
}

void module_mgr::build_module(module_id const & id, bool can_use_olean, name_set module_stack) {
    if (auto & existing_mod = m_modules[id])
        if (!existing_mod->m_out_of_date) return;

    scope_global_ios scope_ios(m_ios);
    scope_log_tree lt(m_lt.mk_child(id, {}, { id, {{1, 0}, {static_cast<unsigned>(-1), 0}} }, log_tree::DefaultLevel, true));
    scope_traces_as_messages scope_trace_msgs(id, {1, 0});

    try {
        auto orig_module_stack = module_stack;
        if (module_stack.contains(id)) {
            throw exception(sstream() << "cyclic import: " << id);
        }
        module_stack.insert(id);

        bool already_have_lean_version = m_modules[id] && m_modules[id]->m_source == module_src::LEAN;

        std::string contents;
        module_src src;
        time_t mtime;
        std::tie(contents, src, mtime) = m_vfs->load_module(id, !already_have_lean_version && can_use_olean);

        if (src == module_src::OLEAN) {
            auto obj_code = contents;

            std::istringstream in2(obj_code, std::ios_base::binary);
            auto olean_fn = olean_of_lean(id);
            bool check_hash = false;
            auto parsed_olean = parse_olean(in2, olean_fn, check_hash);

            auto mod = std::make_shared<module_info>();

            mod->m_mod = id;
            mod->m_lt = lt.get();
            mod->m_source = module_src::OLEAN;
            mod->m_trans_mtime = mod->m_mtime = mtime;

            for (auto & d : parsed_olean.m_imports) {
                auto d_id = resolve(m_path, id, d);
                build_module(d_id, true, module_stack);

                auto & d_mod = m_modules[d_id];
                mod->m_deps.push_back({ d_id, d, d_mod });
                mod->m_trans_mtime = std::max(mod->m_trans_mtime, d_mod->m_trans_mtime);
            }

            if (mod->m_trans_mtime > mod->m_mtime)
                return build_module(id, false, orig_module_stack);

            module_info::parse_result res;

            auto deps = mod->m_deps;
            res.m_loaded_module = cache_preimported_env(
                    { id, parsed_olean.m_imports,
                      parse_olean_modifications(parsed_olean.m_serialized_modifications, id),
                      mk_pure_task<bool>(parsed_olean.m_uses_sorry), {} },
                    m_initial_env, [=] { return mk_loader(id, deps); });

            mod->m_result = mk_pure_task<module_info::parse_result>(res);

            if (auto & old_mod = m_modules[id])
                cancel(old_mod->m_cancel);
            m_modules[id] = mod;
        } else if (src == module_src::LEAN) {
            auto mod = build_lean(id, contents, mtime, module_stack);
            m_modules[id] = mod;
        } else {
            throw exception("unknown module source");
        }
    } catch (throwable & ex) {
        message_builder msg(m_initial_env, m_ios, id, pos_info {1, 0}, ERROR);
        msg.set_exception(ex);
        msg.report();
        throw ex;
    }
}

std::shared_ptr<module_info>
module_mgr::build_lean(module_id const & id, std::string const & contents, time_t mtime, name_set const & module_stack) {
    auto & lt = logtree();
    auto end_pos = find_end_pos(contents);
    scope_log_tree lt2(lt.mk_child({}, {}, { id, {{1, 0}, end_pos} }));

    auto imports = get_direct_imports(id, contents);

    auto mod = std::make_shared<module_info>();
    mod->m_lt = logtree();
    mod->m_mod = id;
    mod->m_source = module_src::LEAN;
    mod->m_trans_mtime = mod->m_mtime = mtime;
    mod->m_lean_contents = contents;
    for (auto & d : imports) {
        module_id d_id;
        std::shared_ptr<module_info const> d_mod;
        try {
            d_id = resolve(m_path, id, d);
            build_module(d_id, true, module_stack);
            d_mod = m_modules[d_id];
            mod->m_trans_mtime = std::max(mod->m_trans_mtime, d_mod->m_trans_mtime);
        } catch (throwable & ex) {
            message_builder(m_initial_env, m_ios, id, {1, 0}, ERROR).set_exception(ex).report();
        }
        mod->m_deps.push_back({ d_id, d, d_mod });
    }

    std::vector<gtask> deps;
    for (auto & d : mod->m_deps)
        if (d.m_mod_info)
            deps.push_back(d.m_mod_info->m_result);
    if (!mod->m_deps.empty()) {
        // also add the preimported environment of the first dependency
        if (auto & mod_info = mod->m_deps.front().m_mod_info) {
            deps.push_back(mk_deep_dependency(mod_info->m_result,
                                              [] (buffer<gtask> & ds, module_info::parse_result const & res) {
                                                  ds.push_back(res.m_loaded_module->m_env);
                                              }));
        }
    }

    auto ldr = mk_loader(id, mod->m_deps);
    auto mod_parser_fn = std::make_shared<module_parser>(id, contents, m_initial_env, ldr);
    mod_parser_fn->save_info(m_use_snapshots);

    module_parser_result snapshots;
    std::tie(mod->m_cancel, snapshots) = build_lean_snapshots(
            mod_parser_fn, m_modules[id], deps, contents);
    scope_cancellation_token scope_cancel(mod->m_cancel);

    if (m_use_snapshots) {
        // Even just keeping a reference to the final environment costs us
        // a few hundred megabytes (when compiling the standard library).
        mod->m_snapshots = snapshots;
    }

    auto initial_env = m_initial_env;
    mod->m_result = map<module_info::parse_result>(
        get_end(snapshots),
        [=](module_parser_result const & res) {
            module_info::parse_result parse_res;

            lean_always_assert(res.m_snapshot_at_end);
            parse_res.m_loaded_module = cache_preimported_env(
                    export_module(res.m_snapshot_at_end->m_env, id),
                    initial_env, [=] { return ldr; });

            parse_res.m_opts = res.m_snapshot_at_end->m_options;

            return parse_res;
        }).build();

    if (m_save_olean) {
        scope_log_tree_core lt3(&lt);
        mod->m_olean_task = compile_olean(mod, lt2.get());
    }

    return mod;
}

static optional<pos_info> get_first_diff_pos(std::string const & as, std::string const & bs) {
    char const * a = as.c_str(), * b = bs.c_str();
    int line = 1;
    while (true) {
        char const * ai = strchr(a, '\n');
        char const * bi = strchr(b, '\n');
        if (ai && bi) {
            if (ai - a == bi - b &&
                    ai[1] && bi[1] && // ignore final newlines, the scanner does not see them
                    strncmp(a, b, ai - a) == 0) {
                a = ai + 1;
                b = bi + 1;
                line++;
            } else {
                break;
            }
        } else if (strcmp(a, b) == 0) {
            return optional<pos_info>();
        } else {
            break;
        }
    }
    return optional<pos_info>(line, 0);
}

std::pair<cancellation_token, module_parser_result>
module_mgr::build_lean_snapshots(std::shared_ptr<module_parser> const & mod_parser,
                                 std::shared_ptr<module_info> const & old_mod,
                                 std::vector<gtask> const & deps, std::string const & contents) {
    auto rebuild = [&] {
        if (old_mod) cancel(old_mod->m_cancel);
        auto cancel_tok = mk_cancellation_token();
        return std::make_pair(cancel_tok, mod_parser->parse(optional<std::vector<gtask>>(deps)));
    };

    if (!m_use_snapshots) return rebuild();
    if (!old_mod) return rebuild();
    if (old_mod->m_source != module_src::LEAN)
        return rebuild();

    for (auto d : old_mod->m_deps) {
        if (!d.m_mod_info && !m_modules[d.m_id]) continue;
        if (d.m_mod_info && m_modules[d.m_id] && m_modules[d.m_id] == d.m_mod_info) continue;

        return rebuild();
    }

    if (!old_mod->m_lean_contents || !old_mod->m_snapshots) return rebuild();

    auto snap = *old_mod->m_snapshots;
    logtree().reuse("_next"); // TODO(gabriel): this needs to be the same name as in module_parser...
    if (auto diff_pos = get_first_diff_pos(contents, *old_mod->m_lean_contents)) {
        return std::make_pair(old_mod->m_cancel,
                              mod_parser->resume_from_start(snap, *diff_pos, optional<std::vector<gtask>>(deps)));
    } else {
        // no diff
        return std::make_pair(old_mod->m_cancel, snap);
    }
}

std::shared_ptr<module_info const> module_mgr::get_module(module_id const & id) {
    unique_lock<mutex> lock(m_mutex);
    name_set module_stack;
    build_module(id, true, module_stack);
    return m_modules.at(id);
}

void module_mgr::invalidate(module_id const & id) {
    unique_lock<mutex> lock(m_mutex);

    if (auto & mod = m_modules[id])
        mod->m_out_of_date = true;
    mark_out_of_date(id);

    buffer<module_id> to_rebuild;
    to_rebuild.push_back(id);
    for (auto & mod : m_modules) {
        if (mod.second && mod.second->m_out_of_date)
            to_rebuild.push_back(mod.first);
    }
    for (auto & i : to_rebuild) {
        try {
            build_module(i, true, {});
        } catch (...) {}
    }
}

std::vector<module_name> module_mgr::get_direct_imports(module_id const & id, std::string const & contents) {
    std::vector<module_name> imports;
    try {
        scope_log_tree lt;
        std::istringstream in(contents);
        bool use_exceptions = true;
        parser p(get_initial_env(), m_ios, nullptr, in, id, use_exceptions);
        p.get_imports(imports);
    } catch (...) {}

    return imports;
}

void module_mgr::cancel_all() {
    for (auto & m : m_modules) {
        if (auto mod = m.second) {
            cancel(mod->m_cancel);
        }
    }
}

std::tuple<std::string, module_src, time_t> fs_module_vfs::load_module(module_id const & id, bool can_use_olean) {
    auto lean_fn = id;
    auto lean_mtime = get_mtime(lean_fn);

    try {
        auto olean_fn = olean_of_lean(lean_fn);
        shared_file_lock olean_lock(olean_fn);
        auto olean_mtime = get_mtime(olean_fn);
        if (olean_mtime != -1 && olean_mtime >= lean_mtime &&
            can_use_olean &&
            !m_modules_to_load_from_source.count(id)) {
            return std::make_tuple(read_file(olean_fn, std::ios_base::binary), module_src::OLEAN, olean_mtime);
        }
    } catch (exception) {}

    return std::make_tuple(read_file(lean_fn), module_src::LEAN, lean_mtime);
}

environment get_combined_environment(environment const & env,
                                     buffer<std::shared_ptr<module_info const>> const & mods) {
    module_id combined_id = "<combined_environment.lean>";

    std::vector<module_info::dependency> deps;
    std::vector<module_name> refs;
    for (auto & mod : mods) {
        // TODO(gabriel): switch module_ids to names, then we don't need this hack
        module_name ref { name(mod->m_mod), {} };
        deps.push_back({ mod->m_mod, ref, mod });
        refs.push_back(ref);
    }

    return import_modules(env, combined_id, refs, mk_loader(combined_id, deps));
}

}
