/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include <utility>
#include <string>
#include <vector>
#include <algorithm>
#include <sys/stat.h>
#include "util/lean_path.h"
#include "util/file_lock.h"
#include "library/module_mgr.h"
#include "library/module.h"
#include "library/versioned_msg_buf.h"
#include "frontends/lean/pp.h"
#include "frontends/lean/parser.h"

namespace lean {

void module_mgr::mark_out_of_date(module_id const & id, buffer<module_id> & to_rebuild) {
    for (auto & mod : m_modules) {
        if (!mod.second || mod.second->m_out_of_date) continue;
        for (auto & dep : mod.second->m_deps) {
            if (dep.first == id) {
                to_rebuild.push_back(mod.first);
                mod.second->m_out_of_date = true;
                mark_out_of_date(mod.first, to_rebuild);
                break;
            }
        }
    }
}

class parse_lean_task : public task<module_info::parse_result> {
    environment m_initial_env;
    std::string m_contents;
    snapshot_vector m_snapshots;
    bool m_use_snapshots;
    std::vector<std::tuple<module_id, module_name, std::shared_ptr<module_info const>>> m_deps;

public:
    parse_lean_task(std::string const & contents, environment const & initial_env,
                    snapshot_vector const & snapshots, bool use_snapshots,
                    std::vector<std::tuple<module_id, module_name, std::shared_ptr<module_info const>>> const & deps) :
        m_initial_env(initial_env), m_contents(contents),
        m_snapshots(snapshots), m_use_snapshots(use_snapshots),
        m_deps(deps) {}
    task_kind get_kind() const override { return task_kind::parse; }

    void description(std::ostream & out) const override {
        out << "parsing " << get_module_id();
    }

    std::vector<generic_task_result> get_dependencies() override {
        std::vector<generic_task_result> deps;
        for (auto & d : m_deps) deps.push_back(std::get<2>(d)->m_result);
        return deps;
    }

    module_info::parse_result execute() override {
        module_loader import_fn = [=] (module_id const & base, module_name const & import) {
            for (auto d : m_deps) {
                if (std::get<0>(d) == base &&
                        std::get<1>(d).m_name == import.m_name &&
                        std::get<1>(d).m_relative == import.m_relative) {
                    auto & mod_info = std::get<2>(d);

                    return loaded_module {
                            mod_info->m_mod,
                            mod_info->m_result.get().m_obj_code,
                            mod_info->m_result.get().m_obj_code_delayed_proofs,
                    };
                }
            }
            throw exception(sstream() << "could not resolve import: " << import.m_name);
        };

        bool use_exceptions = false;
        std::istringstream in(m_contents);
        parser p(m_initial_env, get_global_ios(), import_fn, in, get_module_id(),
                 use_exceptions,
                 (m_snapshots.empty() || !m_use_snapshots) ? std::shared_ptr<snapshot>() : m_snapshots.back(),
                 m_use_snapshots ? &m_snapshots : nullptr);
        bool parsed_ok = p();

        module_info::parse_result mod;

        mod.m_snapshots = std::move(m_snapshots);

        {
            std::ostringstream obj_code_buf(std::ios_base::binary);
            mod.m_obj_code_delayed_proofs =
                    export_module_delayed(obj_code_buf, p.env());
            mod.m_obj_code = obj_code_buf.str();
        }

        mod.m_env = optional<environment>(p.env());

        mod.m_opts = p.ios().get_options();

        mod.m_ok = parsed_ok; // TODO(gabriel): what should this be?

        return mod;
    }
};

class olean_compilation_task : public task<unit> {
    std::shared_ptr<module_info const> m_mod;

public:
    olean_compilation_task(std::shared_ptr<module_info const> const & mod) : m_mod(mod) {}
    task_kind get_kind() const override { return task_kind::parse; }

    std::vector<generic_task_result> get_dependencies() override {
        if (auto res = m_mod->m_result.peek()) {
            std::vector<generic_task_result> deps;
            res->m_env->for_each_declaration([&] (declaration const & d) {
                if (d.is_theorem()) deps.push_back(d.get_value_task());
            });
            return deps;
        } else {
            return {m_mod->m_result};
        }
    }

    void description(std::ostream & out) const override {
        out << "saving object code for " << get_module_id();
    }

    unit execute() override {
        if (m_mod->m_source != module_src::LEAN)
            throw exception("cannot build olean from olean");
        auto res = m_mod->m_result.get();
        auto env = *res.m_env;

        if (!res.m_ok)
            throw exception("not creating olean file because of errors");

        auto olean_fn = olean_of_lean(m_mod->m_mod);
        exclusive_file_lock output_lock(olean_fn);
        std::ofstream out(olean_fn, std::ios_base::binary);
        export_module(out, env);
        return {};
    }
};

// TODO(gabriel): adapt to vfs
static module_id resolve(module_id const & module_file_name, module_name const & ref) {
    auto base_dir = dirname(module_file_name.c_str());
    return find_file(base_dir, ref.m_relative, ref.m_name, ".lean");
}

void module_mgr::build_module(module_id const & id, bool can_use_olean, name_set module_stack) {
    if (auto & existing_mod = m_modules[id])
        if (!existing_mod->m_out_of_date) return;

    auto orig_module_stack = module_stack;
    if (module_stack.contains(id)) {
        throw exception(sstream() << "cyclic import: " << id);
    }
    module_stack.insert(id);

    scope_global_ios scope_ios(m_ios);
    scoped_message_buffer scoped_msg_buf(m_msg_buf);
    scoped_task_context(id, {1, 0});
    message_bucket_id bucket_id { id, m_current_period };
    scope_message_context scope_msg_ctx(bucket_id);
    scope_traces_as_messages scope_trace_msgs(id, {1, 0});

    try {
        bool already_have_lean_version = m_modules[id] && m_modules[id]->m_source == module_src::LEAN;

        std::string contents;
        module_src src;
        time_t mtime;
        std::tie(contents, src, mtime) = m_vfs->load_module(id, !already_have_lean_version && can_use_olean);

        if (src == module_src::OLEAN) {
            auto obj_code = contents;

            std::istringstream in2(obj_code, std::ios_base::binary);
            auto olean_fn = olean_of_lean(id);
            auto parsed_olean = parse_olean(in2, olean_fn);

            auto mod = std::make_shared<module_info>();

            mod->m_mod = id;
            mod->m_source = module_src::OLEAN;
            mod->m_version = m_current_period;
            mod->m_trans_mtime = mod->m_mtime = mtime;

            for (auto & d : parsed_olean.first) {
                auto d_id = resolve(id, d);
                build_module(d_id, true, module_stack);

                mod->m_deps.push_back(std::make_pair(d_id, d));

                auto & d_mod = m_modules[d_id];
                mod->m_trans_mtime = std::max(mod->m_trans_mtime, d_mod->m_trans_mtime);
            }

            if (mod->m_trans_mtime > mod->m_mtime)
                return build_module(id, false, orig_module_stack);

            module_info::parse_result res;
            res.m_obj_code = obj_code;
            res.m_ok = true;
            mod->m_result = mk_pure_task_result(res, "Loading " + olean_fn);

            get_global_task_queue().cancel_if(
                    [=] (generic_task * t) {
                        return t->get_version() < m_current_period && t->get_module_id() == id;
                    });
            m_modules[id] = mod;
        } else if (src == module_src::LEAN) {
            std::istringstream in(contents);

            auto bucket_name = "_build_module";

            snapshot_vector snapshots;
            if (m_use_snapshots) {
                if (get_snapshots_or_unchanged_module(id, contents, mtime, snapshots)) {
                    scope_msg_ctx.new_sub_bucket(bucket_name);
                    return;
                }
            }
            auto task_pos = snapshots.empty() ? pos_info {1, 0} : snapshots.back()->m_pos;
            scoped_task_context scope_task_ctx2(id, task_pos);

            scope_message_context scope_msg_ctx2(bucket_name);

            auto imports = get_direct_imports(id, contents);

            auto mod = std::make_shared<module_info>();
            mod->m_mod = id;
            mod->m_source = module_src::LEAN;
            mod->m_trans_mtime = mod->m_mtime = mtime;
            for (auto & d : imports) {
                module_id d_id;
                try {
                    d_id = resolve(id, d);
                    build_module(d_id, true, module_stack);
                    mod->m_trans_mtime = std::max(mod->m_trans_mtime, m_modules[d_id]->m_trans_mtime);
                } catch (throwable & ex) {
                    message_builder msg(m_initial_env, m_ios, id, pos_info {1, 0}, ERROR);
                    msg.set_exception(ex);
                    msg.report();
                }
                mod->m_deps.push_back({ d_id, d });
            }
            if (m_use_snapshots) {
                mod->m_lean_contents = optional<std::string>(contents);
                mod->m_still_valid_snapshots = snapshots;
            }
            mod->m_version = m_current_period;

            auto deps = gather_transitive_imports(id, imports);
            mod->m_result = get_global_task_queue().submit<parse_lean_task>(
                    contents, m_initial_env,
                    snapshots, m_use_snapshots,
                    deps);

            if (m_save_olean)
                mod->m_olean_task = get_global_task_queue().submit<olean_compilation_task>(mod);

            get_global_task_queue().cancel_if([=] (generic_task * t) {
                return t->get_version() < m_current_period && t->get_module_id() == id && t->get_pos() >= task_pos;
            });
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

std::shared_ptr<module_info const> module_mgr::get_module(module_id const & id) {
    unique_lock<mutex> lock(m_mutex);
    name_set module_stack;
    build_module(id, true, module_stack);
    return m_modules.at(id);
}

void module_mgr::invalidate(module_id const & id) {
    unique_lock<mutex> lock(m_mutex);
    m_current_period++;

    if (auto & mod = m_modules[id]) {
        mod->m_out_of_date = true;

        buffer<module_id> to_rebuild;
        mark_out_of_date(id, to_rebuild);

        build_module(id, true, {});
        for (auto & i : to_rebuild)
            build_module(i, true, {});
    }
}

static optional<pos_info> get_first_diff_pos(std::string const & a, std::string const & b) {
    std::istringstream in_a(a), in_b(b);
    for (unsigned line = 1;; line++) {
        if (in_a.eof() && in_b.eof()) return optional<pos_info>();
        if (in_a.eof() || in_b.eof()) return optional<pos_info>(line, 0);

        std::string line_a, line_b;
        std::getline(in_a, line_a);
        std::getline(in_b, line_b);
        // TODO(gabriel): return column as well
        if (line_a != line_b) return optional<pos_info>(line, 0);
    }
}

snapshot_vector module_mgr::get_snapshots(module_id const & id) {
    return get_module(id)->m_result.get().m_snapshots;
}

bool
module_mgr::get_snapshots_or_unchanged_module(module_id const &id, std::string const &contents, time_t /* mtime */,
                                              snapshot_vector &vector) {
    auto & mod = m_modules[id];
    if (!mod) return false;
    if (mod->m_source != module_src::LEAN) return false;

    for (auto d : mod->m_deps) {
        if (m_modules[d.first] && m_modules[d.first]->m_version > mod->m_version) {
            mod->m_still_valid_snapshots.clear();
            return false;
        }
    }

    if (!mod->m_lean_contents) return false;

    if (*mod->m_lean_contents == contents) return true;

    if (mod->m_result) {
        if (auto parse_res = mod->m_result.peek())
            mod->m_still_valid_snapshots = parse_res->m_snapshots;
    }
    if (mod->m_still_valid_snapshots.empty()) return false;

    if (auto diff_pos = get_first_diff_pos(contents, *mod->m_lean_contents)) {
        auto & snaps = mod->m_still_valid_snapshots;
        auto it = snaps.begin();
        while (it != snaps.end() && (*it)->m_pos < *diff_pos)
            it++;
        if (it != snaps.begin())
            it--;
        snaps.erase(it, snaps.end());
        vector = snaps;
        return false;
    } else {
        return true;
    }
}

std::vector<module_name> module_mgr::get_direct_imports(module_id const & id, std::string const & contents) {
    scope_message_context scope("dependencies");
    std::istringstream in(contents);
    bool use_exceptions = true;
    parser p(get_initial_env(), m_ios, nullptr, in, id, use_exceptions);
    std::vector<std::pair<module_name, module_id>> deps;
    return p.get_imports();
}

void module_mgr::gather_transitive_imports(std::vector<std::tuple<module_id, module_name, std::shared_ptr<module_info const>>> & res,
                                           std::unordered_set<module_id> & visited,
                                           module_id const & id,
                                           module_name const & import) {
    try {
        auto import_id = resolve(id, import);
        if (!m_modules[import_id]) return;
        res.push_back(std::make_tuple(id, import, m_modules[import_id]));
        if (!visited.count(import_id)) {
            visited.insert(import_id);
            for (auto & d : m_modules[import_id]->m_deps)
                gather_transitive_imports(res, visited, import_id, d.second);
        }
    } catch (file_not_found_exception & ex) {}
}

std::vector<std::tuple<module_id, module_name, std::shared_ptr<module_info const>>> module_mgr::gather_transitive_imports(
        module_id const & id, std::vector<module_name> const & imports) {
    std::unordered_set<module_id> visited;
    std::vector<std::tuple<module_id, module_name, std::shared_ptr<module_info const>>> res;
    for (auto & i : imports) gather_transitive_imports(res, visited, id, i);
    return res;
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

}
