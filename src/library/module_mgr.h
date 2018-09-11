/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Gabriel Ebner, Sebastian Ullrich
*/
#pragma once
#include <string>
#include <utility>
#include <vector>
#include <unordered_map>
#include <unordered_set>
#include "util/unit.h"
#include "util/name.h"
#include "kernel/environment.h"
#include "library/io_state.h"
#include "library/trace.h"
#include "frontends/lean/parser.h"
#include "util/lean_path.h"

namespace lean {

enum class module_src {
    OLEAN,
    LEAN,
};

struct module_info {
    module_name m_name;
    std::string m_file_name;
    std::string m_contents;
    module_src m_source = module_src::LEAN;
    time_t m_mtime = -1, m_trans_mtime = -1;

    struct dependency {
        module_name m_name;
        std::shared_ptr<module_info> m_mod_info;
    };
    std::vector<dependency> m_deps;

    struct parse_result {
        options               m_opts;
        std::shared_ptr<loaded_module const> m_loaded_module;
    };
    message_log m_log;
    parse_result m_result;
    bool m_compiled_olean;

    module_info() {}

    module_info(module_name const & name, std::string const & contents, module_src src, time_t mtime)
            : m_name(name), m_contents(contents), m_source(src), m_mtime(mtime) {}
};

class module_mgr {
    bool m_save_olean = false;

    search_path m_path;
    environment m_initial_env;
    io_state m_ios;

    name_map<std::shared_ptr<module_info>> m_modules;

    void build_module(module_name const & mod, bool can_use_olean, name_set module_stack);

    std::vector<module_name>
    get_direct_imports(std::string const & file_name, std::string const & contents);
    void build_lean(std::shared_ptr<module_info> const & mod, std::string const & file_name, name_set const & module_stack);
public:
    module_mgr(search_path const & path,
               environment const & initial_env, io_state const & ios) :
            m_path(path), m_initial_env(initial_env), m_ios(ios) {}

    std::shared_ptr<module_info const> get_module(module_name const &);
    module_loader mk_loader();

    void set_save_olean(bool save_olean) { m_save_olean = save_olean; }
    bool get_save_olean() const { return m_save_olean; }

    environment get_initial_env() const { return m_initial_env; }
    options get_options() const { return m_ios.get_options(); }
    io_state get_io_state() const { return m_ios; }
};
}
