/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include <functional>
#include "kernel/environment.h"
#include "library/tactic/tactic.h"

namespace lean {
class parser;

typedef std::function<environment(parser&)> command_fn;
typedef std::function<tactic(parser&, pos_info const &)> tactic_command_fn;

template<typename F>
struct cmd_info_tmpl {
    name        m_name;
    std::string m_descr;
    F           m_fn;
public:
    cmd_info_tmpl(name const & n, char const * d, F const & fn):
        m_name(n), m_descr(d), m_fn(fn) {}
    cmd_info_tmpl() {}
    name const & get_name() const { return m_name; }
    std::string const & get_descr() const { return m_descr; }
    F const & get_fn() const { return m_fn; }
};

typedef cmd_info_tmpl<command_fn>        cmd_info;
typedef cmd_info_tmpl<tactic_command_fn> tactic_cmd_info;

typedef rb_map<name, cmd_info,        name_quick_cmp> cmd_table;
typedef rb_map<name, tactic_cmd_info, name_quick_cmp> tactic_cmd_table;

inline void add_cmd(cmd_table & t, cmd_info const & cmd) { t.insert(cmd.get_name(), cmd); }
}
