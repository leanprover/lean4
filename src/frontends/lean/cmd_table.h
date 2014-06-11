/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include <functional>
#include "kernel/environment.h"

namespace lean {
class tactic {};  // TODO(Leo): remove after tactic framework is ported to Lean 0.2

class parser;

typedef std::function<environment(parser&)> command_fn;
void register_builtin_cmd(char const * name, char const * descr, command_fn const & fn);

typedef std::function<tactic(parser&)> tactic_command_fn;
void register_builtin_cmd(char const * name, char const * descr, tactic_command_fn const & fn);

template<typename F>
struct register_builtin_cmd_tmpl {
    register_builtin_cmd_tmpl(char const * name, char const * descr, F const & fn) {
        register_builtin_cmd(name, descr, fn);
    }
};

typedef register_builtin_cmd_tmpl<command_fn>        register_builtin_cmd_fn;
typedef register_builtin_cmd_tmpl<tactic_command_fn> register_builtin_tactic_fn;

template<typename F>
struct cmd_info_tmpl {
    name        m_name;
    std::string m_descr;
    F           m_fn;
public:
    cmd_info_tmpl(name const & n, char const * d, F const & fn):
        m_name(n), m_descr(d), m_fn(fn) {}
    name const & get_name() const { return m_name; }
    std::string const & get_descr() const { return m_descr; }
    F const & get_fn() const { return m_fn; }
};

typedef cmd_info_tmpl<command_fn>        cmd_info;
typedef cmd_info_tmpl<tactic_command_fn> tactic_cmd_info;

typedef rb_map<name, cmd_info,        name_quick_cmp> cmd_table;
typedef rb_map<name, tactic_cmd_info, name_quick_cmp> tactic_cmd_table;

cmd_table        get_builtin_cmds();
tactic_cmd_table get_builtin_tactic_cmds();
}
