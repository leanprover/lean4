/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include <functional>
#include "kernel/environment.h"
#include "frontends/lean/decl_util.h"
#include "frontends/lean/parser_pos_provider.h"

namespace lean {
class parser;

struct cmd_meta {
    decl_attributes       m_attrs;
    decl_modifiers        m_modifiers;
    optional<std::string> m_doc_string;
    cmd_meta() {}
    explicit cmd_meta(decl_attributes const & attrs):m_attrs(attrs) {}
    cmd_meta(decl_attributes const & attrs, decl_modifiers const & mods,
             optional<std::string> const & doc = optional<std::string>()):
        m_attrs(attrs), m_modifiers(mods), m_doc_string(doc) {}
};

typedef std::function<environment(parser&, cmd_meta const &)> command_fn;

template<typename F>
struct cmd_info_tmpl {
    name        m_name;
    std::string m_descr;
    F           m_fn;
    bool        m_skip_token;
public:
    cmd_info_tmpl(name const & n, char const * d, F const & fn, bool skip_token = true):
        m_name(n), m_descr(d), m_fn(fn), m_skip_token(skip_token) {}
    cmd_info_tmpl(name const & n, char const * d, std::function<environment(parser&)> const & fn, bool skip_token = true):
        cmd_info_tmpl(n, d, [=](parser & p, cmd_meta const & meta) {
            if (meta.m_modifiers)
                throw exception("command does not accept modifiers");
            if (meta.m_attrs)
                throw exception("command does not accept attributes");
            if (meta.m_doc_string)
                throw exception("command does not accept doc string");
            return fn(p);
        }, skip_token) {}
    cmd_info_tmpl() {}
    name const & get_name() const { return m_name; }
    std::string const & get_descr() const { return m_descr; }
    F const & get_fn() const { return m_fn; }
    bool const & get_skip_token() const { return m_skip_token; }
};

typedef cmd_info_tmpl<command_fn>              cmd_info;
typedef name_map<cmd_info> cmd_table;
inline void add_cmd(cmd_table & t, cmd_info const & cmd) { t.insert(cmd.get_name(), cmd); }
}
