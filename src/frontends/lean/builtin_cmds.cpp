/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "util/sstream.h"
#include "kernel/type_checker.h"
#include "library/io_state_stream.h"
#include "library/scoped_ext.h"
#include "library/aliases.h"
#include "library/locals.h"
#include "frontends/lean/parser.h"

namespace lean {
static name g_raw("raw");
static name g_llevel_curly(".{");
static name g_rcurly("}");
static name g_colon(":");

static void check_atomic(name const & n) {
    if (!n.is_atomic())
        throw exception(sstream() << "invalid declaration name '" << n << "', identifier must be atomic");
}

environment universe_cmd(parser & p) {
    name n = p.check_id_next("invalid universe declaration, identifier expected");
    check_atomic(n);
    environment env = p.env();
    if (in_section(env)) {
        p.add_local_level(n, mk_param_univ(n));
    } else {
        name const & ns = get_namespace(env);
        name full_n  = ns + n;
        env = env.add_universe(full_n);
        if (!ns.is_anonymous())
            env = add_alias(env, n, mk_global_univ(full_n));
    }
    return env;
}

static void check_in_section(parser const & p) {
    if (!in_section(p.env()))
        throw exception(sstream() << "invalid command, it must be used in a section");
}

static void parse_univ_params(parser & p, buffer<name> & ps) {
    if (p.curr_is_token(g_llevel_curly)) {
        p.next();
        while (!p.curr_is_token(g_rcurly)) {
            name l = p.check_id_next("invalid universe parameter, identifier expected");
            p.add_local_level(l, mk_param_univ(l));
            ps.push_back(l);
        }
        p.next();
    }
}

struct local_scope_if_not_section {
    parser & m_p;
    local_scope_if_not_section(parser & p):m_p(p) {
        if (!in_section(p.env()))
            p.push_local_scope();
    }
    ~local_scope_if_not_section() {
        if (!in_section(m_p.env()))
            m_p.pop_local_scope();
    }
};

static void update_parameters(buffer<name> & ls_buffer, name_set const & found, parser const & p) {
    unsigned old_sz = ls_buffer.size();
    found.for_each([&](name const & n) {
            if (std::find(ls_buffer.begin(), ls_buffer.begin() + old_sz, n) == ls_buffer.begin() + old_sz)
                ls_buffer.push_back(n);
        });
    std::sort(ls_buffer.begin(), ls_buffer.end(), [&](name const & n1, name const & n2) {
            return *p.get_local_level_index(n1) < *p.get_local_level_index(n2);
        });
}

environment variable_cmd_core(parser & p, bool is_axiom, binder_info const & bi) {
    name n = p.check_id_next("invalid declaration, identifier expected");
    check_atomic(n);
    buffer<name> ls_buffer;
    buffer<parameter> ps;
    if (p.curr_is_token(g_llevel_curly) && in_section(p.env()))
        throw parser_error("invalid declaration, axioms/parameters occurring in sections cannot be universe polymorphic", p.pos());
    local_scope_if_not_section scope(p);
    parse_univ_params(p, ls_buffer);
    p.set_type_use_placeholder(false);
    if (!p.curr_is_token(g_colon))
        p.parse_binders(ps);
    p.check_token_next(g_colon, "invalid declaration, ':' expected");
    expr type = p.parse_scoped_expr(ps);
    level_param_names ls;
    if (in_section(p.env())) {
        ls = to_level_param_names(collect_univ_params(type));
    } else {
        update_parameters(ls_buffer, collect_univ_params(type), p);
        ls = to_list(ls_buffer.begin(), ls_buffer.end());
    }
    type = p.pi_abstract(ps, type);
    type = p.elaborate(type, ls);
    if (in_section(p.env())) {
        p.add_local_expr(n, mk_local(n, n, type), bi);
        return p.env();
    } else {
        environment env = p.env();
        name const & ns = get_namespace(env);
        name full_n  = ns + n;
        if (is_axiom)
            env = env.add(check(env, mk_axiom(full_n, ls, type)));
        else
            env = env.add(check(env, mk_var_decl(full_n, ls, type)));
        if (!ns.is_anonymous())
            env = add_alias(env, n, mk_constant(full_n));
        return env;
    }
}
environment variable_cmd(parser & p) {
    return variable_cmd_core(p, false, binder_info());
}
environment axiom_cmd(parser & p)    {
    return variable_cmd_core(p, true, binder_info());
}
environment implicit_variable_cmd(parser & p) {
    check_in_section(p);
    return variable_cmd_core(p, false, mk_implicit_binder_info());
}
environment implicit_axiom_cmd(parser & p) {
    check_in_section(p);
    return variable_cmd_core(p, true, mk_implicit_binder_info());
}
environment cast_variable_cmd(parser & p) {
    check_in_section(p);
    return variable_cmd_core(p, false, mk_cast_binder_info());
}

environment print_cmd(parser & p) {
    if (p.curr() == scanner::token_kind::String) {
        p.regular_stream() << p.get_str_val() << "\n";
        p.next();
    } else if (p.curr_is_token(g_raw)) {
        p.next();
        expr e = p.parse_expr();
        p.regular_stream() << e << "\n";
    } else {
        throw parser_error("invalid print command", p.pos());
    }
    return p.env();
}

environment section_cmd(parser & p) {
    p.push_local_scope();
    return push_scope(p.env(), p.ios());
}

environment namespace_cmd(parser & p) {
    name n = p.check_id_next("invalid namespace declaration, identifier expected");
    check_atomic(n);
    return push_scope(p.env(), p.ios(), n);
}

environment end_scoped_cmd(parser & p) {
    if (in_section(p.env()))
        p.pop_local_scope();
    return pop_scope(p.env());
}

environment check_cmd(parser & p) {
    expr e   = p.parse_expr();
    level_param_names ls = to_level_param_names(collect_univ_params(e));
    e = p.elaborate(e, ls);
    expr type = type_checker(p.env()).check(e, ls);
    p.regular_stream() << e << " : " << type << endl;
    return p.env();
}

cmd_table init_cmd_table() {
    cmd_table r;
    add_cmd(r, cmd_info("print",        "print a string", print_cmd));
    add_cmd(r, cmd_info("universe",     "declare a global universe level", universe_cmd));
    add_cmd(r, cmd_info("section",      "open a new section", section_cmd));
    add_cmd(r, cmd_info("namespace",    "open a new namespace", namespace_cmd));
    add_cmd(r, cmd_info("end",          "close the current namespace/section", end_scoped_cmd));
    add_cmd(r, cmd_info("variable",     "declare a new parameter", variable_cmd));
    add_cmd(r, cmd_info("{variable}",   "declare a new implict parameter", implicit_variable_cmd));
    add_cmd(r, cmd_info("[variable]",   "declare a new cast parameter", cast_variable_cmd));
    add_cmd(r, cmd_info("axiom",        "declare a new axiom", axiom_cmd));
    add_cmd(r, cmd_info("{axiom}",      "declare a new implicit axiom", implicit_axiom_cmd));
    add_cmd(r, cmd_info("check",        "type check given expression, and display its type", check_cmd));
    return r;
}

cmd_table get_builtin_cmds() {
    static optional<cmd_table> r;
    if (!r)
        r = init_cmd_table();
    return *r;
}
}
