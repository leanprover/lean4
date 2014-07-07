/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/sstream.h"
#include "library/scoped_ext.h"
#include "library/kernel_serializer.h"
#include "frontends/lean/parser_config.h"
#include "frontends/lean/builtin_exprs.h"
#include "frontends/lean/builtin_cmds.h"

namespace lean {
using notation::transition;
using notation::action;
using notation::action_kind;

struct token_state {
    token_table m_table;
    token_state() { m_table = mk_default_token_table(); }
};

struct token_config {
    typedef token_state  state;
    typedef token_entry  entry;
    static void add_entry(environment const &, io_state const &, state & s, entry const & e) {
        s.m_table = add_token(s.m_table, e.m_token.c_str(), e.m_prec);
    }
    static name const & get_class_name() {
        static name g_class_name("notation");
        return g_class_name;
    }
    static std::string const & get_serialization_key() {
        static std::string g_key("tk");
        return g_key;
    }
    static void  write_entry(serializer & s, entry const & e) {
        s << e.m_token.c_str() << e.m_prec;
    }
    static entry read_entry(deserializer & d) {
        std::string tk = d.read_string();
        unsigned prec  = d.read_unsigned();
        return entry(tk, prec);
    }
};

template class scoped_ext<token_config>;
typedef scoped_ext<token_config> token_ext;

environment add_token(environment const & env, token_entry const & e) {
    return token_ext::add_entry(env, get_dummy_ios(), e);
}

environment add_token(environment const & env, char const * val, unsigned prec) {
    return add_token(env, token_entry(val, prec));
}

token_table const & get_token_table(environment const & env) {
    return token_ext::get_state(env).m_table;
}

serializer & operator<<(serializer & s, action const & a) {
    s << static_cast<char>(a.kind());
    switch (a.kind()) {
    case action_kind::Skip: case action_kind::Binder: case action_kind::Binders:
        break;
    case action_kind::Expr:
        s << a.rbp();
        break;
    case action_kind::Exprs:
        s << a.get_sep() << a.get_rec() << a.get_initial() << a.is_fold_right() << a.rbp();
        break;
    case action_kind::ScopedExpr:
        s << a.get_rec() << a.rbp() << a.use_lambda_abstraction();
        break;
    case action_kind::LuaExt:
        s << a.get_lua_fn();
        break;
    case action_kind::Ext:
        lean_unreachable();
    }
    return s;
}

action read_action(deserializer & d) {
    action_kind k = static_cast<action_kind>(d.read_char());
    unsigned rbp;
    switch (k) {
    case action_kind::Skip:
        return notation::mk_skip_action();
    case action_kind::Binder:
        return notation::mk_binder_action();
    case action_kind::Binders:
        return notation::mk_binders_action();
    case action_kind::Expr:
        d >> rbp;
        return notation::mk_expr_action(rbp);
    case action_kind::Exprs: {
        name sep; expr rec, ini; bool is_fold_right;
        d >> sep >> rec >> ini >> is_fold_right >> rbp;
        return notation::mk_exprs_action(sep, rec, ini, is_fold_right, rbp);
    }
    case action_kind::ScopedExpr: {
        expr rec; bool use_lambda_abstraction;
        d >> rec >> rbp >> use_lambda_abstraction;
        return notation::mk_scoped_expr_action(rec, rbp, use_lambda_abstraction);
    }
    case action_kind::LuaExt:
        return notation::mk_ext_lua_action(d.read_string().c_str());
    case action_kind::Ext:
        break;
    }
    lean_unreachable();
}

serializer & operator<<(serializer & s, transition const & t) {
    s << t.get_token() << t.get_action();
    return s;
}

transition read_transition(deserializer & d) {
    name   n = read_name(d);
    action a = read_action(d);
    return transition(n, a);
}

struct notation_state {
    parse_table      m_nud;
    parse_table      m_led;
    notation_state() {
        m_nud = get_builtin_nud_table();
        m_led = get_builtin_led_table();
    }
};

struct notation_config {
    typedef notation_state  state;
    typedef notation_entry  entry;
    static void add_entry(environment const &, io_state const &, state & s, entry const & e) {
        buffer<transition> ts;
        to_buffer(e.m_transitions, ts);
        if (e.m_is_nud)
            s.m_nud = s.m_nud.add(ts.size(), ts.data(), e.m_expr, e.m_overload);
        else
            s.m_led = s.m_led.add(ts.size(), ts.data(), e.m_expr, e.m_overload);
    }
    static name const & get_class_name() {
        static name g_class_name("notation");
        return g_class_name;
    }
    static std::string const & get_serialization_key() {
        static std::string g_key("nota");
        return g_key;
    }
    static void  write_entry(serializer & s, entry const & e) {
        s << e.m_is_nud << e.m_overload << e.m_expr;
        s << length(e.m_transitions);
        for (auto const & t : e.m_transitions)
            s << t;
    }
    static entry read_entry(deserializer & d) {
        bool is_nud, overload; expr e;
        d >> is_nud >> overload >> e;
        unsigned sz;
        d >> sz;
        buffer<transition> ts;
        for (unsigned i = 0; i < sz; i++)
            ts.push_back(read_transition(d));
        return entry(is_nud, to_list(ts.begin(), ts.end()), e, overload);
    }
};

template class scoped_ext<notation_config>;
typedef scoped_ext<notation_config> notation_ext;

environment add_notation(environment const & env, notation_entry const & e) {
    return notation_ext::add_entry(env, get_dummy_ios(), e);
}

environment add_nud_notation(environment const & env, unsigned num, notation::transition const * ts, expr const & a, bool overload) {
    return add_notation(env, notation_entry(true, to_list(ts, ts+num), a, overload));
}

environment add_led_notation(environment const & env, unsigned num, notation::transition const * ts, expr const & a, bool overload) {
    return add_notation(env, notation_entry(false, to_list(ts, ts+num), a, overload));
}

environment add_nud_notation(environment const & env, std::initializer_list<notation::transition> const & ts, expr const & a, bool overload) {
    return add_nud_notation(env, ts.size(), ts.begin(), a, overload);
}

environment add_led_notation(environment const & env, std::initializer_list<notation::transition> const & ts, expr const & a, bool overload) {
    return add_led_notation(env, ts.size(), ts.begin(), a, overload);
}

environment overwrite_notation(environment const & env, name const & n) {
    environment r = env;
    bool found = false;
    if (auto it = token_ext::get_entries(r, n)) {
        found = true;
        for (token_entry e : *it) {
            r = add_token(r, e);
        }
    }
    if (auto it = notation_ext::get_entries(env, n)) {
        found = true;
        for (notation_entry e : *it) {
            e.m_overload = false;
            r = add_notation(r, e);
        }
    }
    if (!found)
        throw exception(sstream() << "unknown namespace '" << n << "'");
    return r;
}

parse_table const & get_nud_table(environment const & env) {
    return notation_ext::get_state(env).m_nud;
}

parse_table const & get_led_table(environment const & env) {
    return notation_ext::get_state(env).m_led;
}

struct cmd_ext : public environment_extension {
    cmd_table m_cmds;
    cmd_ext() {
        m_cmds        = get_builtin_cmds();
    }
};

struct cmd_ext_reg {
    unsigned m_ext_id;
    cmd_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<cmd_ext>()); }
};
static cmd_ext_reg g_ext;
static cmd_ext const & get_extension(environment const & env) {
    return static_cast<cmd_ext const &>(env.get_extension(g_ext.m_ext_id));
}
cmd_table const & get_cmd_table(environment const & env) {
    return get_extension(env).m_cmds;
}
}
