/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/sstream.h"
#include "util/list_fn.h"
#include "library/scoped_ext.h"
#include "library/kernel_serializer.h"
#include "frontends/lean/parser_config.h"
#include "frontends/lean/builtin_exprs.h"
#include "frontends/lean/builtin_tactics.h"
#include "frontends/lean/builtin_cmds.h"

namespace lean {
using notation::transition;
using notation::action;
using notation::action_kind;

notation_entry replace(notation_entry const & e, std::function<expr(expr const &)> const & f) {
    if (e.is_numeral())
        return notation_entry(e.get_num(), f(e.get_expr()), e.overload(), e.parse_only());
    else
        return notation_entry(e.is_nud(),
                              map(e.get_transitions(), [&](transition const & t) { return notation::replace(t, f); }),
                              f(e.get_expr()), e.overload(), e.priority(), e.group(), e.parse_only());
}

notation_entry::notation_entry():m_kind(notation_entry_kind::NuD) {}
notation_entry::notation_entry(notation_entry const & e):
    m_kind(e.m_kind), m_expr(e.m_expr), m_overload(e.m_overload),
    m_safe_ascii(e.m_safe_ascii), m_group(e.m_group), m_parse_only(e.m_parse_only),
    m_priority(e.m_priority) {
    if (is_numeral())
        new (&m_num) mpz(e.m_num);
    else
        new (&m_transitions) list<transition>(e.m_transitions);
}

notation_entry::notation_entry(bool is_nud, list<transition> const & ts, expr const & e, bool overload,
                               unsigned priority, notation_entry_group g, bool parse_only):
    m_kind(is_nud ? notation_entry_kind::NuD : notation_entry_kind::LeD),
    m_expr(e), m_overload(overload), m_group(g), m_parse_only(parse_only), m_priority(priority) {
    new (&m_transitions) list<transition>(ts);
    m_safe_ascii = std::all_of(ts.begin(), ts.end(), [](transition const & t) { return t.is_safe_ascii(); });
}
notation_entry::notation_entry(notation_entry const & e, bool overload):
    notation_entry(e) {
    m_overload = overload;
}
notation_entry::notation_entry(mpz const & val, expr const & e, bool overload, bool parse_only):
    m_kind(notation_entry_kind::Numeral), m_expr(e), m_overload(overload), m_safe_ascii(true), m_group(notation_entry_group::Main), m_parse_only(parse_only) {
    new (&m_num) mpz(val);
}

notation_entry::~notation_entry() {
    if (is_numeral())
        m_num.~mpz();
    else
        m_transitions.~list<transition>();
}

bool operator==(notation_entry const & e1, notation_entry const & e2) {
    if (e1.kind() != e2.kind() || e1.overload() != e2.overload() || e1.get_expr() != e2.get_expr() ||
        e1.group() != e2.group() || e1.parse_only() != e2.parse_only())
        return false;
    if (e1.is_numeral())
        return e1.get_num() == e2.get_num();
    else
        return e1.get_transitions() == e2.get_transitions();
}

struct token_state {
    token_table m_table;
    token_state() { m_table = mk_default_token_table(); }
};

struct token_config {
    typedef token_state  state;
    typedef token_entry  entry;
    static name * g_class_name;
    static std::string * g_key;

    static void add_entry(environment const &, io_state const &, state & s, entry const & e) {
        if (e.m_expr)
            s.m_table = add_token(s.m_table, e.m_token.c_str(), e.m_prec);
        else
            s.m_table = add_tactic_token(s.m_table, e.m_token.c_str(), e.m_prec);
    }
    static name const & get_class_name() {
        return *g_class_name;
    }
    static std::string const & get_serialization_key() {
        return *g_key;
    }
    static void  write_entry(serializer & s, entry const & e) {
        s << e.m_expr << e.m_token.c_str() << e.m_prec;
    }
    static entry read_entry(deserializer & d) {
        bool is_expr   = d.read_bool();
        std::string tk = d.read_string();
        unsigned prec  = d.read_unsigned();
        return entry(is_expr, tk, prec);
    }
    static optional<unsigned> get_fingerprint(entry const &) {
        return optional<unsigned>();
    }
};
name * token_config::g_class_name = nullptr;
std::string * token_config::g_key = nullptr;

template class scoped_ext<token_config>;
typedef scoped_ext<token_config> token_ext;

environment add_token(environment const & env, token_entry const & e, bool persistent) {
    return token_ext::add_entry(env, get_dummy_ios(), e, persistent);
}

environment add_expr_token(environment const & env, char const * val, unsigned prec) {
    return add_token(env, token_entry(true, val, prec));
}

environment add_tactic_token(environment const & env, char const * val, unsigned prec) {
    return add_token(env, token_entry(false, val, prec));
}

token_table const & get_token_table(environment const & env) {
    return token_ext::get_state(env).m_table;
}

serializer & operator<<(serializer & s, action const & a) {
    s << static_cast<char>(a.kind());
    switch (a.kind()) {
    case action_kind::Skip:
        break;
    case action_kind::Expr: case action_kind::Binder: case action_kind::Binders:
        s << a.rbp();
        break;
    case action_kind::Exprs:
        s << a.get_sep() << a.get_rec();
        if (a.get_initial())
            s << true << *a.get_initial();
        else
            s << false;
        s << a.is_fold_right() << a.rbp();
        if (auto t = a.get_terminator()) {
            s << true << *t;
        } else {
            s << false;
        }
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
        d >> rbp;
        return notation::mk_binder_action(rbp);
    case action_kind::Binders:
        d >> rbp;
        return notation::mk_binders_action(rbp);
    case action_kind::Expr:
        d >> rbp;
        return notation::mk_expr_action(rbp);
    case action_kind::Exprs: {
        name sep; expr rec; optional<expr> ini; bool is_fold_right;
        d >> sep >> rec;
        if (d.read_bool()) {
            ini = read_expr(d);
        }
        d >> is_fold_right >> rbp;
        optional<name> terminator;
        if (d.read_bool())
            terminator = read_name(d);
        return notation::mk_exprs_action(sep, rec, ini, terminator, is_fold_right, rbp);
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
    s << t.get_token() << t.get_pp_token() << t.get_action();
    return s;
}

transition read_transition(deserializer & d) {
    name   n  = read_name(d);
    name   pp = read_name(d);
    action a  = read_action(d);
    return transition(n, a, pp);
}

struct notation_state {
    typedef rb_map<mpz, list<expr>, mpz_cmp_fn> num_map;
    typedef head_map<notation_entry>            head_to_entries;
    parse_table      m_nud;
    parse_table      m_led;
    num_map          m_num_map;
    head_to_entries  m_inv_map;
    // The following two tables are used to implement `reserve notation` commands
    parse_table      m_reserved_nud;
    parse_table      m_reserved_led;
    // The following two tables are used to implement `notation [tactic]` commands
    parse_table      m_tactic_nud;
    parse_table      m_tactic_led;
    notation_state():
        m_nud(get_builtin_nud_table()),
        m_led(get_builtin_led_table()),
        m_reserved_nud(true),
        m_reserved_led(false),
        m_tactic_nud(get_builtin_tactic_nud_table()),
        m_tactic_led(get_builtin_tactic_led_table()) {
    }

    parse_table & nud(notation_entry_group g) {
        switch (g) {
        case notation_entry_group::Main:    return m_nud;
        case notation_entry_group::Reserve: return m_reserved_nud;
        case notation_entry_group::Tactic:  return m_tactic_nud;
        }
        lean_unreachable();
    }

    parse_table & led(notation_entry_group g) {
        switch (g) {
        case notation_entry_group::Main:    return m_led;
        case notation_entry_group::Reserve: return m_reserved_led;
        case notation_entry_group::Tactic:  return m_tactic_led;
        }
        lean_unreachable();
    }
};

struct notation_config {
    typedef notation_state  state;
    typedef notation_entry  entry;
    static name * g_class_name;
    static std::string * g_key;

    static void updt_inv_map(state & s, head_index const & idx, entry const & e) {
        if (!e.parse_only())
            s.m_inv_map.insert(idx, e);
    }

    static void add_entry(environment const &, io_state const &, state & s, entry const & e) {
        buffer<transition> ts;
        switch (e.kind()) {
        case notation_entry_kind::NuD: {
            to_buffer(e.get_transitions(), ts);
            if (auto idx = get_head_index(ts.size(), ts.data(), e.get_expr()))
                updt_inv_map(s, *idx, e);
            parse_table & nud = s.nud(e.group());
            nud = nud.add(ts.size(), ts.data(), e.get_expr(), e.priority(), e.overload());
            break;
        }
        case notation_entry_kind::LeD: {
            to_buffer(e.get_transitions(), ts);
            if (auto idx = get_head_index(ts.size(), ts.data(), e.get_expr()))
                updt_inv_map(s, *idx, e);
            parse_table & led = s.led(e.group());
            led = led.add(ts.size(), ts.data(), e.get_expr(), e.priority(), e.overload());
            break;
        }
        case notation_entry_kind::Numeral:
            if (!is_var(e.get_expr()))
                updt_inv_map(s, head_index(e.get_expr()), e);
            if (!e.overload()) {
                s.m_num_map.insert(e.get_num(), list<expr>(e.get_expr()));
            } else if (auto it = s.m_num_map.find(e.get_num())) {
                list<expr> new_exprs = cons(e.get_expr(), filter(*it, [&](expr const & n) { return n != e.get_expr(); }));
                s.m_num_map.insert(e.get_num(), new_exprs);
            } else {
                s.m_num_map.insert(e.get_num(), list<expr>(e.get_expr()));
            }
        }
    }
    static name const & get_class_name() {
        return *g_class_name;
    }
    static std::string const & get_serialization_key() {
        return *g_key;
    }
    static void  write_entry(serializer & s, entry const & e) {
        s << static_cast<char>(e.kind()) << e.overload() << e.parse_only() << e.get_expr();
        if (e.is_numeral()) {
            s << e.get_num();
        } else {
            s << static_cast<char>(e.group()) << length(e.get_transitions());
            for (auto const & t : e.get_transitions())
                s << t;
            s << e.priority();
        }
    }
    static entry read_entry(deserializer & d) {
        notation_entry_kind k = static_cast<notation_entry_kind>(d.read_char());
        bool overload, parse_only; expr e;
        d >> overload >> parse_only >> e;
        if (k == notation_entry_kind::Numeral) {
            mpz val;
            d >> val;
            return entry(val, e, overload, parse_only);
        } else {
            bool is_nud = k == notation_entry_kind::NuD;
            unsigned sz; char _g;
            d >> _g >> sz;
            notation_entry_group g = static_cast<notation_entry_group>(_g);
            buffer<transition> ts;
            for (unsigned i = 0; i < sz; i++)
                ts.push_back(read_transition(d));
            unsigned priority;
            d >> priority;
            return entry(is_nud, to_list(ts.begin(), ts.end()), e, overload, priority, g, parse_only);
        }
    }
    static optional<unsigned> get_fingerprint(entry const &) {
        return optional<unsigned>();
    }
};
name * notation_config::g_class_name = nullptr;
std::string * notation_config::g_key = nullptr;

template class scoped_ext<notation_config>;
typedef scoped_ext<notation_config> notation_ext;

environment add_notation(environment const & env, notation_entry const & e, bool persistent) {
    return notation_ext::add_entry(env, get_dummy_ios(), e, persistent);
}

parse_table const & get_nud_table(environment const & env) {
    return notation_ext::get_state(env).m_nud;
}

parse_table const & get_led_table(environment const & env) {
    return notation_ext::get_state(env).m_led;
}

parse_table const & get_reserved_nud_table(environment const & env) {
    return notation_ext::get_state(env).m_reserved_nud;
}

parse_table const & get_reserved_led_table(environment const & env) {
    return notation_ext::get_state(env).m_reserved_led;
}

parse_table const & get_tactic_nud_table(environment const & env) {
    return notation_ext::get_state(env).m_tactic_nud;
}

parse_table const & get_tactic_led_table(environment const & env) {
    return notation_ext::get_state(env).m_tactic_led;
}

environment add_mpz_notation(environment const & env, mpz const & n, expr const & e, bool overload, bool parse_only) {
    return add_notation(env, notation_entry(n, e, overload, parse_only));
}

list<expr> get_mpz_notation(environment const & env, mpz const & n) {
    if (auto it = notation_ext::get_state(env).m_num_map.find(n)) {
        return *it;
    } else {
        return list<expr>();
    }
}

list<notation_entry> get_notation_entries(environment const & env, head_index const & idx) {
    if (auto it = notation_ext::get_state(env).m_inv_map.find(idx))
        return *it;
    else
        return list<notation_entry>();
}

environment override_notation(environment const & env, name const & n, bool persistent) {
    environment r = env;
    bool found = false;
    if (auto it = token_ext::get_entries(r, n)) {
        list<token_entry> entries = *it;
        found = true;
        for (token_entry e : entries) {
            r = add_token(r, e, persistent);
        }
    }
    if (auto it = notation_ext::get_entries(env, n)) {
        list<notation_entry> entries = *it;
        found = true;
        for (notation_entry const & e : entries) {
            notation_entry new_e(e, false);
            r = add_notation(r, new_e, persistent);
        }
    }
    if (!found)
        throw exception(sstream() << "unknown namespace '" << n << "'");
    return r;
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
static cmd_ext_reg * g_ext = nullptr;
static cmd_ext const & get_extension(environment const & env) {
    return static_cast<cmd_ext const &>(env.get_extension(g_ext->m_ext_id));
}
cmd_table const & get_cmd_table(environment const & env) {
    return get_extension(env).m_cmds;
}

void initialize_parser_config() {
    token_config::g_class_name = new name("notations");
    token_config::g_key        = new std::string("tk");
    token_ext::initialize();
    notation_config::g_class_name = new name("notations");
    notation_config::g_key        = new std::string("nota");
    notation_ext::initialize();
    g_ext = new cmd_ext_reg();
}
void finalize_parser_config() {
    delete g_ext;
    notation_ext::finalize();
    delete notation_config::g_key;
    delete notation_config::g_class_name;
    token_ext::finalize();
    delete token_config::g_key;
    delete token_config::g_class_name;
}
}
