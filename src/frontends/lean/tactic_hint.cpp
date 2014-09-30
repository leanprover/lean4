/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/sstream.h"
#include "kernel/type_checker.h"
#include "library/scoped_ext.h"
#include "library/kernel_serializer.h"
#include "library/tactic/tactic.h"
#include "library/tactic/expr_to_tactic.h"
#include "frontends/lean/tactic_hint.h"
#include "frontends/lean/cmd_table.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/class.h"
#include "frontends/lean/tokens.h"

namespace lean {
typedef list<tactic_hint_entry> tactic_hint_entries;

struct tactic_hint_state {
    typedef name_map<tactic_hint_entries> class_tactics;
    class_tactics        m_class_tactics;
    tactic_hint_entries  m_tactics;
};

static name * g_class_name = nullptr;
static std::string * g_key = nullptr;

struct tactic_hint_config {
    typedef tactic_hint_state   state;
    typedef tactic_hint_entry   entry;
    typedef tactic_hint_entries entries;

    static entries add(entries const & l, entry const & e) {
        return cons(e, filter(l, [&](entry const & e1) { return e1.m_pre_tactic != e.m_pre_tactic; }));
    }

    static void add_entry_core(state & s, entry const & e) {
        if (e.m_class.is_anonymous())
            s.m_tactics = add(s.m_tactics, e);
        else if (auto it = s.m_class_tactics.find(e.m_class))
            s.m_class_tactics.insert(e.m_class, add(*it, e));
        else
            s.m_class_tactics.insert(e.m_class, entries(e));
    }

    static void add_entry(environment const & env, io_state const &, state & s, entry const & e) {
        if (!e.m_compiled) {
            entry new_e(e);
            new_e.m_tactic   = expr_to_tactic(env, e.m_pre_tactic, nullptr);
            new_e.m_compiled = true;
            add_entry_core(s, new_e);
        } else {
            add_entry_core(s, e);
        }
    }

    static name const & get_class_name() {
        return *g_class_name;
    }

    static std::string const & get_serialization_key() {
        return *g_key;
    }

    static void  write_entry(serializer & s, entry const & e) {
        s << e.m_class << e.m_pre_tactic;
    }

    static entry read_entry(deserializer & d) {
        entry e;
        d >> e.m_class >> e.m_pre_tactic;
        return e;
    }
    static optional<unsigned> get_fingerprint(entry const & e) {
        return some(hash(e.m_class.hash(), e.m_pre_tactic.hash()));
    }
};

template class scoped_ext<tactic_hint_config>;
typedef scoped_ext<tactic_hint_config> tactic_hint_ext;

void initialize_tactic_hint() {
    g_class_name = new name("tactic_hint");
    g_key        = new std::string("tachint");
    tactic_hint_ext::initialize();
}

void finalize_tactic_hint() {
    tactic_hint_ext::finalize();
    delete g_key;
    delete g_class_name;
}

list<tactic_hint_entry> get_tactic_hints(environment const & env, name const & c) {
    tactic_hint_state const & s = tactic_hint_ext::get_state(env);
    return ptr_to_list(s.m_class_tactics.find(c));
}

list<tactic_hint_entry> get_tactic_hints(environment const & env) {
    tactic_hint_state const & s = tactic_hint_ext::get_state(env);
    return s.m_tactics;
}

expr parse_tactic_name(parser & p) {
    auto pos = p.pos();
    name pre_tac = p.check_constant_next("invalid tactic name, constant expected");
    auto decl    = p.env().get(pre_tac);
    expr pre_tac_type = decl.get_type();
    if (!is_constant(pre_tac_type) || const_name(pre_tac_type) != name("tactic"))
        throw parser_error(sstream() << "invalid tactic name, '" << pre_tac << "' is not a tactic", pos);
    buffer<level> ls;
    for (auto const & n : decl.get_univ_params())
        ls.push_back(mk_meta_univ(n));
    return mk_constant(pre_tac, to_list(ls.begin(), ls.end()));
}

environment tactic_hint_cmd(parser & p) {
    name cls;
    if (p.curr_is_token(get_lbracket_tk())) {
        p.next();
        cls      = get_class_name(p.env(), p.parse_expr());
        p.check_token_next(get_rbracket_tk(), "invalid tactic hint, ']' expected");
    }
    expr pre_tac = parse_tactic_name(p);
    tactic tac   = expr_to_tactic(p.env(), pre_tac, nullptr);
    return tactic_hint_ext::add_entry(p.env(), get_dummy_ios(), tactic_hint_entry(cls, pre_tac, tac));
}

void register_tactic_hint_cmd(cmd_table & r) {
    add_cmd(r, cmd_info("tactic_hint",   "add a new tactic hint", tactic_hint_cmd));
}
}
