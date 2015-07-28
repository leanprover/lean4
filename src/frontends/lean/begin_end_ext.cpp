/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "kernel/type_checker.h"
#include "library/scoped_ext.h"
#include "library/kernel_serializer.h"
#include "library/annotation.h"
#include "library/tactic/expr_to_tactic.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/tactic_hint.h"

namespace lean {
// This (scoped) environment extension allows us to set a tactic to be applied before every element
// in a <tt>begin ... end</tt> block
struct be_entry {
    bool m_accumulate; // if true, then accumulate the new tactic, if false replace
    expr m_tac;
    be_entry():m_accumulate(false) {}
    be_entry(bool a, expr const & t):m_accumulate(a), m_tac(t) {}
};

struct be_state {
    optional<expr> m_pre_tac;
    optional<expr> m_pre_tac_body;
};

static name * g_class_name = nullptr;
static std::string * g_key = nullptr;

struct be_config {
    typedef be_state state;
    typedef be_entry entry;
    static void add_entry(environment const &, io_state const &, state & s, entry const & e) {
        if (e.m_accumulate) {
            if (s.m_pre_tac_body)
                s.m_pre_tac_body = mk_app(get_or_else_tac_fn(), *s.m_pre_tac_body, e.m_tac);
            else
                s.m_pre_tac_body = e.m_tac;
            s.m_pre_tac = mk_app(get_repeat_tac_fn(), *s.m_pre_tac_body);
        } else {
            // reset
            s.m_pre_tac      = e.m_tac;
            s.m_pre_tac_body = e.m_tac;
        }
    }
    static name const & get_class_name() {
        return *g_class_name;
    }
    static std::string const & get_serialization_key() {
        return *g_key;
    }
    static void  write_entry(serializer & s, entry const & e) {
        s << e.m_accumulate << e.m_tac;
    }
    static entry read_entry(deserializer & d) {
        entry e;
        d >> e.m_accumulate >> e.m_tac;
        return e;
    }
    static optional<unsigned> get_fingerprint(entry const & e) {
        return some(hash(e.m_accumulate, e.m_tac.hash()));
    }
};

template class scoped_ext<be_config>;
typedef scoped_ext<be_config> begin_end_ext;

static name * g_begin_end = nullptr;
static name * g_begin_end_element = nullptr;

expr mk_begin_end_annotation(expr const & e) { return mk_annotation(*g_begin_end, e, nulltag); }
expr mk_begin_end_element_annotation(expr const & e) { return mk_annotation(*g_begin_end_element, e, nulltag); }
bool is_begin_end_annotation(expr const & e) { return is_annotation(e, *g_begin_end); }
bool is_begin_end_element_annotation(expr const & e) { return is_annotation(e, *g_begin_end_element); }

void initialize_begin_end_ext() {
    g_class_name = new name("begin-end-hints");
    g_key        = new std::string("bepretac");
    begin_end_ext::initialize();
    g_begin_end  = new name("begin-end");
    g_begin_end_element = new name("begin-end-element");
    register_annotation(*g_begin_end);
    register_annotation(*g_begin_end_element);
}

void finalize_begin_end_ext() {
    delete g_begin_end;
    delete g_begin_end_element;
    begin_end_ext::finalize();
    delete g_key;
    delete g_class_name;
}

static void check_valid_tactic(environment const & env, expr const & pre_tac) {
    type_checker tc(env);
    if (!tc.is_def_eq(tc.infer(pre_tac).first, get_tactic_type()).first)
        throw exception("invalid begin-end pre-tactic update, argument is not a tactic");
}

environment add_begin_end_pre_tactic(environment const & env, expr const & pre_tac) {
    check_valid_tactic(env, pre_tac);
    return begin_end_ext::add_entry(env, get_dummy_ios(), be_entry(true, pre_tac));
}

environment set_begin_end_pre_tactic(environment const & env, expr const & pre_tac) {
    check_valid_tactic(env, pre_tac);
    return begin_end_ext::add_entry(env, get_dummy_ios(), be_entry(false, pre_tac));
}

optional<expr> get_begin_end_pre_tactic(environment const & env) {
    be_state const & s = begin_end_ext::get_state(env);
    return s.m_pre_tac;
}

environment add_begin_end_cmd(parser & p) {
    return add_begin_end_pre_tactic(p.env(), parse_tactic_name(p));
}

environment set_begin_end_cmd(parser & p) {
    return set_begin_end_pre_tactic(p.env(), parse_tactic_name(p));
}

void register_begin_end_cmds(cmd_table & r) {
    add_cmd(r, cmd_info("add_begin_end_tactic", "add a new tactic to be automatically applied before every component in a 'begin-end' block",
                        add_begin_end_cmd));
    add_cmd(r, cmd_info("set_begin_end_tactic", "reset the tactic that is automatically applied before every component in a 'begin-end' block",
                        set_begin_end_cmd));
}
}
