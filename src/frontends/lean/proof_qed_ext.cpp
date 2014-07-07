/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "kernel/type_checker.h"
#include "library/scoped_ext.h"
#include "library/kernel_serializer.h"
#include "library/tactic/expr_to_tactic.h"
#include "frontends/lean/parser.h"

namespace lean {
// This (scoped) environment extension allows us to set a tactic to be applied before every element
// in a <tt>proof ... qed</tt> block
struct pq_entry {
    bool m_accumulate; // if true, then accumulate the new tactic, if false replace
    expr m_tac;
    pq_entry():m_accumulate(false) {}
    pq_entry(bool a, expr const & t):m_accumulate(a), m_tac(t) {}
};

struct pq_state {
    optional<expr> m_pre_tac;
    optional<expr> m_pre_tac_body;
};

struct pq_config {
    typedef pq_state state;
    typedef pq_entry entry;
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
        static name g_class_name("proof_qed");
        return g_class_name;
    }
    static std::string const & get_serialization_key() {
        static std::string g_key("pq_pre_tac");
        return g_key;
    }
    static void  write_entry(serializer & s, entry const & e) {
        s << e.m_accumulate << e.m_tac;
    }
    static entry read_entry(deserializer & d) {
        entry e;
        d >> e.m_accumulate >> e.m_tac;
        return e;
    }
};

template class scoped_ext<pq_config>;
typedef scoped_ext<pq_config> proof_qed_ext;

static void check_valid_tactic(environment const & env, expr const & pre_tac) {
    type_checker tc(env);
    if (!tc.is_def_eq(tc.infer(pre_tac), get_tactic_type()))
        throw exception("invalid proof-qed pre-tactic update, argument is not a tactic");
}

environment add_proof_qed_pre_tactic(environment const & env, expr const & pre_tac) {
    check_valid_tactic(env, pre_tac);
    return proof_qed_ext::add_entry(env, get_dummy_ios(), pq_entry(true, pre_tac));
}

environment set_proof_qed_pre_tactic(environment const & env, expr const & pre_tac) {
    check_valid_tactic(env, pre_tac);
    return proof_qed_ext::add_entry(env, get_dummy_ios(), pq_entry(false, pre_tac));
}

optional<expr> get_proof_qed_pre_tactic(environment const & env) {
    pq_state const & s = proof_qed_ext::get_state(env);
    return s.m_pre_tac;
}

static expr parse_tactic_name(parser & p) {
    auto pos = p.pos();
    name id  = p.check_id_next("invalid proof_qed configuration command, indentifier expected");
    return p.id_to_expr(id, pos);
}

environment add_proof_qed_cmd(parser & p) {
    return add_proof_qed_pre_tactic(p.env(), parse_tactic_name(p));
}

environment set_proof_qed_cmd(parser & p) {
    return set_proof_qed_pre_tactic(p.env(), parse_tactic_name(p));
}

void register_proof_qed_cmds(cmd_table & r) {
    add_cmd(r, cmd_info("add_proof_qed",   "add a new tactic to be automatically applied before every component in a 'proof-qed' block",
                        add_proof_qed_cmd));
    add_cmd(r, cmd_info("set_proof_qed", "reset the tactic that is automatically applied before every component in a 'proof-qed' block",
                        set_proof_qed_cmd));
}
}
