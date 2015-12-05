/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/sstream.h"
#include "kernel/type_checker.h"
#include "library/scoped_ext.h"
#include "library/constants.h"
#include "library/kernel_serializer.h"
#include "library/tactic/tactic.h"
#include "frontends/lean/tactic_hint.h"
#include "frontends/lean/cmd_table.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/tokens.h"

namespace lean {
typedef list<expr> tactic_hints;

static name * g_class_name = nullptr;
static std::string * g_key = nullptr;

struct tactic_hint_config {
    typedef tactic_hints   state;
    typedef expr           entry;

    static void add_entry(environment const &, io_state const &, state & s, entry const & e) {
        s = cons(e, filter(s, [&](expr const & e1) { return e1 != e; }));
    }

    static name const & get_class_name() {
        return *g_class_name;
    }

    static std::string const & get_serialization_key() {
        return *g_key;
    }

    static void  write_entry(serializer & s, entry const & e) {
        s << e;
    }

    static entry read_entry(deserializer & d) {
        entry e;
        d >> e;
        return e;
    }

    static optional<unsigned> get_fingerprint(entry const & e) {
        return some(e.hash());
    }
};

template class scoped_ext<tactic_hint_config>;
typedef scoped_ext<tactic_hint_config> tactic_hint_ext;

void initialize_tactic_hint() {
    g_class_name = new name("tactic_hints");
    g_key        = new std::string("tachint");
    tactic_hint_ext::initialize();
}

void finalize_tactic_hint() {
    tactic_hint_ext::finalize();
    delete g_key;
    delete g_class_name;
}

list<expr> const & get_tactic_hints(environment const & env) {
    return tactic_hint_ext::get_state(env);
}

expr parse_tactic_name(parser & p) {
    auto pos = p.pos();
    name pre_tac = p.check_constant_next("invalid tactic name, constant expected");
    auto decl    = p.env().get(pre_tac);
    expr pre_tac_type = decl.get_type();
    if (!is_constant(pre_tac_type) || const_name(pre_tac_type) != get_tactic_name())
        throw parser_error(sstream() << "invalid tactic name, '" << pre_tac << "' is not a tactic", pos);
    buffer<level> ls;
    for (auto const & n : decl.get_univ_params())
        ls.push_back(mk_meta_univ(n));
    return mk_constant(pre_tac, to_list(ls.begin(), ls.end()));
}

environment tactic_hint_cmd(parser & p) {
    expr pre_tac = parse_tactic_name(p);
    return tactic_hint_ext::add_entry(p.env(), get_dummy_ios(), pre_tac, get_namespace(p.env()), true);
}

void register_tactic_hint_cmd(cmd_table & r) {
    add_cmd(r, cmd_info("tactic_hint",   "add a new tactic hint", tactic_hint_cmd));
}
}
