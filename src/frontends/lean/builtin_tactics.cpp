/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <limits>
#include "library/explicit.h"
#include "library/tactic/apply_tactic.h"
#include "library/tactic/rename_tactic.h"
#include "library/tactic/intros_tactic.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/parse_table.h"

#define LEAN_APPLY_RBP 16 // it should be bigger than `;` (and_then) precedence

namespace lean {
using notation::transition;
using notation::mk_ext_action;

static expr parse_apply(parser & p, unsigned, expr const *, pos_info const & pos) {
    parser::no_undef_id_error_scope scope(p);
    expr e = p.parse_expr(LEAN_APPLY_RBP);
    return p.save_pos(mk_apply_tactic_macro(e), pos);
}

static expr parse_rename(parser & p, unsigned, expr const *, pos_info const & pos) {
    name from = p.check_id_next("invalid 'rename' tactic, identifier expected");
    name to   = p.check_id_next("invalid 'rename' tactic, identifier expected");
    return p.save_pos(mk_rename_tactic_macro(from, to), pos);
}

static expr parse_intros(parser & p, unsigned, expr const *, pos_info const & pos) {
    buffer<name> ns;
    while (p.curr_is_identifier()) {
        ns.push_back(p.get_name_val());
        p.next();
    }
    return p.save_pos(mk_intros_tactic_macro(ns), pos);
}

void init_nud_tactic_table(parse_table & r) {
    expr x0 = mk_var(0);
    r = r.add({transition("apply",  mk_ext_action(parse_apply))}, x0);
    r = r.add({transition("rename", mk_ext_action(parse_rename))}, x0);
    r = r.add({transition("intros", mk_ext_action(parse_intros))}, x0);
}

void initialize_builtin_tactics() {
}

void finalize_builtin_tactics() {
}
}
