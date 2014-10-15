/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <limits>
#include "library/explicit.h"
#include "library/tactic/expr_to_tactic.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/parse_table.h"

namespace lean {
using notation::transition;
using notation::mk_ext_action;

static expr parse_apply(parser & p, unsigned, expr const *, pos_info const & pos) {
    parser::no_undef_id_error_scope scope(p);
    expr e = p.parse_expr(std::numeric_limits<unsigned>::max());
    return p.save_pos(mk_apply_tactic_macro(e), pos);
}

void init_nud_tactic_table(parse_table & r) {
    expr x0 = mk_var(0);
    r = r.add({transition("apply", mk_ext_action(parse_apply))}, x0);
}

void initialize_builtin_tactics() {
}

void finalize_builtin_tactics() {
}
}
