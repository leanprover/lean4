/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/tactic/let_tactic.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/parse_rewrite_tactic.h"

namespace lean {
namespace notation {
static expr parse_rewrite_tactic_expr(parser & p, unsigned, expr const *, pos_info const & pos) {
    return p.save_pos(parse_rewrite_tactic(p), pos);
}

static expr parse_esimp_tactic_expr(parser & p, unsigned, expr const *, pos_info const & pos) {
    return p.save_pos(parse_esimp_tactic(p), pos);
}

static expr parse_unfold_tactic_expr(parser & p, unsigned, expr const *, pos_info const & pos) {
    return p.save_pos(parse_unfold_tactic(p), pos);
}

static expr parse_fold_tactic_expr(parser & p, unsigned, expr const *, pos_info const & pos) {
    return p.save_pos(parse_fold_tactic(p), pos);
}

static expr parse_rparen(parser &, unsigned, expr const * args, pos_info const &) {
    return args[0];
}

static expr parse_let_tactic(parser & p, unsigned, expr const *, pos_info const & pos) {
    name id    = p.check_atomic_id_next("invalid 'let' tactic, identifier expected");
    p.check_token_next(get_assign_tk(), "invalid 'let' tactic, ':=' expected");
    expr value = p.parse_expr();
    return p.save_pos(mk_let_tactic_expr(id, value), pos);
}

parse_table init_tactic_nud_table() {
    action Expr(mk_expr_action());
    expr x0 = mk_var(0);
    parse_table r;
    r = r.add({transition("(", Expr), transition(")", mk_ext_action(parse_rparen))}, x0);
    r = r.add({transition("rewrite", mk_ext_action(parse_rewrite_tactic_expr))}, x0);
    r = r.add({transition("esimp",   mk_ext_action(parse_esimp_tactic_expr))}, x0);
    r = r.add({transition("unfold",  mk_ext_action(parse_unfold_tactic_expr))}, x0);
    r = r.add({transition("fold",    mk_ext_action(parse_fold_tactic_expr))}, x0);
    r = r.add({transition("let",    mk_ext_action(parse_let_tactic))}, x0);
    return r;
}

parse_table init_tactic_led_table() {
    parse_table r(false);
    return r;
}
}

static parse_table * g_nud_table = nullptr;
static parse_table * g_led_table = nullptr;

parse_table get_builtin_tactic_nud_table() {
    return *g_nud_table;
}

parse_table get_builtin_tactic_led_table() {
    return *g_led_table;
}

void initialize_builtin_tactics() {
    g_nud_table             = new parse_table();
    *g_nud_table            = notation::init_tactic_nud_table();
    g_led_table             = new parse_table();
    *g_led_table            = notation::init_tactic_led_table();
}

void finalize_builtin_tactics() {
    delete g_led_table;
    delete g_nud_table;
}
}
