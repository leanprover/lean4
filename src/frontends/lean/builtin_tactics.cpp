/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/tactic/let_tactic.h"
#include "library/tactic/generalize_tactic.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/parse_rewrite_tactic.h"
#include "frontends/lean/parse_with_options_tactic.h"
#include "frontends/lean/parse_simp_tactic.h"

namespace lean {
namespace notation {
static expr parse_rewrite_tactic_expr(parser & p, unsigned, expr const *, pos_info const & pos) {
    return p.save_pos(parse_rewrite_tactic(p), pos);
}

static expr parse_xrewrite_tactic_expr(parser & p, unsigned, expr const *, pos_info const & pos) {
    return p.save_pos(parse_xrewrite_tactic(p), pos);
}

static expr parse_krewrite_tactic_expr(parser & p, unsigned, expr const *, pos_info const & pos) {
    return p.save_pos(parse_krewrite_tactic(p), pos);
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
    expr value = p.parse_tactic_expr_arg();
    return p.save_pos(mk_let_tactic_expr(id, value), pos);
}

static expr parse_with_options_tactic_expr(parser & p, unsigned, expr const *, pos_info const & pos) {
    return p.save_pos(parse_with_options_tactic(p), pos);
}

static expr parse_simp_tactic_expr(parser & p, unsigned, expr const *, pos_info const & pos) {
    return p.save_pos(parse_simp_tactic(p), pos);
}

static expr parse_generalize_tactic(parser & p, unsigned, expr const *, pos_info const & pos) {
    expr e = p.parse_tactic_expr_arg();
    name id;
    if (p.curr_is_token(get_as_tk())) {
        p.next();
        id = p.check_atomic_id_next("invalid 'generalize' tactic, identifier expected");
    } else {
        if (is_constant(e))
            id = const_name(e);
        else if (is_local(e))
            id = local_pp_name(e);
        else
            id = name("x");
    }
    return p.save_pos(mk_generalize_tactic_expr(e, id), pos);
}

parse_table init_tactic_nud_table() {
    action Expr(mk_expr_action());
    expr x0 = mk_var(0);
    parse_table r;
    r = r.add({transition("(", Expr), transition(")", mk_ext_action(parse_rparen))}, x0);
    r = r.add({transition("rewrite",      mk_ext_action(parse_rewrite_tactic_expr))}, x0);
    r = r.add({transition("krewrite",     mk_ext_action(parse_krewrite_tactic_expr))}, x0);
    r = r.add({transition("xrewrite",     mk_ext_action(parse_xrewrite_tactic_expr))}, x0);
    r = r.add({transition("esimp",        mk_ext_action(parse_esimp_tactic_expr))}, x0);
    r = r.add({transition("generalize",   mk_ext_action(parse_generalize_tactic))}, x0);
    r = r.add({transition("unfold",       mk_ext_action(parse_unfold_tactic_expr))}, x0);
    r = r.add({transition("fold",         mk_ext_action(parse_fold_tactic_expr))}, x0);
    r = r.add({transition("let",          mk_ext_action(parse_let_tactic))}, x0);
    r = r.add({transition("with_options", mk_ext_action(parse_with_options_tactic_expr))}, x0);
    r = r.add({transition("simp",         mk_ext_action(parse_simp_tactic_expr))}, x0);
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
