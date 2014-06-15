/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <limits>
#include <string>
#include "frontends/lean/parser.h"

namespace lean {
static name g_max("max");
static name g_colon(":");
static name g_assign(":=");

static std::string parse_symbol(parser & p, char const * msg) {
    name n;
    if (p.curr_is_identifier() || p.curr_is_quoted_symbol()) {
        n = p.get_name_val();
    } else if (p.curr_is_keyword()) {
        n = p.get_token_info().value();
    } else {
        throw parser_error(msg, p.pos());
    }
    p.next();
    return n.to_string();
}

static optional<unsigned> parse_optional_precedence(parser & p) {
    if (p.curr_is_numeral()) {
        return optional<unsigned>(p.parse_small_nat());
    } else if (p.curr_is_token_or_id(g_max)) {
        p.next();
        return optional<unsigned>(std::numeric_limits<unsigned>::max());
    } else {
        return optional<unsigned>();
    }
}

static unsigned parse_precedence(parser & p, char const * msg) {
    auto r = parse_optional_precedence(p);
    if (!r)
        throw parser_error(msg, p.pos());
    return *r;
}

environment precedence_cmd(parser & p) {
    std::string tk = parse_symbol(p, "invalid precedence declaration, quoted symbol or identifier expected");
    p.check_token_next(g_colon, "invalid precedence declaration, ':' expected");
    unsigned prec = parse_precedence(p, "invalid precedence declaration, numeral or 'max' expected");
    return add_token(p.env(), tk.c_str(), prec);
}

enum class mixfix_kind { infixl, infixr, postfix };

using notation::mk_expr_action;
using notation::mk_skip_action;
using notation::transition;

environment mixfix_cmd(parser & p, mixfix_kind k) {
    std::string tk = parse_symbol(p, "invalid notation declaration, quoted symbol or identifier expected");
    optional<unsigned> prec = parse_optional_precedence(p);
    environment env = p.env();
    if (!prec) {
        prec = get_precedence(get_token_table(env), tk.c_str());
    } else if (prec != get_precedence(get_token_table(env), tk.c_str())) {
        env = add_token(env, tk.c_str(), *prec);
    }

    if (!prec)
        throw parser_error("invalid notation declaration, precedence was not provided, and it is not set for the given symbol, "
                           "solution: use the 'precedence' command", p.pos());
    if (k == mixfix_kind::infixr && *prec == 0)
        throw parser_error("invalid infixr declaration, precedence must be greater than zero", p.pos());
    p.check_token_next(g_assign, "invalid notation declaration, ':=' expected");
    expr f = p.parse_expr();
    char const * tks = tk.c_str();
    switch (k) {
    case mixfix_kind::infixl:
        return add_led_notation(env, {transition(tks, mk_expr_action(*prec))}, mk_app(f, Var(0), Var(1)));
    case mixfix_kind::infixr:
        return add_led_notation(env, {transition(tks, mk_expr_action(*prec-1))}, mk_app(f, Var(0), Var(1)));
    case mixfix_kind::postfix:
        return add_led_notation(env, {transition(tks, mk_skip_action())}, mk_app(f, Var(0)));
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

environment infixl_cmd(parser & p) { return mixfix_cmd(p, mixfix_kind::infixl); }
environment infixr_cmd(parser & p) { return mixfix_cmd(p, mixfix_kind::infixr); }
environment postfix_cmd(parser & p) { return mixfix_cmd(p, mixfix_kind::postfix); }

environment notation_cmd(parser & p) {
    // TODO(Leo)
    return p.env();
}
}
