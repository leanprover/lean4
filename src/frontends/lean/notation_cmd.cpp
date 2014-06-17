/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <limits>
#include <string>
#include "kernel/abstract.h"
#include "frontends/lean/parser.h"

namespace lean {
static name g_max("max");
static name g_colon(":");
static name g_comma(",");
static name g_assign(":=");
static name g_lparen("(");
static name g_rparen(")");
static name g_scoped("scoped");
static name g_foldr("foldr");
static name g_foldl("foldl");
static name g_binder("binder");
static name g_binders("binders");
static name g_infix("infix");
static name g_infixl("infixl");
static name g_infixr("infixr");
static name g_postfix("postfix");
static name g_notation("notation");

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
using notation::mk_binder_action;
using notation::mk_binders_action;
using notation::mk_exprs_action;
using notation::mk_scoped_expr_action;
using notation::mk_skip_action;
using notation::transition;
using notation::action;

static std::pair<notation_entry, optional<token_entry>> parse_mixfix_notation(parser & p, mixfix_kind k, bool overload) {
    std::string tk = parse_symbol(p, "invalid notation declaration, quoted symbol or identifier expected");
    optional<unsigned> prec = parse_optional_precedence(p);
    environment const & env = p.env();
    optional<token_entry> new_token;
    if (!prec) {
        prec = get_precedence(get_token_table(env), tk.c_str());
    } else if (prec != get_precedence(get_token_table(env), tk.c_str())) {
        new_token = token_entry(tk.c_str(), *prec);
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
        return mk_pair(notation_entry(false, list<transition>(transition(tks, mk_expr_action(*prec))),
                                      mk_app(f, Var(1), Var(0)), overload),
                       new_token);
    case mixfix_kind::infixr:
        return mk_pair(notation_entry(false, list<transition>(transition(tks, mk_expr_action(*prec-1))),
                                      mk_app(f, Var(1), Var(0)), overload),
                       new_token);
    case mixfix_kind::postfix:
        return mk_pair(notation_entry(false, list<transition>(transition(tks, mk_skip_action())),
                                      mk_app(f, Var(0)), overload),
                       new_token);
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

static notation_entry parse_mixfix_notation(parser & p, mixfix_kind k, bool overload, buffer<token_entry> & new_tokens) {
    auto nt = parse_mixfix_notation(p, k, overload);
    if (nt.second)
        new_tokens.push_back(*nt.second);
    return nt.first;
}

static environment mixfix_cmd(parser & p, mixfix_kind k, bool overload) {
    auto nt = parse_mixfix_notation(p, k, overload);
    environment env = p.env();
    if (nt.second)
        env = add_token(env, *nt.second);
    env = add_notation(env, nt.first);
    return env;
}

environment infixl_cmd_core(parser & p, bool overload) { return mixfix_cmd(p, mixfix_kind::infixl, overload); }
environment infixr_cmd_core(parser & p, bool overload) { return mixfix_cmd(p, mixfix_kind::infixr, overload); }
environment postfix_cmd_core(parser & p, bool overload) { return mixfix_cmd(p, mixfix_kind::postfix, overload); }

static name parse_quoted_symbol(parser & p, buffer<token_entry> & new_tokens) {
    if (p.curr_is_quoted_symbol()) {
        environment const & env = p.env();
        auto tk   = p.get_name_val();
        auto tks  = tk.to_string();
        auto tkcs = tks.c_str();
        p.next();
        if (p.curr_is_token(g_colon)) {
            p.next();
            unsigned prec = parse_precedence(p, "invalid notation declaration, precedence (small numeral) expected");
            auto old_prec = get_precedence(get_token_table(env), tkcs);
            if (!old_prec || prec != *old_prec)
                new_tokens.push_back(token_entry(tkcs, prec));
        } else if (!get_precedence(get_token_table(env), tkcs)) {
            new_tokens.push_back(token_entry(tkcs, 0));
        }
        return tk;
    } else {
        throw parser_error("invalid notation declaration, quoted symbol expected", p.pos());
    }
}

static expr parse_notation_expr(parser & p, buffer<expr> const & locals) {
    expr r = p.parse_expr();
    return abstract(r, locals.size(), locals.data());
}

static expr g_local_type = Bool; // type used in notation local declarations, it is irrelevant

static void parse_notation_local(parser & p, buffer<expr> & locals) {
    if (p.curr_is_identifier()) {
        name n = p.get_name_val();
        p.next();
        expr l = mk_local(n, g_local_type); // remark: the type doesn't matter
        p.add_local_expr(n, l);
        locals.push_back(l);
    } else {
        throw parser_error("invalid notation declaration, identifier expected", p.pos());
    }
}

static action parse_action(parser & p, buffer<expr> & locals, buffer<token_entry> & new_tokens) {
    if (p.curr_is_token(g_colon)) {
        p.next();
        if (p.curr_is_numeral()) {
            unsigned prec = parse_precedence(p, "invalid notation declaration, small numeral expected");
            return mk_expr_action(prec);
        } else if (p.curr_is_token_or_id(g_scoped)) {
            p.next();
            return mk_scoped_expr_action(mk_var(0));
        } else {
            p.check_token_next(g_lparen, "invalid notation declaration, '(', numeral or 'scoped' expected");
            if (p.curr_is_token_or_id(g_foldl) || p.curr_is_token_or_id(g_foldr)) {
                bool is_fold_right = p.curr_is_token_or_id(g_foldr);
                p.next();
                auto prec = parse_optional_precedence(p);
                name sep  = parse_quoted_symbol(p, new_tokens);
                expr rec;
                {
                    parser::local_scope scope(p);
                    p.check_token_next(g_lparen, "invalid fold notation argument, '(' expected");
                    parse_notation_local(p, locals);
                    parse_notation_local(p, locals);
                    p.check_token_next(g_comma,  "invalid fold notation argument, ',' expected");
                    rec  = parse_notation_expr(p, locals);
                    p.check_token_next(g_rparen, "invalid fold notation argument, ')' expected");
                    locals.pop_back();
                    locals.pop_back();
                }
                expr ini  = parse_notation_expr(p, locals);
                p.check_token_next(g_rparen, "invalid fold notation argument, ')' expected");
                return mk_exprs_action(sep, rec, ini, is_fold_right, prec ? *prec : 0);
            } else if (p.curr_is_token_or_id(g_scoped)) {
                p.next();
                auto prec = parse_optional_precedence(p);
                expr rec;
                {
                    parser::local_scope scope(p);
                    parse_notation_local(p, locals);
                    p.check_token_next(g_comma,  "invalid scoped notation argument, ',' expected");
                    rec  = parse_notation_expr(p, locals);
                    locals.pop_back();
                }
                p.check_token_next(g_rparen, "invalid scoped notation argument, ')' expected");
                return mk_scoped_expr_action(rec, prec ? *prec : 0);
            } else {
                throw parser_error("invalid notation declaration, 'foldl', 'foldr' or 'scoped' expected", p.pos());
            }
        }
    } else {
        return mk_expr_action();
    }
}

notation_entry parse_notation_core(parser & p, bool overload, buffer<token_entry> & new_tokens) {
    buffer<expr>       locals;
    buffer<transition> ts;
    parser::local_scope scope(p);
    bool is_nud = true;
    if (p.curr_is_identifier()) {
        parse_notation_local(p, locals);
        is_nud = false;
    }
    while (!p.curr_is_token(g_assign)) {
        name tk = parse_quoted_symbol(p, new_tokens);
        if (p.curr_is_quoted_symbol() || p.curr_is_token(g_assign)) {
            ts.push_back(transition(tk, mk_skip_action()));
        } else if (p.curr_is_token_or_id(g_binder)) {
            p.next();
            ts.push_back(transition(tk, mk_binder_action()));
        } else if (p.curr_is_token_or_id(g_binders)) {
            p.next();
            ts.push_back(transition(tk, mk_binders_action()));
        } else if (p.curr_is_identifier()) {
            name n   = p.get_name_val();
            p.next();
            action a = parse_action(p, locals, new_tokens);
            expr l = mk_local(n, g_local_type);
            p.add_local_expr(n, l);
            locals.push_back(l);
            ts.push_back(transition(tk, a));
        } else {
            throw parser_error("invalid notation declaration, quoted-symbol, identifier, 'binder', 'binders' expected", p.pos());
        }
    }
    p.next();
    if (ts.empty())
        throw parser_error("invalid notation declaration, empty notation is not allowed", p.pos());
    expr n = parse_notation_expr(p, locals);
    return notation_entry(is_nud, to_list(ts.begin(), ts.end()), n, overload);
}

environment notation_cmd_core(parser & p, bool overload) {
    environment env = p.env();
    buffer<token_entry> new_tokens;
    auto ne = parse_notation_core(p, overload, new_tokens);
    for (auto const & te : new_tokens)
        env = add_token(env, te);
    env = add_notation(env, ne);
    return env;
}

bool curr_is_notation_decl(parser & p) {
    return p.curr_is_token(g_infix) || p.curr_is_token(g_infixl) || p.curr_is_token(g_infixr) ||
        p.curr_is_token(g_postfix) || p.curr_is_token(g_notation);
}

notation_entry parse_notation(parser & p, bool overload, buffer<token_entry> & new_tokens) {
    if (p.curr_is_token(g_infix) || p.curr_is_token(g_infixl)) {
        p.next();
        return parse_mixfix_notation(p, mixfix_kind::infixl, overload, new_tokens);
    } else if (p.curr_is_token(g_infixr)) {
        p.next();
        return parse_mixfix_notation(p, mixfix_kind::infixr, overload, new_tokens);
    } else if (p.curr_is_token(g_postfix)) {
        p.next();
        return parse_mixfix_notation(p, mixfix_kind::postfix, overload, new_tokens);
    } else if (p.curr_is_token(g_notation)) {
        p.next();
        return parse_notation_core(p, overload, new_tokens);
    } else {
        throw parser_error("invalid notation, 'infix', 'infixl', 'infixr', 'postfix' or 'notation' expected", p.pos());
    }
}
}
