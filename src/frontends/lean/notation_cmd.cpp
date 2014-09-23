/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <limits>
#include <string>
#include "util/sstream.h"
#include "kernel/abstract.h"
#include "kernel/replace_fn.h"
#include "library/scoped_ext.h"
#include "library/explicit.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/tokens.h"

namespace lean {
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
    } else if (p.curr_is_token_or_id(get_max_tk())) {
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
    p.check_token_next(get_colon_tk(), "invalid precedence declaration, ':' expected");
    unsigned prec = parse_precedence(p, "invalid precedence declaration, numeral or 'max' expected");
    return add_token(p.env(), tk.c_str(), prec);
}

/** \brief Auxiliary function for #cleanup_section_notation. */
expr cleanup_section_notation_core(parser & p, expr const & e) {
    if (is_implicit(e)) {
        return cleanup_section_notation_core(p, get_implicit_arg(e));
    } else if (is_explicit(e)) {
        return cleanup_section_notation_core(p, get_explicit_arg(e));
    } else if (is_app(e)) {
        buffer<expr> args;
        expr const & f = get_app_args(e, args);
        for (expr arg : args) {
            if (!is_explicit(arg))
                throw parser_error("unexpected expression in (section) notation", p.pos_of(arg));
            arg = get_explicit_arg(arg);
            if (!is_local(arg))
                throw parser_error("unexpected expression in (section) notation", p.pos_of(arg));
            binder_info bi = local_info(arg);
            if (!bi.is_strict_implicit() && !bi.is_implicit())
                throw parser_error(sstream() << "invalid occurrence of local parameter '" << local_pp_name(arg)
                                   << "' in (section) notation that is not implicit", p.pos_of(e));
        }
        return cleanup_section_notation_core(p, f);
    } else if (is_constant(e)) {
        return p.save_pos(mk_constant(const_name(e)), p.pos_of(e));
    } else if (is_local(e)) {
        throw parser_error(sstream() << "invalid occurrence of local parameter '" << local_pp_name(e)
                           << "' in (section) notation", p.pos_of(e));
    } else {
        throw parser_error("unexpected expression in (section) notation", p.pos_of(e));
    }
}

/** \brief Replace reference to implicit section local constants and universes with placeholders.

    \remark Throws an exception if \c e contains a local constant that is not implicit.
*/
expr cleanup_section_notation(parser & p, expr const & e) {
    if (!in_section(p.env()))
        return e;
    return replace(e, [&](expr const & e) {
            if (is_local(e))
                throw parser_error(sstream() << "invalid occurrence of local parameter '" << local_pp_name(e)
                                   << "' in (section) notation", p.pos_of(e));
            if (is_implicit(e))
                return some_expr(cleanup_section_notation_core(p, e));
            return none_expr();
        });
}

enum class mixfix_kind { infixl, infixr, postfix, prefix };

using notation::mk_expr_action;
using notation::mk_binder_action;
using notation::mk_binders_action;
using notation::mk_exprs_action;
using notation::mk_scoped_expr_action;
using notation::mk_skip_action;
using notation::mk_ext_lua_action;
using notation::transition;
using notation::action;

static pair<notation_entry, optional<token_entry>> parse_mixfix_notation(parser & p, mixfix_kind k, bool overload) {
    std::string tk = parse_symbol(p, "invalid notation declaration, quoted symbol or identifier expected");
    optional<unsigned> prec;
    if (p.curr_is_token(get_colon_tk())) {
        p.next();
        prec = parse_precedence(p, "invalid notation declaration, numeral or 'max' expected");
    }
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
    p.check_token_next(get_assign_tk(), "invalid notation declaration, ':=' expected");
    expr f = cleanup_section_notation(p, p.parse_expr());
    char const * tks = tk.c_str();
    switch (k) {
    case mixfix_kind::infixl:
        return mk_pair(notation_entry(false, to_list(transition(tks, mk_expr_action(*prec))), mk_app(f, Var(1), Var(0)), overload), new_token);
    case mixfix_kind::infixr:
        return mk_pair(notation_entry(false, to_list(transition(tks, mk_expr_action(*prec-1))), mk_app(f, Var(1), Var(0)), overload), new_token);
    case mixfix_kind::postfix:
        return mk_pair(notation_entry(false, to_list(transition(tks, mk_skip_action())), mk_app(f, Var(0)), overload), new_token);
    case mixfix_kind::prefix:
        return mk_pair(notation_entry(true, to_list(transition(tks, mk_expr_action(*prec))), mk_app(f, Var(0)), overload), new_token);
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
environment prefix_cmd_core(parser & p, bool overload) { return mixfix_cmd(p, mixfix_kind::prefix, overload); }

static name parse_quoted_symbol_or_token(parser & p, buffer<token_entry> & new_tokens) {
    if (p.curr_is_quoted_symbol()) {
        environment const & env = p.env();
        auto tk   = p.get_name_val();
        auto tks  = tk.to_string();
        auto tkcs = tks.c_str();
        p.next();
        if (p.curr_is_token(get_colon_tk())) {
            p.next();
            unsigned prec = parse_precedence(p, "invalid notation declaration, precedence (small numeral) expected");
            auto old_prec = get_precedence(get_token_table(env), tkcs);
            if (!old_prec || prec != *old_prec)
                new_tokens.push_back(token_entry(tkcs, prec));
        } else if (!get_precedence(get_token_table(env), tkcs)) {
            new_tokens.push_back(token_entry(tkcs, 0));
        }
        return tk;
    } else if (p.curr_is_keyword()) {
        auto tk = p.get_token_info().token();
        p.next();
        return tk;
    } else {
        throw parser_error("invalid notation declaration, symbol expected", p.pos());
    }
}

static expr parse_notation_expr(parser & p, buffer<expr> const & locals) {
    expr r = p.parse_expr();
    return cleanup_section_notation(p, abstract(r, locals.size(), locals.data()));
}

static void parse_notation_local(parser & p, buffer<expr> & locals) {
    if (p.curr_is_identifier()) {
        name n = p.get_name_val();
        p.next();
        expr local_type = mk_Prop(); // type used in notation local declarations, it is irrelevant
        expr l = mk_local(n, local_type); // remark: the type doesn't matter
        p.add_local_expr(n, l);
        locals.push_back(l);
    } else {
        throw parser_error("invalid notation declaration, identifier expected", p.pos());
    }
}

unsigned get_precedence(environment const & env, buffer<token_entry> const & new_tokens, name const & token) {
    std::string token_str = token.to_string();
    for (auto const & e : new_tokens) {
        if (e.m_token == token_str)
            return e.m_prec;
    }
    auto prec = get_precedence(get_token_table(env), token_str.c_str());
    if (prec)
        return *prec;
    else
        return 0;
}

static action parse_action(parser & p, name const & prev_token, unsigned default_prec, buffer<expr> & locals, buffer<token_entry> & new_tokens) {
    if (p.curr_is_token(get_colon_tk())) {
        p.next();
        if (p.curr_is_numeral() || p.curr_is_token_or_id(get_max_tk())) {
            unsigned prec = parse_precedence(p, "invalid notation declaration, small numeral expected");
            return mk_expr_action(prec);
        } else if (p.curr_is_token_or_id(get_prev_tk())) {
            p.next();
            return mk_expr_action(get_precedence(p.env(), new_tokens, prev_token));
        } else if (p.curr_is_string()) {
            std::string fn = p.get_str_val();
            p.next();
            return mk_ext_lua_action(fn.c_str());
        } else if (p.curr_is_token_or_id(get_scoped_tk())) {
            p.next();
            return mk_scoped_expr_action(mk_var(0));
        } else {
            p.check_token_next(get_lparen_tk(), "invalid notation declaration, '(', numeral or 'scoped' expected");
            if (p.curr_is_token_or_id(get_foldl_tk()) || p.curr_is_token_or_id(get_foldr_tk())) {
                bool is_fold_right = p.curr_is_token_or_id(get_foldr_tk());
                p.next();
                auto prec = parse_optional_precedence(p);
                name sep  = parse_quoted_symbol_or_token(p, new_tokens);
                expr rec;
                {
                    parser::local_scope scope(p);
                    p.check_token_next(get_lparen_tk(), "invalid fold notation argument, '(' expected");
                    parse_notation_local(p, locals);
                    parse_notation_local(p, locals);
                    p.check_token_next(get_comma_tk(),  "invalid fold notation argument, ',' expected");
                    rec  = parse_notation_expr(p, locals);
                    p.check_token_next(get_rparen_tk(), "invalid fold notation argument, ')' expected");
                    locals.pop_back();
                    locals.pop_back();
                }
                expr ini  = parse_notation_expr(p, locals);
                optional<name> terminator;
                if (!p.curr_is_token(get_rparen_tk()))
                    terminator = parse_quoted_symbol_or_token(p, new_tokens);
                p.check_token_next(get_rparen_tk(), "invalid fold notation argument, ')' expected");
                return mk_exprs_action(sep, rec, ini, terminator, is_fold_right, prec ? *prec : 0);
            } else if (p.curr_is_token_or_id(get_scoped_tk())) {
                p.next();
                auto prec = parse_optional_precedence(p);
                expr rec;
                {
                    parser::local_scope scope(p);
                    parse_notation_local(p, locals);
                    p.check_token_next(get_comma_tk(),  "invalid scoped notation argument, ',' expected");
                    rec  = parse_notation_expr(p, locals);
                    locals.pop_back();
                }
                p.check_token_next(get_rparen_tk(), "invalid scoped notation argument, ')' expected");
                return mk_scoped_expr_action(rec, prec ? *prec : 0);
            } else if (p.curr_is_token_or_id(get_call_tk())) {
                p.next();
                name fn = p.check_id_next("invalid call notation argument, identifier expected");
                p.check_token_next(get_rparen_tk(), "invalid call notation argument, ')' expected");
                return mk_ext_lua_action(fn.to_string().c_str());
            } else {
                throw parser_error("invalid notation declaration, 'foldl', 'foldr' or 'scoped' expected", p.pos());
            }
        }
    } else {
        return mk_expr_action(default_prec);
    }
}

/**
   \brief If the action for token \c tk in parse table \c pt is an Expr action,
   then return its precedence. We use this value as the default precedence
   when the user does not provide it. The idea is to minimize conflict with existing
   notation.
*/
unsigned get_default_prec(optional<parse_table> const & pt, name const & tk) {
    if (!pt)
        return 0;
    if (auto at = pt->find(tk)) {
        if (at->first.kind() == notation::action_kind::Expr)
            return at->first.rbp();
    }
    return 0;
}

notation_entry parse_notation_core(parser & p, bool overload, buffer<token_entry> & new_tokens) {
    buffer<expr>       locals;
    buffer<transition> ts;
    parser::local_scope scope(p);
    bool is_nud = true;
    optional<parse_table> pt;
    if (p.curr_is_identifier()) {
        parse_notation_local(p, locals);
        is_nud = false;
        pt = get_led_table(p.env());
    } else {
        pt = get_nud_table(p.env());
    }
    while (!p.curr_is_token(get_assign_tk())) {
        name tk = parse_quoted_symbol_or_token(p, new_tokens);
        if (p.curr_is_token_or_id(get_binder_tk())) {
            p.next();
            ts.push_back(transition(tk, mk_binder_action()));
        } else if (p.curr_is_token_or_id(get_binders_tk())) {
            p.next();
            ts.push_back(transition(tk, mk_binders_action()));
        } else if (p.curr_is_identifier()) {
            unsigned default_prec = get_default_prec(pt, tk);
            name n   = p.get_name_val();
            p.next();
            action a = parse_action(p, tk, default_prec, locals, new_tokens);
            expr local_type = mk_Prop(); // type used in notation local declarations, it is irrelevant
            expr l = mk_local(n, local_type);
            p.add_local_expr(n, l);
            locals.push_back(l);
            ts.push_back(transition(tk, a));
        } else if (p.curr_is_quoted_symbol() || p.curr_is_keyword() || p.curr_is_token(get_assign_tk())) {
            ts.push_back(transition(tk, mk_skip_action()));
        } else {
            throw parser_error("invalid notation declaration, quoted-symbol, identifier, 'binder', 'binders' expected", p.pos());
        }
        if (pt) {
            // new notation is still compatible with the existing one
            transition const & new_trans = ts.back();
            if (auto at = pt->find(new_trans.get_token())) {
                if (new_trans.get_action().is_equal(at->first)) {
                    pt = at->second;
                } else {
                    // new notation is not compatible with existing one
                    pt = optional<parse_table>();
                }
            } else {
                // parse table does not handle this prefix
                pt = optional<parse_table>();
            }
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
    return p.curr_is_token(get_infix_tk()) || p.curr_is_token(get_infixl_tk()) || p.curr_is_token(get_infixr_tk()) ||
        p.curr_is_token(get_postfix_tk()) || p.curr_is_token(get_prefix_tk()) || p.curr_is_token(get_notation_tk());
}

notation_entry parse_notation(parser & p, bool overload, buffer<token_entry> & new_tokens) {
    if (p.curr_is_token(get_infix_tk()) || p.curr_is_token(get_infixl_tk())) {
        p.next();
        return parse_mixfix_notation(p, mixfix_kind::infixl, overload, new_tokens);
    } else if (p.curr_is_token(get_infixr_tk())) {
        p.next();
        return parse_mixfix_notation(p, mixfix_kind::infixr, overload, new_tokens);
    } else if (p.curr_is_token(get_postfix_tk())) {
        p.next();
        return parse_mixfix_notation(p, mixfix_kind::postfix, overload, new_tokens);
    } else if (p.curr_is_token(get_prefix_tk())) {
        p.next();
        return parse_mixfix_notation(p, mixfix_kind::prefix, overload, new_tokens);
    } else if (p.curr_is_token(get_notation_tk())) {
        p.next();
        return parse_notation_core(p, overload, new_tokens);
    } else {
        throw parser_error("invalid notation, 'infix', 'infixl', 'infixr', 'prefix', 'postfix' or 'notation' expected", p.pos());
    }
}

environment notation_cmd(parser & p) { return notation_cmd_core(p, true); }
environment infixl_cmd(parser & p) { return infixl_cmd_core(p, true); }
environment infixr_cmd(parser & p) { return infixr_cmd_core(p, true); }
environment postfix_cmd(parser & p) { return postfix_cmd_core(p, true); }
environment prefix_cmd(parser & p) { return prefix_cmd_core(p, true); }

void register_notation_cmds(cmd_table & r) {
    add_cmd(r, cmd_info("precedence",   "set token left binding power", precedence_cmd));
    add_cmd(r, cmd_info("infixl",       "declare a new infix (left) notation", infixl_cmd));
    add_cmd(r, cmd_info("infix",        "declare a new infix (left) notation", infixl_cmd));
    add_cmd(r, cmd_info("infixr",       "declare a new infix (right) notation", infixr_cmd));
    add_cmd(r, cmd_info("postfix",      "declare a new postfix notation", postfix_cmd));
    add_cmd(r, cmd_info("prefix",       "declare a new prefix notation", prefix_cmd));
    add_cmd(r, cmd_info("notation",     "declare a new notation", notation_cmd));
}
}
