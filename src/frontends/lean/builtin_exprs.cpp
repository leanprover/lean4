/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <algorithm>
#include "library/export_decl.h"
#include "runtime/sstream.h"
#include "util/option_declarations.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "library/annotation.h"
#include "library/placeholder.h"
#include "library/explicit.h"
#include "library/aliases.h"
#include "library/constants.h"
#include "library/string.h"
#include "library/trace.h"
#include "library/compiler/borrowed_annotation.h"
#include "library/equations_compiler/equations.h"
#include "frontends/lean/builtin_exprs.h"
#include "frontends/lean/decl_cmds.h"
#include "frontends/lean/decl_util.h"
#include "frontends/lean/token_table.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/util.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/match_expr.h"
#include "frontends/lean/brackets.h"
#include "frontends/lean/elaborator.h"
#include "frontends/lean/typed_expr.h"
#include "frontends/lean/choice.h"

#ifndef LEAN_DEFAULT_PARSER_CHECKPOINT_HAVE
#define LEAN_DEFAULT_PARSER_CHECKPOINT_HAVE true
#endif

namespace lean {
static name * g_parser_checkpoint_have = nullptr;

bool get_parser_checkpoint_have(options const & opts) {
    return opts.get_bool(*g_parser_checkpoint_have, LEAN_DEFAULT_PARSER_CHECKPOINT_HAVE);
}

using namespace notation; // NOLINT

static name * g_no_universe_annotation = nullptr;

bool is_sort_wo_universe(expr const & e) {
    return is_annotation(e, *g_no_universe_annotation);
}

expr mk_sort_wo_universe(parser & p, pos_info const & pos, bool is_type) {
    expr r = p.save_pos(mk_sort(is_type ? mk_level_one() : mk_level_zero()), pos);
    return p.save_pos(mk_annotation(*g_no_universe_annotation, r), pos);
}

static expr parse_Type(parser & p, unsigned, expr const *, pos_info const & pos) {
    if (p.curr_is_token(get_llevel_curly_tk())) {
        p.next();
        level l = mk_succ(p.parse_level());
        p.check_token_next(get_rcurly_tk(), "invalid Type expression, '}' expected");
        return p.save_pos(mk_sort(l), pos);
    } else {
        return mk_sort_wo_universe(p, pos, true);
    }
}

static expr parse_Sort(parser & p, unsigned, expr const *, pos_info const & pos) {
    if (p.curr_is_token(get_llevel_curly_tk())) {
        p.next();
        level l = p.parse_level();
        p.check_token_next(get_rcurly_tk(), "invalid Sort expression, '}' expected");
        return p.save_pos(mk_sort(l), pos);
    } else {
        return mk_sort_wo_universe(p, pos, false);
    }
}

static expr parse_Type_star(parser & p, unsigned, expr const *, pos_info const & pos) {
    return p.save_pos(mk_sort(mk_succ(mk_level_placeholder())), pos);
}

static expr parse_Sort_star(parser & p, unsigned, expr const *, pos_info const & pos) {
    return p.save_pos(mk_sort(mk_level_placeholder()), pos);
}

static name * g_let_match_name = nullptr;

static expr parse_let(parser & p, pos_info const & pos, bool in_do_block);
static expr parse_do(parser & p, bool has_braces);
static expr parse_let_body(parser & p, pos_info const & pos, bool in_do_block) {
    if (in_do_block) {
        {
            if (p.curr_is_token(get_semicolon_tk())) {
                p.next();
            } else {
                p.check_token_next(get_semicolon_tk(), "invalid 'do' block 'let' declaration, ';' expected");
            }
            if (p.curr_is_token(get_let_tk())) {
                p.next();
                return parse_let(p, pos, in_do_block);
            } else {
                return parse_do(p, false);
            }
        }
    } else {
        if (p.curr_is_token(get_semicolon_tk())) {
            p.next();
            return p.parse_expr();
        } else {
            p.maybe_throw_error({"invalid let declaration, ';' expected", p.pos()});
            return p.parse_expr();
        }
    }
}

// Distribute mk_typed_expr over choice expression.
// see issue #768
static expr mk_typed_expr_distrib_choice(parser & p, expr const & type, expr const & value, pos_info const & pos) {
    if (is_choice(value)) {
        buffer<expr> new_choices;
        for (unsigned i = 0; i < get_num_choices(value); i++) {
            new_choices.push_back(mk_typed_expr_distrib_choice(p, type, get_choice(value, i), pos));
        }
        return p.save_pos(mk_choice(new_choices.size(), new_choices.data()), pos);
    } else {
        return p.save_pos(mk_typed_expr(type, value), pos);
    }
}

static expr parse_let(parser & p, pos_info const & pos, bool in_do_block) {
    parser::local_scope scope1(p);
    if (!in_do_block && p.parse_local_notation_decl()) {
        return parse_let_body(p, pos, in_do_block);
    } else if (p.curr_is_identifier()) {
        auto id_pos     = p.pos();
        name id         = p.check_atomic_id_next("invalid let declaration, atomic identifier expected");
        expr type;
        expr value;
        if (p.curr_is_token(get_assign_tk())) {
            p.next();
            type  = p.save_pos(mk_expr_placeholder(), id_pos);
            value = p.parse_expr();
        } else if (p.curr_is_token(get_colon_tk())) {
            p.next();
            type = p.parse_expr();
            p.check_token_next(get_assign_tk(), "invalid declaration, ':=' expected");
            value = p.parse_expr();
        } else {
            parser::local_scope scope2(p);
            buffer<expr> ps;
            unsigned rbp = 0;
            auto lenv = p.parse_binders(ps, rbp);
            if (p.curr_is_token(get_colon_tk())) {
                p.next();
                type  = p.parse_scoped_expr(ps, lenv);
                type  = Pi(ps, type, p);
            } else {
                type  = p.save_pos(mk_expr_placeholder(), id_pos);
            }
            p.check_token_next(get_assign_tk(), "invalid let declaration, ':=' expected");
            value = p.parse_scoped_expr(ps, lenv);
            value = Fun(ps, value, p);
        }
        expr x = mk_local(id, type);
        p.add_local_expr(id, p.save_pos(x, id_pos));
        expr b = parse_let_body(p, pos, in_do_block);
        return p.save_pos(mk_let(id, type, value, abstract(b, x)), pos);
    } else {
        buffer<expr> new_locals;
        expr lhs = p.parse_pattern(new_locals);
        expr type;
        if (p.curr_is_token(get_colon_tk())) {
            p.next();
            type = mk_pi("a", p.parse_expr(), mk_expr_placeholder());
        } else {
            type = mk_expr_placeholder();
        }
        p.check_token_next(get_assign_tk(), "invalid let declaration, ':=' expected");
        expr value = p.parse_expr();
        for (expr const & l : new_locals)
            p.add_local(l);
        expr body  = parse_let_body(p, pos, in_do_block);
        match_definition_scope match_scope(p.env());
        expr fn = p.save_pos(mk_local(p.next_name(), *g_let_match_name, type, mk_rec_info()), pos);
        expr eqn = Fun(fn, Fun(new_locals, p.save_pos(mk_equation(p.rec_save_pos(mk_app(fn, lhs), pos), body), pos), p), p);
        equations_header h = mk_match_header(match_scope.get_name(), match_scope.get_actual_name());
        expr eqns  = p.save_pos(mk_equations(h, 1, &eqn), pos);
        expr e = mk_app(eqns, value);
        return p.save_pos(e, pos);
    }
}

static expr parse_let_expr(parser & p, unsigned, expr const *, pos_info const & pos) {
    bool in_do_block = false;
    return parse_let(p, pos, in_do_block);
}

static name * g_do_match_name = nullptr;

static std::tuple<optional<expr>, expr, expr, optional<expr>> parse_do_action(parser & p, buffer<expr> & new_locals) {
    auto lhs_pos = p.pos();
    optional<expr> lhs = some(p.parse_pattern_or_expr());
    expr type, curr;
    optional<expr> else_case;
    if (p.curr_is_token(get_colon_tk())) {
        p.next();
        type = p.parse_expr();
        if (is_placeholder(unwrap_pos(*lhs))) {
            lhs = mk_local("_x", type);
        }
        if (!is_local(unwrap_pos(*lhs))) {
            p.maybe_throw_error({"invalid 'do' block, unexpected ':' the left hand side is a pattern", lhs_pos});
            lhs = mk_local("_x", type);
        }
        lhs = p.save_pos(mk_local(local_pp_name_p(*lhs), type), lhs_pos);
        new_locals.clear();
        new_locals.push_back(*lhs);
        p.check_token_next(get_larrow_tk(), "invalid 'do' block, '←' expected");
        curr = p.parse_expr();
    } else if (p.curr_is_token(get_larrow_tk())) {
        p.next();
        type = p.save_pos(mk_expr_placeholder(), lhs_pos);
        bool skip_main_fn = false;
        lhs = p.patexpr_to_pattern(*lhs, skip_main_fn, new_locals);
        curr = p.parse_expr();
        if (p.curr_is_token(get_bar_tk())) {
            p.next();
            else_case = p.parse_expr();
        }
    } else {
        curr = p.patexpr_to_expr(*lhs);
        type = p.save_pos(mk_expr_placeholder(), lhs_pos);
        lhs  = none_expr();
    }
    return std::make_tuple(lhs, type, curr, else_case);
}

static expr mk_bind_fn(parser & p) {
    return mk_no_info(p.id_to_expr("bind", pos_info {}, /* resolve_only */ true));
}

static name * g_do_failure_eq = nullptr;

/* Mark for automatic failure equation when pattern matching in do-expressions. */
expr mark_do_failure_eq(expr const & e) {
    return mk_annotation(*g_do_failure_eq, e);
}

bool is_do_failure_eq(expr const & e) {
    auto it = e;
    while (is_lambda(it))
        it = binding_body(it);
    if (!is_equation(it)) return false;
    return is_annotation(equation_rhs(it), *g_do_failure_eq);
}

static expr parse_do(parser & p, bool has_braces) {
    parser::local_scope scope(p);
    buffer<expr>               es;
    buffer<pos_info>           ps;
    buffer<optional<expr>>     lhss;
    buffer<optional<expr>>     else_cases;
    buffer<list<expr>>         lhss_locals;
    while (true) {
        if (p.curr_is_token(get_let_tk())) {
            auto pos = p.pos();
            p.next();
            bool in_do_block = true;
            es.push_back(parse_let(p, pos, in_do_block));
            break;
        } else {
            auto lhs_pos = p.pos();
            ps.push_back(lhs_pos);
            buffer<expr> new_locals;
            optional<expr> lhs, else_case;
            expr type, curr;
            std::tie(lhs, type, curr, else_case) = parse_do_action(p, new_locals);
            es.push_back(curr);
            if (/* p.curr_is_token(get_comma_tk()) || */ p.curr_is_token(get_semicolon_tk())) {
                p.next();
                for (expr const & l : new_locals)
                    p.add_local(l);
                if (lhs && !is_local(*lhs)) {
                    // if lhs is a pattern, we need to save the locals to create the match
                    lhss_locals.push_back(to_list(new_locals));
                } else {
                    lhss_locals.push_back(list<expr>());
                }
                lhss.push_back(lhs);
                else_cases.push_back(else_case);
            } else {
                if (lhs) {
                    p.maybe_throw_error({"the last statement in a 'do' block must be an expression", lhs_pos});
                }
                break;
            }
        }
    }
    if (has_braces) {
        p.check_token_next(get_rcurly_tk(), "invalid 'do' block, '}' expected");
    }
    lean_assert(!es.empty());
    lean_assert(es.size() == lhss.size() + 1);
    if (es.size() == 1)
        return es[0];
    unsigned i = es.size();
    --i;
    expr r = es[i];
    while (i > 0) {
        --i;
        if (auto lhs = lhss[i]) {
            if (is_local_p(*lhs)) {
                r = p.rec_save_pos(mk_app(p.save_pos(mk_bind_fn(p), ps[i]), es[i], Fun(*lhs, r, p)), ps[i]);
            } else {
                // must introduce a "fake" match
                auto pos   = ps[i];
                match_definition_scope match_scope(p.env());
                expr fn = p.save_pos(mk_local(p.next_name(), *g_do_match_name, mk_expr_placeholder(), mk_rec_info()), pos);
                buffer<expr> locals;
                to_buffer(lhss_locals[i], locals);
                buffer<expr> eqs;
                eqs.push_back(Fun(fn, Fun(locals, p.save_pos(mk_equation(p.rec_save_pos(mk_app(fn, *lhs), pos), r), pos), p), p));
                expr else_case;
                bool ignore_if_unused;
                if (optional<expr> r = else_cases[i]) {
                    else_case        = *r;
                    ignore_if_unused = false;
                } else {
                    else_case        = p.save_pos(mark_do_failure_eq(p.save_pos(mk_constant(get_match_failed_name()), pos)), pos);
                    ignore_if_unused = true;
                }
                // add case
                //    _ := else_case
                expr x = mk_local(p.next_name(), "_x", mk_expr_placeholder(), mk_binder_info());
                expr else_eq = Fun(fn, Fun(x, p.save_pos(mk_equation(p.rec_save_pos(mk_app(fn, x), pos),
                                                                     else_case,
                                                                     ignore_if_unused),
                                                         pos), p), p);
                eqs.push_back(else_eq);
                equations_header h = mk_match_header(match_scope.get_name(), match_scope.get_actual_name());
                expr eqns  = p.save_pos(mk_equations(h, eqs.size(), eqs.data()), pos);
                expr local = mk_local("_p", mk_expr_placeholder());
                expr match = p.mk_app(eqns, local, pos);
                r = p.rec_save_pos(mk_app(p.save_pos(mk_bind_fn(p), ps[i]),
                                          es[i],
                                          p.save_pos(Fun(local, match, p), pos)),
                                   pos);
            }
        } else {
            r = p.rec_save_pos(mk_app(p.save_pos(mk_bind_fn(p), ps[i]),
                                      es[i],
                                      p.save_pos(mk_lambda("_x", mk_expr_placeholder(), r), p.pos_of(r))),
                               ps[i]);
        }
    }
    return r;
}

static expr parse_do_expr(parser & p, unsigned, expr const *, pos_info const &) {
    bool has_braces = false;
    if (p.curr_is_token(get_lcurly_tk())) {
        has_braces = true;
        p.next();
    }
    return parse_do(p, has_braces);
}

static expr parse_unit(parser & p, unsigned, expr const *, pos_info const & pos) {
    return p.save_pos(mk_constant(get_unit_unit_name()), pos);
}

static expr parse_proof(parser & p);

static expr parse_proof(parser & p) {
    if (p.curr_is_token(get_from_tk())) {
        // parse: 'from' expr
        p.next();
        return p.parse_expr();
    } else {
        return p.parser_error_or_expr({"invalid expression, 'from' expected", p.pos()});
    }
}

static expr parse_have(parser & p, unsigned, expr const *, pos_info const & pos) {
    auto id_pos       = p.pos();
    name id;
    expr prop;
    if (p.curr_is_identifier()) {
        id = p.get_name_val();
        p.next();
        if (p.curr_is_token(get_colon_tk())) {
            p.next();
            prop      = p.parse_expr();
        } else {
            expr left = p.id_to_expr(id, id_pos);
            id        = get_this_tk();
            unsigned rbp = 0;
            while (rbp < p.curr_lbp()) {
                left = p.parse_led(left);
            }
            prop      = left;
        }
    } else {
        id            = get_this_tk();
        prop          = p.parse_expr();
    }
    expr proof;
    if (p.curr_is_token(get_assign_tk())) {
        p.next();
        proof = p.parse_expr();
    } else {
        proof = parse_proof(p);
    }
    p.check_token_next(get_semicolon_tk(), "invalid 'have' declaration, ';' expected");
    parser::local_scope scope(p);
    expr l = p.save_pos(mk_local(id, prop), pos);
    p.add_local(l);
    expr body = p.parse_expr();
    body = abstract(body, unwrap_pos(l));
    if (get_parser_checkpoint_have(p.get_options()))
        body = mk_checkpoint_annotation(body);
    expr r = p.save_pos(mk_have_annotation(p.save_pos(mk_lambda(id, prop, body), pos)), pos);
    return p.mk_app(r, proof, pos);
}

static expr parse_show(parser & p, unsigned, expr const *, pos_info const & pos) {
    expr prop  = p.parse_expr();
    expr proof = parse_proof(p);
    expr b = p.save_pos(mk_lambda(get_this_tk(), prop, mk_bvar(0)), pos);
    expr r = p.mk_app(b, proof, pos);
    return p.save_pos(mk_show_annotation(r), pos);
}

static expr parse_suffices(parser & p, unsigned, expr const *, pos_info const & pos) {
    auto prop_pos = p.pos();
    name id;
    expr from;
    if (p.curr_is_identifier()) {
        id = p.get_name_val();
        p.next();
        if (p.curr_is_token(get_colon_tk())) {
            p.next();
            from = p.parse_expr();
        } else {
            expr left = p.id_to_expr(id, prop_pos);
            id        = get_this_tk();
            unsigned rbp = 0;
            while (rbp < p.curr_lbp()) {
                left = p.parse_led(left);
            }
            from = left;
        }
    } else {
        id    = get_this_tk();
        from  = p.parse_expr();
    }
    expr local = p.save_pos(mk_local(id, from), prop_pos);
    expr body;
    {
        parser::local_scope scope(p);
        p.add_local(local);
        body = parse_proof(p);
    }
    expr proof = p.save_pos(Fun(local, body, p), pos);
    p.check_token_next(get_semicolon_tk(), "invalid 'suffices' declaration, ';' expected");
    expr rest  = p.parse_expr();
    expr r = p.mk_app(proof, rest, pos);
    return p.save_pos(mk_suffices_annotation(r), pos);
}

static expr * g_not  = nullptr;
static unsigned g_then_else_prec = 0;

static expr parse_ite(parser & p, expr const & c, pos_info const & pos) {
    if (!p.env().find(get_ite_name()))
        throw parser_error("invalid use of 'if-then-else' expression, environment does not contain 'ite' definition", pos);
    p.check_token_next(get_then_tk(), "invalid 'if-then-else' expression, 'then' expected");
    expr t = p.parse_expr(g_then_else_prec);
    p.check_token_next(get_else_tk(), "invalid 'if-then-else' expression, 'else' expected");
    expr e = p.parse_expr(g_then_else_prec);
    return p.save_pos(mk_app(mk_constant(get_ite_name()), c, t, e), pos);
}

static expr parse_dite(parser & p, name const & H_name, expr const & c, pos_info const & pos) {
    p.check_token_next(get_then_tk(), "invalid 'if-then-else' expression, 'then' expected");
    expr t, e;
    {
        parser::local_scope scope(p);
        expr H = mk_local(H_name, c);
        p.add_local(H);
        auto pos = p.pos();
        t = p.save_pos(Fun(H, p.parse_expr(g_then_else_prec), p), pos);
    }
    p.check_token_next(get_else_tk(), "invalid 'if-then-else' expression, 'else' expected");
    {
        parser::local_scope scope(p);
        expr H = mk_local(H_name, mk_app(*g_not, c));
        p.add_local(H);
        auto pos = p.pos();
        e = p.save_pos(Fun(H, p.parse_expr(g_then_else_prec), p), pos);
    }
    return p.save_pos(mk_app(p.save_pos(mk_constant(get_dite_name()), pos), c, t, e), pos);
}

static expr parse_if_then_else(parser & p, unsigned, expr const *, pos_info const & pos) {
    pair<optional<name>, expr> ie = p.parse_qualified_expr();
    if (ie.first)
        return parse_dite(p, *ie.first, ie.second, pos);
    else
        return parse_ite(p, ie.second, pos);
}

static expr parse_explicit_core(parser & p, pos_info const & pos, bool partial) {
    if (!p.curr_is_identifier())
        return p.parser_error_or_expr({sstream() << "invalid '" << (partial ? "@@" : "@") << "', identifier expected", p.pos()});
    expr fn = unwrap_pos(p.parse_id());
    if (is_choice(fn)) {
        sstream s;
        s << "invalid '" << (partial ? "@@" : "@") << "', function is overloaded, use fully qualified names (overloads: ";
        for (unsigned i = 0; i < get_num_choices(fn); i++) {
            if (i > 0) s << ", ";
            expr const & c = get_choice(fn, i);
            if (is_constant(c))
                s << const_name(c);
            else if (is_local(c))
                s << local_pp_name(c);
            else
                s << "[other]";
        }
        s << ")";
        return p.parser_error_or_expr({s, pos});
    } else if (!is_as_atomic(fn) && !is_constant(fn) && !is_local(fn)) {
        return p.parser_error_or_expr({sstream() << "invalid '" << (partial ? "@@" : "@") << "', function must be a constant or variable", pos});
    }
    if (partial)
        return p.save_pos(mk_partial_explicit(fn), pos);
    else
        return p.save_pos(mk_explicit(fn), pos);
}

static expr parse_explicit_expr(parser & p, unsigned, expr const *, pos_info const & pos) {
    return parse_explicit_core(p, pos, false);
}

static expr parse_partial_explicit_expr(parser & p, unsigned, expr const *, pos_info const & pos) {
    return parse_explicit_core(p, pos, true);
}

static expr parse_sorry(parser & p, unsigned, expr const *, pos_info const & pos) {
    return p.mk_sorry(pos);
}

static expr parse_borrowed_expr(parser & p, unsigned, expr const *, pos_info const & pos) {
    expr e = p.parse_expr(get_max_prec()-1);
    return p.save_pos(mk_borrowed(e), pos);
}

// We have disabled the SMT frontend
// static expr parse_pattern(parser & p, unsigned, expr const * args, pos_info const & pos) {
//    return p.save_pos(mk_pattern_hint(args[0]), pos);
// }

static expr parse_quoted_name(parser & p, unsigned, expr const *, pos_info const & pos) {
    bool resolve = false;
    name id;
    if (p.curr_is_token(get_placeholder_tk())) {
        p.next();
        id = "_";
    } else {
        if (p.curr_is_token(get_backtick_tk())) {
            p.next();
            resolve = true;
        }
        if (p.curr_is_keyword() || p.curr_is_command()) {
            if (resolve)
                return p.parser_error_or_expr({"invalid resolved quote symbol, identifier is a keyword/command", pos});
            id = p.get_token_info().token();
            p.next();
        } else {
            id = p.check_id_next("invalid quoted name, identifier expected");
        }
    }
    if (resolve) {
        parser::error_if_undef_scope scope(p);
        bool resolve_only = true;
        expr e = p.id_to_expr(id, pos, resolve_only);
        if (is_constant(e)) {
            id = const_name(e);
        } else if (is_local(e)) {
            id = local_pp_name(e);
        } else if (is_choice(e)) {
            sstream ss;
            ss << "invalid resolved quoted symbol, it is ambiguous, possible interpretations:";
            for (unsigned i = 0; i < get_num_choices(e); i++)
                ss << " " << get_choice(e, i);
            ss << " (solution: use fully qualified names)";
            return p.parser_error_or_expr({ss, pos});
        } else {
            return p.parser_error_or_expr({"invalid quoted symbol, failed to resolve it "
                               "(solution: use `<identifier> to bypass name resolution)", pos});
        }
    }
    lean_assert(id.is_string());
    expr e  = quote(id);
    return p.rec_save_pos(e, pos);
}

static name * g_anonymous_constructor = nullptr;

expr mk_anonymous_constructor(expr const & e) { return mk_annotation(*g_anonymous_constructor, e); }

bool is_anonymous_constructor(expr const & e) { return is_annotation(e, *g_anonymous_constructor); }

expr const & get_anonymous_constructor_arg(expr const & e) {
    lean_assert(is_anonymous_constructor(e));
    return get_annotation_arg(e);
}

static expr parse_constructor_core(parser & p, pos_info const & pos) {
    buffer<expr> args;
    while (!p.curr_is_token(get_rangle_tk())) {
        args.push_back(p.parse_expr());
        if (p.curr_is_token(get_comma_tk())) {
            p.next();
        } else {
            break;
        }
    }
    p.check_token_next(get_rangle_tk(), "invalid constructor, `⟩` expected");
    expr fn = p.save_pos(mk_expr_placeholder(), pos);
    return p.save_pos(mk_anonymous_constructor(mk_app(fn, args)), pos);
}

static expr parse_constructor(parser & p, unsigned, expr const *, pos_info const & pos) {
    return parse_constructor_core(p, pos);
}

static expr parse_lambda_core(parser & p, pos_info const & pos);

static expr parse_lambda_binder(parser & p, pos_info const & pos) {
    parser::local_scope scope1(p);
    buffer<expr> locals;
    auto new_env = p.parse_binders(locals, 0);
    for (expr const & local : locals)
        p.add_local(local);
    parser::local_scope scope2(p, new_env);
    expr body;
    if (/* p.curr_is_token(get_comma_tk()) || */ p.curr_is_token(get_darrow_tk())) {
        p.next();
        body = p.parse_expr();
    } else if (p.curr_is_token(get_langle_tk())) {
        body = parse_lambda_core(p, pos);
    } else {
        p.maybe_throw_error({"invalid lambda expression, '=>' or '⟨' expected", p.pos()});
        body = p.parse_expr();
    }
    return p.rec_save_pos(Fun(locals, body, p), pos);
}

static name * g_lambda_match_name = nullptr;

static expr parse_lambda_constructor(parser & p, pos_info const & ini_pos) {
    lean_assert(p.curr_is_token(get_langle_tk()));
    parser::local_scope scope(p);
    auto pos = p.pos();
    p.next();
    buffer<expr> locals;
    expr pattern = p.parse_pattern([&](parser & p) { return parse_constructor_core(p, pos); }, locals);
    for (expr const & local : locals)
        p.add_local(local);
    expr body;
    if (p.curr_is_token(get_darrow_tk())) {
        p.next();
        body = p.parse_expr();
    } else {
        body = parse_lambda_core(p, ini_pos);
    }
    match_definition_scope match_scope(p.env());
    expr fn  = p.save_pos(mk_local(p.next_name(), *g_lambda_match_name, mk_expr_placeholder(), mk_rec_info()), pos);
    expr eqn = Fun(fn, Fun(locals, p.save_pos(mk_equation(p.rec_save_pos(mk_app(fn, pattern), pos), body), pos), p), p);
    equations_header h = mk_match_header(match_scope.get_name(), match_scope.get_actual_name());
    expr x = p.rec_save_pos(mk_local(p.next_name(), "_x", mk_expr_placeholder(), mk_binder_info()), pos);
    return p.rec_save_pos(Fun(x, mk_app(mk_equations(h, 1, &eqn), x)), pos);
}

static expr parse_lambda_core(parser & p, pos_info const & pos) {
    if (p.curr_is_token(get_langle_tk())) {
        return parse_lambda_constructor(p, pos);
    } else {
        return parse_lambda_binder(p, pos);
    }
}

static expr parse_lambda(parser & p, unsigned, expr const *, pos_info const & pos) {
    return parse_lambda_core(p, pos);
}

static expr parse_list(parser & p, unsigned, expr const *, pos_info const & pos) {
    buffer<expr> elems;
    if (!p.curr_is_token(get_rbracket_tk())) {
        while (true) {
            expr elem = p.parse_expr();
            elems.push_back(elem);
            if (!p.curr_is_token(get_comma_tk()))
                break;
            p.next();
        }
    }
    p.check_token_next(get_rbracket_tk(), "invalid list, ']' expected");
    expr r = p.save_pos(mk_constant(get_list_nil_name()), pos);
    unsigned i = elems.size();
    while (i > 0) {
        --i;
        expr elem = elems[i];
        r = p.save_pos(mk_app(mk_constant(get_list_cons_name()), elem, r), p.pos_of(elem));
    }
    return r;
}

static expr parse_array(parser & p, unsigned n, expr const * l, pos_info const & pos) {
    expr xs = parse_list(p, n, l, pos);
    return p.save_pos(mk_app(mk_constant(get_list_to_array_name()), xs), pos);
}

static void consume_rparen(parser & p) {
    p.check_token_next(get_rparen_tk(), "invalid expression, `)` expected");
}

static name * g_infix_function = nullptr;

bool is_infix_function(expr const & e) {
    return is_annotation(e, *g_infix_function);
}

expr mk_infix_function(expr const & e) {
    return mk_annotation(*g_infix_function, e);
}

static expr parse_lparen(parser & p, unsigned, expr const *, pos_info const & pos) {
    expr e = p.parse_expr();
    if (p.curr_is_token(get_comma_tk())) {
        buffer<expr> args;
        args.push_back(e);
        while (p.curr_is_token(get_comma_tk())) {
            p.next();
            args.push_back(p.parse_expr());
        }
        consume_rparen(p);
        expr r = args.back();
        unsigned i = args.size() - 1;
        while (i > 0) {
            --i;
            r = p.save_pos(mk_app(p.save_pos(mk_constant(get_prod_mk_name()), pos),
                                  args[i], r), pos);
        }
        return r;
    } else if (p.curr_is_token(get_colon_tk())) {
        p.next();
        expr t = p.parse_expr();
        consume_rparen(p);
        return mk_typed_expr_distrib_choice(p, t, e, pos);
    } else {
        consume_rparen(p);
        return e;
    }
}

static expr parse_inaccessible(parser & p, unsigned, expr const *, pos_info const & pos) {
    expr e = p.parse_expr();
    if (!p.in_pattern()) {
        p.maybe_throw_error({"inaccesible pattern notation `.(t)` can only be used in patterns", pos});
        return e;
    }
    p.check_token_next(get_rparen_tk(), "invalid inaccesible pattern, `)` expected");
    return p.save_pos(mk_inaccessible(e), pos);
}

static expr parse_atomic_inaccessible(parser & p, unsigned, expr const *, pos_info const & pos) {
    if (!p.in_pattern()) {
        return p.parser_error_or_expr({"inaccesible pattern notation `._` can only be used in patterns", pos});
    }
    return p.save_pos(mk_inaccessible(p.save_pos(mk_expr_placeholder(), pos)), pos);
}

expr mk_annotation_with_pos(parser &, name const & a, expr const & e, pos_info const & pos) {
    expr r = mk_annotation(a, e);
    return save_pos(r, pos);
}

static expr parse_parser(parser & p, bool leading, pos_info const & pos) {
    name kind = get_curr_declaration_name();
    expr e = p.parse_expr();
    name n = leading ? get_lean_parser_leading_node_name() : get_lean_parser_trailing_node_name();
    expr r = mk_app(mk_constant(n), quote(kind), e);
    return save_pos(r, pos);
}

static expr parse_lparser(parser & p, unsigned, expr const *, pos_info const & pos) {
    return parse_parser(p, true, pos);
}

static expr parse_tparser(parser & p, unsigned, expr const *, pos_info const & pos) {
    return parse_parser(p, false, pos);
}

static expr parse_panic(parser & p, unsigned, expr const *, pos_info const & pos) {
    expr e = p.parse_expr();
    std::string mod = p.env().get_main_module().to_string();
    expr r = mk_app(mk_constant(get_panic_with_pos_name()), quote(mod.c_str()), quote(pos.first), quote(pos.second), e);
    return save_pos(r, pos);
}

static expr parse_trace(parser & p, unsigned, expr const *, pos_info const & pos) {
    expr k = p.parse_expr(get_max_prec());
    expr e = p.parse_expr(get_max_prec());
    expr m = mk_constant(get_lean_message_data_name());
    e = mk_typed_expr(m, e);
    expr r = mk_app(mk_constant(get_lean_monad_tracer_trace_name()), k, mk_lambda("_", mk_unit(), e, binder_info()));
    return save_pos(r, pos);
}

template<class T>
static T handle_res(object * r, parser const & p) {
    if (cnstr_tag(r) == 0) {
        throw parser_error(sstream() << cnstr_get_ref_t<string_ref>(object_ref(r), 0).to_std_string(), p.pos());
    } else {
        return cnstr_get_ref_t<T>(object_ref(r), 0);
    }
}

extern "C" object * lean_parse_expr(object * env, object * input, object * pos);

static object_ref parse_expr(parser & p) {
    object_ref tup = handle_res<object_ref>(lean_parse_expr(p.env().to_obj_arg(), mk_string(p.m_scanner.m_curr_line), nat(p.m_scanner.m_tk_spos).to_obj_arg()), p);
    size_t col = cnstr_get_ref_t<nat>(tup, 1).get_small_value();
    col = std::min(col, p.m_scanner.m_curr_line.size() - 1);
    p.m_scanner.skip_to_pos(pos_info {0, col});
    p.next();
    return cnstr_get_ref(tup, 0);
}

static object * mk_lean_ctx(parser & p) {
    buffer<name> locals;
    for (auto const & l : p.get_local_expr_decls().get_entries())
        locals.push_back(l.first);
    buffer<name> open_nss;
    for (auto const & e : get_active_export_decls(p.env()))
        open_nss.push_back(e.m_ns);
    return mk_cnstr(0,
                    p.env().to_obj_arg(),
                    to_list_ref(locals).to_obj_arg(),
                    to_list_ref(open_nss).to_obj_arg()).steal();
}

extern "C" object * lean_expand_stx_quot(object * ctx, object * stx);

static expr parse_stx_quot(parser & p, unsigned, expr const *, pos_info const & /* pos */) {
    object_ref stx = parse_expr(p);
    return handle_res<expr>(lean_expand_stx_quot(mk_lean_ctx(p), stx.steal()), p);
}

extern "C" object * lean_expand_match_syntax(object * ctx, object * discr, object * alts);
extern "C" object * lean_get_antiquot_vars(object * ctx, object * pats);

static expr parse_match_syntax(parser & p, unsigned, expr const *, pos_info const & /* pos */) {
    parser::local_scope scope1(p);
    parser::error_if_undef_scope eius(p);
    expr discr = p.parse_expr();
    p.check_token_next(get_with_tk(), "invalid 'match_syntax' expression, 'with' expected");
    unsigned case_column = p.pos().second;
    if (is_eqn_prefix(p))
        p.next(); // optional '|' in the first case
    buffer<object_ref> alts;
    while (true) {
        buffer<object_ref> lhs_args;
        lhs_args.push_back(parse_expr(p));
        while (p.curr_is_token(get_comma_tk())) {
            p.next();
            lhs_args.push_back(parse_expr(p));
        }
        list_ref<object_ref> lhs(lhs_args);
        p.check_token_next(get_darrow_tk(), "invalid 'match_syntax' expression, '=>' expected");
        {
            parser::local_scope scope2(p);
            auto vars = handle_res<list_ref<name>>(lean_get_antiquot_vars(mk_lean_ctx(p), lhs.to_obj_arg()), p);
            for (name const & var : vars)
                p.add_local_expr(var, mk_fvar(var));
            expr rhs = p.parse_expr();
            alts.push_back(mk_cnstr(0, lhs.to_obj_arg(), rhs.to_obj_arg()));
        }
        // terminate match on dedent
        if (!is_eqn_prefix(p) || p.pos().second < case_column)
            break;
        p.next();
    }
    return handle_res<expr>(lean_expand_match_syntax(mk_lean_ctx(p), discr.to_obj_arg(), list_ref<object_ref>(alts).to_obj_arg()), p);
}

parse_table init_nud_table() {
    action Expr(mk_expr_action());
    action Skip(mk_skip_action());
    action Binders(mk_binders_action());
    expr x0 = mk_bvar(0);
    parse_table r;
    r = r.add({transition("have", mk_ext_action(parse_have))}, x0);
    r = r.add({transition("show", mk_ext_action(parse_show))}, x0);
    r = r.add({transition("suffices", mk_ext_action(parse_suffices))}, x0);
    r = r.add({transition("if", mk_ext_action(parse_if_then_else))}, x0);
    r = r.add({transition("(", mk_ext_action(parse_lparen))}, x0);
    r = r.add({transition("[", mk_ext_action(parse_list))}, x0);
    r = r.add({transition("#[", mk_ext_action(parse_array))}, x0);
    r = r.add({transition("⟨", mk_ext_action(parse_constructor))}, x0);
    r = r.add({transition("{", mk_ext_action(parse_curly_bracket))}, x0);
    r = r.add({transition(".(", mk_ext_action(parse_inaccessible))}, x0);
    r = r.add({transition("._", mk_ext_action(parse_atomic_inaccessible))}, x0);
    r = r.add({transition("`", mk_ext_action(parse_quoted_name))}, x0);
    // r = r.add({transition("(:", Expr), transition(":)", mk_ext_action(parse_pattern))}, x0);
    r = r.add({transition("()", mk_ext_action(parse_unit))}, x0);
    r = r.add({transition("fun", mk_ext_action(parse_lambda))}, x0);
    r = r.add({transition("forall", Binders), transition(",", mk_scoped_expr_action(x0, 0, false))}, x0);
    r = r.add({transition("Type", mk_ext_action(parse_Type))}, x0);
    r = r.add({transition("Type*", mk_ext_action(parse_Type_star))}, x0);
    r = r.add({transition("Sort", mk_ext_action(parse_Sort))}, x0);
    r = r.add({transition("Sort*", mk_ext_action(parse_Sort_star))}, x0);
    r = r.add({transition("let", mk_ext_action(parse_let_expr))}, x0);
    r = r.add({transition("@", mk_ext_action(parse_explicit_expr))}, x0);
    r = r.add({transition("@@", mk_ext_action(parse_partial_explicit_expr))}, x0);
    r = r.add({transition("@&", mk_ext_action(parse_borrowed_expr))}, x0);
    r = r.add({transition("sorry", mk_ext_action(parse_sorry))}, x0);
    r = r.add({transition("match", mk_ext_action(parse_match))}, x0);
    r = r.add({transition("nomatch", mk_ext_action(parse_nomatch))}, x0);
    r = r.add({transition("do", mk_ext_action(parse_do_expr))}, x0);
    r = r.add({transition("parser!", mk_ext_action(parse_lparser))}, x0);
    r = r.add({transition("tparser!", mk_ext_action(parse_tparser))}, x0);
    r = r.add({transition("panic!", mk_ext_action(parse_panic))}, x0);
    r = r.add({transition("trace!", mk_ext_action(parse_trace))}, x0);
    r = r.add({transition("`(", mk_ext_action_core(parse_stx_quot))}, x0);
    r = r.add({transition("match_syntax", mk_ext_action(parse_match_syntax))}, x0);
    return r;
}

parse_table init_led_table() {
    parse_table r(false);
    r = r.add({transition("->", mk_expr_action(get_arrow_prec()-1))},    mk_arrow(mk_bvar(1), mk_bvar(1)));
    return r;
}

static parse_table * g_nud_table = nullptr;
static parse_table * g_led_table = nullptr;

parse_table get_builtin_nud_table() {
    return *g_nud_table;
}

parse_table get_builtin_led_table() {
    return *g_led_table;
}

void initialize_builtin_exprs() {
    g_no_universe_annotation = new name("no_univ");
    register_annotation(*g_no_universe_annotation);

    g_do_failure_eq     = new name("do_failure_eq");
    register_annotation(*g_do_failure_eq);

    g_infix_function    = new name("infix_fn");
    register_annotation(*g_infix_function);

    g_not               = new expr(mk_constant(get_not_name()));
    g_nud_table         = new parse_table();
    *g_nud_table        = init_nud_table();
    g_led_table         = new parse_table();
    *g_led_table        = init_led_table();
    g_do_match_name     = new name("_do_match");
    g_let_match_name    = new name("_let_match");
    g_lambda_match_name = new name("_fun_match");

    g_parser_checkpoint_have = new name{"parser", "checkpoint_have"};
    register_bool_option(*g_parser_checkpoint_have, LEAN_DEFAULT_PARSER_CHECKPOINT_HAVE,
                         "(parser) introduces a checkpoint on have-expressions, checkpoints are like Prolog-cuts");

    g_anonymous_constructor = new name("anonymousConstructor");
    register_annotation(*g_anonymous_constructor);
}

void finalize_builtin_exprs() {
    delete g_do_failure_eq;
    delete g_infix_function;
    delete g_led_table;
    delete g_nud_table;
    delete g_not;
    delete g_do_match_name;
    delete g_let_match_name;
    delete g_lambda_match_name;
    delete g_parser_checkpoint_have;
    delete g_anonymous_constructor;
    delete g_no_universe_annotation;
}
}
