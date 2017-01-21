/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/abstract.h"
#include "library/annotation.h"
#include "library/constants.h"
#include "library/quote.h"
#include "library/io_state_stream.h"
#include "library/trace.h"
#include "library/typed_expr.h"
#include "library/placeholder.h"
#include "library/scope_pos_info_provider.h"
#include "library/io_state.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_format.h"
#include "library/tactic/elaborate.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/util.h"
#include "frontends/lean/prenum.h"
#include "frontends/lean/tactic_notation.h"

/* The auto quotation currently supports two classes of tactics: tactic and smt_tactic.
   To add a new class Tac, we have to

   1) Make sure it is a monad. That is, we have an instance for (monad Tac)

   2) There is a namespace Tac.interactive

   3) There is a definition: Tac.step {α : Type} (t : Tac α) : Tac unit

   4) (Optional) Tac.rstep {α : Type} (line : nat) (col : nat) (tac : Tac α) : Tac unit
      similar to Tac.step, but reports an error at the given position if tac fails.
      If this one if not available, then Tac.step is used.

   5) There is a definition Tac.save_info (line col : nat) : Tac unit

   6) There is a definition Tac.execute (tac : Tac unit) : tactic unit

   7) There is a definition Tac.execute_with (cfg : config) (tac : Tac unit) : tactic unit
      where config is an arbitrary type.

   TODO(Leo): improve the "recipe" above. It is too ad hoc.
*/
namespace lean {
static expr mk_tactic_step(parser & p, expr tac, pos_info const & pos, name const & tac_class) {
    if (tac.get_tag() == nulltag)
        tac = p.save_pos(tac, pos);
    name step_name(tac_class, "step");
    if (!p.env().find(step_name))
        throw parser_error(sstream() << "invalid tactic class '" << tac_class << "', '" <<
                           tac_class << ".step' has not been defined", pos);
    return p.save_pos(mk_app(mk_constant(step_name), tac), pos);
}

static expr mk_tactic_rstep(parser & p, expr tac, pos_info const & pos, name const & tac_class) {
    if (tac.get_tag() == nulltag)
        tac = p.save_pos(tac, pos);
    name rstep_name(tac_class, "rstep");
    if (!p.env().find(rstep_name))
        return mk_tactic_step(p, tac, pos, tac_class);
    return p.save_pos(mk_app(mk_constant(rstep_name), mk_prenum(mpz(pos.first)), mk_prenum(mpz(pos.second)), tac), pos);
}

static expr mk_tactic_step(parser & p, expr tac, pos_info const & pos, name const & tac_class, bool use_rstep) {
    if (use_rstep)
        return mk_tactic_rstep(p, tac, pos, tac_class);
    else
        return mk_tactic_step(p, tac, pos, tac_class);
}

static expr mk_tactic_save_info(parser & p, pos_info const & pos, name const & tac_class) {
    name save_info_name(tac_class, "save_info");
    if (!p.env().find(save_info_name))
        throw parser_error(sstream() << "invalid tactic class '" << tac_class << "', '" <<
                           tac_class << ".save_info' has not been defined", pos);
    return p.save_pos(mk_app(mk_constant(save_info_name), mk_prenum(mpz(pos.first)), mk_prenum(mpz(pos.second))), pos);
}

static expr mk_tactic_solve1(parser & p, expr tac, pos_info const & pos, name const & tac_class, bool use_rstep) {
    if (tac.get_tag() == nulltag)
        tac = p.save_pos(tac, pos);
    name solve1_name(tac_class, "solve1");
    if (!p.env().find(solve1_name))
        throw parser_error(sstream() << "invalid tactic class '" << tac_class << "', '" <<
                           tac_class << ".solve1' has not been defined", pos);
    expr r = p.save_pos(mk_app(mk_constant(solve1_name), tac), pos);
    if (use_rstep)
        r = mk_tactic_rstep(p, r, pos, tac_class);
    return r;
}

static expr concat(parser & p, expr const & r, expr tac, pos_info const & pos) {
    return p.save_pos(mk_app(mk_constant(get_pre_monad_and_then_name()), r, tac), pos);
}

static optional<name> is_auto_quote_tactic(parser & p, name const & tac_class) {
    if (!p.curr_is_identifier()) return optional<name>();
    name id = tac_class + name("interactive") + p.get_name_val();
    if (p.env().find(id))
        return optional<name>(id);
    else
        return optional<name>();
}

static expr mk_lean_list(buffer<expr> const & es) {
    expr r = mk_constant(get_list_nil_name());
    unsigned i = es.size();
    while (i > 0) {
        --i;
        r = mk_app(mk_constant(get_list_cons_name()), es[i], r);
    }
    return r;
}

static expr mk_lean_none() {
    return mk_constant(get_option_none_name());
}

static expr mk_lean_some(expr const & e) {
    return mk_app(mk_constant(get_option_some_name()), e);
}

static expr parse_quoted_ident(parser & p, name const & decl_name) {
    if (!p.curr_is_identifier())
        throw parser_error(sstream() << "invalid auto-quote tactic '" << decl_name  << "', identifier expected", p.pos());
    auto pos = p.pos();
    name id  = p.get_name_val();
    p.next();
    return p.save_pos(quote_name(id), pos);
}

static expr parse_optional_quoted_ident(parser & p, name const & decl_name) {
    auto pos = p.pos();
    if (p.curr_is_identifier())
        return p.save_pos(mk_lean_some(parse_quoted_ident(p, decl_name)), pos);
    else
        return p.save_pos(mk_lean_none(), pos);
}


static expr parse_using_id(parser & p, name const & decl_name) {
    auto pos = p.pos();
    if (p.curr_is_token(get_using_tk())) {
        p.next();
        return p.save_pos(mk_lean_some(parse_quoted_ident(p, decl_name)), pos);
    } else {
        return p.save_pos(mk_lean_none(), pos);
    }
}

static expr parse_qexpr(parser & p, unsigned rbp) {
    auto pos = p.pos();
    expr e;
    /* TODO(Leo): avoid p.in_quote by improving
       parser::quote_scope constructor */
    if (p.in_quote()) {
        e = p.parse_expr(rbp);
    } else {
        parser::quote_scope scope(p, true);
        e = p.parse_expr(rbp);
    }
    return p.save_pos(mk_quote(e), pos);
}

static expr parse_qexpr_list(parser & p) {
    buffer<expr> result;
    p.check_token_next(get_lbracket_tk(), "invalid auto-quote tactic argument, '[' expected");
    while (!p.curr_is_token(get_rbracket_tk())) {
        result.push_back(parse_qexpr(p, 0));
        if (!p.curr_is_token(get_comma_tk())) break;
        p.next();
    }
    p.check_token_next(get_rbracket_tk(), "invalid auto-quote tactic argument, ']' expected");
    return mk_lean_list(result);
}

static expr parse_opt_qexpr_list(parser & p) {
    if (p.curr_is_token(get_lbracket_tk()))
        return parse_qexpr_list(p);
    else
        return mk_constant(get_list_nil_name());
}

static expr parse_qexpr_list_or_qexpr0(parser & p) {
    if (p.curr_is_token(get_lbracket_tk())) {
        return parse_qexpr_list(p);
    } else {
        buffer<expr> args;
        args.push_back(parse_qexpr(p, 0));
        /* Remark: We do not save position information for list.cons and list.nil.
           Reason: consider the tactic
              rw add_zero a
           Now, assume we use the position immediately before add_zero for list.cons.
           Then, info_manager::add_type_inf will store the type of list.cons and
           the type of add_zero for this position, and the lean server may incorrectly report
           the type of list.cons when we hover over add_zero. */
        return mk_lean_list(args);
    }
}

static expr mk_pair(expr const & e1, expr const & e2) {
    return mk_app(mk_constant(get_prod_mk_name()), e1, e2);
}

/* Convert given position into an expression of type (prod nat nat) */
static expr to_expr_pos(pos_info const & pos) {
    return mk_pair(mk_prenum(mpz(pos.first)), mk_prenum(mpz(pos.second)));
}

// small 'info' tweak: for `,`, report tactic state at following token instead
static void info_tweak(parser & p) {
    if (!p.get_complete() && p.get_break_at_pos() == some(p.pos()))
        p.set_break_at_pos({p.pos().first, p.pos().second + 1});
}

static expr parse_qexpr_list_with_pos(parser & p) {
    buffer<expr> result;
    p.check_token_next(get_lbracket_tk(), "invalid auto-quote tactic argument, '[' expected");
    while (!p.curr_is_token(get_rbracket_tk())) {
        auto pos = p.pos();
        try {
            expr pos_expr = to_expr_pos(pos);
            expr tac      = parse_qexpr(p, 0);
            result.push_back(mk_pair(tac, pos_expr));
            if (!p.curr_is_token(get_comma_tk())) break;
            info_tweak(p);
            p.next();
        } catch (break_at_pos_exception & ex) {
            ex.report_goal_pos(pos);
            throw ex;
        }
    }
    info_tweak(p);
    p.check_token_next(get_rbracket_tk(), "invalid auto-quote tactic argument, ']' expected");
    return mk_lean_list(result);
}

static expr parse_qexpr_list_or_qexpr0_with_pos(parser & p) {
    if (p.curr_is_token(get_lbracket_tk())) {
        return parse_qexpr_list_with_pos(p);
    } else {
        buffer<expr> args;
        expr pos = to_expr_pos(p.pos());
        expr tac = parse_qexpr(p, 0);
        args.push_back(mk_pair(tac, pos));
        /* Remark: We do not save position information for list.cons and list.nil.
           Reason: consider the tactic
              rw add_zero a
           Now, assume we use the position immediately before add_zero for list.cons.
           Then, info_manager::add_type_inf will store the type of list.cons and
           the type of add_zero for this position, and the lean server may incorrectly report
           the type of list.cons when we hover over add_zero. */
        return mk_lean_list(args);
    }
}

static expr parse_raw_id_list(parser & p) {
    buffer<expr> result;
    while (p.curr_is_identifier()) {
        auto id_pos = p.pos();
        name id = p.get_name_val();
        p.next();
        result.push_back(p.save_pos(quote_name(id), id_pos));
    }
    return mk_lean_list(result);
}

static expr parse_with_id_list(parser & p) {
    if (p.curr_is_token(get_with_tk())) {
        p.next();
        return parse_raw_id_list(p);
    } else {
        return mk_constant(get_list_nil_name());
    }
}

static expr parse_without_id_list(parser & p) {
    if (p.curr_is_token(get_without_tk())) {
        p.next();
        return parse_raw_id_list(p);
    } else {
        return mk_constant(get_list_nil_name());
    }
}

static expr parse_location(parser & p) {
    if (p.curr_is_token(get_at_tk())) {
        p.next();
        return parse_raw_id_list(p);
    } else {
        return mk_constant(get_list_nil_name());
    }
}

static expr parse_begin_end_block(parser & p, pos_info const & start_pos, name const & end_token, name tac_class, bool use_rstep);

static expr parse_nested_auto_quote_tactic(parser & p, name const & tac_class) {
    auto pos = p.pos();
    bool use_rstep = false;
    if (p.curr_is_token(get_lcurly_tk())) {
        return parse_begin_end_block(p, pos, get_rcurly_tk(), tac_class, use_rstep);
    } else if (p.curr_is_token(get_begin_tk())) {
        return parse_begin_end_block(p, pos, get_end_tk(), tac_class, use_rstep);
    } else {
        throw parser_error("invalid nested auto-quote tactic, '{' or 'begin' expected", pos);
    }
}

static expr parse_auto_quote_tactic(parser & p, name const & decl_name, name const & tac_class, bool use_rstep) {
    auto pos = p.pos();
    p.next();
    expr type    = p.env().get(decl_name).get_type();
    name itactic(name(tac_class, "interactive"), "itactic");
    buffer<expr> args;
    while (is_pi(type)) {
        if (is_explicit(binding_info(type))) {
            expr arg_type = binding_domain(type);
            if (is_constant(arg_type, get_interactive_types_qexpr_name())) {
                args.push_back(parse_qexpr(p, get_max_prec()));
            } else if (is_constant(arg_type, get_interactive_types_qexpr0_name())) {
                args.push_back(parse_qexpr(p, 0));
            } else if (is_constant(arg_type, get_interactive_types_qexpr_list_name())) {
                args.push_back(parse_qexpr_list(p));
            } else if (is_constant(arg_type, get_interactive_types_qexpr_list_with_pos_name())) {
                args.push_back(parse_qexpr_list_with_pos(p));
            } else if (is_constant(arg_type, get_interactive_types_opt_qexpr_list_name())) {
                args.push_back(parse_opt_qexpr_list(p));
            } else if (is_constant(arg_type, get_interactive_types_qexpr_list_or_qexpr0_name())) {
                args.push_back(parse_qexpr_list_or_qexpr0(p));
            } else if (is_constant(arg_type, get_interactive_types_qexpr_list_or_qexpr0_with_pos_name())) {
                args.push_back(parse_qexpr_list_or_qexpr0_with_pos(p));
            } else if (is_constant(arg_type, get_interactive_types_ident_name())) {
                args.push_back(parse_quoted_ident(p, decl_name));
            } else if (is_constant(arg_type, get_interactive_types_opt_ident_name())) {
                args.push_back(parse_optional_quoted_ident(p, decl_name));
            } else if (is_constant(arg_type, get_interactive_types_raw_ident_list_name())) {
                args.push_back(parse_raw_id_list(p));
            } else if (is_constant(arg_type, get_interactive_types_with_ident_list_name())) {
                args.push_back(parse_with_id_list(p));
            } else if (is_constant(arg_type, get_interactive_types_without_ident_list_name())) {
                args.push_back(parse_without_id_list(p));
            } else if (is_constant(arg_type, get_interactive_types_using_ident_name())) {
                args.push_back(parse_using_id(p, decl_name));
            } else if (is_constant(arg_type, get_interactive_types_location_name())) {
                args.push_back(parse_location(p));
            } else if (is_constant(arg_type, get_interactive_types_colon_tk_name())) {
                p.check_token_next(get_colon_tk(), "invalid auto-quote tactic, ':' expected");
                args.push_back(mk_constant(get_unit_star_name()));
            } else if (is_constant(arg_type, get_interactive_types_assign_tk_name())) {
                p.check_token_next(get_assign_tk(), "invalid auto-quote tactic, ':=' expected");
                args.push_back(mk_constant(get_unit_star_name()));
            } else if (is_constant(arg_type, get_interactive_types_comma_tk_name())) {
                p.check_token_next(get_comma_tk(), "invalid auto-quote tactic, ',' expected");
                args.push_back(mk_constant(get_unit_star_name()));
            } else if (is_constant(arg_type, itactic)) {
                args.push_back(parse_nested_auto_quote_tactic(p, tac_class));
            } else {
                args.push_back(p.parse_expr(get_max_prec()));
            }
        }
        type = binding_body(type);
    }
    expr r = p.mk_app(p.save_pos(mk_constant(decl_name), pos), args, pos);
    return mk_tactic_step(p, r, pos, tac_class, use_rstep);
}

static bool is_curr_exact_shortcut(parser & p) {
    return
        p.curr_is_token(get_have_tk()) ||
        p.curr_is_token(get_show_tk()) ||
        p.curr_is_token(get_assume_tk()) ||
        p.curr_is_token(get_calc_tk()) ||
        p.curr_is_token(get_suppose_tk());
}

static expr parse_tactic_core(parser & p, name const & tac_class, bool use_rstep) {
    try {
        p.check_break_before();
        if (p.curr_is_identifier())
            p.check_break_at_pos();
    } catch (break_at_pos_exception & e) {
        e.m_token_info.m_context = break_at_pos_exception::token_context::interactive_tactic;
        e.m_token_info.m_tac_class = tac_class;
        throw;
    }

    expr r;
    auto pos = p.pos();
    if (auto dname = is_auto_quote_tactic(p, tac_class)) {
        r = parse_auto_quote_tactic(p, *dname, tac_class, use_rstep);
    } else if (is_curr_exact_shortcut(p)) {
        expr arg = parse_qexpr(p, 0);
        r = p.mk_app(p.save_pos(mk_constant(tac_class + name({"interactive", "exact"})), pos), arg, pos);
        if (use_rstep) r = mk_tactic_rstep(p, r, pos, tac_class);
    } else {
        r = p.parse_expr();
        if (use_rstep) r = mk_tactic_rstep(p, r, pos, tac_class);
    }
    return concat(p, mk_tactic_save_info(p, pos, tac_class), r, pos);
}

static expr parse_tactic(parser & p, name const & tac_class, bool use_rstep) {
    if (p.in_quote()) {
        parser::quote_scope _(p, false);
        return parse_tactic_core(p, tac_class, use_rstep);
    } else {
        return parse_tactic_core(p, tac_class, use_rstep);
    }
}

static expr mk_tactic_unit(name const & tac_class) {
    return mk_app(mk_constant(tac_class), mk_constant(get_unit_name()));
}

static optional<name> is_tactic_class(environment const & env, name const & n) {
    if (n == "smt") {
        return optional<name>(name("smt_tactic"));
    } else if (env.find(name(n, "step")) && env.find(name(n, "save_info"))) {
        // TODO(Leo): improve check above
        return optional<name>(n);
    } else {
        return optional<name>();
    }
}

static name parse_tactic_class(parser & p, name tac_class) {
    if (p.curr_is_token(get_lbracket_tk())) {
        p.next();
        auto id_pos = p.pos();
        name id = p.check_id_next("invalid 'begin [...] ... end' block, identifier expected");
        auto new_class = is_tactic_class(p.env(), id);
        if (!new_class)
            throw parser_error(sstream() << "invalid 'begin [" << id << "] ...end' block, "
                               << "'" << id << "' is not a valid tactic class", id_pos);
        p.check_token_next(get_rbracket_tk(), "invalid 'begin [...] ... end block', ']' expected");
        return *new_class;
    } else {
        return tac_class;
    }
}

static expr parse_begin_end_block(parser & p, pos_info const & start_pos, name const & end_token, name tac_class, bool use_rstep) {
    p.next();
    name new_tac_class = tac_class;
    if (tac_class == get_tactic_name())
        new_tac_class = parse_tactic_class(p, tac_class);
    optional<expr> cfg;
    bool is_ext_tactic_class = tac_class == get_tactic_name() && new_tac_class != get_tactic_name();
    if (is_ext_tactic_class && p.curr_is_token(get_with_tk())) {
        p.next();
        cfg = p.parse_expr();
        p.check_token_next(get_comma_tk(), "invalid begin [...] with cfg, ... end block, ',' expected");
    }
    tac_class = new_tac_class;
    expr r = mk_tactic_save_info(p, start_pos, tac_class);
    try {
        while (!p.curr_is_token(end_token)) {
            auto pos = p.pos();
            try {
                /* parse next element */
                expr next_tac;
                if (p.curr_is_token(get_begin_tk()) ||
                    p.curr_is_token(get_lcurly_tk())) {
                    name const & end_tk = p.curr_is_token(get_begin_tk()) ? get_end_tk() : get_rcurly_tk();
                    expr info_tac = mk_tactic_save_info(p, pos, tac_class);
                    r = concat(p, r, info_tac, start_pos);
                    next_tac = parse_begin_end_block(p, pos, end_tk, tac_class, use_rstep);
                    auto block_pos = p.pos_of(next_tac);
                    next_tac = mk_tactic_solve1(p, next_tac, block_pos, tac_class, use_rstep);
                } else if (p.curr_is_token(get_do_tk())) {
                    expr tac = p.parse_expr();
                    expr type = p.save_pos(mk_tactic_unit(tac_class), pos);
                    next_tac = p.save_pos(mk_typed_expr(type, tac), pos);
                    next_tac = mk_tactic_step(p, next_tac, pos, tac_class, use_rstep);
                } else {
                    next_tac = parse_tactic(p, tac_class, use_rstep);
                }
                r = concat(p, r, next_tac, start_pos);
                if (!p.curr_is_token(end_token)) {
                    r = concat(p, r, mk_tactic_save_info(p, {p.pos().first, p.pos().second+1}, tac_class), start_pos);
                    info_tweak(p);
                    p.check_token_next(get_comma_tk(), "invalid 'begin-end' expression, ',' expected");
                }
            } catch (break_at_pos_exception & ex) {
                ex.report_goal_pos(pos);
                throw ex;
            }
        }
    } catch (exception & ex) {
        if (end_token == get_end_tk())
            consume_until_end_or_command(p);
        throw;
    }
    auto end_pos = p.pos();
    r = concat(p, r, mk_tactic_save_info(p, end_pos, tac_class), end_pos);
    try {
        p.next();
    } catch (break_at_pos_exception & ex) {
        ex.report_goal_pos(end_pos);
        throw;
    }
    if (!is_ext_tactic_class) {
        return r;
    } else if (cfg) {
        return copy_tag(r, mk_app(mk_constant(name(tac_class, "execute_with")), *cfg, r));
    } else {
        return copy_tag(r, mk_app(mk_constant(name(tac_class, "execute")), r));
    }
}

expr parse_begin_end_expr_core(parser & p, pos_info const & pos, name const & end_token) {
    parser::local_scope _(p);
    p.clear_expr_locals();
    bool use_rstep = true;
    expr tac = parse_begin_end_block(p, pos, end_token, get_tactic_name(), use_rstep);
    return copy_tag(tac, mk_by(tac));
}

expr parse_begin_end_expr(parser & p, pos_info const & pos) {
    return parse_begin_end_expr_core(p, pos, get_end_tk());
}

expr parse_curly_begin_end_expr(parser & p, pos_info const & pos) {
    return parse_begin_end_expr_core(p, pos, get_rcurly_tk());
}

expr parse_begin_end(parser & p, unsigned, expr const *, pos_info const & pos) {
    return parse_begin_end_expr(p, pos);
}

expr parse_by(parser & p, unsigned, expr const *, pos_info const & pos) {
    p.next();
    parser::local_scope _(p);
    p.clear_expr_locals();
    auto tac_pos = p.pos();
    try {
        bool use_rstep = false;
        expr tac  = parse_tactic(p, get_tactic_name(), use_rstep);
        expr type = mk_tactic_unit(get_tactic_name());
        expr r    = p.save_pos(mk_typed_expr(type, tac), tac_pos);
        return p.save_pos(mk_by(r), pos);
    } catch (break_at_pos_exception & ex) {
        ex.report_goal_pos(tac_pos);
        throw ex;
    }
}

expr parse_auto_quote_tactic_block(parser & p, unsigned, expr const *, pos_info const & pos) {
    name const & tac_class = get_tactic_name();
    bool use_rstep = false;
    expr r = parse_tactic(p, tac_class, use_rstep);
    while (p.curr_is_token(get_comma_tk())) {
        p.next();
        expr next = parse_tactic(p, tac_class, use_rstep);
        r = p.mk_app({p.save_pos(mk_constant(get_pre_monad_and_then_name()), pos), r, next}, pos);
    }
    p.check_token_next(get_rbracket_tk(), "invalid auto-quote tactic block, ']' expected");
    return r;
}

vm_obj tactic_report_error(vm_obj const & line, vm_obj const & col, vm_obj const & fmt, vm_obj const & _s) {
    tactic_state s = to_tactic_state(_s);
    pos_info pos(force_to_unsigned(line), force_to_unsigned(col));
    pos_info_provider * pip = get_pos_info_provider();
    if (pip) {
        std::shared_ptr<abstract_type_context> tc = std::make_shared<type_context>(mk_type_context_for(s));
        message_builder out(pip, tc, s.env(), get_global_ios(), pip->get_file_name(), pos, ERROR);
        out << mk_pair(to_format(fmt), s.get_options());
        out.report();
    }
    return mk_tactic_success(s);
}

void initialize_tactic_notation() {
    DECLARE_VM_BUILTIN(name({"tactic", "report_error"}), tactic_report_error);
}

void finalize_tactic_notation() {
}
}
