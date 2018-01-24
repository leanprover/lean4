/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/abstract.h"
#include "kernel/for_each_fn.h"
#include "library/annotation.h"
#include "library/constants.h"
#include "library/quote.h"
#include "library/io_state_stream.h"
#include "library/trace.h"
#include "library/typed_expr.h"
#include "library/placeholder.h"
#include "library/explicit.h"
#include "kernel/scope_pos_info_provider.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_format.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_parser.h"
#include "library/tactic/elaborate.h"
#include "library/tactic/tactic_evaluator.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/util.h"
#include "frontends/lean/prenum.h"
#include "frontends/lean/tactic_notation.h"
#include "frontends/lean/elaborator.h"
#include "frontends/lean/decl_util.h"
#include "frontends/lean/pp.h"
#include "frontends/lean/builtin_exprs.h"

/* The auto quotation currently supports two classes of tactics: tactic and smt_tactic.
   To add a new class Tac, we have to

   1) Make sure it is a monad. That is, we have an instance for (monad Tac)

   2) There is a namespace Tac.interactive

   3) There is a definition: Tac.step {α : Type} (t : Tac α) : Tac unit

   4) (Optional) Tac.istep {α : Type} (line0 col0 : nat) (line col : nat) (tac : Tac α) : Tac unit
      Similar to step but it should scope trace messages at the given line/col,
      and ensure that the exception position is after (line0, col0)

   6) There is a definition Tac.save_info (line col : nat) : Tac unit

   7) There is a definition Tac.execute (tac : Tac unit) : tactic unit

   8) There is a definition Tac.execute_with (cfg : config) (tac : Tac unit) : tactic unit
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

static expr mk_tactic_istep(parser &p, expr tac, pos_info const & pos0, pos_info const & pos, name const &tac_class) {
    if (p.in_notation())
        return mk_tactic_step(p, tac, pos, tac_class);
    if (tac.get_tag() == nulltag)
        tac = p.save_pos(tac, pos);
    name c(tac_class, "istep");
    if (!p.env().find(c))
        return mk_tactic_step(p, tac, pos, tac_class);
    return p.save_pos(mk_app({mk_constant(c),
            mk_prenum(mpz(pos0.first)), mk_prenum(mpz(pos0.second)),
            mk_prenum(mpz(pos.first)), mk_prenum(mpz(pos.second)),
            tac}), pos);
}

static expr mk_tactic_step(parser & p, expr tac, pos_info const & pos0, pos_info const & pos, name const & tac_class, bool use_istep) {
    if (use_istep)
        return mk_tactic_istep(p, tac, pos0, pos, tac_class);
    else
        return mk_tactic_step(p, tac, pos, tac_class);
}

static expr mk_tactic_save_info(parser & p, pos_info const & pos, name const & tac_class) {
    name save_info_name(tac_class, "save_info");
    if (!p.env().find(save_info_name))
        throw parser_error(sstream() << "invalid tactic class '" << tac_class << "', '" <<
                           tac_class << ".save_info' has not been defined", pos);
    auto pos_e = mk_anonymous_constructor(mk_app(mk_expr_placeholder(),
                                                 mk_prenum(mpz(pos.first)),
                                                 mk_prenum(mpz(pos.second))));
    return p.save_pos(mk_app(mk_constant(save_info_name), pos_e), pos);
}

static expr mk_tactic_solve1(parser & p, expr tac, pos_info const & pos0, pos_info const & pos, name const & tac_class, bool use_istep) {
    if (tac.get_tag() == nulltag)
        tac = p.save_pos(tac, pos);
    name solve1_name(tac_class, "solve1");
    if (!p.env().find(solve1_name))
        throw parser_error(sstream() << "invalid tactic class '" << tac_class << "', '" <<
                           tac_class << ".solve1' has not been defined", pos);
    expr r = p.save_pos(mk_app(mk_constant(solve1_name), tac), pos);
    if (use_istep)
        r = mk_tactic_istep(p, r, pos0, pos, tac_class);
    return r;
}

static expr concat(parser & p, expr const & tac1, expr const & tac2, pos_info const & pos) {
    return p.save_pos(mk_app(mk_constant(get_has_bind_seq_name()), tac1, tac2), pos);
}

name get_interactive_tactic_full_name(name const & tac_class, name const & tac) {
    return name(tac_class, "interactive") + tac;
}

static bool is_curr_exact_shortcut(parser & p) {
    return p.curr_is_token(get_calc_tk());
}

static optional<name> is_interactive_tactic(parser & p, name const & tac_class) {
    name id;
    switch (p.curr()) {
        case token_kind::Identifier:
            id = p.get_name_val();
            break;
        case token_kind::Keyword:
            id = p.get_token_info().value();
            break;
        default:
            return {};
    }
    id = get_interactive_tactic_full_name(tac_class, id);
    if (p.env().find(id))
        return optional<name>(id);
    else
        return optional<name>();
}

static expr parse_begin_end_block(parser & p, pos_info const & start_pos, name const & end_token, name tac_class, bool use_istep);

static expr parse_nested_interactive_tactic(parser & p, name const & tac_class, bool use_istep) {
    auto pos = p.pos();
    if (p.curr_is_token(get_lcurly_tk())) {
        return parse_begin_end_block(p, pos, get_rcurly_tk(), tac_class, use_istep);
    } else if (p.curr_is_token(get_begin_tk())) {
        return parse_begin_end_block(p, pos, get_end_tk(), tac_class, use_istep);
    } else {
        return p.parser_error_or_expr({"invalid nested auto-quote tactic, '{' or 'begin' expected", pos});
    }
}

static optional<name> is_itactic(expr const & type) {
    if (!is_constant(type))
        return optional<name>();
    name const & n = const_name(type);
    if (n.is_atomic() ||
        !n.is_string() ||
        strcmp(n.get_string(), "itactic") != 0)
        return optional<name>();
    name const & pre = n.get_prefix();
    if (pre.is_atomic() ||
        !pre.is_string() ||
        strcmp(pre.get_string(), "interactive") != 0)
        return optional<name>();
    return optional<name>(pre.get_prefix());
}

static expr parse_interactive_tactic(parser & p, name const & decl_name, name const & tac_class, bool use_istep) {
    auto pos = p.pos();
    expr type     = p.env().get(decl_name).get_type();
    buffer<expr> args;
    try {
        try {
            p.next();
            while (is_pi(type)) {
                p.check_break_before();
                if (is_explicit(binding_info(type))) {
                    expr arg_type = binding_domain(type);
                    if (is_app_of(arg_type, get_interactive_parse_name())) {
                        parser::quote_scope scope(p, true);
                        args.push_back(parse_interactive_param(p, arg_type));
                    } else if (auto new_tac_class = is_itactic(arg_type)) {
                        args.push_back(parse_nested_interactive_tactic(p, *new_tac_class, use_istep));
                    } else {
                        break;
                    }
                }
                type = binding_body(type);
            }
            while (p.curr_lbp() >= get_max_prec()) {
                p.check_break_before();
                args.push_back(p.parse_expr(get_max_prec()));
            }
            p.check_break_before();
        } catch (break_at_pos_exception) {
            throw;
        } catch (...) {
            p.check_break_before();
            throw;
        }
    } catch (break_at_pos_exception & e) {
        e.m_token_info.m_tac_param_idx = args.size();
        throw;
    }
    expr r = p.mk_app(p.save_pos(mk_constant(decl_name), pos), args, pos);
    return mk_tactic_step(p, r, pos, pos, tac_class, use_istep);
}

static expr mk_tactic_unit(name const & tac_class) {
    return mk_app(mk_constant(tac_class), mk_constant(get_unit_name()));
}

struct parse_tactic_fn {
    parser & m_p;
    name     m_tac_class;
    bool     m_use_istep;

    parse_tactic_fn(parser & p, name tac_class, bool use_istep):
        m_p(p), m_tac_class(tac_class), m_use_istep(use_istep) {}

    expr concat(expr const & tac1, expr const & tac2, pos_info const & pos) {
        return ::lean::concat(m_p, tac1, tac2, pos);
    }

    expr andthen(expr const & tac1, expr const & tac2, pos_info const & pos) {
        expr r = m_p.save_pos(mk_app(mk_constant(get_has_andthen_andthen_name()), tac1, tac2), pos);
        if (m_use_istep)
            r = mk_tactic_istep(m_p, r, pos, pos, m_tac_class);
        return r;
    }

    expr orelse(expr const & tac1, expr const & tac2, pos_info const & pos) {
        return m_p.save_pos(mk_app(mk_constant(get_has_orelse_orelse_name()), tac1, tac2), pos);
    }

    expr parse_qexpr(unsigned rbp = 0) {
        auto p = m_p.pos();
        parser::quote_scope scope1(m_p, true);
        restore_decl_meta_scope scope2;
        expr e = m_p.parse_expr(rbp);
        return m_p.save_pos(mk_pexpr_quote_and_substs(e, /* is_strict */ false), p);
    }

    expr parse_elem_core(bool save_info) {
        try {
            m_p.check_break_before();
            if (m_p.curr_is_identifier())
                m_p.check_break_at_pos();
        } catch (break_at_pos_exception & e) {
            e.m_token_info.m_context   = break_at_pos_exception::token_context::interactive_tactic;
            e.m_token_info.m_param     = m_tac_class;
            throw;
        }
        expr r;
        auto pos = m_p.pos();
        if (auto dname = is_interactive_tactic(m_p, m_tac_class)) {
            try {
                r = parse_interactive_tactic(m_p, *dname, m_tac_class, m_use_istep);
            } catch (break_at_pos_exception & e) {
                if (!m_p.get_complete() &&
                    (!e.m_token_info.m_token.size() ||
                     e.m_token_info.m_context == break_at_pos_exception::token_context::none)) {
                    e.m_token_info.m_pos       = pos;
                    e.m_token_info.m_token     = dname->get_string();
                    e.m_token_info.m_context   = break_at_pos_exception::token_context::interactive_tactic;
                    e.m_token_info.m_param     = m_tac_class;
                }
                throw;
            }
        } else if (is_curr_exact_shortcut(m_p)) {
            expr arg = parse_qexpr();
            r = m_p.mk_app(m_p.save_pos(mk_constant(get_interactive_tactic_full_name(m_tac_class, "exact")), pos), arg, pos);
            if (m_use_istep) r = mk_tactic_istep(m_p, r, pos, pos, m_tac_class);
        } else {
            r = m_p.parse_expr();
            if (m_use_istep) r = mk_tactic_istep(m_p, r, pos, pos, m_tac_class);
        }
        if (save_info)
            return concat(mk_tactic_save_info(m_p, pos, m_tac_class), r, pos);
        else
            return r;
    }

    expr parse_block(pos_info const & pos, name const & end_tk) {
        return ::lean::parse_begin_end_block(m_p, pos, end_tk, m_tac_class, m_use_istep);
    }

    expr parse_elem(bool save_info, bool use_solve1 = true) {
        if (m_p.curr_is_token(get_begin_tk()) ||
            m_p.curr_is_token(get_lcurly_tk())) {
            auto pos = m_p.pos();
            name const & end_tk = m_p.curr_is_token(get_begin_tk()) ? get_end_tk() : get_rcurly_tk();
            expr next_tac = parse_block(pos, end_tk);
            auto end_pos = m_p.pos_of(next_tac);
            if (use_solve1) {
                next_tac       = mk_tactic_solve1(m_p, next_tac, pos, end_pos, m_tac_class, m_use_istep && save_info);
            }
            if (save_info) {
                expr info_tac = mk_tactic_save_info(m_p, pos, m_tac_class);
                return concat(info_tac, next_tac, pos);
            } else {
                return next_tac;
            }
        } else if (m_p.curr_is_token(get_lbracket_tk())) {
            auto pos = m_p.pos();
            m_p.next();
            buffer<expr> args;
            if (!m_p.curr_is_token(get_rbracket_tk())) {
                while (true) {
                    args.push_back(parse_elem(save_info, false));
                    if (!m_p.curr_is_token(get_comma_tk()))
                        break;
                    m_p.next();
                }
            }
            m_p.check_token_next(get_rbracket_tk(), "invalid tactic list, ']' expected");
            expr r = mk_lean_list(m_p, args, pos);
            expr type = mk_app(mk_constant(get_list_name()), mk_tactic_unit(m_tac_class));
            r = m_p.save_pos(mk_typed_expr(type, r), pos);
            return r;
        } else {
            if (m_p.curr_is_token(get_by_tk())) {
                // `by tac` ~> `solve1 { tac }`
                m_p.next();
                auto pos = m_p.pos();
                expr tac = operator()(save_info);
                auto end_pos = m_p.pos_of(tac);
                tac = mk_tactic_solve1(m_p, tac, pos, end_pos, m_tac_class, m_use_istep && save_info);
                if (save_info) {
                    expr info_tac = mk_tactic_save_info(m_p, pos, m_tac_class);
                    return concat(info_tac, tac, pos);
                } else {
                    return tac;
                }
            } else {
                return parse_elem_core(save_info);
            }
        }
    }

    expr parse_orelse(expr left) {
        auto start_pos = m_p.pos();
        expr r = left;
        while (m_p.curr_is_token(get_orelse_tk())) {
            m_p.next();
            expr curr = parse_elem(false);
            r         = orelse(r, curr, start_pos);
        }
        return r;
    }

    expr parse_andthen(expr left) {
        auto start_pos = m_p.pos();
        expr r = left;
        while (m_p.curr_is_token(get_semicolon_tk())) {
            m_p.next();
            expr curr = parse_elem(false);
            if (m_p.curr_is_token(get_orelse_tk()))
                curr = parse_orelse(curr);
            r = andthen(r, curr, start_pos);
        }
        return r;
    }

    expr operator()(bool save_info = true) {
        expr r = parse_elem(save_info);
        if (m_p.curr_is_token(get_semicolon_tk()))
            return parse_andthen(r);
        else if (m_p.curr_is_token(get_orelse_tk()))
            return parse_orelse(r);
        else
            return r;
    }
};

static expr parse_tactic_core(parser & p, name const & tac_class, bool use_istep) {
    return parse_tactic_fn(p, tac_class, use_istep)();
}

static expr parse_tactic(parser & p, name const & tac_class, bool use_istep) {
    if (p.in_quote()) {
        parser::quote_scope _(p, false);
        return parse_tactic_core(p, tac_class, use_istep);
    } else {
        return parse_tactic_core(p, tac_class, use_istep);
    }
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
        if (!new_class) {
            p.maybe_throw_error({sstream() << "invalid 'begin [" << id << "] ...end' block, "
                               << "'" << id << "' is not a valid tactic class", id_pos});
            return tac_class;
        }
        p.check_token_next(get_rbracket_tk(), "invalid 'begin [...] ... end block', ']' expected");
        return *new_class;
    } else {
        return tac_class;
    }
}

struct parse_begin_end_block_fn {
    parser & m_p;
    name     m_tac_class;
    bool     m_use_istep;

    parse_begin_end_block_fn(parser & p, name tac_class, bool use_istep):
        m_p(p), m_tac_class(tac_class), m_use_istep(use_istep) {}

    expr concat(expr const & tac1, expr const & tac2, pos_info const & pos) {
        return ::lean::concat(m_p, tac1, tac2, pos);
    }

    expr concat(buffer<expr> const & args, unsigned start, unsigned end, pos_info const & pos) {
        lean_assert(start < end);
        lean_assert(end <= args.size());
        if (end == start+1)
            return args[start];
        unsigned mid = (start + end)/2;
        expr left  = concat(args, start, mid, pos);
        expr right = concat(args, mid, end, pos);
        return concat(left, right, pos);
    }

    expr concat(buffer<expr> const & args, pos_info const & pos) {
        lean_assert(!args.empty());
        return concat(args, 0, args.size(), pos);
    }

    expr mk_save_info() {
        expr r = mk_tactic_save_info(m_p, {m_p.pos().first, m_p.pos().second+1}, m_tac_class);
        return r;
    }

    expr parse_tactic() {
        return ::lean::parse_tactic(m_p, m_tac_class, m_use_istep);
    }

    expr operator()(pos_info const & start_pos, name const & end_token) {
        auto sync = [&] {
            while (!m_p.curr_is_token(get_comma_tk()) && !m_p.curr_is_token(end_token) &&
                    !m_p.curr_is_token(get_semicolon_tk()) && !m_p.curr_is_token(get_orelse_tk())) {
                auto pos0 = m_p.pos();
                m_p.next();
                if (m_p.pos() == pos0) break;
            }
            if (!m_p.curr_is_token(get_end_tk())) m_p.next();
            m_p.maybe_throw_error({"sync", m_p.pos()});
        };

        m_p.next();
        name new_tac_class = m_tac_class;
        if (m_tac_class == get_tactic_name())
            new_tac_class = parse_tactic_class(m_p, m_tac_class);
        optional<expr> cfg;
        bool is_ext_tactic_class = m_tac_class == get_tactic_name() && new_tac_class != get_tactic_name();
        if (is_ext_tactic_class && m_p.curr_is_token(get_with_tk())) {
            m_p.next();
            cfg = m_p.parse_expr();
            m_p.check_token_next(get_comma_tk(), "invalid begin [...] with cfg, ... end block, ',' expected");
        }
        m_tac_class = new_tac_class;
        buffer<expr> to_concat;
        to_concat.push_back(mk_tactic_save_info(m_p, start_pos, m_tac_class));
        while (!m_p.curr_is_token(end_token)) {
            pos_info pos = m_p.pos();
            try {
                to_concat.push_back(parse_tactic());
                if (!m_p.curr_is_token(end_token)) {
                    m_p.without_break_at_pos<void>([&]() {
                        if (!m_p.check_token_next(get_comma_tk(), "invalid 'begin-end' expression, ',' expected")) {
                            sync();
                        }
                    });
                }
                to_concat.push_back(mk_save_info());
            } catch (break_at_pos_exception & ex) {
                ex.report_goal_pos(pos);
                throw;
            }
            if (m_p.pos() == pos) sync();
            if (m_p.pos() == pos) break;
        }
        auto end_pos = m_p.pos();
        expr r = concat(to_concat, start_pos);
        r = concat(r, mk_tactic_save_info(m_p, end_pos, m_tac_class), end_pos);
        try {
            m_p.next();
        } catch (break_at_pos_exception & ex) {
            ex.report_goal_pos(end_pos);
            throw;
        }
        if (!is_ext_tactic_class) {
            return r;
        } else if (cfg) {
            return copy_tag(r, mk_app(mk_constant(name(m_tac_class, "execute_with")), *cfg, r));
        } else {
            return copy_tag(r, mk_app(mk_constant(name(m_tac_class, "execute")), r));
        }
    }
};

static expr parse_begin_end_block(parser & p, pos_info const & start_pos, name const & end_token, name tac_class, bool use_istep) {
    return parse_begin_end_block_fn(p, tac_class, use_istep)(start_pos, end_token);
}

expr parse_begin_end_expr_core(parser & p, pos_info const & pos, name const & end_token) {
    parser::local_scope scope1(p);
    meta_definition_scope scope2;
    p.clear_expr_locals();
    bool use_istep = true;
    expr tac = parse_begin_end_block(p, pos, end_token, get_tactic_name(), use_istep);
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
    parser::local_scope scope1(p);
    meta_definition_scope scope2;
    p.clear_expr_locals();
    auto tac_pos = p.pos();
    try {
        bool use_istep    = true;
        expr tac  = parse_tactic(p, get_tactic_name(), use_istep);
        expr type = mk_tactic_unit(get_tactic_name());
        expr r    = p.save_pos(mk_typed_expr(type, tac), tac_pos);
        return p.save_pos(mk_by(r), pos);
    } catch (break_at_pos_exception & ex) {
        ex.report_goal_pos(tac_pos);
        throw ex;
    }
}

/*
Consider the following example:

  meta def apply_zero_add (a : pexpr) : tactic unit :=
  `[apply zero_add %%a] -- We don't want the error to be reported here when 'a' does not have the expected type.

  example (a : nat) : 0 + a = a :=
  begin
    apply_zero_add `(tt), -- Error should be here
  end

We address the issue above by erasing position information from quoted terms nested in 'e'.
*/
static void erase_quoted_terms_pos_info(parser & p, expr const & e) {
    for_each(e, [&](expr const & e, unsigned) {
            if (is_pexpr_quote(e)) {
                for_each(get_pexpr_quote_value(e), [&](expr const & e, unsigned) {
                        p.erase_pos(e);
                        return true;
                    });
            }
            return true;
        });
}

expr parse_interactive_tactic_block(parser & p, unsigned, expr const *, pos_info const & pos) {
    name const & tac_class = get_tactic_name();
    bool use_istep    = false;
    expr r = parse_tactic(p, tac_class, use_istep);
    erase_quoted_terms_pos_info(p, r);
    while (p.curr_is_token(get_comma_tk())) {
        p.next();
        expr next = parse_tactic(p, tac_class, use_istep);
        erase_quoted_terms_pos_info(p, next);
        r = p.mk_app({p.save_pos(mk_constant(get_has_bind_and_then_name()), pos), r, next}, pos);
    }
    p.check_token_next(get_rbracket_tk(), "invalid auto-quote tactic block, ']' expected");
    return r;
}

void initialize_tactic_notation() {
}

void finalize_tactic_notation() {
}
}
