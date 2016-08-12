/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/trace.h"
#include "library/equations_compiler/equations.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/elaborator.h"
#include "frontends/lean/util.h"
#include "frontends/lean/decl_util.h"
#include "frontends/lean/decl_attributes.h"
#include "frontends/lean/definition_cmds.h"

namespace lean {
expr parse_equation_lhs(parser & p, expr const & fn, buffer<expr> & locals) {
    auto lhs_pos = p.pos();
    buffer<expr> lhs_args;
    lhs_args.push_back(p.parse_pattern_or_expr(get_max_prec()));
    while (!p.curr_is_token(get_assign_tk())) {
        lhs_args.push_back(p.parse_pattern_or_expr(get_max_prec()));
    }
    expr lhs = p.mk_app(fn, lhs_args, lhs_pos);
    bool skip_main_fn = true;
    return p.patexpr_to_pattern(lhs, skip_main_fn, locals);
}

expr parse_equation(parser & p, expr const & fn) {
    p.check_token_next(get_bar_tk(), "invalid equation, '|' expected");
    buffer<expr> locals;
    expr lhs = parse_equation_lhs(p, fn, locals);
    auto assign_pos = p.pos();
    p.check_token_next(get_assign_tk(), "invalid equation, ':=' expected");
    expr rhs = p.parse_scoped_expr(locals);
    return Fun(locals, p.save_pos(mk_equation(lhs, rhs), assign_pos), p);
}

optional<expr_pair> parse_using_well_founded(parser & p) {
    if (p.curr_is_token(get_using_well_founded_tk())) {
        p.next();
        expr R   = p.parse_expr(get_max_prec());
        expr Rwf = p.parse_expr(get_max_prec());
        return optional<expr_pair>(R, Rwf);
    } else {
        return optional<expr_pair>();
    }
}

expr mk_equations(parser & p, buffer<expr> const & fns, buffer<expr> const & eqs,
                  optional<expr_pair> const & R_Rwf, pos_info const & pos) {
    buffer<expr> new_eqs;
    for (expr const & eq : eqs) {
        new_eqs.push_back(Fun(fns, eq, p));
    }
    if (R_Rwf) {
        return p.save_pos(mk_equations(fns.size(), new_eqs.size(), new_eqs.data(), R_Rwf->first, R_Rwf->second), pos);
    } else {
        return p.save_pos(mk_equations(fns.size(), new_eqs.size(), new_eqs.data()), pos);
    }
}

expr parse_mutual_definition(parser & p, buffer<name> & lp_names, buffer<expr> & fns, buffer<expr> & params) {
    parser::local_scope scope(p);
    auto header_pos = p.pos();
    buffer<expr> pre_fns;
    parse_mutual_header(p, lp_names, pre_fns, params);
    buffer<expr> eqns;
    for (expr const & pre_fn : pre_fns) {
        expr fn_type = parse_inner_header(p, local_pp_name(pre_fn));
        if (p.curr_is_token(get_none_tk())) {
            auto none_pos = p.pos();
            p.next();
            eqns.push_back(p.save_pos(mk_no_equation(), none_pos));
        } else {
            while (p.curr_is_token(get_bar_tk())) {
                eqns.push_back(parse_equation(p, pre_fn));
            }
        }
        expr fn      = mk_local(local_pp_name(pre_fn), fn_type);
        fns.push_back(fn);
    }
    if (p.curr_is_token(get_with_tk()))
        throw parser_error("unexpected 'with' clause", p.pos());
    optional<expr_pair> R_Rwf = parse_using_well_founded(p);
    for (expr & eq : eqns) {
        eq = replace_locals(eq, pre_fns, fns);
    }
    expr r = mk_equations(p, fns, eqns, R_Rwf, header_pos);
    collect_implicit_locals(p, lp_names, params, r);
    return r;
}

environment mutual_definition_cmd_core(parser & p, bool is_private, bool is_protected, bool is_noncomputable,
                                       decl_attributes attrs) {
    buffer<name> lp_names;
    buffer<expr> fns, params;
    expr val = parse_mutual_definition(p, lp_names, fns, params);
    elaborator elab(p.env(), p.get_options(), metavar_context(), local_context());
    buffer<expr> new_params;
    elaborate_params(elab, params, new_params);
    val = replace_locals(val, params, new_params);

    // TODO(Leo)
    for (auto p : new_params) { tout() << ">> " << p << " : " << mlocal_type(p) << "\n"; }
    tout() << val << "\n";

    return p.env();
}

expr_pair parse_definition(parser & p, buffer<name> & lp_names, buffer<expr> & params) {
    parser::local_scope scope(p);
    auto header_pos = p.pos();
    expr fn = parse_single_header(p, lp_names, params);
    expr val;
    if (p.curr_is_token(get_assign_tk())) {
        p.next();
        val = p.parse_expr();
    } else if (p.curr_is_token(get_bar_tk())) {
        buffer<expr> eqns;
        if (p.curr_is_token(get_none_tk())) {
            auto none_pos = p.pos();
            p.next();
            eqns.push_back(p.save_pos(mk_no_equation(), none_pos));
        } else {
            while (p.curr_is_token(get_bar_tk())) {
                eqns.push_back(parse_equation(p, fn));
            }
        }
        optional<expr_pair> R_Rwf = parse_using_well_founded(p);
        buffer<expr> fns;
        fns.push_back(fn);
        val = mk_equations(p, fns, eqns, R_Rwf, header_pos);
    } else {
        throw parser_error("invalid definition, '|' or ':=' expected", p.pos());
    }
    collect_implicit_locals(p, lp_names, params, val);
    return mk_pair(fn, val);
}

environment xdefinition_cmd_core(parser & p, def_cmd_kind kind, bool is_private, bool is_protected, bool is_noncomputable,
                                 decl_attributes attrs) {
    buffer<name> lp_names;
    buffer<expr> params;
    expr fn, val;
    std::tie(fn, val) = parse_definition(p, lp_names, params);
    elaborator elab(p.env(), p.get_options(), metavar_context(), local_context());
    buffer<expr> new_params;
    elaborate_params(elab, params, new_params);
    val = replace_locals(val, params, new_params);

    // TODO(Leo)
    for (auto p : params) { tout() << ">> " << p << " : " << mlocal_type(p) << "\n"; }
    tout() << val << "\n";

    return p.env();
}
}
