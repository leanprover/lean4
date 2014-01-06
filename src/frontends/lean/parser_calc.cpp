/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/builtin.h"
#include "library/placeholder.h"
#include "library/io_state_stream.h"
#include "frontends/lean/parser_calc.h"
#include "frontends/lean/parser_imp.h"
#include "frontends/lean/operator_info.h"
#include "frontends/lean/frontend.h"

namespace lean {
bool calc_proof_parser::supports(expr const & op1) const {
    return
        std::find_if(m_supported_operators.begin(), m_supported_operators.end(), [&](op_data const & op2) { return op1 == op2.m_fn; })
        != m_supported_operators.end();
}

void calc_proof_parser::add_supported_operator(op_data const & op1) {
    if (supports(op1.m_fn))
        throw exception("operator already supported in the calculational proof manager");
    m_supported_operators = cons(op1, m_supported_operators);
}

optional<trans_data> calc_proof_parser::find_trans_data(expr const & op1, expr const & op2) const {
    auto it = std::find_if(m_trans_ops.begin(), m_trans_ops.end(),
                           [&](std::tuple<expr, expr, trans_data> const & entry) { return std::get<0>(entry) == op1 && std::get<1>(entry) == op2; });
    if (it == m_trans_ops.end())
        return optional<trans_data>();
    else
        return optional<trans_data>(std::get<2>(*it));
}

void calc_proof_parser::add_trans_step(expr const & op1, expr const & op2, trans_data const & d) {
    if (!supports(op1) || !supports(op2) || !supports(d.m_rop))
        throw exception("invalid transitivity step in calculational proof manager, operator not supported");
    if (find_trans_data(op1, op2))
        throw exception("transitivity step is already supported in the calculational proof manager");
    if (d.m_num_args < 5)
        throw exception("transitivity step must have at least 5 arguments");
    m_trans_ops.emplace_front(op1, op2, d);
}

static name g_eq_imp_trans({"eq", "imp", "trans"});
static name g_imp_eq_trans({"imp", "eq", "trans"});
static name g_imp_trans({"imp", "trans"});
static name g_eq_ne_trans({"eq", "ne", "trans"});
static name g_ne_eq_trans({"ne", "eq", "trans"});
static name g_neq("neq");

calc_proof_parser::calc_proof_parser() {
    expr imp = mk_implies_fn();
    expr eq  = mk_homo_eq_fn();
    expr iff = mk_iff_fn();
    expr neq = mk_constant(g_neq);

    add_supported_operator(op_data(imp, 2));
    add_supported_operator(op_data(eq, 3));
    add_supported_operator(op_data(iff, 2));
    add_supported_operator(op_data(neq, 3));
    add_trans_step(eq, eq,    trans_data(mk_trans_fn(), 6, eq));
    add_trans_step(eq, imp,   trans_data(mk_constant(g_eq_imp_trans), 5, imp));
    add_trans_step(imp, eq,   trans_data(mk_constant(g_imp_eq_trans), 5, imp));
    add_trans_step(imp, imp,  trans_data(mk_constant(g_imp_trans), 5, imp));
    add_trans_step(iff, iff,  trans_data(mk_trans_fn(), 6, iff));
    add_trans_step(iff, imp,  trans_data(mk_constant(g_eq_imp_trans), 5, imp));
    add_trans_step(imp, iff,  trans_data(mk_constant(g_imp_eq_trans), 5, imp));
    add_trans_step(eq, iff,   trans_data(mk_trans_fn(), 6, iff));
    add_trans_step(iff, eq,   trans_data(mk_trans_fn(), 6, iff));
    add_trans_step(eq,  neq,  trans_data(mk_constant(g_eq_ne_trans), 6, neq));
    add_trans_step(neq, eq,   trans_data(mk_constant(g_ne_eq_trans), 6, neq));
}

optional<expr> calc_proof_parser::find_op(operator_info const & op, pos_info const & p) const {
    if (!op)
        return none_expr();
    for (auto d : op.get_denotations()) {
        // TODO(Leo): I'm ignoring overloading.
        if (supports(d))
            return some_expr(d);
    }
    throw parser_error("invalid calculational proof, operator is not supported", p);
    return none_expr();
}

expr calc_proof_parser::parse_op(parser_imp & imp) const {
    environment const & env = imp.get_environment();
    auto p   = imp.pos();
    name id  = imp.check_identifier_next("invalid calculational proof, identifier expected");
    if (auto r = find_op(find_led(env, id), p))
        return *r;
    if (auto r = find_op(find_nud(env, id), p))
        return *r;
    expr e = imp.get_name_ref(id, p, false /* do not process implicit args */);
    if (!supports(e))
        throw parser_error("invalid calculational proof, operator is not supported", p);
    return e;
}

static expr parse_step_pr(parser_imp & imp, expr const & lhs) {
    auto p = imp.pos();
    imp.check_colon_next("invalid calculational proof, ':' expected");
    if (imp.curr_is_lcurly()) {
        imp.next();
        expr eq_pr = imp.parse_expr();
        imp.check_rcurly_next("invalid calculational proof, '}' expected");
        // Using axiom Subst {A : TypeU} {a b : A} {P : A → Bool} (H1 : P a) (H2 : a == b) : P b.
        return imp.save(Subst(imp.save(mk_placeholder(), p),
                              imp.save(mk_placeholder(), p),
                              imp.save(mk_placeholder(), p),
                              imp.save(mk_placeholder(), p), // let elaborator compute the first four arguments
                              imp.save(Refl(imp.save(mk_placeholder(), p), lhs), p),
                              eq_pr), p);
    } else {
        return imp.parse_expr();
    }
}

/**
   \brief Parse

   calc expr op expr : proof1
        ...  op expr : proof2

        ...  op expr : proofn
*/
expr calc_proof_parser::parse(parser_imp & imp) const {
    auto p = imp.pos();
    expr first = imp.parse_expr();
    if (!is_app(first))
        throw parser_error("invalid calculational proof, first expression must be an application", p);
    expr op      = arg(first, 0);
    if (!supports(op))
        throw parser_error("invalid calculational proof, first expression is not an application of a supported operator", p);
    if (num_args(first) < 3)
        throw parser_error("invalid calculational proof, first expression must be an application of a binary operator (modulo implicit arguments)", p);
    unsigned num = num_args(first);
    expr lhs     = arg(first, num - 2);
    expr rhs     = arg(first, num - 1);
    expr result  = parse_step_pr(imp, lhs);
    while (imp.curr() == scanner::token::Ellipsis) {
        imp.next();
        p = imp.pos();
        expr new_op  = parse_op(imp);
        auto tdata = find_trans_data(op, new_op);
        if (!tdata)
            throw parser_error("invalid calculational proof, operators cannot be combined", p);
        expr new_rhs = imp.parse_expr();
        expr step_pr = parse_step_pr(imp, rhs);
        buffer<expr> args;
        args.push_back(tdata->m_fn);
        for (unsigned i = 0; i < tdata->m_num_args - 5; i++) {
            // transitivity step has implicit arguments
            args.push_back(imp.save(mk_placeholder(), p));
        }
        args.push_back(lhs);
        args.push_back(rhs);
        args.push_back(new_rhs);
        args.push_back(result);
        args.push_back(step_pr);
        result = imp.save(mk_app(args), p);
        op  = tdata->m_rop;
        rhs = new_rhs;
    }
    return result;
}
}
