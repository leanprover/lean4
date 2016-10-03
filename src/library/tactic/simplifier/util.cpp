/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include <string>
#include "util/sstream.h"
#include "kernel/expr.h"
#include "kernel/instantiate.h"
#include "library/kernel_serializer.h"
#include "library/util.h"
#include "library/constants.h"
#include "library/app_builder.h"
#include "library/tactic/ac_tactics.h"
#include "library/tactic/simplifier/util.h"

namespace lean {

static void get_app_nary_args_core(type_context * tctx_ptr, expr const & op, expr const & e, buffer<expr> & nary_args, bool unsafe) {
    lean_assert(unsafe || tctx_ptr);
    auto next_op = get_binary_op(e);
    if (next_op && (unsafe ? (get_app_fn(*next_op) == get_app_fn(op)) : tctx_ptr->is_def_eq(*next_op, op))) {
        get_app_nary_args_core(tctx_ptr, op, app_arg(app_fn(e)), nary_args, unsafe);
        get_app_nary_args_core(tctx_ptr, op, app_arg(e), nary_args, unsafe);
    } else {
        nary_args.push_back(e);
    }
}

void unsafe_get_app_nary_args(expr const & op, expr const & e, buffer<expr> & nary_args) {
    bool unsafe = true;
    get_app_nary_args_core(nullptr, op, app_arg(app_fn(e)), nary_args, unsafe);
    get_app_nary_args_core(nullptr, op, app_arg(e), nary_args, unsafe);
}

void get_app_nary_args(type_context & tctx, expr const & op, expr const & e, buffer<expr> & nary_args) {
    bool unsafe = false;
    get_app_nary_args_core(&tctx, op, app_arg(app_fn(e)), nary_args, unsafe);
    get_app_nary_args_core(&tctx, op, app_arg(e), nary_args, unsafe);
}

optional<pair<expr, expr> > is_assoc(type_context & tctx, expr const & e) {
    auto op = get_binary_op(e);
    if (!op)
        return optional<pair<expr, expr> >();
    try {
        expr assoc_class = mk_app(tctx, get_is_associative_name(), *op);
        if (auto assoc_inst = tctx.mk_class_instance(assoc_class))
            return optional<pair<expr, expr> >(mk_pair(mk_app(tctx, get_is_associative_op_assoc_name(), 3, *op, *assoc_inst), *op));
        else
            return optional<pair<expr, expr> >();
    } catch (app_builder_exception ex) {
        return optional<pair<expr, expr> >();
    }
}

expr mk_congr_bin_op(abstract_type_context & tctx, expr const & H, expr const & arg1, expr const & arg2) {
    expr eq = tctx.relaxed_whnf(tctx.infer(H));
    expr A_op, op1, op2;
    lean_verify(is_eq(eq, A_op, op1, op2));
    lean_assert(is_pi(A_op));
    expr A = binding_domain(A_op);
    level lvl  = get_level(tctx, A);
    return ::lean::mk_app({mk_constant(get_simplifier_congr_bin_op_name(), {lvl}), A, op1, op2, H, arg1, arg2});
}

expr mk_congr_bin_arg1(abstract_type_context & tctx, expr const & op, expr const & H1, expr const & arg2) {
    expr eq = tctx.relaxed_whnf(tctx.infer(H1));
    expr A, arg11, arg12;
    lean_verify(is_eq(eq, A, arg11, arg12));
    level lvl  = get_level(tctx, A);
    return ::lean::mk_app({mk_constant(get_simplifier_congr_bin_arg1_name(), {lvl}), A, op, arg11, arg12, arg2, H1});
}

expr mk_congr_bin_arg2(abstract_type_context & tctx, expr const & op, expr const & arg1, expr const & H2) {
    expr eq = tctx.relaxed_whnf(tctx.infer(H2));
    expr A, arg21, arg22;
    lean_verify(is_eq(eq, A, arg21, arg22));
    level lvl  = get_level(tctx, A);
    return ::lean::mk_app({mk_constant(get_simplifier_congr_bin_arg2_name(), {lvl}), A, op, arg1, arg21, arg22, H2});
}

expr mk_congr_bin_args(abstract_type_context & tctx, expr const & op, expr const & H1, expr const & H2) {
    expr eq1 = tctx.relaxed_whnf(tctx.infer(H1));
    expr eq2 = tctx.relaxed_whnf(tctx.infer(H2));
    expr A, A0, arg11, arg12, arg21, arg22;
    lean_verify(is_eq(eq1, A, arg11, arg12));
    lean_verify(is_eq(eq2, A0, arg21, arg22));
    lean_assert(tctx.is_def_eq(A, A0));
    level lvl  = get_level(tctx, A);
    return ::lean::mk_app({mk_constant(get_simplifier_congr_bin_args_name(), {lvl}), A, op, arg11, arg12, arg21, arg22, H1, H2});
}

expr mk_assoc_subst(abstract_type_context & tctx, expr const & old_op, expr const & new_op, expr const & pf_op, expr const & assoc) {
    expr A_op = tctx.relaxed_whnf(tctx.infer(new_op));
    lean_assert(is_pi(A_op));
    expr A = binding_domain(A_op);
    level lvl  = get_level(tctx, A);
    return ::lean::mk_app({mk_constant(get_simplifier_assoc_subst_name(), {lvl}), A, old_op, new_op, pf_op, assoc});
}

// flat macro
static name * g_flat_macro_name    = nullptr;
static std::string * g_flat_opcode = nullptr;

class flat_macro_definition_cell : public macro_definition_cell {
    void check_macro(expr const & m) const {
        if (!is_macro(m) || macro_num_args(m) != 2)
            throw exception(sstream() << "invalid 'flat' macro, incorrect number of arguments");
    }

public:
    flat_macro_definition_cell() {}

    virtual name get_name() const override { return *g_flat_macro_name; }
    virtual expr check_type(expr const & m, abstract_type_context &, bool) const override {
        check_macro(m);
        return macro_arg(m, 1);
    }

    virtual optional<expr> expand(expr const & m, abstract_type_context & tctx) const override {
        check_macro(m);
        expr const & assoc      = macro_arg(m, 0);
        expr const & thm        = macro_arg(m, 1);

        expr old_e = app_arg(app_fn(thm));
        expr new_e = app_arg(thm);

        optional<expr> op = get_binary_op(old_e);
        lean_assert(op);

        pair<expr, optional<expr>> r_assoc = flat_assoc(tctx, *op, assoc, old_e);
        optional<expr> const & pf_of_assoc = r_assoc.second;

        if (!pf_of_assoc)
            return some_expr(mk_eq_refl(tctx, old_e));
        else
            return pf_of_assoc;
    }

    virtual void write(serializer & s) const override {
        s.write_string(*g_flat_opcode);
    }

    virtual bool operator==(macro_definition_cell const & other) const override {
        if (dynamic_cast<flat_macro_definition_cell const *>(&other)) {
            return true;
        } else {
            return false;
        }
    }

    virtual unsigned hash() const override {
        return get_name().hash();
    }
};

// Rewrite-assoc macro
static name * g_rewrite_assoc_macro_name    = nullptr;
static std::string * g_rewrite_assoc_opcode = nullptr;

class rewrite_assoc_macro_definition_cell : public macro_definition_cell {
    unsigned m_arg_idx;
    unsigned m_num_patterns;
    unsigned m_num_args;

    void check_macro(expr const & m) const {
        if (!is_macro(m) || macro_num_args(m) != 4)
            throw exception(sstream() << "invalid 'rewrite_assoc' macro, incorrect number of arguments");
    }
public:
    rewrite_assoc_macro_definition_cell(unsigned arg_idx, unsigned num_patterns, unsigned num_args):
        m_arg_idx(arg_idx), m_num_patterns(num_patterns), m_num_args(num_args) {}

    virtual name get_name() const { return *g_rewrite_assoc_macro_name; }
    virtual expr check_type(expr const & m, abstract_type_context &, bool) const {
        check_macro(m);
        return macro_arg(m, 1);
    }

    pair<expr, optional<expr> > group_args(expr const & e, unsigned pat_idx) const {
        if (pat_idx + 1 < m_num_patterns) {
            pair<expr, optional<expr> > p = group_args(app_arg(e), pat_idx + 1);
            return mk_pair(mk_app(app_fn(e), p.first), p.second);
        } else {
            lean_assert(pat_idx + 1 == m_num_patterns);
            if (m_arg_idx + m_num_patterns == m_num_args) {
                return mk_pair(e, none_expr());
            } else {
                return mk_pair(app_arg(app_fn(e)), some_expr(app_arg(e)));
            }
        }
    }

    expr compute_pre_motive(abstract_type_context & tctx, expr const & e, expr & l, expr & lhs, unsigned i) const {
        if (i == m_arg_idx) {
            // (lhs, rest)
            l = tctx.push_local(name("lhs"), tctx.infer(e));
            pair<expr, optional<expr> > lhs_rest = group_args(e, 0);
            lhs = lhs_rest.first;
            if (lhs_rest.second)
                return mk_app(app_fn(app_fn(e)), l, *lhs_rest.second);
            else
                return l;
        } else {
            return mk_app(app_fn(e), compute_pre_motive(tctx, app_arg(e), l, lhs, i+1));
        }
    }

    virtual optional<expr> expand(expr const & m, abstract_type_context & tctx) const {
        check_macro(m);
        expr const & assoc      = macro_arg(m, 0);
        expr const & thm        = macro_arg(m, 1);
        /* expr const & step_rhs   = macro_arg(m, 2); */
        expr pf_of_step         = macro_arg(m, 3);

        expr const & old_e = app_arg(app_fn(thm));
        /* expr const & new_e = app_arg(thm); */

        expr op = app_fn(app_fn(old_e));

        // Step 1: Re-arrange to group the args being rewritten
        expr local;
        expr step_lhs;

        expr pre_motive = tctx.abstract_locals(compute_pre_motive(tctx, old_e, local, step_lhs, 0), 1, &local);
        expr middle_e = instantiate(pre_motive, step_lhs);
        expr motive = mk_lambda(mlocal_name(local), tctx.infer(local), mk_app(app_fn(app_fn(thm)), middle_e, pre_motive));

        optional<expr> pf_flat = flat_assoc(tctx, op, assoc, middle_e).second;
        simp_result r_middle;
        if (pf_flat)
            r_middle = simp_result(middle_e, mk_eq_symm(tctx, *pf_flat));
        else
            r_middle = simp_result(middle_e);

        expr thm_of_step = tctx.infer(pf_of_step);
        if (auto pf_step_lhs_not_flat = flat_assoc(tctx, op, assoc, app_arg(app_fn(thm_of_step))).second) {
            // lemma needs to be flattened
            expr l = tctx.push_local(name("pf_lhs"), tctx.infer(old_e));
            expr motive = mk_lambda(mlocal_name(l), tctx.infer(l), tctx.abstract_locals(mk_app(app_fn(app_fn(thm)), l, app_arg(thm_of_step)), 1, &l));
            pf_of_step = mk_eq_subst(tctx, motive, *pf_step_lhs_not_flat, pf_of_step);
        }
        if (r_middle.has_proof())
            return some_expr(mk_eq_trans(tctx, r_middle.get_proof(), mk_eq_subst(tctx, motive, pf_of_step, mk_eq_refl(tctx, r_middle.get_new()))));
        else
            return some_expr(mk_eq_subst(tctx, motive, pf_of_step, mk_eq_refl(tctx, r_middle.get_new())));
    }

    virtual void write(serializer & s) const {
        s.write_string(*g_rewrite_assoc_opcode);
        s << m_arg_idx;
        s << m_num_patterns;
        s << m_num_args;
    }

    virtual bool operator==(macro_definition_cell const & other) const {
        if (auto other_ptr = dynamic_cast<rewrite_assoc_macro_definition_cell const *>(&other)) {
            return m_arg_idx == other_ptr->m_arg_idx && m_num_patterns == other_ptr->m_num_patterns
                && m_num_args == other_ptr->m_num_args;
        } else {
            return false;
        }
    }

    virtual unsigned hash() const {
        return ::lean::hash(m_arg_idx, ::lean::hash(m_num_patterns,
                                                    ::lean::hash(m_num_args, get_name().hash())));
    }
};

expr mk_flat_proof(expr const & assoc, expr const & thm) {
    expr margs[3];
    margs[0] = assoc;
    margs[1] = thm;
    macro_definition m(new flat_macro_definition_cell());
    return mk_macro(m, 2, margs);
}

expr mk_flat_macro(unsigned num_args, expr const * args) {
    lean_assert(num_args == 2);
    macro_definition m(new flat_macro_definition_cell());
    return mk_macro(m, num_args, args);
}

expr mk_rewrite_assoc_proof(expr const & assoc, expr const & thm, unsigned arg_idx, unsigned num_patterns,
                            unsigned num_args, expr const & step_rhs, expr const & pf_of_step) {
    expr margs[4];
    margs[0] = assoc;
    margs[1] = thm;
    margs[2] = step_rhs;
    margs[3] = pf_of_step;
    macro_definition m(new rewrite_assoc_macro_definition_cell(arg_idx, num_patterns, num_args));
    return mk_macro(m, 4, margs);
}

expr mk_rewrite_assoc_macro(unsigned num_args, expr const * args, unsigned arg_idx, unsigned num_patterns, unsigned num_e_args) {
    lean_assert(num_args == 4);
    macro_definition m(new rewrite_assoc_macro_definition_cell(arg_idx, num_patterns, num_e_args));
    return mk_macro(m, num_args, args);
}

// Setup and teardown
void initialize_simp_util() {
    // flat macro
    g_flat_macro_name = new name("flat");
    g_flat_opcode     = new std::string("FLAT");
    register_macro_deserializer(*g_flat_opcode,
                                [](deserializer & /* d */, unsigned num, expr const * args) {
                                    if (num != 2)
                                        throw corrupted_stream_exception();
                                    return mk_flat_macro(num, args);
                                });

    // rewrite_assoc macro
    g_rewrite_assoc_macro_name = new name("rewrite_assoc");
    g_rewrite_assoc_opcode     = new std::string("REWRITE_ASSOC");
    register_macro_deserializer(*g_rewrite_assoc_opcode,
                                [](deserializer & d, unsigned num, expr const * args) {
                                    if (num != 4)
                                        throw corrupted_stream_exception();
                                    unsigned arg_idx, num_patterns, num_e_args;
                                    d >> arg_idx;
                                    d >> num_patterns;
                                    d >> num_e_args;
                                    return mk_rewrite_assoc_macro(num, args, arg_idx, num_patterns, num_e_args);
                                });
}

void finalize_simp_util() {
    // rewrite_assoc macro
    delete g_rewrite_assoc_macro_name;
    delete g_rewrite_assoc_opcode;

    // flat macro
    delete g_flat_macro_name;
    delete g_flat_opcode;
}
}
