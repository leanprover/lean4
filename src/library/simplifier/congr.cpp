/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sstream.h"
#include "kernel/kernel.h"
#include "library/equality.h"
#include "library/simplifier/congr.h"

namespace lean {
typedef congr_theorem_info::app_arg_info app_arg_info;
/**
   \brief Return true iff arg_info contains an entry s.t. m_proof_arg_pos or m_proof_new_arg_pos is pos.
*/
static bool contains_pos(buffer<app_arg_info> const & arg_info, unsigned pos) {
    return std::any_of(arg_info.begin(), arg_info.end(),
                       [&](app_arg_info const & info) {
                           return
                               info.get_pos_at_proof() == pos ||
                               (info.get_new_pos_at_proof() && *info.get_new_pos_at_proof() == pos);
                       });
}

static void check_conclusion_lhs_rhs(expr const & lhs, expr const & rhs, unsigned num) {
    if (!is_var(lhs) || !is_var(rhs))
        throw exception("invalid congruence theorem, the arguments in the left and right-hand-sides must be variables");
    if (var_idx(lhs) >= num)
        throw exception("invalid congruence theorem, left-hand-side contains free variables");
    if (var_idx(rhs) >= num)
        throw exception("invalid congruence theorem, right-hand-side contains free variables");
}

static void check_arg_lhs_rhs(expr const & lhs, expr const & rhs, unsigned num) {
    if (!is_var(lhs) || !is_var(rhs))
        throw exception(sstream() << "invalid congruence theorem, type of argument #" << (num+1) << " is not an equality between variables");
    if (var_idx(lhs) >= num)
        throw exception(sstream() << "invalid congruence theorem, left-hand-side of argument #" << (num+1) << " contains free variables");
    if (var_idx(rhs) >= num)
        throw exception(sstream() << "invalid congruence theorem, right-hand-side of argument #" << (num+1) << " contains free variables");
}

static buffer<app_arg_info>::iterator find_arg_info(buffer<app_arg_info> & arg_infos, unsigned proof_arg_pos, unsigned proof_new_arg_pos) {
    return std::find_if(arg_infos.begin(), arg_infos.end(), [&](app_arg_info const & info) {
            return info.get_pos_at_proof() == proof_arg_pos && info.get_new_pos_at_proof() && *info.get_new_pos_at_proof() == proof_new_arg_pos;
        });
}

static std::pair<unsigned, bool> find_hypothesis(buffer<app_arg_info> & arg_infos, unsigned vidx, unsigned num) {
    for (auto const & info : arg_infos) {
        if (vidx == info.get_pos_at_proof()) {
            return mk_pair(info.get_arg_pos(), false);
        } else if (info.get_new_pos_at_proof() && vidx == *info.get_new_pos_at_proof()) {
            return mk_pair(info.get_arg_pos(), true);
        }
    }
    throw exception(sstream() << "invalid congruence theorem, invalid hypothesis for argument #" << num
                    << ", variable must occur in the left or right hand side of the conclusion of the theorem");
}

void congr_theorem_info::context::display(std::ostream & out) const {
    if (!m_pos)
        out << "!";
    out << "#" << m_arg;
    if (m_new)
        out << "'";
}

void congr_theorem_info::app_arg_info::display(std::ostream & out) const {
    out << "#" << m_arg_pos << ": ";
    if (m_context) {
        m_context->display(out);
        out << " -> ";
    }
    out << "#" << m_proof_arg_pos;
    if (m_proof_new_arg_pos)
        out << " #" << *m_proof_new_arg_pos << " #" << *m_proof_proof_pos;
}

void congr_theorem_info::display(std::ostream & out) const {
    out << m_fun << " " << m_num_proof_args << "\n" << m_proof << "\n";
    for (auto const & info : m_arg_info) {
        info.display(out);
        out << "\n";
    }
    out << "\n";
}

congr_theorem_info check_congr_theorem(ro_environment const & env, expr const & e) {
    expr t = env->infer_type(e);
    expr b = t;
    unsigned num = 0;
    while (is_pi(b)) {
        b = abst_body(b);
        num++;
    }
    expr lhs, rhs;
    if (!is_equality(b, lhs, rhs))
        throw exception("invalid congruence theorem, conclusion is not an equality");
    if (!is_app(lhs))
        throw exception("invalid congruence theorem, left-hand-side of the conclusion is not a function application");
    if (!is_app(rhs))
        throw exception("invalid congruence theorem, right-hand-side of the conclusion is not a function application");
    if (arg(lhs, 0) != arg(rhs, 0))
        throw exception("invalid congruence theorem, the functions in the left and right-hand-sides are different");
    if (num_args(lhs) != num_args(rhs))
        throw exception("invalid congruence theorem, the number of arguments in the left and right-hand-sides is different");

    congr_theorem_info r;
    r.m_fun            = arg(lhs, 0);
    r.m_proof          = e;
    r.m_num_proof_args = num;

    buffer<app_arg_info> arg_infos;
    for (unsigned i = 1; i < num_args(lhs); i++) {
        expr a     = arg(lhs, i);
        expr new_a = arg(rhs, i);
        check_conclusion_lhs_rhs(a, new_a, num);
        unsigned proof_arg_pos     = num - var_idx(a) - 1;
        unsigned proof_new_arg_pos = num - var_idx(new_a) - 1;

        if (contains_pos(arg_infos, proof_arg_pos) ||
            contains_pos(arg_infos, proof_new_arg_pos))
            throw exception("invalid congruence theorem, variables can only occur once in the left and right-hand sides");

        if (proof_arg_pos == proof_new_arg_pos) {
            // this argument does not need proof, then add it directly to
            // r.m_arg_info
            r.m_arg_info.push_back(app_arg_info(i, proof_arg_pos));
        } else {
            // we have to find where the proof for this one is located
            arg_infos.push_back(app_arg_info(i, proof_arg_pos, proof_new_arg_pos));
        }
    }

    bool progress = true;
    while (progress) {
        progress = false;
        expr b = t;
        num = 0;
        while (is_pi(b)) {
            expr d = abst_domain(b);
            expr lhs, rhs;
            if (is_equality(d, lhs, rhs)) {
                check_arg_lhs_rhs(lhs, rhs, num);
                auto it = find_arg_info(arg_infos, num - var_idx(lhs) - 1, num - var_idx(rhs) - 1);
                if (it == arg_infos.end())
                    throw exception(sstream() << "invalid congruence theorem, argument #" << num << " does not match conclusion of the theorem");
                if (!it->m_proof_proof_pos) {
                    progress = true;
                    it->m_proof_proof_pos = num;
                    r.m_arg_info.push_back(*it);
                }
            } else if (is_pi(d) && is_equality(abst_body(d), lhs, rhs)) {
                check_arg_lhs_rhs(lhs, rhs, num+1);
                auto it = find_arg_info(arg_infos, num - var_idx(lhs), num - var_idx(rhs));
                if (it == arg_infos.end())
                    throw exception(sstream() << "invalid congruence theorem, argument #" << num
                                    << " does not match conclusion of the theorem");
                if (!it->m_proof_proof_pos) {
                    bool     ctx_pos;
                    std::pair<unsigned, bool> p;
                    if (is_var(abst_domain(d))) {
                        ctx_pos = true;
                        p = find_hypothesis(arg_infos, num - var_idx(abst_domain(d)) - 1, num);
                    } else if (is_not(abst_domain(d)) && is_var(arg(abst_domain(d), 1))) {
                        ctx_pos = false;
                        p = find_hypothesis(arg_infos, num - var_idx(arg(abst_domain(d), 1)) - 1, num);
                    } else {
                        throw exception(sstream() << "invalid congruence theorem, hypothesis for argument #" << num
                                        << " must be a variable or the negation of variable");
                    }
                    progress              = true;
                    unsigned ctx_arg      = p.first;
                    bool ctx_new          = p.second;
                    it->m_proof_proof_pos = num;
                    it->m_context         = congr_theorem_info::context(ctx_arg, ctx_pos, ctx_new);
                    r.m_arg_info.push_back(*it);
                }
            }
            b = abst_body(b);
            num++;
        }
    }
    buffer<bool> found_args;
    found_args.resize(num, false);
    for (auto const & info : r.m_arg_info) {
        found_args[info.get_pos_at_proof()] = true;
        if (info.get_new_pos_at_proof())
            found_args[*info.get_new_pos_at_proof()] = true;
        if (info.get_proof_pos_at_proof())
            found_args[*info.get_proof_pos_at_proof()] = true;
    }
    for (unsigned i = 0; i < num; i++)
        if (!found_args[i])
            throw exception(sstream() << "invalid congruence theorem, cannot synthesize argument #" << i);
    return r;
}
}
