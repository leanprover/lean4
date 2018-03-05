/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <string>
#include "library/trace.h"
#include "library/app_builder.h"
#include "library/tactic/ac_tactics.h"
#include "library/tactic/smt/util.h"
#include "library/tactic/smt/congruence_closure.h"
#include "library/tactic/smt/theory_ac.h"

namespace lean {
/* Given e and ac_term that is provably equal to e using AC, return a proof for e = ac_term */
static expr mk_ac_refl_proof(type_context_old & ctx, expr const & e, expr const & ac_term, expr const & assoc, expr const & comm) {
    return mk_perm_ac_macro(ctx, assoc, comm, e, ac_term);
}

/* Given (tr := t*r) (sr := s*r) (t_eq_s : t = s), return a proof for
   tr = sr

   We use a*b to denote an AC application. That is, (a*b)*(c*a) is the term (a*a*b*c). */
static expr mk_ac_simp_proof(type_context_old & ctx, expr const & tr, expr const & t, expr const & s, expr const & r, expr const & sr,
                             expr const & t_eq_s, expr const & assoc, expr const & comm) {
    if (tr == t) {
        return t_eq_s;
    } else if (tr == sr) {
        return mk_eq_refl(ctx, tr);
    } else {
        lean_assert(is_ac_app(tr));
        expr const & op = get_ac_app_op(tr);
        expr op_r       = mk_app(op, r);
        expr rt         = mk_app(op_r, t);
        expr rs         = mk_app(op, r, s);
        expr rt_eq_rs   = mk_congr_arg(ctx, op_r, t_eq_s);
        expr tr_eq_rt   = mk_perm_ac_macro(ctx, assoc, comm, tr, rt);
        expr rs_eq_sr   = mk_perm_ac_macro(ctx, assoc, comm, rs, sr);
        return mk_eq_trans(ctx, mk_eq_trans(ctx, tr_eq_rt, rt_eq_rs), rs_eq_sr);
    }
}

/* Given (ra := a*r) (sb := b*s) (ts := t*s) (tr := t*r) (ts_eq_a : t*s = a) (tr_eq_b : t*r = b),
   return a proof for ra = sb.

   We use a*b to denote an AC application. That is, (a*b)*(c*a) is the term (a*a*b*c).

   The proof is constructed using congruence and the perm_ac macro. */
static expr mk_ac_superpose_proof(type_context_old & ctx,
                                  expr const & ra, expr const & sb,
                                  expr const & a, expr const & b,
                                  expr const & r, expr const & s,
                                  expr const & ts, expr const & tr,
                                  expr const & ts_eq_a, expr const & tr_eq_b,
                                  expr const & assoc, expr const & comm) {
    lean_assert(is_ac_app(tr));
    lean_assert(is_ac_app(ts));
    expr const & op = get_ac_app_op(ts);
    expr tsr_eq_ar  = mk_congr_fun(ctx, mk_congr_arg(ctx, op, ts_eq_a), r);
    expr trs_eq_bs  = mk_congr_fun(ctx, mk_congr_arg(ctx, op, tr_eq_b), s);
    expr tsr        = mk_app(op, ts, r);
    expr trs        = mk_app(op, tr, s);
    expr tsr_eq_trs = mk_perm_ac_macro(ctx, assoc, comm, tsr, trs);
    expr ar         = mk_app(op, a, r);
    expr bs         = mk_app(op, b, s);
    expr ra_eq_ar   = mk_perm_ac_macro(ctx, assoc, comm, ra, ar);
    expr bs_eq_sb   = mk_perm_ac_macro(ctx, assoc, comm, bs, sb);
    return mk_eq_trans(ctx, ra_eq_ar,
           mk_eq_trans(ctx, mk_eq_symm(ctx, tsr_eq_ar),
           mk_eq_trans(ctx, tsr_eq_trs,
           mk_eq_trans(ctx, trs_eq_bs, bs_eq_sb))));
}

static char const * ac_var_prefix = "x_";

format theory_ac::state::pp_term(formatter const & fmt, expr const & e) const {
    if (auto it = m_entries.find(e)) {
        return format(ac_var_prefix) + format(it->m_idx);
    } else if (is_ac_app(e)) {
        format r          = fmt(get_ac_app_op(e));
        unsigned nargs    = get_ac_app_num_args(e);
        expr const * args = get_ac_app_args(e);
        for (unsigned i = 0; i < nargs; i++) {
            r += line() + pp_term(fmt, args[i]);
        }
        return group(bracket("[", r, "]"));
    } else {
        tout() << "pp_term: " << e << "\n";
        lean_unreachable();
    }
}

format theory_ac::state::pp_decl(formatter const & fmt, expr const & e) const {
    lean_assert(m_entries.contains(e));
    auto it = m_entries.find(e);
    return group(format(ac_var_prefix) + format(it->m_idx) + line() + format(":=") + line() + fmt(e));
}

format theory_ac::state::pp_decls(formatter const & fmt) const {
    format r;
    bool first = true;
    m_entries.for_each([&](expr const & k, entry const &) {
            if (first) first = false; else r += comma() + line();
            r += pp_decl(fmt, k);
        });
    return group(bracket("{", r, "}"));
}

format theory_ac::state::pp_R(formatter const & fmt) const {
    format r;
    unsigned indent = get_pp_indent(fmt.get_options());
    bool first = true;
    m_R.for_each([&](expr const & k, expr_pair const & p) {
            format curr = pp_term(fmt, k) + line() + format("-->") + nest(indent, line() + pp_term(fmt, p.first));
            if (first) first = false; else r += comma() + line();
            r += group(curr);
        });
    return group(bracket("{", r, "}"));
}

format theory_ac::state::pp(formatter const & fmt) const {
    return group(bracket("[", pp_decls(fmt) + comma() + line() + pp_R(fmt), "]"));
}

theory_ac::theory_ac(congruence_closure & cc, state & s):
    m_ctx(cc.ctx()),
    m_cc(cc),
    m_state(s),
    m_ac_manager(cc.ctx()) {
}

theory_ac::~theory_ac() {
}

optional<expr> theory_ac::is_ac(expr const & e) {
    optional<expr> assoc_pr = m_ac_manager.is_assoc(e);
    if (!assoc_pr) return none_expr();
    optional<expr> comm_pr  = m_ac_manager.is_comm(e);
    if (!comm_pr) return none_expr();
    expr op = app_fn(app_fn(e));
    op = m_cc.get_defeq_canonizer().canonize(op);
    if (auto it = m_state.m_can_ops.find(op))
        return some_expr(*it);
    optional<expr> found_op;
    m_state.m_op_info.for_each([&](expr const & c_op, expr_pair const &) {
            if (!found_op && m_ctx.pure_relaxed_is_def_eq(op, c_op))
                found_op = c_op;
        });
    if (found_op) {
        m_state.m_can_ops.insert(op, *found_op);
        return found_op;
    } else {
        m_state.m_can_ops.insert(op, op);
        m_state.m_op_info.insert(op, mk_pair(*assoc_pr, *comm_pr));
        return some_expr(op);
    }
}

expr theory_ac::convert(expr const & op, expr const & e, buffer<expr> & args) {
    if (optional<expr> curr_op = is_ac(e)) {
        if (op == *curr_op) {
            expr arg1 = convert(op, app_arg(app_fn(e)), args);
            expr arg2 = convert(op, app_arg(e), args);
            return mk_app(op, arg1, arg2);
        }
    }

    internalize_var(e);
    args.push_back(e);
    return e;
}

bool theory_ac::internalize_var(expr const & e) {
    if (m_state.m_entries.contains(e)) return false;
    m_state.m_entries.insert(e, entry(m_state.m_next_idx));
    m_state.m_next_idx++;
    m_cc.set_ac_var(e);
    return true;
}

void theory_ac::dbg_trace_state() const {
    lean_trace(name({"debug", "cc", "ac"}), scope_trace_env s(m_ctx.env(), m_ctx);
               auto out = tout();
               auto fmt = out.get_formatter();
               out << group(format("state:") + nest(get_pp_indent(fmt.get_options()), line() + m_state.pp(fmt))) << "\n";);
}

void theory_ac::dbg_trace_eq(char const * header, expr const & lhs, expr const & rhs) const {
    lean_trace(name({"debug", "cc", "ac"}), scope_trace_env s(m_ctx.env(), m_ctx);
               auto out = tout();
               auto fmt = out.get_formatter();
               out << group(format(header) + line() + pp_term(fmt, lhs) + line() + format("=") + line() + pp_term(fmt, rhs)) << "\n";);
}

void theory_ac::internalize(expr const & e, optional<expr> const & parent) {
    auto op = is_ac(e);
    if (!op) return;
    optional<expr> parent_op;
    if (parent) parent_op = is_ac(*parent);
    if (parent_op && *op == *parent_op) return;

    if (!internalize_var(e)) return;

    buffer<expr> args;
    expr norm_e = convert(*op, e, args);
    expr rep    = mk_ac_app(*op, args);
    auto ac_prs = m_state.m_op_info.find(*op);
    lean_assert(ac_prs);
    expr pr     = mk_ac_refl_proof(m_ctx, norm_e, rep, ac_prs->first, ac_prs->second);

    lean_trace(name({"debug", "cc", "ac"}), scope_trace_env s(m_ctx.env(), m_ctx);
               auto out = tout();
               auto fmt = out.get_formatter();
               format d = group(paren(pp_term(fmt, e) + space() + format(":=") + line() + fmt(e)));
               format r = format("new term:") + line() + d + line() + format("===>") + line() + pp_term(fmt, rep);
               out << group(r) << "\n";);

    m_todo.emplace_back(e, rep, pr);
    process();
    dbg_trace_state();
}

void theory_ac::insert_erase_R_occ(expr const & arg, expr const & lhs, bool in_lhs, bool is_insert) {
    entry new_entry  = *m_state.m_entries.find(arg);
    occurrences occs = new_entry.get_R_occs(in_lhs);
    if (is_insert)
        occs.insert(lhs);
    else
        occs.erase(lhs);
    new_entry.set_R_occs(occs, in_lhs);
    m_state.m_entries.insert(arg, new_entry);
}

void theory_ac::insert_erase_R_occs(expr const & e, expr const & lhs, bool in_lhs, bool is_insert) {
    if (is_ac_app(e)) {
        unsigned nargs    = get_ac_app_num_args(e);
        expr const * args = get_ac_app_args(e);
        insert_erase_R_occ(args[0], lhs, in_lhs, is_insert);
        for (unsigned i = 1; i < nargs; i++) {
            if (args[i] != args[i-1])
                insert_erase_R_occ(args[i], lhs, in_lhs, is_insert);
        }
    } else {
        insert_erase_R_occ(e, lhs, in_lhs, is_insert);
    }
}

void theory_ac::insert_R_occs(expr const & e, expr const & lhs, bool in_lhs) {
    insert_erase_R_occs(e, lhs, in_lhs, true);
}

void theory_ac::erase_R_occs(expr const & e, expr const & lhs, bool in_lhs) {
    insert_erase_R_occs(e, lhs, in_lhs, false);
}

void theory_ac::insert_R_occs(expr const & lhs, expr const & rhs) {
    insert_R_occs(lhs, lhs, true);
    insert_R_occs(rhs, lhs, false);
}

void theory_ac::erase_R_occs(expr const & lhs, expr const & rhs) {
    erase_R_occs(lhs, lhs, true);
    erase_R_occs(rhs, lhs, false);
}

/*
  Given, e is of the form lhs*r, (H : lhs = rhs),
  return (rhs*r) and proof ac_simp_pr(e, lhs, rhs, r, rhs*r, H) : e = rhs*r
*/
expr_pair theory_ac::simplify_core(expr const & e, expr const & lhs, expr const & rhs, expr const & H) {
    lean_assert(is_ac_subset(lhs, e));
    if (e == lhs) {
        return mk_pair(rhs, H);
    } else {
        lean_assert(is_ac_app(e));
        expr dummy = mk_Prop();
        expr op    = get_ac_app_op(e);
        buffer<expr> new_args;
        ac_diff(e, lhs, new_args);
        expr r      = new_args.empty() ? dummy : mk_ac_app(op, new_args);
        ac_append(op, rhs, new_args);
        expr new_e  = mk_ac_app(op, new_args);
        auto ac_prs = m_state.m_op_info.find(op);
        lean_assert(ac_prs);
        expr new_pr = mk_ac_simp_proof(m_ctx, e, lhs, rhs, r, new_e, H, ac_prs->first, ac_prs->second);
        return mk_pair(new_e, new_pr);
    }
}

optional<expr_pair> theory_ac::simplify_step(expr const & e) {
    if (is_ac_app(e)) {
        unsigned nargs = get_ac_app_num_args(e);
        expr const * args = get_ac_app_args(e);
        for (unsigned i = 0; i < nargs; i++) {
            if (i == 0 || args[i] != args[i-1]) {
                occurrences const & occs = m_state.m_entries.find(args[i])->get_R_lhs_occs();
                optional<expr> R_lhs = occs.find_if([&](expr const & R_lhs) {
                        return is_ac_subset(R_lhs, e);
                    });
                if (R_lhs) {
                    expr_pair const * p = m_state.m_R.find(*R_lhs);
                    lean_assert(p);
                    expr R_rhs = p->first;
                    expr H     = p->second;
                    return optional<expr_pair>(simplify_core(e, *R_lhs, R_rhs, H));
                }
            }
        }
    } else if (expr_pair const * p = m_state.m_R.find(e)) {
        return optional<expr_pair>(*p);
    }
    return optional<expr_pair>();
}

optional<expr_pair> theory_ac::simplify(expr const & e) {
    optional<expr_pair> p = simplify_step(e);
    if (!p) return p;
    expr curr = p->first;
    expr pr   = p->second;
    while (optional<expr_pair> p = simplify_step(curr)) {
        expr new_curr = p->first;
        pr   = mk_eq_trans(m_ctx, e, curr, new_curr, pr, p->second);
        curr = new_curr;
    }
    return optional<expr_pair>(mk_pair(curr, pr));
}

unsigned theory_ac::state::get_num_R_occs(expr const & e, bool in_lhs) const {
    return m_entries.find(e)->m_R_occs[in_lhs].size();
}

expr theory_ac::state::get_var_with_least_occs(expr const & e, bool in_lhs) const {
    if (is_ac_app(e)) {
        unsigned nargs    = get_ac_app_num_args(e);
        expr const * args = get_ac_app_args(e);
        expr r            = args[0];
        unsigned num_occs = get_num_R_occs(r, in_lhs);
        for (unsigned i = 1; i < nargs; i++) {
            if (args[i] != args[i-1]) {
                unsigned curr_occs = get_num_R_occs(args[i], in_lhs);
                if (curr_occs < num_occs) {
                    r        = args[i];
                    num_occs = curr_occs;
                }
            }
        }
        return r;
    } else {
        return e;
    }
}

void theory_ac::compose_expr(expr const & lhs, expr const & rhs, expr const & H) {
    expr x           = m_state.get_var_with_least_rhs_occs(lhs);
    occurrences occs = m_state.m_entries.find(x)->get_R_rhs_occs();
    occs.for_each([&](expr const & R_lhs) {
            auto p = m_state.m_R.find(R_lhs);
            expr R_rhs = p->first;
            expr R_H  = p->second;
            if (is_ac_subset(lhs, R_rhs)) {
                expr new_R_rhs, R_rhs_eq_new_R_rhs;
                std::tie(new_R_rhs, R_rhs_eq_new_R_rhs) = simplify_core(R_rhs, lhs, rhs, H);
                expr new_R_H = mk_eq_trans(m_ctx, R_lhs, R_rhs, new_R_rhs, R_H, R_rhs_eq_new_R_rhs);
                m_state.m_R.insert(R_lhs, mk_pair(new_R_rhs, new_R_H));
                erase_R_rhs_occs(R_rhs, R_lhs);
                insert_R_rhs_occs(new_R_rhs, R_lhs);
                lean_trace(name({"debug", "cc", "ac"}), scope_trace_env s(m_ctx.env(), m_ctx);
                           auto out      = tout();
                           auto fmt      = out.get_formatter();
                           format old_rw = group(paren(pp_term(fmt, R_lhs) + line() + format("-->") + line() + pp_term(fmt, R_rhs)));
                           format new_rw = group(paren(pp_term(fmt, lhs) + line() + format("-->") + line() + pp_term(fmt, rhs)));
                           format r      = format("compose:");
                           r += nest(get_pp_indent(fmt.get_options()), line() + group(old_rw + line() + format("with") + line() + new_rw) +
                                     line() + format(":=") + line() + pp_term(fmt, new_R_rhs));
                           out << group(r) << "\n";);
            }
        });
}

void theory_ac::collapse(expr const & lhs, expr const & rhs, expr const & H) {
    expr x           = m_state.get_var_with_least_lhs_occs(lhs);
    occurrences occs = m_state.m_entries.find(x)->get_R_lhs_occs();
    occs.for_each([&](expr const & R_lhs) {
            if (is_ac_subset(lhs, R_lhs)) {
                expr R_rhs, R_H;
                std::tie(R_rhs, R_H) = *m_state.m_R.find(R_lhs);
                erase_R_occs(R_lhs, R_rhs);
                m_state.m_R.erase(R_lhs);
                expr new_R_lhs, R_lhs_eq_new_R_lhs;
                std::tie(new_R_lhs, R_lhs_eq_new_R_lhs) = simplify_core(R_lhs, lhs, rhs, H);
                expr new_R_lhs_eq_R_lhs = mk_eq_symm(m_ctx, R_lhs, new_R_lhs, R_lhs_eq_new_R_lhs);
                expr new_R_H            = mk_eq_trans(m_ctx, new_R_lhs, R_lhs, R_rhs, new_R_lhs_eq_R_lhs, R_H);
                m_todo.emplace_back(new_R_lhs, R_rhs, new_R_H);
                lean_trace(name({"debug", "cc", "ac"}), scope_trace_env s(m_ctx.env(), m_ctx);
                           auto out      = tout();
                           auto fmt      = out.get_formatter();
                           format new_rw = group(paren(pp_term(fmt, lhs) + line() + format("-->") + line() + pp_term(fmt, rhs)));
                           format old_rw = group(paren(pp_term(fmt, R_rhs) + line() + format("<--") + line() + pp_term(fmt, R_lhs)));
                           format r      = format("collapse:");
                           r += nest(get_pp_indent(fmt.get_options()), line() + group(new_rw + line() + format("at") + line() + old_rw) +
                                     line() + format(":=") + line() + pp_term(fmt, new_R_lhs));
                           out << group(r) << "\n";);
            }
        });
}

void theory_ac::superpose(expr const & ts, expr const & a, expr const & ts_eq_a) {
    if (!is_ac_app(ts)) return;
    expr const & op = get_ac_app_op(ts);
    unsigned nargs  = get_ac_app_num_args(ts);
    expr const * args = get_ac_app_args(ts);
    for (unsigned i = 0; i < nargs; i++) {
        if (i == 0 || args[i] != args[i-1]) {
            occurrences const & occs = m_state.m_entries.find(args[i])->get_R_lhs_occs();
            occs.for_each([&](expr const & tr) {
                    if (get_ac_app_op(tr) != op) return;
                    expr b, tr_eq_b;
                    std::tie(b, tr_eq_b) = *m_state.m_R.find(tr);
                    buffer<expr> t_args, s_args, r_args;
                    ac_intersection(ts, tr, t_args); lean_assert(!t_args.empty());
                    expr t = mk_ac_app(op, t_args);
                    ac_diff(ts, t, s_args); lean_assert(!s_args.empty());
                    ac_diff(tr, t, r_args); lean_assert(!r_args.empty());
                    expr s  = mk_ac_app(op, s_args);
                    expr r  = mk_ac_app(op, r_args);
                    expr ra = mk_ac_flat_app(op, r, a);
                    expr sb = mk_ac_flat_app(op, s, b);
                    auto ac_prs = m_state.m_op_info.find(op);
                    lean_assert(ac_prs);
                    expr ra_eq_sb = mk_ac_superpose_proof(m_ctx, ra, sb, a, b, r, s, ts, tr, ts_eq_a, tr_eq_b,
                                                          ac_prs->first, ac_prs->second);
                    m_todo.emplace_back(ra, sb, ra_eq_sb);
                    lean_trace(name({"debug", "cc", "ac"}), scope_trace_env s(m_ctx.env(), m_ctx);
                               auto out      = tout();
                               auto fmt      = out.get_formatter();
                               format rw1    = group(paren(pp_term(fmt, ts) + line() + format("-->") + line() + pp_term(fmt, a)));
                               format rw2    = group(paren(pp_term(fmt, tr) + line() + format("-->") + line() + pp_term(fmt, b)));
                               format eq     = group(paren(pp_term(fmt, ra) + line() + format("=") + line() + pp_term(fmt, sb)));
                               format r      = format("superpose:");
                               r += nest(get_pp_indent(fmt.get_options()), line() + group(rw1 + line() + format("with") + line() + rw2) +
                                         line() + format(":=") + line() + eq);
                               out << group(r) << "\n";);
                });
        }
    }
}

void theory_ac::process() {
    while (!m_todo.empty()) {
        expr lhs, rhs, H;
        std::tie(lhs, rhs, H) = m_todo.back();
        m_todo.pop_back();
        dbg_trace_eq("process eq:", lhs, rhs);
        expr lhs0 = lhs;
        expr rhs0 = rhs;

        /* Forward simplification lhs/rhs */
        if (optional<expr_pair> p = simplify(lhs)) {
            H  = mk_eq_trans(m_ctx, p->first, lhs, rhs, mk_eq_symm(m_ctx, lhs, p->first, p->second), H);
            lhs = p->first;
        }
        if (optional<expr_pair> p = simplify(rhs)) {
            H  = mk_eq_trans(m_ctx, lhs, rhs, p->first, H, p->second);
            rhs = p->first;
        }

        if (lhs != lhs0 || rhs != rhs0) {
            dbg_trace_eq("after simp:", lhs, rhs);
        }

        /* Check trivial */
        if (lhs == rhs) {
            lean_trace(name({"debug", "cc", "ac"}), tout() << "trivial\n";);
            continue;
        }

        /* Propagate new equality to congruence closure module */
        if (!is_ac_app(lhs) && !is_ac_app(rhs) && m_cc.get_root(lhs) != m_cc.get_root(rhs)) {
            m_cc.push_eq(lhs, rhs, mark_cc_theory_proof(H));
        }

        /* Orient */
        if (ac_lt(lhs, rhs)) {
            H = mk_eq_symm(m_ctx, lhs, rhs, H);
            std::swap(lhs, rhs);
        }

        /* Backward simplification */
        compose_expr(lhs, rhs, H);
        collapse(lhs, rhs, H);

        /* Superposition */
        superpose(lhs, rhs, H);

        /* Update R */
        m_state.m_R.insert(lhs, mk_pair(rhs, H));
        insert_R_occs(lhs, rhs);

        lean_trace(name({"debug", "cc", "ac"}), scope_trace_env s(m_ctx.env(), m_ctx);
                   auto out      = tout();
                   auto fmt      = out.get_formatter();
                   format new_rw = group(pp_term(fmt, lhs) + line() + format("-->") + line() + pp_term(fmt, rhs));
                   out << group(format("new rw:") + line() + new_rw) << "\n";);
    }
}

void theory_ac::add_eq(expr const & e1, expr const & e2) {
    dbg_trace_eq("cc eq:", e1, e2);
    m_todo.emplace_back(e1, e2, mk_delayed_cc_eq_proof(e1, e2));
    process();
    dbg_trace_state();
}

void initialize_theory_ac() {
    register_trace_class(name({"cc", "ac"}));
    register_trace_class(name({"debug", "cc", "ac"}));
}

void finalize_theory_ac() {
}
}
