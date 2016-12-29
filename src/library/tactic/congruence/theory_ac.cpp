/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <string>
#include "library/trace.h"
#include "library/app_builder.h"
#include "library/kernel_serializer.h"
#include "library/tactic/ac_tactics.h"
#include "library/tactic/congruence/util.h"
#include "library/tactic/congruence/congruence_closure.h"
#include "library/tactic/congruence/theory_ac.h"

/* TODO(Leo): reduce after testing */
#define AC_TRUST_LEVEL 10000000

namespace lean {
enum class ac_term_kind { App };

static name * g_ac_app_name = nullptr;
static macro_definition * g_ac_app_macro = nullptr;
static std::string * g_ac_app_opcode = nullptr;

static expr expand_ac_core(expr const & e) {
    unsigned nargs = macro_num_args(e);
    unsigned i     = nargs - 1;
    expr const & op = macro_arg(e, i);
    --i;
    expr r = macro_arg(e, i);
    while (i > 0) {
        --i;
        r = mk_app(op, macro_arg(e, i), r);
    }
    return r;
}

class ac_app_macro_cell : public macro_definition_cell {
public:
    virtual name get_name() const { return *g_ac_app_name; }

    virtual unsigned trust_level() const { return AC_TRUST_LEVEL; }

    virtual expr check_type(expr const & e, abstract_type_context & ctx, bool) const {
        return ctx.infer(macro_arg(e, 0));
    }

    virtual optional<expr> expand(expr const & e, abstract_type_context &) const {
        return some_expr(expand_ac_core(e));
    }

    virtual void write(serializer & s) const {
        s.write_string(*g_ac_app_opcode);
    }

    virtual bool operator==(macro_definition_cell const & other) const {
        ac_app_macro_cell const * other_ptr = dynamic_cast<ac_app_macro_cell const *>(&other);
        return other_ptr;
    }

    virtual unsigned hash() const { return 37; }
};

static expr mk_ac_app_core(unsigned nargs, expr const * args_op) {
    lean_assert(nargs >= 3);
    return mk_macro(*g_ac_app_macro, nargs, args_op);
}

static expr mk_ac_app_core(expr const & op, buffer<expr> & args) {
    lean_assert(args.size() >= 2);
    args.push_back(op);
    expr r = mk_ac_app_core(args.size(), args.data());
    args.pop_back();
    return r;
}

static expr mk_ac_app(expr const & op, buffer<expr> & args) {
    lean_assert(args.size() > 0);
    if (args.size() == 1) {
        return args[0];
    } else {
        std::sort(args.begin(), args.end(), is_hash_lt);
        return mk_ac_app_core(op, args);
    }
}

static bool is_ac_app(expr const & e) {
    return is_macro(e) && is_eqp(macro_def(e), *g_ac_app_macro);
}

static expr const & get_ac_app_op(expr const & e) {
    lean_assert(is_ac_app(e));
    return macro_arg(e, macro_num_args(e) - 1);
}

static unsigned get_ac_app_num_args(expr const & e) {
    lean_assert(is_ac_app(e));
    return macro_num_args(e) - 1;
}

static expr const * get_ac_app_args(expr const & e) {
    lean_assert(is_ac_app(e));
    return macro_args(e);
}

/* Return true iff e1 is a "subset" of e2.
   Example: The result is true for e1 := (a*a*a*b*d) and e2 := (a*a*a*a*b*b*c*d*d) */
static bool is_ac_subset(expr const & e1, expr const & e2) {
    if (is_ac_app(e1)) {
        if (is_ac_app(e2) && get_ac_app_op(e1) == get_ac_app_op(e2)) {
            unsigned nargs1 = get_ac_app_num_args(e1);
            unsigned nargs2 = get_ac_app_num_args(e2);
            if (nargs1 > nargs2) return false;
            expr const * args1 = get_ac_app_args(e1);
            expr const * args2 = get_ac_app_args(e2);
            unsigned i1 = 0;
            unsigned i2 = 0;
            while (i1 < nargs1 && i2 < nargs2) {
                if (args1[i1] == args2[i2]) {
                    i1++;
                    i2++;
                } else if (is_hash_lt(args2[i2], args1[i1])) {
                    i2++;
                } else {
                    lean_assert(is_hash_lt(args1[i1], args2[i2]));
                    return false;
                }
            }
            return i1 == nargs1;
        } else {
            return false;
        }
    } else {
        if (is_ac_app(e2)) {
            unsigned nargs2    = get_ac_app_num_args(e2);
            expr const * args2 = get_ac_app_args(e2);
            return std::find(args2, args2+nargs2, e1) != args2+nargs2;
        } else {
            return e1 == e2;
        }
    }
}

/* Store in r e1\e2.
   Example: given e1 := (a*a*a*a*b*b*c*d*d*d) and e2 := (a*a*a*b*b*d),
   the result is (a, c, d, d)

   \pre is_ac_subset(e2, e1) */
static void ac_diff(expr const & e1, expr const & e2, buffer<expr> & r) {
    lean_assert(is_ac_subset(e2, e1));
    if (is_ac_app(e1)) {
        if (is_ac_app(e2) && get_ac_app_op(e1) == get_ac_app_op(e2)) {
            unsigned nargs1 = get_ac_app_num_args(e1);
            unsigned nargs2 = get_ac_app_num_args(e2);
            lean_assert(nargs1 >= nargs2);
            expr const * args1 = get_ac_app_args(e1);
            expr const * args2 = get_ac_app_args(e2);
            unsigned i2 = 0;
            for (unsigned i1 = 0; i1 < nargs1; i1++) {
                if (i2 == nargs2) {
                    r.push_back(args1[i1]);
                } else if (args1[i1] == args2[i2]) {
                    i2++;
                } else {
                    lean_assert(is_hash_lt(args1[i1], args2[i2]));
                    r.push_back(args1[i1]);
                }
            }
        } else {
            bool found = false;
            unsigned nargs1    = get_ac_app_num_args(e1);
            expr const * args1 = get_ac_app_args(e1);
            for (unsigned i = 0; i < nargs1; i++) {
                if (!found && args1[i] == e2) {
                    found = true;
                } else {
                    r.push_back(args1[i]);
                }
            }
            lean_assert(found);
        }
    } else {
        lean_assert(!is_ac_app(e1));
        lean_assert(!is_ac_app(e2));
        lean_assert(e1 == e2);
    }
}

static void ac_append(expr const & e, buffer<expr> & r) {
    if (is_ac_app(e)) {
        r.append(get_ac_app_num_args(e), get_ac_app_args(e));
    } else {
        r.push_back(e);
    }
}

/* lexdeg order */
static bool ac_lt(expr const & e1, expr const & e2) {
    if (is_ac_app(e1)) {
        if (is_ac_app(e2) && get_ac_app_op(e1) == get_ac_app_op(e2)) {
            unsigned nargs1 = get_ac_app_num_args(e1);
            unsigned nargs2 = get_ac_app_num_args(e2);
            if (nargs1 < nargs2) return true;
            if (nargs1 > nargs2) return false;
            expr const * args1 = get_ac_app_args(e1);
            expr const * args2 = get_ac_app_args(e2);
            for (unsigned i = 0; i < nargs1; i++) {
                if (args1[i] != args2[i])
                    return is_hash_lt(args1[i], args2[i]);
            }
            return false;
        } else {
            return false;
        }
    } else {
        if (is_ac_app(e2)) {
            return true;
        } else {
            return is_hash_lt(e1, e2);
        }
    }
}

static expr expand_if_ac_app(expr const & e) {
    if (is_ac_app(e))
        return expand_ac_core(e);
    else
        return e;
}

static name * g_ac_simp_name = nullptr;
static macro_definition * g_ac_simp_macro = nullptr;
static std::string * g_ac_simp_opcode = nullptr;

class ac_simp_macro_cell : public macro_definition_cell {
public:
    virtual name get_name() const { return *g_ac_simp_name; }

    virtual expr check_type(expr const & e, abstract_type_context & ctx, bool) const {
        return mk_eq(ctx, macro_arg(e, 0), macro_arg(e, 3));
    }

    virtual unsigned trust_level() const { return AC_TRUST_LEVEL; }

    virtual optional<expr> expand(expr const & H, abstract_type_context & ctx) const {
        expr e      = expand_if_ac_app(macro_arg(H, 0)); /* it is of the form t*r */
        expr t      = expand_if_ac_app(macro_arg(H, 1));
        expr s      = expand_if_ac_app(macro_arg(H, 2));
        expr r      = expand_if_ac_app(macro_arg(H, 3));
        expr sr     = expand_if_ac_app(macro_arg(H, 4));
        expr t_eq_s = expand_if_ac_app(macro_arg(H, 5));
        expr const & assoc = macro_arg(H, 6);
        expr const & comm  = macro_arg(H, 7);
        if (e == sr) {
            return some_expr(mk_eq_refl(ctx, e));
        } else if (e == t) {
            lean_assert(s == sr);
            return some_expr(t_eq_s);
        } else {
            expr op       = app_fn(app_fn(e));
            expr op_r     = mk_app(op, r);
            expr rt       = mk_app(op_r, t);
            expr rs       = mk_app(op, r, s);
            expr rt_eq_rs = mk_congr_arg(ctx, op_r, t_eq_s);
            expr e_eq_rt  = perm_ac(ctx, op, assoc, comm, e, rt);
            expr rs_eq_sr = perm_ac(ctx, op, assoc, comm, rs, sr);
            return some_expr(mk_eq_trans(ctx, mk_eq_trans(ctx, e_eq_rt, rt_eq_rs), rs_eq_sr));
        }
    }

    virtual void write(serializer & s) const {
        s.write_string(*g_ac_simp_opcode);
    }

    virtual bool operator==(macro_definition_cell const & other) const {
        ac_simp_macro_cell const * other_ptr = dynamic_cast<ac_simp_macro_cell const *>(&other);
        return other_ptr;
    }

    virtual unsigned hash() const { return 31; }
};

/* Given e of the form t*r,  (pr : t = s) and s_r is of the form (s*r),
   return a proof for e = s_r */
static expr mk_ac_simp_proof(expr const & e, expr const & t, expr const & s, expr const & r, expr const & s_r, expr const & pr, expr const & assoc, expr const & comm) {
    expr args[8] = {e, t, s, r, s_r, pr, assoc, comm};
    return mk_macro(*g_ac_simp_macro, 8, args);
}

static name * g_ac_refl_name = nullptr;
static macro_definition * g_ac_refl_macro = nullptr;
static std::string * g_ac_refl_opcode = nullptr;

class ac_refl_macro_cell : public macro_definition_cell {
public:
    virtual name get_name() const { return *g_ac_refl_name; }

    virtual expr check_type(expr const & e, abstract_type_context & ctx, bool) const {
        return mk_eq(ctx, macro_arg(e, 0), macro_arg(e, 2));
    }

    virtual unsigned trust_level() const { return AC_TRUST_LEVEL; }

    virtual optional<expr> expand(expr const & e, abstract_type_context & ctx) const {
        expr const & t      = macro_arg(e, 0);
        expr ac_t           = macro_arg(e, 1);
        if (is_ac_app(ac_t))
            ac_t            = expand_ac_core(ac_t);
        expr const & op     = app_fn(app_fn(ac_t));
        expr const & assoc  = macro_arg(e, 2);
        expr const & comm   = macro_arg(e, 3);
        return some_expr(perm_ac(ctx, op, assoc, comm, t, ac_t));
    }

    virtual void write(serializer & s) const {
        s.write_string(*g_ac_refl_opcode);
    }

    virtual bool operator==(macro_definition_cell const & other) const {
        ac_refl_macro_cell const * other_ptr = dynamic_cast<ac_refl_macro_cell const *>(&other);
        return other_ptr;
    }

    virtual unsigned hash() const { return 31; }
};

/* Given e and ac_term that is provably equal to e using AC, return a proof for e = ac_term */
static expr mk_ac_refl_proof(expr const & e, expr const & ac_term, expr const & assoc, expr const & comm) {
    expr args[4] = {e, ac_term, assoc, comm};
    return mk_macro(*g_ac_refl_macro, 4, args);
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
            if (!found_op && m_ctx.relaxed_is_def_eq(op, c_op))
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
    expr pr     = mk_ac_refl_proof(norm_e, rep, ac_prs->first, ac_prs->second);

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
        insert_erase_R_occ(args[0], e, lhs, is_insert);
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
        ac_append(rhs, new_args);
        expr new_e  = mk_ac_app(op, new_args);
        auto ac_prs = m_state.m_op_info.find(op);
        lean_assert(ac_prs);
        expr new_pr = mk_ac_simp_proof(e, lhs, rhs, r, new_e, H, ac_prs->first, ac_prs->second);
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
                optional<expr> lhs = occs.find_if([&](expr const & t) {
                        return is_ac_subset(t, e);
                    });
                if (lhs) {
                    expr_pair const & p = *m_state.m_R.find(*lhs);
                    expr const & rhs = p.first;
                    expr const & H   = p.second;
                    return optional<expr_pair>(simplify_core(e, *lhs, rhs, H));
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

void theory_ac::compose(expr const & lhs, expr const & rhs, expr const & H) {
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
    // TODO(Leo)
}

void theory_ac::superpose(expr const & lhs, expr const & rhs, expr const & H) {
    // TODO(Leo)
}

void theory_ac::process() {
    while (!m_todo.empty()) {
        expr lhs, rhs, pr;
        std::tie(lhs, rhs, pr) = m_todo.back();
        m_todo.pop_back();
        dbg_trace_eq("process eq:", lhs, rhs);
        expr lhs0 = lhs;
        expr rhs0 = rhs;

        /* Simplify lhs/rhs */
        if (optional<expr_pair> p = simplify(lhs)) {
            pr  = mk_eq_trans(m_ctx, p->first, lhs, rhs, mk_eq_symm(m_ctx, lhs, p->first, p->second), pr);
            lhs = p->first;
        }
        if (optional<expr_pair> p = simplify(rhs)) {
            pr  = mk_eq_trans(m_ctx, lhs, rhs, p->first, pr, p->second);
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

        if (!is_ac_app(lhs) && !is_ac_app(rhs) && m_cc.get_root(lhs) != m_cc.get_root(rhs)) {
            /* Propagate new equality to congruence closure module */
            m_cc.push_new_eq(lhs, rhs, mark_cc_theory_proof(pr));
        }

        /* Orient */
        if (ac_lt(lhs, rhs)) {
            pr = mk_eq_symm(m_ctx, lhs, rhs, pr);
            std::swap(lhs, rhs);
        }

        /* Backward simplification */
        compose(lhs, rhs, pr);
        collapse(lhs, rhs, pr);

        /* Superposition */
        superpose(lhs, rhs, pr);

        /* Update R */
        m_state.m_R.insert(lhs, mk_pair(rhs, pr));
        insert_R_occs(lhs, rhs);
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

    g_ac_app_name   = new name("ac_app");
    g_ac_app_opcode = new std::string("ACApp");
    g_ac_app_macro  = new macro_definition(new ac_app_macro_cell());
    register_macro_deserializer(*g_ac_app_opcode,
                                [](deserializer &, unsigned num, expr const * args) {
                                    return mk_ac_app_core(num, args);
                                });

    g_ac_simp_name   = new name("ac_simp");
    g_ac_simp_opcode = new std::string("ACSimp");
    g_ac_simp_macro  = new macro_definition(new ac_simp_macro_cell());
    register_macro_deserializer(*g_ac_simp_opcode,
                                [](deserializer &, unsigned num, expr const * args) {
                                    if (num != 8) corrupted_stream_exception();
                                    return mk_ac_simp_proof(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7]);
                                });

    g_ac_refl_name   = new name("ac_refl");
    g_ac_refl_opcode = new std::string("ACRefl");
    g_ac_refl_macro  = new macro_definition(new ac_refl_macro_cell());
    register_macro_deserializer(*g_ac_refl_opcode,
                                [](deserializer &, unsigned num, expr const * args) {
                                    if (num != 4) corrupted_stream_exception();
                                    return mk_ac_refl_proof(args[0], args[1], args[2], args[3]);
                                });
}

void finalize_theory_ac() {
    delete g_ac_app_name;
    delete g_ac_app_opcode;
    delete g_ac_app_macro;

    delete g_ac_simp_name;
    delete g_ac_simp_opcode;
    delete g_ac_simp_macro;

    delete g_ac_refl_name;
    delete g_ac_refl_opcode;
    delete g_ac_refl_macro;
}
}
