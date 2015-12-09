/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <vector>
#include "kernel/abstract.h"
#include "library/trace.h"
#include "library/constants.h"
#include "library/blast/simplifier/simp_rule_set.h"
#include "library/blast/congruence_closure.h"
#include "library/blast/util.h"
#include "library/blast/blast.h"
#include "library/blast/trace.h"
#include "library/blast/options.h"

namespace lean {
namespace blast {
/* Not all user-defined congruence lemmas can be use by this module
   We cache the ones that can be used. */
struct congr_lemma_key {
    name     m_R;
    expr     m_fn;
    unsigned m_nargs;
    unsigned m_hash;
    congr_lemma_key(name const & R, expr const & fn, unsigned nargs):
        m_R(R), m_fn(fn), m_nargs(nargs),
        m_hash(hash(hash(R.hash(), fn.hash()), nargs)) {}
};

struct congr_lemma_key_hash_fn {
    unsigned operator()(congr_lemma_key const & k) const { return k.m_hash; }
};

struct congr_lemma_key_eq_fn {
    bool operator()(congr_lemma_key const & k1, congr_lemma_key const & k2) const {
        return k1.m_R == k2.m_R && k1.m_fn == k2.m_fn && k1.m_nargs == k2.m_nargs;
    }
};

static list<optional<name>> rel_names_from_arg_kinds(list<congr_arg_kind> const & kinds, name const & R) {
    return map2<optional<name>>(kinds, [&](congr_arg_kind k) {
            return k == congr_arg_kind::Eq ? optional<name>(R) : optional<name>();
        });
}

ext_congr_lemma::ext_congr_lemma(congr_lemma const & H):
    m_R(get_eq_name()),
    m_congr_lemma(H),
    m_rel_names(rel_names_from_arg_kinds(H.get_arg_kinds(), get_eq_name())),
    m_lift_needed(false),
    m_fixed_fun(true) {}
ext_congr_lemma::ext_congr_lemma(name const & R, congr_lemma const & H, bool lift_needed):
    m_R(R),
    m_congr_lemma(H),
    m_rel_names(rel_names_from_arg_kinds(H.get_arg_kinds(), get_eq_name())),
    m_lift_needed(lift_needed),
    m_fixed_fun(true) {}
ext_congr_lemma::ext_congr_lemma(name const & R, congr_lemma const & H, list<optional<name>> const & rel_names, bool lift_needed):
    m_R(R),
    m_congr_lemma(H),
    m_rel_names(rel_names),
    m_lift_needed(lift_needed),
    m_fixed_fun(true) {}

/* We use the following cache for user-defined lemmas and automatically generated ones. */
typedef std::unordered_map<congr_lemma_key, optional<ext_congr_lemma>, congr_lemma_key_hash_fn, congr_lemma_key_eq_fn> congr_cache;
typedef std::tuple<name, expr, expr, expr> cc_todo_entry;

static expr * g_congr_mark    = nullptr; // dummy congruence proof, it is just a placeholder.
static expr * g_iff_true_mark = nullptr; // dummy iff_true proof, it is just a placeholder.
static expr * g_lift_mark     = nullptr; // dummy lift eq proof, it is just a placeholder.

/* Small hack for not storing a pointer to the congruence_closure object
   at congruence_closure::congr_key_cmp */
LEAN_THREAD_PTR(congruence_closure, g_cc);

LEAN_THREAD_VALUE(congr_cache *, g_congr_cache, nullptr);

MK_THREAD_LOCAL_GET_DEF(std::vector<cc_todo_entry>, get_todo);

static void clear_todo() {
    get_todo().clear();
}

static void push_todo(name const & R, expr const & lhs, expr const & rhs, expr const & H) {
    get_todo().emplace_back(R, lhs, rhs, H);
}

scope_congruence_closure::scope_congruence_closure():
    m_old_cache(g_congr_cache) {
    g_congr_cache = new congr_cache();
}

scope_congruence_closure::~scope_congruence_closure() {
    delete g_congr_cache;
    g_congr_cache = static_cast<congr_cache*>(m_old_cache);
}

void congruence_closure::initialize() {
    mk_entry_core(get_iff_name(), mk_true(), false, true);
    mk_entry_core(get_iff_name(), mk_false(), false, true);
}

void congruence_closure::mk_entry_core(name const & R, expr const & e, bool to_propagate, bool interpreted) {
    lean_assert(!m_entries.find(eqc_key(R, e)));
    entry n;
    n.m_next         = e;
    n.m_root         = e;
    n.m_cg_root      = e;
    n.m_size         = 1;
    n.m_flipped      = false;
    n.m_interpreted  = interpreted;
    n.m_to_propagate = to_propagate;
    n.m_mt           = m_gmt;
    m_entries.insert(eqc_key(R, e), n);
    if (R != get_eq_name()) {
        // lift equalities to R
        auto n = m_entries.find(eqc_key(get_eq_name(), e));
        if (n) {
            // e has an eq equivalence class
            expr it = n->m_next;
            while (it != e) {
                if (m_entries.find(eqc_key(R, it))) {
                    push_todo(R, e, it, *g_lift_mark);
                    break;
                }
                auto it_n = m_entries.find(eqc_key(get_eq_name(), it));
                lean_assert(it_n);
                it = it_n->m_next;
            }
        }
    }
}

void congruence_closure::mk_entry(name const & R, expr const & e, bool to_propagate) {
    if (to_propagate && !is_prop(e))
        to_propagate = false;
    if (auto it = m_entries.find(eqc_key(R, e))) {
        if (!it->m_to_propagate && to_propagate) {
            entry new_it = *it;
            new_it.m_to_propagate = to_propagate;
            m_entries.insert(eqc_key(R, e), new_it);
        }
        return;
    }
    bool interpreted = false;
    mk_entry_core(R, e, to_propagate, interpreted);
}

static bool all_distinct(buffer<expr> const & es) {
    for (unsigned i = 0; i < es.size(); i++)
        for (unsigned j = i+1; j < es.size(); j++)
            if (es[i] == es[j])
                return false;
    return true;
}

/* Try to convert user-defined congruence rule into an ext_congr_lemma */
static optional<ext_congr_lemma> to_ext_congr_lemma(name const & R, expr const & fn, unsigned nargs, congr_rule const & r) {
    buffer<expr> lhs_args, rhs_args;
    expr const & lhs_fn = get_app_args(r.get_lhs(), lhs_args);
    expr const & rhs_fn = get_app_args(r.get_rhs(), rhs_args);
    if (nargs != lhs_args.size() || nargs != rhs_args.size()) {
        return optional<ext_congr_lemma>();
    }
    if (!all_distinct(lhs_args) || !all_distinct(rhs_args)) {
        return optional<ext_congr_lemma>();
    }
    blast_tmp_type_context ctx(r.get_num_umeta(), r.get_num_emeta());
    if (!ctx->is_def_eq(fn, lhs_fn) || !ctx->is_def_eq(fn, rhs_fn)) {
        return optional<ext_congr_lemma>();
    }
    for (unsigned i = 0; i < lhs_args.size(); i++) {
        if (has_expr_metavar(lhs_args[i])) {
            if (!ctx->is_mvar(lhs_args[i]) || !ctx->is_mvar(rhs_args[i])) {
                return optional<ext_congr_lemma>();
            }
        } else {
            // It is is not a simple meta-variable, then lhs and rhs must be the same
            if (lhs_args[i] != rhs_args[i]) {
                return optional<ext_congr_lemma>();
            }
        }
    }
    buffer<congr_arg_kind> kinds;
    buffer<optional<name>> Rcs;
    buffer<optional<expr>> r_hyps;
    kinds.resize(lhs_args.size(), congr_arg_kind::Cast);
    Rcs.resize(lhs_args.size(), optional<name>());
    r_hyps.resize(lhs_args.size(), none_expr());
    // Set Fixed args
    for (unsigned i = 0; i < lhs_args.size(); i++) {
        if (lhs_args[i] == rhs_args[i])
            kinds[i] = congr_arg_kind::Fixed;
    }
    // Set Eq args and child relations
    for (expr const & h : r.get_congr_hyps()) {
        if (!ctx->is_mvar(h)) {
            return optional<ext_congr_lemma>();
        }
        expr h_type = ctx->infer(h);
        name h_R; expr h_lhs, h_rhs;
        if (!is_equivalence_relation_app(h_type, h_R, h_lhs, h_rhs)) {
            return optional<ext_congr_lemma>();
        }
        bool found_lhs_rhs = false;
        for (unsigned i = 0; i < lhs_args.size(); i++) {
            if (kinds[i] == congr_arg_kind::Cast && // has not been marked yet
                lhs_args[i] == h_lhs && rhs_args[i] == h_rhs) {
                kinds[i]      = congr_arg_kind::Eq;
                Rcs[i]        = h_R;
                r_hyps[i]     = h;
                found_lhs_rhs = true;
                break;
            }
        }
        if (!found_lhs_rhs) {
            return optional<ext_congr_lemma>();
        }
    }
    buffer<expr> lemma_hyps;
    for (unsigned i = 0; i < lhs_args.size(); i++) {
        expr type = ctx->instantiate_uvars_mvars(ctx->infer(lhs_args[i]));
        if (has_expr_metavar(type)) {
            return optional<ext_congr_lemma>();
        }
        expr new_lhs = ctx->mk_tmp_local(type);
        lemma_hyps.push_back(new_lhs);
        if (!ctx->is_mvar(lhs_args[i])) {
            // This is a small hack... the argument is fixed, but we add an unnecessary hypothesis
            // just to make the lemma have the same "shape" of the automatically generated
            // congruence lemmas.
            // TODO(Leo): mark this kind of argument in the ext_congr_lemma and avoid the unnecessary
            // hypothesis. This option is also safer.
            continue;
        }
        if (!ctx->is_def_eq(lhs_args[i], new_lhs)) {
            return optional<ext_congr_lemma>();
        }
        switch (kinds[i]) {
        case congr_arg_kind::Fixed:
            break;
        case congr_arg_kind::Eq: {
            expr new_rhs = ctx->mk_tmp_local(type);
            if (!ctx->is_def_eq(rhs_args[i], new_rhs)) {
                return optional<ext_congr_lemma>();
            }
            lean_assert(r_hyps[i]);
            expr new_hyp = ctx->mk_tmp_local(ctx->instantiate_uvars_mvars(ctx->infer(*r_hyps[i])));
            if (!ctx->is_def_eq(*r_hyps[i], new_hyp)) {
                return optional<ext_congr_lemma>();
            }
            lemma_hyps.push_back(new_rhs);
            lemma_hyps.push_back(new_hyp);
            break;
        }
        case congr_arg_kind::Cast: {
            expr rhs_type = ctx->instantiate_uvars_mvars(ctx->infer(rhs_args[i]));
            if (has_expr_metavar(rhs_type))
                return optional<ext_congr_lemma>();
            expr new_rhs = ctx->mk_tmp_local(rhs_type);
            if (!ctx->is_def_eq(rhs_args[i], new_rhs))
                return optional<ext_congr_lemma>();
            lemma_hyps.push_back(new_rhs);
            break;
        }}
    }
    expr new_proof = ctx->instantiate_uvars_mvars(r.get_proof());
    if (has_expr_metavar(new_proof)) {
        return optional<ext_congr_lemma>();
    }
    new_proof = Fun(lemma_hyps, new_proof);
    expr new_type  = ctx->infer(new_proof);
    congr_lemma new_lemma(new_type, new_proof, to_list(kinds));
    bool lift_needed = false;
    return optional<ext_congr_lemma>(R, new_lemma, to_list(Rcs), lift_needed);
}

static optional<ext_congr_lemma> mk_ext_congr_lemma_core(name const & R, expr const & fn, unsigned nargs) {
    simp_rule_set const * sr = get_simp_rule_sets(env()).find(R);
    if (sr) {
        list<congr_rule> const * crs = sr->find_congr(fn);
        if (crs) {
            for (congr_rule const & r : *crs) {
                if (auto lemma = to_ext_congr_lemma(R, fn, nargs, r))
                    return lemma;
            }
        }
    }

    // Automatically generated lemma for equivalence relation over iff/eq
    if (auto info = is_relation(fn)) {
        if (info->get_arity() == nargs) {
            if (R == get_iff_name()) {
                if (optional<congr_lemma> cgr = mk_rel_iff_congr(fn)) {
                    auto child_rel_names = rel_names_from_arg_kinds(cgr->get_arg_kinds(), const_name(fn));
                    return optional<ext_congr_lemma>(R, *cgr, child_rel_names, false);
                }
            }
            if (optional<congr_lemma> cgr = mk_rel_eq_congr(fn)) {
                auto child_rel_names = rel_names_from_arg_kinds(cgr->get_arg_kinds(), const_name(fn));
                bool lift_needed     = R != get_eq_name();
                return optional<ext_congr_lemma>(R, *cgr, child_rel_names, lift_needed);
            }
        }
    }

    // Automatically generated lemma
    optional<congr_lemma> eq_congr = mk_congr_lemma(fn, nargs);
    if (!eq_congr)
        return optional<ext_congr_lemma>();
    ext_congr_lemma res1(*eq_congr);
    // If all arguments are Eq kind, then we can use generic congr axiom and consider equality for the function.
    if (eq_congr->all_eq_kind())
        res1.m_fixed_fun = false;
    if (R == get_eq_name())
        return optional<ext_congr_lemma>(res1);
    bool lift_needed = true;
    return optional<ext_congr_lemma>(R, *eq_congr, lift_needed);
}

optional<ext_congr_lemma> mk_ext_congr_lemma(name const & R, expr const & fn, unsigned nargs) {
    congr_lemma_key key(R, fn, nargs);
    auto it = g_congr_cache->find(key);
    if (it != g_congr_cache->end())
        return it->second;
    auto r = mk_ext_congr_lemma_core(R, fn, nargs);
    g_congr_cache->insert(mk_pair(key, r));
    return r;
}

void congruence_closure::update_non_eq_relations(name const & R) {
    if (R == get_eq_name())
        return;
    if (std::find(m_non_eq_relations.begin(), m_non_eq_relations.end(), R) == m_non_eq_relations.end())
        m_non_eq_relations = cons(R, m_non_eq_relations);
}

void congruence_closure::add_occurrence(name const & Rp, expr const & parent, name const & Rc, expr const & child) {
    child_key k(Rc, child);
    parent_occ_set ps;
    if (auto old_ps = m_parents.find(k))
        ps = *old_ps;
    ps.insert(parent_occ(Rp, parent));
    m_parents.insert(k, ps);
}

/* Auxiliary function for comparing (lhs1 ~ rhs1) and (lhs2 ~ rhs2),
   when ~ is symmetric.
   It returns 0 (equal) for (a ~ b) (b ~ a) */
int congruence_closure::compare_symm(name const & R, expr lhs1, expr rhs1, expr lhs2, expr rhs2) const {
    lhs1 = get_root(R, lhs1);
    rhs1 = get_root(R, rhs1);
    lhs2 = get_root(R, lhs2);
    rhs2 = get_root(R, rhs2);
    if (is_lt(lhs1, rhs1, true))
        std::swap(lhs1, rhs1);
    if (is_lt(lhs2, rhs2, true))
        std::swap(lhs2, rhs2);
    if (lhs1 != lhs2)
        return is_lt(lhs1, lhs2, true) ? -1 : 1;
    if (rhs1 != rhs2)
        return is_lt(rhs1, rhs2, true) ? -1 : 1;
    return 0;
}

int congruence_closure::compare_root(name const & R, expr e1, expr e2) const {
    e1 = get_root(R, e1);
    e2 = get_root(R, e2);
    return expr_quick_cmp()(e1, e2);
}

int congruence_closure::congr_key_cmp::operator()(congr_key const & k1, congr_key const & k2) const {
    if (k1.m_hash != k2.m_hash)
        return unsigned_cmp()(k1.m_hash, k2.m_hash);
    if (k1.m_R != k2.m_R)
        return quick_cmp(k1.m_R, k2.m_R);
    if (k1.m_eq != k2.m_eq)
        return k1.m_eq ? -1 : 1;
    if (k2.m_iff != k2.m_iff)
        return k1.m_iff ? -1 : 1;
    if (k2.m_symm_rel != k2.m_symm_rel)
        return k1.m_symm_rel ? -1 : 1;
    if (k1.m_eq || k1.m_iff) {
        name const & R = k1.m_eq ? get_eq_name() : get_iff_name();
        expr const & lhs1 = app_arg(app_fn(k1.m_expr));
        expr const & rhs1 = app_arg(k1.m_expr);
        expr const & lhs2 = app_arg(app_fn(k2.m_expr));
        expr const & rhs2 = app_arg(k2.m_expr);
        return g_cc->compare_symm(R, lhs1, rhs1, lhs2, rhs2);
    } else if (k1.m_symm_rel) {
        name R1, R2;
        expr lhs1, rhs1, lhs2, rhs2;
        lean_verify(is_equivalence_relation_app(k1.m_expr, R1, lhs1, rhs1));
        lean_verify(is_equivalence_relation_app(k2.m_expr, R2, lhs2, rhs2));
        if (R1 != R2)
            return quick_cmp(R1, R2);
        return g_cc->compare_symm(R1, lhs1, rhs1, lhs2, rhs2);
    } else {
        lean_assert(!k1.m_eq && !k2.m_eq && !k1.m_iff && !k2.m_iff &&
                    !k1.m_symm_rel && !k2.m_symm_rel);
        lean_assert(k1.m_R == k2.m_R);
        buffer<expr> args1, args2;
        expr const & fn1 = get_app_args(k1.m_expr, args1);
        expr const & fn2 = get_app_args(k2.m_expr, args2);
        if (args1.size() != args2.size())
            return unsigned_cmp()(args1.size(), args2.size());
        auto lemma = mk_ext_congr_lemma(k1.m_R, fn1, args1.size());
        lean_assert(lemma);
        if (!lemma->m_fixed_fun) {
            int r = g_cc->compare_root(get_eq_name(), fn1, fn2);
            if (r != 0) return r;
            for (unsigned i = 0; i < args1.size(); i++) {
                r = g_cc->compare_root(get_eq_name(), args1[i], args2[i]);
                if (r != 0) return r;
            }
            return 0;
        } else {
            list<optional<name>> const * it1 = &lemma->m_rel_names;
            list<congr_arg_kind> const * it2 = &lemma->m_congr_lemma.get_arg_kinds();
            int r;
            for (unsigned i = 0; i < args1.size(); i++) {
                lean_assert(*it1); lean_assert(*it2);
                switch (head(*it2)) {
                case congr_arg_kind::Eq:
                    lean_assert(head(*it1));
                    r = g_cc->compare_root(*head(*it1), args1[i], args2[i]);
                    if (r != 0) return r;
                    break;
                case congr_arg_kind::Fixed:
                    r = expr_quick_cmp()(args1[i], args2[i]);
                    if (r != 0) return r;
                    break;
                case congr_arg_kind::Cast:
                    // do nothing... ignore argument
                    break;
                }
                it1 = &(tail(*it1));
                it2 = &(tail(*it2));
            }
            return 0;
        }
    }
}

unsigned congruence_closure::symm_hash(name const & R, expr const & lhs, expr const & rhs) const {
    unsigned h1 = get_root(R, lhs).hash();
    unsigned h2 = get_root(R, rhs).hash();
    if (h1 > h2)
        std::swap(h1, h2);
    return (h1 << 16) | (h2 & 0xFFFF);
}

auto congruence_closure::mk_congr_key(ext_congr_lemma const & lemma, expr const & e) const -> congr_key {
    congr_key k;
    k.m_R    = lemma.m_R;
    k.m_expr = e;
    lean_assert(is_app(e));
    bool std = is_standard(env());
    name R; expr lhs, rhs;
    if (std && is_eq(e, lhs, rhs)) {
        k.m_eq   = true;
        k.m_hash = symm_hash(get_eq_name(), lhs, rhs);
    } else if (std && is_iff(e, lhs, rhs)) {
        k.m_iff  = true;
        k.m_hash = symm_hash(get_iff_name(), lhs, rhs);
    } else if (std && is_equivalence_relation_app(e, R, lhs, rhs) && is_symmetric(R)) {
        k.m_symm_rel = true;
        k.m_hash = symm_hash(R, lhs, rhs);
    } else {
        buffer<expr> args;
        expr const & fn = get_app_args(e, args);
        if (!lemma.m_fixed_fun) {
            unsigned h = get_root(get_eq_name(), fn).hash();
            for (unsigned i = 0; i < args.size(); i++)  {
                h = hash(h, get_root(get_eq_name(), args[i]).hash());
            }
            k.m_hash = h;
        } else {
            unsigned h = fn.hash();
            list<optional<name>> const * it1 = &lemma.m_rel_names;
            list<congr_arg_kind> const * it2 = &lemma.m_congr_lemma.get_arg_kinds();
            for (unsigned i = 0; i < args.size(); i++) {
                lean_assert(*it1); lean_assert(*it2);
                switch (head(*it2)) {
                case congr_arg_kind::Eq:
                    lean_assert(head(*it1));
                    h = hash(h, get_root(*head(*it1), args[i]).hash());
                    break;
                case congr_arg_kind::Fixed:
                    h = hash(h, args[i].hash());
                    break;
                case congr_arg_kind::Cast:
                    // do nothing... ignore argument
                    break;
                }
                it1 = &(tail(*it1));
                it2 = &(tail(*it2));
            }
            k.m_hash = h;
        }
    }
    return k;
}

void congruence_closure::check_iff_true(congr_key const & k) {
    expr const & e = k.m_expr;
    name R; expr lhs, rhs;
    if (k.m_eq || k.m_iff) {
        R   = k.m_eq ? get_eq_name() : get_iff_name();
        lhs = app_arg(app_fn(e));
        rhs = app_arg(e);
    } else if (k.m_symm_rel) {
        lean_verify(is_equivalence_relation_app(e, R, lhs, rhs));
    } else {
        return;
    }
    if (is_eqv(get_iff_name(), e, mk_true()))
        return; // it is already equivalent to true
    lhs = get_root(R, lhs);
    rhs = get_root(R, rhs);
    if (lhs != rhs)
        return;
    // Add e <-> true
    push_todo(get_iff_name(), e, mk_true(), *g_iff_true_mark);
}

void congruence_closure::add_congruence_table(ext_congr_lemma const & lemma, expr const & e) {
    lean_assert(is_app(e));
    congr_key k = mk_congr_key(lemma, e);
    if (auto old_k = m_congruences.find(k)) {
        // Found new equivalence: e ~ old_k->m_expr
        // 1. Update m_cg_root field for e
        eqc_key k(lemma.m_R, e);
        entry new_entry = *m_entries.find(k);
        new_entry.m_cg_root = old_k->m_expr;
        m_entries.insert(k, new_entry);
        // 2. Put new equivalence in the TODO queue
        push_todo(lemma.m_R, e, old_k->m_expr, *g_congr_mark);
    } else {
        m_congruences.insert(k);
    }
    check_iff_true(k);
}

static bool is_logical_app(expr const & n) {
    if (!is_app(n)) return false;
    expr const & fn = get_app_fn(n);
    return
        is_constant(fn) &&
        (const_name(fn) == get_or_name()  ||
         const_name(fn) == get_and_name() ||
         const_name(fn) == get_not_name() ||
         const_name(fn) == get_iff_name() ||
         (const_name(fn) == get_ite_name() && is_prop(n)));
}

void congruence_closure::internalize_core(name const & R, expr const & e, bool toplevel, bool to_propagate) {
    lean_assert(closed(e));
    // we allow metavariables after partitions have been frozen
    if (has_expr_metavar(e) && !m_froze_partitions)
        return;
    if (m_entries.find(eqc_key(R, e)))
        return; // e has already been internalized
    update_non_eq_relations(R);
    switch (e.kind()) {
    case expr_kind::Var:
        lean_unreachable();
    case expr_kind::Sort:
        return;
    case expr_kind::Constant: case expr_kind::Local:
    case expr_kind::Meta:
        mk_entry_core(R, e, to_propagate, false);
        return;
    case expr_kind::Lambda:
        mk_entry_core(R, e, false, false);
        return;
    case expr_kind::Macro:
        for (unsigned i = 0; i < macro_num_args(e); i++)
            internalize_core(R, macro_arg(e, i), false, false);
        mk_entry_core(R, e, to_propagate, false);
        break;
    case expr_kind::Pi:
        // TODO(Leo): should we support congruence for arrows?
        if (is_arrow(e) && is_prop(binding_domain(e)) && is_prop(binding_body(e))) {
            to_propagate = toplevel; // we must propagate children if arrow is top-level
            internalize_core(R, binding_domain(e), toplevel, to_propagate);
            internalize_core(R, binding_body(e), toplevel, to_propagate);
        }
        if (is_prop(e)) {
            mk_entry_core(R, e, false, false);
        }
        return;
    case expr_kind::App: {
        bool is_lapp = is_logical_app(e);
        mk_entry_core(R, e, to_propagate && !is_lapp, false);
        buffer<expr> args;
        expr const & fn = get_app_args(e, args);
        if (toplevel) {
            if (is_lapp) {
                to_propagate = true; // we must propagate the children of a top-level logical app (or, and, iff, ite)
            } else {
                toplevel = false;    // children of a non-logical application will not be marked as toplevel
            }
        } else {
            to_propagate = false;
        }
        if (auto lemma = mk_ext_congr_lemma(R, fn, args.size())) {
            list<optional<name>> const * it = &(lemma->m_rel_names);
            for (expr const & arg : args) {
                lean_assert(*it);
                if (auto R1 = head(*it)) {
                    internalize_core(*R1, arg, toplevel, to_propagate);
                    add_occurrence(R, e, *R1, arg);
                }
                it = &tail(*it);
            }
            if (!lemma->m_fixed_fun) {
                internalize_core(get_eq_name(), fn, false, false);
                add_occurrence(get_eq_name(), e, get_eq_name(), fn);
            }
            add_congruence_table(*lemma, e);
        }
        break;
    }}
}

void congruence_closure::internalize(name const & R, expr const & e, bool toplevel) {
    flet<congruence_closure *> set_cc(g_cc, this);
    bool to_propagate = false; // We don't need to mark units for propagation
    internalize_core(R, e, toplevel, to_propagate);
    process_todo(none_expr());
}

void congruence_closure::internalize(expr const & e) {
    if (is_prop(e))
        internalize(get_iff_name(), e, true);
    else
        internalize(get_eq_name(), e, false);
}

/*
  The fields m_target and m_proof in e's entry are encoding a transitivity proof
  Let target(e) and proof(e) denote these fields.

  e    = target(e)           :  proof(e)
   ... = target(target(e))   :  proof(target(e))
   ... ...
       = root(e)             : ...

  The transitivity proof eventually reaches the root of the equivalence class.
  This method "inverts" the proof. That is, the m_target goes from root(e) to e after
  we execute it.
*/
void congruence_closure::invert_trans(name const & R, expr const & e, bool new_flipped, optional<expr> new_target, optional<expr> new_proof) {
    eqc_key k(R, e);
    auto n = m_entries.find(k);
    lean_assert(n);
    entry new_n = *n;
    if (n->m_target)
        invert_trans(R, *new_n.m_target, !new_n.m_flipped, some_expr(e), new_n.m_proof);
    new_n.m_target  = new_target;
    new_n.m_proof   = new_proof;
    new_n.m_flipped = new_flipped;
    m_entries.insert(k, new_n);
}
void congruence_closure::invert_trans(name const & R, expr const & e) {
    invert_trans(R, e, false, none_expr(), none_expr());
}

void congruence_closure::remove_parents(name const & R, expr const & e) {
    auto ps = m_parents.find(child_key(R, e));
    if (!ps) return;
    ps->for_each([&](parent_occ const & p) {
            expr const & fn = get_app_fn(p.m_expr);
            unsigned nargs  = get_app_num_args(p.m_expr);
            auto lemma = mk_ext_congr_lemma(p.m_R, fn, nargs);
            lean_assert(lemma);
            congr_key k = mk_congr_key(*lemma, p.m_expr);
            m_congruences.erase(k);
        });
}

void congruence_closure::reinsert_parents(name const & R, expr const & e) {
    auto ps = m_parents.find(child_key(R, e));
    if (!ps) return;
    ps->for_each([&](parent_occ const & p) {
            expr const & fn = get_app_fn(p.m_expr);
            unsigned nargs  = get_app_num_args(p.m_expr);
            auto lemma = mk_ext_congr_lemma(p.m_R, fn, nargs);
            lean_assert(lemma);
            add_congruence_table(*lemma, p.m_expr);
        });
}

void congruence_closure::update_mt(name const & R, expr const & e) {
    expr r  = get_root(R, e);
    auto ps = m_parents.find(child_key(R, r));
    if (!ps) return;
    ps->for_each([&](parent_occ const & p) {
            auto it = m_entries.find(p);
            lean_assert(it);
            if (it->m_mt < m_gmt) {
                auto new_it = *it;
                new_it.m_mt = m_gmt;
                m_entries.insert(p, new_it);
                update_mt(p.m_R, p.m_expr);
            }
        });
}

static bool is_true_or_false(expr const & e) {
    return is_constant(e, get_true_name()) || is_constant(e, get_false_name());
}

/* Remark: If added_prop is not none, then it contains the proposition provided to ::add.
   We use it here to avoid an unnecessary propagation back to the current_state. */
void congruence_closure::add_eqv_step(name const & R, expr e1, expr e2, expr const & H, optional<expr> const & added_prop) {
    auto n1 = m_entries.find(eqc_key(R, e1));
    auto n2 = m_entries.find(eqc_key(R, e2));
    if (!n1 || !n2)
        return;
    if (n1->m_root == n2->m_root)
        return; // they are already in the same equivalence class
    auto r1 = m_entries.find(eqc_key(R, n1->m_root));
    auto r2 = m_entries.find(eqc_key(R, n2->m_root));
    lean_assert(r1 && r2);
    bool flipped = false;

    // We want r2 to be the root of the combined class.

    // We swap (e1,n1,r1) with (e2,n2,r2) when
    // 1- is_interpreted(n1->m_root) && !is_interpreted(n2->m_root).
    //    Reason: to decide when to propagate we check whether the root of the equivalence class
    //    is true/false. So, this condition is to make sure if true/false is an equivalence class,
    //    then one of them is the root. If both are, it doesn't matter, since the state is inconsistent
    //    anyway.
    // 2- r1->m_size > r2->m_size
    //    Reason: performance. Condition was has precedence
    if ((r1->m_size > r2->m_size && !r2->m_interpreted) || r1->m_interpreted) {
        std::swap(e1, e2);
        std::swap(n1, n2);
        std::swap(r1, r2);
        // Remark: we don't apply symmetry eagerly. So, we don't adjust H.
        flipped = true;
    }

    if (r1->m_interpreted && r2->m_interpreted)
        m_inconsistent = true;

    expr e1_root   = n1->m_root;
    expr e2_root   = n2->m_root;
    entry new_n1   = *n1;

    // Following target/proof we have
    // e1 -> ... -> r1
    // e2 -> ... -> r2
    // We want
    // r1 -> ... -> e1 -> e2 -> ... -> r2
    invert_trans(R, e1);
    new_n1.m_target  = e2;
    new_n1.m_proof   = H;
    new_n1.m_flipped = flipped;
    m_entries.insert(eqc_key(R, e1), new_n1);

    // The hash code for the parents is going to change
    remove_parents(R, e1_root);

    // force all m_root fields in e1 equivalence class to point to e2_root
    bool propagate = R == get_iff_name() && is_true_or_false(e2_root);
    buffer<expr> to_propagate;
    expr it = e1;
    do {
        auto it_n = m_entries.find(eqc_key(R, it));
        if (propagate && it_n->m_to_propagate)
            to_propagate.push_back(it);
        lean_assert(it_n);
        entry new_it_n   = *it_n;
        new_it_n.m_root = e2_root;
        m_entries.insert(eqc_key(R, it), new_it_n);
        it = new_it_n.m_next;
    } while (it != e1);

    reinsert_parents(R, e1_root);

    // update next of e1_root and e2_root, and size of e2_root
    r1 = m_entries.find(eqc_key(R, e1_root));
    r2 = m_entries.find(eqc_key(R, e2_root));
    lean_assert(r1 && r2);
    lean_assert(r1->m_root == e2_root);
    entry new_r1   = *r1;
    entry new_r2   = *r2;
    new_r1.m_next  = r2->m_next;
    new_r2.m_next  = r1->m_next;
    new_r2.m_size += r1->m_size;
    m_entries.insert(eqc_key(R, e1_root), new_r1);
    m_entries.insert(eqc_key(R, e2_root), new_r2);
    lean_assert(check_invariant());

    // copy e1_root parents to e2_root
    child_key k1(R, e1_root);
    auto ps1 = m_parents.find(k1);
    if (ps1) {
        parent_occ_set ps2;
        child_key k2(R, e2_root);
        if (auto it = m_parents.find(k2))
            ps2 = *it;
        ps1->for_each([&](parent_occ const & p) {
                if (is_congr_root(p.m_R, p.m_expr))
                    ps2.insert(p);
            });
        m_parents.erase(k1);
        m_parents.insert(k2, ps2);
    }

    // lift equivalence
    if (R == get_eq_name()) {
        for (name const & R2 : m_non_eq_relations) {
            if (m_entries.find(eqc_key(R2, e1)) ||
                m_entries.find(eqc_key(R2, e2))) {
                mk_entry(R2, e1, false);
                mk_entry(R2, e2, false);
                push_todo(R2, e1, e2, *g_lift_mark);
            }
        }
    }

    // propagate new hypotheses back to current state
    if (!to_propagate.empty()) {
        state & s       = curr_state();
        app_builder & b = get_app_builder();
        bool is_true    = e2_root == mk_true();
        for (expr const & e : to_propagate) {
            lean_assert(R == get_iff_name());
            expr type = e;
            if ((!added_prop || *added_prop != type) && !s.contains_hypothesis(type)) {
                expr pr   = *get_eqv_proof(R, e, e2_root);
                if (is_true) {
                    pr = b.mk_of_iff_true(pr);
                } else {
                    type = b.mk_not(e);
                    pr   = b.mk_not_of_iff_false(pr);
                }
                expr H = s.mk_hypothesis(type, pr);
                lean_trace(name({"cc", "propagation"}),
                           tout() << ppb(H) << " : " << ppb(infer_type(H)) << "\n";);
            }
        }
    }

    update_mt(R, e2_root);

    lean_trace(name({"cc", "merge"}), tout() << ppb(e1) << " [" << R << "] " << ppb(e2) << "\n";);
    lean_trace(name({"cc", "state"}), trace(););
}

void congruence_closure::process_todo(optional<expr> const & added_prop) {
    auto & todo = get_todo();
    while (!todo.empty()) {
        name R; expr lhs, rhs, H;
        std::tie(R, lhs, rhs, H) = todo.back();
        todo.pop_back();
        add_eqv_step(R, lhs, rhs, H, added_prop);
    }
}

void congruence_closure::add_eqv_core(name const & R, expr const & lhs, expr const & rhs, expr const & H, optional<expr> const & added_prop) {
    push_todo(R, lhs, rhs, H);
    process_todo(added_prop);
}

void congruence_closure::add_eqv(name const & R, expr const & lhs, expr const & rhs, expr const & H) {
    if (is_inconsistent())
        return;
    flet<congruence_closure *> set_cc(g_cc, this);
    clear_todo();
    bool toplevel = false; bool to_propagate = false;
    internalize_core(R, lhs, toplevel, to_propagate);
    internalize_core(R, rhs, toplevel, to_propagate);
    add_eqv_core(R, lhs, rhs, H, none_expr());
}

void congruence_closure::add(hypothesis_idx hidx) {
    state & s            = curr_state();
    hypothesis const & h = s.get_hypothesis_decl(hidx);
    add(h.get_type(), h.get_self());
}

void congruence_closure::assume(expr const & type) {
    lean_assert(m_froze_partitions);
    expr dummy = mk_true_intro();
    add(type, dummy);
}

expr congruence_closure::mk_iff_false_intro(expr const & proof) {
    return m_froze_partitions ? proof : get_app_builder().mk_iff_false_intro(proof);
}

expr congruence_closure::mk_iff_true_intro(expr const & proof) {
    return m_froze_partitions ? proof : get_app_builder().mk_iff_true_intro(proof);
}

void congruence_closure::add(expr const & type, expr const & proof) {
    if (is_inconsistent())
        return;
    flet<congruence_closure *> set_cc(g_cc, this);
    clear_todo();
    expr p      = type;
    bool is_neg = is_not(type, p);
    if (is_neg && !is_standard(env()))
        return;
    name R; expr lhs, rhs;
    if (is_equivalence_relation_app(p, R, lhs, rhs)) {
        if (is_neg) {
            bool toplevel = true; bool to_propagate = false;
            internalize_core(get_iff_name(), p, toplevel, to_propagate);
            add_eqv_core(get_iff_name(), p, mk_false(), mk_iff_false_intro(proof), some_expr(type));
        } else {
            bool toplevel = false; bool to_propagate = false;
            internalize_core(R, lhs, toplevel, to_propagate);
            internalize_core(R, rhs, toplevel, to_propagate);
            add_eqv_core(R, lhs, rhs, proof, some_expr(type));
        }
    } else if (is_prop(p)) {
        bool toplevel = true; bool to_propagate = false;
        internalize_core(get_iff_name(), p, toplevel, to_propagate);
        if (is_neg) {
            add_eqv_core(get_iff_name(), p, mk_false(), mk_iff_false_intro(proof), some_expr(type));
        } else {
            add_eqv_core(get_iff_name(), p, mk_true(), mk_iff_true_intro(proof), some_expr(type));
        }
    }
}

bool congruence_closure::is_eqv(name const & R, expr const & e1, expr const & e2) const {
    auto n1 = m_entries.find(eqc_key(R, e1));
    if (!n1) return false;
    auto n2 = m_entries.find(eqc_key(R, e2));
    if (!n2) return false;
    return n1->m_root == n2->m_root;
}

expr congruence_closure::mk_congr_proof_core(name const & R, expr const & lhs, expr const & rhs) const {
    app_builder & b = get_app_builder();
    buffer<expr> lhs_args, rhs_args;
    expr const & lhs_fn = get_app_args(lhs, lhs_args);
    expr const & rhs_fn = get_app_args(rhs, rhs_args);
    lean_assert(lhs_args.size() == rhs_args.size());
    auto lemma = mk_ext_congr_lemma(R, lhs_fn, lhs_args.size());
    lean_assert(lemma);
    if (lemma->m_fixed_fun) {
        list<optional<name>> const * it1 = &lemma->m_rel_names;
        list<congr_arg_kind> const * it2 = &lemma->m_congr_lemma.get_arg_kinds();
        buffer<expr> lemma_args;
        for (unsigned i = 0; i < lhs_args.size(); i++) {
            lean_assert(*it1 && *it2);
            switch (head(*it2)) {
            case congr_arg_kind::Eq:
                lean_assert(head(*it1));
                lemma_args.push_back(lhs_args[i]);
                lemma_args.push_back(rhs_args[i]);
                lemma_args.push_back(*get_eqv_proof(*head(*it1), lhs_args[i], rhs_args[i]));
                break;
            case congr_arg_kind::Fixed:
                lemma_args.push_back(lhs_args[i]);
                break;
            case congr_arg_kind::Cast:
                lemma_args.push_back(lhs_args[i]);
                lemma_args.push_back(rhs_args[i]);
                break;
            }
            it1 = &(tail(*it1));
            it2 = &(tail(*it2));
        }
        expr r = mk_app(lemma->m_congr_lemma.get_proof(), lemma_args);
        if (lemma->m_lift_needed)
            r = b.lift_from_eq(R, r);
        return r;
    } else {
        optional<expr> r;
        unsigned i = 0;
        if (!is_def_eq(lhs_fn, rhs_fn)) {
            r = get_eqv_proof(get_eq_name(), lhs_fn, rhs_fn);
        } else {
            for (; i < lhs_args.size(); i++) {
                if (!is_def_eq(lhs_args[i], rhs_args[i])) {
                    expr g  = mk_app(lhs_fn, i, lhs_args.data());
                    expr Hi = *get_eqv_proof(get_eq_name(), lhs_args[i], rhs_args[i]);
                    r = b.mk_congr_arg(g, Hi);
                    i++;
                    break;
                }
            }
            if (!r) {
                // lhs and rhs are definitionally equal
                r = b.mk_eq_refl(lhs);
            }
        }
        lean_assert(r);
        for (; i < lhs_args.size(); i++) {
            if (is_def_eq(lhs_args[i], rhs_args[i])) {
                r = b.mk_congr_fun(*r, lhs_args[i]);
            } else {
                expr Hi = *get_eqv_proof(get_eq_name(), lhs_args[i], rhs_args[i]);
                r = b.mk_congr(*r, Hi);
            }
        }
        if (lemma->m_lift_needed)
            r = b.lift_from_eq(R, *r);
        return *r;
    }
}

expr congruence_closure::mk_congr_proof(name const & R, expr const & e1, expr const & e2) const {
    name R1; expr lhs1, rhs1;
    if (is_equivalence_relation_app(e1, R1, lhs1, rhs1)) {
        name R2; expr lhs2, rhs2;
        if (is_equivalence_relation_app(e2, R2, lhs2, rhs2) && R1 == R2) {
            if (!is_eqv(R1, lhs1, lhs2)) {
                lean_assert(is_eqv(R1, lhs1, rhs2));
                // We must apply symmetry.
                // The congruence table is implicitly using symmetry.
                app_builder & b = get_app_builder();
                expr new_e1 = b.mk_rel(R1, rhs1, lhs1);
                expr h1  = mk_fresh_local(e1);
                expr h2  = mk_fresh_local(new_e1);
                expr e1_eqv_new_e1 = b.mk_app(get_iff_intro_name(),
                                              Fun(h1, b.mk_symm(R1, h1)),
                                              Fun(h2, b.mk_symm(R1, h2)));
                if (R != get_iff_name()) {
                    e1_eqv_new_e1 = b.mk_app(get_propext_name(), e1_eqv_new_e1);
                    if (R != get_eq_name())
                        e1_eqv_new_e1 = b.lift_from_eq(R, e1_eqv_new_e1);
                }
                return b.mk_trans(R, e1_eqv_new_e1, mk_congr_proof_core(R, new_e1, e2));
            }
        }
    }
    return mk_congr_proof_core(R, e1, e2);
}

expr congruence_closure::mk_proof(name const & R, expr const & lhs, expr const & rhs, expr const & H) const {
    if (H == *g_congr_mark) {
        return mk_congr_proof(R, lhs, rhs);
    } else if (H == *g_iff_true_mark) {
        bool flip;
        name R1; expr a, b;
        if (lhs == mk_true()) {
            lean_verify(is_equivalence_relation_app(rhs, R1, a, b));
            flip = true;
        } else {
            lean_verify(is_equivalence_relation_app(lhs, R1, a, b));
            flip = false;
        }
        expr H1 = get_app_builder().mk_iff_true_intro(*get_eqv_proof(R1, a, b));
        if (flip)
            H1 = get_app_builder().mk_iff_symm(H1);
        return H1;
    } else if (H == *g_lift_mark) {
        expr H1 = *get_eqv_proof(get_eq_name(), lhs, rhs);
        return get_app_builder().lift_from_eq(R, H1);
    } else {
        return H;
    }
}

static expr flip_proof(name const & R, expr const & H, bool flipped) {
    if (!flipped || H == *g_congr_mark || H == *g_iff_true_mark || H == *g_lift_mark) {
        return H;
    } else {
        return get_app_builder().mk_symm(R, H);
    }
}

static expr mk_trans(name const & R, optional<expr> const & H1, expr const & H2) {
    return !H1 ? H2 : get_app_builder().mk_trans(R, *H1, H2);
}

optional<expr> congruence_closure::get_eqv_proof(name const & R, expr const & e1, expr const & e2) const {
    app_builder & b = get_app_builder();
    if (has_expr_metavar(e1) || has_expr_metavar(e2)) return none_expr();
    if (is_def_eq(e1, e2))
        return some_expr(b.lift_from_eq(R, b.mk_eq_refl(e1)));
    auto n1 = m_entries.find(eqc_key(R, e1));
    if (!n1) return none_expr();
    auto n2 = m_entries.find(eqc_key(R, e2));
    if (!n2) return none_expr();
    if (n1->m_root != n2->m_root) return none_expr();
    // 1. Retrieve "path" from e1 to root
    buffer<expr> path1, Hs1;
    rb_tree<expr, expr_quick_cmp> visited;
    expr it1 = e1;
    while (true) {
        visited.insert(it1);
        auto it1_n = m_entries.find(eqc_key(R, it1));
        lean_assert(it1_n);
        if (!it1_n->m_target)
            break;
        path1.push_back(*it1_n->m_target);
        Hs1.push_back(flip_proof(R, *it1_n->m_proof, it1_n->m_flipped));
        it1 = *it1_n->m_target;
    }
    lean_assert(it1 == n1->m_root);
    // 2. The path from e2 to root must have at least one element c in visited
    // Retrieve "path" from e2 to c
    buffer<expr> path2, Hs2;
    expr it2 = e2;
    while (true) {
        if (visited.contains(it2))
            break; // found common
        auto it2_n = m_entries.find(eqc_key(R, it2));
        lean_assert(it2_n);
        lean_assert(it2_n->m_target);
        path2.push_back(it2);
        Hs2.push_back(flip_proof(R, *it2_n->m_proof, !it2_n->m_flipped));
        it2 = *it2_n->m_target;
    }
    // it2 is the common element...
    // 3. Shink path1/Hs1 until we find it2 (the common element)
    while (true) {
        if (path1.empty()) {
            lean_assert(it2 == e1);
            break;
        }
        if (path1.back() == it2) {
            // found it!
            break;
        }
        path1.pop_back();
        Hs1.pop_back();
    }

    // 4. Build transitivity proof
    optional<expr> pr;
    expr lhs = e1;
    for (unsigned i = 0; i < path1.size(); i++) {
        pr  = mk_trans(R, pr, mk_proof(R, lhs, path1[i], Hs1[i]));
        lhs = path1[i];
    }
    unsigned i = Hs2.size();
    while (i > 0) {
        --i;
        pr  = mk_trans(R, pr, mk_proof(R, lhs, path2[i], Hs2[i]));
        lhs = path2[i];
    }
    lean_assert(pr);
    return pr;
}

bool congruence_closure::is_uneqv(name const & R, expr const & e1, expr const & e2) const {
    if (!is_standard(env()))
        return false;
    try {
        app_builder & b = get_app_builder();
        // TODO(Leo): check if this is a bootleneck
        expr tmp = b.mk_rel(R, e1, e2);
        return is_eqv(get_iff_name(), tmp, mk_false());
    } catch (app_builder_exception &) {
        return false;
    }
}

optional<expr> congruence_closure::get_uneqv_proof(name const & R, expr const & e1, expr const & e2) const {
    if (!is_standard(env()))
        return none_expr();
    try {
        app_builder & b = get_app_builder();
        // TODO(Leo): check if this is a bootleneck
        expr tmp = b.mk_rel(R, e1, e2);
        if (auto p = get_eqv_proof(get_iff_name(), tmp, mk_false())) {
            return some_expr(b.mk_not_of_iff_false(*p));
        } else {
            return none_expr();
        }
    } catch (app_builder_exception &) {
        return none_expr();
    }
}

bool congruence_closure::is_inconsistent() const {
    // If the m_inconsistent flag is true and partitions have not been frozen, then
    // true and false must be in the same equivalence class.
    lean_assert(!m_inconsistent || m_froze_partitions || is_eqv(get_iff_name(), mk_true(), mk_false()));
    return m_inconsistent;
}

optional<expr> congruence_closure::get_inconsistency_proof() const {
    lean_assert(!m_froze_partitions);
    try {
        app_builder & b = get_app_builder();
        if (auto p = get_eqv_proof(get_iff_name(), mk_true(), mk_false())) {
            return some_expr(b.mk_false_of_true_iff_false(*p));
        } else {
            return none_expr();
        }
    } catch (app_builder_exception &) {
        return none_expr();
    }
}

bool congruence_closure::proved(expr const & e) const {
    return is_eqv(get_iff_name(), e, mk_true());
}

optional<expr> congruence_closure::get_proof(expr const & e) const {
    lean_assert(!m_froze_partitions);
    try {
        app_builder & b = get_app_builder();
        if (auto p = get_eqv_proof(get_iff_name(), e, mk_true())) {
            return some_expr(b.mk_of_iff_true(*p));
        } else {
            return none_expr();
        }
    } catch (app_builder_exception &) {
        return none_expr();
    }
}

bool congruence_closure::disproved(expr const & e) const {
    return is_eqv(get_iff_name(), e, mk_false());
}

optional<expr> congruence_closure::get_disproof(expr const & e) const {
    lean_assert(!m_froze_partitions);
    try {
        app_builder & b = get_app_builder();
        if (auto p = get_eqv_proof(get_iff_name(), e, mk_false())) {
            return some_expr(b.mk_not_of_iff_false(*p));
        } else {
            return none_expr();
        }
    } catch (app_builder_exception &) {
        return none_expr();
    }
}

bool congruence_closure::is_congr_root(name const & R, expr const & e) const {
    if (auto n = m_entries.find(eqc_key(R, e))) {
        return e == n->m_cg_root;
    } else {
        return true;
    }
}

expr congruence_closure::get_root(name const & R, expr const & e) const {
    if (auto n = m_entries.find(eqc_key(R, e))) {
        return n->m_root;
    } else {
        return e;
    }
}

expr congruence_closure::get_next(name const & R, expr const & e) const {
    if (auto n = m_entries.find(eqc_key(R, e))) {
        return n->m_next;
    } else {
        return e;
    }
}

unsigned congruence_closure::get_mt(name const & R, expr const & e) const {
    if (auto n = m_entries.find(eqc_key(R, e))) {
        return n->m_mt;
    } else {
        return m_gmt;
    }
}

void congruence_closure::freeze_partitions() {
    m_froze_partitions = true;
    entries new_entries;
    m_entries.for_each([&](eqc_key const & k, entry e) {
            if (k.m_expr == e.m_root)
                e.m_interpreted = true;
            new_entries.insert(k, e);
        });
    m_entries = new_entries;
}

void congruence_closure::trace_eqc(name const & R, expr const & e) const {
    auto out   = tout();
    bool first = true;
    expr it = e;
    out << R << " {";
    do {
        auto it_n = m_entries.find(eqc_key(R, it));
        if (first) first = false; else out << ", ";
        out << ppb(it);
        it = it_n->m_next;
    } while (it != e);
    out << "}";
}

void congruence_closure::trace_eqcs() const {
    auto out = tout();
    m_entries.for_each([&](eqc_key const & k, entry const & n) {
            if (k.m_expr == n.m_root) {
                trace_eqc(k.m_R, k.m_expr);
                out << "\n";
            }
        });
}

static void trace_rel(io_state_stream & out, name const & R) {
    if (R != get_eq_name())
        out << "(" << R << ") ";
}

void congruence_closure::trace_parents() const {
    auto out = tout();
    m_parents.for_each([&](child_key const & k, parent_occ_set const & ps) {
            trace_rel(out, k.m_R);
            out << ppb(k.m_expr);
            out << ", parents: {";
            bool first = true;
            ps.for_each([&](parent_occ const & o) {
                    if (first) first = false; else out << ", ";
                    trace_rel(out, o.m_R);
                    out << ppb(o.m_expr);
                });
            out << "}\n";
        });
}

void congruence_closure::trace() const {
    tout() << "\n";
    trace_eqcs();
    trace_parents();
    tout() << "\n";
}

bool congruence_closure::check_eqc(name const & R, expr const & e) const {
    expr root     = get_root(R, e);
    unsigned size = 0;
    expr it       = e;
    do {
        auto it_n = m_entries.find(eqc_key(R, it));
        lean_assert(it_n);
        lean_assert(it_n->m_root == root);
        auto it2  = it;
        // following m_target fields should lead to root
        while (true) {
            auto it2_n = m_entries.find(eqc_key(R, it2));
            if (!it2_n->m_target)
                break;
            it2 = *it2_n->m_target;
        }
        lean_assert(it2 == root);
        it = it_n->m_next;
        size++;
    } while (it != e);
    lean_assert(m_entries.find(eqc_key(R, root))->m_size == size);
    return true;
}

bool congruence_closure::check_invariant() const {
    m_entries.for_each([&](eqc_key const & k, entry const & n) {
            if (k.m_expr == n.m_root) {
                lean_assert(check_eqc(k.m_R, k.m_expr));
            }
        });
    return true;
}

static unsigned g_ext_id = 0;
struct cc_branch_extension : public branch_extension {
    congruence_closure m_cc;
    cc_branch_extension() {}
    cc_branch_extension(cc_branch_extension const & o):m_cc(o.m_cc) {}
    virtual ~cc_branch_extension() {}
    virtual branch_extension * clone() override { return new cc_branch_extension(*this); }
    virtual void initialized() override { m_cc.initialize(); }
    virtual void target_updated() override { m_cc.internalize(curr_state().get_target()); }
};

congruence_closure & get_cc() {
    return static_cast<cc_branch_extension&>(curr_state().get_extension(g_ext_id)).m_cc;
}

void initialize_congruence_closure() {
    register_trace_class("cc");
    register_trace_class({"cc", "state"});
    register_trace_class({"cc", "propagation"});
    register_trace_class({"cc", "merge"});
    g_ext_id = register_branch_extension(new cc_branch_extension());
    name prefix = name::mk_internal_unique_name();
    g_congr_mark    = new expr(mk_constant(name(prefix, "[congruence]")));
    g_iff_true_mark = new expr(mk_constant(name(prefix, "[iff-true]")));
    g_lift_mark     = new expr(mk_constant(name(prefix, "[lift]")));
}

void finalize_congruence_closure() {
    delete g_congr_mark;
    delete g_iff_true_mark;
    delete g_lift_mark;
}
}}
