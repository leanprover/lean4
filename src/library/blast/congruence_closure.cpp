/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include "library/constants.h"
#include "library/simplifier/simp_rule_set.h"
#include "library/blast/congruence_closure.h"
#include "library/blast/util.h"
#include "library/blast/blast.h"
#include "library/blast/trace.h"

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

struct ext_congr_lemma {
    name                 m_R;
    congr_lemma          m_congr_lemma;    // actual lemma
    list<optional<name>> m_rel_names;      // relation congruence to be used with each child, none means child is ignored by congruence closure.
    unsigned             m_lift_needed:1;  // if true, m_congr_lemma is for equality, and we need to lift to m_R.
    unsigned             m_fixed_fun:1;    // if true, we build equivalences for functions, and use generic congr lemma, and ignore m_congr_lemma
    ext_congr_lemma(congr_lemma const & H):
        m_R(get_eq_name()),
        m_congr_lemma(H),
        m_rel_names(rel_names_from_arg_kinds(H.get_arg_kinds(), get_eq_name())),
        m_lift_needed(false),
        m_fixed_fun(true) {}
    ext_congr_lemma(name const & R, congr_lemma const & H, bool lift_needed):
        m_R(R),
        m_congr_lemma(H),
        m_rel_names(rel_names_from_arg_kinds(H.get_arg_kinds(), get_eq_name())),
        m_lift_needed(lift_needed),
        m_fixed_fun(true) {}
    ext_congr_lemma(name const & R, congr_lemma const & H, list<optional<name>> const & rel_names, bool lift_needed):
        m_R(R),
        m_congr_lemma(H),
        m_rel_names(rel_names),
        m_lift_needed(lift_needed),
        m_fixed_fun(true) {}
};

/* We use the following cache for user-defined lemmas and automatically generated ones. */
typedef std::unordered_map<congr_lemma_key, optional<ext_congr_lemma>, congr_lemma_key_hash_fn, congr_lemma_key_eq_fn> congr_cache;

LEAN_THREAD_VALUE(congr_cache *, g_congr_cache, nullptr);

scope_congruence_closure::scope_congruence_closure():
    m_old_cache(g_congr_cache) {
    g_congr_cache = new congr_cache();
}

scope_congruence_closure::~scope_congruence_closure() {
    delete g_congr_cache;
    g_congr_cache = static_cast<congr_cache*>(m_old_cache);
}

void congruence_closure::initialize() {
    mk_entry_for(get_iff_name(), mk_true());
    mk_entry_for(get_iff_name(), mk_false());
}

void congruence_closure::mk_entry_for(name const & R, expr const & e) {
    lean_assert(!m_entries.find(eqc_key(R, e)));
    entry n;
    n.m_next    = e;
    n.m_root    = e;
    n.m_cg_root = e;
    n.m_size    = 1;
    m_entries.insert(eqc_key(R, e), n);
}

static optional<ext_congr_lemma> mk_ext_congr_lemma_core(name const & R, expr const & fn, unsigned nargs) {
    simp_rule_set const * sr = get_simp_rule_sets(env()).find(R);
    if (sr) {
        list<congr_rule> const * crs = sr->find_congr(fn);
        if (crs) {
            for (congr_rule const & r : *crs) {
                // TODO(Leo):
                std::cout << r.get_id() << "\n";
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

static optional<ext_congr_lemma> mk_ext_congr_lemma(name const & R, expr const & fn, unsigned nargs) {
    congr_lemma_key key(R, fn, nargs);
    auto it = g_congr_cache->find(key);
    if (it != g_congr_cache->end())
        return it->second;
    auto r = mk_ext_congr_lemma_core(R, fn, nargs);
    g_congr_cache->insert(mk_pair(key, r));
    return r;
}

void congruence_closure::add_occurrence(name const & Rp, expr const & parent, name const & Rc, expr const & child) {
    child_key k(Rc, child);
    parent_occ_set ps;
    if (auto old_ps = m_parents.find(k))
        ps = *old_ps;
    ps.insert(parent_occ(Rp, parent));
    m_parents.insert(k, ps);
}

/* Small hack for not storing a pointer to the congruence_closure object
   at congruence_closure::congr_key_cmp */
LEAN_THREAD_PTR(congruence_closure, g_cc);

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
        lean_verify(is_relation_app(k1.m_expr, R1, lhs1, rhs1));
        lean_verify(is_relation_app(k2.m_expr, R2, lhs2, rhs2));
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
    name R; expr lhs, rhs;
    if (is_eq(e, lhs, rhs)) {
        k.m_eq   = true;
        k.m_hash = symm_hash(get_eq_name(), lhs, rhs);
    } else if (is_iff(e, lhs, rhs)) {
        k.m_iff  = true;
        k.m_hash = symm_hash(get_iff_name(), lhs, rhs);
    } else if (is_relation_app(e, R, lhs, rhs) && is_symmetric(R)) {
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

static expr * g_congr_mark    = nullptr; // dummy congruence proof, it is just a placeholder.
static expr * g_iff_true_mark = nullptr; // dummy iff_true proof, it is just a placeholder.

typedef std::tuple<name, expr, expr, expr> cc_todo_entry;

MK_THREAD_LOCAL_GET_DEF(std::vector<cc_todo_entry>, get_todo);

static void clear_todo() {
    get_todo().clear();
}

void congruence_closure::check_iff_true(congr_key const & k) {
    expr const & e = k.m_expr;
    name R; expr lhs, rhs;
    if (k.m_eq || k.m_iff) {
        R   = k.m_eq ? get_eq_name() : get_iff_name();
        lhs = app_arg(app_fn(e));
        rhs = app_arg(e);
    } else if (k.m_symm_rel) {
        lean_verify(is_relation_app(e, R, lhs, rhs));
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
    get_todo().emplace_back(get_iff_name(), e, mk_true(), *g_iff_true_mark);
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
        get_todo().emplace_back(lemma.m_R, e, old_k->m_expr, *g_congr_mark);
    } else {
        m_congruences.insert(k);
    }
    check_iff_true(k);
}

void congruence_closure::internalize(name const & R, expr const & e) {
    lean_assert(closed(e));
    if (has_expr_metavar(e))
        return;
    if (m_entries.find(eqc_key(R, e)))
        return; // e has already been internalized
    switch (e.kind()) {
    case expr_kind::Var: case expr_kind::Meta:
        lean_unreachable();
    case expr_kind::Sort:
        return;
    case expr_kind::Constant: case expr_kind::Local:
    case expr_kind::Lambda:
        mk_entry_for(R, e);
        return;
    case expr_kind::Macro:
        for (unsigned i = 0; i < macro_num_args(e); i++)
            internalize(R, macro_arg(e, i));
        mk_entry_for(R, e);
        break;
    case expr_kind::Pi:
        if (is_arrow(e) && is_prop(binding_domain(e)) && is_prop(binding_body(e))) {
            internalize(R, binding_domain(e));
            internalize(R, binding_body(e));
        }
        if (is_prop(e)) {
            mk_entry_for(R, e);
        }
        return;
    case expr_kind::App: {
        mk_entry_for(R, e);
        buffer<expr> args;
        expr const & fn = get_app_args(e, args);
        if (auto lemma = mk_ext_congr_lemma(R, fn, args.size())) {
            list<optional<name>> const * it = &(lemma->m_rel_names);
            for (expr const & arg : args) {
                lean_assert(*it);
                if (auto R1 = head(*it)) {
                    internalize(*R1, arg);
                    add_occurrence(R, e, *R1, arg);
                }
                it = &tail(*it);
            }
            if (!lemma->m_fixed_fun) {
                internalize(get_eq_name(), fn);
                add_occurrence(get_eq_name(), e, get_eq_name(), fn);
            }
            add_congruence_table(*lemma, e);
        }
        break;
    }}
}

void congruence_closure::internalize(expr const & e) {
    if (is_prop(e))
        internalize(get_iff_name(), e);
    else
        internalize(get_eq_name(), e);
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
void congruence_closure::invert_trans(name const & R, expr const & e, optional<expr> new_target, optional<expr> new_proof) {
    eqc_key k(R, e);
    auto n = m_entries.find(k);
    lean_assert(n);
    entry new_n = *n;
    if (n->m_target)
        invert_trans(R, *new_n.m_target, some_expr(e), new_n.m_proof);
    new_n.m_target = new_target;
    new_n.m_proof  = new_proof;
    m_entries.insert(k, new_n);
}
void congruence_closure::invert_trans(name const & R, expr const & e) {
    invert_trans(R, e, none_expr(), none_expr());
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

void congruence_closure::add_eqv_step(name const & R, expr e1, expr e2, expr const & H) {
    auto n1 = m_entries.find(eqc_key(R, e1));
    auto n2 = m_entries.find(eqc_key(R, e2));
    if (!n1 || !n2)
        return;
    if (n1->m_root == n2->m_root)
        return; // they are already in the same equivalence class
    auto r1 = m_entries.find(eqc_key(R, n1->m_root));
    auto r2 = m_entries.find(eqc_key(R, n2->m_root));
    lean_assert(r1 && r2);

    // We want r2 to be the root of the combined class.

    if (r1->m_size > r2->m_size) {
        std::swap(e1, e2);
        std::swap(n1, n2);
        std::swap(r1, r2);
        // Remark: we don't apply symmetry eagerly. So, we don't adjust H.
    }

    expr e1_root   = n1->m_root;
    expr e2_root   = n2->m_root;
    entry new_n1   = *n1;

    // Following target/proof we have
    // e1 -> ... -> r1
    // e2 -> ... -> r2
    // We want
    // r1 -> ... -> e1 -> e2 -> ... -> r2
    invert_trans(R, e1);
    new_n1.m_target = e2;
    new_n1.m_proof  = H;
    m_entries.insert(eqc_key(R, e1), new_n1);

    // The hash code for the parents is going to change
    remove_parents(R, e1);

    // force all m_root fields in e1 equivalence class to point to e2_root
    expr it = e1;
    do {
        auto it_n = m_entries.find(eqc_key(R, it));
        lean_assert(it_n);
        entry new_it_n   = *it_n;
        new_it_n.m_root = e2_root;
        m_entries.insert(eqc_key(R, it), new_it_n);
        it = new_it_n.m_next;
    } while (it != e1);

    reinsert_parents(R, e1);

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
    if (!ps1) return; // e1_root doesn't have parents
    parent_occ_set ps2;
    child_key k2(R, e2_root);
    if (auto it = m_parents.find(k2))
        ps2 = *it;
    ps1->for_each([&](parent_occ const & p) {
            ps2.insert(p);
        });
    m_parents.erase(k1);
    m_parents.insert(k2, ps2);
}

void congruence_closure::add_eqv(name const & _R, expr const & _lhs, expr const & _rhs, expr const & _H) {
    auto & todo = get_todo();
    todo.emplace_back(_R, _lhs, _rhs, _H);
    while (!todo.empty()) {
        name R; expr lhs, rhs, H;
        std::tie(R, lhs, rhs, H) = todo.back();
        todo.pop_back();
        add_eqv_step(R, lhs, rhs, H);
    }
}

void congruence_closure::add(hypothesis_idx hidx) {
    if (is_inconsistent())
        return;
    flet<congruence_closure *> set_cc(g_cc, this);
    clear_todo();
    state & s       = curr_state();
    app_builder & b = get_app_builder();
    hypothesis const & h = s.get_hypothesis_decl(hidx);
    try {
        expr const & type = h.get_type();
        expr p      = type;
        bool is_neg = is_not(type, p);
        if (is_neg && !is_standard(env()))
            return;
        name R; expr lhs, rhs;
        if (is_relation_app(p, R, lhs, rhs)) {
            if (is_neg) {
                internalize(get_iff_name(), p);
                add_eqv(get_iff_name(), p, mk_false(), b.mk_iff_false_intro(h.get_self()));
            } else {
                internalize(R, lhs);
                internalize(R, rhs);
                add_eqv(R, lhs, rhs, h.get_self());
            }
        } else if (is_prop(p)) {
            internalize(get_iff_name(), p);
            if (is_neg) {
                add_eqv(get_iff_name(), p, mk_false(), b.mk_iff_false_intro(h.get_self()));
            } else {
                add_eqv(get_iff_name(), p, mk_true(), b.mk_iff_true_intro(h.get_self()));
            }
        }
    } catch (app_builder_exception &) {}
}

bool congruence_closure::is_eqv(name const & R, expr const & e1, expr const & e2) const {
    auto n1 = m_entries.find(eqc_key(R, e1));
    if (!n1) return false;
    auto n2 = m_entries.find(eqc_key(R, e2));
    if (!n2) return false;
    return n1->m_root == n2->m_root;
}

optional<expr> congruence_closure::get_eqv_proof(name const & R, expr const & e1, expr const & e2) const {
    // TODO(Leo):
    std::cout << R << e1 << e2 << "\n";
    return none_expr();
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
    return is_eqv(get_iff_name(), mk_true(), mk_false());
}

optional<expr> congruence_closure::get_inconsistency_proof() const {
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
        return n->m_cg_root;
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

void congruence_closure::display_eqc(name const & R, expr const & e) const {
    auto out = diagnostic(env(), ios());
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

void congruence_closure::display_eqcs() const {
    auto out = diagnostic(env(), ios());
    m_entries.for_each([&](eqc_key const & k, entry const & n) {
            if (k.m_expr == n.m_root) {
                display_eqc(k.m_R, k.m_expr);
                out << "\n";
            }
        });
}

static void display_rel(io_state_stream & out, name const & R) {
    if (R != get_eq_name())
        out << "[" << R << "] ";
}

void congruence_closure::display_parents() const {
    auto out = diagnostic(env(), ios());
    m_parents.for_each([&](child_key const & k, parent_occ_set const & ps) {
            display_rel(out, k.m_R);
            out << ppb(k.m_expr);
            out << ", parents: {";
            bool first = true;
            ps.for_each([&](parent_occ const & o) {
                    if (first) first = false; else out << ", ";
                    display_rel(out, o.m_R);
                    out << ppb(o.m_expr);
                });
            out << "}\n";
        });
}

void congruence_closure::display() const {
    diagnostic(env(), ios()) << "congruence closure state\n";
    display_eqcs();
    display_parents();
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
    // TODO(Leo):
    return true;
}

void initialize_congruence_closure() {
    name prefix = name::mk_internal_unique_name();
    g_congr_mark    = new expr(mk_constant(name(prefix, "[congruence]")));
    g_iff_true_mark = new expr(mk_constant(name(prefix, "[iff-true]")));
}

void finalize_congruence_closure() {
    delete g_congr_mark;
    delete g_iff_true_mark;
}
}}
