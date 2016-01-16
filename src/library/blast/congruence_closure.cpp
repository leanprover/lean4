/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <vector>
#include "util/sexpr/option_declarations.h"
#include "kernel/abstract.h"
#include "library/trace.h"
#include "library/constants.h"
#include "library/blast/simplifier/simp_lemmas.h"
#include "library/blast/congruence_closure.h"
#include "library/blast/util.h"
#include "library/blast/blast.h"
#include "library/blast/trace.h"
#include "library/blast/options.h"

#ifndef LEAN_DEFAULT_BLAST_CC_HEQ
#define LEAN_DEFAULT_BLAST_CC_HEQ true
#endif

#ifndef LEAN_DEFAULT_BLAST_CC_SUBSINGLETON
#define LEAN_DEFAULT_BLAST_CC_SUBSINGLETON true
#endif

namespace lean {
namespace blast {
static name * g_blast_cc_heq          = nullptr;
static name * g_blast_cc_subsingleton = nullptr;

bool get_blast_cc_heq(options const & o) {
    return o.get_bool(*g_blast_cc_heq, LEAN_DEFAULT_BLAST_CC_HEQ);
}

bool get_blast_cc_subsingleton(options const & o) {
    return o.get_bool(*g_blast_cc_subsingleton, LEAN_DEFAULT_BLAST_CC_SUBSINGLETON);
}

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

LEAN_THREAD_VALUE(bool, g_heq_based, false);
LEAN_THREAD_VALUE(bool, g_propagate_subsingletons, false);

static list<optional<name>> rel_names_from_arg_kinds(list<congr_arg_kind> const & kinds, name const & R) {
    return map2<optional<name>>(kinds, [&](congr_arg_kind k) {
            switch (k) {
            case congr_arg_kind::Eq:
                return optional<name>(R);
            case congr_arg_kind::HEq:
                if (g_heq_based && (R == get_eq_name() || R == get_heq_name())) {
                    /* Remark: we store equality and heterogeneous equality in the same class. */
                    return optional<name>(get_eq_name());
                } else {
                    return optional<name>();
                }
            case congr_arg_kind::Fixed: case congr_arg_kind::Cast:
            case congr_arg_kind::FixedNoParam:
                return optional<name>();
            }
            lean_unreachable();
        });
}

ext_congr_lemma::ext_congr_lemma(congr_lemma const & H):
    m_R(get_eq_name()),
    m_congr_lemma(H),
    m_rel_names(rel_names_from_arg_kinds(H.get_arg_kinds(), get_eq_name())),
    m_lift_needed(false),
    m_fixed_fun(true),
    m_heq_result(false),
    m_hcongr_lemma(false) {}
ext_congr_lemma::ext_congr_lemma(name const & R, congr_lemma const & H, bool lift_needed):
    m_R(R),
    m_congr_lemma(H),
    m_rel_names(rel_names_from_arg_kinds(H.get_arg_kinds(), get_eq_name())),
    m_lift_needed(lift_needed),
    m_fixed_fun(true),
    m_heq_result(false),
    m_hcongr_lemma(false) {}
ext_congr_lemma::ext_congr_lemma(name const & R, congr_lemma const & H, list<optional<name>> const & rel_names, bool lift_needed):
    m_R(R),
    m_congr_lemma(H),
    m_rel_names(rel_names),
    m_lift_needed(lift_needed),
    m_fixed_fun(true),
    m_heq_result(false),
    m_hcongr_lemma(false) {}

/* We use the following cache for user-defined lemmas and automatically generated ones. */
typedef std::unordered_map<congr_lemma_key, optional<ext_congr_lemma>, congr_lemma_key_hash_fn, congr_lemma_key_eq_fn> congr_cache;
typedef std::tuple<name, expr, expr, expr, bool> cc_todo_entry;

static expr * g_eq_congr_mark = nullptr; // dummy eq congruence proof, it is just a placeholder.
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

static void push_todo(name const & R, expr const & lhs, expr const & rhs, expr const & H, bool heq_proof) {
    get_todo().emplace_back(R, lhs, rhs, H, heq_proof);
}

scope_congruence_closure::scope_congruence_closure():
    m_old_cache(g_congr_cache) {
    g_congr_cache = new congr_cache();
    g_heq_based               = is_standard(env()) && get_blast_cc_heq(ios().get_options());
    g_propagate_subsingletons = get_blast_cc_subsingleton(ios().get_options());
}

scope_congruence_closure::~scope_congruence_closure() {
    delete g_congr_cache;
    g_congr_cache = static_cast<congr_cache*>(m_old_cache);
}

void congruence_closure::initialize() {
    bool propagate_back = false;
    bool interpreted    = true;
    bool constructor    = false;
    mk_entry_core(get_iff_name(), mk_true(), propagate_back, interpreted, constructor);
    mk_entry_core(get_iff_name(), mk_false(), propagate_back, interpreted, constructor);

    /* Put (nat.zero) and (@zero nat nat_has_zero) in the same equivalence class.
       TODO(Leo): this is hackish, we should have a more general solution for this kind of equality. */
    app_builder & b = get_app_builder();
    expr nat_zero   = mk_constant(get_nat_zero_name());
    expr zero_nat   = normalize(b.mk_zero(mk_constant(get_nat_name())));
    add_eqv(get_eq_name(), nat_zero, zero_nat, b.mk_eq_refl(nat_zero));
}

void congruence_closure::push_subsingleton_eq(expr const & a, expr const & b) {
    expr A = infer_type(a);
    expr B = infer_type(b);
    if (is_def_eq(A, B)) {
        // TODO(Leo): to improve performance we can create the following proof lazily
        bool heq_proof = false;
        expr proof     = get_app_builder().mk_app(get_subsingleton_elim_name(), a, b);
        push_todo(get_eq_name(), a, b, proof, heq_proof);
    } else if (g_heq_based) {
        bool heq_proof = true;
        expr A_eq_B    = *get_eqv_proof(get_eq_name(), A, B);
        expr proof     = get_app_builder().mk_app(get_subsingleton_helim_name(), A_eq_B, a, b);
        push_todo(get_eq_name(), a, b, proof, heq_proof);
    }
}

void congruence_closure::check_new_subsingleton_eq(expr const & old_root, expr const & new_root) {
    lean_assert(is_eqv(get_eq_name(), old_root, new_root));
    lean_assert(get_root(get_eq_name(), old_root) == new_root);
    auto it1 = m_subsingleton_reprs.find(old_root);
    if (!it1) return;
    if (auto it2 = m_subsingleton_reprs.find(new_root)) {
        push_subsingleton_eq(*it1, *it2);
    } else {
        m_subsingleton_reprs.insert(new_root, *it1);
    }
}

/* If \c typeof(e) is a subsingleton, then try to propagate equality */
void congruence_closure::process_subsingleton_elem(expr const & e) {
    if (!g_propagate_subsingletons)
        return;
    expr type = infer_type(e);
    optional<expr> ss = mk_subsingleton_instance(type);
    if (!ss)
        return; /* type is not a subsingleton */
    /* Make sure type has been internalized */
    bool toplevel  = true;
    bool propagate = false;
    internalize_core(get_eq_name(), type, toplevel, propagate);
    /* Try to find representative */
    if (auto it = m_subsingleton_reprs.find(type)) {
        push_subsingleton_eq(e, *it);
    } else {
        m_subsingleton_reprs.insert(type, e);
    }
    if (!g_heq_based)
        return;
    expr type_root     = get_root(get_eq_name(), type);
    if (type_root == type)
        return;
    if (auto it2 = m_subsingleton_reprs.find(type_root)) {
        push_subsingleton_eq(e, *it2);
    } else {
        m_subsingleton_reprs.insert(type_root, e);
    }
}

void congruence_closure::mk_entry_core(name const & R, expr const & e, bool to_propagate, bool interpreted, bool constructor) {
    lean_assert(!m_entries.find(eqc_key(R, e)));
    entry n;
    n.m_next         = e;
    n.m_root         = e;
    n.m_cg_root      = e;
    n.m_size         = 1;
    n.m_flipped      = false;
    n.m_interpreted  = interpreted;
    n.m_constructor  = constructor;
    n.m_to_propagate = to_propagate;
    n.m_heq_proofs   = false;
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
                    bool heq_proof = false;
                    push_todo(R, e, it, *g_lift_mark, heq_proof);
                    break;
                }
                auto it_n = m_entries.find(eqc_key(get_eq_name(), it));
                lean_assert(it_n);
                it = it_n->m_next;
            }
        }
    }
    process_subsingleton_elem(e);
}

void congruence_closure::mk_entry_core(name const & R, expr const & e, bool to_propagate) {
    bool interpreted = false;
    bool constructor = R == get_eq_name() && is_constructor_app(env(), e);
    return mk_entry_core(R, e, to_propagate, interpreted, constructor);
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
    mk_entry_core(R, e, to_propagate);
}

static bool all_distinct(buffer<expr> const & es) {
    for (unsigned i = 0; i < es.size(); i++)
        for (unsigned j = i+1; j < es.size(); j++)
            if (es[i] == es[j])
                return false;
    return true;
}

/* Try to convert user-defined congruence rule into an ext_congr_lemma */
static optional<ext_congr_lemma> to_ext_congr_lemma(name const & R, expr const & fn, unsigned nargs, user_congr_lemma const & r) {
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
        case congr_arg_kind::FixedNoParam:
        case congr_arg_kind::HEq:
            // User defined congruence rules do not use FixedNoParam
            lean_unreachable();
            break;
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

static optional<ext_congr_lemma> mk_ext_user_congr_lemma(name const & R, expr const & fn, unsigned nargs) {
    simp_lemmas_for const * sr = get_simp_lemmas().find(R);
    if (sr) {
        list<user_congr_lemma> const * crs = sr->find_congr(fn);
        if (crs) {
            for (user_congr_lemma const & r : *crs) {
                if (auto lemma = to_ext_congr_lemma(R, fn, nargs, r))
                    return lemma;
            }
        }
    }
    return optional<ext_congr_lemma>();
}

/* Automatically generated lemma for equivalence relation over iff/eq. */
static optional<ext_congr_lemma> mk_relation_congr_lemma(name const & R, expr const & fn, unsigned nargs) {
    if (auto info = is_relation(fn)) {
        if (info->get_arity() == nargs) {
            if (R == get_iff_name()) {
                if (optional<congr_lemma> cgr = mk_rel_iff_congr(fn)) {
                    auto child_rel_names = rel_names_from_arg_kinds(cgr->get_arg_kinds(), const_name(fn));
                    bool lift_needed = false;
                    return optional<ext_congr_lemma>(R, *cgr, child_rel_names, lift_needed);
                }
            }
            if (optional<congr_lemma> cgr = mk_rel_eq_congr(fn)) {
                bool heq_proof       = false;
                if (g_heq_based && R == get_heq_name()) {
                    heq_proof        = true;
                }
                auto child_rel_names = rel_names_from_arg_kinds(cgr->get_arg_kinds(), const_name(fn));
                bool lift_needed     = R != get_eq_name();
                ext_congr_lemma r(R, *cgr, child_rel_names, lift_needed);
                r.m_heq_result       = heq_proof;
                return optional<ext_congr_lemma>(r);
            }
        }
    }
    return optional<ext_congr_lemma>();
}

/* Automatically generated lemma for function application \c e. The lemma is specialized using the
   specialization prefix for \c e. */
static optional<ext_congr_lemma> mk_ext_specialized_congr_lemma(name const & R, expr const & e) {
    optional<congr_lemma> eq_congr = mk_specialized_congr_lemma(e);
    if (!eq_congr)
        return optional<ext_congr_lemma>();
    ext_congr_lemma res1(*eq_congr);
    /* If all arguments are Eq kind, then we can use generic congr axiom and consider equality for the function. */
    if (eq_congr->all_eq_kind())
        res1.m_fixed_fun = false;
    if (R == get_eq_name())
        return optional<ext_congr_lemma>(res1);
    bool lift_needed = true;
    return optional<ext_congr_lemma>(R, *eq_congr, lift_needed);
}

/* Automatically generated congruence lemma based on heterogeneous equality. */
static optional<ext_congr_lemma> mk_hcongr_lemma_core(name const & R, expr const & fn, unsigned nargs) {
    optional<congr_lemma> eq_congr = mk_hcongr_lemma(fn, nargs);
    if (!eq_congr)
        return optional<ext_congr_lemma>();
    ext_congr_lemma res1(*eq_congr);
    expr type = eq_congr->get_type();
    while (is_pi(type)) type = binding_body(type);
    /* If all arguments are Eq kind, then we can use generic congr axiom and consider equality for the function. */
    if (!is_heq(type) && eq_congr->all_eq_kind())
        res1.m_fixed_fun = false;
    lean_assert(is_eq(type) || is_heq(type));
    if (R == get_eq_name() || R == get_heq_name()) {
        res1.m_hcongr_lemma = true;
        if (is_heq(type))
            res1.m_heq_result = true;
        return optional<ext_congr_lemma>(res1);
    }
    /* If R is not equality (=) nor heterogeneous equality (==),
       we try to lift, but we can only lift if the congruence lemma produces an equality. */
    if (is_heq(type)) {
        /* We cannot lift heterogeneous equality. */
        return optional<ext_congr_lemma>();
    } else {
        bool lift_needed = true;
        ext_congr_lemma res2(R, *eq_congr, lift_needed);
        res2.m_hcongr_lemma = true;
        return optional<ext_congr_lemma>(res2);
    }
}

optional<ext_congr_lemma> mk_ext_congr_lemma(name const & R, expr const & e) {
    expr const & fn     = get_app_fn(e);
    unsigned nargs      = get_app_num_args(e);
    /* Check if (R, fn, nargs) is in the cache */
    congr_lemma_key key1(R, fn, nargs);
    auto it1 = g_congr_cache->find(key1);
    if (it1 != g_congr_cache->end())
        return it1->second;
    if (g_heq_based) {
        /* Check if there is user defined lemma for (R, fn, nargs).
           Remark: specialization prefix is irrelevan for used defined congruence lemmas. */
        auto lemma = mk_ext_user_congr_lemma(R, fn, nargs);
        /* Try automatically generated lemma for equivalence relation over iff/eq */
        if (!lemma) lemma = mk_relation_congr_lemma(R, fn, nargs);
        /* Try automatically generated congruence lemma with support for heterogeneous equality. */
        if (!lemma) lemma = mk_hcongr_lemma_core(R, fn, nargs);

        if (lemma) {
            /* succeeded */
            g_congr_cache->insert(mk_pair(key1, lemma));
            return lemma;
        }
    } else {
        lean_assert(!g_heq_based);
        /* When heterogeneous equality support is disabled, we use specialization prefix +
           congruence lemmas that take care of subsingletons */

        /* Check if (g := fn+specialization prefix) is in the cache */
        unsigned prefix_sz  = get_specialization_prefix_size(fn, nargs);
        unsigned rest_nargs = nargs - prefix_sz;
        expr g = e;
        for (unsigned i = 0; i < rest_nargs; i++) g = app_fn(g);
        congr_lemma_key key2(R, g, rest_nargs);
        auto it2 = g_congr_cache->find(key2);
        if (it2 != g_congr_cache->end())
            return it2->second;
        /* Check if there is user defined lemma for (R, fn, nargs).
           Remark: specialization prefix is irrelevan for used defined congruence lemmas. */
        if (auto lemma = mk_ext_user_congr_lemma(R, fn, nargs)) {
            g_congr_cache->insert(mk_pair(key1, lemma));
            return lemma;
        }
        /* Try automatically generated lemma for equivalence relation over iff/eq */
        if (auto lemma = mk_relation_congr_lemma(R, fn, nargs)) {
            g_congr_cache->insert(mk_pair(key1, lemma));
            return lemma;
        }
        /* Try automatically generated specialized congruence lemma */
        if (auto lemma = mk_ext_specialized_congr_lemma(R, e)) {
            if (prefix_sz == 0)
                g_congr_cache->insert(mk_pair(key1, lemma));
            else
                g_congr_cache->insert(mk_pair(key2, lemma));
            return lemma;
        }
    }
    /* cache failure */
    g_congr_cache->insert(mk_pair(key1, optional<ext_congr_lemma>()));
    return optional<ext_congr_lemma>();
}

optional<ext_congr_lemma> mk_ext_hcongr_lemma(expr const & fn, unsigned nargs) {
    congr_lemma_key key1(get_eq_name(), fn, nargs);
    auto it1 = g_congr_cache->find(key1);
    if (it1 != g_congr_cache->end())
        return it1->second;

    if (auto lemma = mk_hcongr_lemma_core(get_eq_name(), fn, nargs)) {
        /* succeeded */
        g_congr_cache->insert(mk_pair(key1, lemma));
        return lemma;
    }

    /* cache failure */
    g_congr_cache->insert(mk_pair(key1, optional<ext_congr_lemma>()));
    return optional<ext_congr_lemma>();
}

void congruence_closure::update_non_eq_relations(name const & R) {
    if (R == get_eq_name())
        return;
    if (std::find(m_non_eq_relations.begin(), m_non_eq_relations.end(), R) == m_non_eq_relations.end())
        m_non_eq_relations = cons(R, m_non_eq_relations);
}

void congruence_closure::add_occurrence(name const & Rp, expr const & parent, name const & Rc, expr const & child, bool eq_table) {
    child_key k(Rc, child);
    parent_occ_set ps;
    if (auto old_ps = m_parents.find(k))
        ps = *old_ps;
    ps.insert(parent_occ(Rp, parent, eq_table));
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

/** \brief Return true iff the given function application are congruent */
static bool is_eq_congruent(expr const & e1, expr const & e2) {
    lean_assert(is_app(e1) && is_app(e2));
    /* Given e1 := f a,  e2 := g b */
    expr f = app_fn(e1);
    expr a = app_arg(e1);
    expr g = app_fn(e2);
    expr b = app_arg(e2);
    if (g_cc->get_root(get_eq_name(), a) != g_cc->get_root(get_eq_name(), b)) {
        /* a and b are not equivalent */
        return false;
    }
    if (g_cc->get_root(get_eq_name(), f) != g_cc->get_root(get_eq_name(), g)) {
        /* f and g are not equivalent */
        return false;
    }
    if (is_def_eq(infer_type(f), infer_type(g))) {
        /* Case 1: f and g have the same type, then we can create a congruence proof for f a == g b */
        return true;
    }
    if (is_app(f) && is_app(g)) {
        /* Case 2: f and g are congruent */
        return is_eq_congruent(f, g);
    }
    /*
      f and g are not congruent nor they have the same type.
      We can't generate a congruence proof in this case because the following lemma

          hcongr : f1 == f2 -> a1 == a2 -> f1 a1 == f2 a2

      is not provable. Remark: it is also not provable in MLTT, Coq and Agda (even if we assume UIP).
    */
    return false;
}

int congruence_closure::eq_congr_key_cmp::operator()(eq_congr_key const & k1, eq_congr_key const & k2) const {
    lean_assert(g_heq_based);
    if (k1.m_hash != k2.m_hash)
        return unsigned_cmp()(k1.m_hash, k2.m_hash);
    if (is_eq_congruent(k1.m_expr, k2.m_expr))
        return 0;
    return expr_quick_cmp()(k1.m_expr, k2.m_expr);
}

/* \brief Create a equality congruence table key.
   \remark This table and key are only used when heterogeneous equality support is enabled. */
auto congruence_closure::mk_eq_congr_key(expr const & e) const -> eq_congr_key {
    lean_assert(is_app(e));
    eq_congr_key k;
    k.m_expr = e;
    expr const & f = app_fn(e);
    expr const & a = app_arg(e);
    unsigned h = hash(get_root(get_eq_name(), f).hash(), get_root(get_eq_name(), a).hash());
    k.m_hash = h;
    return k;
}

int congruence_closure::cmp_eq_iff_keys(congr_key const & k1, congr_key const & k2) const {
    lean_assert(k1.m_eq  == k2.m_eq);
    lean_assert(k1.m_iff == k2.m_iff);
    lean_assert(k1.m_eq  != k1.m_iff);
    name const & R = k1.m_eq ? get_eq_name() : get_iff_name();
    expr const & lhs1 = app_arg(app_fn(k1.m_expr));
    expr const & rhs1 = app_arg(k1.m_expr);
    expr const & lhs2 = app_arg(app_fn(k2.m_expr));
    expr const & rhs2 = app_arg(k2.m_expr);
    return compare_symm(R, lhs1, rhs1, lhs2, rhs2);
}

int congruence_closure::cmp_symm_rel_keys(congr_key const & k1, congr_key const & k2) const {
    name R1, R2;
    expr lhs1, rhs1, lhs2, rhs2;
    lean_verify(is_equivalence_relation_app(k1.m_expr, R1, lhs1, rhs1));
    lean_verify(is_equivalence_relation_app(k2.m_expr, R2, lhs2, rhs2));
    if (R1 != R2)
        return quick_cmp(R1, R2);
    return compare_symm(R1, lhs1, rhs1, lhs2, rhs2);
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
    if (k1.m_eq || k1.m_iff)
        return g_cc->cmp_eq_iff_keys(k1, k2);
    if (k1.m_symm_rel)
        return g_cc->cmp_symm_rel_keys(k1, k2);

    lean_assert(!k1.m_eq && !k2.m_eq && !k1.m_iff && !k2.m_iff &&
                !k1.m_symm_rel && !k2.m_symm_rel);
    lean_assert(k1.m_R == k2.m_R);
    buffer<expr> args1, args2;
    expr const & fn1 = get_app_args(k1.m_expr, args1);
    expr const & fn2 = get_app_args(k2.m_expr, args2);
    if (args1.size() != args2.size())
        return unsigned_cmp()(args1.size(), args2.size());
    auto lemma = mk_ext_congr_lemma(k1.m_R, k1.m_expr);
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
            case congr_arg_kind::HEq:
            case congr_arg_kind::Eq:
                lean_assert(head(*it1));
                r = g_cc->compare_root(*head(*it1), args1[i], args2[i]);
                if (r != 0) return r;
                break;
            case congr_arg_kind::Fixed:
            case congr_arg_kind::FixedNoParam:
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
                case congr_arg_kind::HEq:
                case congr_arg_kind::Eq:
                    lean_assert(head(*it1));
                    h = hash(h, get_root(*head(*it1), args[i]).hash());
                    break;
                case congr_arg_kind::Fixed:
                case congr_arg_kind::FixedNoParam:
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
    bool heq_proof = false;
    push_todo(get_iff_name(), e, mk_true(), *g_iff_true_mark, heq_proof);
}

void congruence_closure::add_eq_congruence_table(expr const & e) {
    lean_assert(is_app(e));
    lean_assert(g_heq_based);
    eq_congr_key k = mk_eq_congr_key(e);
    if (auto old_k = m_eq_congruences.find(k)) {
        /*
          Found new equivalence: e ~ old_k->m_expr
          1. Update m_cg_root field for e
        */
        eqc_key k(get_eq_name(), e);
        entry new_entry = *m_entries.find(k);
        new_entry.m_cg_root = old_k->m_expr;
        m_entries.insert(k, new_entry);
        /* 2. Put new equivalence in the TODO queue */
        /* TODO(Leo): check if the following line is a bottleneck */
        bool heq_proof = !is_def_eq(infer_type(e), infer_type(old_k->m_expr));
        push_todo(get_eq_name(), e, old_k->m_expr, *g_eq_congr_mark, heq_proof);
    } else {
        m_eq_congruences.insert(k);
    }
}

void congruence_closure::add_congruence_table(ext_congr_lemma const & lemma, expr const & e) {
    lean_assert(is_app(e));
    congr_key k = mk_congr_key(lemma, e);
    if (auto old_k = m_congruences.find(k)) {
        /*
          Found new equivalence: e ~ old_k->m_expr
          1. Update m_cg_root field for e
        */
        eqc_key k(lemma.m_R, e);
        entry new_entry = *m_entries.find(k);
        new_entry.m_cg_root = old_k->m_expr;
        m_entries.insert(k, new_entry);
        /* 2. Put new equivalence in the TODO queue */
        bool heq_proof = false;
        if (lemma.m_heq_result) {
            lean_assert(g_heq_based);
            if (!is_def_eq(infer_type(e), infer_type(old_k->m_expr)))
                heq_proof = true;
        }
        push_todo(lemma.m_R, e, old_k->m_expr, *g_congr_mark, heq_proof);
    } else {
        m_congruences.insert(k);
    }
    check_iff_true(k);
}

// TODO(Leo): this should not be hard-coded
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

/* This method is invoked during internalization and eagerly apply basic equivalences for term \c e
   Examples:
   - If e := cast H e', then it merges the equivalence classes of (cast H e') and e'

   In principle, we could mark theorems such as cast_eq as simplification rules, but this creates
   problems with the builtin support for cast-introduction in the ematching module.

   Eagerly merging the equivalence classes is also more efficient. */
void congruence_closure::apply_simple_eqvs(expr const & e) {
    if (g_heq_based) {
        /* equivalences when == support is enabled */
        if (is_app_of(e, get_cast_name(), 4)) {
            /* cast H a == a

               theorem cast_heq : ∀ {A B : Type.{l_1}} (H : A = B) (a : A), @cast.{l_1} A B H a == a
            */
            buffer<expr> args;
            expr const & cast = get_app_args(e, args);
            expr const & a    = args[3];
            expr proof     = mk_app(mk_constant(get_cast_heq_name(), const_levels(cast)), args);
            bool heq_proof = true;
            push_todo(get_eq_name(), e, a, proof, heq_proof);
        }

        if (is_app_of(e, get_eq_rec_name(), 6)) {
            /* eq.rec p H == p

               theorem eq_rec_heq : ∀ {A : Type.{l_1}} {P : A → Type.{l_2}} {a a' : A} (H : a = a') (p : P a), @eq.rec.{l_2 l_1} A a P p a' H == p
            */
            buffer<expr> args;
            expr const & eq_rec = get_app_args(e, args);
            expr A = args[0]; expr a = args[1]; expr P = args[2]; expr p = args[3];
            expr a_prime = args[4]; expr H = args[5];
            level l_2  = head(const_levels(eq_rec));
            level l_1  = head(tail(const_levels(eq_rec)));
            expr proof = mk_app({mk_constant(get_eq_rec_heq_name(), {l_1, l_2}), A, P, a, a_prime, H, p});
            bool heq_proof = true;
            push_todo(get_eq_name(), e, p, proof, heq_proof);
        }
    }
}

void congruence_closure::internalize_core(name R, expr const & e, bool toplevel, bool to_propagate) {
    lean_assert(closed(e));
    if (g_heq_based && R == get_heq_name())
        R = get_eq_name();
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
        mk_entry_core(R, e, to_propagate);
        return;
    case expr_kind::Lambda:
        mk_entry_core(R, e, false);
        return;
    case expr_kind::Macro:
        for (unsigned i = 0; i < macro_num_args(e); i++)
            internalize_core(R, macro_arg(e, i), false, false);
        mk_entry_core(R, e, to_propagate);
        break;
    case expr_kind::Pi:
        // TODO(Leo): should we support congruence for arrows?
        if (is_arrow(e) && is_prop(binding_domain(e)) && is_prop(binding_body(e))) {
            to_propagate = toplevel; // we must propagate children if arrow is top-level
            internalize_core(R, binding_domain(e), toplevel, to_propagate);
            internalize_core(R, binding_body(e), toplevel, to_propagate);
        }
        if (is_prop(e)) {
            mk_entry_core(R, e, false);
        }
        return;
    case expr_kind::App: {
        bool is_lapp = is_logical_app(e);
        mk_entry_core(R, e, to_propagate && !is_lapp);
        if (toplevel) {
            if (is_lapp) {
                to_propagate = true; // we must propagate the children of a top-level logical app (or, and, iff, ite)
            } else {
                toplevel = false;    // children of a non-logical application will not be marked as toplevel
            }
        } else {
            to_propagate = false;
        }
        if (auto lemma = mk_ext_congr_lemma(R, e)) {
            if (g_heq_based && lemma->m_hcongr_lemma && R == get_eq_name()) {
                internalize_core(R, app_fn(e), toplevel, to_propagate);
                internalize_core(R, app_arg(e), toplevel, to_propagate);
                bool eq_table = true;
                expr it = e;
                while (is_app(it)) {
                    add_occurrence(R, e, R, app_fn(it), eq_table);
                    add_occurrence(R, e, R, app_arg(it), eq_table);
                    it = app_fn(it);
                }
                add_eq_congruence_table(e);
            } else {
                /* Handle user-defined congruence lemmas, congruence lemmas for other relations,
                   and automatically generated lemmas for weakly-dependent-functions and relations. */
                bool eq_table = false;
                buffer<expr> args;
                expr const & fn = get_app_args(e, args);
                list<optional<name>> const * it = &(lemma->m_rel_names);
                for (expr const & arg : args) {
                    lean_assert(*it);
                    if (auto R1 = head(*it)) {
                        internalize_core(*R1, arg, toplevel, to_propagate);
                        add_occurrence(R, e, *R1, arg, eq_table);
                    }
                    it = &tail(*it);
                }
                if (!lemma->m_fixed_fun) {
                    internalize_core(get_eq_name(), fn, false, false);
                    add_occurrence(get_eq_name(), e, get_eq_name(), fn, eq_table);
                }
                add_congruence_table(*lemma, e);
            }
        }
        apply_simple_eqvs(e);
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
            if (p.m_eq_table) {
                eq_congr_key k = mk_eq_congr_key(p.m_expr);
                m_eq_congruences.erase(k);
            } else {
                auto lemma = mk_ext_congr_lemma(p.m_R, p.m_expr);
                lean_assert(lemma);
                congr_key k = mk_congr_key(*lemma, p.m_expr);
                m_congruences.erase(k);
            }
        });
}

void congruence_closure::reinsert_parents(name const & R, expr const & e) {
    auto ps = m_parents.find(child_key(R, e));
    if (!ps) return;
    ps->for_each([&](parent_occ const & p) {
            if (p.m_eq_table) {
                add_eq_congruence_table(p.m_expr);
            } else {
                auto lemma = mk_ext_congr_lemma(p.m_R, p.m_expr);
                lean_assert(lemma);
                add_congruence_table(*lemma, p.m_expr);
            }
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

void congruence_closure::propagate_no_confusion_eq(expr const & e1, expr const & e2) {
    lean_assert(is_constructor_app(env(), e1));
    lean_assert(is_constructor_app(env(), e2));
    /* Add equality e1 =?= e2 to set of hypotheses. no_confusion_action will process it */
    app_builder & b = get_app_builder();
    state & s       = curr_state();
    expr type       = b.mk_eq(e1, e2);
    expr pr         = *get_eqv_proof(get_eq_name(), e1, e2);
    expr H          = s.mk_hypothesis(type, pr);
    lean_trace(name({"cc", "propagation"}),
               tout() << "no confusion eq: " << ppb(H) << " : " << ppb(infer_type(H)) << "\n";);
}

/* Remark: If added_prop is not none, then it contains the proposition provided to ::add.
   We use it here to avoid an unnecessary propagation back to the current_state. */
void congruence_closure::add_eqv_step(name const & R, expr e1, expr e2, expr const & H, optional<expr> const & added_prop,
                                      bool heq_proof) {
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

    /* We want r2 to be the root of the combined class. */

    /*
     We swap (e1,n1,r1) with (e2,n2,r2) when
     1- r1->m_interpreted && !r2->m_interpreted.
        Reason: to decide when to propagate we check whether the root of the equivalence class
        is true/false. So, this condition is to make sure if true/false is an equivalence class,
        then one of them is the root. If both are, it doesn't matter, since the state is inconsistent
        anyway.
     2- r1->m_constructor && !r2->m_interpreted && !r2->m_constructor
        Reason: we want constructors to be the representative of their equivalence classes.
     3- r1->m_size > r2->m_size && !r2->m_interpreted && !r2->m_constructor
        Reason: performance.
    */
    if ((r1->m_interpreted && !r2->m_interpreted) ||
        (r1->m_constructor && !r2->m_interpreted && !r2->m_constructor) ||
        (r1->m_size > r2->m_size && !r2->m_interpreted && !r2->m_constructor)) {
        std::swap(e1, e2);
        std::swap(n1, n2);
        std::swap(r1, r2);
        // Remark: we don't apply symmetry eagerly. So, we don't adjust H.
        flipped = true;
    }

    if (r1->m_interpreted && r2->m_interpreted)
        m_inconsistent = true;

    bool use_no_confusion = R == get_eq_name() && r1->m_constructor && r2->m_constructor;

    expr e1_root   = n1->m_root;
    expr e2_root   = n2->m_root;
    entry new_n1   = *n1;

    /*
     Following target/proof we have
     e1 -> ... -> r1
     e2 -> ... -> r2
     We want
     r1 -> ... -> e1 -> e2 -> ... -> r2
    */
    invert_trans(R, e1);
    new_n1.m_target  = e2;
    new_n1.m_proof   = H;
    new_n1.m_flipped = flipped;
    m_entries.insert(eqc_key(R, e1), new_n1);

    /* The hash code for the parents is going to change */
    remove_parents(R, e1_root);

    /* force all m_root fields in e1 equivalence class to point to e2_root */
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
    if (heq_proof)
        new_r2.m_heq_proofs = true;
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
                bool propagate_back = false;
                mk_entry(R2, e1, propagate_back);
                mk_entry(R2, e2, propagate_back);
                bool heq_proof = false;
                push_todo(R2, e1, e2, *g_lift_mark, heq_proof);
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

    if (use_no_confusion) {
        propagate_no_confusion_eq(e1_root, e2_root);
    }

    update_mt(R, e2_root);
    if (R == get_eq_name()) {
        check_new_subsingleton_eq(e1_root, e2_root);
    }
    lean_trace(name({"cc", "merge"}), tout() << ppb(e1_root) << " [" << R << "] " << ppb(e2_root) << "\n";);
    lean_trace(name({"cc", "state"}), trace(););
}

void congruence_closure::process_todo(optional<expr> const & added_prop) {
    auto & todo = get_todo();
    while (!todo.empty()) {
        name R; expr lhs, rhs, H; bool heq_proof;
        std::tie(R, lhs, rhs, H, heq_proof) = todo.back();
        todo.pop_back();
        add_eqv_step(R, lhs, rhs, H, added_prop, heq_proof);
    }
}

void congruence_closure::add_eqv_core(name const & R, expr const & lhs, expr const & rhs, expr const & H,
                                      optional<expr> const & added_prop, bool heq_proof) {
    push_todo(R, lhs, rhs, H, heq_proof);
    process_todo(added_prop);
}

void congruence_closure::add_eqv(name const & R, expr const & lhs, expr const & rhs, expr const & H) {
    if (is_inconsistent())
        return;
    flet<congruence_closure *> set_cc(g_cc, this);
    clear_todo();
    bool toplevel = false; bool to_propagate = false;
    bool heq_proof = false;
    name _R = R;
    if (g_heq_based && R == get_heq_name()) {
        heq_proof = true;
        _R = get_eq_name();
    }
    internalize_core(_R, lhs, toplevel, to_propagate);
    internalize_core(_R, rhs, toplevel, to_propagate);
    add_eqv_core(_R, lhs, rhs, H, none_expr(), heq_proof);
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
            bool heq_proof = false;
            internalize_core(get_iff_name(), p, toplevel, to_propagate);
            add_eqv_core(get_iff_name(), p, mk_false(), mk_iff_false_intro(proof), some_expr(type), heq_proof);
        } else {
            bool toplevel  = false; bool to_propagate = false;
            bool heq_proof = false;
            if (g_heq_based && R == get_heq_name()) {
                /* When heterogeneous equality support is enabled, we
                   store equality and heterogeneous equality are stored in the same equivalence classes. */
                R = get_eq_name();
                heq_proof = true;
            }
            internalize_core(R, lhs, toplevel, to_propagate);
            internalize_core(R, rhs, toplevel, to_propagate);
            add_eqv_core(R, lhs, rhs, proof, some_expr(type), heq_proof);
        }
    } else if (is_prop(p)) {
        bool toplevel = true; bool to_propagate = false;
        bool heq_proof = false;
        internalize_core(get_iff_name(), p, toplevel, to_propagate);
        if (is_neg) {
            add_eqv_core(get_iff_name(), p, mk_false(), mk_iff_false_intro(proof), some_expr(type), heq_proof);
        } else {
            add_eqv_core(get_iff_name(), p, mk_true(), mk_iff_true_intro(proof), some_expr(type), heq_proof);
        }
    }
}

bool congruence_closure::has_heq_proofs(expr const & root) const {
    lean_assert(m_entries.find(eqc_key(get_eq_name(), root)));
    lean_assert(m_entries.find(eqc_key(get_eq_name(), root))->m_root == root);
    return m_entries.find(eqc_key(get_eq_name(), root))->m_heq_proofs;
}

bool congruence_closure::is_eqv(name const & R, expr const & e1, expr const & e2) const {
    name R_norm = R;
    if (g_heq_based && R == get_heq_name()) {
        R_norm = get_eq_name();
    }
    auto n1 = m_entries.find(eqc_key(R_norm, e1));
    if (!n1) return false;
    auto n2 = m_entries.find(eqc_key(R_norm, e2));
    if (!n2) return false;
    /* Remark: this method assumes that is_eqv is invoked with type correct parameters.
       An eq class may contain equality and heterogeneous equality proofs when g_heq_based
       is enabled. When this happens, the answer is correct only if e1 and e2 have the same type.
    */
    return n1->m_root == n2->m_root;
}

expr congruence_closure::mk_eq_congr_proof(expr const & lhs, expr const & rhs, bool heq_proofs) const {
    lean_assert(g_heq_based);
    app_builder & b = get_app_builder();
    buffer<expr> lhs_args, rhs_args;
    expr const * lhs_it = &lhs;
    expr const * rhs_it = &rhs;
    if (lhs != rhs) {
        while (true) {
            lean_assert(is_eqv(get_eq_name(), *lhs_it, *rhs_it));
            lhs_args.push_back(app_arg(*lhs_it));
            rhs_args.push_back(app_arg(*rhs_it));
            lhs_it = &app_fn(*lhs_it);
            rhs_it = &app_fn(*rhs_it);
            if (*lhs_it == *rhs_it)
                break;
            if (is_def_eq(infer_type(*lhs_it), infer_type(*rhs_it)))
                break;
        }
    }
    if (lhs_args.empty()) {
        if (heq_proofs)
            return b.mk_heq_refl(lhs);
        else
            return b.mk_eq_refl(lhs);
    }
    std::reverse(lhs_args.begin(), lhs_args.end());
    std::reverse(rhs_args.begin(), rhs_args.end());
    lean_assert(lhs_args.size() == rhs_args.size());
    expr const & lhs_fn = *lhs_it;
    expr const & rhs_fn = *rhs_it;
    lean_assert(is_eqv(get_eq_name(), lhs_fn, rhs_fn) || is_def_eq(lhs_fn, rhs_fn));
    lean_assert(is_def_eq(infer_type(lhs_fn), infer_type(rhs_fn)));
    /* Create proof for
          (lhs_fn lhs_args[0] ... lhs_args[n-1]) = (lhs_fn rhs_args[0] ... rhs_args[n-1])
       where
          n == lhs_args.size()
    */
    auto spec_lemma = mk_ext_hcongr_lemma(lhs_fn, lhs_args.size());
    lean_assert(spec_lemma);
    list<congr_arg_kind> const * kinds_it = &spec_lemma->m_congr_lemma.get_arg_kinds();
    buffer<expr> lemma_args;
    for (unsigned i = 0; i < lhs_args.size(); i++) {
        lean_assert(kinds_it);
        lemma_args.push_back(lhs_args[i]);
        lemma_args.push_back(rhs_args[i]);
        if (head(*kinds_it) == congr_arg_kind::HEq) {
            lemma_args.push_back(*get_eqv_proof(get_heq_name(), lhs_args[i], rhs_args[i]));
        } else {
            lean_assert(head(*kinds_it) == congr_arg_kind::Eq);
            lemma_args.push_back(*get_eqv_proof(get_eq_name(), lhs_args[i], rhs_args[i]));
        }
        kinds_it = &(tail(*kinds_it));
    }
    expr r = mk_app(spec_lemma->m_congr_lemma.get_proof(), lemma_args);
    if (spec_lemma->m_heq_result && !heq_proofs)
        r = b.mk_eq_of_heq(r);
    else if (!spec_lemma->m_heq_result && heq_proofs)
        r = b.mk_heq_of_eq(r);
    if (is_def_eq(lhs_fn, rhs_fn))
        return r;
    /* Convert r into a proof of lhs = rhs using eq.rec and
       the proof that lhs_fn = rhs_fn */
    expr lhs_fn_eq_rhs_fn = *get_eqv_proof(get_eq_name(), lhs_fn, rhs_fn);
    expr x                = mk_fresh_local(infer_type(lhs_fn));
    expr motive_rhs       = mk_app(x, rhs_args);
    expr motive           = heq_proofs ? b.mk_heq(lhs, motive_rhs) : b.mk_eq(lhs, motive_rhs);
    return b.mk_eq_rec(Fun(x, motive), r, lhs_fn_eq_rhs_fn);
}

expr congruence_closure::mk_congr_proof_core(name const & R, expr const & lhs, expr const & rhs, bool heq_proofs) const {
    app_builder & b = get_app_builder();
    buffer<expr> lhs_args, rhs_args;
    expr const & lhs_fn = get_app_args(lhs, lhs_args);
    expr const & rhs_fn = get_app_args(rhs, rhs_args);
    lean_assert(lhs_args.size() == rhs_args.size());
    auto lemma = mk_ext_congr_lemma(R, lhs);
    lean_assert(lemma);
    if (lemma->m_fixed_fun) {
        /* Main case: convers user-defined congruence lemmas, and
           all automatically generated congruence lemmas */
        list<optional<name>> const * it1 = &lemma->m_rel_names;
        list<congr_arg_kind> const * it2 = &lemma->m_congr_lemma.get_arg_kinds();
        buffer<expr> lemma_args;
        for (unsigned i = 0; i < lhs_args.size(); i++) {
            lean_assert(*it1 && *it2);
            switch (head(*it2)) {
            case congr_arg_kind::HEq:
                lemma_args.push_back(lhs_args[i]);
                lemma_args.push_back(rhs_args[i]);
                lemma_args.push_back(*get_eqv_proof(get_heq_name(), lhs_args[i], rhs_args[i]));
                break;
            case congr_arg_kind::Eq:
                lean_assert(head(*it1));
                lemma_args.push_back(lhs_args[i]);
                lemma_args.push_back(rhs_args[i]);
                lemma_args.push_back(*get_eqv_proof(*head(*it1), lhs_args[i], rhs_args[i]));
                break;
            case congr_arg_kind::Fixed:
                lemma_args.push_back(lhs_args[i]);
                break;
            case congr_arg_kind::FixedNoParam:
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
        if (lemma->m_lift_needed) {
            r = b.lift_from_eq(R, r);
        }
        if (g_heq_based) {
            if (lemma->m_heq_result && !heq_proofs)
                r = b.mk_eq_of_heq(r);
            else if (!lemma->m_heq_result && heq_proofs)
                r = b.mk_heq_of_eq(r);
        }
        return r;
    } else {
        /* This branch builds congruence proofs that handle equality between functions.
           The proof is created using congr_arg/congr_fun/congr lemmas.
           It can build proofs for congruence such as:
                f = g -> a = b -> f a = g b
           but it is limited to simply typed functions. */
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
        if (g_heq_based && heq_proofs)
            r = b.mk_heq_of_eq(*r);
        return *r;
    }
}

expr congruence_closure::mk_congr_proof(name const & R, expr const & e1, expr const & e2, bool heq_proofs) const {
    name R1; expr lhs1, rhs1;
    if (is_equivalence_relation_app(e1, R1, lhs1, rhs1)) {
        name R2; expr lhs2, rhs2;
        if (is_equivalence_relation_app(e2, R2, lhs2, rhs2) && R1 == R2) {
            if (!is_eqv(R1, lhs1, lhs2)) {
                lean_assert(is_eqv(R1, lhs1, rhs2));
                /*
                   We must apply symmetry.
                   The congruence table is implicitly using symmetry.
                   That is, we have
                        e1 := lhs1 ~R1~ rhs1
                   and
                        e2 := lhs2 ~R1~ rhs2
                   But,
                        (lhs1 ~R1 ~rhs2) and (rhs1 ~R1~ lhs2)
                */

                /* Given e1 := lhs1 ~R1~ rhs1,
                   create proof for
                         (lhs1 ~R1~ rhs1) <-> (rhs1 ~R1~ lhs1)
                */
                app_builder & b = get_app_builder();
                expr new_e1 = b.mk_rel(R1, rhs1, lhs1);
                expr h1  = mk_fresh_local(e1);
                expr h2  = mk_fresh_local(new_e1);
                expr e1_eqv_new_e1 = b.mk_app(get_iff_intro_name(),
                                              Fun(h1, b.mk_symm(R1, h1)),
                                              Fun(h2, b.mk_symm(R1, h2)));
                if (R != get_iff_name()) {
                    /* Convert
                          (lhs1 ~R1~ rhs1) <-> (rhs1 ~R1~ lhs1)
                       into
                          (lhs1 ~R1~ rhs1) ~R~ (rhs1 ~R1~ lhs1)
                    */
                    e1_eqv_new_e1 = b.mk_app(get_propext_name(), e1_eqv_new_e1);
                    if (R != get_eq_name())
                        e1_eqv_new_e1 = b.lift_from_eq(R, e1_eqv_new_e1);
                }
                bool cgr_heq_proofs = g_heq_based && R == get_heq_name();
                /*  Create transitivity proof
                         (lhs1 ~R1~ rhs1) ~R~ (rhs1 ~R1~ lhs1) ~R~ (lhs2 ~R1~ rhs2)
                */
                expr r = b.mk_trans(R, e1_eqv_new_e1, mk_congr_proof_core(R, new_e1, e2, cgr_heq_proofs));
                if (g_heq_based) {
                    if (cgr_heq_proofs && !heq_proofs)
                        r = b.mk_eq_of_heq(r);
                    else if (!cgr_heq_proofs && heq_proofs)
                        r = b.mk_heq_of_eq(r);
                }
                return r;
            }
        }
    }
    return mk_congr_proof_core(R, e1, e2, heq_proofs);
}

expr congruence_closure::mk_proof(name const & R, expr const & lhs, expr const & rhs, expr const & H, bool heq_proofs) const {
    if (H == *g_eq_congr_mark) {
        return mk_eq_congr_proof(lhs, rhs, heq_proofs);
    } else if (H == *g_congr_mark) {
        return mk_congr_proof(R, lhs, rhs, heq_proofs);
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

static expr flip_proof(name const & R, expr const & H, bool flipped, bool heq_proofs) {
    if (H == *g_eq_congr_mark || H == *g_congr_mark || H == *g_iff_true_mark || H == *g_lift_mark) {
        return H;
    } else {
        auto & b = get_app_builder();
        expr new_H = H;
        if (heq_proofs && is_eq(relaxed_whnf(infer_type(new_H)))) {
            new_H = b.mk_heq_of_eq(new_H);
        }
        if (!flipped) {
            return new_H;
        } else {
            return b.mk_symm(R, new_H);
        }
    }
}

static expr mk_trans(name const & R, optional<expr> const & H1, expr const & H2) {
    return !H1 ? H2 : get_app_builder().mk_trans(R, *H1, H2);
}

optional<expr> congruence_closure::get_eqv_proof(name const & R, expr const & e1, expr const & e2) const {
    app_builder & b = get_app_builder();
    name R_key = R; // We use R_key to access the equivalence class data
    if (g_heq_based && R == get_heq_name()) {
        R_key = get_eq_name();
    }
    if (has_expr_metavar(e1) || has_expr_metavar(e2)) return none_expr();
    if (is_def_eq(e1, e2))
        return some_expr(b.lift_from_eq(R, b.mk_eq_refl(e1)));
    auto n1 = m_entries.find(eqc_key(R_key, e1));
    if (!n1) return none_expr();
    auto n2 = m_entries.find(eqc_key(R_key, e2));
    if (!n2) return none_expr();
    if (n1->m_root != n2->m_root) return none_expr();
    bool heq_proofs = R_key == get_eq_name() && has_heq_proofs(n1->m_root);
    // R_trans is the relation we use to build the transitivity proofs
    name R_trans = heq_proofs ? get_heq_name() : R_key;
    // 1. Retrieve "path" from e1 to root
    buffer<expr> path1, Hs1;
    rb_tree<expr, expr_quick_cmp> visited;
    expr it1 = e1;
    while (true) {
        visited.insert(it1);
        auto it1_n = m_entries.find(eqc_key(R_key, it1));
        lean_assert(it1_n);
        if (!it1_n->m_target)
            break;
        path1.push_back(*it1_n->m_target);
        Hs1.push_back(flip_proof(R_trans, *it1_n->m_proof, it1_n->m_flipped, heq_proofs));
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
        auto it2_n = m_entries.find(eqc_key(R_key, it2));
        lean_assert(it2_n);
        lean_assert(it2_n->m_target);
        path2.push_back(it2);
        Hs2.push_back(flip_proof(R_trans, *it2_n->m_proof, !it2_n->m_flipped, heq_proofs));
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
        pr  = mk_trans(R_trans, pr, mk_proof(R, lhs, path1[i], Hs1[i], heq_proofs));
        lhs = path1[i];
    }
    unsigned i = Hs2.size();
    while (i > 0) {
        --i;
        pr  = mk_trans(R_trans, pr, mk_proof(R, lhs, path2[i], Hs2[i], heq_proofs));
        lhs = path2[i];
    }
    lean_assert(pr);
    if (g_heq_based) {
        if (heq_proofs && R == get_eq_name())
            pr = b.mk_eq_of_heq(*pr);
        else if (!heq_proofs && R == get_heq_name())
            pr = b.mk_heq_of_eq(*pr);
    }
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

bool congruence_closure::eq_class_heterogeneous(expr const & e) const {
    expr root = get_root(get_eq_name(), e);
    if (auto e = m_entries.find(eqc_key(get_eq_name(), root))) return e->m_heq_proofs;
    else return false;
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
    g_eq_congr_mark = new expr(mk_constant(name(prefix, "[eq-congruence]")));
    g_congr_mark    = new expr(mk_constant(name(prefix, "[congruence]")));
    g_iff_true_mark = new expr(mk_constant(name(prefix, "[iff-true]")));
    g_lift_mark     = new expr(mk_constant(name(prefix, "[lift]")));

    g_blast_cc_heq           = new name{"blast", "cc", "heq"};
    g_blast_cc_subsingleton  = new name{"blast", "cc", "subsingleton"};

    register_bool_option(*g_blast_cc_heq, LEAN_DEFAULT_BLAST_CC_HEQ,
                         "(blast) enable support for heterogeneous equality "
                         "and more general congruence lemmas in the congruence closure module "
                         "(this option is ignore in HoTT mode)");

    register_bool_option(*g_blast_cc_subsingleton, LEAN_DEFAULT_BLAST_CC_SUBSINGLETON,
                         "(blast) enable support for subsingleton equality propagation in congruence closure module");
}

void finalize_congruence_closure() {
    delete g_blast_cc_heq;
    delete g_blast_cc_subsingleton;
    delete g_eq_congr_mark;
    delete g_congr_mark;
    delete g_iff_true_mark;
    delete g_lift_mark;
}
}}
