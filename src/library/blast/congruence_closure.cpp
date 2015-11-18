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

void congruence_closure::mk_entry_for(name const & R, expr const & e) {
    lean_assert(!m_entries.find(eqc_key(R, e)));
    entry n;
    n.m_next    = e;
    n.m_root    = e;
    n.m_cg_root = e;
    n.m_rank    = 0;
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
    // TODO(Leo):
    std::cout << Rp << parent << Rc << child << "\n";
}

void congruence_closure::add_congruence_table(ext_congr_lemma const & lemma, expr const & e) {
    // TODO(Leo):
    std::cout << lemma.m_R << e << "\n";
}

void congruence_closure::internalize(name const & R, expr const & e) {
    lean_assert(closed(e));
    if (has_expr_metavar(e))
        return;
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

typedef std::tuple<name, expr, expr, expr> cc_todo_entry;

MK_THREAD_LOCAL_GET_DEF(std::vector<cc_todo_entry>, get_todo);

static void clear_todo() {
    get_todo().clear();
}

void congruence_closure::add_eqv(name const & R, expr const & lhs, expr const & rhs, expr const & pr) {
    auto & todo = get_todo();
    todo.emplace_back(R, lhs, rhs, pr);
    while (!todo.empty()) {
        name R; expr lhs, rhs, pr;
        std::tie(R, lhs, rhs, pr) = todo.back();
        todo.pop_back();
        // TODO(Leo): process
    }
}

void congruence_closure::add(hypothesis_idx hidx) {
    if (is_inconsistent())
        return;
    clear_todo();
    state & s       = curr_state();
    app_builder & b = get_app_builder();
    hypothesis const * h = s.get_hypothesis_decl(hidx);
    lean_assert(h);
    try {
        expr const & type = h->get_type();
        expr p;
        bool is_neg = is_not(type, p);
        if (is_neg && !is_standard(env()))
            return;
        name R; expr lhs, rhs;
        if (is_relation_app(p, R, lhs, rhs)) {
            if (is_neg) {
                internalize(get_iff_name(), p);
                add_eqv(get_iff_name(), p, mk_false(), b.mk_iff_false_intro(h->get_self()));
            } else {
                internalize(R, lhs);
                internalize(R, rhs);
                add_eqv(R, lhs, rhs, h->get_self());
            }
        } else if (is_prop(p)) {
            internalize(get_iff_name(), p);
            if (is_neg) {
                add_eqv(get_iff_name(), p, mk_false(), b.mk_iff_false_intro(h->get_self()));
            } else {
                add_eqv(get_iff_name(), p, mk_true(), b.mk_iff_true_intro(h->get_self()));
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

bool congruence_closure::prove(expr const & e) const {
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
        return e;;
    }
}

expr congruence_closure::get_next(name const & R, expr const & e) const {
    if (auto n = m_entries.find(eqc_key(R, e))) {
        return n->m_next;
    } else {
        return e;;
    }
}

void congruence_closure::display() const {
    // TODO(Leo):
}

bool congruence_closure::check_invariant() const {
    // TODO(Leo):
    return true;
}
}}
