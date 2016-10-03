/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include <string>
#include <library/constants.h>
#include "util/priority_queue.h"
#include "util/sstream.h"
#include "util/flet.h"
#include "util/list_fn.h"
#include "util/name_hash_map.h"
#include "kernel/error_msgs.h"
#include "kernel/find_fn.h"
#include "kernel/instantiate.h"
#include "library/trace.h"
#include "library/num.h"
#include "library/cache_helper.h"
#include "library/scoped_ext.h"
#include "library/attribute_manager.h"
#include "library/type_context.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_name.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/simplifier/ceqv.h"
#include "library/tactic/simplifier/simp_lemmas.h"

namespace lean {

/* Caching */
struct simp_lemma_cache {
    typedef name_hash_map<simp_lemmas> cache;

    environment                        m_env;
    cache                              m_simp_lemma_cache;
    cache                              m_congr_lemma_cache;

    simp_lemma_cache(environment const & env): m_env(env) {}
    environment const & env() const { return m_env; }

    cache & simp_cache() { return m_simp_lemma_cache; }
    cache & congr_cache() { return m_congr_lemma_cache; }
};

typedef cache_compatibility_helper<simp_lemma_cache> simp_lemma_cache_helper;

MK_THREAD_LOCAL_GET_DEF(simp_lemma_cache_helper, get_slch);

simp_lemma_cache & get_simp_lemma_cache_for(type_context const & ctx) {
    return get_slch().get_cache_for(ctx);
}

/* Validation */

LEAN_THREAD_VALUE(bool, g_throw_ex, false);
void validate_simp(type_context & tctx, name const & n);
void validate_congr(type_context & tctx, name const & n);

void on_add_simp_lemma(environment const & env, name const & c, bool) {
    type_context tctx(env);
    validate_simp(tctx, c);
}

void on_add_congr_lemma(environment const & env, name const & c, bool) {
    type_context tctx(env);
    validate_congr(tctx, c);
}

/* Getters/checkers */

static void report_failure(sstream const & strm) {
    if (g_throw_ex){
        throw exception(strm);
    } else {
        lean_trace(name({"simplifier", "failure"}),
                   tout() << strm.str() << "\n";);
    }
}

simp_lemmas add_core(tmp_type_context & tmp_tctx, simp_lemmas const & s,
                     name const & id, levels const & univ_metas, expr const & e, expr const & h,
                     unsigned priority) {
    list<expr_pair> ceqvs   = to_ceqvs(tmp_tctx, e, h);
    if (is_nil(ceqvs)) {
        report_failure(sstream() << "invalid [simp] lemma '" << id << "' : " << e);
        return s;
    }
    environment const & env = tmp_tctx.tctx().env();
    simp_lemmas new_s = s;
    for (expr_pair const & p : ceqvs) {
        /* We only clear the eassignment since we want to reuse the temporary universe metavariables associated
           with the declaration. */
        tmp_tctx.clear_eassignment();
        expr rule  = tmp_tctx.whnf(p.first);
        expr proof = tmp_tctx.whnf(p.second);
        bool is_perm = is_permutation_ceqv(env, rule);
        buffer<expr> emetas;
        buffer<bool> instances;
        while (is_pi(rule)) {
            expr mvar = tmp_tctx.mk_tmp_mvar(binding_domain(rule));
            emetas.push_back(mvar);
            instances.push_back(binding_info(rule).is_inst_implicit());
            rule = tmp_tctx.whnf(instantiate(binding_body(rule), mvar));
            proof = mk_app(proof, mvar);
        }
        expr rel, lhs, rhs;
        if (is_simp_relation(env, rule, rel, lhs, rhs) && is_constant(rel)) {
            new_s.insert(const_name(rel), simp_lemma(id, univ_metas, reverse_to_list(emetas),
                                                     reverse_to_list(instances), lhs, rhs, proof, is_perm, priority));
        }
    }
    return new_s;
}

static simp_lemmas add_core(tmp_type_context & tmp_tctx, simp_lemmas const & s, name const & cname, unsigned priority) {
    declaration const & d = tmp_tctx.tctx().env().get(cname);
    buffer<level> us;
    unsigned num_univs = d.get_num_univ_params();
    for (unsigned i = 0; i < num_univs; i++) {
        us.push_back(tmp_tctx.mk_tmp_univ_mvar());
    }
    levels ls = to_list(us);
    expr e    = tmp_tctx.whnf(instantiate_type_univ_params(d, ls));
    expr h    = mk_constant(cname, ls);
    return add_core(tmp_tctx, s, cname, ls, e, h, priority);
}


// Return true iff lhs is of the form (B (x : ?m1), ?m2) or (B (x : ?m1), ?m2 x),
// where B is lambda or Pi
static bool is_valid_congr_rule_binding_lhs(expr const & lhs, name_set & found_mvars) {
    lean_assert(is_binding(lhs));
    expr const & d = binding_domain(lhs);
    expr const & b = binding_body(lhs);
    if (!is_metavar(d))
        return false;
    if (is_metavar(b) && b != d) {
        found_mvars.insert(mlocal_name(b));
        found_mvars.insert(mlocal_name(d));
        return true;
    }
    if (is_app(b) && is_metavar(app_fn(b)) && is_var(app_arg(b), 0) && app_fn(b) != d) {
        found_mvars.insert(mlocal_name(app_fn(b)));
        found_mvars.insert(mlocal_name(d));
        return true;
    }
    return false;
}

// Return true iff all metavariables in e are in found_mvars
static bool only_found_mvars(expr const & e, name_set const & found_mvars) {
    return !find(e, [&](expr const & m, unsigned) {
            return is_metavar(m) && !found_mvars.contains(mlocal_name(m));
        });
}

// Check whether rhs is of the form (mvar l_1 ... l_n) where mvar is a metavariable,
// and l_i's are local constants, and mvar does not occur in found_mvars.
// If it is return true and update found_mvars
static bool is_valid_congr_hyp_rhs(expr const & rhs, name_set & found_mvars) {
    buffer<expr> rhs_args;
    expr const & rhs_fn = get_app_args(rhs, rhs_args);
    if (!is_metavar(rhs_fn) || found_mvars.contains(mlocal_name(rhs_fn)))
        return false;
    for (expr const & arg : rhs_args)
        if (!is_local(arg))
            return false;
    found_mvars.insert(mlocal_name(rhs_fn));
    return true;
}

simp_lemmas add_congr_core(tmp_type_context & tmp_tctx, simp_lemmas const & s, name const & n, unsigned prio) {
    declaration const & d = tmp_tctx.tctx().env().get(n);
    buffer<level> us;
    unsigned num_univs = d.get_num_univ_params();
    for (unsigned i = 0; i < num_univs; i++) {
        us.push_back(tmp_tctx.mk_tmp_univ_mvar());
    }
    levels ls = to_list(us);
    expr rule    = tmp_tctx.whnf(instantiate_type_univ_params(d, ls));
    expr proof   = mk_constant(n, ls);

    buffer<expr> emetas;
    buffer<bool> instances, explicits;

    while (is_pi(rule)) {
        expr mvar = tmp_tctx.mk_tmp_mvar(binding_domain(rule));
        emetas.push_back(mvar);
        explicits.push_back(is_explicit(binding_info(rule)));
        instances.push_back(binding_info(rule).is_inst_implicit());
        rule = tmp_tctx.whnf(instantiate(binding_body(rule), mvar));
        proof = mk_app(proof, mvar);
    }
    expr rel, lhs, rhs;
    if (!is_simp_relation(tmp_tctx.tctx().env(), rule, rel, lhs, rhs) || !is_constant(rel)) {
        report_failure(sstream() << "invalid [congr] lemma, '" << n
                       << "' resulting type is not of the form t ~ s, where '~' is a transitive and reflexive relation");
    }
    name_set found_mvars;
    buffer<expr> lhs_args, rhs_args;
    expr const & lhs_fn = get_app_args(lhs, lhs_args);
    expr const & rhs_fn = get_app_args(rhs, rhs_args);
    if (is_constant(lhs_fn)) {
        if (!is_constant(rhs_fn) || const_name(lhs_fn) != const_name(rhs_fn) || lhs_args.size() != rhs_args.size()) {
            report_failure(sstream() << "invalid [congr] lemma, '" << n
                           << "' resulting type is not of the form (" << const_name(lhs_fn) << "  ...) "
                           << "~ (" << const_name(lhs_fn) << " ...), where ~ is '" << const_name(rel) << "'");
        }
        for (expr const & lhs_arg : lhs_args) {
            if (is_sort(lhs_arg))
                continue;
            if (!is_metavar(lhs_arg) || found_mvars.contains(mlocal_name(lhs_arg))) {
                report_failure(sstream() << "invalid [congr] lemma, '" << n
                               << "' the left-hand-side of the congruence resulting type must be of the form ("
                               << const_name(lhs_fn) << " x_1 ... x_n), where each x_i is a distinct variable or a sort");
            }
            found_mvars.insert(mlocal_name(lhs_arg));
        }
    } else if (is_binding(lhs)) {
        if (lhs.kind() != rhs.kind()) {
            report_failure(sstream() << "invalid [congr] lemma, '" << n
                           << "' kinds of the left-hand-side and right-hand-side of "
                           << "the congruence resulting type do not match");
        }
        if (!is_valid_congr_rule_binding_lhs(lhs, found_mvars)) {
            report_failure(sstream() << "invalid [congr] lemma, '" << n
                           << "' left-hand-side of the congruence resulting type must "
                           << "be of the form (fun/Pi (x : A), B x)");
        }
    } else {
        report_failure(sstream() << "invalid [congr] lemma, '" << n
                       << "' left-hand-side is not an application nor a binding");
    }

    buffer<expr> congr_hyps;
    lean_assert(emetas.size() == explicits.size());
    for (unsigned i = 0; i < emetas.size(); i++) {
        expr const & mvar = emetas[i];
        if (explicits[i] && !found_mvars.contains(mlocal_name(mvar))) {
            buffer<expr> locals;
            expr type = mlocal_type(mvar);
            type_context::tmp_locals local_factory(tmp_tctx.tctx());
            while (is_pi(type)) {
                expr local = local_factory.push_local_from_binding(type);
                locals.push_back(local);
                type = instantiate(binding_body(type), local);
            }
            expr h_rel, h_lhs, h_rhs;
            if (!is_simp_relation(tmp_tctx.tctx().env(), type, h_rel, h_lhs, h_rhs) || !is_constant(h_rel))
                continue;
            unsigned j = 0;
            for (expr const & local : locals) {
                j++;
                if (!only_found_mvars(mlocal_type(local), found_mvars)) {
                    report_failure(sstream() << "invalid [congr] lemma, '" << n
                                   << "' argument #" << j << " of parameter #" << (i+1) << " contains "
                                   << "unresolved parameters");
                }
            }
            if (!only_found_mvars(h_lhs, found_mvars)) {
                report_failure(sstream() << "invalid [congr] lemma, '" << n
                               << "' argument #" << (i+1) << " is not a valid hypothesis, the left-hand-side contains "
                               << "unresolved parameters");
            }
            if (!is_valid_congr_hyp_rhs(h_rhs, found_mvars)) {
                report_failure(sstream() << "invalid [congr] lemma, '" << n
                               << "' argument #" << (i+1) << " is not a valid hypothesis, the right-hand-side must be "
                               << "of the form (m l_1 ... l_n) where m is parameter that was not "
                               << "'assigned/resolved' yet and l_i's are locals");
            }
            found_mvars.insert(mlocal_name(mvar));
            congr_hyps.push_back(mvar);
        }
    }
    simp_lemmas new_s = s;
    new_s.insert(const_name(rel), user_congr_lemma(n, ls, reverse_to_list(emetas),
                                                   reverse_to_list(instances), lhs, rhs, proof, to_list(congr_hyps), prio));
    return new_s;
}

simp_lemmas add_poly(type_context & tctx, simp_lemmas const & s, name const & id, unsigned priority) {
    tmp_type_context tmp_tctx(tctx);
    return add_core(tmp_tctx, s, id, priority);
}

simp_lemmas add(type_context & tctx, simp_lemmas const & s, name const & id, expr const & e, expr const & h, unsigned priority) {
    tmp_type_context tmp_tctx(tctx);
    return add_core(tmp_tctx, s, id, list<level>(), e, h, priority);
}

simp_lemmas join(simp_lemmas const & s1, simp_lemmas const & s2) {
    simp_lemmas new_s1 = s1;

    buffer<pair<name const &, simp_lemma const &>> slemmas;
    s2.for_each_simp([&](name const & eqv, simp_lemma const & r) {
            slemmas.push_back({eqv, r});
        });
    for (unsigned i = slemmas.size() - 1; i + 1 > 0; --i)
        new_s1.insert(slemmas[i].first, slemmas[i].second);

    buffer<pair<name const &, user_congr_lemma const &>> clemmas;
    s2.for_each_congr([&](name const & eqv, user_congr_lemma const & r) {
            clemmas.push_back({eqv, r});
        });
    for (unsigned i = clemmas.size() - 1; i + 1 > 0; --i)
        new_s1.insert(clemmas[i].first, clemmas[i].second);

    return new_s1;
}

void validate_simp(type_context & tctx, name const & n) {
    simp_lemmas s;
    flet<bool> set_ex(g_throw_ex, true);
    tmp_type_context tmp_tctx(tctx);
    add_core(tmp_tctx, s, n, LEAN_DEFAULT_PRIORITY);
}

void validate_congr(type_context & tctx, name const & n) {
    simp_lemmas s;
    flet<bool> set_ex(g_throw_ex, true);
    tmp_type_context tmp_tctx(tctx);
    add_congr_core(tmp_tctx, s, n, LEAN_DEFAULT_PRIORITY);
}

simp_lemma_core::simp_lemma_core(name const & id, levels const & umetas, list<expr> const & emetas,
                                 list<bool> const & instances, expr const & lhs, expr const & rhs, expr const & proof,
                                 unsigned priority):
    m_id(id), m_umetas(umetas), m_emetas(emetas), m_instances(instances),
    m_lhs(lhs), m_rhs(rhs), m_proof(proof), m_priority(priority) {}

simp_lemma::simp_lemma(name const & id, levels const & umetas, list<expr> const & emetas,
                       list<bool> const & instances, expr const & lhs, expr const & rhs, expr const & proof,
                       bool is_perm, unsigned priority):
    simp_lemma_core(id, umetas, emetas, instances, lhs, rhs, proof, priority),
    m_is_permutation(is_perm) {}

bool operator==(simp_lemma const & r1, simp_lemma const & r2) {
    return r1.m_lhs == r2.m_lhs && r1.m_rhs == r2.m_rhs;
}

format simp_lemma::pp(formatter const & fmt) const {
    format r;
    r += format("[") + format(get_id()) + format("]") + space();
    r += format("#") + format(get_num_emeta());
    if (m_priority != LEAN_DEFAULT_PRIORITY)
        r += space() + paren(format(m_priority));
    if (m_is_permutation)
        r += space() + format("perm");
    format r1 = comma() + space() + fmt(get_lhs());
    r1       += space() + format("↦") + pp_indent_expr(fmt, get_rhs());
    r += group(r1);
    return r;
}

user_congr_lemma::user_congr_lemma(name const & id, levels const & umetas, list<expr> const & emetas,
                                   list<bool> const & instances, expr const & lhs, expr const & rhs, expr const & proof,
                                   list<expr> const & congr_hyps, unsigned priority):
    simp_lemma_core(id, umetas, emetas, instances, lhs, rhs, proof, priority),
    m_congr_hyps(congr_hyps) {}

bool operator==(user_congr_lemma const & r1, user_congr_lemma const & r2) {
    return r1.m_lhs == r2.m_lhs && r1.m_rhs == r2.m_rhs && r1.m_congr_hyps == r2.m_congr_hyps;
}

format user_congr_lemma::pp(formatter const & fmt) const {
    format r;
    r += format("[") + format(get_id()) + format("]") + space();
    r += format("#") + format(get_num_emeta());
    if (m_priority != LEAN_DEFAULT_PRIORITY)
        r += space() + paren(format(m_priority));
    format r1;
    for (expr const & h : m_congr_hyps) {
        r1 += space() + paren(fmt(mlocal_type(h)));
    }
    r += group(r1);
    r += space() + format(":") + space();
    format r2 = paren(fmt(get_lhs()));
    r2       += space() + format("↦") + space() + paren(fmt(get_rhs()));
    r += group(r2);
    return r;
}

simp_lemmas_for::simp_lemmas_for(name const & eqv):
    m_eqv(eqv) {}

void simp_lemmas_for::insert(simp_lemma const & r) {
    m_simp_set.insert(r.get_lhs(), r);
}

void simp_lemmas_for::erase(simp_lemma const & r) {
    m_simp_set.erase(r.get_lhs(), r);
}

void simp_lemmas_for::insert(user_congr_lemma const & r) {
    m_congr_set.insert(r.get_lhs(), r);
}

void simp_lemmas_for::erase(user_congr_lemma const & r) {
    m_congr_set.erase(r.get_lhs(), r);
}

list<simp_lemma> const * simp_lemmas_for::find_simp(head_index const & h) const {
    return m_simp_set.find(h);
}

void simp_lemmas_for::for_each_simp(std::function<void(simp_lemma const &)> const & fn) const {
    m_simp_set.for_each_entry([&](head_index const &, simp_lemma const & r) { fn(r); });
}

list<user_congr_lemma> const * simp_lemmas_for::find_congr(head_index const & h) const {
    return m_congr_set.find(h);
}

void simp_lemmas_for::for_each_congr(std::function<void(user_congr_lemma const &)> const & fn) const {
    m_congr_set.for_each_entry([&](head_index const &, user_congr_lemma const & r) { fn(r); });
}

void simp_lemmas_for::erase_simp(name_set const & ids) {
    // This method is not very smart and doesn't use any indexing or caching.
    // So, it may be a bottleneck in the future
    buffer<simp_lemma> to_delete;
    for_each_simp([&](simp_lemma const & r) {
            if (ids.contains(r.get_id())) {
                to_delete.push_back(r);
            }
        });
    for (simp_lemma const & r : to_delete) {
        erase(r);
    }
}

void simp_lemmas_for::erase_simp(buffer<name> const & ids) {
    erase_simp(to_name_set(ids));
}

template<typename R>
void simp_lemmas::insert_core(name const & eqv, R const & r) {
    simp_lemmas_for s(eqv);
    if (auto const * curr = m_sets.find(eqv)) {
        s = *curr;
    }
    s.insert(r);
    m_sets.insert(eqv, s);
}

template<typename R>
void simp_lemmas::erase_core(name const & eqv, R const & r) {
    if (auto const * curr = m_sets.find(eqv)) {
        simp_lemmas_for s = *curr;
        s.erase(r);
        if (s.empty())
            m_sets.erase(eqv);
        else
            m_sets.insert(eqv, s);
    }
}

void simp_lemmas::insert(name const & eqv, simp_lemma const & r) {
    return insert_core(eqv, r);
}

void simp_lemmas::erase(name const & eqv, simp_lemma const & r) {
    return erase_core(eqv, r);
}

void simp_lemmas::insert(name const & eqv, user_congr_lemma const & r) {
    return insert_core(eqv, r);
}

void simp_lemmas::erase(name const & eqv, user_congr_lemma const & r) {
    return erase_core(eqv, r);
}

void simp_lemmas::get_relations(buffer<name> & rs) const {
    m_sets.for_each([&](name const & r, simp_lemmas_for const &) {
            rs.push_back(r);
        });
}

void simp_lemmas::erase_simp(name_set const & ids) {
    name_map<simp_lemmas_for> new_sets;
    m_sets.for_each([&](name const & n, simp_lemmas_for const & s) {
            simp_lemmas_for new_s = s;
            new_s.erase_simp(ids);
            new_sets.insert(n, new_s);
        });
    m_sets = new_sets;
}

void simp_lemmas::erase_simp(buffer<name> const & ids) {
    erase_simp(to_name_set(ids));
}

simp_lemmas_for const * simp_lemmas::find(name const & eqv) const {
    return m_sets.find(eqv);
}

list<simp_lemma> const * simp_lemmas::find_simp(name const & eqv, head_index const & h) const {
    if (auto const * s = m_sets.find(eqv))
        return s->find_simp(h);
    return nullptr;
}

list<user_congr_lemma> const * simp_lemmas::find_congr(name const & eqv, head_index const & h) const {
    if (auto const * s = m_sets.find(eqv))
        return s->find_congr(h);
    return nullptr;
}

void simp_lemmas::for_each_simp(std::function<void(name const &, simp_lemma const &)> const & fn) const {
    m_sets.for_each([&](name const & eqv, simp_lemmas_for const & s) {
            s.for_each_simp([&](simp_lemma const & r) {
                    fn(eqv, r);
                });
        });
}

void simp_lemmas::for_each_congr(std::function<void(name const &, user_congr_lemma const &)> const & fn) const {
    m_sets.for_each([&](name const & eqv, simp_lemmas_for const & s) {
            s.for_each_congr([&](user_congr_lemma const & r) {
                    fn(eqv, r);
                });
        });
}

format simp_lemmas::pp(formatter const & fmt, format const & header, bool simp, bool congr) const {
    format r;
    if (simp) {
        name prev_eqv;
        for_each_simp([&](name const & eqv, simp_lemma const & rw) {
                if (prev_eqv != eqv) {
                    r += format("simplification rules for ") + format(eqv);
                    r += header;
                    r += line();
                    prev_eqv = eqv;
                }
                r += rw.pp(fmt) + line();
            });
    }

    if (congr) {
        name prev_eqv;
        for_each_congr([&](name const & eqv, user_congr_lemma const & cr) {
                if (prev_eqv != eqv) {
                    r += format("congruencec rules for ") + format(eqv) + line();
                    prev_eqv = eqv;
                }
                r += cr.pp(fmt) + line();
            });
    }
    return r;
}

format simp_lemmas::pp_simp(formatter const & fmt, format const & header) const {
    return pp(fmt, header, true, false);
}

format simp_lemmas::pp_simp(formatter const & fmt) const {
    return pp(fmt, format(), true, false);
}

format simp_lemmas::pp_congr(formatter const & fmt) const {
    return pp(fmt, format(), false, true);
}

format simp_lemmas::pp(formatter const & fmt) const {
    return pp(fmt, format(), true, true);
}

simp_lemmas get_simp_lemmas_for_attr(simp_lemma_cache & sl_cache, type_context & tctx, name const & simp_attr) {
    auto it = sl_cache.simp_cache().find(simp_attr);
    if (it != sl_cache.simp_cache().end())
        return it->second;

    auto const & attr = get_attribute(tctx.env(), simp_attr);
    simp_lemmas r;
    buffer<name> simp_lemmas;
    attr.get_instances(tctx.env(), simp_lemmas);
    unsigned i = simp_lemmas.size();
    while (i > 0) {
        i--;
        name const & id = simp_lemmas[i];
        tmp_type_context tmp_tctx(tctx);
        r = add_core(tmp_tctx, r, id, attr.get_prio(tctx.env(), id));
    }
    sl_cache.simp_cache().insert({simp_attr, r});
    return r;
}

simp_lemmas get_congr_lemmas_for_attr(simp_lemma_cache & sl_cache, type_context & tctx, name const & congr_attr) {
    auto it = sl_cache.congr_cache().find(congr_attr);
    if (it != sl_cache.congr_cache().end())
        return it->second;

    auto const & attr = get_attribute(tctx.env(), congr_attr);
    simp_lemmas r;
    buffer<name> congr_lemmas;
    attr.get_instances(tctx.env(), congr_lemmas);
    unsigned i = congr_lemmas.size();
    while (i > 0) {
        i--;
        name const & id = congr_lemmas[i];
        tmp_type_context tmp_tctx(tctx);
        r = add_congr_core(tmp_tctx, r, id, attr.get_prio(tctx.env(), id));
    }
    sl_cache.congr_cache().insert({congr_attr, r});
    return r;
}

simp_lemmas get_simp_lemmas(type_context & tctx, buffer<name> const & simp_attrs, buffer<name> const & congr_attrs) {
    simp_lemma_cache & sl_cache = get_simp_lemma_cache_for(tctx);
    simp_lemmas r;

    // Optimization for the case when there is only one simp attr
    // (we avoid the redundant head_map_prio inserts)
    if (simp_attrs.size() > 0)
        r = get_simp_lemmas_for_attr(sl_cache, tctx, simp_attrs[0]);

    for (unsigned i = 1; i < simp_attrs.size(); ++i)
        r = join(r, get_simp_lemmas_for_attr(sl_cache, tctx, simp_attrs[i]));

    for (unsigned i = 0; i < congr_attrs.size(); ++i)
        r = join(r, get_congr_lemmas_for_attr(sl_cache, tctx, congr_attrs[i]));

    return r;
}

struct vm_simp_lemmas : public vm_external {
    simp_lemmas m_val;
    vm_simp_lemmas(simp_lemmas const & v): m_val(v) {}
    virtual ~vm_simp_lemmas() {}
    virtual void dealloc() override { this->~vm_simp_lemmas(); get_vm_allocator().deallocate(sizeof(vm_simp_lemmas), this); }
};

simp_lemmas const & to_simp_lemmas(vm_obj const & o) {
    lean_assert(is_external(o));
    lean_assert(dynamic_cast<vm_simp_lemmas*>(to_external(o)));
    return static_cast<vm_simp_lemmas*>(to_external(o))->m_val;
}

vm_obj to_obj(simp_lemmas const & idx) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_simp_lemmas))) vm_simp_lemmas(idx));
}

vm_obj tactic_mk_simp_lemmas(vm_obj const & m, vm_obj const & sattrs, vm_obj const & cattrs, vm_obj const & s) {
    LEAN_TACTIC_TRY;
    type_context ctx = mk_type_context_for(s, m);
    buffer<name> simp_attrs, congr_attrs;
    to_buffer(to_list_name(sattrs), simp_attrs);
    to_buffer(to_list_name(cattrs), congr_attrs);
    return mk_tactic_success(to_obj(get_simp_lemmas(ctx, simp_attrs, congr_attrs)), to_tactic_state(s));
    LEAN_TACTIC_CATCH(to_tactic_state(s));
}

vm_obj tactic_mk_empty_simp_lemmas(vm_obj const & s) {
    return mk_tactic_success(to_obj(simp_lemmas()), to_tactic_state(s));
}

vm_obj tactic_simp_lemmas_insert(vm_obj const & m, vm_obj const & lemmas, vm_obj const & lemma, vm_obj const & s) {
    LEAN_TACTIC_TRY;
    type_context tctx = mk_type_context_for(s, m);
    expr e = to_expr(lemma);
    name id;
    if (is_constant(e))
        id = const_name(e);
    else if (is_local(e))
        id = local_pp_name(e);

    expr e_type = tctx.infer(e);
    // TODO(dhs): accept priority as an argument
    // Reason for postponing: better plumbing of numerals through the vm
    simp_lemmas new_lemmas = add(tctx, to_simp_lemmas(lemmas), id, tctx.infer(e), e, LEAN_DEFAULT_PRIORITY);
    return mk_tactic_success(to_obj(new_lemmas), to_tactic_state(s));
    LEAN_TACTIC_CATCH(to_tactic_state(s));
}

vm_obj tactic_simp_lemmas_insert_constant(vm_obj const & m, vm_obj const & lemmas, vm_obj const & lemma_name, vm_obj const & s) {
    LEAN_TACTIC_TRY;
    type_context ctx = mk_type_context_for(s, m);
    simp_lemmas new_lemmas = add_poly(ctx, to_simp_lemmas(lemmas), to_name(lemma_name), LEAN_DEFAULT_PRIORITY);
    return mk_tactic_success(to_obj(new_lemmas), to_tactic_state(s));
    LEAN_TACTIC_CATCH(to_tactic_state(s));
}

vm_obj tactic_simp_lemmas_erase(vm_obj const & lemmas, vm_obj const & lemma_list) {
    name_set S;
    for (name const & l : to_list_name(lemma_list))
        S.insert(l);
    simp_lemmas new_lemmas = to_simp_lemmas(lemmas);
    new_lemmas.erase_simp(S);
    return to_obj(new_lemmas);
}

void initialize_simp_lemmas() {
    DECLARE_VM_BUILTIN(name({"tactic", "mk_simp_lemmas_core"}),              tactic_mk_simp_lemmas);
    DECLARE_VM_BUILTIN(name({"tactic", "mk_empty_simp_lemmas"}),             tactic_mk_empty_simp_lemmas);
    DECLARE_VM_BUILTIN(name({"tactic", "simp_lemmas_insert_core"}),          tactic_simp_lemmas_insert);
    DECLARE_VM_BUILTIN(name({"tactic", "simp_lemmas_insert_constant_core"}), tactic_simp_lemmas_insert);
    DECLARE_VM_BUILTIN(name({"tactic", "simp_lemmas_erase"}),                tactic_simp_lemmas_erase);

    register_system_attribute(basic_attribute::with_check("simp", "simplification lemma", on_add_simp_lemma));
    register_system_attribute(basic_attribute::with_check("congr", "congruence lemma", on_add_congr_lemma));
}

void finalize_simp_lemmas() {
}
}
