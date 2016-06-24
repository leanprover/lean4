/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include <string>
#include "util/priority_queue.h"
#include "util/sstream.h"
#include "util/flet.h"
#include "kernel/error_msgs.h"
#include "kernel/find_fn.h"
#include "kernel/instantiate.h"
#include "library/trace.h"
#include "library/scoped_ext.h"
#include "library/attribute_manager.h"
#include "library/type_context.h"
#include "library/tactic/simplifier/ceqv.h"
#include "library/tactic/simplifier/simp_lemmas.h"

namespace lean {

/* The environment extension */
static name * g_class_name = nullptr;
static std::string * g_key = nullptr;

struct simp_state {
    priority_queue<name, name_quick_cmp> m_simp_lemmas;
    priority_queue<name, name_quick_cmp> m_congr_lemmas;
};

typedef std::tuple<bool, unsigned, name> simp_entry;

struct simp_config {
    typedef simp_entry entry;
    typedef simp_state state;

    static void add_entry(environment const &, io_state const &, state & s, entry const & e) {
        bool is_simp; unsigned prio; name n;
        std::tie(is_simp, prio, n) = e;
        if (is_simp) {
            s.m_simp_lemmas.insert(n, prio);
        } else {
            s.m_congr_lemmas.insert(n, prio);
        }
    }
    static name const & get_class_name() {
        return *g_class_name;
    }
    static std::string const & get_serialization_key() {
        return *g_key;
    }
    static void  write_entry(serializer & s, entry const & e) {
        bool is_simp; unsigned prio; name n;
        std::tie(is_simp, prio, n) = e;
        s << is_simp << prio << n;
    }
    static entry read_entry(deserializer & d) {
        bool is_simp; unsigned prio; name n;
        d >> is_simp >> prio >> n;
        return entry(is_simp, prio, n);
    }
    static optional<unsigned> get_fingerprint(entry const & e) {
        bool is_simp; unsigned prio; name n;
        std::tie(is_simp, prio, n) = e;
        return some(hash(hash(n.hash(), prio), is_simp ? 17u : 31u));
    }
};

typedef scoped_ext<simp_config> simp_ext;

/* Validation */

LEAN_THREAD_VALUE(bool, g_throw_ex, false);
void validate_simp(type_context & tctx, name const & n);
void validate_congr(type_context & tctx, name const & n);

/* Registering simp/congr lemmas */

environment add_simp_lemma(environment const & env, io_state const & ios, name const & c, unsigned prio, name const & ns, bool persistent) {
    aux_type_context aux_ctx(env);
    type_context & tctx = aux_ctx.get();
    validate_simp(tctx, c);
    return simp_ext::add_entry(env, ios, simp_entry(true, prio, c), ns, persistent);
}

environment add_congr_lemma(environment const & env, io_state const & ios, name const & c, unsigned prio, name const & ns, bool persistent) {
    aux_type_context aux_ctx(env);
    type_context & tctx = aux_ctx.get();
    validate_congr(tctx, c);
    return simp_ext::add_entry(env, ios, simp_entry(false, prio, c), ns, persistent);
}

/* Getters/checkers */

unsigned get_simp_lemma_priority(environment const & env, name const & n) {
    if (auto r = simp_ext::get_state(env).m_simp_lemmas.get_prio(n))
        return *r;
    else
        return LEAN_DEFAULT_PRIORITY;
}

bool is_simp_lemma(environment const & env, name const & c) {
    return simp_ext::get_state(env).m_simp_lemmas.contains(c);
}

bool is_congr_lemma(environment const & env, name const & c) {
    return simp_ext::get_state(env).m_congr_lemmas.contains(c);
}

void get_simp_lemma_names(environment const & env, buffer<name> & r) {
    return simp_ext::get_state(env).m_simp_lemmas.to_buffer(r);
}

void get_congr_lemma_names(environment const & env, buffer<name> & r) {
    return simp_ext::get_state(env).m_congr_lemmas.to_buffer(r);
}

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
    list<expr_pair> ceqvs   = to_ceqvs(tmp_tctx.tctx(), e, h);
    if (is_nil(ceqvs)) {
        report_failure(sstream() << "invalid [simp] lemma '" << id << "'");
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

simp_lemmas add(type_context & tctx, simp_lemmas const & s, name const & id, expr const & e, expr const & h, unsigned priority) {
    tmp_type_context tmp_tctx(tctx);
    return add_core(tmp_tctx, s, id, list<level>(), e, h, priority);
}

simp_lemmas join(simp_lemmas const & s1, simp_lemmas const & s2) {
    simp_lemmas new_s1 = s1;
    s2.for_each_simp([&](name const & eqv, simp_lemma const & r) {
            new_s1.insert(eqv, r);
        });
    return new_s1;
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

simp_lemmas get_simp_lemmas(environment const & env) {
    simp_lemmas r;
    buffer<name> simp_lemmas, congr_lemmas;
    aux_type_context aux_ctx(env);
    type_context & tctx = aux_ctx.get();
    auto const & s = simp_ext::get_state(env);
    s.m_simp_lemmas.to_buffer(simp_lemmas);
    s.m_congr_lemmas.to_buffer(congr_lemmas);
    unsigned i = simp_lemmas.size();
    while (i > 0) {
        --i;
        tmp_type_context tmp_tctx(tctx);
        r = add_core(tmp_tctx, r, simp_lemmas[i], *s.m_simp_lemmas.get_prio(simp_lemmas[i]));
    }
    i = congr_lemmas.size();
    while (i > 0) {
        --i;
        tmp_type_context tmp_tctx(tctx);
        r = add_congr_core(tmp_tctx, r, congr_lemmas[i], *s.m_congr_lemmas.get_prio(congr_lemmas[i]));
    }
    return r;
}

template<typename NSS>
simp_lemmas get_simp_lemmas_core(environment const & env, NSS const & nss) {
    simp_lemmas r;
    aux_type_context aux_ctx(env);
    type_context & tctx = aux_ctx.get();
    for (name const & ns : nss) {
        list<simp_entry> const * entries = simp_ext::get_entries(env, ns);
        if (entries) {
            for (auto const & e : *entries) {
                bool is_simp; unsigned prio; name n;
                std::tie(is_simp, prio, n) = e;
                if (is_simp) {
                    tmp_type_context tmp_tctx(tctx);
                    r = add_core(tmp_tctx, r, n, prio);
                }
            }
        }
    }
    return r;
}

simp_lemmas get_simp_lemmas(environment const & env, std::initializer_list<name> const & nss) {
    return get_simp_lemmas_core(env, nss);
}

simp_lemmas get_simp_lemmas(environment const & env, name const & ns) {
    return get_simp_lemmas(env, {ns});
}

void initialize_simp_lemmas() {
    g_class_name    = new name("simp");
    g_key           = new std::string("SIMP");
    simp_ext::initialize();

    register_prio_attribute("simp", "simplification lemma",
                            add_simp_lemma,
                            is_simp_lemma,
                            [](environment const & env, name const & d) {
                                if (auto p = simp_ext::get_state(env).m_simp_lemmas.get_prio(d))
                                    return *p;
                                else
                                    return LEAN_DEFAULT_PRIORITY;
                            });

    register_prio_attribute("congr", "congruence lemma",
                            add_congr_lemma,
                            is_congr_lemma,
                            [](environment const & env, name const & d) {
                                if (auto p = simp_ext::get_state(env).m_congr_lemmas.get_prio(d))
                                    return *p;
                                else
                                    return LEAN_DEFAULT_PRIORITY;
                            });
}

void finalize_simp_lemmas() {
    simp_ext::finalize();
    delete g_key;
    delete g_class_name;
}
}
