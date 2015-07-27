/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/sstream.h"
#include "kernel/instantiate.h"
#include "kernel/find_fn.h"
#include "kernel/error_msgs.h"
#include "library/scoped_ext.h"
#include "library/expr_pair.h"
#include "library/relation_manager.h"
#include "library/simplifier/ceqv.h"
#include "library/simplifier/simp_rule_set.h"

namespace lean {
simp_rule_core::simp_rule_core(name const & id, levels const & univ_metas, list<expr> const & metas,
                               expr const & lhs, expr const & rhs, expr const & proof):
    m_id(id), m_univ_metas(univ_metas), m_metas(metas), m_lhs(lhs), m_rhs(rhs), m_proof(proof) {}

simp_rule::simp_rule(name const & id, levels const & univ_metas, list<expr> const & metas,
                     expr const & lhs, expr const & rhs, expr const & proof, bool is_perm):
    simp_rule_core(id, univ_metas, metas, lhs, rhs, proof),
    m_is_permutation(is_perm) {}

bool operator==(simp_rule const & r1, simp_rule const & r2) {
    return r1.m_lhs == r2.m_lhs && r1.m_rhs == r2.m_rhs;
}

format simp_rule::pp(formatter const & fmt) const {
    format r;
    r += format("#") + format(length(m_metas));
    if (m_is_permutation)
        r += space() + format("perm");
    format r1 = comma() + space() + fmt(m_lhs);
    r1       += space() + format("↦") + pp_indent_expr(fmt, m_rhs);
    r += group(r1);
    return r;
}

congr_rule::congr_rule(name const & id, levels const & univ_metas, list<expr> const & metas,
                       expr const & lhs, expr const & rhs, expr const & proof, list<expr> const & congr_hyps):
    simp_rule_core(id, univ_metas, metas, lhs, rhs, proof),
    m_congr_hyps(congr_hyps) {}

bool operator==(congr_rule const & r1, congr_rule const & r2) {
    return r1.m_lhs == r2.m_lhs && r1.m_rhs == r2.m_rhs && r1.m_congr_hyps == r2.m_congr_hyps;
}

format congr_rule::pp(formatter const & fmt) const {
    format r;
    r += format("#") + format(length(m_metas));
    format r1;
    for (expr const & h : m_congr_hyps) {
        r1 += space() + paren(fmt(mlocal_type(h)));
    }
    r += group(r1);
    r += space() + format(":") + space();
    format r2 = paren(fmt(m_lhs));
    r2       += space() + format("↦") + space() + paren(fmt(m_rhs));
    r += group(r2);
    return r;
}

simp_rule_set::simp_rule_set(name const & eqv):
    m_eqv(eqv) {}

void simp_rule_set::insert(simp_rule const & r) {
    m_simp_set.insert(r.get_lhs(), r);
}

void simp_rule_set::erase(simp_rule const & r) {
    m_simp_set.erase(r.get_lhs(), r);
}

void simp_rule_set::insert(congr_rule const & r) {
    m_congr_set.insert(r.get_lhs(), r);
}

void simp_rule_set::erase(congr_rule const & r) {
    m_congr_set.erase(r.get_lhs(), r);
}

list<simp_rule> const * simp_rule_set::find_simp(head_index const & h) const {
    return m_simp_set.find(h);
}

void simp_rule_set::for_each_simp(std::function<void(simp_rule const &)> const & fn) const {
    m_simp_set.for_each_entry([&](head_index const &, simp_rule const & r) { fn(r); });
}

list<congr_rule> const * simp_rule_set::find_congr(head_index const & h) const {
    return m_congr_set.find(h);
}

void simp_rule_set::for_each_congr(std::function<void(congr_rule const &)> const & fn) const {
    m_congr_set.for_each_entry([&](head_index const &, congr_rule const & r) { fn(r); });
}

void simp_rule_set::erase_simp(name_set const & ids) {
    // This method is not very smart and doesn't use any indexing or caching.
    // So, it may be a bottleneck in the future
    buffer<simp_rule> to_delete;
    for_each_simp([&](simp_rule const & r) {
            if (ids.contains(r.get_id())) {
                to_delete.push_back(r);
            }
        });
    for (simp_rule const & r : to_delete) {
        erase(r);
    }
}

void simp_rule_set::erase_simp(buffer<name> const & ids) {
    erase_simp(to_name_set(ids));
}

template<typename R>
void simp_rule_sets::insert_core(name const & eqv, R const & r) {
    simp_rule_set s(eqv);
    if (auto const * curr = m_sets.find(eqv)) {
        s = *curr;
    }
    s.insert(r);
    m_sets.insert(eqv, s);
}

template<typename R>
void simp_rule_sets::erase_core(name const & eqv, R const & r) {
    if (auto const * curr = m_sets.find(eqv)) {
        simp_rule_set s = *curr;
        s.erase(r);
        if (s.empty())
            m_sets.erase(eqv);
        else
            m_sets.insert(eqv, s);
    }
}

void simp_rule_sets::insert(name const & eqv, simp_rule const & r) {
    return insert_core(eqv, r);
}

void simp_rule_sets::erase(name const & eqv, simp_rule const & r) {
    return erase_core(eqv, r);
}

void simp_rule_sets::insert(name const & eqv, congr_rule const & r) {
    return insert_core(eqv, r);
}

void simp_rule_sets::erase(name const & eqv, congr_rule const & r) {
    return erase_core(eqv, r);
}

void simp_rule_sets::get_relations(buffer<name> & rs) const {
    m_sets.for_each([&](name const & r, simp_rule_set const &) {
            rs.push_back(r);
        });
}

void simp_rule_sets::erase_simp(name_set const & ids) {
    name_map<simp_rule_set> new_sets;
    m_sets.for_each([&](name const & n, simp_rule_set const & s) {
            simp_rule_set new_s = s;
            new_s.erase_simp(ids);
            new_sets.insert(n, new_s);
        });
    m_sets = new_sets;
}

void simp_rule_sets::erase_simp(buffer<name> const & ids) {
    erase_simp(to_name_set(ids));
}

simp_rule_set const * simp_rule_sets::find(name const & eqv) const {
    return m_sets.find(eqv);
}

list<simp_rule> const * simp_rule_sets::find_simp(name const & eqv, head_index const & h) const {
    if (auto const * s = m_sets.find(eqv))
        return s->find_simp(h);
    return nullptr;
}

list<congr_rule> const * simp_rule_sets::find_congr(name const & eqv, head_index const & h) const {
    if (auto const * s = m_sets.find(eqv))
        return s->find_congr(h);
    return nullptr;
}

void simp_rule_sets::for_each_simp(std::function<void(name const &, simp_rule const &)> const & fn) const {
    m_sets.for_each([&](name const & eqv, simp_rule_set const & s) {
            s.for_each_simp([&](simp_rule const & r) {
                    fn(eqv, r);
                });
        });
}

void simp_rule_sets::for_each_congr(std::function<void(name const &, congr_rule const &)> const & fn) const {
    m_sets.for_each([&](name const & eqv, simp_rule_set const & s) {
            s.for_each_congr([&](congr_rule const & r) {
                    fn(eqv, r);
                });
        });
}

format simp_rule_sets::pp(formatter const & fmt, format const & header, bool simp, bool congr) const {
    format r;
    if (simp) {
        name prev_eqv;
        for_each_simp([&](name const & eqv, simp_rule const & rw) {
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
        for_each_congr([&](name const & eqv, congr_rule const & cr) {
                if (prev_eqv != eqv) {
                    r += format("congruencec rules for ") + format(eqv) + line();
                    prev_eqv = eqv;
                }
                r += cr.pp(fmt) + line();
            });
    }
    return r;
}

format simp_rule_sets::pp_simp(formatter const & fmt, format const & header) const {
    return pp(fmt, header, true, false);
}

format simp_rule_sets::pp_simp(formatter const & fmt) const {
    return pp(fmt, format(), true, false);
}

format simp_rule_sets::pp_congr(formatter const & fmt) const {
    return pp(fmt, format(), false, true);
}

format simp_rule_sets::pp(formatter const & fmt) const {
    return pp(fmt, format(), true, true);
}

static name * g_prefix = nullptr;

simp_rule_sets add_core(type_checker & tc, simp_rule_sets const & s,
                        name const & id, levels const & univ_metas, expr const & e, expr const & h) {
    list<expr_pair> ceqvs   = to_ceqvs(tc, e, h);
    environment const & env = tc.env();
    simp_rule_sets new_s = s;
    for (expr_pair const & p : ceqvs) {
        expr new_e = p.first;
        expr new_h = p.second;
        bool is_perm       = is_permutation_ceqv(env, new_e);
        buffer<expr> metas;
        unsigned idx = 0;
        while (is_pi(new_e)) {
            expr mvar = mk_metavar(name(*g_prefix, idx), binding_domain(new_e));
            idx++;
            metas.push_back(mvar);
            new_e = instantiate(binding_body(new_e), mvar);
        }
        expr rel, lhs, rhs;
        if (is_simp_relation(env, new_e, rel, lhs, rhs) && is_constant(rel)) {
            new_s.insert(const_name(rel), simp_rule(id, univ_metas, to_list(metas), lhs, rhs, new_h, is_perm));
        }
    }
    return new_s;
}

simp_rule_sets add(type_checker & tc, simp_rule_sets const & s, name const & id, expr const & e, expr const & h) {
    return add_core(tc, s, id, list<level>(), e, h);
}

simp_rule_sets join(simp_rule_sets const & s1, simp_rule_sets const & s2) {
    simp_rule_sets new_s1 = s1;
    s2.for_each_simp([&](name const & eqv, simp_rule const & r) {
            new_s1.insert(eqv, r);
        });
    return new_s1;
}

static name * g_class_name = nullptr;
static std::string * g_key = nullptr;

static simp_rule_sets add_core(type_checker & tc, simp_rule_sets const & s, name const & cname) {
    declaration const & d = tc.env().get(cname);
    buffer<level> us;
    unsigned num_univs = d.get_num_univ_params();
    for (unsigned i = 0; i < num_univs; i++) {
        us.push_back(mk_meta_univ(name(*g_prefix, i)));
    }
    levels ls = to_list(us);
    expr e    = instantiate_type_univ_params(d, ls);
    expr h    = mk_constant(cname, ls);
    return add_core(tc, s, cname, ls, e, h);
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

void add_congr_core(environment const & env, simp_rule_sets & s, name const & n) {
    declaration const & d = env.get(n);
    type_checker tc(env);
    buffer<level> us;
    unsigned num_univs = d.get_num_univ_params();
    for (unsigned i = 0; i < num_univs; i++) {
        us.push_back(mk_meta_univ(name(*g_prefix, i)));
    }
    levels ls = to_list(us);
    expr pr   = mk_constant(n, ls);
    expr e    = instantiate_type_univ_params(d, ls);
    buffer<bool> explicit_args;
    buffer<expr> metas;
    unsigned idx = 0;
    while (is_pi(e)) {
        expr mvar = mk_metavar(name(*g_prefix, idx), binding_domain(e));
        idx++;
        explicit_args.push_back(is_explicit(binding_info(e)));
        metas.push_back(mvar);
        e   = instantiate(binding_body(e), mvar);
        pr  = mk_app(pr, mvar);
    }
    expr rel, lhs, rhs;
    if (!is_simp_relation(env, e, rel, lhs, rhs) || !is_constant(rel)) {
        throw exception(sstream() << "invalid congruence rule, '" << n
                        << "' resulting type is not of the form t ~ s, where '~' is a transitive and reflexive relation");
    }
    name_set found_mvars;
    buffer<expr> lhs_args, rhs_args;
    expr const & lhs_fn = get_app_args(lhs, lhs_args);
    expr const & rhs_fn = get_app_args(rhs, rhs_args);
    if (is_constant(lhs_fn)) {
        if (!is_constant(rhs_fn) || const_name(lhs_fn) != const_name(rhs_fn) || lhs_args.size() != rhs_args.size()) {
            throw exception(sstream() << "invalid congruence rule, '" << n
                            << "' resulting type is not of the form (" << const_name(lhs_fn) << "  ...) "
                            << "~ (" << const_name(lhs_fn) << " ...), where ~ is '" << const_name(rel) << "'");
        }
        for (expr const & lhs_arg : lhs_args) {
            if (is_sort(lhs_arg))
                continue;
            if (!is_metavar(lhs_arg) || found_mvars.contains(mlocal_name(lhs_arg))) {
                throw exception(sstream() << "invalid congruence rule, '" << n
                                << "' the left-hand-side of the congruence resulting type must be of the form ("
                                << const_name(lhs_fn) << " x_1 ... x_n), where each x_i is a distinct variable or a sort");
            }
            found_mvars.insert(mlocal_name(lhs_arg));
        }
    } else if (is_binding(lhs)) {
        if (lhs.kind() != rhs.kind()) {
            throw exception(sstream() << "invalid congruence rule, '" << n
                            << "' kinds of the left-hand-side and right-hand-side of "
                            << "the congruence resulting type do not match");
        }
        if (!is_valid_congr_rule_binding_lhs(lhs, found_mvars)) {
            throw exception(sstream() << "invalid congruence rule, '" << n
                            << "' left-hand-side of the congruence resulting type must "
                            << "be of the form (fun/Pi (x : A), B x)");
        }
    } else {
        throw exception(sstream() << "invalid congruence rule, '" << n
                        << "' left-hand-side is not an application nor a binding");
    }

    buffer<expr> congr_hyps;
    lean_assert(metas.size() == explicit_args.size());
    for (unsigned i = 0; i < metas.size(); i++) {
        expr const & mvar = metas[i];
        if (explicit_args[i] && !found_mvars.contains(mlocal_name(mvar))) {
            buffer<expr> locals;
            expr type = mlocal_type(mvar);
            while (is_pi(type)) {
                expr local = mk_local(tc.mk_fresh_name(), binding_domain(type));
                locals.push_back(local);
                type = instantiate(binding_body(type), local);
            }
            expr h_rel, h_lhs, h_rhs;
            if (!is_simp_relation(env, type, h_rel, h_lhs, h_rhs) || !is_constant(h_rel))
                continue;
            unsigned j = 0;
            for (expr const & local : locals) {
                j++;
                if (!only_found_mvars(mlocal_type(local), found_mvars)) {
                    throw exception(sstream() << "invalid congruence rule, '" << n
                                    << "' argument #" << j << " of parameter #" << (i+1) << " contains "
                                    << "unresolved parameters");
                }
            }
            if (!only_found_mvars(h_lhs, found_mvars)) {
                throw exception(sstream() << "invalid congruence rule, '" << n
                                << "' argument #" << (i+1) << " is not a valid hypothesis, the left-hand-side contains "
                                << "unresolved parameters");
            }
            if (!is_valid_congr_hyp_rhs(h_rhs, found_mvars)) {
                throw exception(sstream() << "invalid congruence rule, '" << n
                                << "' argument #" << (i+1) << " is not a valid hypothesis, the right-hand-side must be "
                                << "of the form (m l_1 ... l_n) where m is parameter that was not "
                                << "'assigned/resolved' yet and l_i's are locals");
            }
            found_mvars.insert(mlocal_name(mvar));
            congr_hyps.push_back(mvar);
        }
    }
    congr_rule rule(n, ls, to_list(metas), lhs, rhs, pr, to_list(congr_hyps));
    s.insert(const_name(rel), rule);
}

struct rrs_state {
    simp_rule_sets           m_sets;
    name_set                 m_simp_names;
    name_set                 m_congr_names;

    void add_simp(environment const & env, name const & cname) {
        type_checker tc(env);
        m_sets = add_core(tc, m_sets, cname);
        m_simp_names.insert(cname);
    }

    void add_congr(environment const & env, name const & n) {
        add_congr_core(env, m_sets, n);
        m_congr_names.insert(n);
    }
};

struct rrs_config {
    typedef pair<bool, name> entry;
    typedef rrs_state        state;
    static void add_entry(environment const & env, io_state const &, state & s, entry const & e) {
        if (e.first)
            s.add_simp(env, e.second);
        else
            s.add_congr(env, e.second);
    }
    static name const & get_class_name() {
        return *g_class_name;
    }
    static std::string const & get_serialization_key() {
        return *g_key;
    }
    static void  write_entry(serializer & s, entry const & e) {
        s << e.first << e.second;
    }
    static entry read_entry(deserializer & d) {
        entry e; d >> e.first >> e.second; return e;
    }
    static optional<unsigned> get_fingerprint(entry const & e) {
        return some(hash(e.first ? 17 : 31, e.second.hash()));
    }
};

template class scoped_ext<rrs_config>;
typedef scoped_ext<rrs_config> rrs_ext;

environment add_simp_rule(environment const & env, name const & n, bool persistent) {
    return rrs_ext::add_entry(env, get_dummy_ios(), mk_pair(true, n), persistent);
}

environment add_congr_rule(environment const & env, name const & n, bool persistent) {
    return rrs_ext::add_entry(env, get_dummy_ios(), mk_pair(false, n), persistent);
}

bool is_simp_rule(environment const & env, name const & n) {
    return rrs_ext::get_state(env).m_simp_names.contains(n);
}

bool is_congr_rule(environment const & env, name const & n) {
    return rrs_ext::get_state(env).m_congr_names.contains(n);
}

simp_rule_sets get_simp_rule_sets(environment const & env) {
    return rrs_ext::get_state(env).m_sets;
}

simp_rule_sets get_simp_rule_sets(environment const & env, name const & ns) {
    simp_rule_sets set;
    list<pair<bool, name>> const * cnames = rrs_ext::get_entries(env, ns);
    if (cnames) {
        type_checker tc(env);
        for (pair<bool, name> const & p : *cnames) {
            set = add_core(tc, set, p.second);
        }
    }
    return set;
}

io_state_stream const & operator<<(io_state_stream const & out, simp_rule_sets const & s) {
    options const & opts = out.get_options();
    out.get_stream() << mk_pair(s.pp(out.get_formatter()), opts);
    return out;
}

void initialize_simp_rule_set() {
    g_prefix     = new name(name::mk_internal_unique_name());
    g_class_name = new name("rrs");
    g_key        = new std::string("rrs");
    rrs_ext::initialize();
}

void finalize_simp_rule_set() {
    rrs_ext::finalize();
    delete g_key;
    delete g_class_name;
    delete g_prefix;
}
}
