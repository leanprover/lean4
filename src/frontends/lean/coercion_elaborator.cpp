/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/type_checker.h"
#include "kernel/metavar.h"
#include "kernel/constraint.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "library/coercion.h"
#include "library/unifier.h"
#include "library/choice_iterator.h"
#include "frontends/lean/coercion_elaborator.h"

namespace lean {
coercion_elaborator::coercion_elaborator(coercion_info_manager & info, expr const & arg,
                                         list<constraints> const & choices, list<expr> const & coes,
                                         bool use_id):
    m_info(info), m_arg(arg), m_id(use_id), m_choices(choices), m_coercions(coes) {
    lean_assert(!use_id || length(m_coercions) + 1 == length(m_choices));
    lean_assert(use_id  || length(m_coercions)     == length(m_choices));
}

list<expr> get_coercions_from_to(type_checker & from_tc, type_checker & to_tc,
                                 expr const & from_type, expr const & to_type, constraint_seq & cs, bool lift_coe) {
    constraint_seq new_cs;
    environment const & env = to_tc.env();
    expr whnf_from_type = from_tc.whnf(from_type, new_cs);
    expr whnf_to_type   = to_tc.whnf(to_type, new_cs);
    if (lift_coe && is_pi(whnf_from_type)) {
        // Try to lift coercions.
        // The idea is to convert a coercion from A to B, into a coercion from D->A to D->B
        if (!is_pi(whnf_to_type))
            return list<expr>(); // failed
        if (!from_tc.is_def_eq(binding_domain(whnf_from_type), binding_domain(whnf_to_type), justification(), new_cs))
            return list<expr>(); // failed, the domains must be definitionally equal
        expr x = mk_local(from_tc.mk_fresh_name(), "x", binding_domain(whnf_from_type), binder_info());
        expr A = instantiate(binding_body(whnf_from_type), x);
        expr B = instantiate(binding_body(whnf_to_type), x);
        list<expr> coe = get_coercions_from_to(from_tc, to_tc, A, B, new_cs, lift_coe);
        if (coe) {
            cs += new_cs;
            // Remark: each coercion c in coe is a function from A to B
            // We create a new list: (fun (f : D -> A) (x : D), c (f x))
            expr f = mk_local(from_tc.mk_fresh_name(), "f", whnf_from_type, binder_info());
            expr fx = mk_app(f, x);
            return map(coe, [&](expr const & c) { return Fun(f, Fun(x, mk_app(c, fx))); });
        } else {
            return list<expr>();
        }
    } else {
        expr const & fn   = get_app_fn(whnf_to_type);
        list<expr> r;
        if (is_constant(fn)) {
            r = get_coercions(env, whnf_from_type, const_name(fn));
        } else if (is_pi(whnf_to_type)) {
            r = get_coercions_to_fun(env, whnf_from_type);
        } else if (is_sort(whnf_to_type)) {
            r = get_coercions_to_sort(env, whnf_from_type);
        }
        if (r)
            cs += new_cs;
        return r;
    }
}

optional<constraints> coercion_elaborator::next() {
    if (!m_choices)
        return optional<constraints>();
    if (m_id) {
        m_id = false;
        m_info.erase_coercion_info(m_arg);
    } else if (m_coercions) {
        expr c      = head(m_coercions);
        m_coercions = tail(m_coercions);
        m_info.save_coercion_info(m_arg, mk_app(c, m_arg));
    }
    auto r = head(m_choices);
    m_choices = tail(m_choices);
    return optional<constraints>(r);
}

bool is_pi_meta(expr const & e) {
    if (is_pi(e)) {
        return is_pi_meta(binding_body(e));
    } else {
        return is_meta(e);
    }
}

/** \brief Given a term <tt>a : a_type</tt>, and a metavariable \c m, creates a constraint
    that considers coercions from a_type to the type assigned to \c m. */
constraint mk_coercion_cnstr(type_checker & from_tc, type_checker & to_tc, coercion_info_manager & infom,
                             expr const & m, expr const & a, expr const & a_type,
                             justification const & j, unsigned delay_factor, bool lift_coe) {
    auto choice_fn = [=, &from_tc, &to_tc, &infom](expr const & meta, expr const & d_type, substitution const & s,
                                                   name_generator && /* ngen */) {
        expr          new_a_type;
        justification new_a_type_jst;
        if (is_meta(a_type)) {
            auto p = substitution(s).instantiate_metavars(a_type);
            new_a_type     = p.first;
            new_a_type_jst = p.second;
        } else {
            new_a_type     = a_type;
        }
        if (is_meta(new_a_type)) {
            if (delay_factor < to_delay_factor(cnstr_group::DelayedChoice)) {
                // postpone...
                return lazy_list<constraints>(constraints(mk_coercion_cnstr(from_tc, to_tc, infom, m, a, a_type, justification(),
                                                                            delay_factor+1, lift_coe)));
            } else {
                // giveup...
                return lazy_list<constraints>(constraints(mk_eq_cnstr(meta, a, justification())));
            }
        }
        constraint_seq cs;
        new_a_type = from_tc.whnf(new_a_type, cs);
        if ((lift_coe && is_pi_meta(d_type)) || (!lift_coe && is_meta(d_type))) {
            // case-split
            buffer<expr> locals;
            expr it_from = new_a_type;
            expr it_to   = d_type;
            while (is_pi(it_from) && is_pi(it_to)) {
                expr dom_from = binding_domain(it_from);
                expr dom_to   = binding_domain(it_to);
                if (!from_tc.is_def_eq(dom_from, dom_to, justification(), cs))
                    return lazy_list<constraints>();
                expr local = mk_local(from_tc.mk_fresh_name(), binding_name(it_from), dom_from, binder_info());
                locals.push_back(local);
                it_from  = instantiate(binding_body(it_from), local);
                it_to    = instantiate(binding_body(it_to), local);
            }
            buffer<expr> alts;
            get_coercions_from(from_tc.env(), it_from, alts);
            expr fn_a;
            if (!locals.empty())
                fn_a = mk_local(from_tc.mk_fresh_name(), "f", new_a_type, binder_info());
            buffer<constraints> choices;
            buffer<expr> coes;
            // first alternative: no coercion
            constraint_seq cs1 = cs + mk_eq_cnstr(meta, a, justification());
            choices.push_back(cs1.to_list());
            unsigned i = alts.size();
            while (i > 0) {
                --i;
                expr coe = alts[i];
                if (!locals.empty())
                    coe = Fun(fn_a, Fun(locals, mk_app(coe, mk_app(fn_a, locals))));
                expr new_a = copy_tag(a, mk_app(coe, a));
                coes.push_back(coe);
                constraint_seq csi = cs + mk_eq_cnstr(meta, new_a, new_a_type_jst);
                choices.push_back(csi.to_list());
            }
            return choose(std::make_shared<coercion_elaborator>(infom, meta,
                                                                to_list(choices.begin(), choices.end()),
                                                                to_list(coes.begin(), coes.end())));
        } else {
            list<expr> coes    = get_coercions_from_to(from_tc, to_tc, new_a_type, d_type, cs, lift_coe);
            if (is_nil(coes)) {
                expr new_a = a;
                infom.erase_coercion_info(a);
                cs += mk_eq_cnstr(meta, new_a, new_a_type_jst);
                return lazy_list<constraints>(cs.to_list());
            } else if (is_nil(tail(coes))) {
                expr new_a = copy_tag(a, mk_app(head(coes), a));
                infom.save_coercion_info(a, new_a);
                cs += mk_eq_cnstr(meta, new_a, new_a_type_jst);
                return lazy_list<constraints>(cs.to_list());
            } else {
                list<constraints> choices = map2<constraints>(coes, [&](expr const & coe) {
                        expr new_a   = copy_tag(a, mk_app(coe, a));
                        constraint c = mk_eq_cnstr(meta, new_a, new_a_type_jst);
                        return (cs + c).to_list();
                    });
                return choose(std::make_shared<coercion_elaborator>(infom, meta, choices, coes, false));
            }
        }
    };
    return mk_choice_cnstr(m, choice_fn, delay_factor, true, j);
}
}
