/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/type_checker.h"
#include "kernel/metavar.h"
#include "kernel/constraint.h"
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

list<expr> get_coercions_from_to(type_checker & /* from_tc */, type_checker & to_tc,
                                 expr const & from_type, expr const & to_type, constraint_seq & cs) {
    constraint_seq new_cs;
    environment const & env = to_tc.env();
    expr whnf_to_type = to_tc.whnf(to_type, new_cs);
    expr const & fn   = get_app_fn(whnf_to_type);
    list<expr> r;
    if (is_constant(fn)) {
        r = get_coercions(env, from_type, const_name(fn));
    } else if (is_pi(whnf_to_type)) {
        r = get_coercions_to_fun(env, from_type);
    } else if (is_sort(whnf_to_type)) {
        r = get_coercions_to_sort(env, from_type);
    }
    if (r)
        cs += new_cs;
    return r;
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

/** \brief Given a term <tt>a : a_type</tt>, and a metavariable \c m, creates a constraint
    that considers coercions from a_type to the type assigned to \c m. */
constraint mk_coercion_cnstr(type_checker & from_tc, type_checker & to_tc, coercion_info_manager & infom,
                             expr const & m, expr const & a, expr const & a_type,
                             justification const & j, unsigned delay_factor) {
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
                                                                            delay_factor+1)));
            } else {
                // giveup...
                return lazy_list<constraints>(constraints(mk_eq_cnstr(meta, a, justification())));
            }
        }
        constraint_seq cs;
        new_a_type = from_tc.whnf(new_a_type, cs);
        if (is_meta(d_type)) {
            // case-split
            buffer<std::tuple<coercion_class, expr, expr>> alts;
            get_coercions_from(from_tc.env(), new_a_type, alts);
            buffer<constraints> choices;
            buffer<expr> coes;
            // first alternative: no coercion
            constraint_seq cs1 = cs + mk_eq_cnstr(meta, a, justification());
            choices.push_back(cs1.to_list());
            unsigned i = alts.size();
            while (i > 0) {
                --i;
                auto const & t = alts[i];
                expr coe   = std::get<1>(t);
                expr new_a = copy_tag(a, mk_app(coe, a));
                coes.push_back(coe);
                constraint_seq csi = cs + mk_eq_cnstr(meta, new_a, new_a_type_jst);
                choices.push_back(csi.to_list());
            }
            return choose(std::make_shared<coercion_elaborator>(infom, meta,
                                                                to_list(choices.begin(), choices.end()),
                                                                to_list(coes.begin(), coes.end())));
        } else {
            list<expr> coes    = get_coercions_from_to(from_tc, to_tc, new_a_type, d_type, cs);
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
