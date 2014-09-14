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
#include "frontends/lean/choice_iterator.h"
#include "frontends/lean/coercion_elaborator.h"

namespace lean {
coercion_elaborator::coercion_elaborator(coercion_info_manager & info, expr const & arg,
                                         list<constraints> const & choices, list<expr> const & coes,
                                         bool use_id):
    m_info(info), m_arg(arg), m_id(use_id), m_choices(choices), m_coercions(coes) {
    lean_assert(length(m_coercions) + 1 == length(m_choices));
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

constraint mk_coercion_cnstr(type_checker & tc, coercion_info_manager & infom,
                             expr const & m, expr const & a, expr const & a_type,
                             justification const & j, unsigned delay_factor, bool relax) {
    auto choice_fn = [=, &tc, &infom](expr const & meta, expr const & d_type, substitution const & s,
                                      name_generator const & /* ngen */) {
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
                return lazy_list<constraints>(constraints(mk_coercion_cnstr(tc, infom, m, a, a_type, justification(),
                                                                            delay_factor+1, relax)));
            } else {
                // giveup...
                return lazy_list<constraints>(constraints(mk_eq_cnstr(meta, a, justification(), relax)));
            }
        }
        constraint_seq cs;
        new_a_type = tc.whnf(new_a_type, cs);
        if (is_meta(d_type)) {
            // case-split
            buffer<std::tuple<name, expr, expr>> alts;
            get_user_coercions(tc.env(), new_a_type, alts);
            buffer<constraints> choices;
            buffer<expr> coes;
            // first alternative: no coercion
            constraint_seq cs1 = cs + mk_eq_cnstr(meta, a, justification(), relax);
            choices.push_back(cs1.to_list());
            unsigned i = alts.size();
            while (i > 0) {
                --i;
                auto const & t = alts[i];
                expr coe   = std::get<1>(t);
                expr new_a = copy_tag(a, mk_app(coe, a));
                coes.push_back(coe);
                constraint_seq csi = cs + mk_eq_cnstr(meta, new_a, new_a_type_jst, relax);
                choices.push_back(csi.to_list());
            }
            return choose(std::make_shared<coercion_elaborator>(infom, meta,
                                                                to_list(choices.begin(), choices.end()),
                                                                to_list(coes.begin(), coes.end())));
        } else {
            expr new_d_type    = tc.whnf(d_type, cs);
            expr const & d_cls = get_app_fn(new_d_type);
            if (is_constant(d_cls)) {
                list<expr> coes = get_coercions(tc.env(), new_a_type, const_name(d_cls));
                if (is_nil(coes)) {
                    expr new_a = a;
                    infom.erase_coercion_info(a);
                    cs += mk_eq_cnstr(meta, new_a, new_a_type_jst, relax);
                    return lazy_list<constraints>(cs.to_list());
                } else if (is_nil(tail(coes))) {
                    expr new_a = copy_tag(a, mk_app(head(coes), a));
                    infom.save_coercion_info(a, new_a);
                    cs += mk_eq_cnstr(meta, new_a, new_a_type_jst, relax);
                    return lazy_list<constraints>(cs.to_list());
                } else {
                    list<constraints> choices = map2<constraints>(coes, [&](expr const & coe) {
                            expr new_a   = copy_tag(a, mk_app(coe, a));
                            constraint c = mk_eq_cnstr(meta, new_a, new_a_type_jst, relax);
                            return (cs + c).to_list();
                        });
                    return choose(std::make_shared<coercion_elaborator>(infom, meta, choices, coes, false));
                }
            } else {
                expr new_a = a;
                infom.erase_coercion_info(a);
                cs += mk_eq_cnstr(meta, new_a, new_a_type_jst, relax);
                return lazy_list<constraints>(cs.to_list());
            }
        }
    };
    return mk_choice_cnstr(m, choice_fn, delay_factor, true, j, relax);
}

/** \brief Given a term <tt>a : a_type</tt>, and an expected type generate a metavariable with a delayed coercion. */
pair<expr, constraint> mk_coercion_elaborator(type_checker & tc, coercion_info_manager & infom, local_context & ctx,
                                              bool relax, expr const & a, expr const & a_type, expr const & expected_type,
                                              justification const & j) {
    expr m = ctx.mk_meta(some_expr(expected_type), a.get_tag());
    return mk_pair(m, mk_coercion_cnstr(tc, infom, m, a, a_type, j, to_delay_factor(cnstr_group::Basic), relax));
}
}
