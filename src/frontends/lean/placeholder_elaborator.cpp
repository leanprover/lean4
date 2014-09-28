/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/lazy_list_fn.h"
#include "util/flet.h"
#include "kernel/instantiate.h"
#include "kernel/for_each_fn.h"
#include "kernel/abstract.h"
#include "library/unifier.h"
#include "library/reducible.h"
#include "library/metavar_closure.h"
#include "library/error_handling/error_handling.h"
#include "frontends/lean/util.h"
#include "frontends/lean/class.h"
#include "frontends/lean/tactic_hint.h"
#include "frontends/lean/local_context.h"
#include "frontends/lean/choice_iterator.h"

namespace lean {
/** \brief Context for handling placeholder metavariable choice constraint */
struct placeholder_context {
    io_state         m_ios;
    name_generator   m_ngen;
    type_checker_ptr m_tc;
    local_context    m_ctx;
    bool             m_relax;
    bool             m_use_local_instances;
    placeholder_context(environment const & env, io_state const & ios, local_context const & ctx,
                        name const & prefix, bool relax, bool use_local_instances):
        m_ios(ios),
        m_ngen(prefix),
        m_tc(mk_type_checker(env, m_ngen.mk_child(), relax)),
        m_ctx(ctx),
        m_relax(relax),
        m_use_local_instances(use_local_instances) {
    }

    environment const & env() const { return m_tc->env(); }
    io_state const & ios() const { return m_ios; }
    bool use_local_instances() const { return m_use_local_instances; }
    type_checker & tc() const { return *m_tc; }
};

pair<expr, constraint> mk_placeholder_elaborator(std::shared_ptr<placeholder_context> const & C,
                                                 optional<expr> const & type, tag g);

/** \brief Whenever the elaborator finds a placeholder '_' or introduces an
    implicit argument, it creates a metavariable \c ?m. It also creates a
    delayed choice constraint (?m in fn).

    The function \c fn produces a stream of alternative solutions for ?m.
    In this case, \c fn will do the following:
    1) if the elaborated type of ?m is a 'class' C, then the stream will start with
         a) all local instances of class C (if elaborator.local_instances == true)
         b) solutions produced by tactic_hints for class C

    2) if the elaborated type of ?m is not a class, then the stream will only contain
       the solutions produced by tactic_hints.

    The unifier only process delayed choice constraints when there are no other kind
    of constraint to be processed.

    This is a helper class for implementing this choice function.
*/
struct placeholder_elaborator : public choice_iterator {
    std::shared_ptr<placeholder_context> m_C;
    expr                    m_meta;
    // elaborated type of the metavariable
    expr                    m_meta_type;
    // local instances that should also be included in the
    // class-instance resolution.
    // This information is retrieved from the local context
    list<expr>              m_local_instances;
    // global declaration names that are class instances.
    // This information is retrieved using #get_class_instances.
    list<name>              m_instances;
    // Tactic hints for the class
    list<tactic_hint_entry> m_tactics;
    // result produce by last executed tactic.
    proof_state_seq         m_tactic_result;
    justification           m_jst;

    placeholder_elaborator(std::shared_ptr<placeholder_context> const & C,
                           expr const & meta, expr const & meta_type,
                           list<expr> const & local_insts, list<name> const & instances,
                           list<tactic_hint_entry> const & tacs,
                           justification const & j):
        choice_iterator(), m_C(C),
        m_meta(meta), m_meta_type(meta_type),
        m_local_instances(local_insts), m_instances(instances),
        m_tactics(tacs),
        m_jst(j) {
    }

    constraints mk_constraints(constraint const & c, buffer<constraint> const & cs) {
        return cons(c, to_list(cs.begin(), cs.end()));
    }

    optional<constraints> try_instance(expr const & inst, expr const & inst_type) {
        type_checker & tc     = m_C->tc();
        name_generator & ngen = m_C->m_ngen;
        tag g                 = inst.get_tag();
        local_context & ctx   = m_C->m_ctx;
        try {
            flet<local_context> scope(ctx, ctx);
            buffer<expr> locals;
            expr meta_type = m_meta_type;
            while (true) {
                meta_type = tc.whnf(meta_type).first;
                if (!is_pi(meta_type))
                    break;
                expr local  = mk_local(ngen.next(), binding_name(meta_type),
                                       binding_domain(meta_type), binding_info(meta_type));
                ctx.add_local(local);
                locals.push_back(local);
                meta_type = instantiate(binding_body(meta_type), local);
            }
            expr type  = inst_type;
            expr r     = inst;
            buffer<constraint> cs;
            while (true) {
                type = tc.whnf(type).first;
                if (!is_pi(type))
                    break;
                pair<expr, constraint> ac = mk_placeholder_elaborator(m_C, some_expr(binding_domain(type)), g);
                expr arg = ac.first;
                cs.push_back(ac.second);
                r    = mk_app(r, arg).set_tag(g);
                type = instantiate(binding_body(type), arg);
            }
            r = Fun(locals, r);
            bool relax   = m_C->m_relax;
            constraint c = mk_eq_cnstr(m_meta, r, m_jst, relax);
            return optional<constraints>(mk_constraints(c, cs));
        } catch (exception &) {
            return optional<constraints>();
        }
    }

    optional<constraints> try_instance(name const & inst) {
        environment const & env = m_C->env();
        if (auto decl = env.find(inst)) {
            name_generator & ngen = m_C->m_ngen;
            buffer<level> ls_buffer;
            unsigned num_univ_ps = length(decl->get_univ_params());
            for (unsigned i = 0; i < num_univ_ps; i++)
                ls_buffer.push_back(mk_meta_univ(ngen.next()));
            levels ls = to_list(ls_buffer.begin(), ls_buffer.end());
            expr inst_cnst = copy_tag(m_meta, mk_constant(inst, ls));
            expr inst_type = instantiate_type_univ_params(*decl, ls);
            return try_instance(inst_cnst, inst_type);
        } else {
            return optional<constraints>();
        }
    }

    optional<constraints> get_next_tactic_result() {
        while (auto next = m_tactic_result.pull()) {
            m_tactic_result = next->second;
            if (!empty(next->first.get_goals()))
                continue; // has unsolved goals
            substitution subst = next->first.get_subst();
            expr const & mvar = get_app_fn(m_meta);
            bool relax        = m_C->m_relax;
            constraints cs    = metavar_closure(m_meta_type).mk_constraints(subst, m_jst, relax);
            constraint  c     = mk_eq_cnstr(mvar, subst.instantiate(mvar), m_jst, relax);
            return some(cons(c, cs));
        }
        return optional<constraints>();
    }

    virtual optional<constraints> next() {
        while (!empty(m_local_instances)) {
            expr inst         = head(m_local_instances);
            m_local_instances = tail(m_local_instances);
            if (!is_local(inst))
                continue;
            if (auto r = try_instance(inst, mlocal_type(inst)))
                return r;
        }
        while (!empty(m_instances)) {
            name inst   = head(m_instances);
            m_instances = tail(m_instances);
            if (auto cs = try_instance(inst))
                return cs;
        }
        if (auto cs = get_next_tactic_result())
            return cs;
        while (!empty(m_tactics)) {
            tactic const & tac = head(m_tactics).get_tactic();
            m_tactics          = tail(m_tactics);
            proof_state ps(goals(goal(m_meta, m_meta_type)), substitution(), m_C->m_ngen.mk_child());
            try {
                m_tactic_result    = tac(m_C->env(), m_C->ios(), ps);
                if (auto cs = get_next_tactic_result())
                    return cs;
            } catch (exception &) {}
        }
        return optional<constraints>();
    }
};


constraint mk_placeholder_cnstr(std::shared_ptr<placeholder_context> const & C, expr const & m) {
    environment const & env = C->env();
    justification j         = mk_failed_to_synthesize_jst(env, m);
    auto choice_fn = [=](expr const & meta, expr const & meta_type, substitution const & s,
                         name_generator const & /* ngen */) {
        expr const & mvar = get_app_fn(meta);
        if (auto cls_name_it = is_ext_class(C->tc(), meta_type)) {
            name cls_name = *cls_name_it;
            list<expr> const & ctx = C->m_ctx.get_data();
            list<expr> local_insts;
            if (C->use_local_instances())
                local_insts = get_local_instances(C->tc(), ctx, cls_name);
            list<name>  insts = get_class_instances(env, cls_name);
            list<tactic_hint_entry> tacs;
            if (!s.is_assigned(mvar))
                tacs = get_tactic_hints(env, cls_name);
            if (empty(local_insts) && empty(insts) && empty(tacs))
                return lazy_list<constraints>(); // nothing to be done
            // we are always strict with placeholders associated with classes
            return choose(std::make_shared<placeholder_elaborator>(C, meta, meta_type, local_insts, insts, tacs, j));
        } else {
            // do nothing, type is not a class...
            return lazy_list<constraints>(constraints());
        }
    };
    bool owner      = false;
    bool relax      = C->m_relax;
    return mk_choice_cnstr(m, choice_fn, to_delay_factor(cnstr_group::ClassInstance),
                           owner, j, relax);
}

pair<expr, constraint> mk_placeholder_elaborator(std::shared_ptr<placeholder_context> const & C,
                                                 optional<expr> const & type, tag g) {
    expr m       = C->m_ctx.mk_meta(C->m_ngen, type, g);
    constraint c = mk_placeholder_cnstr(C, m);
    return mk_pair(m, c);
}

/** \brief Similar to has_expr_metavar, but ignores metavariables occurring in the type
    of local constants */
static bool has_expr_metavar_relaxed(expr const & e) {
    if (!has_expr_metavar(e))
        return false;
    bool found = false;
    for_each(e, [&](expr const & e, unsigned) {
            if (found || !has_expr_metavar(e))
                return false;
            if (is_metavar(e)) {
                found = true;
                return false;
            }
            if (is_local(e))
                return false; // do not visit type
            return true;
        });
    return found;
}

constraint mk_placeholder_root_cnstr(std::shared_ptr<placeholder_context> const & C, expr const & m, bool is_strict,
                                     unifier_config const & cfg, delay_factor const & factor) {
    environment const & env = C->env();
    justification j         = mk_failed_to_synthesize_jst(env, m);
    auto choice_fn = [=](expr const & meta, expr const & meta_type, substitution const & s,
                         name_generator const & ngen) {
        if (has_expr_metavar_relaxed(meta_type)) {
            // TODO(Leo): remove
            if (factor.on_demand()) {
                constraint delayed_c = mk_placeholder_root_cnstr(C, m, is_strict, cfg, to_delay_factor(cnstr_group::Basic));
                return lazy_list<constraints>(constraints(delayed_c));
            } else if (factor.explict_value() < to_delay_factor(cnstr_group::ClassInstance)) {
                constraint delayed_c = mk_placeholder_root_cnstr(C, m, is_strict, cfg, factor.explict_value()+1);
                return lazy_list<constraints>(constraints(delayed_c));
            }
        }
        if (!is_ext_class(C->tc(), meta_type)) {
            // do nothing, since type is not a class.
            return lazy_list<constraints>(constraints());
        }
        pair<expr, justification> mj = update_meta(meta, s);
        expr new_meta       = mj.first;
        justification new_j = mj.second;
        constraint c = mk_placeholder_cnstr(C, new_meta);
        unifier_config new_cfg(cfg);
        new_cfg.m_discard        = false;
        new_cfg.m_use_exceptions = false;
        unify_result_seq seq1    = unify(env, 1, &c, ngen, new_cfg);
        unify_result_seq seq2    = filter(seq1, [=](pair<substitution, constraints> const & p) {
                substitution new_s     = p.first;
                expr result = new_s.instantiate(new_meta);
                // We only keep complete solution (modulo universe metavariables)
                return !has_expr_metavar_relaxed(result);
            });
        lazy_list<constraints> seq3 = map2<constraints>(seq2, [=](pair<substitution, constraints> const & p) {
                substitution new_s     = p.first;
            // some constraints may have been postponed (example: universe level constraints)
            constraints  postponed = map(p.second,
                                         [&](constraint const & c) {
                                             // we erase internal justifications
                                             return update_justification(c, new_j);
                                         });
            metavar_closure cls(new_meta);
            cls.add(meta_type);
            bool relax     = C->m_relax;
            constraints cs = cls.mk_constraints(new_s, new_j, relax);
            return append(cs, postponed);
            });
        if (is_strict) {
            return seq3;
        } else {
            // make sure it does not fail by appending empty set of constraints
            return append(seq3, lazy_list<constraints>(constraints()));
        }
    };
    bool owner = false;
    bool relax = C->m_relax;
    return mk_choice_cnstr(m, choice_fn, factor, owner, j, relax);
}

/** \brief Create a metavariable, and attach choice constraint for generating
    solutions using class-instances and tactic-hints.
*/
pair<expr, constraint> mk_placeholder_elaborator(
    environment const & env, io_state const & ios, local_context const & ctx,
    name const & prefix, bool relax, bool use_local_instances,
    bool is_strict, optional<expr> const & type, tag g, unifier_config const & cfg) {
    auto C       = std::make_shared<placeholder_context>(env, ios, ctx, prefix, relax, use_local_instances);
    expr m       = C->m_ctx.mk_meta(C->m_ngen, type, g);
    constraint c = mk_placeholder_root_cnstr(C, m, is_strict, cfg, delay_factor());
    return mk_pair(m, c);
}
}
