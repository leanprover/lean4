/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "library/unifier.h"
#include "library/opaque_hints.h"
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
    placeholder_context(environment const & env, io_state const & ios, list<expr> const & ctx,
                        name const & prefix, bool relax, bool use_local_instances):
        m_ios(ios),
        m_ngen(prefix),
        m_tc(mk_type_checker_with_hints(env, m_ngen.mk_child(), relax)),
        m_ctx(m_ngen.next(), ctx),
        m_relax(relax),
        m_use_local_instances(use_local_instances) {
    }

    environment const & env() const { return m_tc->env(); }
    io_state const & ios() const { return m_ios; }
    bool use_local_instances() const { return m_use_local_instances; }
    type_checker & tc() const { return *m_tc; }
};

pair<expr, constraint> mk_placeholder_elaborator(std::shared_ptr<placeholder_context> const & C,
                                                 bool is_strict, optional<expr> const & type, tag g);

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
    // metavariables that occur in m_meta_type, the tactics may instantiate some of them
    buffer<expr>            m_mvars_in_meta_type;
    justification           m_jst;

    placeholder_elaborator(std::shared_ptr<placeholder_context> const & C,
                           expr const & meta, expr const & meta_type,
                           list<expr> const & local_insts, list<name> const & instances,
                           list<tactic_hint_entry> const & tacs,
                           justification const & j, bool ignore_failure):
        choice_iterator(ignore_failure), m_C(C),
        m_meta(meta), m_meta_type(meta_type),
        m_local_instances(local_insts), m_instances(instances),
        m_tactics(tacs),
        m_jst(j) {
        collect_metavars(meta_type, m_mvars_in_meta_type);
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
            local_context::scope scope(ctx);
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
                bool is_strict = true;
                pair<expr, constraint> ac = mk_placeholder_elaborator(m_C, is_strict,
                                                                      some_expr(binding_domain(type)), g);
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
            buffer<constraint> cs;
            expr const & mvar = get_app_fn(m_meta);
            bool relax        = m_C->m_relax;
            cs.push_back(mk_eq_cnstr(mvar, subst.instantiate(mvar), m_jst, relax));
            for (auto const & mvar : m_mvars_in_meta_type)
                cs.push_back(mk_eq_cnstr(mvar, subst.instantiate(mvar), m_jst, relax));
            return optional<constraints>(to_list(cs.begin(), cs.end()));
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


pair<expr, constraint> mk_placeholder_elaborator(std::shared_ptr<placeholder_context> const & C,
                                                 bool is_strict, optional<expr> const & type, tag g) {
    expr m                  = C->m_ctx.mk_meta(type, g);
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
            bool ignore_failure = false;
            return choose(std::make_shared<placeholder_elaborator>(C, meta, meta_type, local_insts, insts, tacs,
                                                                   j, ignore_failure));
        } else if (s.is_assigned(mvar)) {
            // if the metavariable is assigned and it is not a class, then we just ignore it, and return
            // the an empty set of constraints.
            return lazy_list<constraints>(constraints());
        } else {
            list<tactic_hint_entry> tacs = get_tactic_hints(env);
            bool ignore_failure = !is_strict;
            return choose(std::make_shared<placeholder_elaborator>(C, meta, meta_type, list<expr>(), list<name>(),
                                                                   tacs, j, ignore_failure));
        }
    };
    bool owner      = false;
    bool relax      = C->m_relax;
    constraint c    = mk_choice_cnstr(m, choice_fn, to_delay_factor(cnstr_group::ClassInstance),
                                      owner, j, relax);
    return mk_pair(m, c);
}

/** \brief Create a metavariable, and attach choice constraint for generating
    solutions using class-instances and tactic-hints.
*/
pair<expr, constraint> mk_placeholder_elaborator(
    environment const & env, io_state const & ios, list<expr> const & ctx,
    name const & prefix, bool relax, bool use_local_instances,
    bool is_strict, optional<expr> const & type, tag g) {
    auto C = std::make_shared<placeholder_context>(env, ios, ctx, prefix, relax, use_local_instances);
    return mk_placeholder_elaborator(C, is_strict, type, g);
}
}
