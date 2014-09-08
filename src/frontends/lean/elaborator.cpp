/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <vector>
#include "util/flet.h"
#include "util/list_fn.h"
#include "util/lazy_list_fn.h"
#include "util/sstream.h"
#include "util/name_map.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "kernel/type_checker.h"
#include "kernel/for_each_fn.h"
#include "kernel/replace_fn.h"
#include "kernel/kernel_exception.h"
#include "kernel/error_msgs.h"
#include "kernel/expr_maps.h"
#include "library/coercion.h"
#include "library/placeholder.h"
#include "library/choice.h"
#include "library/explicit.h"
#include "library/unifier.h"
#include "library/opaque_hints.h"
#include "library/locals.h"
#include "library/let.h"
#include "library/deep_copy.h"
#include "library/typed_expr.h"
#include "library/tactic/tactic.h"
#include "library/tactic/expr_to_tactic.h"
#include "library/error_handling/error_handling.h"
#include "frontends/lean/local_decls.h"
#include "frontends/lean/class.h"
#include "frontends/lean/tactic_hint.h"
#include "frontends/lean/info_manager.h"
#include "frontends/lean/elaborator.h"
#include "frontends/lean/no_info.h"
#include "frontends/lean/extra_info.h"

#ifndef LEAN_DEFAULT_ELABORATOR_LOCAL_INSTANCES
#define LEAN_DEFAULT_ELABORATOR_LOCAL_INSTANCES true
#endif

namespace lean {
// ==========================================
// elaborator configuration options
static name g_elaborator_local_instances{"elaborator", "local_instances"};
RegisterBoolOption(g_elaborator_local_instances, LEAN_DEFAULT_ELABORATOR_LOCAL_INSTANCES, "(lean elaborator) use local declarates as class instances");
bool get_elaborator_local_instances(options const & opts) {
    return opts.get_bool(g_elaborator_local_instances, LEAN_DEFAULT_ELABORATOR_LOCAL_INSTANCES);
}
// ==========================================

/** \brief Functional object for converting the universe metavariables in an expression in new universe parameters.
    The substitution is updated with the mapping metavar -> new param.
    The set of parameter names m_params and the buffer m_new_params are also updated.
*/
class univ_metavars_to_params_fn {
    environment const &        m_env;
    local_decls<level> const & m_lls;
    substitution &             m_subst;
    name_set &                 m_params;
    buffer<name> &             m_new_params;
    unsigned                   m_next_idx;

    /** \brief Create a new universe parameter s.t. the new name does not occur in \c m_params, nor it is
        a global universe in \e m_env or in the local_decls<level> m_lls.
        The new name is added to \c m_params, and the new level parameter is returned.
        The name is of the form "l_i" where \c i >= m_next_idx.
    */
    level mk_new_univ_param() {
        name l("l");
        name r = l.append_after(m_next_idx);
        while (m_lls.contains(r) || m_params.contains(r) || m_env.is_universe(r)) {
            m_next_idx++;
            r = l.append_after(m_next_idx);
        }
        m_params.insert(r);
        m_new_params.push_back(r);
        return mk_param_univ(r);
    }

public:
    univ_metavars_to_params_fn(environment const & env, local_decls<level> const & lls, substitution & s, name_set & ps, buffer<name> & new_ps):
        m_env(env), m_lls(lls), m_subst(s), m_params(ps), m_new_params(new_ps), m_next_idx(1) {}

    level apply(level const & l) {
        return replace(l, [&](level const & l) {
                if (!has_meta(l))
                    return some_level(l);
                if (is_meta(l)) {
                    if (auto it = m_subst.get_level(meta_id(l))) {
                        return some_level(*it);
                    } else {
                        level new_p = mk_new_univ_param();
                        m_subst.assign(l, new_p);
                        return some_level(new_p);
                    }
                }
                return none_level();
            });
    }

    expr apply(expr const & e) {
        if (!has_univ_metavar(e)) {
            return e;
        } else {
            return replace(e, [&](expr const & e) {
                    if (!has_univ_metavar(e)) {
                        return some_expr(e);
                    } else if (is_sort(e)) {
                        return some_expr(update_sort(e, apply(sort_level(e))));
                    } else if (is_constant(e)) {
                        levels ls = map(const_levels(e), [&](level const & l) { return apply(l); });
                        return some_expr(update_constant(e, ls));
                    } else {
                        return none_expr();
                    }
                });
        }
    }

    expr operator()(expr const & e) { return apply(e); }
};

elaborator_context::elaborator_context(environment const & env, io_state const & ios, local_decls<level> const & lls,
                                       pos_info_provider const * pp, info_manager * info, bool check_unassigned):
    m_env(env), m_ios(ios), m_lls(lls), m_pos_provider(pp), m_info_manager(info), m_check_unassigned(check_unassigned) {
    m_use_local_instances = get_elaborator_local_instances(ios.get_options());
}

/** \brief Return true iff \c type is a class or Pi that produces a class. */
optional<name> is_ext_class(environment const & env, expr const & type) {
    if (is_pi(type)) {
        return is_ext_class(env, binding_body(type));
    } else {
        expr f = get_app_fn(type);
        if (!is_constant(f))
            return optional<name>();
        name const & cls_name = const_name(f);
        if (is_class(env, cls_name) || !empty(get_tactic_hints(env, cls_name)))
            return optional<name>(cls_name);
        else
            return optional<name>();
    }
}

/** \brief Return a list of instances of the class \c cls_name that occur in \c ctx */
list<expr> get_local_instances(environment const & env, list<expr> const & ctx, name const & cls_name) {
    buffer<expr> buffer;
    for (auto const & l : ctx) {
        if (!is_local(l))
            continue;
        expr inst_type    = mlocal_type(l);
        if (auto it = is_ext_class(env, inst_type))
            if (*it == cls_name)
                buffer.push_back(l);
    }
    return to_list(buffer.begin(), buffer.end());
}

/** \brief Helper class for implementing the \c elaborate functions. */
class elaborator {
    typedef name_map<expr> mvar2meta;

    /** \brief Auxiliary data-structure for storing the local context, and creating metavariables in the scope of the local context efficiently */
    class context {
        name_generator & m_ngen;
        mvar2meta &      m_mvar2meta;
        list<expr>       m_ctx; // current local context: a list of local constants
        buffer<expr>     m_ctx_buffer; // m_ctx as a buffer
        buffer<expr>     m_ctx_domain_buffer; // m_ctx_domain_buffer[i] == abstract_locals(m_ctx_buffer[i], i, m_ctx_buffer.beg
    public:
        context(name_generator & ngen, mvar2meta & m, list<expr> const & ctx):m_ngen(ngen), m_mvar2meta(m) { set_ctx(ctx); }

        void set_ctx(list<expr> const & ctx) {
            m_ctx = ctx;
            m_ctx_buffer.clear();
            m_ctx_domain_buffer.clear();
            to_buffer(ctx, m_ctx_buffer);
            std::reverse(m_ctx_buffer.begin(), m_ctx_buffer.end());
            for (unsigned i = 0; i < m_ctx_buffer.size(); i++) {
                m_ctx_domain_buffer.push_back(abstract_locals(m_ctx_buffer[i], i, m_ctx_buffer.data()));
            }
        }

        /** \brief Given <tt>e[l_1, ..., l_n]</tt> and assuming \c m_ctx is
               <tt>[l_n : A_n[l_1, ..., l_{n-1}], ..., l_1 : A_1 ]</tt>,
            then the result is
               <tt>(Pi (x_1 : A_1) ... (x_n : A_n[x_1, ..., x_{n-1}]), e[x_1, ... x_n])</tt>.
        */
        expr pi_abstract_context(expr e, tag g) {
            e = abstract_locals(e, m_ctx_buffer.size(), m_ctx_buffer.data());
            unsigned i = m_ctx_domain_buffer.size();
            while (i > 0) {
                --i;
                expr const & l = m_ctx_domain_buffer[i];
                e = save_tag(mk_pi(local_pp_name(l), mlocal_type(l), e, local_info(l)), g);
            }
            return e;
        }

        /** \brief Assuming \c m_ctx is
               <tt>[l_n : A_n[l_1, ..., l_{n-1}], ..., l_1 : A_1 ]</tt>,
            return <tt>(f l_1 ... l_n)</tt>.
        */
        expr apply_context(expr const & f, tag g) {
            expr r = f;
            for (unsigned i = 0; i < m_ctx_buffer.size(); i++)
                r = save_tag(::lean::mk_app(r, m_ctx_buffer[i]), g);
            return r;
        }

        /** \brief Assuming \c m_ctx is
                <tt>[l_n : A_n[l_1, ..., l_{n-1}], ..., l_1 : A_1 ]</tt>,
            return a fresh metavariable \c ?m with type
                <tt>(Pi (x_1 : A_1) ... (x_n : A_n[x_1, ..., x_{n-1}]), Type.{?u})</tt>,
            where \c ?u is a fresh universe metavariable.
        */
        expr mk_type_metavar(tag g) {
            name n = m_ngen.next();
            expr s = save_tag(mk_sort(mk_meta_univ(m_ngen.next())), g);
            expr t = pi_abstract_context(s, g);
            return save_tag(::lean::mk_metavar(n, t), g);
        }

        /** \brief Assuming \c m_ctx is
               <tt>[l_n : A_n[l_1, ..., l_{n-1}], ..., l_1 : A_1 ]</tt>,
            return <tt>(?m l_1 ... l_n)</tt> where \c ?m is a fresh metavariable with type
               <tt>(Pi (x_1 : A_1) ... (x_n : A_n[x_1, ..., x_{n-1}]), Type.{?u})</tt>,
            and \c ?u is a fresh universe metavariable.

            \remark The type of the resulting expression is <tt>Type.{?u}</tt>
        */
        expr mk_type_meta(tag g) {
            return apply_context(mk_type_metavar(g), g);
        }

        /** \brief Given <tt>type[l_1, ..., l_n]</tt> and assuming \c m_ctx is
               <tt>[l_n : A_n[l_1, ..., l_{n-1}], ..., l_1 : A_1 ]</tt>,
            then the result is a fresh metavariable \c ?m with type
               <tt>(Pi (x_1 : A_1) ... (x_n : A_n[x_1, ..., x_{n-1}]), type[x_1, ... x_n])</tt>.
            If <tt>type</tt> is none, then the result is a fresh metavariable \c ?m1 with type
               <tt>(Pi (x_1 : A_1) ... (x_n : A_n[x_1, ..., x_{n-1}]), ?m2 x1 .... xn)</tt>,
            where ?m2 is another fresh metavariable with type
               <tt>(Pi (x_1 : A_1) ... (x_n : A_n[x_1, ..., x_{n-1}]), Type.{?u})</tt>,
            and \c ?u is a fresh universe metavariable.
        */
        expr mk_metavar(optional<expr> const & type, tag g) {
            name n      = m_ngen.next();
            expr r_type = type ? *type : mk_type_meta(g);
            expr t      = pi_abstract_context(r_type, g);
            return save_tag(::lean::mk_metavar(n, t), g);
        }

        /** \brief Given <tt>type[l_1, ..., l_n]</tt> and assuming \c m_ctx is
               <tt>[l_n : A_n[l_1, ..., l_{n-1}], ..., l_1 : A_1 ]</tt>,
            return (?m l_1 ... l_n), where ?m is a fresh metavariable
            created using \c mk_metavar.

            \see mk_metavar
        */
        expr mk_meta(optional<expr> const & type, tag g) {
            expr mvar = mk_metavar(type, g);
            expr meta = apply_context(mvar, g);
            m_mvar2meta.insert(mlocal_name(mvar), meta);
            return meta;
        }

        void add_local(expr const & l) {
            m_ctx = cons(l, m_ctx);
            m_ctx_domain_buffer.push_back(abstract_locals(l, m_ctx_buffer.size(), m_ctx_buffer.data()));
            m_ctx_buffer.push_back(l);
        }

        list<expr> const & get_data() const {
            return m_ctx;
        }

        /** \brief Scope object for restoring the content of the context */
        class scope {
            context &   m_main;
            list<expr>  m_old_ctx;
            unsigned    m_old_sz;
        public:
            scope(context & main):m_main(main), m_old_ctx(main.m_ctx), m_old_sz(main.m_ctx_buffer.size()) {}
            ~scope() {
                m_main.m_ctx = m_old_ctx;
                m_main.m_ctx_buffer.shrink(m_old_sz);
                m_main.m_ctx_domain_buffer.shrink(m_old_sz);
            }
        };

        /** \brief Scope object for temporarily replacing the content of the context */
        class scope_replace {
            context &   m_main;
            list<expr>  m_saved;
        public:
            scope_replace(context & main, list<expr> const & new_ctx):m_main(main), m_saved(m_main.m_ctx) {
                m_main.set_ctx(new_ctx);
            }
            ~scope_replace() {
                m_main.set_ctx(m_saved);
            }
        };
    };

    typedef std::vector<constraint> constraint_vect;
    typedef name_map<expr> local_tactic_hints;
    typedef std::unique_ptr<type_checker> type_checker_ptr;
    typedef rb_map<expr, pair<expr, constraint_seq>, expr_quick_cmp> cache;

    elaborator_context & m_env;
    name_generator       m_ngen;
    type_checker_ptr     m_tc[2];
    mvar2meta            m_mvar2meta; // mapping from metavariable ?m to the (?m l_1 ... l_n) where [l_1 ... l_n] are the local constants
                                     // representing the context where ?m was created.
    context              m_context; // current local context: a list of local constants
    context              m_full_context; // superset of m_context, it also contains non-contextual locals.
    cache                m_cache;

    local_tactic_hints   m_local_tactic_hints; // mapping from metavariable name ?m to tactic expression that should be used to solve it.
                                              // this mapping is populated by the 'by tactic-expr' expression.
    name_set             m_displayed_errors; // set of metavariables that we already reported unsolved/unassigned
    bool                 m_relax_main_opaque; // if true, then treat opaque definitions from the main module as transparent.
    bool                 m_no_info;  // when true, we do not collect information when true, we set is to true whenever we find no_info annotation.
    info_manager         m_pre_info_data;

    // Auxiliary object to "saving" elaborator state
    struct saved_state {
        list<expr> m_ctx;
        list<expr> m_full_ctx;
        cache      m_cache;
        saved_state(elaborator & e):
            m_ctx(e.m_context.get_data()), m_full_ctx(e.m_full_context.get_data()), m_cache(e.m_cache) {}
    };

    struct scope_ctx {
        elaborator &   m_main;
        context::scope m_scope1;
        context::scope m_scope2;
        cache          m_old_cache;
        scope_ctx(elaborator & e):m_main(e), m_scope1(e.m_context), m_scope2(e.m_full_context), m_old_cache(e.m_cache) {}
        ~scope_ctx() { m_main.m_cache = m_old_cache; }
    };

    /** \brief Auxiliary object for creating backtracking points, and replacing the local scopes. */
    struct new_scope {
        elaborator &           m_main;
        bool                   m_old_no_info;
        context::scope_replace m_context_scope;
        context::scope_replace m_full_context_scope;
        cache                  m_old_cache;
        new_scope(elaborator & e, saved_state const & s, bool no_info = false):
            m_main(e),
            m_context_scope(e.m_context, s.m_ctx),
            m_full_context_scope(e.m_full_context, s.m_full_ctx){
            m_old_no_info    = m_main.m_no_info;
            m_main.m_no_info = no_info;
            m_old_cache     = m_main.m_cache;
            m_main.m_cache  = s.m_cache;
        }
        ~new_scope() {
            m_main.m_no_info = m_old_no_info;
            m_main.m_cache  = m_old_cache;
        }
    };

    struct choice_elaborator {
        bool m_ignore_failure;
        choice_elaborator(bool ignore_failure = false):m_ignore_failure(ignore_failure) {}
        virtual optional<constraints> next() = 0;
    };

    /** \brief 'Choice' expressions <tt>(choice e_1 ... e_n)</tt> are mapped into a metavariable \c ?m
        and a choice constraints <tt>(?m in fn)</tt> where \c fn is a choice function.
        The choice function produces a stream of alternatives. In this case, it produces a stream of
        size \c n, one alternative for each \c e_i.
        This is a helper class for implementing this choice functions.
    */
    struct choice_expr_elaborator : public choice_elaborator {
        elaborator & m_elab;
        expr         m_mvar;
        expr         m_choice;
        saved_state  m_state;
        unsigned     m_idx;
        bool         m_relax_main_opaque;
        choice_expr_elaborator(elaborator & elab, expr const & mvar, expr const & c,
                               saved_state const & s, bool relax):
            m_elab(elab), m_mvar(mvar), m_choice(c), m_state(s),
            m_idx(get_num_choices(m_choice)), m_relax_main_opaque(relax) {
        }

        virtual optional<constraints> next() {
            while (m_idx > 0) {
                --m_idx;
                expr const & c = get_choice(m_choice, m_idx);
                expr const & f = get_app_fn(c);
                m_elab.save_identifier_info(f);
                try {
                    new_scope s(m_elab, m_state);
                    pair<expr, constraint_seq> rcs = m_elab.visit(c);
                    expr r = rcs.first;
                    constraint_seq cs = mk_eq_cnstr(m_mvar, r, justification(), m_relax_main_opaque) + rcs.second;
                    return optional<constraints>(cs.to_list());
                } catch (exception &) {}
            }
            return optional<constraints>();
        }
    };

    /** \brief Whenever the elaborator finds a placeholder '_' or introduces an implicit argument, it creates
        a metavariable \c ?m. It also creates a delayed choice constraint (?m in fn).

        The function \c fn produces a stream of alternative solutions for ?m.
        In this case, \c fn will do the following:
          1) if the elaborated type of ?m is a 'class' C, then the stream will start with
                  a) all local instances of class C (if elaborator.local_instances == true)
                  b) solutions produced by tactic_hints for class C
          2) if the elaborated type of ?m is not a class, then the stream will only contain
             the solutions produced by tactic_hints.

        The unifier only process delayed choice constraints when there are no other kind of constraint to be
        processed.

        This is a helper class for implementing this choice function.
    */
    struct placeholder_elaborator : public choice_elaborator {
        elaborator &            m_elab;
        expr                    m_meta;
        expr                    m_meta_type; // elaborated type of the metavariable
        list<expr>              m_local_instances; // local instances that should also be included in the class-instance resolution.
        list<name>              m_instances; // global declaration names that are class instances.
                                             // This information is retrieved using #get_class_instances.
        list<tactic_hint_entry> m_tactics;
        proof_state_seq         m_tactic_result; // result produce by last executed tactic.
        buffer<expr>            m_mvars_in_meta_type; // metavariables that occur in m_meta_type, the tactics may instantiate some of them
        saved_state             m_state;
        justification           m_jst;
        bool                    m_relax_main_opaque;

        placeholder_elaborator(elaborator & elab, expr const & meta, expr const & meta_type,
                               list<expr> const & local_insts, list<name> const & instances, list<tactic_hint_entry> const & tacs,
                               saved_state const & s, justification const & j, bool ignore_failure, bool relax):
            choice_elaborator(ignore_failure),
            m_elab(elab), m_meta(meta), m_meta_type(meta_type), m_local_instances(local_insts), m_instances(instances),
            m_tactics(tacs), m_state(s), m_jst(j), m_relax_main_opaque(relax) {
            collect_metavars(meta_type, m_mvars_in_meta_type);
        }

        optional<constraints> try_instance(expr const & inst, expr const & inst_type) {
            expr type   = inst_type;
            // create the term pre (inst _ ... _)
            expr pre    = copy_tag(m_meta, mk_explicit(inst));
            while (is_pi(type)) {
                type = binding_body(type);
                pre  = copy_tag(m_meta, ::lean::mk_app(pre, copy_tag(m_meta, mk_strict_expr_placeholder())));
            }
            try {
                bool no_info = true;
                new_scope s(m_elab, m_state, no_info);
                pair<expr, constraint_seq> rcs = m_elab.visit(pre); // use elaborator to create metavariables, levels, etc.
                expr r = rcs.first;
                buffer<constraint> cs;
                to_buffer(rcs.second, m_jst, cs);
                return optional<constraints>(cons(mk_eq_cnstr(m_meta, r, m_jst, m_relax_main_opaque),
                                                  to_list(cs.begin(), cs.end())));
            } catch (exception &) {
                return optional<constraints>();
            }
        }

        optional<constraints> try_instance(name const & inst) {
            auto decl   = m_elab.env().find(inst);
            if (!decl)
                return optional<constraints>();
            return try_instance(copy_tag(m_meta, mk_constant(inst)), decl->get_type());
        }

        optional<constraints> get_next_tactic_result() {
            while (auto next = m_tactic_result.pull()) {
                m_tactic_result = next->second;
                if (!empty(next->first.get_goals()))
                    continue; // has unsolved goals
                substitution subst = next->first.get_subst();
                buffer<constraint> cs;
                expr const & mvar = get_app_fn(m_meta);
                cs.push_back(mk_eq_cnstr(mvar, subst.instantiate(mvar), m_jst, m_relax_main_opaque));
                for (auto const & mvar : m_mvars_in_meta_type)
                    cs.push_back(mk_eq_cnstr(mvar, subst.instantiate(mvar), m_jst, m_relax_main_opaque));
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
                proof_state ps(goals(goal(m_meta, m_meta_type)), substitution(), m_elab.m_ngen.mk_child());
                try {
                    m_tactic_result    = tac(m_elab.env(), m_elab.ios(), ps);
                    if (auto cs = get_next_tactic_result())
                        return cs;
                } catch (exception &) {}
            }
            return optional<constraints>();
        }
    };

    lazy_list<constraints> choose(std::shared_ptr<choice_elaborator> c) {
        return mk_lazy_list<constraints>([=]() {
                auto s = c->next();
                if (s) {
                    return some(mk_pair(*s, choose(c)));
                } else if (c->m_ignore_failure) {
                    // return singleton empty list of constraints, and let tactic hints try to instantiate the metavariable.
                    return lazy_list<constraints>::maybe_pair(constraints(), lazy_list<constraints>());
                } else {
                    return lazy_list<constraints>::maybe_pair();
                }
            });
    }

public:
    elaborator(elaborator_context & env, list<expr> const & ctx, name_generator const & ngen):
        m_env(env),
        m_ngen(ngen),
        m_context(m_ngen, m_mvar2meta, ctx),
        m_full_context(m_ngen, m_mvar2meta, ctx) {
        m_relax_main_opaque = false;
        m_no_info = false;
        m_tc[0]  = mk_type_checker_with_hints(env.m_env, m_ngen.mk_child(), false);
        m_tc[1]  = mk_type_checker_with_hints(env.m_env, m_ngen.mk_child(), true);
    }

    environment const & env() const { return m_env.m_env; }
    io_state const & ios() const { return m_env.m_ios; }
    local_decls<level> const & lls() const { return m_env.m_lls; }
    bool use_local_instances() const { return m_env.m_use_local_instances; }
    info_manager * infom() const { return m_env.m_info_manager; }
    pos_info_provider const * pip() const { return m_env.m_pos_provider; }
    bool check_unassigned() const { return m_env.m_check_unassigned; }

    expr mk_local(name const & n, expr const & t, binder_info const & bi) {
        return ::lean::mk_local(m_ngen.next(), n, t, bi);
    }

    pair<expr, constraint_seq> infer_type(expr const & e) { return m_tc[m_relax_main_opaque]->infer(e); }
    pair<expr, constraint_seq> whnf(expr const & e) { return m_tc[m_relax_main_opaque]->whnf(e); }
    expr infer_type(expr const & e, constraint_seq & s) { return m_tc[m_relax_main_opaque]->infer(e, s); }
    expr whnf(expr const & e, constraint_seq & s) { return m_tc[m_relax_main_opaque]->whnf(e, s); }

    static expr save_tag(expr && e, tag g) { e.set_tag(g); return e; }
    expr mk_app(expr const & f, expr const & a, tag g) { return save_tag(::lean::mk_app(f, a), g); }

    /** \brief Store the pair (pos(e), type(r)) in the info_data if m_info_manager is available. */
    void save_type_data(expr const & e, expr const & r) {
        if (!m_no_info && infom() && pip() && (is_constant(e) || is_local(e) || is_placeholder(e))) {
            if (auto p = pip()->get_pos_info(e)) {
                expr t = m_tc[m_relax_main_opaque]->infer(r).first;
                m_pre_info_data.add_type_info(p->first, p->second, t);
            }
        }
    }

    /** \brief Store type information at pos(e) for r if \c e is marked as "extra" in the info_manager */
    void save_extra_type_data(expr const & e, expr const & r) {
        if (!m_no_info && infom() && pip()) {
            if (auto p = pip()->get_pos_info(e)) {
                expr t = m_tc[m_relax_main_opaque]->infer(r).first;
                m_pre_info_data.add_extra_type_info(p->first, p->second, r, t);
            }
        }
    }

    /** \brief Auxiliary function for saving information about which overloaded identifier was used by the elaborator. */
    void save_identifier_info(expr const & f) {
        if (!m_no_info && infom() && pip() && is_constant(f)) {
            if (auto p = pip()->get_pos_info(f))
                m_pre_info_data.add_identifier_info(p->first, p->second, const_name(f));
        }
    }

    /** \brief Store actual term that was synthesized for an explicit placeholders */
    void save_synth_data(expr const & e, expr const & r) {
        if (!m_no_info && infom() && pip() && is_placeholder(e)) {
            if (auto p = pip()->get_pos_info(e))
                m_pre_info_data.add_synth_info(p->first, p->second, r);
        }
    }

    void save_placeholder_info(expr const & e, expr const & r) {
        if (is_explicit_placeholder(e)) {
            save_type_data(e, r);
            save_synth_data(e, r);
        }
    }

    /** \brief Auxiliary function for saving information about which coercion was used by the elaborator.
        It marks that coercion c was used on e.
    */
    void save_coercion_info(expr const & e, expr const & c) {
        if (!m_no_info && infom() && pip()) {
            if (auto p = pip()->get_pos_info(e)) {
                expr t = m_tc[m_relax_main_opaque]->infer(c).first;
                m_pre_info_data.add_coercion_info(p->first, p->second, c, t);
            }
        }
    }

    /** \brief Remove coercion information associated with \c e */
    void erase_coercion_info(expr const & e) {
        if (!m_no_info && infom() && pip()) {
            if (auto p = pip()->get_pos_info(e))
                m_pre_info_data.erase_coercion_info(p->first, p->second);
        }
    }

    void copy_info_to_manager(substitution s) {
        if (!infom())
            return;
        m_pre_info_data.instantiate(s);
        bool overwrite = true;
        infom()->merge(m_pre_info_data, overwrite);
        m_pre_info_data.clear();
    }

    list<name> get_class_instances(expr const & type) {
        if (is_constant(get_app_fn(type))) {
            name const & c = const_name(get_app_fn(type));
            return ::lean::get_class_instances(env(), c);
        } else {
            return list<name>();
        }
    }

    static expr instantiate_meta(expr const & meta, substitution & subst) {
        buffer<expr> locals;
        expr mvar = get_app_args(meta, locals);
        mvar = update_mlocal(mvar, subst.instantiate_all(mlocal_type(mvar)));
        for (auto & local : locals) local = subst.instantiate_all(local);
        return ::lean::mk_app(mvar, locals);
    }

    /** \brief Return a 'failed to synthesize placholder' justification for the given
        metavariable application \c m of the form (?m l_1 ... l_k) */
    justification mk_failed_to_synthesize_jst(expr const & m) {
        environment _env = env();
        return mk_justification(m, [=](formatter const & fmt, substitution const & subst) {
                substitution tmp(subst);
                expr new_m    = instantiate_meta(m, tmp);
                expr new_type = type_checker(_env).infer(new_m).first;
                proof_state ps(goals(goal(new_m, new_type)), substitution(), name_generator("dontcare"));
                return format("failed to synthesize placeholder") + line() + ps.pp(fmt);
            });
    }

    /** \brief Create a metavariable, and attach choice constraint for generating
        solutions using class-instances and tactic-hints.
    */
    expr mk_placeholder_meta(optional<expr> const & type, tag g, bool is_strict, constraint_seq & cs) {
        expr m              = m_context.mk_meta(type, g);
        saved_state st(*this);
        justification j     = mk_failed_to_synthesize_jst(m);
        auto choice_fn = [=](expr const & meta, expr const & meta_type, substitution const & s, name_generator const & /* ngen */) {
            expr const & mvar = get_app_fn(meta);
            if (is_ext_class(env(), meta_type)) {
                name const & cls_name = const_name(get_app_fn(meta_type));
                list<expr> local_insts;
                if (use_local_instances())
                    local_insts = get_local_instances(env(), st.m_ctx, cls_name);
                list<name>  insts = get_class_instances(meta_type);
                list<tactic_hint_entry> tacs;
                if (!s.is_assigned(mvar))
                    tacs = get_tactic_hints(env(), cls_name);
                if (empty(local_insts) && empty(insts) && empty(tacs))
                    return lazy_list<constraints>(); // nothing to be done
                bool ignore_failure = false; // we are always strict with placeholders associated with classes
                return choose(std::make_shared<placeholder_elaborator>(*this, meta, meta_type, local_insts, insts, tacs, st,
                                                                       j, ignore_failure, m_relax_main_opaque));
            } else if (s.is_assigned(mvar)) {
                // if the metavariable is assigned and it is not a class, then we just ignore it, and return
                // the an empty set of constraints.
                return lazy_list<constraints>(constraints());
            } else {
                list<tactic_hint_entry> tacs = get_tactic_hints(env());
                bool ignore_failure = !is_strict;
                return choose(std::make_shared<placeholder_elaborator>(*this, meta, meta_type, list<expr>(), list<name>(),
                                                                       tacs, st, j, ignore_failure, m_relax_main_opaque));
            }
        };
        cs += mk_choice_cnstr(m, choice_fn, to_delay_factor(cnstr_group::ClassInstance), false, j, m_relax_main_opaque);
        return m;
    }

    /** \brief Convert the metavariable to the metavariable application that captures
        the context where it was defined.
    */
    optional<expr> mvar_to_meta(expr mvar) {
        if (auto it = m_mvar2meta.find(mlocal_name(mvar)))
            return some_expr(*it);
        else
            return none_expr();
    }

    expr visit_expecting_type(expr const & e, constraint_seq & cs) {
        if (is_placeholder(e) && !placeholder_type(e)) {
            expr r = m_context.mk_type_meta(e.get_tag());
            save_placeholder_info(e, r);
            return r;
        } else {
            return visit(e, cs);
        }
    }

    expr visit_expecting_type_of(expr const & e, expr const & t, constraint_seq & cs) {
        if (is_placeholder(e) && !placeholder_type(e)) {
            expr r = mk_placeholder_meta(some_expr(t), e.get_tag(), is_strict_placeholder(e), cs);
            save_placeholder_info(e, r);
            return r;
        } else if (is_choice(e)) {
            return visit_choice(e, some_expr(t), cs);
        } else if (is_by(e)) {
            return visit_by(e, some_expr(t), cs);
        } else {
            return visit(e, cs);
        }
    }

    expr visit_choice(expr const & e, optional<expr> const & t, constraint_seq & cs) {
        lean_assert(is_choice(e));
        // Possible optimization: try to lookahead and discard some of the alternatives.
        expr m              = m_full_context.mk_meta(t, e.get_tag());
        saved_state s(*this);
        bool relax          = m_relax_main_opaque;
        auto fn = [=](expr const & mvar, expr const & /* type */, substitution const & /* s */, name_generator const & /* ngen */) {
            return choose(std::make_shared<choice_expr_elaborator>(*this, mvar, e, s, relax));
        };
        justification j = mk_justification("none of the overloads is applicable", some_expr(e));
        cs += mk_choice_cnstr(m, fn, to_delay_factor(cnstr_group::Basic), true, j, m_relax_main_opaque);
        return m;
    }

    expr visit_by(expr const & e, optional<expr> const & t, constraint_seq & cs) {
        lean_assert(is_by(e));
        expr tac = visit(get_by_arg(e), cs);
        expr m   = m_context.mk_meta(t, e.get_tag());
        m_local_tactic_hints.insert(mlocal_name(get_app_fn(m)), tac);
        return m;
    }

    /** \brief Make sure \c f is really a function, if it is not, try to apply coercions.
        The result is a pair <tt>new_f, f_type</tt>, where new_f is the new value for \c f,
        and \c f_type is its type (and a Pi-expression)
    */
    pair<expr, expr> ensure_fun(expr f, constraint_seq & cs) {
        expr f_type = infer_type(f, cs);
        if (!is_pi(f_type))
            f_type = whnf(f_type, cs);
        if (!is_pi(f_type) && has_metavar(f_type)) {
            constraint_seq saved_cs = cs;
            f_type = whnf(f_type, cs);
            if (!is_pi(f_type) && is_meta(f_type)) {
                cs = saved_cs;
                // let type checker add constraint
                f_type = m_tc[m_relax_main_opaque]->ensure_pi(f_type, f, cs);
            }
        }
        if (!is_pi(f_type)) {
            // try coercion to function-class
            optional<expr> c = get_coercion_to_fun(env(), f_type);
            if (c) {
                expr old_f = f;
                f = mk_app(*c, f, f.get_tag());
                f_type = infer_type(f, cs);
                save_coercion_info(old_f, f);
                lean_assert(is_pi(f_type));
            } else {
                throw_kernel_exception(env(), f, [=](formatter const & fmt) { return pp_function_expected(fmt, f); });
            }
        } else {
            erase_coercion_info(f);
        }
        lean_assert(is_pi(f_type));
        return mk_pair(f, f_type);
    }

    bool has_coercions_from(expr const & a_type) {
        expr const & a_cls = get_app_fn(whnf(a_type).first);
        return is_constant(a_cls) && ::lean::has_coercions_from(env(), const_name(a_cls));
    }

    bool has_coercions_to(expr const & d_type) {
        expr const & d_cls = get_app_fn(whnf(d_type).first);
        return is_constant(d_cls) && ::lean::has_coercions_to(env(), const_name(d_cls));
    }

    expr apply_coercion(expr const & a, expr a_type, expr d_type) {
        a_type = whnf(a_type).first;
        d_type = whnf(d_type).first;
        expr const & d_cls = get_app_fn(d_type);
        if (is_constant(d_cls)) {
            if (auto c = get_coercion(env(), a_type, const_name(d_cls))) {
                expr r = mk_app(*c, a, a.get_tag());
                save_coercion_info(a, r);
                return r;
            } else {
                erase_coercion_info(a);
            }
        }
        return a;
    }

    struct coercion_case_split {
        elaborator &      m_elab;
        expr              m_arg;
        bool              m_id; // true if identity was not tried yet
        list<constraints> m_choices;
        list<expr>        m_coercions;

        coercion_case_split(elaborator & elab, expr const & arg, list<constraints> const & choices, list<expr> const & coes):
            m_elab(elab), m_arg(arg), m_id(true), m_choices(choices), m_coercions(coes) {
            lean_assert(length(m_coercions) + 1 == length(m_choices));
        }

        optional<constraints> next() {
            if (!m_choices)
                return optional<constraints>();
            if (m_id) {
                m_id = false;
                m_elab.erase_coercion_info(m_arg);
            } else if (m_coercions) {
                expr c      = head(m_coercions);
                m_coercions = tail(m_coercions);
                m_elab.save_coercion_info(m_arg, ::lean::mk_app(c, m_arg));
            }
            auto r = head(m_choices);
            m_choices = tail(m_choices);
            return optional<constraints>(r);
        }
    };

    lazy_list<constraints> choose(std::shared_ptr<coercion_case_split> c) {
        return mk_lazy_list<constraints>([=]() {
                auto s = c->next();
                if (s) {
                    return some(mk_pair(*s, choose(c)));
                } else {
                    return lazy_list<constraints>::maybe_pair();
                }
            });
    }

    constraint mk_delayed_coercion_cnstr(expr const & m, expr const & a, expr const & a_type,
                                         justification const & j, unsigned delay_factor) {
        bool relax = m_relax_main_opaque;
        auto choice_fn = [=](expr const & mvar, expr const & d_type, substitution const & s, name_generator const & /* ngen */) {
            type_checker & tc = *m_tc[relax];
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
                    return lazy_list<constraints>(constraints(mk_delayed_coercion_cnstr(m, a, a_type, justification(), delay_factor+1)));
                } else {
                    // giveup...
                    return lazy_list<constraints>(constraints(mk_eq_cnstr(mvar, a, justification(), relax)));
                }
            }
            constraint_seq cs;
            new_a_type = tc.whnf(new_a_type, cs);
            if (is_meta(d_type)) {
                // case-split
                buffer<std::tuple<name, expr, expr>> alts;
                get_user_coercions(env(), new_a_type, alts);
                buffer<constraints> choices;
                buffer<expr> coes;
                // first alternative: no coercion
                constraint_seq cs1 = cs + mk_eq_cnstr(mvar, a, justification(), relax);
                choices.push_back(cs1.to_list());
                unsigned i = alts.size();
                while (i > 0) {
                    --i;
                    auto const & t = alts[i];
                    expr coe   = std::get<1>(t);
                    expr new_a = mk_app(coe, a, a.get_tag());
                    coes.push_back(coe);
                    constraint_seq csi = cs + mk_eq_cnstr(mvar, new_a, new_a_type_jst, relax);
                    choices.push_back(csi.to_list());
                }
                return choose(std::make_shared<coercion_case_split>(*this, mvar,
                                                                    to_list(choices.begin(), choices.end()),
                                                                    to_list(coes.begin(), coes.end())));
            } else {
                expr new_a         = a;
                expr new_d_type    = tc.whnf(d_type, cs);
                expr const & d_cls = get_app_fn(new_d_type);
                if (is_constant(d_cls)) {
                    if (auto c = get_coercion(env(), new_a_type, const_name(d_cls))) {
                        new_a = mk_app(*c, a, a.get_tag());
                        save_coercion_info(a, new_a);
                    } else {
                        erase_coercion_info(a);
                    }
                }
                cs += mk_eq_cnstr(mvar, new_a, new_a_type_jst, relax);
                return lazy_list<constraints>(cs.to_list());
            }
        };
        return mk_choice_cnstr(m, choice_fn, delay_factor, true, j, m_relax_main_opaque);
    }

    /** \brief Given a term <tt>a : a_type</tt>, and an expected type generate a metavariable with a delayed coercion. */
    pair<expr, constraint_seq> mk_delayed_coercion(expr const & a, expr const & a_type, expr const & expected_type, justification const & j) {
        expr m = m_full_context.mk_meta(some_expr(expected_type), a.get_tag());
        return to_ecs(m, mk_delayed_coercion_cnstr(m, a, a_type, j, to_delay_factor(cnstr_group::Basic)));
    }

    /** \brief Given a term <tt>a : a_type</tt>, ensure it has type \c expected_type. Apply coercions if needed

        \remark relax == true affects how opaque definitions in the main module are treated.
    */
    pair<expr, constraint_seq> ensure_has_type(expr const & a, expr const & a_type, expr const & expected_type,
                                               justification const & j, bool relax) {
        if (is_meta(expected_type) && has_coercions_from(a_type)) {
            return mk_delayed_coercion(a, a_type, expected_type, j);
        } else if (is_meta(a_type) && has_coercions_to(expected_type)) {
            return mk_delayed_coercion(a, a_type, expected_type, j);
        } else {
            auto dcs = m_tc[relax]->is_def_eq(a_type, expected_type, j);
            if (dcs.first) {
                return to_ecs(a, dcs.second);
            } else {
                expr new_a = apply_coercion(a, a_type, expected_type);
                bool coercion_worked = false;
                constraint_seq cs;
                if (!is_eqp(a, new_a)) {
                    expr new_a_type = infer_type(new_a, cs);
                    coercion_worked = m_tc[relax]->is_def_eq(new_a_type, expected_type, j, cs);
                }
                if (coercion_worked) {
                    return to_ecs(new_a, cs);
                } else if (has_metavar(a_type) || has_metavar(expected_type)) {
                    // rely on unification hints to solve this constraint
                    return to_ecs(a, mk_eq_cnstr(a_type, expected_type, j, relax));
                } else {
                    throw unifier_exception(j, substitution());
                }
            }
        }
    }

    bool is_choice_app(expr const & e) {
        expr const & f = get_app_fn(e);
        return is_choice(f) || (is_annotation(f) && is_choice(get_nested_annotation_arg(f)));
    }

    /** \brief Process ((choice f_1 ... f_n) a_1 ... a_k) as
        (choice (f_1 a_1 ... a_k) ... (f_n a_1 ... a_k))
    */
    expr visit_choice_app(expr const & e, constraint_seq & cs) {
        buffer<expr> args;
        expr r = get_app_rev_args(e, args);
        expr f = get_nested_annotation_arg(r);
        lean_assert(is_choice(f));
        buffer<expr> new_choices;
        unsigned num = get_num_choices(f);
        for (unsigned i = 0; i < num; i++) {
            expr f_i = get_choice(f, i);
            f_i      = copy_annotations(r, f_i);
            new_choices.push_back(mk_rev_app(f_i, args));
        }
        return visit_choice(copy_tag(e, mk_choice(new_choices.size(), new_choices.data())), none_expr(), cs);
    }

    expr visit_app(expr const & e, constraint_seq & cs) {
        if (is_choice_app(e))
            return visit_choice_app(e, cs);
        constraint_seq f_cs;
        bool expl   = is_nested_explicit(get_app_fn(e));
        expr f      = visit(app_fn(e), f_cs);
        auto f_t    = ensure_fun(f, f_cs);
        f           = f_t.first;
        expr f_type = f_t.second;
        lean_assert(is_pi(f_type));
        if (!expl) {
            bool first = true;
            while (binding_info(f_type).is_strict_implicit() || (!first && binding_info(f_type).is_implicit())) {
                tag g          = f.get_tag();
                bool is_strict = false;
                expr imp_arg   = mk_placeholder_meta(some_expr(binding_domain(f_type)), g, is_strict, f_cs);
                f              = mk_app(f, imp_arg, g);
                auto f_t       = ensure_fun(f, f_cs);
                f              = f_t.first;
                f_type         = f_t.second;
                first          = false;
            }
            if (!first) {
                // we save the info data again for application of functions with strict implicit arguments
                save_type_data(get_app_fn(e), f);
            }
        }
        constraint_seq a_cs;
        expr d_type = binding_domain(f_type);
        expr a      = visit_expecting_type_of(app_arg(e), d_type, a_cs);
        expr a_type = infer_type(a, a_cs);
        expr r      = mk_app(f, a, e.get_tag());

        justification j = mk_app_justification(r, a, d_type, a_type);
        auto new_a_cs   = ensure_has_type(a, a_type, d_type, j, m_relax_main_opaque);
        expr new_a      = new_a_cs.first;
        cs += f_cs + new_a_cs.second + a_cs;
        return update_app(r, app_fn(r), new_a);
    }

    expr visit_placeholder(expr const & e, constraint_seq & cs) {
        expr r = mk_placeholder_meta(placeholder_type(e), e.get_tag(), is_strict_placeholder(e), cs);
        save_placeholder_info(e, r);
        return r;
    }

    level replace_univ_placeholder(level const & l) {
        return replace(l, [&](level const & l) {
                if (is_placeholder(l))
                    return some_level(mk_meta_univ(m_ngen.next()));
                else
                    return none_level();
            });
    }

    expr visit_sort(expr const & e) {
        return update_sort(e, replace_univ_placeholder(sort_level(e)));
    }

    expr visit_macro(expr const & e, constraint_seq & cs) {
        if (is_as_is(e)) {
            return get_as_is_arg(e);
        } else {
            // Remark: Macros are not meant to be used in the front end.
            // Perhaps, we should throw error.
            buffer<expr> args;
            for (unsigned i = 0; i < macro_num_args(e); i++)
                args.push_back(visit(macro_arg(e, i), cs));
            return update_macro(e, args.size(), args.data());
        }
    }

    expr visit_constant(expr const & e) {
        declaration d = env().get(const_name(e));
        buffer<level> ls;
        for (level const & l : const_levels(e))
            ls.push_back(replace_univ_placeholder(l));
        unsigned num_univ_params = length(d.get_univ_params());
        if (num_univ_params < ls.size())
            throw_kernel_exception(env(), sstream() << "incorrect number of universe levels parameters for '"
                                   << const_name(e) << "', #" << num_univ_params
                                   << " expected, #" << ls.size() << " provided");
        // "fill" with meta universe parameters
        for (unsigned i = ls.size(); i < num_univ_params; i++)
            ls.push_back(mk_meta_univ(m_ngen.next()));
        lean_assert(num_univ_params == ls.size());
        return update_constant(e, to_list(ls.begin(), ls.end()));
    }

    /** \brief Make sure \c e is a type. If it is not, then try to apply coercions. */
    expr ensure_type(expr const & e, constraint_seq & cs) {
        expr t = infer_type(e, cs);
        erase_coercion_info(e);
        if (is_sort(t))
            return e;
        t = whnf(t, cs);
        if (is_sort(t))
            return e;
        if (has_metavar(t)) {
            t = whnf(t, cs);
            if (is_sort(t))
                return e;
            if (is_meta(t)) {
                // let type checker add constraint
                m_tc[m_relax_main_opaque]->ensure_sort(t, e, cs);
                return e;
            }
        }
        optional<expr> c = get_coercion_to_sort(env(), t);
        if (c) {
            expr r = mk_app(*c, e, e.get_tag());
            save_coercion_info(e, r);
            return r;
        }
        throw_kernel_exception(env(), e, [=](formatter const & fmt) { return pp_type_expected(fmt, e); });
    }

    /** \brief Similar to instantiate_rev, but assumes that subst contains only local constants.
        When replacing a variable with a local, we copy the local constant and inherit the tag
        associated with the variable. This is a trick for getter better error messages */
    expr instantiate_rev_locals(expr const & a, unsigned n, expr const * subst) {
        if (closed(a))
            return a;
        return replace(a, [=](expr const & m, unsigned offset) -> optional<expr> {
                if (offset >= get_free_var_range(m))
                    return some_expr(m); // expression m does not contain free variables with idx >= offset
                if (is_var(m)) {
                    unsigned vidx = var_idx(m);
                    if (vidx >= offset) {
                        unsigned h = offset + n;
                        if (h < offset /* overflow, h is bigger than any vidx */ || vidx < h) {
                            expr local = subst[n - (vidx - offset) - 1];
                            lean_assert(is_local(local));
                            return some_expr(copy_tag(m, copy(local)));
                        } else {
                            return some_expr(copy_tag(m, mk_var(vidx - n)));
                        }
                    }
                }
                return none_expr();
            });
    }

    expr visit_binding(expr e, expr_kind k, constraint_seq & cs) {
        scope_ctx scope(*this);
        buffer<expr> ds, ls, es;
        while (e.kind() == k) {
            es.push_back(e);
            expr d   = binding_domain(e);
            d = instantiate_rev_locals(d, ls.size(), ls.data());
            d = ensure_type(visit_expecting_type(d, cs), cs);
            ds.push_back(d);
            expr l   = mk_local(binding_name(e), d, binding_info(e));
            if (binding_info(e).is_contextual())
                m_context.add_local(l);
            m_full_context.add_local(l);
            ls.push_back(l);
            e = binding_body(e);
        }
        lean_assert(ls.size() == es.size() && ls.size() == ds.size());
        e = instantiate_rev_locals(e, ls.size(), ls.data());
        e = (k == expr_kind::Pi) ? ensure_type(visit_expecting_type(e, cs), cs) : visit(e, cs);
        e = abstract_locals(e, ls.size(), ls.data());
        unsigned i = ls.size();
        while (i > 0) {
            --i;
            e = update_binding(es[i], abstract_locals(ds[i], i, ls.data()), e);
        }
        return e;
    }
    expr visit_pi(expr const & e, constraint_seq & cs) { return visit_binding(e, expr_kind::Pi, cs); }
    expr visit_lambda(expr const & e, constraint_seq & cs) { return visit_binding(e, expr_kind::Lambda, cs); }

    expr visit_typed_expr(expr const & e, constraint_seq & cs) {
        constraint_seq t_cs;
        expr t      = visit(get_typed_expr_type(e), t_cs);
        constraint_seq v_cs;
        expr v      = visit(get_typed_expr_expr(e), v_cs);
        expr v_type = infer_type(v, v_cs);
        justification j = mk_justification(e, [=](formatter const & fmt, substitution const & subst) {
                substitution s(subst);
                format expected_fmt, given_fmt;
                std::tie(expected_fmt, given_fmt) = pp_until_different(fmt, s.instantiate(t), s.instantiate(v_type));
                format r("type mismatch at term");
                r += pp_indent_expr(fmt, s.instantiate(v));
                r += compose(line(), format("has type"));
                r += given_fmt;
                r += compose(line(), format("but is expected to have type"));
                r += expected_fmt;
                return r;
            });
        auto new_vcs    = ensure_has_type(v, v_type, t, j, m_relax_main_opaque);
        v = new_vcs.first;
        cs += t_cs + new_vcs.second + v_cs;
        return v;
    }

    expr visit_let_value(expr const & e, constraint_seq & cs) {
        if (auto p = m_cache.find(e)) {
            cs += p->second;
            return p->first;
        } else {
            auto ecs = visit(get_let_value_expr(e));
            expr r = copy_tag(ecs.first, mk_let_value(ecs.first));
            m_cache.insert(e, mk_pair(r, ecs.second));
            cs += ecs.second;
            return r;
        }
    }

    expr visit_core(expr const & e, constraint_seq & cs) {
        if (is_placeholder(e)) {
            return visit_placeholder(e, cs);
        } else if (is_choice(e)) {
            return visit_choice(e, none_expr(), cs);
        } else if (is_let_value(e)) {
            return visit_let_value(e, cs);
        } else if (is_by(e)) {
            return visit_by(e, none_expr(), cs);
        } else if (is_no_info(e)) {
            flet<bool> let(m_no_info, true);
            return visit(get_annotation_arg(e), cs);
        } else if (is_typed_expr(e)) {
            return visit_typed_expr(e, cs);
        } else {
            switch (e.kind()) {
            case expr_kind::Local:      return e;
            case expr_kind::Meta:       return e;
            case expr_kind::Sort:       return visit_sort(e);
            case expr_kind::Var:        lean_unreachable();  // LCOV_EXCL_LINE
            case expr_kind::Constant:   return visit_constant(e);
            case expr_kind::Macro:      return visit_macro(e, cs);
            case expr_kind::Lambda:     return visit_lambda(e, cs);
            case expr_kind::Pi:         return visit_pi(e, cs);
            case expr_kind::App:        return visit_app(e, cs);
            }
            lean_unreachable(); // LCOV_EXCL_LINE
        }
    }

    pair<expr, constraint_seq> visit(expr const & e) {
        if (is_extra_info(e)) {
            auto ecs = visit(get_annotation_arg(e));
            save_extra_type_data(e, ecs.first);
            return ecs;
        }
        expr r;
        expr b = e;
        constraint_seq cs;
        if (is_explicit(e)) {
            b    = get_explicit_arg(e);
            r    = visit_core(get_explicit_arg(e), cs);
        } else if (is_explicit(get_app_fn(e))) {
            r    = visit_core(e, cs);
        } else {
            if (is_implicit(e)) {
                r = get_implicit_arg(e);
                if (is_explicit(r)) r = get_explicit_arg(r);
                b = r;
                r = visit_core(r, cs);
            } else {
                r = visit_core(e, cs);
            }
            tag  g         = e.get_tag();
            expr r_type    = whnf(infer_type(r, cs), cs);
            expr imp_arg;
            bool is_strict = false;
            while (is_pi(r_type) && binding_info(r_type).is_implicit()) {
                imp_arg = mk_placeholder_meta(some_expr(binding_domain(r_type)), g, is_strict, cs);
                r       = mk_app(r, imp_arg, g);
                r_type  = whnf(instantiate(binding_body(r_type), imp_arg), cs);
            }
        }
        save_type_data(b, r);
        return mk_pair(r, cs);
    }

    expr visit(expr const & e, constraint_seq & cs) {
        auto r = visit(e);
        cs += r.second;
        return r.first;
    }

    lazy_list<substitution> solve(constraint_seq const & cs) {
        buffer<constraint> tmp;
        cs.linearize(tmp);
        return unify(env(), tmp.size(), tmp.data(), m_ngen.mk_child(), unifier_config(ios().get_options(), true));
    }

    static void collect_metavars(expr const & e, buffer<expr> & mvars) {
        for_each(e, [&](expr const & e, unsigned) {
                if (is_metavar(e)) {
                    mvars.push_back(e);
                    return false; /* do not visit its type */
                }
                return has_metavar(e);
            });
    }

    void display_unsolved_proof_state(expr const & mvar, proof_state const & ps, char const * msg) {
        lean_assert(is_metavar(mvar));
        if (!m_displayed_errors.contains(mlocal_name(mvar))) {
            m_displayed_errors.insert(mlocal_name(mvar));
            auto out = regular(env(), ios());
            flycheck_error err(out);
            display_error_pos(out, pip(), mvar);
            out << " unsolved placeholder, " << msg << "\n" << ps << endl;
        }
    }

    // For each occurrence of \c exact_tac in \c pre_tac, display its unassigned metavariables.
    // This is a trick to improve the quality of the error messages.
    void check_exact_tacs(expr const & pre_tac, substitution const & s) {
        for_each(pre_tac, [&](expr const & e, unsigned) {
                expr const & f = get_app_fn(e);
                if (is_constant(f) && const_name(f) == const_name(get_exact_tac_fn())) {
                    display_unassigned_mvars(e, s);
                    return false;
                } else {
                    return true;
                }
            });
    }

    optional<expr> get_pre_tactic_for(substitution & subst, expr const & mvar, name_set & visited) {
        if (auto it = m_local_tactic_hints.find(mlocal_name(mvar))) {
            expr pre_tac = subst.instantiate(*it);
            pre_tac = solve_unassigned_mvars(subst, pre_tac, visited);
            check_exact_tacs(pre_tac, subst);
            return some_expr(pre_tac);
        } else {
            return none_expr();
        }
    }

    optional<tactic> pre_tactic_to_tactic(expr const & pre_tac, expr const & mvar) {
        try {
            return optional<tactic>(expr_to_tactic(env(), pre_tac, pip()));
        } catch (expr_to_tactic_exception & ex) {
            auto out = regular(env(), ios());
            display_error_pos(out, pip(), mvar);
            out << " " << ex.what();
            out << pp_indent_expr(out.get_formatter(), pre_tac) << endl << "failed at:"
                << pp_indent_expr(out.get_formatter(), ex.get_expr()) << endl;
            return optional<tactic>();
        }
    }

    optional<tactic> get_local_tactic_hint(substitution & subst, expr const & mvar, name_set & visited) {
        if (auto pre_tac = get_pre_tactic_for(subst, mvar, visited)) {
            return pre_tactic_to_tactic(*pre_tac, mvar);
        } else {
            return optional<tactic>();
        }
    }

    /** \brief Try to instantiate meta-variable \c mvar (modulo its state ps) using the given tactic.
        If it succeeds, then update subst with the solution.
        Return true iff the metavariable \c mvar has been assigned.
    */
    bool try_using(substitution & subst, expr const & mvar, proof_state const & ps, tactic const & tac) {
        lean_assert(length(ps.get_goals()) == 1);
        // make sure ps is a really a proof state for mvar.
        lean_assert(mlocal_name(get_app_fn(head(ps.get_goals()).get_meta())) == mlocal_name(mvar));
        try {
            proof_state_seq seq = tac(env(), ios(), ps);
            auto r = seq.pull();
            if (!r) {
                // tactic failed to produce any result
                display_unsolved_proof_state(mvar, ps, "tactic failed");
                return false;
            } else if (!empty(r->first.get_goals())) {
                // tactic contains unsolved subgoals
                display_unsolved_proof_state(mvar, r->first, "unsolved subgoals");
                return false;
            } else {
                subst = r->first.get_subst();
                expr v = subst.instantiate(mvar);
                subst.assign(mlocal_name(mvar), v);
                return true;
            }
        } catch (tactic_exception & ex) {
            auto out = regular(env(), ios());
            display_error_pos(out, pip(), ex.get_expr());
            out << " tactic failed: " << ex.what() << "\n";
            return false;
        }
    }

    void solve_unassigned_mvar(substitution & subst, expr mvar, name_set & visited) {
        if (visited.contains(mlocal_name(mvar)))
            return;
        visited.insert(mlocal_name(mvar));
        if (auto local_hint = get_local_tactic_hint(subst, mvar, visited)) {
            auto meta = mvar_to_meta(mvar);
            if (!meta)
                return;
            meta = instantiate_meta(*meta, subst);
            // TODO(Leo): we are discarding constraints here
            expr type = m_tc[m_relax_main_opaque]->infer(*meta).first;
            // first solve unassigned metavariables in type
            type = solve_unassigned_mvars(subst, type, visited);
            proof_state ps(goals(goal(*meta, type)), subst, m_ngen.mk_child());
            try_using(subst, mvar, ps, *local_hint);
        }
    }

    expr solve_unassigned_mvars(substitution & subst, expr e, name_set & visited) {
        e = subst.instantiate(e);
        buffer<expr> mvars;
        collect_metavars(e, mvars);
        if (mvars.empty())
            return e;
        for (auto mvar : mvars) {
            check_interrupted();
            solve_unassigned_mvar(subst, mvar, visited);
        }
        return subst.instantiate(e);
    }

    expr solve_unassigned_mvars(substitution & subst, expr const & e) {
        name_set visited;
        return solve_unassigned_mvars(subst, e, visited);
    }

    void display_unassigned_mvars(expr const & e, substitution const & s) {
        if (check_unassigned() && has_metavar(e)) {
            substitution tmp_s(s);
            for_each(e, [&](expr const & e, unsigned) {
                    if (!is_metavar(e))
                        return has_metavar(e);
                    if (auto it = m_mvar2meta.find(mlocal_name(e))) {
                        expr meta      = tmp_s.instantiate(*it);
                        expr meta_type = tmp_s.instantiate(type_checker(env()).infer(meta).first);
                        goal g(meta, meta_type);
                        display_unsolved_proof_state(e, proof_state(goals(g), substitution(), m_ngen),
                                                     "don't know how to synthesize it");
                    }
                    return false;
                });
        }
    }

    /** \brief Apply substitution and solve remaining metavariables using tactics. */
    expr apply(substitution & s, expr const & e, name_set & univ_params, buffer<name> & new_params) {
        expr r = s.instantiate(e);
        if (has_univ_metavar(r))
            r = univ_metavars_to_params_fn(env(), lls(), s, univ_params, new_params)(r);
        r = solve_unassigned_mvars(s, r);
        display_unassigned_mvars(r, s);
        return r;
    }

    std::tuple<expr, level_param_names> apply(substitution & s, expr const & e) {
        auto ps = collect_univ_params(e);
        buffer<name> new_ps;
        expr r = apply(s, e, ps, new_ps);
        return std::make_tuple(r, to_list(new_ps.begin(), new_ps.end()));
    }

    std::tuple<expr, level_param_names> operator()(expr const & e, bool _ensure_type, bool relax_main_opaque) {
        flet<bool> set_relax(m_relax_main_opaque, relax_main_opaque && !get_hide_main_opaque(env()));
        constraint_seq cs;
        expr r = visit(e, cs);
        if (_ensure_type)
            r = ensure_type(r, cs);
        auto p  = solve(cs).pull();
        lean_assert(p);
        substitution s = p->first;
        auto result = apply(s, r);
        copy_info_to_manager(s);
        return result;
    }

    std::tuple<expr, expr, level_param_names> operator()(expr const & t, expr const & v, name const & n, bool is_opaque) {
        lean_assert(!has_local(t)); lean_assert(!has_local(v));
        constraint_seq t_cs;
        expr r_t      = ensure_type(visit(t, t_cs), t_cs);
        // Opaque definitions in the main module may treat other opaque definitions (in the main module) as transparent.
        flet<bool> set_relax(m_relax_main_opaque, is_opaque && !get_hide_main_opaque(env()));
        constraint_seq v_cs;
        expr r_v      = visit(v, v_cs);
        expr r_v_type = infer_type(r_v, v_cs);
        justification j = mk_justification(r_v, [=](formatter const & fmt, substitution const & subst) {
                substitution s(subst);
                return pp_def_type_mismatch(fmt, n, s.instantiate(r_t), s.instantiate(r_v_type));
            });
        pair<expr, constraint_seq> r_v_cs = ensure_has_type(r_v, r_v_type, r_t, j, is_opaque);
        r_v = r_v_cs.first;
        constraint_seq cs = t_cs + r_v_cs.second + v_cs;
        auto p  = solve(cs).pull();
        lean_assert(p);
        substitution s = p->first;
        name_set univ_params = collect_univ_params(r_v, collect_univ_params(r_t));
        buffer<name> new_params;
        expr new_r_t = apply(s, r_t, univ_params, new_params);
        expr new_r_v = apply(s, r_v, univ_params, new_params);
        copy_info_to_manager(s);
        return std::make_tuple(new_r_t, new_r_v, to_list(new_params.begin(), new_params.end()));
    }
};

static name g_tmp_prefix = name::mk_internal_unique_name();

std::tuple<expr, level_param_names> elaborate(elaborator_context & env, list<expr> const & ctx, expr const & e,
                                              bool relax_main_opaque, bool ensure_type) {
    return elaborator(env, ctx, name_generator(g_tmp_prefix))(e, ensure_type, relax_main_opaque);
}

std::tuple<expr, expr, level_param_names> elaborate(elaborator_context & env, name const & n, expr const & t, expr const & v,
                                                    bool is_opaque) {
    return elaborator(env, list<expr>(), name_generator(g_tmp_prefix))(t, v, n, is_opaque);
}
}
