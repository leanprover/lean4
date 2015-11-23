/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include "util/sstream.h"
#include "kernel/for_each_fn.h"
#include "kernel/find_fn.h"
#include "kernel/type_checker.h"
#include "library/replace_visitor.h"
#include "library/util.h"
#include "library/reducible.h"
#include "library/class.h"
#include "library/type_context.h"
#include "library/relation_manager.h"
#include "library/congr_lemma_manager.h"
#include "library/abstract_expr_manager.h"
#include "library/projection.h"
#include "library/tactic/goal.h"
#include "library/blast/expr.h"
#include "library/blast/state.h"
#include "library/blast/blast.h"
#include "library/blast/proof_expr.h"
#include "library/blast/blast_exception.h"
#include "library/blast/simple_strategy.h"
#include "library/blast/choice_point.h"
#include "library/blast/congruence_closure.h"
#include "library/blast/trace.h"
#include "library/blast/options.h"

namespace lean {
namespace blast {
static name * g_prefix     = nullptr;
static name * g_tmp_prefix = nullptr;

class blastenv {
    friend class scope_assignment;
    typedef std::vector<tmp_type_context *> tmp_type_context_pool;
    typedef std::unique_ptr<tmp_type_context> tmp_type_context_ptr;

    environment                m_env;
    io_state                   m_ios;
    name_generator             m_ngen;
    tmp_local_generator        m_tmp_local_generator;
    list<expr>                 m_initial_context; // for setting type_context local instances
    name_set                   m_lemma_hints;
    name_set                   m_unfold_hints;
    name_map<level>            m_uvar2uref;    // map global universe metavariables to blast uref's
    name_map<pair<expr, expr>> m_mvar2meta_mref; // map global metavariables to blast mref's
    name_predicate             m_not_reducible_pred;
    name_predicate             m_class_pred;
    name_predicate             m_instance_pred;
    name_map<projection_info>  m_projection_info;
    is_relation_pred           m_is_relation_pred;
    state                      m_curr_state;   // current state
    tmp_type_context_pool      m_tmp_ctx_pool;
    tmp_type_context_ptr       m_tmp_ctx; // for app_builder and congr_lemma_manager
    app_builder                m_app_builder;
    fun_info_manager           m_fun_info_manager;
    congr_lemma_manager        m_congr_lemma_manager;
    abstract_expr_manager      m_abstract_expr_manager;
    relation_info_getter       m_rel_getter;
    refl_info_getter           m_refl_getter;
    symm_info_getter           m_symm_getter;

    class tctx : public type_context {
        blastenv &                              m_benv;
        std::vector<state::assignment_snapshot> m_stack;
    public:
        tctx(blastenv & benv):
            type_context(benv.m_env, benv.m_ios, benv.m_tmp_local_generator),
            m_benv(benv) {}

        virtual bool is_extra_opaque(name const & n) const {
            // TODO(Leo): class and instances
            return m_benv.m_not_reducible_pred(n) || m_benv.m_projection_info.contains(n);
        }

        virtual bool is_uvar(level const & l) const {
            return blast::is_uref(l);
        }

        virtual bool is_mvar(expr const & e) const {
            return blast::is_mref(e);
        }

        virtual optional<level> get_assignment(level const & u) const {
            if (auto v = m_benv.m_curr_state.get_uref_assignment(u))
                return some_level(*v);
            else
                return none_level();
        }

        virtual optional<expr> get_assignment(expr const & m) const {
            if (auto v = m_benv.m_curr_state.get_mref_assignment(m))
                return some_expr(*v);
            else
                return none_expr();
        }

        virtual void update_assignment(level const & u, level const & v) {
            m_benv.m_curr_state.assign_uref(u, v);
        }

        virtual void update_assignment(expr const & m, expr const & v) {
            m_benv.m_curr_state.assign_mref(m, v);
        }

        bool check_href_core(metavar_decl const & d, expr const & h, hypothesis_idx_set & visited) {
            lean_assert(is_href(h));
            lean_assert(!d.contains_href(h));
            if (visited.contains(href_index(h)))
                return true;
            visited.insert(href_index(h));
            state & s = m_benv.m_curr_state;
            hypothesis const & h_decl = s.get_hypothesis_decl(h);
            if (h_decl.is_assumption())
                return false;
            return !find(*h_decl.get_value(), [&](expr const & e, unsigned) {
                    return is_href(e) && !d.contains_href(e) && !check_href_core(d, e, visited);
                });
        }

        bool check_href(metavar_decl const & d, expr const & h) {
            lean_assert(is_href(h));
            if (d.contains_href(h))
                return true;
            hypothesis_idx_set visited;
            return check_href_core(d, h, visited);
        }

        virtual bool validate_assignment(expr const & m, buffer<expr> const & locals, expr const & v) {
            // We must check
            //   1. All href in new_v are in the context of m.
            //   2. The context of any (unassigned) mref in new_v must be a subset of the context of m.
            //      If it is not we force it to be.
            //   3. Any (non tmp) local constant occurring in new_v occurs in locals
            //   4. m does not occur in new_v
            state & s = m_benv.m_curr_state;
            metavar_decl const * d = s.get_metavar_decl(m);
            lean_assert(d);
            bool ok = true;
            for_each(v, [&](expr const & e, unsigned) {
                    if (!ok)
                        return false; // stop search
                    if (is_href(e)) {
                        if (!check_href(*d, e)) {
                            ok = false; // failed 1
                            return false;
                        }
                    } else if (is_local(e) && !is_tmp_local(e)) {
                        if (std::all_of(locals.begin(), locals.end(), [&](expr const & a) {
                                    return mlocal_name(a) != mlocal_name(e); })) {
                            ok = false; // failed 3
                            return false;
                        }
                    } else if (is_mref(e)) {
                        if (m == e) {
                            ok = false; // failed 4
                            return false;
                        }
                        s.restrict_mref_context_using(e, m); // enforce 2
                        return false;
                    }
                    return true;
                });
            return ok;
        }

        /** \brief Return the type of a local constant (local or not).
            \remark This method allows the customer to store the type of local constants
            in a different place. */
        virtual expr infer_local(expr const & e) const {
            if (is_href(e)) {
                state const & s = m_benv.m_curr_state;
                hypothesis const & h = s.get_hypothesis_decl(e);
                return h.get_type();
            } else {
                return mlocal_type(e);
            }
        }

        virtual expr infer_metavar(expr const & m) const {
            // Remark: we do not tolerate external meta-variables here.
            lean_assert(is_mref(m));
            state const & s = m_benv.m_curr_state;
            metavar_decl const * d = s.get_metavar_decl(m);
            lean_assert(d);
            return d->get_type();
        }

        virtual level mk_uvar() {
            return mk_fresh_uref();
        }

        virtual expr mk_mvar(expr const & type) {
            return m_benv.m_curr_state.mk_metavar(type);
        }

        virtual void push() {
            m_stack.push_back(m_benv.m_curr_state.save_assignment());
        }

        virtual void pop() {
            m_benv.m_curr_state.restore_assignment(m_stack.back());
            m_stack.pop_back();
        }

        virtual void commit() {
            m_stack.pop_back();
        }
    };

    class to_blast_expr_fn : public replace_visitor {
        type_checker                 m_tc;
        state &                      m_state;
        // We map each metavariable to a metavariable application and the mref associated with it.
        name_map<level> &            m_uvar2uref;
        name_map<pair<expr, expr>> & m_mvar2meta_mref;
        name_map<expr> &             m_local2href;

        level to_blast_level(level const & l) {
            level lhs;
            switch (l.kind()) {
            case level_kind::Succ:    return mk_succ(to_blast_level(succ_of(l)));
            case level_kind::Zero:    return mk_level_zero();
            case level_kind::Param:   return mk_param_univ(param_id(l));
            case level_kind::Global:  return mk_global_univ(global_id(l));
            case level_kind::Max:
                lhs = to_blast_level(max_lhs(l));
                return mk_max(lhs, to_blast_level(max_rhs(l)));
            case level_kind::IMax:
                lhs = to_blast_level(imax_lhs(l));
                return mk_imax(lhs, to_blast_level(imax_rhs(l)));
            case level_kind::Meta:
                if (auto r = m_uvar2uref.find(meta_id(l))) {
                    return *r;
                } else {
                    level uref = mk_fresh_uref();
                    m_uvar2uref.insert(meta_id(l), uref);
                    return uref;
                }
            }
            lean_unreachable();
        }

        virtual expr visit_sort(expr const & e) {
            return mk_sort(to_blast_level(sort_level(e)));
        }

        virtual expr visit_macro(expr const & e) {
            buffer<expr> new_args;
            for (unsigned i = 0; i < macro_num_args(e); i++) {
                new_args.push_back(visit(macro_arg(e, i)));
            }
            return mk_macro(macro_def(e), new_args.size(), new_args.data());
        }

        virtual expr visit_constant(expr const & e) {
            levels new_ls = map(const_levels(e), [&](level const & l) { return to_blast_level(l); });
            return mk_constant(const_name(e), new_ls);
        }

        virtual expr visit_var(expr const & e) {
            return mk_var(var_idx(e));
        }

        void throw_unsupported_metavar_occ(expr const & e) {
            // TODO(Leo): improve error message
            throw blast_exception("'blast' tactic failed, goal contains a "
                                  "meta-variable application that is not supported", e);
        }

        expr mk_mref_app(expr const & mref, unsigned nargs, expr const * args) {
            lean_assert(is_mref(mref));
            buffer<expr> new_args;
            for (unsigned i = 0; i < nargs; i++) {
                new_args.push_back(visit(args[i]));
            }
            return mk_app(mref, new_args.size(), new_args.data());
        }

        expr visit_meta_app(expr const & e) {
            lean_assert(is_meta(e));
            buffer<expr> args;
            expr const & mvar = get_app_args(e, args);
            if (pair<expr, expr> const * meta_mref = m_mvar2meta_mref.find(mlocal_name(mvar))) {
                lean_assert(is_meta(meta_mref->first));
                lean_assert(is_mref(meta_mref->second));
                buffer<expr> decl_args;
                get_app_args(meta_mref->first, decl_args);
                if (decl_args.size() > args.size())
                    throw_unsupported_metavar_occ(e);
                // Make sure the the current metavariable application prefix matches the one
                // found before.
                for (unsigned i = 0; i < decl_args.size(); i++) {
                    if (is_local(decl_args[i])) {
                        if (!is_local(args[i]) || mlocal_name(args[i]) != mlocal_name(decl_args[i]))
                            throw_unsupported_metavar_occ(e);
                    } else if (decl_args[i] != args[i]) {
                        throw_unsupported_metavar_occ(e);
                    }
                }
                return mk_mref_app(meta_mref->second, args.size() - decl_args.size(), args.data() + decl_args.size());
            } else {
                unsigned i = 0;
                hypothesis_idx_buffer ctx;
                // Find prefix that contains only closed terms.
                for (; i < args.size(); i++) {
                    if (!closed(args[i]))
                        break;
                    if (!is_local(args[i])) {
                        // Ignore arguments that are not local constants.
                        // In the blast tactic we only support higher-order patterns.
                        continue;
                    }
                    expr const & l = args[i];
                    if (!std::all_of(args.begin(), args.begin() + i,
                                     [&](expr const & prev) { return mlocal_name(prev) != mlocal_name(l); })) {
                        // Local has already been processed
                        continue;
                    }
                    auto href = m_local2href.find(mlocal_name(l));
                    if (!href) {
                        // One of the arguments is a local constant that is not in m_local2href
                        throw_unsupported_metavar_occ(e);
                    }
                    ctx.push_back(href_index(*href));
                }
                unsigned  prefix_sz = i;
                expr aux  = e;
                for (; i < args.size(); i++)
                    aux = app_fn(aux);
                lean_assert(is_meta(aux));
                expr type = visit(m_tc.infer(aux).first);
                expr mref = m_state.mk_metavar(ctx, type);
                m_mvar2meta_mref.insert(mlocal_name(mvar), mk_pair(e, mref));
                return mk_mref_app(mref, args.size() - prefix_sz, args.data() + prefix_sz);
            }
        }

        virtual expr visit_meta(expr const & e) {
            return visit_meta_app(e);
        }

        virtual expr visit_local(expr const & e) {
            if (auto r = m_local2href.find(mlocal_name(e)))
                return * r;
            else
                throw blast_exception("blast tactic failed, ill-formed input goal", e);
        }

        virtual expr visit_app(expr const & e) {
            if (is_meta(e)) {
                return visit_meta_app(e);
            } else {
                expr f = visit(app_fn(e));
                return mk_app(f, visit(app_arg(e)));
            }
        }

        virtual expr visit_lambda(expr const & e) {
            expr d = visit(binding_domain(e));
            return mk_lambda(binding_name(e), d, visit(binding_body(e)), binding_info(e));
        }

        virtual expr visit_pi(expr const & e) {
            expr d = visit(binding_domain(e));
            return mk_pi(binding_name(e), d, visit(binding_body(e)), binding_info(e));
        }

    public:
        to_blast_expr_fn(environment const & env, state & s,
                         name_map<level> & uvar2uref, name_map<pair<expr, expr>> & mvar2meta_mref,
                         name_map<expr> & local2href):
            m_tc(env), m_state(s), m_uvar2uref(uvar2uref), m_mvar2meta_mref(mvar2meta_mref), m_local2href(local2href) {}
    };

    void init_curr_state(goal const & g) {
        state & s = curr_state();
        name_map<expr>             local2href;
        to_blast_expr_fn to_blast_expr(m_env, s, m_uvar2uref, m_mvar2meta_mref, local2href);
        buffer<expr> hs;
        g.get_hyps(hs);
        for (expr const & h : hs) {
            lean_assert(is_local(h));
            expr new_type = normalize(to_blast_expr(mlocal_type(h)));
            expr href     = s.mk_hypothesis(local_pp_name(h), new_type, h);
            local2href.insert(mlocal_name(h), href);
        }
        expr new_target = normalize(to_blast_expr(g.get_type()));
        s.set_target(new_target);
        lean_assert(s.check_invariant());
    }

    tctx                       m_tctx;
    normalizer                 m_normalizer;
    expr_map<expr>             m_norm_cache; // normalization cache

    void save_initial_context() {
        hypothesis_idx_buffer hidxs;
        m_curr_state.get_sorted_hypotheses(hidxs);
        buffer<expr> ctx;
        for (unsigned hidx : hidxs) {
            ctx.push_back(mk_href(hidx));
        }
        m_initial_context = to_list(ctx);
    }


    expr to_tactic_proof(expr const & pr) {
        // When a proof is found we must
        // 1- Remove all occurrences of href's from pr
        expr pr1 = unfold_hypotheses_ge(m_curr_state, pr, 0);
        // 2- Replace mrefs with their assignments,
        //    and convert unassigned meta-variables back into
        //    tactic meta-variables.
        expr pr2 = m_curr_state.instantiate_urefs_mrefs(pr1);
        // TODO(Leo):
        // 3- The external tactic meta-variables that have been instantiated
        //    by blast must also be communicated back to the tactic framework.
        return pr2;
    }

public:
    blastenv(environment const & env, io_state const & ios, list<name> const & ls, list<name> const & ds):
        m_env(env), m_ios(ios), m_ngen(*g_prefix), m_lemma_hints(to_name_set(ls)), m_unfold_hints(to_name_set(ds)),
        m_not_reducible_pred(mk_not_reducible_pred(env)),
        m_class_pred(mk_class_pred(env)),
        m_instance_pred(mk_instance_pred(env)),
        m_is_relation_pred(mk_is_relation_pred(env)),
        m_tmp_ctx(mk_tmp_type_context()),
        m_app_builder(*m_tmp_ctx),
        m_fun_info_manager(*m_tmp_ctx),
        m_congr_lemma_manager(m_app_builder, m_fun_info_manager),
        m_abstract_expr_manager(m_fun_info_manager),
        m_rel_getter(mk_relation_info_getter(env)),
        m_refl_getter(mk_refl_info_getter(env)),
        m_symm_getter(mk_symm_info_getter(env)),
        m_tctx(*this),
        m_normalizer(m_tctx) {
        init_uref_mref_href_idxs();
        clear_choice_points();
    }

    ~blastenv() {
        for (auto ctx : m_tmp_ctx_pool)
            delete ctx;
    }

    void init_state(goal const & g) {
        init_curr_state(g);
        save_initial_context();
        m_tctx.set_local_instances(m_initial_context);
        m_tmp_ctx->set_local_instances(m_initial_context);
    }

    optional<expr> operator()(goal const & g) {
        init_state(g);
        if (auto r = apply_simple_strategy()) {
            return some_expr(to_tactic_proof(*r));
        } else {
            return none_expr();
        }
    }

    environment const & get_env() const { return m_env; }

    io_state const & get_ios() const { return m_ios; }

    state & get_curr_state() { return m_curr_state; }

    bool is_reducible(name const & n) const {
        if (m_not_reducible_pred(n))
            return false;
        return !m_projection_info.contains(n);
    }

    projection_info const * get_projection_info(name const & n) const {
        return m_projection_info.find(n);
    }

    expr mk_fresh_local(expr const & type, binder_info const & bi) {
        return m_tmp_local_generator.mk_tmp_local(type, bi);
    }
    bool is_fresh_local(expr const & e) const {
        return m_tmp_local_generator.is_tmp_local(e);
    }
    expr whnf(expr const & e) { return m_tctx.whnf(e); }
    expr relaxed_whnf(expr const & e) { return m_tctx.relaxed_whnf(e); }
    expr infer_type(expr const & e) { return m_tctx.infer(e); }
    bool is_prop(expr const & e) { return m_tctx.is_prop(e); }
    bool is_def_eq(expr const & e1, expr const & e2) { return m_tctx.is_def_eq(e1, e2); }
    optional<expr> mk_class_instance(expr const & e) { return m_tctx.mk_class_instance(e); }

    tmp_type_context * mk_tmp_type_context();

    void recycle_tmp_type_context(tmp_type_context * ctx) {
        lean_assert(ctx);
        ctx->clear();
        m_tmp_ctx_pool.push_back(ctx);
    }

    optional<congr_lemma> mk_congr_lemma_for_simp(expr const & fn, unsigned num_args) {
        return m_congr_lemma_manager.mk_congr_simp(fn, num_args);
    }

    optional<congr_lemma> mk_congr_lemma_for_simp(expr const & fn) {
        return m_congr_lemma_manager.mk_congr_simp(fn);
    }

    optional<congr_lemma> mk_congr_lemma(expr const & fn, unsigned num_args) {
        return m_congr_lemma_manager.mk_congr(fn, num_args);
    }

    optional<congr_lemma> mk_congr_lemma(expr const & fn) {
        return m_congr_lemma_manager.mk_congr(fn);
    }

    optional<congr_lemma> mk_rel_iff_congr(expr const & fn) {
        return m_congr_lemma_manager.mk_rel_iff_congr(fn);
    }

    optional<congr_lemma> mk_rel_eq_congr(expr const & fn) {
        return m_congr_lemma_manager.mk_rel_eq_congr(fn);
    }

    fun_info get_fun_info(expr const & fn) {
        return m_fun_info_manager.get(fn);
    }

    fun_info get_fun_info(expr const & fn, unsigned nargs) {
        return m_fun_info_manager.get(fn, nargs);
    }

    unsigned abstract_hash(expr const & e) {
        return m_abstract_expr_manager.hash(e);
    }

    bool abstract_is_equal(expr const & e1, expr const & e2) {
        return m_abstract_expr_manager.is_equal(e1, e2);
    }

    /** \brief Convert an external expression into a blast expression
        It converts meta-variables to blast meta-variables, and ensures the expressions
        are maximally shared.
        \remark This procedure should only be used for debugging purposes. */
    expr internalize(expr const & e) {
        name_map<expr> local2href;
        return to_blast_expr_fn(m_env, m_curr_state, m_uvar2uref, m_mvar2meta_mref, local2href)(e);
    }

    app_builder & get_app_builder() {
        return m_app_builder;
    }

    type_context & get_type_context() {
        return m_tctx;
    }

    expr normalize(expr const & e) {
        auto it = m_norm_cache.find(e);
        if (it != m_norm_cache.end())
            return it->second;
        expr r = m_normalizer(e);
        m_norm_cache.insert(mk_pair(e, r));
        return r;
    }

    bool is_relation_app(expr const & e, name & rop, expr & lhs, expr & rhs) {
        return m_is_relation_pred(e, rop, lhs, rhs);
    }

    bool is_reflexive(name const & rop) const {
        return static_cast<bool>(m_refl_getter(rop));
    }

    bool is_symmetric(name const & rop) const {
        return static_cast<bool>(m_symm_getter(rop));
    }

    optional<relation_info> get_relation_info(name const & rop) const {
        return m_rel_getter(rop);
    }
};

LEAN_THREAD_PTR(blastenv, g_blastenv);
struct scope_blastenv {
    blastenv * m_prev_blastenv;
public:
    scope_blastenv(blastenv & c):m_prev_blastenv(g_blastenv) { g_blastenv = &c; }
    ~scope_blastenv() { g_blastenv = m_prev_blastenv; }
};

environment const & env() {
    lean_assert(g_blastenv);
    return g_blastenv->get_env();
}

io_state const & ios() {
    lean_assert(g_blastenv);
    return g_blastenv->get_ios();
}

type_context & get_type_context() {
    lean_assert(g_blastenv);
    return g_blastenv->get_type_context();
}

app_builder & get_app_builder() {
    lean_assert(g_blastenv);
    return g_blastenv->get_app_builder();
}

state & curr_state() {
    lean_assert(g_blastenv);
    return g_blastenv->get_curr_state();
}

bool is_reducible(name const & n) {
    lean_assert(g_blastenv);
    return g_blastenv->is_reducible(n);
}

projection_info const * get_projection_info(name const & n) {
    lean_assert(g_blastenv);
    return g_blastenv->get_projection_info(n);
}

bool is_relation_app(expr const & e, name & rop, expr & lhs, expr & rhs) {
    lean_assert(g_blastenv);
    return g_blastenv->is_relation_app(e, rop, lhs, rhs);
}

bool is_relation_app(expr const & e) {
    name rop; expr lhs, rhs;
    return is_relation_app(e, rop, lhs, rhs);
}

bool is_reflexive(name const & rop) {
    lean_assert(g_blastenv);
    return g_blastenv->is_reflexive(rop);
}

bool is_symmetric(name const & rop) {
    lean_assert(g_blastenv);
    return g_blastenv->is_symmetric(rop);
}

optional<relation_info> get_relation_info(name const & rop) {
    lean_assert(g_blastenv);
    return g_blastenv->get_relation_info(rop);
}

expr whnf(expr const & e) {
    lean_assert(g_blastenv);
    return g_blastenv->whnf(e);
}

expr relaxed_whnf(expr const & e) {
    lean_assert(g_blastenv);
    return g_blastenv->relaxed_whnf(e);
}

expr infer_type(expr const & e) {
    lean_assert(g_blastenv);
    return g_blastenv->infer_type(e);
}

expr normalize(expr const & e) {
    lean_assert(g_blastenv);
    return g_blastenv->normalize(e);
}

bool is_prop(expr const & e) {
    lean_assert(g_blastenv);
    return g_blastenv->is_prop(e);
}

bool is_def_eq(expr const & e1, expr const & e2) {
    lean_assert(g_blastenv);
    return g_blastenv->is_def_eq(e1, e2);
}

optional<expr> mk_class_instance(expr const & e) {
    lean_assert(g_blastenv);
    return g_blastenv->mk_class_instance(e);
}

expr mk_fresh_local(expr const & type, binder_info const & bi) {
    lean_assert(g_blastenv);
    return g_blastenv->mk_fresh_local(type, bi);
}

bool is_fresh_local(expr const & e) {
    lean_assert(g_blastenv);
    return g_blastenv->is_fresh_local(e);
}

optional<congr_lemma> mk_congr_lemma_for_simp(expr const & fn, unsigned num_args) {
    lean_assert(g_blastenv);
    return g_blastenv->mk_congr_lemma_for_simp(fn, num_args);
}

optional<congr_lemma> mk_congr_lemma_for_simp(expr const & fn) {
    lean_assert(g_blastenv);
    return g_blastenv->mk_congr_lemma_for_simp(fn);
}

optional<congr_lemma> mk_congr_lemma(expr const & fn, unsigned num_args) {
    lean_assert(g_blastenv);
    return g_blastenv->mk_congr_lemma(fn, num_args);
}

optional<congr_lemma> mk_congr_lemma(expr const & fn) {
    lean_assert(g_blastenv);
    return g_blastenv->mk_congr_lemma(fn);
}

optional<congr_lemma> mk_rel_iff_congr(expr const & fn) {
    lean_assert(g_blastenv);
    return g_blastenv->mk_rel_iff_congr(fn);
}

optional<congr_lemma> mk_rel_eq_congr(expr const & fn) {
    lean_assert(g_blastenv);
    return g_blastenv->mk_rel_eq_congr(fn);
}

fun_info get_fun_info(expr const & fn) {
    lean_assert(g_blastenv);
    return g_blastenv->get_fun_info(fn);
}

fun_info get_fun_info(expr const & fn, unsigned nargs) {
    lean_assert(g_blastenv);
    return g_blastenv->get_fun_info(fn, nargs);
}

unsigned abstract_hash(expr const & e) {
    lean_assert(g_blastenv);
    return g_blastenv->abstract_hash(e);
}

bool abstract_is_equal(expr const & e1, expr const & e2) {
    lean_assert(g_blastenv);
    return g_blastenv->abstract_is_equal(e1, e2);
}

void display_curr_state() {
    curr_state().display(env(), ios());
    display("\n");
}

void display_expr(expr const & e) {
    ios().get_diagnostic_channel() << e << "\n";
}

void display(char const * msg) {
    ios().get_diagnostic_channel() << msg;
}

void display(sstream const & msg) {
    ios().get_diagnostic_channel() << msg.str();
}

scope_assignment::scope_assignment():m_keep(false) {
    lean_assert(g_blastenv);
    g_blastenv->m_tctx.push();
}

scope_assignment::~scope_assignment() {
    if (m_keep)
        g_blastenv->m_tctx.commit();
    else
        g_blastenv->m_tctx.pop();
}

void scope_assignment::commit() {
    m_keep = true;
}

struct scope_debug::imp {
    scoped_expr_caching      m_scope1;
    blastenv                 m_benv;
    scope_blastenv           m_scope2;
    scope_congruence_closure m_scope3;
    scope_config             m_scope4;
    scope_trace              m_scope5;
    imp(environment const & env, io_state const & ios):
        m_scope1(true),
        m_benv(env, ios, list<name>(), list<name>()),
        m_scope2(m_benv),
        m_scope4(ios.get_options()) {
        expr aux_mvar = mk_metavar("dummy_mvar", mk_true());
        goal aux_g(aux_mvar, mlocal_type(aux_mvar));
        m_benv.init_state(aux_g);
    }
};

scope_debug::scope_debug(environment const & env, io_state const & ios):
    m_imp(new imp(env, ios)) {
}

scope_debug::~scope_debug() {}

/** \brief We need to redefine infer_local and infer_metavar, because the types of hypotheses
    and blast meta-variables are stored in the blast state */
class tmp_tctx : public tmp_type_context {
public:
    tmp_tctx(environment const & env, io_state const & ios, tmp_local_generator & gen):
        tmp_type_context(env, ios, gen) {}

    /** \brief Return the type of a local constant (local or not).
        \remark This method allows the customer to store the type of local constants
        in a different place. */
    virtual expr infer_local(expr const & e) const {
        state const & s = curr_state();
        if (is_href(e)) {
            hypothesis const & h = s.get_hypothesis_decl(e);
            return h.get_type();
        } else {
            return mlocal_type(e);
        }
    }

    virtual expr infer_metavar(expr const & m) const {
        if (is_mref(m)) {
            state const & s = curr_state();
            metavar_decl const * d = s.get_metavar_decl(m);
            lean_assert(d);
            return d->get_type();
        } else {
            // The type of external meta-variables is encoded in the usual way.
            // In temporary type_context objects, we may have temporary meta-variables
            // created by external modules (e.g., simplifier and app_builder).
            return mlocal_type(m);
        }
    }
};

tmp_type_context * blastenv::mk_tmp_type_context() {
    tmp_type_context * r;
    if (m_tmp_ctx_pool.empty()) {
        r = new tmp_tctx(m_env, m_ios, m_tmp_local_generator);
        // Design decision: in the blast tactic, we only consider the instances that were
        // available in initial goal provided to the blast tactic.
        // So, we only need to setup the local instances when we create a new (temporary) type context.
        // This is important since whenever we set the local instances the cache in at type context is
        // invalidated.
        r->set_local_instances(m_initial_context);
    } else {
        r = m_tmp_ctx_pool.back();
        m_tmp_ctx_pool.pop_back();
    }
    return r;
}

blast_tmp_type_context::blast_tmp_type_context(unsigned num_umeta, unsigned num_emeta) {
    lean_assert(g_blastenv);
    m_ctx = g_blastenv->mk_tmp_type_context();
    m_ctx->clear();
    m_ctx->set_next_uvar_idx(num_umeta);
    m_ctx->set_next_mvar_idx(num_emeta);
}

blast_tmp_type_context::blast_tmp_type_context() {
    lean_assert(g_blastenv);
    m_ctx = g_blastenv->mk_tmp_type_context();
}

blast_tmp_type_context::~blast_tmp_type_context() {
    g_blastenv->recycle_tmp_type_context(m_ctx);
}

expr internalize(expr const & e) {
    lean_assert(g_blastenv);
    return g_blastenv->internalize(e);
}
}
optional<expr> blast_goal(environment const & env, io_state const & ios, list<name> const & ls, list<name> const & ds,
                          goal const & g) {
    scoped_expr_caching             scope1(true);
    blast::blastenv                 b(env, ios, ls, ds);
    blast::scope_blastenv           scope2(b);
    blast::scope_congruence_closure scope3;
    blast::scope_config             scope4(ios.get_options());
    blast::scope_trace              scope5;
    return b(g);
}
void initialize_blast() {
    blast::g_prefix           = new name(name::mk_internal_unique_name());
    blast::g_tmp_prefix       = new name(name::mk_internal_unique_name());
}
void finalize_blast() {
    delete blast::g_prefix;
    delete blast::g_tmp_prefix;
}
}
