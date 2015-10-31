/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include "util/sstream.h"
#include "kernel/for_each_fn.h"
#include "kernel/type_checker.h"
#include "library/replace_visitor.h"
#include "library/util.h"
#include "library/reducible.h"
#include "library/normalize.h"
#include "library/class.h"
#include "library/type_inference.h"
#include "library/projection.h"
#include "library/tactic/goal.h"
#include "library/blast/expr.h"
#include "library/blast/state.h"
#include "library/blast/blast.h"
#include "library/blast/blast_exception.h"

namespace lean {
namespace blast {
static name * g_prefix = nullptr;

class blastenv {
    friend class scope_assignment;
    environment                m_env;
    io_state                   m_ios;
    name_generator             m_ngen;
    name_set                   m_lemma_hints;
    name_set                   m_unfold_hints;
    name_map<level>            m_uvar2uref;    // map global universe metavariables to blast uref's
    name_map<pair<expr, expr>> m_mvar2meta_mref; // map global metavariables to blast mref's
    name_predicate             m_not_reducible_pred;
    name_predicate             m_class_pred;
    name_predicate             m_instance_pred;
    name_map<projection_info>  m_projection_info;
    state                      m_curr_state;   // current state

    class ti : public type_inference {
        blastenv &         m_benv;
        std::vector<state> m_stack;
    public:
        ti(blastenv & benv):
            type_inference(benv.m_env, benv.m_ios),
            m_benv(benv) {}

        virtual bool is_extra_opaque(name const & n) const {
            // TODO(Leo): class and instances
            return m_benv.m_not_reducible_pred(n) || m_benv.m_projection_info.contains(n);
        }

        virtual expr mk_tmp_local(expr const & type, binder_info const & bi) {
            name n = m_benv.m_ngen.next();
            return blast::mk_local(n, n, type, bi);
        }

        virtual bool is_tmp_local(expr const & e) const {
            return blast::is_local(e);
        }

        virtual bool is_uvar(level const & l) const {
            return blast::is_uref(l);
        }

        virtual bool is_mvar(expr const & e) const {
            return blast::is_mref(e);
        }

        virtual level const * get_assignment(level const & u) const {
            return m_benv.m_curr_state.get_uref_assignment(u);
        }

        virtual expr const * get_assignment(expr const & m) const {
            return m_benv.m_curr_state.get_mref_assignment(m);
        }

        virtual void update_assignment(level const & u, level const & v) {
            m_benv.m_curr_state.assign_uref(u, v);
        }

        virtual void update_assignment(expr const & m, expr const & v) {
            m_benv.m_curr_state.assign_mref(m, v);
        }

        virtual bool validate_assignment(expr const & m, buffer<expr> const & locals, expr const & v) {
            // We must check
            //   1. All href in new_v are in the context of m.
            //   2. The context of any (unassigned) mref in new_v must be a subset of the context of m.
            //      If it is not we force it to be.
            //   3. Any local constant occurring in new_v occurs in locals
            //   4. m does not occur in new_v
            state & s = m_benv.m_curr_state;
            metavar_decl const * d = s.get_metavar_decl(m);
            lean_assert(d);
            bool ok = true;
            for_each(v, [&](expr const & e, unsigned) {
                    if (!ok)
                        return false; // stop search
                    if (is_href(e)) {
                        if (!d->contains_href(e)) {
                            ok = false; // failed 1
                            return false;
                        }
                    } else if (blast::is_local(e)) {
                        if (std::all_of(locals.begin(), locals.end(), [&](expr const & a) {
                                    return local_index(a) != local_index(e); })) {
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
                branch const & b = m_benv.m_curr_state.get_main_branch();
                hypothesis const * h = b.get(e);
                lean_assert(h);
                return h->get_type();
            } else {
                return mlocal_type(e);
            }
        }

        virtual expr infer_metavar(expr const & m) const {
            state const & s = m_benv.m_curr_state;
            metavar_decl const * d = s.get_metavar_decl(m);
            lean_assert(d);
            return d->get_type();
        }

        virtual level mk_uvar() {
            return m_benv.m_curr_state.mk_uref();
        }

        virtual expr mk_mvar(expr const & type) {
            return m_benv.m_curr_state.mk_metavar(type);
        }

        virtual void push() {
            // TODO(Leo): we only need to save the assignment and metavar_decls.
            m_stack.push_back(m_benv.m_curr_state);
        }

        virtual void pop() {
            m_benv.m_curr_state = m_stack.back();
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
            case level_kind::Succ:    return blast::mk_succ(to_blast_level(succ_of(l)));
            case level_kind::Zero:    return blast::mk_level_zero();
            case level_kind::Param:   return blast::mk_param_univ(param_id(l));
            case level_kind::Global:  return blast::mk_global_univ(global_id(l));
            case level_kind::Max:
                lhs = to_blast_level(max_lhs(l));
                return blast::mk_max(lhs, to_blast_level(max_rhs(l)));
            case level_kind::IMax:
                lhs = to_blast_level(imax_lhs(l));
                return blast::mk_imax(lhs, to_blast_level(imax_rhs(l)));
            case level_kind::Meta:
                if (auto r = m_uvar2uref.find(meta_id(l))) {
                    return *r;
                } else {
                    level uref = m_state.mk_uref();
                    m_uvar2uref.insert(meta_id(l), uref);
                    return uref;
                }
            }
            lean_unreachable();
        }

        virtual expr visit_sort(expr const & e) {
            return blast::mk_sort(to_blast_level(sort_level(e)));
        }

        virtual expr visit_macro(expr const & e) {
            buffer<expr> new_args;
            for (unsigned i = 0; i < macro_num_args(e); i++) {
                new_args.push_back(visit(macro_arg(e, i)));
            }
            return blast::mk_macro(macro_def(e), new_args.size(), new_args.data());
        }

        virtual expr visit_constant(expr const & e) {
            levels new_ls = map(const_levels(e), [&](level const & l) { return to_blast_level(l); });
            return blast::mk_constant(const_name(e), new_ls);
        }

        virtual expr visit_var(expr const & e) {
            return blast::mk_var(var_idx(e));
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
            return blast::mk_app(mref, new_args.size(), new_args.data());
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
                return blast::mk_app(f, visit(app_arg(e)));
            }
        }

        virtual expr visit_lambda(expr const & e) {
            expr d = visit(binding_domain(e));
            return blast::mk_lambda(binding_name(e), d, visit(binding_body(e)), binding_info(e));
        }

        virtual expr visit_pi(expr const & e) {
            expr d = visit(binding_domain(e));
            return blast::mk_pi(binding_name(e), d, visit(binding_body(e)), binding_info(e));
        }

    public:
        to_blast_expr_fn(environment const & env, state & s,
                         name_map<level> & uvar2uref, name_map<pair<expr, expr>> & mvar2meta_mref,
                         name_map<expr> & local2href):
            m_tc(env), m_state(s), m_uvar2uref(uvar2uref), m_mvar2meta_mref(mvar2meta_mref), m_local2href(local2href) {}
    };

    state to_state(goal const & g) {
        state s;
        type_checker_ptr norm_tc = mk_type_checker(m_env, name_generator(*g_prefix), UnfoldReducible);
        name_map<expr>             local2href;
        to_blast_expr_fn to_blast_expr(m_env, s, m_uvar2uref, m_mvar2meta_mref, local2href);
        buffer<expr> hs;
        g.get_hyps(hs);
        for (expr const & h : hs) {
            lean_assert(is_local(h));
            expr type     = normalize(*norm_tc, mlocal_type(h));
            expr new_type = to_blast_expr(type);
            expr href     = s.add_hypothesis(local_pp_name(h), new_type, h);
            local2href.insert(mlocal_name(h), href);
        }
        expr target     = normalize(*norm_tc, g.get_type());
        expr new_target = to_blast_expr(target);
        s.set_target(new_target);
        lean_assert(s.check_invariant());
        return s;
    }

    ti m_ti;

public:
    blastenv(environment const & env, io_state const & ios, list<name> const & ls, list<name> const & ds):
        m_env(env), m_ios(ios), m_ngen(*g_prefix), m_lemma_hints(to_name_set(ls)), m_unfold_hints(to_name_set(ds)),
        m_not_reducible_pred(mk_not_reducible_pred(env)),
        m_class_pred(mk_class_pred(env)),
        m_instance_pred(mk_instance_pred(env)),
        m_ti(*this) {
    }

    void init_state(goal const & g) {
        m_curr_state = to_state(g);

        // TODO(Leo): set local context for type class resolution at ti
    }

    optional<expr> operator()(goal const & g) {
        init_state(g);

        // TODO(Leo): blast main loop
        display("Blast tactic initial state\n");
        display_curr_state();

        return none_expr();
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

    name mk_fresh_local_name() { return m_ngen.next(); }
    expr mk_fresh_local(expr const & type, binder_info const & bi) {
        name n = m_ngen.next();
        return blast::mk_local(n, n, type, bi);
    }
    expr whnf(expr const & e) { return m_ti.whnf(e); }
    expr infer_type(expr const & e) { return m_ti.infer(e); }
    bool is_prop(expr const & e) { return m_ti.is_prop(e); }
    bool is_def_eq(expr const & e1, expr const & e2) { return m_ti.is_def_eq(e1, e2); }
    optional<expr> mk_class_instance(expr const & e) { return m_ti.mk_class_instance(e); }
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

expr whnf(expr const & e) {
    lean_assert(g_blastenv);
    return g_blastenv->whnf(e);
}

expr infer_type(expr const & e) {
    lean_assert(g_blastenv);
    return g_blastenv->infer_type(e);
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

name mk_fresh_local_name() {
    lean_assert(g_blastenv);
    return g_blastenv->mk_fresh_local_name();
}

expr mk_fresh_local(expr const & type, binder_info const & bi) {
    lean_assert(g_blastenv);
    return g_blastenv->mk_fresh_local(type, bi);
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
    g_blastenv->m_ti.push();
}

scope_assignment::~scope_assignment() {
    if (m_keep)
        g_blastenv->m_ti.commit();
    else
        g_blastenv->m_ti.pop();
}

void scope_assignment::commit() {
    m_keep = true;
}

struct scope_debug::imp {
    scope_hash_consing m_scope1;
    blastenv           m_benv;
    scope_blastenv     m_scope2;
    imp(environment const & env, io_state const & ios):
        m_benv(env, ios, list<name>(), list<name>()),
        m_scope2(m_benv) {
        expr aux_mvar = mk_metavar("dummy_mvar", mk_true());
        goal aux_g(aux_mvar, mlocal_type(aux_mvar));
        m_benv.init_state(aux_g);
    }
};

scope_debug::scope_debug(environment const & env, io_state const & ios):
    m_imp(new imp(env, ios)) {
}

scope_debug::~scope_debug() {}
}
optional<expr> blast_goal(environment const & env, io_state const & ios, list<name> const & ls, list<name> const & ds,
                          goal const & g) {
    blast::scope_hash_consing scope1;
    blast::blastenv b(env, ios, ls, ds);
    blast::scope_blastenv    scope2(b);
    return b(g);
}
void initialize_blast() {
    blast::g_prefix = new name(name::mk_internal_unique_name());
}
void finalize_blast() {
    delete blast::g_prefix;
}
}
