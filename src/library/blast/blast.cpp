/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/for_each_fn.h"
#include "kernel/type_checker.h"
#include "library/replace_visitor.h"
#include "library/util.h"
#include "library/reducible.h"
#include "library/normalize.h"
#include "library/projection.h"
#include "library/blast/expr.h"
#include "library/blast/state.h"
#include "library/blast/infer_type.h"
#include "library/blast/blast.h"
#include "library/blast/blast_context.h"
#include "library/blast/blast_exception.h"

namespace lean {
namespace blast {
static name * g_prefix = nullptr;

class blastenv {
    environment                m_env;
    io_state                   m_ios;
    name_set                   m_lemma_hints;
    name_set                   m_unfold_hints;
    name_map<level>            m_uvar2uref;    // map global universe metavariables to blast uref's
    name_map<pair<expr, expr>> m_mvar2meta_mref; // map global metavariables to blast mref's
    name_predicate             m_not_reducible_pred;
    name_map<projection_info>  m_projection_info;
    state                      m_curr_state;   // current state

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

public:
    blastenv(environment const & env, io_state const & ios, list<name> const & ls, list<name> const & ds):
        m_env(env), m_ios(ios), m_lemma_hints(to_name_set(ls)), m_unfold_hints(to_name_set(ds)),
        m_not_reducible_pred(mk_not_reducible_pred(env)) {
    }

    optional<expr> operator()(goal const & g) {
        m_curr_state = to_state(g);

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

void display_curr_state() {
    curr_state().display(env(), ios());
    display("\n");
}

void display(char const * msg) {
    ios().get_diagnostic_channel() << msg;
}

void display(sstream const & msg) {
    ios().get_diagnostic_channel() << msg.str();
}

/** \brief Auxiliary object to interface blast state with existing kernel extensions */
class ext_context : public extension_context {
    name_generator m_ngen;
public:
    virtual environment const & env() const { return env(); }

    virtual pair<expr, constraint_seq> whnf(expr const & e) {
        return mk_pair(blast::whnf(e), constraint_seq());
    }

    virtual pair<bool, constraint_seq> is_def_eq(expr const & e1, expr const & e2, delayed_justification &) {
        return mk_pair(blast::is_def_eq(e1, e2), constraint_seq());
    }

    virtual pair<expr, constraint_seq> check_type(expr const & e, bool) {
        return mk_pair(blast::infer_type(e), constraint_seq());
    }

    virtual name mk_fresh_name() {
        return m_ngen.next();
    }

    virtual optional<expr> is_stuck(expr const &) {
        return none_expr();
    }
};

LEAN_THREAD_PTR(ext_context, g_ext_context);
struct scope_ext_context {
    ext_context * m_prev_context;
public:
    scope_ext_context(ext_context & c):m_prev_context(g_ext_context) { g_ext_context = &c; }
    ~scope_ext_context() { g_ext_context = m_prev_context; }
};

extension_context & ext_ctx() {
    lean_assert(g_ext_context);
    return *g_ext_context;
}

name mk_fresh_local_name() {
    lean_assert(g_ext_context);
    return g_ext_context->mk_fresh_name();
}
}
optional<expr> blast_goal(environment const & env, io_state const & ios, list<name> const & ls, list<name> const & ds,
                          goal const & g) {
    blast::scope_hash_consing scope1;
    blast::blastenv b(env, ios, ls, ds);
    blast::ext_context x;
    blast::scope_blastenv    scope2(b);
    blast::scope_ext_context scope3(x);
    return b(g);
}
void initialize_blast() {
    blast::g_prefix = new name(name::mk_internal_unique_name());
}
void finalize_blast() {
    delete blast::g_prefix;
}
}
