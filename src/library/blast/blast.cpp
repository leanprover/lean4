/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/type_checker.h"
#include "library/replace_visitor.h"
#include "library/blast/expr.h"
#include "library/blast/state.h"
#include "library/blast/blast.h"

namespace lean {
namespace blast {
level to_blast_level(level const & l) {
    level lhs;
    switch (l.kind()) {
    case level_kind::Succ:    return blast::mk_succ(to_blast_level(succ_of(l)));
    case level_kind::Zero:    return blast::mk_level_zero();
    case level_kind::Param:   return blast::mk_param_univ(param_id(l));
    case level_kind::Meta:    return blast::mk_meta_univ(meta_id(l));
    case level_kind::Global:  return blast::mk_global_univ(global_id(l));
    case level_kind::Max:
        lhs = to_blast_level(max_lhs(l));
        return blast::mk_max(lhs, to_blast_level(max_rhs(l)));
    case level_kind::IMax:
        lhs = to_blast_level(imax_lhs(l));
        return blast::mk_imax(lhs, to_blast_level(imax_rhs(l)));
    }
    lean_unreachable();
}

class context {
    environment m_env;
    io_state    m_ios;
    name_set    m_lemma_hints;
    name_set    m_unfold_hints;

    class to_blast_expr_fn : public replace_visitor {
        type_checker                 m_tc;
        state &                      m_state;
        // We map each metavariable to a metavariable application that contains only pairwise
        // distinct local constants (that have been converted into lrefs).
        name_map<pair<expr, expr>> & m_mvar2meta_mref;
        name_map<expr> &             m_local2lref;

        expr visit_sort(expr const & e) {
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

        void throw_unsupported_metavar_occ(expr const &) {
            // TODO(Leo): improve error message
            throw exception("'blast' tactic failed, goal contains a meta-variable application that is not supported");
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
                for (unsigned i = 0; i < decl_args.size(); i++) {
                    lean_assert(is_local(decl_args[i]));
                    if (!is_local(args[i]) || mlocal_name(args[i]) != mlocal_name(decl_args[i]))
                        throw_unsupported_metavar_occ(e);
                }
                return mk_mref_app(meta_mref->second, args.size() - decl_args.size(), args.data() + decl_args.size());
            } else {
                unsigned i = 0;
                hypothesis_set ctx;
                // find prefix of pair-wise distinct local constants that have already been processed.
                for (; i < args.size(); i++) {
                    if (!is_local(args[i]))
                        break;
                    expr const & l = args[i];
                    if (!std::all_of(args.begin(), args.begin() + i,
                                     [&](expr const & prev) { return mlocal_name(prev) != mlocal_name(l); }))
                        break;
                    if (auto lref = m_local2lref.find(mlocal_name(l))) {
                        ctx.insert(lref_index(*lref));
                    } else {
                        break;
                    }
                }
                unsigned  prefix_sz = i;
                expr aux  = e;
                for (; i < args.size(); i++)
                    aux = app_fn(aux);
                lean_assert(is_meta(aux));
                expr type           = visit(m_tc.infer(aux).first);
                unsigned mref_index = m_state.add_metavar_decl(metavar_decl(ctx, type));
                expr mref           = blast::mk_mref(mref_index);
                m_mvar2meta_mref.insert(mlocal_name(mvar), mk_pair(aux, mref));
                return mk_mref_app(mref, args.size() - prefix_sz, args.data() + prefix_sz);
            }
        }

        virtual expr visit_meta(expr const & e) {
            return visit_meta_app(e);
        }

        virtual expr visit_local(expr const & e) {
            if (auto r = m_local2lref.find(mlocal_name(e)))
                return * r;
            else
                throw exception("blast tactic failed, ill-formed input goal");
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
        to_blast_expr_fn(environment const & env, state & s, name_map<pair<expr, expr>> & mvar2meta_mref,
                         name_map<expr> & local2lref):
            m_tc(env), m_state(s), m_mvar2meta_mref(mvar2meta_mref), m_local2lref(local2lref) {}
    };

    state to_state(goal const & g) {
        state s;
        branch b;
        name_map<pair<expr, expr>> mvar2meta_mref;
        name_map<expr> local2lref;
        to_blast_expr_fn to_blast_expr(m_env, s, mvar2meta_mref, local2lref);
        buffer<expr> hs;
        g.get_hyps(hs);
        for (expr const & h : hs) {
            expr new_type = to_blast_expr(mlocal_type(h));
            // TODO(Leo): create hypothesis using new_type
        }
        expr new_target = to_blast_expr(g.get_type());
        // TODO(Leo): create branch and store in the state.
        return s;
    }

public:
    context(environment const & env, io_state const & ios, list<name> const & ls, list<name> const & ds):
        m_env(env), m_ios(ios), m_lemma_hints(to_name_set(ls)), m_unfold_hints(to_name_set(ds)) {
    }

    optional<expr> operator()(goal const & g) {
        state s = to_state(g);
        return none_expr();
    }
};
}
optional<expr> blast_goal(environment const & env, io_state const & ios, list<name> const & ls, list<name> const & ds,
                          goal const & g) {
    blast::scope_hash_consing scope;
    blast::context c(env, ios, ls, ds);
    return c(g);
}
void initialize_blast() {}
void finalize_blast() {}
}
