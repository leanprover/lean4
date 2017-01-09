/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/expr_sets.h"
#include "kernel/expr_maps.h"
#include "kernel/instantiate.h"
#include "kernel/replace_fn.h"
#include "library/trace.h"
#include "library/constants.h"
#include "library/locals.h"
#include "library/vm/vm.h"
#include "library/compiler/procedure.h"
#include "library/compiler/erase_irrelevant.h"
#include "library/compiler/compiler_step_visitor.h"
#include "library/compiler/simp_inductive.h"

namespace lean {
class cse_fn : public compiler_step_visitor {
    unsigned m_counter{1};

    class visitor_fn {
    protected:
        expr_set m_visited;

        bool check_visited(expr const & e) {
            if (m_visited.find(e) != m_visited.end())
                return true;
            m_visited.insert(e);
            return false;
        }

        virtual void visit_macro(expr const & e) = 0;
        virtual void visit_app(expr const & e) = 0;

        void visit_let(expr const & e) {
            if (check_visited(e)) return;
            visit(let_value(e));
            visit(let_body(e));
        }

        void visit_lambda(expr const & e) {
            if (check_visited(e)) return;
            visit(binding_body(e));
        }

        void visit(expr const & e) {
            switch (e.kind()) {
            case expr_kind::Var:      case expr_kind::Sort:
            case expr_kind::Meta:     case expr_kind::Pi:
            case expr_kind::Constant: case expr_kind::Local:
                break;
            case expr_kind::Lambda:   visit_lambda(e); break;
            case expr_kind::Macro:    visit_macro(e); break;
            case expr_kind::App:      visit_app(e); break;
            case expr_kind::Let:      visit_let(e); break;
            default: break;
            }
        }
    public:
        void operator()(expr const & e) { return visit(e); }
    };

    class collect_candidates_fn : public visitor_fn {
        environment const & m_env;
        expr_struct_set m_candidates;

        void add_candidate(expr const & e) {
            if (!closed(e)) return;
            m_candidates.insert(e);
        }

        virtual void visit_macro(expr const & e) override {
            if (check_visited(e)) return;
            if (macro_num_args(e) > 0) add_candidate(e);
            for (unsigned i = 0; i < macro_num_args(e); i++)
                visit(macro_arg(e, i));
        }

        virtual void visit_app(expr const & e) override {
            if (check_visited(e)) return;
            add_candidate(e);
            expr const & fn = get_app_fn(e);
            if (is_vm_supported_cases(m_env, fn)) {
                /* We do not eliminate a common subexpression if it *only* occurs inside of a cases */
                return;
            }
            buffer<expr> args;
            get_app_args(e, args);
            for (expr const & arg : args)
                visit(arg);
        }
    public:
        collect_candidates_fn(environment const & env):m_env(env) {}
        expr_struct_set const & get_candidates() const { return m_candidates; }
    };

    class collect_num_occs_fn : public visitor_fn {
        expr_struct_set const &   m_candidates;
        expr_struct_map<unsigned> m_num_occs;

        void add_occ(expr const & e) {
            if (!closed(e)) return;
            if (m_candidates.find(e) == m_candidates.end()) return;
            if (m_num_occs.find(e) == m_num_occs.end()) {
                m_num_occs.insert(mk_pair(e, 1));
            } else {
                m_num_occs[e]++;
            }
        }

        virtual void visit_macro(expr const & e) override {
            add_occ(e);
            if (check_visited(e)) return;
            for (unsigned i = 0; i < macro_num_args(e); i++)
                visit(macro_arg(e, i));
        }

        virtual void visit_app(expr const & e) override {
            add_occ(e);
            if (check_visited(e)) return;
            buffer<expr> args;
            get_app_args(e, args);
            for (expr const & arg : args)
                visit(arg);
        }
    public:
        collect_num_occs_fn(expr_struct_set const & cs):m_candidates(cs) {}
        expr_struct_map<unsigned> const & get_num_occs() const { return m_num_occs; }
    };

    void collect_common_subexprs(buffer<expr> const & let_values, expr const & body,
                                 expr_struct_set & r) {
        /* first pass */
        collect_candidates_fn candidate_collector(m_ctx.env());
        for (expr const & v : let_values) candidate_collector(v);
        candidate_collector(body);

        /* second pass */
        collect_num_occs_fn num_occs_collector(candidate_collector.get_candidates());
        for (expr const & v : let_values) num_occs_collector(v);
        num_occs_collector(body);

        for (pair<expr, unsigned> const & p : num_occs_collector.get_num_occs()) {
            if (p.second > 1)
                r.insert(p.first);
        }
    }

    expr visit_lambda_let(expr const & e) {
        type_context::tmp_locals locals(m_ctx);
        expr t = e;
        buffer<expr> let_values;
        while (true) {
            /* Types are ignored in compilation steps. So, we do not invoke visit for d. */
            if (is_lambda(t)) {
                expr d = instantiate_rev(binding_domain(t), locals.size(), locals.data());
                locals.push_local(binding_name(t), d, binding_info(t));
                t = binding_body(t);
            } else if (is_let(t)) {
                expr d = instantiate_rev(let_type(t), locals.size(), locals.data());
                expr v = visit(instantiate_rev(let_value(t), locals.size(), locals.data()));
                let_values.push_back(v);
                locals.push_let(let_name(t), d, v);
                t = let_body(t);
            } else {
                break;
            }
        }
        t = instantiate_rev(t, locals.size(), locals.data());
        t = visit(t);

        expr_struct_set common_subexprs;
        collect_common_subexprs(let_values, t, common_subexprs);
        if (common_subexprs.empty())
            return copy_tag(e, locals.mk_lambda(t));

        expr_struct_map<expr> common_subexpr_to_local;
        buffer<expr> new_locals;
        type_context::tmp_locals all_locals(m_ctx); /* new local declarations + let-decls for common-subexprs */
        local_context const & lctx = m_ctx.lctx();

        std::function<expr(expr const &, optional<expr> const &)>
        process = [&](expr const & e, optional<expr> const & main) {
            return replace(e, [&](expr const & s, unsigned) {
                    if (main && s == *main) return none_expr();
                    if (!is_app(s) && !is_macro(s)) return none_expr();
                    if (!closed(s)) return none_expr();
                    auto it1 = common_subexpr_to_local.find(s);
                    if (it1 != common_subexpr_to_local.end())
                        return some_expr(it1->second);
                    if (common_subexprs.find(s) == common_subexprs.end())
                        return none_expr();
                    /* Eliminate common subexpressions nested in s */
                    expr new_v = process(s, some_expr(s));
                    new_v      = replace_locals(new_v, new_locals.size(), locals.data(), new_locals.data());
                    name n = name("_c").append_after(m_counter);
                    m_counter++;
                    expr l = all_locals.push_let(n, mk_neutral_expr(), new_v);
                    common_subexpr_to_local.insert(mk_pair(s, l));
                    return some_expr(l);
                });
        };

        for (expr const & local : locals.as_buffer()) {
            local_decl decl = *lctx.get_local_decl(local);
            if (decl.get_value()) {
                /* let-entry */
                expr new_v = process(*decl.get_value(), none_expr());
                expr l     = all_locals.push_let(decl.get_pp_name(),
                                                 replace_locals(decl.get_type(), new_locals.size(), locals.data(), new_locals.data()),
                                                 replace_locals(new_v, new_locals.size(), locals.data(), new_locals.data()));
                new_locals.push_back(l);
            } else {
                /* lambda-entry */
                expr l = all_locals.push_local(decl.get_pp_name(),
                                               replace_locals(decl.get_type(), new_locals.size(), locals.data(), new_locals.data()),
                                               decl.get_info());
                new_locals.push_back(l);
            }
        }

        expr new_t = process(t, none_expr());
        new_t = replace_locals(new_t, new_locals.size(), locals.data(), new_locals.data());
        return copy_tag(e, all_locals.mk_lambda(new_t));
    }

    virtual expr visit_lambda(expr const & e) override {
        return visit_lambda_let(e);
    }

    virtual expr visit_let(expr const & e) override {
        return visit_lambda_let(e);
    }

public:
    cse_fn(environment const & env):compiler_step_visitor(env) {}
};

void cse(environment const & env, buffer<procedure> & procs) {
    cse_fn fn(env);
    for (auto & proc : procs)
        proc.m_code = fn(proc.m_code);
}
}
