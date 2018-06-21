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
        expr_set m_visited; /* do we need this? */

        bool check_visited(expr const & e) {
            if (m_visited.find(e) != m_visited.end())
                return true;
            m_visited.insert(e);
            return false;
        }

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
            case expr_kind::BVar:     case expr_kind::Sort:
            case expr_kind::MVar:     case expr_kind::Pi:
            case expr_kind::Const:    case expr_kind::FVar:
            case expr_kind::Lit:
                break;
            case expr_kind::Lambda:   visit_lambda(e); break;
            case expr_kind::App:      visit_app(e); break;
            case expr_kind::Let:      visit_let(e); break;
            case expr_kind::MData:    visit(mdata_expr(e)); break;
            case expr_kind::Proj:     visit(proj_expr(e)); break;
            case expr_kind::Quote:
                break;
            }
        }
    public:
        void operator()(expr const & e) { return visit(e); }
    };

    class collect_candidates_fn : public visitor_fn {
        environment const & m_env;
        expr_set m_candidates;

        void add_candidate(expr const & e) {
            if (has_loose_bvars(e)) return;
            m_candidates.insert(e);
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
        expr_set const & get_candidates() const { return m_candidates; }
    };

    class collect_num_occs_fn : public visitor_fn {
        expr_set const &   m_candidates;
        expr_map<unsigned> m_num_occs;

        void add_occ(expr const & e) {
            if (has_loose_bvars(e)) return;
            if (m_candidates.find(e) == m_candidates.end()) return;
            if (m_num_occs.find(e) == m_num_occs.end()) {
                m_num_occs.insert(mk_pair(e, 1));
            } else {
                m_num_occs[e]++;
            }
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
        collect_num_occs_fn(expr_set const & cs):m_candidates(cs) {}
        expr_map<unsigned> const & get_num_occs() const { return m_num_occs; }
    };

    void collect_common_subexprs(buffer<expr> const & let_values, expr const & body,
                                 expr_set & r) {
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

    void collect_common_subexprs(expr const & e, expr_set & r) {
        buffer<expr> tmp;
        collect_common_subexprs(tmp, e, r);
    }

    /* Helper functor for converting common subexpressions into fresh let-decls */
    struct cse_processor {
        unsigned &        m_counter;
        expr_set const &  m_common_subexprs;
        expr_map<expr>    m_common_subexpr_to_local;
        type_context_old::tmp_locals m_all_locals; /* new local declarations, it also include let-decls for common-subexprs */
        local_context const &        m_lctx;

        cse_processor(unsigned & counter, type_context_old & ctx, expr_set const & s):
            m_counter(counter),
            m_common_subexprs(s),
            m_all_locals(ctx),
            m_lctx(ctx.lctx()) {
        }

        virtual expr adjust_locals(expr const & v) {
            return v;
        }

        expr process(expr const & e, optional<expr> const & main = none_expr()) {
            expr r = replace(e, [&](expr const & s, unsigned) {
                    if (main && s == *main) return none_expr();
                    if (!is_app(s)) return none_expr();
                    if (has_loose_bvars(s)) return none_expr();
                    auto it1 = m_common_subexpr_to_local.find(s);
                    if (it1 != m_common_subexpr_to_local.end())
                        return some_expr(it1->second);
                    if (m_common_subexprs.find(s) == m_common_subexprs.end())
                        return none_expr();
                    /* Eliminate common subexpressions nested in s */
                    expr new_v = process(s, some_expr(s));
                    name n = name("_c").append_after(m_counter);
                    m_counter++;
                    expr l = m_all_locals.push_let(n, mk_neutral_expr(), new_v);
                    m_common_subexpr_to_local.insert(mk_pair(s, l));
                    return some_expr(l);
                });
            return adjust_locals(r);
        }
    };

    /* Similar to cse_processor, but has support for binding exprs (lambda and let) */
    struct cse_processor_for_binding : public cse_processor {
        type_context_old::tmp_locals const & m_locals;
        buffer<expr>                         m_new_locals;

        cse_processor_for_binding(unsigned & counter, type_context_old & ctx, type_context_old::tmp_locals const & locals, expr_set const & s):
            cse_processor(counter, ctx, s),
            m_locals(locals) {
        }

        virtual expr adjust_locals(expr const & v) {
            return replace_locals(v, m_new_locals.size(), m_locals.data(), m_new_locals.data());
        }

        void process_locals() {
            lean_assert(m_new_locals.empty());
            for (expr const & local : m_locals.as_buffer()) {
                local_decl decl = m_lctx.get_local_decl(local);
                if (decl.get_value()) {
                    /* let-entry */
                    expr new_v = process(*decl.get_value());
                    expr l     = m_all_locals.push_let(decl.get_user_name(), adjust_locals(decl.get_type()), new_v);
                    m_new_locals.push_back(l);
            } else {
                /* lambda-entry */
                    expr l = m_all_locals.push_local(decl.get_user_name(), adjust_locals(decl.get_type()), decl.get_info());
                    m_new_locals.push_back(l);
                }
            }
        }
    };

    expr visit_lambda_let(expr const & e) {
        type_context_old::tmp_locals locals(m_ctx);
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

        expr_set common_subexprs;
        collect_common_subexprs(let_values, t, common_subexprs);
        if (common_subexprs.empty())
            return locals.mk_lambda(t);

        cse_processor_for_binding proc(m_counter, m_ctx, locals, common_subexprs);
        proc.process_locals();
        expr new_t = proc.process(t);
        return proc.m_all_locals.mk_lambda(new_t);
    }

    virtual expr visit_lambda(expr const & e) override {
        return visit_lambda_let(e);
    }

    virtual expr visit_let(expr const & e) override {
        return visit_lambda_let(e);
    }

    expr visit_cases_on(expr const & e) {
        buffer<expr> args;
        expr const & fn = get_app_args(e, args);
        args[0] = visit(args[0]); // major premise
        for (unsigned i = 1; i < args.size(); i++) {
            expr m = args[i];
            if (is_lambda(m)) {
                args[i] = visit(m);
            } else {
                m = visit(m);
                expr_set common_subexprs;
                collect_common_subexprs(m, common_subexprs);
                if (!common_subexprs.empty()) {
                    cse_processor proc(m_counter, m_ctx, common_subexprs);
                    m = proc.process(m);
                    m = proc.m_all_locals.mk_lambda(m);
                }
                args[i] = m;
            }
        }
        return mk_app(fn, args);
    }

    virtual expr visit_app(expr const & e) override {
        expr const & fn = get_app_fn(e);
        if (is_vm_supported_cases(m_env, fn)) {
            return visit_cases_on(e);
        } else {
            return compiler_step_visitor::visit_app(e);
        }
    }

public:
    cse_fn(environment const & env, abstract_context_cache & cache):
        compiler_step_visitor(env, cache) {}
};

void cse(environment const & env, abstract_context_cache & cache, buffer<procedure> & procs) {
    cse_fn fn(env, cache);
    for (auto & proc : procs)
        proc.m_code = fn(proc.m_code);
}
}
