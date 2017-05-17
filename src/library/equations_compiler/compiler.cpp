/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "kernel/find_fn.h"
#include "kernel/instantiate.h"
#include "library/trace.h"
#include "library/locals.h"
#include "library/replace_visitor.h"
#include "library/equations_compiler/compiler.h"
#include "library/equations_compiler/util.h"
#include "library/equations_compiler/pack_domain.h"
#include "library/equations_compiler/structural_rec.h"
#include "library/equations_compiler/unbounded_rec.h"
#include "library/equations_compiler/elim_match.h"

namespace lean {
#define trace_compiler(Code) lean_trace("eqn_compiler", scope_trace_env _scope1(ctx.env(), ctx); Code)

static bool has_nested_rec(expr const & eqns) {
    return static_cast<bool>(find(eqns, [&](expr const & e, unsigned) {
                return is_local(e) && local_info(e).is_rec();
            }));
}

static expr compile_equations_core(environment & env, options const & opts,
                                   metavar_context & mctx, local_context const & lctx,
                                   expr const & eqns) {
    type_context ctx(env, opts, mctx, lctx, transparency_mode::Semireducible);
    trace_compiler(tout() << "compiling\n" << eqns << "\n";);
    trace_compiler(tout() << "recursive:          " << is_recursive_eqns(ctx, eqns) << "\n";);
    trace_compiler(tout() << "nested recursion:   " << has_nested_rec(eqns) << "\n";);
    trace_compiler(tout() << "using_well_founded: " << is_wf_equations(eqns) << "\n";);
    equations_header const & header = get_equations_header(eqns);
    lean_assert(header.m_is_meta || !has_nested_rec(eqns));

    if (header.m_is_meta) {
        if (is_wf_equations(eqns)) {
            throw exception("invalid use of 'using_well_founded', we do not need to use well founded recursion for meta definitions, since they can use unbounded recursion");
        }
        return mk_equations_result(unbounded_rec(env, opts, mctx, lctx, eqns));
    }

    if (header.m_num_fns == 1) {
        if (!is_recursive_eqns(ctx, eqns)) {
            return mk_equations_result(mk_nonrec(env, opts, mctx, lctx, eqns));
        } else if (optional<expr> r = try_structural_rec(env, opts, mctx, lctx, eqns)) {
            return mk_equations_result(*r);
        }
    }

    throw exception("support for well-founded recursion has not been implemented yet, "
                    "use 'set_option trace.eqn_compiler true' for additional information");
    // test pack_domain
    // pack_domain(ctx, eqns);
}

/** Auxiliary class for pulling nested recursive calls.
    Example: given

    definition f : nat → (nat × nat) → nat
    | 0      m := m.1
    | (n+1)  m :=
      match m with
      | (a, b) := f n (b, a + 1)
      end

    when we compile

      match m with
      | (a, b) := f n (b, a + 1)
      end

    we consinder (f n (b, a + 1)) to be a nested recursive call.
    Then, we transform the expression to

      (fun g,
       match m with
       | (a, b) := g a b
       end) (fun a b, f n (b, a + 1))

    Compile the match, and then beta-reduce.
*/
struct pull_nested_rec_fn : public replace_visitor {
    environment &         m_env;
    options               m_opts;
    metavar_context &     m_mctx;
    buffer<local_context> m_lctx_stack;
    buffer<expr>          m_new_locals;
    buffer<expr>          m_new_values;

    pull_nested_rec_fn(environment & env, options const & opts, metavar_context & mctx, local_context const & lctx):
        m_env(env), m_opts(opts), m_mctx(mctx) {
        m_lctx_stack.push_back(lctx);
    }

    local_context & base_lctx() { return m_lctx_stack[0]; }

    local_context & lctx() { return m_lctx_stack.back(); }

    type_context mk_type_context(local_context const & lctx) {
        return type_context(m_env, m_opts, m_mctx, lctx, transparency_mode::Semireducible);
    }

    expr visit_lambda_pi_let(bool is_lam, expr const & e) {
        buffer<expr> locals;
        m_lctx_stack.push_back(m_lctx_stack.back());
        expr t = e;
        while (true) {
            if ((is_lam && is_lambda(t)) || (!is_lam && is_pi(t))) {
                expr d = instantiate_rev(binding_domain(t), locals.size(), locals.data());
                d = visit(d);
                expr x = lctx().mk_local_decl(binding_name(t), d, binding_info(t));
                locals.push_back(x);
                t = binding_body(t);
            } else if (is_let(t)) {
                expr d = instantiate_rev(let_type(t), locals.size(), locals.data());
                expr v = instantiate_rev(let_value(t), locals.size(), locals.data());
                d = visit(d);
                v = visit(v);
                expr x = lctx().mk_local_decl(let_name(t), d, v);
                locals.push_back(x);
                t = let_body(t);
            } else {
                break;
            }
        }
        t = instantiate_rev(t, locals.size(), locals.data());
        t = visit(t);
        type_context ctx = mk_type_context(lctx());
        t = is_lam ? ctx.mk_lambda(locals, t) : ctx.mk_pi(locals, t);
        m_mctx = ctx.mctx();
        m_lctx_stack.pop_back();
        return t;
    }

    virtual expr visit_lambda(expr const & e) override {
        return visit_lambda_pi_let(true, e);
    }

    virtual expr visit_let(expr const & e) override {
        return visit_lambda_pi_let(true, e);
    }

    virtual expr visit_pi(expr const & e) override {
        return visit_lambda_pi_let(false, e);
    }

    expr default_visit_app(expr const & e, expr const & fn, buffer<expr> & args) {
        expr new_fn   = visit(fn);
        bool modified = !is_eqp(fn, new_fn);
        for (expr & arg : args) {
            expr new_arg = visit(arg);
            if (!is_eqp(new_arg, arg))
                modified = true;
            arg = new_arg;
        }
        if (!modified)
            return e;
        else
            return mk_app(new_fn, args);
    }

    void collect_locals_core(expr const & e, name_set & found, buffer<expr> & R) {
        for_each(e, [&](expr const & e, unsigned) {
                if (is_local(e) && !base_lctx().find_local_decl(e) && !found.contains(mlocal_name(e))) {
                    found.insert(mlocal_name(e));
                    R.push_back(e);
                }
                return true;
            });
    }

    void collect_locals(expr const & e, buffer<expr> & R) {
        name_set found;
        collect_locals_core(e, found, R);
        for (unsigned i = 0; i < R.size(); i++) {
            expr const & x = R[i];
            collect_locals_core(lctx().get_local_decl(x).get_type(), found, R);
        }
        std::sort(R.begin(), R.end(), [&](expr const & x1, expr const & x2) {
                return lctx().get_local_decl(x1).get_idx() < lctx().get_local_decl(x2).get_idx();
            });
    }

    expr declare_new_local(name const & uid, name const & n, expr const & type) {
        lean_assert(m_lctx_stack.size() > 1);
        expr r;
        for (unsigned i = 0; i < m_lctx_stack.size(); i++) {
            local_context & lctx = m_lctx_stack[i];
            if (i == 0) {
                r = lctx.mk_local_decl(uid, n, type);
            } else {
                DEBUG_CODE(expr r2 =) lctx.mk_local_decl(uid, n, type);
                lean_assert(r == r2);
            }
        }
        return r;
    }

    virtual expr visit_app(expr const & e) override {
        buffer<expr> args;
        expr const & fn = get_app_args(e, args);
        if (is_local(fn) && local_info(fn).is_rec() && base_lctx().find_local_decl(fn)) {
            buffer<expr> local_deps;
            collect_locals(e, local_deps);
            type_context ctx = mk_type_context(lctx());
            expr val         = ctx.mk_lambda(local_deps, e);
            expr val_type    = ctx.infer(val);
            name fn_aux      = name("_f").append_after(m_new_locals.size() + 1);
            name uid         = mk_local_decl_name();
            expr g           = declare_new_local(uid, fn_aux, val_type);
            m_new_locals.push_back(g);
            m_new_values.push_back(val);
            expr r           = g;
            for (expr const & d : local_deps) {
                if (!lctx().get_local_decl(d).get_value())
                    r = mk_app(r, d);
            }
            return r;
        } else {
            return default_visit_app(e, fn, args);
        }
    }

    expr operator()(expr const & e) {
        expr new_e             = visit(e);
        lean_assert(m_lctx_stack.size() == 1);
        local_context new_lctx = m_lctx_stack[0];
        expr r                 = compile_equations_core(m_env, m_opts, m_mctx, new_lctx, new_e);
        type_context ctx       = mk_type_context(new_lctx);
        expr new_r             = replace_locals(r, m_new_locals, m_new_values);
        m_mctx                 = ctx.mctx();
        return new_r;
    }
};

expr compile_equations(environment & env, options const & opts, metavar_context & mctx, local_context const & lctx,
                       expr const & _eqns) {
    expr eqns = _eqns;
    equations_header const & header = get_equations_header(eqns);
    if (!header.m_is_meta && has_nested_rec(eqns)) {
        return pull_nested_rec_fn(env, opts, mctx, lctx)(eqns);
    } else {
        return compile_equations_core(env, opts, mctx, lctx, eqns);
    }
}

void initialize_compiler() {
}
void finalize_compiler() {
}
}
