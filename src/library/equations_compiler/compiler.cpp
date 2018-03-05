/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <string>
#include "kernel/find_fn.h"
#include "kernel/instantiate.h"
#include "library/trace.h"
#include "library/locals.h"
#include "library/util.h"
#include "library/replace_visitor.h"
#include "library/equations_compiler/compiler.h"
#include "library/equations_compiler/util.h"
#include "library/equations_compiler/structural_rec.h"
#include "library/equations_compiler/unbounded_rec.h"
#include "library/equations_compiler/wf_rec.h"
#include "library/equations_compiler/elim_match.h"
#include "frontends/lean/elaborator.h"

namespace lean {
#define trace_compiler(Code) lean_trace("eqn_compiler", scope_trace_env _scope1(ctx.env(), ctx); Code)

static bool has_nested_rec(expr const & eqns) {
    return static_cast<bool>(find(eqns, [&](expr const & e, unsigned) {
                return is_local(e) && local_info(e).is_rec();
            }));
}

static eqn_compiler_result compile_equations_core(environment & env, elaborator & elab, metavar_context & mctx, local_context const & lctx, expr const & eqns) {
    type_context_old ctx(env, mctx, lctx, elab.get_cache(), transparency_mode::Semireducible);
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
        return unbounded_rec(env, elab, mctx, lctx, eqns);
    }

    if (is_wf_equations(eqns)) {
        return wf_rec(env, elab, mctx, lctx, eqns);
    }

    if (header.m_num_fns == 1) {
        if (!is_recursive_eqns(ctx, eqns)) {
            return mk_nonrec(env, elab, mctx, lctx, eqns);
        } else if (auto r = try_structural_rec(env, elab, mctx, lctx, eqns)) {
            return *r;
        }
    }

    return wf_rec(env, elab, mctx, lctx, eqns);
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
    environment &            m_env;
    elaborator &             m_elab;
    metavar_context &        m_mctx;
    buffer<local_context>    m_lctx_stack;
    buffer<expr>             m_new_locals;
    buffer<expr>             m_new_values;

    pull_nested_rec_fn(environment & env, elaborator & elab, metavar_context & mctx, local_context const & lctx):
        m_env(env), m_elab(elab), m_mctx(mctx) {
        m_lctx_stack.push_back(lctx);
    }

    local_context & base_lctx() { return m_lctx_stack[0]; }

    local_context & lctx() { return m_lctx_stack.back(); }

    type_context_old mk_type_context(local_context const & lctx) {
        return type_context_old(m_env, m_mctx, lctx, m_elab.get_cache(), transparency_mode::Semireducible);
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
        type_context_old ctx = mk_type_context(lctx());
        t = is_lam ? ctx.mk_lambda(locals, t) : ctx.mk_pi(locals, t);
        m_mctx = ctx.mctx();
        m_lctx_stack.pop_back();
        /* We clear the cache whenever we visit a binder because of
           collect_local_props.

           When pulling a recursive call (f t), the resulting term
           may contain local variables that do not occur in (f t).
           Thus, the cached value for (f t) may not be valid
           in other contexts.

           By clearing the cache we conservatively fix this issue.

           Here is an example:

           def filter : list A → list A
           | nil      := nil
           | (a :: l) :=
              match (H a) with
              | (is_true h_1) := a :: filter l
              | (is_false h_2) := filter l
              end

           The first (filter l) is replaced with a term
           (_f_1 l h_1) where _f_1 is a new fresh local.
           We cannot replace the second (filter l)
           with (_f_1 l h_1), since h_1 is not in the scope.
        */
        m_cache.clear();
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

    /* Collect local propositions. This is needed when the nested recursive call will
       be defined by well-founded recursion, and we don't know whether local propositions
       are hints for helping the "decreasing tactic".
       In the future, we should add a mechanism that will only include these propositions
       if the recursive call will be defined using well founded recursion.
    */
    void collect_local_props(name_set & found, buffer<expr> & R) {
        type_context_old ctx = mk_type_context(lctx());
        lctx().for_each([&](local_decl const & d) {
                if (!base_lctx().find_local_decl(d.get_name()) &&
                    !found.contains(d.get_name()) &&
                    !d.get_info().is_rec() &&
                    ctx.is_prop(d.get_type())) {
                    found.insert(d.get_name());
                    R.push_back(d.mk_ref());
                }
            });
    }

    void collect_locals(expr const & e, buffer<expr> & R) {
        name_set found;
        /* Collect used local declarations. */
        collect_locals_core(e, found, R);
        /* Collect local propositions. */
        collect_local_props(found, R);
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

    virtual expr visit_app(expr const & _e) override {
        expr const & fn = get_app_fn(_e);
        if (is_local(fn) && local_info(fn).is_rec() && base_lctx().find_local_decl(fn)) {
            /* `_e` may contain references to let-variables.
               Here is an example from issue #1917

               ```
               def foo : ℕ → false
               | x :=
                 match x with
                 y := let z := y in foo z
                 end
               ```

               We address this issue by using zeta-expansion.
               Remark: this may cause an unintended code size blowup.
             */
            expr e = zeta_expand(lctx(), _e);
            buffer<expr> args;
            get_app_args(e, args);
            buffer<expr> local_deps;
            collect_locals(e, local_deps);
            type_context_old ctx = mk_type_context(lctx());
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
            buffer<expr> args;
            get_app_args(_e, args);
            return default_visit_app(_e, fn, args);
        }
    }

    eqn_compiler_result operator()(expr const & e) {
        expr new_e             = visit(e);
        lean_assert(m_lctx_stack.size() == 1);
        local_context new_lctx = m_lctx_stack[0];
        auto r                 = compile_equations_core(m_env, m_elab, m_mctx, new_lctx, new_e);
        type_context_old ctx       = mk_type_context(new_lctx);
        r.m_fns = map(r.m_fns, [&] (expr const & fn) { return replace_locals(fn, m_new_locals, m_new_values); });
        m_mctx                 = ctx.mctx();
        return r;
    }
};

static expr remove_aux_main_name(expr const & e) {
    buffer<expr> args;
    expr fn = get_app_args(e, args);
    if (!is_constant(fn)) return e;
    name n = const_name(fn);
    if (n.is_string() && n.get_string() == std::string("_main")) {
        n = n.get_prefix();
        fn = mk_constant(n, const_levels(fn));
        return mk_app(fn, args);
    }
    return e;
}

static expr compile_equations_main(environment & env, elaborator & elab,
                                   metavar_context & mctx, local_context const & lctx, expr const & _eqns, bool report_cexs) {
    expr eqns = _eqns;
    equations_header const & header = get_equations_header(eqns);
    eqn_compiler_result r;
    if (!header.m_is_meta && has_nested_rec(eqns)) {
        r = pull_nested_rec_fn(env, elab, mctx, lctx)(eqns);
    } else {
        r = compile_equations_core(env, elab, mctx, lctx, eqns);
    }

    if (report_cexs && r.m_counter_examples) {
        auto pp = mk_pp_ctx(env, elab.get_options(), mctx, lctx);
        auto fmt = format("non-exhaustive match, the following cases are missing:");
        for (auto & ce : r.m_counter_examples) {
            fmt += line() + pp(remove_aux_main_name(ce));
        }
        elab.report_or_throw({_eqns, fmt});
    }

    buffer<expr> fns; to_buffer(r.m_fns, fns);
    return mk_equations_result(fns.size(), fns.data());
}

expr compile_equations(environment & env, elaborator & elab, metavar_context & mctx, local_context const & lctx, expr const & eqns) {
    equations_header const & header = get_equations_header(eqns);
    type_context_old ctx(env, mctx, lctx, elab.get_cache(), transparency_mode::Semireducible);
    if (!header.m_is_meta &&
        !header.m_is_lemma &&
        !header.m_is_noncomputable &&
        /* Remark: we don't need special compilation scheme for non recursive equations */
        is_recursive_eqns(ctx, eqns)) {
        /* We compile non-meta recursive definitions as meta definitions first.
           The motivations are:
           - Clear execution cost semantics for recursive functions.
           - Auxiliary meta definition may assist recursive definition unfolding in the type_context_old object.
        */
        equations_header aux_header = header;
        aux_header.m_is_meta    = true;
        aux_header.m_aux_lemmas = false;
        aux_header.m_fn_actual_names = map(header.m_fn_actual_names, mk_aux_meta_rec_name);
        expr aux_eqns = remove_wf_annotation_from_equations(update_equations(eqns, aux_header));
        compile_equations_main(env, elab, mctx, lctx, aux_eqns, false);
    }
    return compile_equations_main(env, elab, mctx, lctx, eqns, true);
}

void initialize_compiler() {
}

void finalize_compiler() {
}
}
