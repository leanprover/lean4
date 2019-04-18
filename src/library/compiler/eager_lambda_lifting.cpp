/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "runtime/flet.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "library/trace.h"
#include "library/class.h"
#include "library/compiler/util.h"
#include "library/compiler/closed_term_cache.h"

namespace lean {
name mk_elambda_lifting_name(name const & fn, unsigned idx) {
    name r(fn, "_elambda");
    return r.append_after(idx);
}

bool is_elambda_lifting_name(name fn) {
    while (!fn.is_atomic()) {
        if (fn.is_string() && strncmp(fn.get_string().data(), "_elambda", 8) == 0)
            return true;
        fn = fn.get_prefix();
    }
    return false;
}

/*
   We eagerly lift lambda expressions that are stored in terminal constructors.
   We say a constructor application is terminal if it is the result/returned.
   We use this transformation to generate good code for the following scenario:
   Suppose we have a definition
   ```
   def f (x : nat) : Pro (Nat -> Nat) (Nat -> Bool) :=
   ((fun y, <code1 using x y>), (fun z, <code2 using x z>))
   ```
   That is, `f` is "packing" functions in a structure and returning it.
   Now, consider the following application:
   ```
   (f a).1 b
   ```
   Without eager lambda lifting, `f a` will create two closures and one pair.
   Then, we project the first closure in the pair and apply it to `b`.
   This is inefficient. If `f` is small, we can workaround this problem by inlining
   `f`. However, if inlining is not feasible, we would have to perform all memory allocations.
   This is particularly bad, if `f` is a structure with many fields.
   With eager lambda lifting, we transform `f` into
   ```
   def f._elambda_1 (x y) : Nat :=
   <code1 using x y>
   def f._elambda_2 (x z) : Bool :=
   <code2 using x z>
   def f (x : nat) : Pro (Nat -> Nat) (Nat -> Bool) :=
   (f._elambda_1 x, f._elambda_2 x)
   ```
   Then, when the simplifier sees `(f a).1 b`, it can reduce it to `f._elambda_1 a b`,
   and closure and pair allocations are avoided.

   Note that we do not lift all nested lambdas here, only the ones in terminal constructors.
   Premature lambda lifting may hurt performance in the non-terminal case. Example:
   ```
   def f (xs : List Nat) :=
   let g := fun x, x + x in
   List.map g xs
   ```
   We want to keep `fun x, x+x` until we specialize `f`.

   Remark: we also skip this transformation for definitions marked as `[inline]` or `[instance]`.
*/
class eager_lambda_lifting_fn {
    type_checker::state m_st;
    local_ctx           m_lctx;
    buffer<comp_decl>   m_new_decls;
    name                m_base_name;
    name_set            m_terminal_lambdas;
    name_set            m_nonterminal_lambdas;

    environment const & env() const { return m_st.env(); }

    name_generator & ngen() { return m_st.ngen(); }

    expr lift_lambda(expr const & e) {
        lean_assert(is_lambda(e));
        // tout() << "FOUND: " << e << "\n";
        return e;
    }

    /* Given a free variable `x`, follow let-decls and return a pair `(x, v)`.
       Examples for `find(x)`
       - `x := 1` ==> `(x, 1)`
       - `z := (fun w, w+1); y := z; x := y` ==> `(z, (fun w, w+1))`
       - `z := f a; y := mdata kv z; x := y` ==> `(z, f a)`
    */
    pair<name, expr> find(expr const & x) const {
        lean_assert(is_fvar(x));
        expr e = x;
        name r = fvar_name(x);
        while (true) {
            if (is_mdata(e)) {
                e = mdata_expr(e);
            } else if (is_fvar(e)) {
                r = fvar_name(e);
                optional<local_decl> decl = m_lctx.find_local_decl(e);
                lean_assert(decl);
                if (optional<expr> v = decl->get_value()) {
                    if (is_join_point_name(decl->get_user_name())) {
                        return mk_pair(r, e);
                    } else {
                        e = *v;
                    }
                } else {
                    return mk_pair(r, e);
                }
            } else {
                return mk_pair(r, e);
            }
        }
    }

    expr visit_lambda_core(expr e) {
        flet<local_ctx> save_lctx(m_lctx, m_lctx);
        buffer<expr> fvars;
        while (is_lambda(e)) {
            expr new_type = instantiate_rev(binding_domain(e), fvars.size(), fvars.data());
            expr new_fvar = m_lctx.mk_local_decl(ngen(), binding_name(e), new_type);
            fvars.push_back(new_fvar);
            e = binding_body(e);
        }
        expr r = visit_terminal(instantiate_rev(e, fvars.size(), fvars.data()));
        return m_lctx.mk_lambda(fvars, r);
    }

    expr visit_let(expr e) {
        flet<local_ctx> save_lctx(m_lctx, m_lctx);
        buffer<expr> fvars;
        while (is_let(e)) {
            bool not_root = false;
            bool jp       = is_join_point_name(let_name(e));
            expr new_type = instantiate_rev(let_type(e), fvars.size(), fvars.data());
            expr new_val  = visit(instantiate_rev(let_value(e), fvars.size(), fvars.data()), not_root, jp);
            expr new_fvar = m_lctx.mk_local_decl(ngen(), let_name(e), new_type, new_val);
            fvars.push_back(new_fvar);
            e = let_body(e);
        }
        expr r = visit_terminal(instantiate_rev(e, fvars.size(), fvars.data()));
        r      = abstract(r, fvars.size(), fvars.data());
        unsigned i = fvars.size();
        while (i > 0) {
            --i;
            name const & n = fvar_name(fvars[i]);
            local_decl const & decl = m_lctx.get_local_decl(n);
            expr type = abstract(decl.get_type(), i, fvars.data());
            expr val  = *decl.get_value();
            if (m_terminal_lambdas.contains(n) && !m_nonterminal_lambdas.contains(n)) {
                val = lift_lambda(val);
            }
            r = ::lean::mk_let(decl.get_user_name(), type, abstract(val, i, fvars.data()), r);
        }
        return r;
    }

    expr visit_cases_on(expr const & e) {
        lean_assert(is_cases_on_app(env(), e));
        buffer<expr> args;
        expr const & c = get_app_args(e, args);
        /* Remark: eager lambda lifting is applied before we have erased most type information. */
        unsigned minor_idx; unsigned minors_end;
        bool before_erasure = true;
        std::tie(minor_idx, minors_end) = get_cases_on_minors_range(env(), const_name(c), before_erasure);
        for (; minor_idx < minors_end; minor_idx++) {
            args[minor_idx] = visit_lambda_core(args[minor_idx]);
        }
        return mk_app(c, args);
    }

    expr visit_app(expr const & e) {
        if (is_cases_on_app(env(), e)) {
            return visit_cases_on(e);
        } else {
            buffer<expr> args;
            get_app_args(e, args);
            for (expr const & arg : args) {
                if (is_fvar(arg)) {
                    name x; expr v;
                    std::tie(x, v) = find(arg);
                    if (is_lambda(v)) {
                        m_nonterminal_lambdas.insert(x);
                    }
                }
            }
            return e;
        }
    }

    expr visit_lambda(expr const & e, bool root, bool join_point) {
        if (root || join_point)
            return visit_lambda_core(e);
        else
            return e;
    }

    expr visit(expr const & e, bool root = false, bool join_point = false) {
        switch (e.kind()) {
        case expr_kind::App:    return visit_app(e);
        case expr_kind::Lambda: return visit_lambda(e, root, join_point);
        case expr_kind::Let:    return visit_let(e);
        default:                return e;
        }
    }

    expr visit_terminal(expr const & e) {
        expr t = is_fvar(e) ? find(e).second : e;
        if (is_constructor_app(env(), t)) {
            buffer<expr> args;
            get_app_args(e, args);
            for (expr const & arg : args) {
                if (is_fvar(arg)) {
                    name x; expr v;
                    std::tie(x, v) = find(arg);
                    if (is_lambda(v)) {
                        m_terminal_lambdas.insert(x);
                    }
                }
            }
            return e;
        } else {
            return visit(e);
        }
    }

public:
    eager_lambda_lifting_fn(environment const & env):
        m_st(env) {}

    pair<environment, comp_decls> operator()(comp_decl const & cdecl) {
        m_base_name = cdecl.fst();
        expr r = visit(cdecl.snd(), true);
        comp_decl new_cdecl(cdecl.fst(), r);
        m_new_decls.push_back(new_cdecl);
        return mk_pair(env(), comp_decls(m_new_decls));
    }
};

pair<environment, comp_decls> eager_lambda_lifting(environment env, comp_decls const & ds) {
    comp_decls r;
    for (comp_decl const & d : ds) {
        if (has_inline_attribute(env, d.fst()) || is_instance(env, d.fst())) {
            r = append(r, comp_decls(d));
        } else {
            comp_decls new_ds;
            std::tie(env, new_ds) = eager_lambda_lifting_fn(env)(d);
            r = append(r, new_ds);
        }
    }
    return mk_pair(env, r);
}
}
