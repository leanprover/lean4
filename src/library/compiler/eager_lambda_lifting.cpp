/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "runtime/flet.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/for_each_fn.h"
#include "kernel/type_checker.h"
#include "kernel/inductive.h"
#include "kernel/trace.h"
#include "library/class.h"
#include "library/compiler/util.h"
#include "library/compiler/csimp.h"
#include "library/compiler/closed_term_cache.h"

namespace lean {
extern "C" object* lean_mk_eager_lambda_lifting_name(object* n, object* idx);
extern "C" uint8 lean_is_eager_lambda_lifting_name(object* n);

name mk_elambda_lifting_name(name const & fn, unsigned idx) {
    return name(lean_mk_eager_lambda_lifting_name(fn.to_obj_arg(), mk_nat_obj(idx)));
}

bool is_elambda_lifting_name(name fn) {
    return lean_is_eager_lambda_lifting_name(fn.to_obj_arg());
}

/* Return true iff `e` contains a free variable that is not in `exception_set`. */
static bool has_fvar_except(expr const & e, name_set const & exception_set) {
    if (!has_fvar(e)) return false;
    bool found = false;
    for_each(e, [&](expr const & e, unsigned) {
            if (!has_fvar(e)) return false;
            if (found) return false; // done
            if (is_fvar(e) && !exception_set.contains(fvar_name(e))) {
                found = true;
                return false; // done
            }
            return true;
        });
    return found;
}

/* Return true if the type of a parameter in `params` depends on `fvar`. */
static bool depends_on_fvar(local_ctx const & lctx, buffer<expr> const & params, expr const & fvar) {
    for (expr const & param : params) {
        local_decl const & decl = lctx.get_local_decl(param);
        lean_assert(!decl.get_value());
        if (has_fvar(decl.get_type(), fvar))
            return true;
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
    elab_environment    m_env;
    type_checker::state m_st;
    csimp_cfg           m_cfg;
    local_ctx           m_lctx;
    buffer<comp_decl>   m_new_decls;
    name                m_base_name;
    name_set            m_closed_fvars; /* let-declarations that only depend on global constants and other closed_fvars */
    name_set            m_terminal_lambdas;
    name_set            m_nonterminal_lambdas;
    unsigned            m_next_idx{1};

    elab_environment const & env() const { return m_env; }

    name_generator & ngen() { return m_st.ngen(); }

    expr eta_expand(expr const & e) {
        return lcnf_eta_expand(m_st, m_lctx, e);
    }

    name next_name() {
        name r = mk_elambda_lifting_name(m_base_name, m_next_idx);
        m_next_idx++;
        return r;
    }

    bool collect_fvars_core(expr const & e, name_set & collected, buffer<expr> & fvars) {
        if (!has_fvar(e)) return true;
        bool ok = true;
        for_each(e, [&](expr const & x, unsigned) {
                if (!has_fvar(x)) return false;
                if (!ok) return false;
                if (is_fvar(x)) {
                    if (!collected.contains(fvar_name(x))) {
                        collected.insert(fvar_name(x));
                        local_decl d = m_lctx.get_local_decl(x);
                        /* We do not eagerly lift a lambda if we need to copy a join-point.
                           Remark: we may revise this decision in the future, and use the same
                           approach we use at `lambda_lifting.cpp`.
                         */
                        if (is_join_point_name(d.get_user_name())) {
                            ok = false;
                            return false;
                        } else {
                            if (!collect_fvars_core(d.get_type(), collected, fvars)) {
                                ok = false;
                                return false;
                            }
                            if (m_closed_fvars.contains(fvar_name(x))) {
                                /* If x only depends on global constants and other variables in m_closed_fvars.
                                   Then, we also collect the other variables at m_closed_fvars. */
                                if (!collect_fvars_core(*d.get_value(), collected, fvars)) {
                                    ok = false;
                                    return false;
                                }
                            }
                            fvars.push_back(x);
                        }
                    }
                }
                return true;
            });
        return ok;
    }

    bool collect_fvars(expr const & e, buffer<expr> & fvars) {
        if (!has_fvar(e)) return true;
        name_set collected;
        if (collect_fvars_core(e, collected, fvars)) {
            sort_fvars(m_lctx, fvars);
            return true;
        } else {
            return false;
        }
    }

    /* Split fvars in two groups: `new_params` and `to_copy`.
       We put a fvar `x` in `new_params` if it is not a let declaration,
       or a variable in `params` depend on `x`, or it is not in `m_closed_fvars`.

       The variables in `to_copy` are variables that depend only on
       global constants or other variables in `to_copy`, and `params` do not depend on them. */
    void split_fvars(buffer<expr> const & fvars, buffer<expr> const & params, buffer<expr> & new_params, buffer<expr> & to_copy) {
        for (expr const & fvar : fvars) {
            local_decl const & decl = m_lctx.get_local_decl(fvar);
            if (!decl.get_value()) {
                new_params.push_back(fvar);
            } else {
                if (!m_closed_fvars.contains(fvar_name(fvar)) || depends_on_fvar(m_lctx, params, fvar)) {
                    new_params.push_back(fvar);
                } else {
                    to_copy.push_back(fvar);
                }
            }
        }
    }

    expr lift_lambda(expr e, bool apply_simp) {
        /* Hack: We use `try` here because previous compilation steps may have
           produced type incorrect terms. */
        try {
            lean_assert(is_lambda(e));
            buffer<expr> fvars;
            if (!collect_fvars(e, fvars)) {
                return e;
            }
            buffer<expr> params;
            while (is_lambda(e)) {
                expr param_type = instantiate_rev(binding_domain(e), params.size(), params.data());
                expr param      = m_lctx.mk_local_decl(ngen(), binding_name(e), param_type, binding_info(e));
                params.push_back(param);
                e = binding_body(e);
            }
            e = instantiate_rev(e, params.size(), params.data());
            buffer<expr> new_params, to_copy;
            split_fvars(fvars, params, new_params, to_copy);
            /*
              Variables in `to_copy` only depend on global constants
              and other variables in `to_copy`. Moreover, `params` do not depend on them.
              It is wasteful to pass them as new parameters to the new lifted declaration.
              We can just copy them. The code duplication is not problematic because later at `extract_closed`
              we will create global names for closed terms, and eliminate the redundancy.
            */
            e = m_lctx.mk_lambda(to_copy, e);
            e = m_lctx.mk_lambda(params, e);
            expr code = abstract(e, new_params.size(), new_params.data());
            unsigned i = new_params.size();
            while (i > 0) {
                --i;
                local_decl const & decl = m_lctx.get_local_decl(new_params[i]);
                expr type = abstract(decl.get_type(), i, new_params.data());
                code = ::lean::mk_lambda(decl.get_user_name(), type, code);
            }
            if (apply_simp) {
                code = csimp(env(), code, m_cfg);
            }
            expr type = cheap_beta_reduce(type_checker(m_st).infer(code));
            name n    = next_name();
            /* We add the auxiliary declaration `n` as a "meta" axiom to the elab_environment.
               This is a hack to make sure we can use `csimp` to simplify `code` and
               other definitions that use `n`.
               We used a similar hack at `specialize.cpp`. */
            declaration aux_ax = mk_axiom(n, names(), type, true /* meta */);
            m_env = m_env.add(aux_ax, false);
            m_st.env() = m_env;
            m_new_decls.push_back(comp_decl(n, code));
            return mk_app(mk_constant(n), new_params);
        } catch (exception &) {
            return e;
        }
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
            expr new_fvar = m_lctx.mk_local_decl(ngen(), binding_name(e), new_type, binding_info(e));
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
            if (!has_fvar_except(new_type, m_closed_fvars) && !has_fvar_except(new_val, m_closed_fvars)) {
                m_closed_fvars.insert(fvar_name(new_fvar));
            }
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
                expr new_val = eta_expand(val);
                lean_assert(is_lambda(new_val));
                bool apply_simp = new_val != val;
                val = lift_lambda(new_val, apply_simp);
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
                    v = eta_expand(v);
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
    eager_lambda_lifting_fn(elab_environment const & env, csimp_cfg const & cfg):
        m_env(env), m_st(env), m_cfg(cfg) {}

    pair<elab_environment, comp_decls> operator()(comp_decl const & cdecl) {
        m_base_name = cdecl.fst();
        expr r = visit(cdecl.snd(), true);
        comp_decl new_cdecl(cdecl.fst(), r);
        m_new_decls.push_back(new_cdecl);
        return mk_pair(env(), comp_decls(m_new_decls));
    }
};

pair<elab_environment, comp_decls> eager_lambda_lifting(elab_environment env, comp_decls const & ds, csimp_cfg const & cfg) {
    comp_decls r;
    for (comp_decl const & d : ds) {
        if (has_inline_attribute(env, d.fst()) || is_instance(env, d.fst())) {
            r = append(r, comp_decls(d));
        } else {
            comp_decls new_ds;
            std::tie(env, new_ds) = eager_lambda_lifting_fn(env, cfg)(d);
            r = append(r, new_ds);
        }
    }
    return mk_pair(env, r);
}
}
