/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <unordered_set>
#include "runtime/flet.h"
#include "kernel/type_checker.h"
#include "kernel/for_each_fn.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "library/util.h"
#include "library/constants.h"
#include "library/class.h"
#include "library/compiler/util.h"

#include "library/trace.h"

namespace lean {
class csimp_fn {
    type_checker::state m_st;
    local_ctx           m_lctx;
    buffer<expr>        m_fvars;
    name                m_x;
    unsigned            m_next_idx{1};
    typedef std::unordered_set<name, name_hash> name_set;

    environment const & env() const { return m_st.env(); }

    name_generator & ngen() { return m_st.ngen(); }

    /* Very simple predicate used to decide whether we should inline joint-points or not.
       TODO(Leo): improve */
    bool is_small(expr const & e) const {
        if (is_app(e) && !is_cases_on_app(env(), e))
            return true;
        if (is_lambda(e))
            return is_small(binding_body(e));
        return false;
    }

    expr find(expr const & e, bool skip_mdata = true) const {
        if (is_fvar(e)) {
            if (optional<local_decl> decl = m_lctx.find_local_decl(e)) {
                if (optional<expr> v = decl->get_value()) {
                    if (!is_join_point_name(decl->get_user_name()))
                        return find(*v, skip_mdata);
                    else if (is_small(*v))
                        return find(*v, skip_mdata);
                }
            }
        } else if (is_mdata(e) && skip_mdata) {
            return find(mdata_expr(e), true);
        }
        return e;
    }

    type_checker tc() { return type_checker(m_st, m_lctx); }

    expr infer_type(expr const & e) { return type_checker(m_st, m_lctx).infer(e); }

    expr whnf(expr const & e) { return type_checker(m_st, m_lctx).whnf(e); }

    expr whnf_infer_type(expr const & e) { type_checker tc(m_st, m_lctx); return tc.whnf(tc.infer(e)); }

    name next_name() {
        /* Remark: we use `m_x.append_after(m_next_idx)` instead of `name(m_x, m_next_idx)`
           because the resulting name is confusing during debugging: it looks like a projection application.
           We should replace it with `name(m_x, m_next_idx)` when the compiler code gets more stable. */
        name r = m_x.append_after(m_next_idx);
        m_next_idx++;
        return r;
    }

    /* Create a new let-declaration `x : t := e`, add `x` to `m_fvars` and return `x`. */
    expr mk_let_decl(expr const & e) {
        lean_assert(!is_lcnf_atom(e));
        expr type = cheap_beta_reduce(infer_type(e));
        expr fvar = m_lctx.mk_local_decl(ngen(), next_name(), type, e);
        m_fvars.push_back(fvar);
        return fvar;
    }

    /* Given the `cases_on` application, return [first_minor_idx, first_minor_idx + nminors) */
    pair<unsigned, unsigned> get_cases_on_minors_range(name const & cases) {
        inductive_val I_val = env().get(cases.get_prefix()).to_inductive_val();
        unsigned nparams    = I_val.get_nparams();
        unsigned nindices   = I_val.get_nindices();
        unsigned nminors    = I_val.get_ncnstrs();
        unsigned first_minor_idx = nparams + 1 /*motive*/ + nindices + 1 /* major */;
        return mk_pair(first_minor_idx, first_minor_idx + nminors);
    }

    /* Given a cases_on application `c`, return `some idx` iff `fvar` only occurs
       in the argument `idx`, this argument is a minor premise. */
    optional<unsigned> used_in_one_minor(expr const & c, expr const & fvar) {
        lean_assert(is_cases_on_app(env(), c));
        lean_assert(is_fvar(fvar));
        buffer<expr> args;
        expr const & c_fn = get_app_args(c, args);
        unsigned minors_begin; unsigned minors_end;
        std::tie(minors_begin, minors_end) = get_cases_on_minors_range(const_name(c_fn));
        unsigned i = 0;
        for (; i < minors_begin; i++) {
            if (has_fvar(args[i], fvar)) {
                /* Free variable occurs in a term that is a not a minor premise. */
                return optional<unsigned>();
            }
        }
        lean_assert(i == minors_begin);
        /* The following #pragma is to disable a bogus g++ 4.9 warning at `optional<unsigned> r` */
        #if defined(__GNUC__) && !defined(__CLANG__)
        #pragma GCC diagnostic ignored "-Wmaybe-uninitialized"
        #endif
        optional<unsigned> r;
        for (; i < minors_end; i++) {
            expr minor = args[i];
            while (is_lambda(minor)) {
                if (has_fvar(binding_domain(minor), fvar)) {
                    /* Free variable occurs in the type of a field */
                    return optional<unsigned>();
                }
                minor = binding_body(minor);
            }
            if (has_fvar(minor, fvar)) {
                if (r) {
                    /* Free variable occur in more than one minor premise. */
                    return optional<unsigned>();
                }
                r = i;
            }
        }
        return r;
    }

    /* Move let-decl `fvar` to the minor premise at position `minor_idx` of cases_on-application `c`. */
    expr move_let_to_minor(expr const & c, unsigned minor_idx, expr const & fvar) {
        lean_assert(is_cases_on_app(env(), c));
        buffer<expr> args;
        expr const & c_fn = get_app_args(c, args);
        expr minor = args[minor_idx];
        flet<local_ctx> save_lctx(m_lctx, m_lctx);
        buffer<expr> xs;
        while (is_lambda(minor)) {
            expr d = instantiate_rev(binding_domain(minor), xs.size(), xs.data());
            expr x = m_lctx.mk_local_decl(ngen(), binding_name(minor), d, binding_info(minor));
            xs.push_back(x);
            minor  = binding_body(minor);
        }
        minor = instantiate_rev(minor, xs.size(), xs.data());
        if (minor == fvar) {
            /* `let x := v in x` ==> `v` */
            minor = *m_lctx.get_local_decl(fvar).get_value();
        } else {
            xs.push_back(fvar);
        }
        args[minor_idx] = m_lctx.mk_lambda(xs, minor);
        return mk_app(c_fn, args);
    }

    static void collect_used(expr const & e, name_set & S) {
        if (!has_fvar(e)) return;
        for_each(e, [&](expr const & e, unsigned) {
                if (!has_fvar(e)) return false;
                if (is_fvar(e)) { S.insert(fvar_name(e)); return false; }
                return true;
            });
    }

    /* Create the let-expression
       ```
       let x_1 := v_1
           ...
           x_n := v_n
       in e
       ```
       Where `x_1` and `x_n` are the free variables in `fvars`. Remark: we don't use their declaration
       at `m_lctx` to retrieve their user-name/type/value, but `entries`. We build entries because
       the value may have been simplified by the main `mk_let` method (e.g., when the value is a lambda).
       The main `mk_let` does not modify the user-name/type, but we store them at `entries` just for
       convenience and to avoid additional accesses to `m_lctx`.

       Remark: `fvars` and `entries` are not modified. */
    expr mk_let(buffer<expr> & fvars, buffer<std::tuple<name, expr, expr>> & entries, expr e) {
        lean_assert(fvars.size() == entries.size());
        std::reverse(fvars.begin(), fvars.end());
        std::reverse(entries.begin(), entries.end());
        e = abstract(e, fvars.size(), fvars.data());
        unsigned i = entries.size();
        while (i > 0) {
            --i;
            expr new_value = abstract(std::get<2>(entries[i]), i, fvars.data());
            expr new_type  = abstract(std::get<1>(entries[i]), i, fvars.data());
            e = ::lean::mk_let(std::get<0>(entries[i]), new_type, new_value, e);
        }
        /* Restore `fvars` and `entries` */
        std::reverse(fvars.begin(), fvars.end());
        std::reverse(entries.begin(), entries.end());
        return e;
    }

    /* Float cases transformation
      ```
      let x := cases_on m (fun y_1, let ... in e_1)
      ...
      (fun y_n, let ... in e_n))
      in e
      ```
      ==>
      ```
      cases_on m (fun y_1, let ... x := e_1 in e)
      ...
      (fun y_n, let ... x := e_n in e)
      ``` */
    optional<expr> float_cases_on(expr const & fvar, expr const & c, expr const & e) {
        lean_assert(is_cases_on_app(env(), c));
        local_decl fvar_decl     = m_lctx.get_local_decl(fvar);
        expr result_type         = whnf_infer_type(e);
        buffer<expr> c_args;
        expr c_fn = get_app_args(c, c_args);
        inductive_val I_val      = env().get(const_name(c_fn).get_prefix()).to_inductive_val();
        unsigned motive_idx      = I_val.get_nparams();
        unsigned first_index     = motive_idx + 1;
        unsigned nindices        = I_val.get_nindices();
        unsigned major_idx       = first_index + nindices;
        unsigned first_minor_idx = major_idx + 1;
        unsigned nminors         = I_val.get_ncnstrs();
        /* Update motive */
        {
            flet<local_ctx> save_lctx(m_lctx, m_lctx);
            buffer<expr> fvars;
            expr motive              = c_args[motive_idx];
            expr motive_type         = whnf_infer_type(motive);
            for (unsigned i = 0; i < nindices + 1; i++) {
                lean_assert(is_pi(motive_type));
                expr fvar = m_lctx.mk_local_decl(ngen(), binding_name(motive_type), binding_domain(motive_type), binding_info(motive_type));
                fvars.push_back(fvar);
                motive_type = whnf(instantiate(binding_body(motive_type), fvar));
            }
            level result_lvl       = sort_level(tc().ensure_type(result_type));
            expr new_motive        = m_lctx.mk_lambda(fvars, result_type);
            c_args[motive_idx] = new_motive;
            /* We need to update the resultant universe. */
            levels new_cases_lvls  = levels(result_lvl, tail(const_levels(c_fn)));
            c_fn = update_constant(c_fn, new_cases_lvls);
        }
        flet<local_ctx> save_lctx(m_lctx, m_lctx);
        unsigned  saved_fvars_size = m_fvars.size();
        /* Update minor premises */
        for (unsigned i = 0; i < nminors; i++) {
            unsigned minor_idx    = first_minor_idx + i;
            expr minor            = c_args[minor_idx];
            buffer<expr> minor_fvars;
            unsigned old_fvars_size = m_fvars.size();
            while (is_lambda(minor)) {
                expr new_d    = instantiate_rev(binding_domain(minor), minor_fvars.size(), minor_fvars.data());
                expr new_fvar = m_lctx.mk_local_decl(ngen(), binding_name(minor), new_d, binding_info(minor));
                minor_fvars.push_back(new_fvar);
                minor = binding_body(minor);
            }
            expr minor_val = visit(instantiate_rev(minor, minor_fvars.size(), minor_fvars.data()), true);
            /* TODO(Leo): We need to preserve join points. */
            expr minor_val_type = infer_type(minor_val);
            minor_val           = mk_cast(minor_val_type, fvar_decl.get_type(), minor_val);
            expr new_fvar       = m_lctx.mk_local_decl(ngen(), fvar_decl.get_user_name(), fvar_decl.get_type(), minor_val);
            m_fvars.push_back(new_fvar);
            expr new_minor;
            if (optional<expr> new_minor_opt = replace_fvar_with(m_st, m_lctx, e, fvar, new_fvar)) {
                new_minor = *new_minor_opt;
            } else {
                m_fvars.resize(saved_fvars_size);
                return none_expr(); /* Failed to produce type correct `new_minor` */
            }
            new_minor           = visit(new_minor, false);
            expr new_minor_type = infer_type(new_minor);
            new_minor           = mk_cast(new_minor_type, result_type, new_minor);
            new_minor           = mk_let(old_fvars_size, new_minor);
            new_minor           = m_lctx.mk_lambda(minor_fvars, new_minor);
            c_args[minor_idx] = new_minor;
        }
        return some_expr(mk_app(c_fn, c_args));
    }

    /* Create a let-expression with body `e`, and
       all "used" let-declarations `m_fvars[i]` for `i in [old_fvars_size, m_fvars.size)`.

       BTW, we also visit the lambda expressions in used let-declarations of the form
       `x : t := fun ...`

       Note that, we don't visit them when we have visit let-expressions. */
    expr mk_let(unsigned old_fvars_size, expr e) {
        if (old_fvars_size == m_fvars.size())
            return e;
        name_set e_fvars;
        name_set entries_fvars;
        collect_used(e, e_fvars);
        unsigned i = m_fvars.size();
        buffer<std::tuple<name, expr, expr>> entries;
        buffer<expr> fvars;
        bool e_is_cases = is_cases_on_app(env(), e);
        while (i > old_fvars_size) {
            lean_assert(entries.size() == fvars.size());
            --i;
            expr fvar = m_fvars.back();
            m_fvars.pop_back();
            bool used_in_e       = (e_fvars.find(fvar_name(fvar)) != e_fvars.end());
            bool used_in_entries = (entries_fvars.find(fvar_name(fvar)) != entries_fvars.end());
            if (!used_in_e && !used_in_entries) {
                /* Skip unused variables */
                continue;
            }

            local_decl decl = m_lctx.get_local_decl(fvar);
            expr type       = decl.get_type();
            expr val        = *decl.get_value();
            if (is_lambda(val)) {
                /* We don't simplify lambdas when we visit `let`-expressions. */
                DEBUG_CODE(unsigned saved_fvars_size = m_fvars.size(););
                val         = visit_lambda(val);
                lean_assert(m_fvars.size() == saved_fvars_size);
            }

            if (is_fvar(e) && entries.empty() && fvar_name(e) == fvar_name(fvar)) {
                /* `let x := v in x` ==> `v` */
                e = val;
                collect_used(val, e_fvars);
                e_is_cases = is_cases_on_app(env(), e);
                continue;
            }

            /* TODO(Leo): enable "float cases" as soon as it has descent performance */
            if (false && is_cases_on_app(env(), val)) {
                /* Float cases transformation. */
                DEBUG_CODE(unsigned saved_fvars_size = m_fvars.size(););
                expr new_e = mk_let(fvars, entries, e);
                /* TODO(Leo): create new joint point if `e` is too big */
                if (optional<expr> new_e_opt = float_cases_on(fvar, val, new_e)) {
                    e = *new_e_opt;
                    fvars.clear();   entries.clear();
                    e_fvars.clear(); entries_fvars.clear();
                    collect_used(e, e_fvars);
                    lean_assert(m_fvars.size() == saved_fvars_size);
                    continue;
                } else {
                    lean_assert(m_fvars.size() == saved_fvars_size);
                }
            }

            if (e_is_cases && used_in_e) {
                optional<unsigned> minor_idx = used_in_one_minor(e, fvar);
                if (minor_idx && !used_in_entries) {
                    /* If fvar is only used in only one minor declaration,
                       and is *not* used in any expression at entries */
                    if (is_lambda(val)) {
                        /* We need to create a new free variable since the new
                           simplified value `val` */
                        expr new_fvar = m_lctx.mk_local_decl(ngen(), decl.get_user_name(), type, val);
                        e = replace_fvar(e, fvar, new_fvar);
                        fvar = new_fvar;
                    }
                    collect_used(type, e_fvars);
                    collect_used(val, e_fvars);
                    e = move_let_to_minor(e, *minor_idx, fvar);
                    continue;
                }
            }

            fvars.push_back(fvar);
            collect_used(type, entries_fvars);
            collect_used(val,  entries_fvars);
            entries.emplace_back(decl.get_user_name(), type, val);
        }
        return mk_let(fvars, entries, e);
    }

    expr visit_let(expr e) {
        buffer<expr> let_fvars;
        while (is_let(e)) {
            expr new_type = instantiate_rev(let_type(e), let_fvars.size(), let_fvars.data());
            expr new_val  = visit(instantiate_rev(let_value(e), let_fvars.size(), let_fvars.data()), true);
            if (is_lcnf_atom(new_val)) {
                let_fvars.push_back(new_val);
            } else {
                name n = let_name(e);
                if (is_internal_name(n) && !is_join_point_name(n))
                    n = next_name();
                expr new_fvar = m_lctx.mk_local_decl(ngen(), n, new_type, new_val);
                let_fvars.push_back(new_fvar);
                m_fvars.push_back(new_fvar);
            }
            e = let_body(e);
        }
        return visit(instantiate_rev(e, let_fvars.size(), let_fvars.data()), false);
    }

    expr visit_lambda(expr e) {
        lean_assert(is_lambda(e));
        expr r;
        flet<local_ctx> save_lctx(m_lctx, m_lctx);
        unsigned old_fvars_size = m_fvars.size();
        buffer<expr> binding_fvars;
        while (is_lambda(e)) {
            /* Types are ignored in compilation steps. So, we do not invoke visit for d. */
            expr new_d    = instantiate_rev(binding_domain(e), binding_fvars.size(), binding_fvars.data());
            expr new_fvar = m_lctx.mk_local_decl(ngen(), binding_name(e), new_d, binding_info(e));
            binding_fvars.push_back(new_fvar);
            e = binding_body(e);
        }
        expr new_body = visit(instantiate_rev(e, binding_fvars.size(), binding_fvars.data()), false);
        new_body      = mk_let(old_fvars_size, new_body);
        return m_lctx.mk_lambda(binding_fvars, new_body);
    }

    bool should_inline_instance(name const & n) const {
        if (is_instance(env(), n))
            return !has_noinline_attribute(env(), n);
        else
            return false;
    }

    static unsigned get_num_nested_lambdas(expr e) {
        unsigned r = 0;
        while (is_lambda(e)) {
            r++;
            e = binding_body(e);
        }
        return r;
    }

    expr beta_reduce(expr fn, unsigned nargs, expr const * args, bool is_let_val) {
        unsigned i = 0;
        while (is_lambda(fn) && i < nargs) {
            i++;
            fn = binding_body(fn);
        }
        expr r = instantiate_rev(fn, i, args);
        if (is_lambda(r)) {
            lean_assert(i == nargs);
            return visit(r, is_let_val);
        } else {
            r = visit(r, false);
            if (!is_lcnf_atom(r))
                r = mk_let_decl(r);
            return visit(mk_app(r, nargs - i, args + i), is_let_val);
        }
    }

    /* Remark: if `fn` is not a lambda expression, then this function
       will simply create the application `fn args_of(e)` */
    expr beta_reduce(expr fn, expr const & e, bool is_let_val) {
        buffer<expr> args;
        get_app_args(e, args);
        return beta_reduce(fn, args.size(), args.data(), is_let_val);
    }

    optional<expr> try_inline_instance(expr const & fn, expr const & e) {
        lean_assert(is_constant(fn));
        optional<constant_info> info = env().find(mk_cstage1_name(const_name(fn)));
        if (!info || !info->is_definition()) return none_expr();
        if (get_app_num_args(e) < get_num_nested_lambdas(info->get_value())) return none_expr();
        local_ctx saved_lctx       = m_lctx;
        unsigned  saved_fvars_size = m_fvars.size();
        expr new_fn = instantiate_value_lparams(*info, const_levels(fn));
        expr r      = find(beta_reduce(new_fn, e, false));
        if (!is_constructor_app(env(), r)) {
            m_lctx = saved_lctx;
            m_fvars.resize(saved_fvars_size);
            return none_expr();
        }
        return some_expr(r);
    }

    expr proj_constructor(expr const & k_app, unsigned proj_idx) {
        lean_assert(is_constructor_app(env(), k_app));
        buffer<expr> args;
        expr const & k        = get_app_args(k_app, args);
        constructor_val k_val = env().get(const_name(k)).to_constructor_val();
        lean_assert(k_val.get_nparams() + proj_idx < args.size());
        return args[k_val.get_nparams() + proj_idx];
    }

    expr visit_proj(expr const & e, bool is_let_val) {
        expr s = find(proj_expr(e));
        if (is_constructor_app(env(), s))
            return proj_constructor(s, proj_idx(e).get_small_value());
        expr const & s_fn = get_app_fn(s);
        if (is_constant(s_fn) && should_inline_instance(const_name(s_fn))) {
            if (optional<expr> k_app = try_inline_instance(s_fn, s))
                return visit(proj_constructor(*k_app, proj_idx(e).get_small_value()), is_let_val);
        }
        return e;
    }

    expr reduce_cases_cnstr(buffer<expr> const & args, inductive_val const & I_val, expr const & major, bool is_let_val) {
        lean_assert(is_constructor_app(env(), major));
        unsigned nparams = I_val.get_nparams();
        buffer<expr> k_args;
        expr const & k   = get_app_args(major, k_args);
        lean_assert(is_constant(k));
        lean_assert(nparams <= k_args.size());
        unsigned first_minor_idx = nparams + 1 /* typeformer/motive */ + I_val.get_nindices() + 1 /* major */;
        constructor_val k_val = env().get(const_name(k)).to_constructor_val();
        expr const & minor    = args[first_minor_idx + k_val.get_cidx()];
        return beta_reduce(minor, k_args.size() - nparams, k_args.data() + nparams, is_let_val);
    }

    /* Return `let _x := e in _x` */
    expr mk_trivial_let(expr const & e) {
        expr type = infer_type(e);
        return ::lean::mk_let("_x", type, e, mk_bvar(0));
    }

    /* Just simplify minor premises. */
    expr visit_cases_default(expr const & c, buffer<expr> & args) {
        /* simplify minor premises */
        unsigned minor_idx; unsigned minors_end;
        std::tie(minor_idx, minors_end) = get_cases_on_minors_range(const_name(c));
        for (; minor_idx < minors_end; minor_idx++) {
            expr minor            = args[minor_idx];
            flet<local_ctx> save_lctx(m_lctx, m_lctx);
            buffer<expr> minor_fvars;
            unsigned old_fvars_size = m_fvars.size();
            while (is_lambda(minor)) {
                expr new_d    = instantiate_rev(binding_domain(minor), minor_fvars.size(), minor_fvars.data());
                expr new_fvar = m_lctx.mk_local_decl(ngen(), binding_name(minor), new_d, binding_info(minor));
                minor_fvars.push_back(new_fvar);
                minor = binding_body(minor);
            }
            expr new_minor = visit(instantiate_rev(minor, minor_fvars.size(), minor_fvars.data()), false);
            new_minor = mk_let(old_fvars_size, new_minor);
            if (is_lambda(new_minor)) {
                /* We don't want to "mix" `minor_fvars` variables with
                   the variables of the `new_minor` lambda */
                new_minor = mk_trivial_let(new_minor);
            }
            new_minor = m_lctx.mk_lambda(minor_fvars, new_minor);
            args[minor_idx] = new_minor;
        }
        return mk_app(c, args);
    }

    expr mk_cast(type_checker & tc, expr const & A, expr const & B, expr t) {
        if (tc.is_def_eq(A, B)) {
            return t;
        } else if (is_lc_proof_app(t)) {
            return mk_app(mk_constant(get_lc_proof_name()), B);
        } else {
            /* lc_cast.{u_1 u_2} : Π {α : Sort u_2} {β : Sort u_1}, α → β */
            level u_2 = sort_level(tc.ensure_type(A));
            level u_1 = sort_level(tc.ensure_type(B));
            if (!is_lcnf_atom(t))
                t = mk_let_decl(t);
            return mk_app(mk_constant(get_lc_cast_name(), {u_1, u_2}), A, B, t);
        }
    }

    expr mk_cast(expr const & A, expr const & B, expr const & t) {
        type_checker tc(m_st, m_lctx);
        return mk_cast(tc, A, B, t);
    }

    /* We can eliminate `S.cases_on` using projections when `S` is a structure.
       Example:
       ```
       prod.cases_on M (\fun a b, t)
       ```
       ==>
       ```
       let a := M.0 in
       let b := M.1 in
       t

       May kill the cases on cases optimization

       let v := cases_on ... (fun, ... (mk ...))
       let y := prod.cases_on v (fun a b, ...)
       ==>
       let v := cases_on ... (fun, ... (mk ...))
       let y := prod.cases_on v (fun a b, ...)

       ``` */
    // expr elim_cases_struct(expr const & major, expr minor, expr const & e) {
    //     unsigned i = 0;
    //     buffer<expr> fields;
    //     while (is_lambda(minor)) {
    //         fields.push_back(mk_let_decl(mk_proj(i, major)));
    //         i++;
    //         minor = binding_body(minor);
    //     }
    //     expr r = instantiate_rev(minor, fields.size(), fields.data());
    //     if (!is_lambda(r))
    //         r = visit(r);
    //     expr e_type = infer_type(e);
    //     expr r_type = infer_type(r);
    //     return mk_cast(r_type, e_type, r);
    // }

    expr visit_cases(expr const & e, bool is_let_val) {
        buffer<expr> args;
        expr const & c = get_app_args(e, args);
        lean_assert(is_constant(c));
        inductive_val I_val      = env().get(const_name(c).get_prefix()).to_inductive_val();
        unsigned major_idx       = I_val.get_nparams() + 1 /* typeformer/motive */ + I_val.get_nindices();
        lean_assert(major_idx < args.size());
        expr const & major       = find(args[major_idx]);
        // if (I_val.get_ncnstrs() == 1) {
        //   return elim_cases_struct(args[major_idx], args[major_idx + 1], e);
        // } else
        if (is_constructor_app(env(), major)) {
            return reduce_cases_cnstr(args, I_val, major, is_let_val);
        // } else if (is_cases_on_app(env(), major)) {
        // return reduce_cases_cases(c, args, I_val, major);
        } else if (!is_let_val) {
            return visit_cases_default(c, args);
        } else {
            return e;
        }
    }

    expr reduce_lc_cast(expr const & e) {
        buffer<expr> args;
        expr const & cast_fn1 = get_app_args(e, args);
        lean_assert(args.size() == 3);
        if (type_checker(m_st, m_lctx).is_def_eq(args[0], args[1])) {
            /* (lc_cast A A t) ==> t */
            return args[2];
        }
        expr major = find(args[2]);
        if (is_lc_cast_app(major)) {
            /* Cast transitivity:
               (lc_cast B C (lc_cast A B t)) ==> (lc_cast A C t)


               lc_cast.{u_1 u_2} : Π {α : Sort u_2} {β : Sort u_1}, α → β */
            buffer<expr> nested_args;
            expr const & cast_fn2 = get_app_args(major, nested_args);
            expr const & C = args[1];
            expr const & A = nested_args[0];
            level u1       = head(const_levels(cast_fn1));
            level u2       = head(tail(const_levels(cast_fn2)));
            return reduce_lc_cast(mk_app(mk_constant(get_lc_cast_name(), {u1, u2}), A, C, nested_args[2]));
        }
        return e;
    }

    expr merge_app_app(expr const & fn, expr const & e, bool is_let_val) {
        lean_assert(is_app(fn));
        lean_assert(is_eqp(find(get_app_fn(e)), fn));
        if (!is_lc_cast_app(fn) && !is_cases_on_app(env(), fn)) {
            buffer<expr> args;
            get_app_args(e, args);
            return visit_app(mk_app(fn, args), is_let_val);
        } else {
            return e;
        }
    }

    expr reduce_cast_app_app(expr const & fn, expr const & e, bool is_let_val) {
        lean_assert(is_lc_cast_app(fn));
        lean_assert(is_eqp(find(get_app_fn(e)), fn));
        /*
            f  := lc_cast g
            e  := f a_1 ... a_n
            ==>
            b_1 := lc_cast a_1
            ...
            b_n := lc_cast a_n
            e   := g b_1 ... b_n
        */
        expr const & g = app_arg(fn);
        buffer<expr> args;
        get_app_args(e, args);
        expr g_type = whnf_infer_type(g);
        for (expr & arg : args) {
            lean_assert(is_pi(g_type));
            expr expected_type = binding_domain(g_type);
            expr arg_type      = infer_type(arg);
            expr new_arg       = mk_cast(arg_type, expected_type, arg);
            arg                = new_arg;
            g_type             = whnf(instantiate(binding_body(g_type), new_arg));
        }
        expr r      = visit_app(mk_app(g, args), is_let_val);
        type_checker tc(m_st, m_lctx);
        expr r_type = tc.infer(r);
        expr e_type = tc.infer(e);
        return mk_cast(tc, r_type, e_type, r);
    }

    expr try_inline(expr const & fn, expr const & e, bool is_let_val) {
        lean_assert(is_constant(fn));
        lean_assert(is_eqp(find(get_app_fn(e)), fn));
        if (has_noinline_attribute(env(), const_name(fn))) return e;
        optional<constant_info> info = env().find(mk_cstage1_name(const_name(fn)));
        if (!info || !info->is_definition()) return e;
        // if (get_app_num_args(e) < get_num_nested_lambdas(info->get_value())) return e;
        /* TODO(Leo): check size and whether function is boring or not. */
        if (!has_inline_attribute(env(), const_name(fn))) return e;
        expr new_fn = instantiate_value_lparams(*info, const_levels(fn));
        return beta_reduce(new_fn, e, is_let_val);
    }

    expr visit_app(expr const & e, bool is_let_val) {
        if (is_cases_on_app(env(), e)) {
            return visit_cases(e, is_let_val);
        } else if (is_lc_cast_app(e)) {
            return reduce_lc_cast(e);
        }
        expr fn = find(get_app_fn(e));
        if (is_lambda(fn)) {
            return beta_reduce(fn, e, is_let_val);
        // } else if (is_cases_on_app(env(), fn)) {
        // return distrib_app_cases(fn, e);
        } else if (is_lc_cast_app(fn)) {
            return reduce_cast_app_app(fn, e, is_let_val);
        } else if (is_lc_unreachable_app(fn)) {
            expr type = infer_type(e);
            return mk_lc_unreachable(m_st, m_lctx, type);
        } else if (is_app(fn)) {
            return merge_app_app(fn, e, is_let_val);
        } else if (is_constant(fn)) {
            return try_inline(fn, e, is_let_val);
        }
        return e;
    }

    expr visit(expr const & e, bool is_let_val) {
        switch (e.kind()) {
        case expr_kind::Lambda: return is_let_val ? e : visit_lambda(e);
        case expr_kind::Let:    return visit_let(e);
        case expr_kind::Proj:   return visit_proj(e, is_let_val);
        case expr_kind::App:    return visit_app(e, is_let_val);
        default:                return e;
        }
    }

public:
    csimp_fn(environment const & env, local_ctx const & lctx):
        m_st(env), m_lctx(lctx), m_x("_x") {}

    expr operator()(expr const & e) {
        expr r = visit(e, false);
        return m_lctx.mk_lambda(m_fvars, r);
    }
};
expr csimp(environment const & env, local_ctx const & lctx, expr const & e) {
    return csimp_fn(env, lctx)(e);
}
}
