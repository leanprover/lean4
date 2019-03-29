/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <unordered_set>
#include <unordered_map>
#include "runtime/flet.h"
#include "kernel/type_checker.h"
#include "kernel/for_each_fn.h"
#include "kernel/find_fn.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "kernel/inductive.h"
#include "library/util.h"
#include "library/constants.h"
#include "library/class.h"
#include "library/trace.h"
#include "library/expr_pair_maps.h"
#include "library/compiler/util.h"
#include "library/compiler/csimp.h"
#include "library/compiler/reduce_arity.h"

namespace lean {
csimp_cfg::csimp_cfg(options const &):
    csimp_cfg() {
}

csimp_cfg::csimp_cfg() {
    m_inline                          = true;
    m_inline_threshold                = 1;
    m_float_cases_threshold           = 20;
    m_inline_jp_threshold             = 2;
}

/*
@[export lean.fold_un_op_core]
def fold_un_op (before_erasure : bool) (f : expr) (a : expr) : option expr :=
*/
object * fold_un_op_core(uint8 before_erasure, object * f, object * a);

optional<expr> fold_un_op(bool before_erasure, expr const & f, expr const & a) {
    inc(f.raw()); inc(a.raw());
    return to_optional_expr(fold_un_op_core(before_erasure, f.raw(), a.raw()));
}

/*
@[export lean.fold_bin_op_core]
def fold_bin_op (before_erasure : bool) (f : expr) (a : expr) (b : expr) : option expr :=
*/
object * fold_bin_op_core(uint8 before_erasure, object * f, object * a, object * b);

optional<expr> fold_bin_op(bool before_erasure, expr const & f, expr const & a, expr const & b) {
    inc(f.raw()); inc(a.raw()); inc(b.raw());
    return to_optional_expr(fold_bin_op_core(before_erasure, f.raw(), a.raw(), b.raw()));
}

class csimp_fn {
    typedef expr_pair_struct_map<expr> jp_cache;
    type_checker::state      m_st;
    local_ctx                m_lctx;
    bool                     m_before_erasure;
    csimp_cfg                m_cfg;
    buffer<expr>             m_fvars;
    name                     m_x;
    name                     m_j;
    unsigned                 m_next_idx{1};
    unsigned                 m_next_jp_idx{1};
    expr_set                 m_simplified;
    /* Cache for the method `mk_new_join_point`. It maps the pair `(jp, lambda(x, e))` to the new joint point. */
    jp_cache                 m_jp_cache;
    /* Maps a free variables to a list of joint points that must be inserted after it. */
    expr_map<exprs>          m_fvar2jps;
    /* Maps a new join point to the free variable it must be defined after.
       It is the "inverse" of m_fvar2jps. It maps to `none` if the joint point is in `m_closed_jps` */
    expr_map<optional<expr>> m_jp2fvar;
    /* Join points that do not depend on any free variable. */
    exprs                    m_closed_jps;
    /* Mapping from projection to eliminated variable.
       Example: at
       ```
       prod.cases_on p
         (λ (p_fst : A) (p_snd : B),
            t[p.1, p.2])
       ```
       replace `p.1` with `p_fst` and `p.2` with `p_snd`.
    */
    typedef rb_map<pair<expr, unsigned>, expr, pair_cmp<expr_quick_cmp, unsigned_cmp>> proj2var;
    proj2var                 m_proj2var;

    environment const & env() const { return m_st.env(); }

    name_generator & ngen() { return m_st.ngen(); }

    unsigned get_fvar_idx(expr const & x) {
        lean_assert(is_fvar(x));
        return m_lctx.get_local_decl(x).get_idx();
    }

    optional<expr> find_max_fvar(expr const & e) {
        if (!has_fvar(e)) return none_expr();
        unsigned max_idx = 0;
        optional<expr> r;
        for_each(e, [&](expr const & x, unsigned) {
                if (!has_fvar(x)) return false;
                if (is_fvar(x)) {
                    auto it = m_jp2fvar.find(x);
                    expr y;
                    if (it != m_jp2fvar.end()) {
                        if (!it->second) {
                            /* `x` is a join point in `m_closed_jps`. */
                            return false;
                        }
                        y = *it->second;
                    } else {
                        y = x;
                    }
                    unsigned curr_idx = get_fvar_idx(y);
                    if (!r || curr_idx > max_idx) {
                        r = y;
                        max_idx = curr_idx;
                    }
                }
                return true;
            });
        return r;
    }

    void register_new_jp(expr const & jp) {
        local_decl jp_decl   = m_lctx.get_local_decl(jp);
        expr jp_val          = *jp_decl.get_value();
        if (optional<expr> max_var = find_max_fvar(jp_val)) {
            m_jp2fvar.insert(mk_pair(jp, some_expr(*max_var)));
            auto it = m_fvar2jps.find(*max_var);
            if (it == m_fvar2jps.end()) {
                m_fvar2jps.insert(mk_pair(*max_var, exprs(jp)));
            } else {
                it->second = exprs(jp, it->second);
            }
        } else {
            m_jp2fvar.insert(mk_pair(jp, none_expr()));
            m_closed_jps = exprs(jp, m_closed_jps);
        }
    }

    void check(expr const & e) {
        if (m_before_erasure) {
            try {
                type_checker(m_st, m_lctx).check(e);
            } catch (exception &) {
                lean_unreachable();
            }
        }
    }

    void mark_simplified(expr const & e) {
        m_simplified.insert(e);
    }

    bool already_simplified(expr const & e) const {
        return m_simplified.find(e) != m_simplified.end();
    }

    bool is_join_point_app(expr const & e) const {
        if (!is_app(e)) return false;
        expr const & fn = get_app_fn(e);
        return
            is_fvar(fn) &&
            is_join_point_name(m_lctx.get_local_decl(fn).get_user_name());
    }

    bool is_small_join_point(expr const & e) const {
        return get_lcnf_size(env(), e) <= m_cfg.m_inline_jp_threshold;
    }

    expr find(expr const & e, bool skip_mdata = true) const {
        if (is_fvar(e)) {
            if (optional<local_decl> decl = m_lctx.find_local_decl(e)) {
                if (optional<expr> v = decl->get_value()) {
                    if (!is_join_point_name(decl->get_user_name()))
                        return find(*v, skip_mdata);
                    else if (is_small_join_point(*v))
                        return find(*v, skip_mdata);
                }
            }
        } else if (is_mdata(e) && skip_mdata) {
            return find(mdata_expr(e), true);
        }
        return e;
    }

    type_checker tc() {
        lean_assert(m_before_erasure);
        return type_checker(m_st, m_lctx);
    }

    expr infer_type(expr const & e) {
        if (m_before_erasure)
            return type_checker(m_st, m_lctx).infer(e);
        else
            return mk_enf_object_type();
    }

    expr whnf(expr const & e) {
        lean_assert(m_before_erasure);
        return type_checker(m_st, m_lctx).whnf(e);
    }

    expr whnf_infer_type(expr const & e) {
        lean_assert(m_before_erasure);
        type_checker tc(m_st, m_lctx);
        return tc.whnf(tc.infer(e));
    }

    name next_name() {
        /* Remark: we use `m_x.append_after(m_next_idx)` instead of `name(m_x, m_next_idx)`
           because the resulting name is confusing during debugging: it looks like a projection application.
           We should replace it with `name(m_x, m_next_idx)` when the compiler code gets more stable. */
        name r = m_x.append_after(m_next_idx);
        m_next_idx++;
        return r;
    }

    name next_jp_name() {
        name r = m_j.append_after(m_next_jp_idx);
        m_next_jp_idx++;
        return mk_join_point_name(r);
    }

    /* Create a new let-declaration `x : t := e`, add `x` to `m_fvars` and return `x`. */
    expr mk_let_decl(expr const & e) {
        lean_assert(!is_lcnf_atom(e));
        expr type = cheap_beta_reduce(infer_type(e));
        expr fvar = m_lctx.mk_local_decl(ngen(), next_name(), type, e);
        m_fvars.push_back(fvar);
        return fvar;
    }

    /* Given a cases_on application `c`, return `some idx` iff `fvar` only occurs
       in the argument `idx`, this argument is a minor premise. */
    optional<unsigned> used_in_one_minor(expr const & c, expr const & fvar) {
        lean_assert(is_cases_on_app(env(), c));
        lean_assert(is_fvar(fvar));
        buffer<expr> args;
        expr const & c_fn = get_app_args(c, args);
        unsigned minors_begin; unsigned minors_end;
        std::tie(minors_begin, minors_end) = get_cases_on_minors_range(env(), const_name(c_fn), m_before_erasure);
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

    /* Return `let _x := e in _x` */
    expr mk_trivial_let(expr const & e) {
        expr type = infer_type(e);
        return ::lean::mk_let("_x", type, e, mk_bvar(0));
    }

    /* Create minor premise in LCNF.
       The minor premise is of the form `fun xs, e`.
       However, if `e` is a lambda, we create `fun xs, let _x := e in _x`.
       Thus, we don't "mix" `xs` variables with
       the variables of the `new_minor` lambda */
    expr mk_minor_lambda(buffer<expr> const & xs, expr e) {
        if (is_lambda(e)) {
            /* We don't want to "mix" `xs` variables with
               the variables of the `new_minor` lambda */
            e = mk_trivial_let(e);
        }
        return m_lctx.mk_lambda(xs, e);
    }

    /* See `mk_minor_lambda`. We want to preserve the arity of join-points. */
    expr mk_join_point_lambda(buffer<expr> const & xs, expr e) {
        return mk_minor_lambda(xs, e);
    }

    expr get_lambda_body(expr e, buffer<expr> & xs) {
        while (is_lambda(e)) {
            expr d = instantiate_rev(binding_domain(e), xs.size(), xs.data());
            expr x = m_lctx.mk_local_decl(ngen(), binding_name(e), d, binding_info(e));
            xs.push_back(x);
            e  = binding_body(e);
        }
        return instantiate_rev(e, xs.size(), xs.data());
    }

    expr get_minor_body(expr const & major, expr e, buffer<expr> & xs) {
        unsigned i = 0;
        while (is_lambda(e)) {
            expr d = instantiate_rev(binding_domain(e), xs.size(), xs.data());
            expr x = m_lctx.mk_local_decl(ngen(), binding_name(e), d, binding_info(e));
            xs.push_back(x);
            m_proj2var.insert(mk_pair(major, i), x);
            i++;
            e  = binding_body(e);
        }
        return instantiate_rev(e, xs.size(), xs.data());
    }

    /* Move let-decl `fvar` to the minor premise at position `minor_idx` of cases_on-application `c`. */
    expr move_let_to_minor(expr const & c, unsigned minor_idx, expr const & fvar) {
        lean_assert(is_cases_on_app(env(), c));
        buffer<expr> args;
        expr const & c_fn = get_app_args(c, args);
        expr minor = args[minor_idx];
        buffer<expr> xs;
        minor = get_lambda_body(minor, xs);
        if (minor == fvar) {
            /* `let x := v in x` ==> `v` */
            minor = *m_lctx.get_local_decl(fvar).get_value();
        } else {
            xs.push_back(fvar);
        }
        args[minor_idx] = mk_minor_lambda(xs, minor);
        return mk_app(c_fn, args);
    }

    /* Collect information for deciding whether `float_cases_on` is useful or not, and control
       code blowup. */
    struct cases_info_result {
        /* The number of branches takes into account join-points too. That is,
           it is not just the number of minor premises. */
        unsigned m_num_branches{0};
        /* The number of branches that return a constructor application. */
        unsigned m_num_cnstr_results{0};
        name_hash_set m_visited_jps;
    };

    void collect_cases_info(expr e, cases_info_result & result) {
        lean_assert(m_before_erasure);
        while (true) {
            if (is_lambda(e))
                e = binding_body(e);
            else if (is_let(e))
                e = let_body(e);
            else
                break;
        }
        if (is_constructor_app(env(), e)) {
            result.m_num_branches++;
            result.m_num_cnstr_results++;
        } else if (is_cases_on_app(env(), e)) {
            buffer<expr> args;
            expr const & fn = get_app_args(e, args);
            unsigned begin_minors; unsigned end_minors;
            std::tie(begin_minors, end_minors) = get_cases_on_minors_range(env(), const_name(fn), m_before_erasure);
            for (unsigned i = begin_minors; i < end_minors; i++) {
                collect_cases_info(args[i], result);
            }
        } else if (is_join_point_app(e)) {
            expr const & fn = get_app_fn(e);
            lean_assert(is_fvar(fn));
            if (result.m_visited_jps.find(fvar_name(fn)) != result.m_visited_jps.end())
                return;
            result.m_visited_jps.insert(fvar_name(fn));
            local_decl decl = m_lctx.get_local_decl(fn);
            collect_cases_info(*decl.get_value(), result);
        } else {
            result.m_num_branches++;
        }
    }

    /* The `float_cases_on` transformation may produce code duplication.
       The term `e` is "copied" in each branch of the the `cases_on` expression `c`.
       This method creates one (or more) join-point(s) for `e` (if needed).
       Return `none` if the code size increase is above the threshold.
       Remark: it may produce type incorrect terms. */
    expr mk_join_point_float_cases_on(expr const & fvar, expr const & e, expr const & c) {
        lean_assert(is_cases_on_app(env(), c));
        unsigned e_size = get_lcnf_size(env(), e);
        if (e_size == 1) {
            return e;
        }
        cases_info_result c_info;
        collect_cases_info(c, c_info);
        unsigned code_increase = e_size*(c_info.m_num_branches - 1);
        if (code_increase <= m_cfg.m_float_cases_threshold) {
            return e;
        }
        local_decl fvar_decl = m_lctx.get_local_decl(fvar);
        if (is_cases_on_app(env(), e)) {
            buffer<expr> args;
            expr const & fn = get_app_args(e, args);
            inductive_val e_I_val = get_cases_on_inductive_val(env(), fn);
            /* We can control the code blowup by creating join points for each branch.
               In the worst case, each branch becomes a join point jump, and the
               "compressed size" is equal to the number of branches + 1 for the cases_on application. */
            unsigned e_compressed_size = e_I_val.get_ncnstrs() + 1;
            /* We can ignore the cost of branches that return constructors since they will in the worst case become
               join point jumps. */
            unsigned new_code_increase = e_compressed_size*(c_info.m_num_branches - c_info.m_num_cnstr_results);
            if (new_code_increase <= m_cfg.m_float_cases_threshold) {
                unsigned branch_threshold = m_cfg.m_float_cases_threshold / (c_info.m_num_branches - 1);
                unsigned begin_minors; unsigned end_minors;
                std::tie(begin_minors, end_minors) = get_cases_on_minors_range(env(), const_name(fn), m_before_erasure);
                for (unsigned minor_idx = begin_minors; minor_idx < end_minors; minor_idx++) {
                    expr minor = args[minor_idx];
                    if (get_lcnf_size(env(), minor) > branch_threshold) {
                        buffer<bool> used_zs; /* used_zs[i] iff `minor` uses `zs[i]` */
                        bool         used_fvar = false; /* true iff `minor` uses `fvar` */
                        bool         used_unit = false; /* true if we needed to add `unit ->` to joint point */
                        expr         jp_val;
                        /* Create join-point value: `jp-val` */
                        {
                            buffer<expr> zs;
                            minor                = get_lambda_body(minor, zs);
                            mark_used_fvars(minor, zs, used_zs);
                            lean_assert(zs.size() == used_zs.size());
                            used_fvar            = false;
                            jp_val               = minor;
                            buffer<expr> jp_args;
                            if (has_fvar(minor, fvar)) {
                                /* `fvar` is a let-decl variable, we need to convert into a lambda variable.
                                   Remark: we need to use `replace_fvar_with` because replacing the let-decl variable `fvar` with
                                   the lambda variable `new_fvar` may produce a type incorrect term. */
                                used_fvar      = true;
                                expr new_fvar  = m_lctx.mk_local_decl(ngen(), fvar_decl.get_user_name(), fvar_decl.get_type());
                                jp_args.push_back(new_fvar);
                                jp_val = replace_fvar(jp_val, fvar, new_fvar);
                            }
                            for (unsigned i = 0; i < used_zs.size(); i++) {
                                if (used_zs[i])
                                    jp_args.push_back(zs[i]);
                            }
                            if (jp_args.empty()) {
                                jp_args.push_back(m_lctx.mk_local_decl(ngen(), "_", mk_unit()));
                                used_unit = true;
                            }
                            jp_val = mk_join_point_lambda(jp_args, jp_val);
                        }
                        /* Create new jp */
                        expr jp_type = cheap_beta_reduce(infer_type(jp_val));
                        mark_simplified(jp_val);
                        expr jp_var  = m_lctx.mk_local_decl(ngen(), next_jp_name(), jp_type, jp_val);
                        register_new_jp(jp_var);
                        /* Replace minor with new jp */
                        {
                            buffer<expr> zs;
                            minor = args[minor_idx];
                            minor = get_lambda_body(minor, zs);
                            lean_assert(zs.size() == used_zs.size());
                            expr new_minor = jp_var;
                            if (used_unit)
                                new_minor = mk_app(new_minor, mk_unit_mk());
                            if (used_fvar)
                                new_minor = mk_app(new_minor, fvar);
                            for (unsigned i = 0; i < used_zs.size(); i++) {
                                if (used_zs[i])
                                    new_minor = mk_app(new_minor, zs[i]);
                            }
                            new_minor       = mk_minor_lambda(zs, new_minor);
                            args[minor_idx] = new_minor;
                        }
                    }
                }
                lean_trace(name({"compiler", "simp"}),
                           tout() << "mk_join " << fvar << "\n" << c << "\n---\n"
                           << e << "\n======>\n" << mk_app(fn, args) << "\n";);
                return mk_app(fn, args);
            }
        }
        /* Create simple join point */
        expr jp_val = e;
        if (is_lambda(e))
            jp_val = mk_trivial_let(jp_val);
        jp_val       = ::lean::mk_lambda(fvar_decl.get_user_name(), fvar_decl.get_type(), abstract(jp_val, fvar));
        expr jp_type = cheap_beta_reduce(infer_type(jp_val));
        mark_simplified(jp_val);
        expr jp_var  = m_lctx.mk_local_decl(ngen(), next_jp_name(), jp_type, jp_val);
        register_new_jp(jp_var);
        return mk_app(jp_var, fvar);
    }

    /* Given `e[x]`, create a let-decl `y := v`, and return `e[y]`
       Note that, this transformation may produce type incorrect terms.

       Remove: if `v` is an atom, we do not create `y`. */
    expr apply_at(expr const & x, expr const & e, expr const & v) {
        if (is_lcnf_atom(v)) {
            expr e_v = replace_fvar(e, x, v);
            return visit(e_v, false);
        } else {
            local_decl x_decl      = m_lctx.get_local_decl(x);
            expr y                 = m_lctx.mk_local_decl(ngen(), x_decl.get_user_name(), x_decl.get_type(), v);
            expr e_y               = replace_fvar(e, x, y);
            m_fvars.push_back(y);
            return visit(e_y, false);
        }
    }

    expr_pair mk_jp_cache_key(expr const & x, expr const & e, expr const & jp) {
        expr x_type = m_lctx.get_local_decl(x).get_type();
        expr abst_e = ::lean::mk_lambda("_x", x_type, abstract(e, x));
        return mk_pair(abst_e, jp);
    }

    /*
      Given `e[x]`
      ```
      let jp := fun z, let .... in e'
      ```
      ==>
      ```
      let jp' := fun z, let ... y := e' in e[y]
      ```
      If `e'` is a `cases_on` application, we use `float_cases_on_core`. That is,
      ```
      let jp := fun z, let ... in
                cases_on m
                 (fun y_1, let ... in e_1)
                 ...
                 (fun y_n, let ... in e_n)
      ```
      ==>
      ```
      let jp := fun z, let ... in
                cases_on m
                 (fun y_1, let ... y := e_1 in e[y])
                 ...
                 (fun y_n, let ... y := e_n in e[y])
      ```

      Remark: this method may produce type incorrect terms because of dependent types. */
    expr mk_new_join_point(expr const & x, expr const & e, expr const & jp) {
        expr_pair key = mk_jp_cache_key(x, e, jp);
        auto it = m_jp_cache.find(key);
        if (it != m_jp_cache.end())
            return it->second;
        local_decl jp_decl = m_lctx.get_local_decl(jp);
        lean_assert(is_join_point_name(jp_decl.get_user_name()));
        expr jp_val = *jp_decl.get_value();
        buffer<expr> zs;
        unsigned saved_fvars_size = m_fvars.size();
        jp_val = visit(get_lambda_body(jp_val, zs), false);
        expr e_y;
        if (is_join_point_app(jp_val)) {
            buffer<expr> jp2_args;
            expr const & jp2  = get_app_args(jp_val, jp2_args);
            expr new_jp2      = mk_new_join_point(x, e, jp2);
            e_y = mk_app(new_jp2, jp2_args);
        } else if (is_cases_on_app(env(), jp_val)) {
            e_y = float_cases_on_core(x, e, jp_val);
        } else {
            e_y = apply_at(x, e, jp_val);
        }
        expr new_jp_val  = e_y;
        new_jp_val = mk_let(zs, saved_fvars_size, new_jp_val, false);
        new_jp_val = mk_join_point_lambda(zs, new_jp_val);
        mark_simplified(new_jp_val);
        expr new_jp_type = cheap_beta_reduce(infer_type(new_jp_val));
        expr new_jp_var  = m_lctx.mk_local_decl(ngen(), next_jp_name(), new_jp_type, new_jp_val);
        register_new_jp(new_jp_var);
        m_jp_cache.insert(mk_pair(key, new_jp_var));
        return new_jp_var;
    }

    /* Given `e[x]`
      ```
      cases_on m
              (fun zs, let ... in e_1)
              ...
              (fun zs, let ... in e_n)
      ```
      ==>
      ```
      cases_on m
        (fun zs, let ... y := e_1 in e[y])
        ...
        (fun y_n, let ... y := e_n in e[y])
      ``` */
    expr float_cases_on_core(expr const & x, expr const & e, expr const & c) {
        lean_assert(is_cases_on_app(env(), c));
        local_decl x_decl     = m_lctx.get_local_decl(x);
        buffer<expr> c_args;
        expr c_fn             = get_app_args(c, c_args);
        inductive_val I_val   = get_cases_on_inductive_val(env(), c_fn);
        unsigned major_idx;
        /* Update motive and get major_idx */
        if (m_before_erasure) {
            unsigned motive_idx      = I_val.get_nparams();
            unsigned first_index     = motive_idx + 1;
            unsigned nindices        = I_val.get_nindices();
            major_idx                = first_index + nindices;
            buffer<expr> zs;
            expr result_type         = whnf_infer_type(e);
            expr motive              = c_args[motive_idx];
            expr motive_type         = whnf_infer_type(motive);
            for (unsigned i = 0; i < nindices + 1; i++) {
                lean_assert(is_pi(motive_type));
                expr z = m_lctx.mk_local_decl(ngen(), binding_name(motive_type), binding_domain(motive_type), binding_info(motive_type));
                zs.push_back(z);
                motive_type = whnf(instantiate(binding_body(motive_type), z));
            }
            level result_lvl       = sort_level(tc().ensure_type(result_type));
            if (has_fvar(result_type, x)) {
                /* `x` will be deleted after the float_cases_on transformation.
                   So, if the result type depends on it, we must replace it with its value. */
                result_type = replace_fvar(result_type, x, *x_decl.get_value());
            }
            expr new_motive        = m_lctx.mk_lambda(zs, result_type);
            c_args[motive_idx] = new_motive;
            /* We need to update the resultant universe. */
            levels new_cases_lvls  = levels(result_lvl, tail(const_levels(c_fn)));
            c_fn = update_constant(c_fn, new_cases_lvls);
        } else {
            /* After erasure, we keep only major and minor premises. */
            major_idx = 0;
        }
        /* Update minor premises */
        expr const & major = c_args[major_idx];
        unsigned first_minor_idx = major_idx + 1;
        unsigned nminors         = I_val.get_ncnstrs();
        for (unsigned i = 0; i < nminors; i++) {
            unsigned minor_idx        = first_minor_idx + i;
            expr minor                = c_args[minor_idx];
            buffer<expr> zs;
            unsigned saved_fvars_size = m_fvars.size();
            flet<proj2var> save_proj2var(m_proj2var, m_proj2var);
            expr minor_val            = visit(get_minor_body(major, minor, zs), false);
            expr new_minor;
            if (is_join_point_app(minor_val)) {
                buffer<expr> jp_args;
                expr const & jp = get_app_args(minor_val, jp_args);
                expr new_jp     = mk_new_join_point(x, e, jp);
                new_minor       = visit(mk_app(new_jp, jp_args), false);
            } else {
                new_minor       = apply_at(x, e, minor_val);
            }
            new_minor                 = mk_let(zs, saved_fvars_size, new_minor, false);
            new_minor                 = mk_minor_lambda(zs, new_minor);
            c_args[minor_idx]         = new_minor;
        }
        lean_trace(name({"compiler", "simp"}),
                   tout() << "float_cases_on [" << get_lcnf_size(env(), e) << "]\n" << c << "\n----\n" << e << "\n=====>\n"
                   << mk_app(c_fn, c_args) << "\n";);
        return mk_app(c_fn, c_args);
    }

    /* Float cases transformation (see: `float_cases_on_core`).
       This version may create join points if `e` is big, or "good" join-points could not be created. */
    expr float_cases_on(expr const & x, expr const & e, expr const & c) {
        expr new_e = mk_join_point_float_cases_on(x, e, c);
        return float_cases_on_core(x, new_e, c);
    }

    /* Given the buffer `entries`: `[(x_1, w_1), ..., (x_n, w_n)]`, and `e`.
       Create the let-expression
       ```
       let x_n := w_n
           ...
           x_1 := w_1
       in e
       ```
       The values `w_i` are the "simplified values" for the let-declaration `x_i`. */
    expr mk_let_core(buffer<pair<expr, expr>> const & entries, expr e) {
        buffer<expr> fvars;
        buffer<name> user_names;
        buffer<expr> types;
        buffer<expr> vals;
        unsigned i = entries.size();
        while (i > 0) {
            --i;
            expr const & fvar = entries[i].first;
            fvars.push_back(fvar);
            expr const & val  = entries[i].second;
            vals.push_back(val);
            local_decl fvar_decl = m_lctx.get_local_decl(fvar);
            user_names.push_back(fvar_decl.get_user_name());
            types.push_back(fvar_decl.get_type());
        }
        e = abstract(e, fvars.size(), fvars.data());
        i = fvars.size();
        while (i > 0) {
            --i;
            expr new_value = abstract(vals[i], i, fvars.data());
            expr new_type  = abstract(types[i], i, fvars.data());
            e = ::lean::mk_let(user_names[i], new_type, new_value, e);
        }
        return e;
    }

    /* Split `entries` into two groups: `entries_dep_x` and `entries_ndep_x`.
       The first group contains the entries that depend on `x` and the second the ones that doesn't.
       This auxiliary method is used to float cases_on over expressions.

       `entries` is of the form `[(x_1, w_1), ..., (x_n, w_n)]`, where `x_i`s are
       let-decl free variables, and `w_i`s their new values. We use `entries`
       and an expression `e` to create a `let` expression:
       ```
       let x_n := w_n
           ...
           x_1 := w_1
       in e
       ``` */
    void split_entries(buffer<pair<expr, expr>> const & entries,
                       expr const & x,
                       buffer<pair<expr, expr>> & entries_dep_x,
                       buffer<pair<expr, expr>> & entries_ndep_x) {
        if (entries.empty())
            return;
        name_hash_set deps;
        deps.insert(fvar_name(x));
        /* Recall that `entries` are in reverse order. That is, pos 0 is the inner most variable. */
        unsigned i = entries.size();
        while (i > 0) {
            --i;
            expr const & fvar = entries[i].first;
            expr fvar_type    = m_lctx.get_type(fvar);
            expr fvar_new_val = entries[i].second;
            if (depends_on(fvar_type, deps) ||
                depends_on(fvar_new_val, deps)) {
                deps.insert(fvar_name(fvar));
                entries_dep_x.push_back(entries[i]);
            } else {
                entries_ndep_x.push_back(entries[i]);
            }
        }
        std::reverse(entries_dep_x.begin(), entries_dep_x.end());
        std::reverse(entries_ndep_x.begin(), entries_ndep_x.end());
    }

    bool push_dep_jps(expr const & fvar) {
        lean_assert(is_fvar(fvar));
        auto it = m_fvar2jps.find(fvar);
        if (it == m_fvar2jps.end())
            return false;
        buffer<expr> tmp;
        to_buffer(it->second, tmp);
        m_fvar2jps.erase(fvar);
        std::reverse(tmp.begin(), tmp.end());
        m_fvars.append(tmp);
        return true;
    }

    bool push_dep_jps(buffer<expr> const & zs, bool top) {
        buffer<expr> tmp;
        if (top) {
            to_buffer(m_closed_jps, tmp);
            m_closed_jps = exprs();
        }
        for (expr const & z : zs) {
            auto it = m_fvar2jps.find(z);
            if (it != m_fvar2jps.end()) {
                to_buffer(it->second, tmp);
                m_fvar2jps.erase(z);
            }
        }
        if (tmp.empty())
            return false;
        sort_fvars(m_lctx, tmp);
        m_fvars.append(tmp);
        return true;
    }

    void sort_entries(buffer<expr_pair> & entries) {
        std::sort(entries.begin(), entries.end(), [&](expr_pair const & p1, expr_pair const & p2) {
                /* We use `>` because entries in `entries` are in reverse dependency order */
                return m_lctx.get_local_decl(p1.first).get_idx() > m_lctx.get_local_decl(p2.first).get_idx();
            });
    }

    /* Copy `src_entries` and the new joint points that depend on them to `entries`, and update `entries_fvars`.
       This method is used after we perform a `float_cases_on`. */
    void move_to_entries(buffer<expr_pair> const & src_entries, buffer<expr_pair> & entries, name_hash_set & entries_fvars) {
        buffer<expr_pair> todo;
        for (unsigned i = 0; i < src_entries.size(); i++) {
            expr_pair const & entry = src_entries[i];
            /* New join points may have been attached to `ndep_entry` */
            todo.push_back(entry);
            while (!todo.empty()) {
                expr_pair const & curr = todo.back();
                auto it = m_fvar2jps.find(curr.first);
                if (it != m_fvar2jps.end()) {
                    buffer<expr> tmp;
                    to_buffer(it->second, tmp);
                    for (expr const & jp : tmp) {
                        /* Recall that new join points have already been simplified.
                           So, it is ok to move them to `entries`. */
                        todo.emplace_back(jp, *m_lctx.get_local_decl(jp).get_value());
                    }
                    m_fvar2jps.erase(curr.first);
                } else {
                    entries.push_back(curr);
                    collect_used(curr.second, entries_fvars);
                    todo.pop_back();
                }
            }
        }
        /* The following sorting operation is necessary because of non trivial dependencies between entries.
           For example, consider the following scenario. When starting a `float_cases_on` operation, we determine
           that the already processed entries `[_j_1._join, _x_1]` do not depend on the operation.
           Moreover, `_j_1._join` is a new join-point that depends on `_x_1`. Recall that entries are in reverse
           dependecy order, and this is why `_j_1._join` occurs before `_x_1`.
           Then, during the actual execution of the `float_cases_on` operation, we create a new joint point `_j_2._join` that depends on `_j_1._join`,
           and is consequently attached to `_x_1`, that is, `m_fvar2jps[_x_1]` contains `_j_2._join`.
           After executing this procedure, `entries` will contain `[_j_1._join, _j_2._join, _x_1]` which is incorrect
           since `_j_2._join` depends on `_j_1._join`. */
        sort_entries(entries);
    }

    /* Create a let-expression with body `e`, and
       all "used" let-declarations `m_fvars[i]` for `i in [saved_fvars_size, m_fvars.size)`.
       We also include all join points that depends on these free variables,
       nad join points that depends on `zs`. The buffer `zs` (when non empty) contains
       the free variables for a lambda expression that will be created around the let-expression.

       BTW, we also visit the lambda expressions in used let-declarations of the form
       `x : t := fun ...`


       Note that, we don't visit them when we have visit let-expressions. */
    expr mk_let(buffer<expr> const & zs, unsigned saved_fvars_size, expr e, bool top) {
        if (saved_fvars_size == m_fvars.size()) {
            if (!push_dep_jps(zs, top))
                return e;
        }
        /* `entries` contains pairs (let-decl fvar, new value) for building the resultant let-declaration.
           We simplify the value of some let-declarations in this method, but we don't want to create
           a new temporary declaration just for this. */
        buffer<expr_pair> entries;
        name_hash_set e_fvars; /* Set of free variables names used in `e` */
        name_hash_set entries_fvars; /* Set of free variable names used in `entries` */
        collect_used(e, e_fvars);
        bool e_is_cases      = is_cases_on_app(env(), e);
        /*
          Recall that all free variables in `m_fvars` are let-declarations.
          In the following loop, we have the following "order" for the let-declarations:
          ```
             m_fvars[saved_fvars_size]
             ...
             m_fvars[m_fvars.size() - 1]

             entries[entries.size() - 1]
             ...
             entries[0]
          ```
          The "body" of the let-declaration is `e`.
          The mapping `m_fvar2jps` maps a free variable `x to join points that must be inserted after `x`.
        */
        while (true) {
            if (m_fvars.size() == saved_fvars_size) {
                if (!push_dep_jps(zs, top))
                    break;
            }
            lean_assert(m_fvars.size() > saved_fvars_size);
            expr x               = m_fvars.back();
            if (push_dep_jps(x)) {
                /* We must process the join points that depend on `x` before we process `x`. */
                continue;
            }
            m_fvars.pop_back();
            bool used_in_e       = (e_fvars.find(fvar_name(x)) != e_fvars.end());
            bool used_in_entries = (entries_fvars.find(fvar_name(x)) != entries_fvars.end());
            if (!used_in_e && !used_in_entries) {
                /* Skip unused variables */
                continue;
            }
            local_decl x_decl = m_lctx.get_local_decl(x);
            expr type       = x_decl.get_type();
            expr val        = *x_decl.get_value();
            bool is_jp      = false;
            bool modified_val = false;
            if (is_lambda(val)) {
                /* We don't simplify lambdas when we visit `let`-expressions. */
                DEBUG_CODE(unsigned saved_fvars_size = m_fvars.size(););
                is_jp        = is_join_point_name(x_decl.get_user_name());
                val          = visit_lambda(val, is_jp, false);
                modified_val = true;
                lean_assert(m_fvars.size() == saved_fvars_size);
            }

            if (is_lc_unreachable_app(val)) {
                /* `let x := lc_unreachable in e` => `lc_unreachable` */
                e = val;
                e_is_cases = false;
                e_fvars.clear(); entries_fvars.clear();
                collect_used(e, e_fvars);
                entries.clear();
                continue;
            }

            if (entries.empty() && e == x) {
                /* `let x := v in x` ==> `v` */
                e = val;
                collect_used(val, e_fvars);
                e_is_cases = is_cases_on_app(env(), e);
                continue;
            }

            if (is_cases_on_app(env(), val)) {
                /* We first create a let-declaration with all entries that depends on the current
                   `x` which is a cases_on application. */
                buffer<pair<expr, expr>> entries_dep_curr;
                buffer<pair<expr, expr>> entries_ndep_curr;
                split_entries(entries, x, entries_dep_curr, entries_ndep_curr);
                expr new_e = mk_let_core(entries_dep_curr, e);
                e = float_cases_on(x, new_e, val);
                lean_assert(is_cases_on_app(env(), e));
                e_is_cases = true;
                /* Reset `e_fvars` and `entries_fvars`, we need to reconstruct them. */
                e_fvars.clear(); entries_fvars.clear();
                collect_used(e, e_fvars);
                entries.clear();
                /* Copy `entries_ndep_curr` to `entries` */
                move_to_entries(entries_ndep_curr, entries, entries_fvars);
                continue;
            }

            if (!is_jp && e_is_cases && used_in_e) {
                optional<unsigned> minor_idx = used_in_one_minor(e, x);
                if (minor_idx && !used_in_entries) {
                    /* If x is only used in only one minor declaration,
                       and is *not* used in any expression at entries */
                    if (modified_val) {
                        /* We need to create a new free variable since the new
                           simplified value `val` */
                        expr new_x = m_lctx.mk_local_decl(ngen(), x_decl.get_user_name(), type, val);
                        e = replace_fvar(e, x, new_x);
                        x = new_x;
                    }
                    collect_used(type, e_fvars);
                    collect_used(val, e_fvars);
                    e = move_let_to_minor(e, *minor_idx, x);
                    continue;
                }
            }

            collect_used(type, entries_fvars);
            collect_used(val,  entries_fvars);
            entries.emplace_back(x, val);
        }
        return mk_let_core(entries, e);
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
                if (is_internal_name(n)) {
                    if (is_join_point_name(n))
                        n = next_jp_name();
                    else
                        n = next_name();
                }
                expr new_fvar = m_lctx.mk_local_decl(ngen(), n, new_type, new_val);
                let_fvars.push_back(new_fvar);
                m_fvars.push_back(new_fvar);
            }
            e = let_body(e);
        }
        return visit(instantiate_rev(e, let_fvars.size(), let_fvars.data()), false);
    }

    /* - `is_join_point_def` is true if the lambda is the value of a join point.
       - `root` is true if the lambda is the value of a definition. */
    expr visit_lambda(expr e, bool is_join_point_def, bool top) {
        lean_assert(is_lambda(e));
        lean_assert(!top || m_fvars.size() == 0);
        lean_assert(!top || !already_simplified(e));
        if (already_simplified(e))
            return e;
        buffer<expr> binding_fvars;
        while (is_lambda(e)) {
            /* Types are ignored in compilation steps. So, we do not invoke visit for d. */
            expr new_d    = instantiate_rev(binding_domain(e), binding_fvars.size(), binding_fvars.data());
            expr new_fvar = m_lctx.mk_local_decl(ngen(), binding_name(e), new_d, binding_info(e));
            binding_fvars.push_back(new_fvar);
            e = binding_body(e);
        }
        e = instantiate_rev(e, binding_fvars.size(), binding_fvars.data());
        /* When we simplify before erasure, we eta-expand all lambdas which are not join points. */
        buffer<expr> eta_args;
        if (m_before_erasure && !is_join_point_def) {
            expr e_type = whnf_infer_type(e);
            while (is_pi(e_type)) {
                expr arg = m_lctx.mk_local_decl(ngen(), binding_name(e_type), binding_domain(e_type), binding_info(e_type));
                eta_args.push_back(arg);
                e_type = whnf(instantiate(binding_body(e_type), arg));
            }
        }
        unsigned saved_fvars_size = m_fvars.size();
        expr new_body             = visit(e, false);
        if (!eta_args.empty()) {
            if (is_join_point_app(new_body)) {
                /* Remark: we cannot simply set
                   ```
                   new_body = mk_app(new_body, eta_args);
                   ```
                   when `new_body` is a join-point, because the result will not be a valid LCNF term.
                   We could expand the join-point, but it this will create a copy.
                   So, for now, we simply avoid eta-expansion.
                */
                eta_args.clear();
            } else {
                if (is_lcnf_atom(new_body)) {
                    new_body = mk_app(new_body, eta_args);
                } else if (is_app(new_body) && !is_cases_on_app(env(), new_body)) {
                    new_body = mk_app(new_body, eta_args);
                } else {
                    expr f   = mk_let_decl(new_body);
                    new_body = mk_app(f, eta_args);
                }
                new_body = visit(new_body, false);
            }
            binding_fvars.append(eta_args);
        }
        new_body      = mk_let(binding_fvars, saved_fvars_size, new_body, top);
        expr r;
        if (is_join_point_def) {
            lean_assert(eta_args.empty());
            r = mk_join_point_lambda(binding_fvars, new_body);
        } else {
            r = m_lctx.mk_lambda(binding_fvars, new_body);
        }
        mark_simplified(r);
        return r;
    }

    /* Auxiliary method for `beta_reduce` and `beta_reduce_if_not_cases` */
    expr beta_reduce_cont(expr r, unsigned i, unsigned nargs, expr const * args, bool is_let_val) {
        r = visit(r, false);
        if (i == nargs)
            return r;
        lean_assert(i < nargs);
        if (is_join_point_app(r)) {
            /* Expand join-point */
            lean_assert(!is_let_val);
            buffer<expr> new_args;
            expr const & jp = get_app_args(r, new_args);
            lean_assert(is_fvar(jp));
            for (; i < nargs; i++)
                new_args.push_back(args[i]);
            expr jp_val     = *m_lctx.get_local_decl(jp).get_value();
            lean_assert(is_lambda(jp_val));
            return beta_reduce(jp_val, new_args.size(), new_args.data(), false);
        } else {
            if (!is_lcnf_atom(r))
                r = mk_let_decl(r);
            return visit(mk_app(r, nargs - i, args + i), is_let_val);
        }
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
            return beta_reduce_cont(r, i, nargs, args, is_let_val);
        }
    }

    /* Remark: if `fn` is not a lambda expression, then this function
       will simply create the application `fn args_of(e)` */
    expr beta_reduce(expr fn, expr const & e, bool is_let_val) {
        buffer<expr> args;
        get_app_args(e, args);
        return beta_reduce(fn, args.size(), args.data(), is_let_val);
    }

    bool should_inline_instance(name const & n) const {
        if (is_instance(env(), n))
            return !has_noinline_attribute(env(), n);
        else
            return false;
    }

    optional<expr> try_inline_instance(expr const & fn, expr const & e) {
        if (!m_before_erasure)
            return none_expr();
        if (!is_constant(fn) || !should_inline_instance(const_name(fn)))
            return none_expr();
        lean_assert(is_constant(fn));
        optional<constant_info> info = env().find(mk_cstage1_name(const_name(fn)));
        if (!info || !info->is_definition()) return none_expr();
        if (get_app_num_args(e) < get_num_nested_lambdas(info->get_value())) return none_expr();
        unsigned  saved_fvars_size = m_fvars.size();
        expr new_fn = instantiate_value_lparams(*info, const_levels(fn));
        expr r      = find(beta_reduce(new_fn, e, false));
        if (is_constructor_app(env(), r)) {
            return some_expr(r);
        } else if (optional<expr> new_r = try_inline_instance(get_app_fn(r), r)) {
            return new_r;
        } else {
            lean_trace(name({"compiler", "erase_irrelevant"}), tout() << ">> r: " << r << "\n";);
            m_fvars.resize(saved_fvars_size);
            return none_expr();
        }
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
        if (optional<expr> k_app = try_inline_instance(s_fn, s))
            return visit(proj_constructor(*k_app, proj_idx(e).get_small_value()), is_let_val);
        if (proj_idx(e).is_small()) {
            if (expr const * x = m_proj2var.find(mk_pair(s, proj_idx(e).get_small_value())))
                return *x;
        }
        expr new_arg = visit_arg(proj_expr(e));
        if (is_eqp(proj_expr(e), new_arg))
            return e;
        else
            return update_proj(e, new_arg);
    }

    expr reduce_cases_cnstr(buffer<expr> const & args, inductive_val const & I_val, expr const & major, bool is_let_val) {
        lean_assert(is_constructor_app(env(), major));
        unsigned nparams = I_val.get_nparams();
        buffer<expr> k_args;
        expr const & k   = get_app_args(major, k_args);
        lean_assert(is_constant(k));
        lean_assert(nparams <= k_args.size());
        unsigned first_minor_idx = m_before_erasure ? (nparams + 1 /* typeformer/motive */ + I_val.get_nindices() + 1 /* major */) : 1;
        constructor_val k_val = env().get(const_name(k)).to_constructor_val();
        expr const & minor    = args[first_minor_idx + k_val.get_cidx()];
        return beta_reduce(minor, k_args.size() - nparams, k_args.data() + nparams, is_let_val);
    }

    /* Just simplify minor premises. */
    expr visit_cases_default(expr const & e) {
        if (already_simplified(e))
            return e;
        lean_assert(is_cases_on_app(env(), e));
        buffer<expr> args;
        expr const & c = get_app_args(e, args);
        /* simplify minor premises */
        unsigned minor_idx; unsigned minors_end;
        std::tie(minor_idx, minors_end) = get_cases_on_minors_range(env(), const_name(c), m_before_erasure);
        expr const & major = args[minor_idx-1];
        for (; minor_idx < minors_end; minor_idx++) {
            expr minor                = args[minor_idx];
            unsigned saved_fvars_size = m_fvars.size();
            flet<proj2var> save_proj2var(m_proj2var, m_proj2var);
            buffer<expr> zs;
            minor          = get_minor_body(major, minor, zs);
            expr new_minor = visit(minor, false);
            new_minor = mk_let(zs, saved_fvars_size, new_minor, false);
            new_minor = mk_minor_lambda(zs, new_minor);
            args[minor_idx] = new_minor;
        }
        expr r = mk_app(c, args);
        mark_simplified(r);
        return r;
    }

    expr visit_cases(expr const & e, bool is_let_val) {
        buffer<expr> args;
        expr const & c = get_app_args(e, args);
        lean_assert(is_constant(c));
        inductive_val I_val      = get_cases_on_inductive_val(env(), c);
        unsigned major_idx       = get_cases_on_major_idx(env(), const_name(c), m_before_erasure);
        lean_assert(major_idx < args.size());
        expr major               = find(args[major_idx]);
        if (is_nat_lit(major))
            major = nat_lit_to_constructor(major);
        if (is_constructor_app(env(), major)) {
            return reduce_cases_cnstr(args, I_val, major, is_let_val);
        } else if (!is_let_val) {
            return visit_cases_default(e);
        } else {
            return e;
        }
    }

    expr merge_app_app(expr const & fn, expr const & e, bool is_let_val) {
        lean_assert(is_app(fn));
        lean_assert(is_eqp(find(get_app_fn(e)), fn));
        lean_assert(!is_join_point_app(fn));
        if (!is_cases_on_app(env(), fn)) {
            buffer<expr> args;
            get_app_args(e, args);
            return visit_app(mk_app(fn, args), is_let_val);
        } else {
            return e;
        }
    }

    /* We don't inline recursive functions.
       TODO(Leo): this predicate does not handle mutual recursion.
       We need a better solution. Example: we tag which definitions are recursive when we create them. */
    bool is_recursive(name const & c) {
        constant_info info = env().get(c);
        return static_cast<bool>(::lean::find(info.get_value(), [&](expr const & e, unsigned) {
                    return is_constant(e) && const_name(e) == c.get_prefix();
                }));
    }

    bool uses_unsafe_inductive(name const & c) {
        constant_info info = env().get(c);
        return static_cast<bool>(::lean::find(info.get_value(), [&](expr const & e, unsigned) {
                    if (!is_constant(e) || !is_cases_on_recursor(env(), const_name(e))) return false;
                    name const & I = const_name(e).get_prefix();
                    constant_info I_cinfo = env().get(I);
                    return I_cinfo.is_unsafe();
                }));
    }

    bool is_stuck_at_cases(expr e) {
        type_checker tc(m_st, m_lctx);
        while (true) {
            bool cheap = true;
            expr e1 = tc.whnf_core(e, cheap);
            expr const & fn = get_app_fn(e1);
            if (!is_constant(fn)) return false;
            if (is_recursor(env(), const_name(fn))) return true;
            if (!is_cases_on_recursor(env(), const_name(fn))) return false;
            auto next_e = tc.unfold_definition(e1);
            if (!next_e) return true;
            e = *next_e;
        }
    }

    optional<expr> beta_reduce_if_not_cases(expr fn, unsigned nargs, expr const * args, bool is_let_val) {
        unsigned i = 0;
        while (is_lambda(fn) && i < nargs) {
            i++;
            fn = binding_body(fn);
        }
        expr r = instantiate_rev(fn, i, args);
        if (is_lambda(r) || is_stuck_at_cases(r)) return none_expr();
        return some_expr(beta_reduce_cont(r, i, nargs, args, is_let_val));
    }

    /* Auxiliary method used to inline functions marked with `[inline_if_reduce]`. It is similar to `beta_reduce`
       but it fails if the head is a `cases_on` application after `whnf_core`. */
    optional<expr> beta_reduce_if_not_cases(expr fn, expr const & e, bool is_let_val) {
        buffer<expr> args;
        get_app_args(e, args);
        return beta_reduce_if_not_cases(fn, args.size(), args.data(), is_let_val);
    }

    bool check_noinline_attribute(name const & n) {
        if (!has_noinline_attribute(env(), n)) return false;
        /* Even if the function has `@[noinline]` attribute, we must still inline if its arguments
           were reduced by `reduce_arity`. This should only be checked after erasure. */
        if (m_before_erasure) return true;
        name c = mk_cstage2_name(n);
        optional<constant_info> info = env().find(c);
        if (!info || !info->is_definition()) return true;
        return !arity_was_reduced(comp_decl(n, info->get_value()));
    }

    optional<expr> try_inline(expr const & fn, expr const & e, bool is_let_val) {
        lean_assert(is_constant(fn));
        lean_assert(is_constant(e) || is_eqp(find(get_app_fn(e)), fn));
        if (!m_cfg.m_inline) return none_expr();
        if (check_noinline_attribute(const_name(fn))) return none_expr();
        if (m_before_erasure) {
            if (already_simplified(e)) return none_expr();
            name c = mk_cstage1_name(const_name(fn));
            optional<constant_info> info = env().find(c);
            if (!info || !info->is_definition()) return none_expr();
            if (get_app_num_args(e) < get_num_nested_lambdas(info->get_value())) return none_expr();
            bool inline_attr           = has_inline_attribute(env(), const_name(fn));
            bool inline_if_reduce_attr = has_inline_if_reduce_attribute(env(), const_name(fn));
            if (!inline_attr && !inline_if_reduce_attr &&
                (get_lcnf_size(env(), info->get_value()) > m_cfg.m_inline_threshold ||
                 is_constant(e))) { /* We only inline constants if they are marked with the `[inline]` or `[inline_if_reduce]` attrs */
                return none_expr();
            }
            if (!inline_if_reduce_attr && is_recursive(c)) return none_expr();
            if (uses_unsafe_inductive(c)) return none_expr();
            expr new_fn = instantiate_value_lparams(*info, const_levels(fn));
            if (inline_if_reduce_attr && !inline_attr) {
                return beta_reduce_if_not_cases(new_fn, e, is_let_val);
            } else {
                return some_expr(beta_reduce(new_fn, e, is_let_val));
            }
        } else {
            if (is_constant(e)) return none_expr(); /* We don't inline constants after erasure */
            name c = mk_cstage2_name(const_name(fn));
            optional<constant_info> info = env().find(c);
            if (!info || !info->is_definition()) return none_expr();
            unsigned arity = get_num_nested_lambdas(info->get_value());
            if (arity == 0 || get_app_num_args(e) < arity) return none_expr();
            if (get_lcnf_size(env(), info->get_value()) > m_cfg.m_inline_threshold) return none_expr();
            if (is_recursive(c)) return none_expr();
            if (uses_unsafe_inductive(c)) return none_expr();
            return some_expr(beta_reduce(info->get_value(), e, is_let_val));
        }
    }

    expr visit_inline_app(expr const & e, bool is_let_val) {
        buffer<expr> args;
        get_app_args(e, args);
        lean_assert(!args.empty());
        if (args.size() < 2)
            return visit_app_default(e);
        buffer<expr> new_args;
        expr fn = get_app_args(find(args[1]), new_args);
        new_args.append(args.size() - 2, args.data() + 2);
        expr r  = mk_app(fn, new_args);
        if (!m_cfg.m_inline || !is_constant(fn))
            return visit(r, is_let_val);
        name main  = const_name(fn);
        bool first = true;
        while (true) {
            name c = mk_cstage1_name(const_name(fn));
            optional<constant_info> info = env().find(c);
            if (!info || !info->is_definition())
                return first ? visit(r, is_let_val) : r;
            expr new_fn = instantiate_value_lparams(*info, const_levels(fn));
            r = beta_reduce(new_fn, new_args.size(), new_args.data(), is_let_val);
            if (!is_app(r)) return r;
            fn = get_app_fn(r);
            /* If `r` is an application of the form `g ...` where
               `g` is an interal name and `g` prefix of the main function, we unfold this
               application too. */
            if (!is_constant(fn) || !is_internal_name(const_name(fn)) ||
                const_name(fn).get_prefix() != main)
                return r;
            new_args.clear();
            get_app_args(r, new_args);
            first = false;
        }
    }

    expr visit_app_default(expr const & e) {
        if (already_simplified(e)) return e;
        buffer<expr> args;
        bool modified   = true;
        expr const & fn = get_app_args(e, args);
        for (expr & arg : args) {
            expr new_arg = visit_arg(arg);
            if (!is_eqp(arg, new_arg))
                modified = true;
            arg = new_arg;
        }
        expr new_e = modified ? mk_app(fn, args) : e;
        mark_simplified(new_e);
        return new_e;
    }

    expr visit_nat_succ(expr const & e) {
        expr arg = visit(app_arg(e), false);
        return mk_app(mk_constant(get_nat_add_name()), arg, mk_lit(literal(nat(1))));
    }

    /*
      Replace `fixCore<n> f a_1 ... a_m`
      with `fixCore<m> f a_1 ... a_m` whenever `n < m`.
      This optimization is for writing reusable/generic code. For
      example, we cannot write an efficient `rec_t` monad transformer
      without it because we don't know the arity of `m A` when we write `rec_t`.
      Remark: the runtime provides a small set of `fixCore<i>` implementations (`i in [1, 6]`).
      This methods does nothing if `m > 6`. */
    expr visit_fix_core(expr const & e, unsigned n) {
        if (m_before_erasure) return visit_app_default(e);
        buffer<expr> args;
        expr fn = get_app_args(e, args);
        lean_assert(is_constant(fn) && is_fix_core(const_name(fn)));
        unsigned arity =
            n + /* α_1 ... α_n Type arguments */
            1 + /* β : Type */
            1 + /* (base : α_1 → ... → α_n → β) */
            1 + /* (rec : (α_1 → ... → α_n → β) → α_1 → ... → α_n → β) */
            n; /* α_1 → ... → α_n */
        if (args.size() <= arity) return visit_app_default(e);
        /* This `fixCore<n>` application is an overapplication.
           The `fixCore<n>` is implemented by the runtime, and the result
           is a closure. This is bad for performance. We should
           replace it with `fixCore<m>` (if the runtime contains one) */
        unsigned num_extra = args.size() - arity;
        unsigned m = n + num_extra;
        optional<expr> fix_core_m = mk_enf_fix_core(m);
        if (!fix_core_m) return visit_app_default(e);
        buffer<expr> new_args;
        /* Add α_1 ... α_n and β */
        for (unsigned i = 0; i < m+1; i++) {
            new_args.push_back(mk_enf_neutral());
        }
        /* `(base : α_1 → ... → α_n → β)` is not used in the runtime primitive.
           So, we replace it with a neutral value :) */
        new_args.push_back(mk_enf_neutral());
        new_args.append(args.size() - n - 2, args.data() + n + 2);
        return mk_app(*fix_core_m, new_args);
    }

    expr visit_app(expr const & e, bool is_let_val) {
        if (is_cases_on_app(env(), e)) {
            return visit_cases(e, is_let_val);
        } else if (is_app_of(e, get_inline_name())) {
            return visit_inline_app(e, is_let_val);
        }
        expr fn = find(get_app_fn(e));
        if (is_lambda(fn)) {
            return beta_reduce(fn, e, is_let_val);
        } else if (is_cases_on_app(env(), fn)) {
            expr new_e = float_cases_on_core(get_app_fn(e), e, fn);
            mark_simplified(new_e);
            return new_e;
        } else if (is_lc_unreachable_app(fn)) {
            lean_assert(m_before_erasure);
            expr type = infer_type(e);
            return mk_lc_unreachable(m_st, m_lctx, type);
        } else if (is_app(fn)) {
            return merge_app_app(fn, e, is_let_val);
        } else if (is_constant(fn)) {
            unsigned nargs = get_app_num_args(e);
            if (nargs == 1) {
                expr a1 = find(app_arg(e));
                if (optional<expr> r = fold_un_op(m_before_erasure, fn, a1)) {
                    return *r;
                }
            } else if (nargs == 2) {
                expr a1 = find(app_arg(app_fn(e)));
                expr a2 = find(app_arg(e));
                if (optional<expr> r = fold_bin_op(m_before_erasure, fn, a1, a2)) {
                    return *r;
                }
            }
            name const & n = const_name(fn);
            if (n == get_nat_succ_name()) {
                return visit_nat_succ(e);
            } else if (n == get_nat_zero_name()) {
                return mk_lit(literal(nat(0)));
            } else if (optional<expr> r = try_inline(fn, e, is_let_val)) {
                return *r;
            } else if (optional<unsigned> i = is_fix_core(n)) {
                return visit_fix_core(e, *i);
            } else {
                return visit_app_default(e);
            }
        } else {
            return visit_app_default(e);
        }
    }

    expr visit_constant(expr const & e, bool is_let_val) {
        if (optional<expr> r = try_inline(e, e, is_let_val))
            return *r;
        else
            return e;
    }

    expr visit_arg(expr const & e) {
        if (!is_lcnf_atom(e)) {
            /* non-atomic arguments are irrelevant in LCNF */
            return e;
        }
        expr new_e = visit(e, false);
        if (is_lcnf_atom(new_e))
            return new_e;
        else
            return mk_let_decl(new_e);
    }

    expr visit(expr const & e, bool is_let_val) {
        switch (e.kind()) {
        case expr_kind::Lambda: return is_let_val ? e : visit_lambda(e, false, false);
        case expr_kind::Let:    return visit_let(e);
        case expr_kind::Proj:   return visit_proj(e, is_let_val);
        case expr_kind::App:    return visit_app(e, is_let_val);
        case expr_kind::Const:  return visit_constant(e, is_let_val);
        default:                return e;
        }
    }

public:
    csimp_fn(environment const & env, local_ctx const & lctx, bool before_erasure, csimp_cfg const & cfg):
        m_st(env), m_lctx(lctx), m_before_erasure(before_erasure), m_cfg(cfg), m_x("_x"), m_j("j") {}

    expr operator()(expr const & e) {
        if (is_lambda(e)) {
            return visit_lambda(e, false, true);
        } else {
            buffer<expr> empty_xs;
            expr r = visit(e, false);
            return mk_let(empty_xs, 0, r, true);
        }
    }
};

uint8 at_most_once_core(obj_arg e, obj_arg x);

bool at_most_once(expr const & e, name const & x) {
    inc_ref(e.raw()); inc_ref(x.raw());
    return at_most_once_core(e.raw(), x.raw());
}

/* Eliminate join-points that are used only once */
class elim_jp1_fn {
    environment const & m_env;
    local_ctx           m_lctx;
    bool                m_before_erasure;
    name_generator      m_ngen;
    name_set            m_to_expand;
    bool                m_expanded{false};

    void mark_to_expand(expr const & e) {
        m_to_expand.insert(fvar_name(e));
    }

    bool is_to_expand_jp_app(expr const & e) {
        expr const & f = get_app_fn(e);
        return is_fvar(f) && m_to_expand.contains(fvar_name(f));
    }

    expr visit_lambda(expr e) {
        buffer<expr> fvars;
        while (is_lambda(e)) {
            expr domain     = visit(instantiate_rev(binding_domain(e), fvars.size(), fvars.data()));
            expr fvar       = m_lctx.mk_local_decl(m_ngen, binding_name(e), domain, binding_info(e));
            fvars.push_back(fvar);
            e = binding_body(e);
        }
        e = visit(instantiate_rev(e, fvars.size(), fvars.data()));
        return m_lctx.mk_lambda(fvars, e);
    }

    expr visit_cases(expr const & e) {
        lean_assert(is_cases_on_app(m_env, e));
        buffer<expr> args;
        expr const & c = get_app_args(e, args);
        /* simplify minor premises */
        unsigned minor_idx; unsigned minors_end;
        std::tie(minor_idx, minors_end) = get_cases_on_minors_range(m_env, const_name(c), m_before_erasure);
        for (; minor_idx < minors_end; minor_idx++) {
            args[minor_idx] = visit(args[minor_idx]);
        }
        return mk_app(c, args);
    }

    expr visit_app(expr const & e) {
        lean_assert(is_app(e));
        if (is_cases_on_app(m_env, e)) {
            return visit_cases(e);
        } else if (is_to_expand_jp_app(e)) {
            buffer<expr> args;
            expr const & jp    = get_app_rev_args(e, args);
            local_decl jp_decl = m_lctx.get_local_decl(jp);
            lean_assert(is_join_point_name(jp_decl.get_user_name()));
            lean_assert(jp_decl.get_value());
            lean_assert(is_lambda(*jp_decl.get_value()));
            return apply_beta(*jp_decl.get_value(), args.size(), args.data());
        } else {
            return e;
        }
    }

    bool at_most_once(expr const & e, expr const & jp) {
        lean_assert(is_fvar(jp));
        return lean::at_most_once(e, fvar_name(jp));
    }

    expr visit_let(expr e) {
        buffer<expr> fvars;
        buffer<expr> all_fvars;
        while (is_let(e)) {
            expr new_type = visit(instantiate_rev(let_type(e), fvars.size(), fvars.data()));
            expr new_val  = visit(instantiate_rev(let_value(e), fvars.size(), fvars.data()));
            expr fvar     = m_lctx.mk_local_decl(m_ngen, let_name(e), new_type, new_val);
            fvars.push_back(fvar);
            if (is_join_point_name(let_name(e))) {
                e = instantiate_rev(let_body(e), fvars.size(), fvars.data());
                fvars.clear();
                if (at_most_once(e, fvar)) {
                    m_expanded = true;
                    mark_to_expand(fvar);
                } else {
                    /* Keep join point */
                    all_fvars.push_back(fvar);
                }
            } else {
                all_fvars.push_back(fvar);
                e = let_body(e);
            }
        }
        e = instantiate_rev(e, fvars.size(), fvars.data());
        e = visit(e);
        return m_lctx.mk_lambda(all_fvars, e);
    }

    expr visit(expr const & e) {
        switch (e.kind()) {
        case expr_kind::Lambda: return visit_lambda(e);
        case expr_kind::Let:    return visit_let(e);
        case expr_kind::App:    return visit_app(e);
        default:                return e;
        }
    }

public:
    elim_jp1_fn(environment const & env, local_ctx const & lctx, bool before_erasure):
        m_env(env), m_lctx(lctx), m_before_erasure(before_erasure) {}
    expr operator()(expr const & e) {
        m_expanded = false;
        return visit(e);
    }

    bool expanded() const { return m_expanded; }
};

expr csimp_core(environment const & env, local_ctx const & lctx, expr const & e0, bool before_erasure, csimp_cfg const & cfg) {
    csimp_fn simp(env, lctx, before_erasure, cfg);
    elim_jp1_fn elim_jp1(env, lctx, before_erasure);
    expr e = e0;
    while (true) {
        e = simp(e);
        e = elim_jp1(e);
        if (!elim_jp1.expanded())
            return e;
    }
}
}
