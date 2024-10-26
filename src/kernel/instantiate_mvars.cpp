/*
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura
*/
#include <vector>
#include <unordered_map>
#include "util/name_set.h"
#include "runtime/option_ref.h"
#include "runtime/array_ref.h"
#include "runtime/sharecommon.h"
#include "kernel/instantiate.h"
#include "kernel/replace_fn.h"
#include "kernel/for_each_fn.h"

/*
This module is not used by the kernel. It just provides an efficient implementation of
`instantiateExprMVars`
*/

namespace lean {
extern "C" object * lean_get_lmvar_assignment(obj_arg mctx, obj_arg mid);
extern "C" object * lean_assign_lmvar(obj_arg mctx, obj_arg mid, obj_arg val);

typedef object_ref metavar_ctx;
void assign_lmvar(metavar_ctx & mctx, name const & mid, level const & l) {
    object * r = lean_assign_lmvar(mctx.steal(), mid.to_obj_arg(), l.to_obj_arg());
    mctx.set_box(r);
}

option_ref<level> get_lmvar_assignment(metavar_ctx & mctx, name const & mid) {
    return option_ref<level>(lean_get_lmvar_assignment(mctx.to_obj_arg(), mid.to_obj_arg()));
}

class instantiate_lmvars_fn {
    metavar_ctx & m_mctx;
    std::unordered_map<lean_object *, level> m_cache;
    std::vector<level> m_saved; // Helper vector to prevent values from being garbage collected

    inline level cache(level const & l, level r, bool shared) {
        if (shared) {
            m_cache.insert(mk_pair(l.raw(), r));
        }
        return r;
    }
public:
    instantiate_lmvars_fn(metavar_ctx & mctx):m_mctx(mctx) {}
    level visit(level const & l) {
        if (!has_mvar(l))
            return l;
        bool shared = false;
        if (is_shared(l)) {
            auto it = m_cache.find(l.raw());
            if (it != m_cache.end()) {
                return it->second;
            }
            shared = true;
        }
        switch (l.kind()) {
        case level_kind::Succ:
            return cache(l, update_succ(l, visit(succ_of(l))), shared);
        case level_kind::Max: case level_kind::IMax:
            return cache(l, update_max(l, visit(level_lhs(l)), visit(level_rhs(l))), shared);
        case level_kind::Zero: case level_kind::Param:
            lean_unreachable();
        case level_kind::MVar: {
            option_ref<level> r = get_lmvar_assignment(m_mctx, mvar_id(l));
            if (!r) {
                return l;
            } else {
                level a(r.get_val());
                if (!has_mvar(a)) {
                    return a;
                } else {
                    level a_new = visit(a);
                    if (!is_eqp(a, a_new)) {
                        /*
                        We save `a` to ensure it will not be garbage collected
                        after we update `mctx`. This is necessary because `m_cache`
                        may contain references to its subterms.
                        */
                        m_saved.push_back(a);
                        assign_lmvar(m_mctx, mvar_id(l), a_new);
                    }
                    return a_new;
                }
            }
        }}
    }
    level operator()(level const & l) { return visit(l); }
};

extern "C" LEAN_EXPORT object * lean_instantiate_level_mvars(object * m, object * l) {
    metavar_ctx mctx(m);
    level l_new = instantiate_lmvars_fn(mctx)(level(l));
    object * r = alloc_cnstr(0, 2, 0);
    cnstr_set(r, 0, mctx.steal());
    cnstr_set(r, 1, l_new.steal());
    return r;
}

extern "C" object * lean_get_mvar_assignment(obj_arg mctx, obj_arg mid);
extern "C" object * lean_get_delayed_mvar_assignment(obj_arg mctx, obj_arg mid);
extern "C" object * lean_assign_mvar(obj_arg mctx, obj_arg mid, obj_arg val);
typedef object_ref delayed_assignment;

void assign_mvar(metavar_ctx & mctx, name const & mid, expr const & e) {
    object * r = lean_assign_mvar(mctx.steal(), mid.to_obj_arg(), e.to_obj_arg());
    mctx.set_box(r);
}

option_ref<expr> get_mvar_assignment(metavar_ctx & mctx, name const & mid) {
    return option_ref<expr>(lean_get_mvar_assignment(mctx.to_obj_arg(), mid.to_obj_arg()));
}

option_ref<delayed_assignment> get_delayed_mvar_assignment(metavar_ctx & mctx, name const & mid) {
    return option_ref<delayed_assignment>(lean_get_delayed_mvar_assignment(mctx.to_obj_arg(), mid.to_obj_arg()));
}

static size_t g_replace_visited = 0;
static size_t g_lift_visited = 0;

expr lift_loose_bvars2(expr const & e, unsigned s, unsigned d) {
    if (d == 0 || s >= get_loose_bvar_range(e))
        return e;
    return replace(e, [=](expr const & e, unsigned offset) -> optional<expr> {
            unsigned s1 = s + offset;
            if (s1 < s)
                return some_expr(e); // overflow, vidx can't be >= max unsigned
            if (s1 >= get_loose_bvar_range(e))
                return some_expr(e); // expression e does not contain bound variables with idx >= s1
            g_lift_visited++;
            if (is_var(e) && bvar_idx(e) >= s + offset) {
                return some_expr(mk_bvar(bvar_idx(e) + nat(d)));
            } else {
                return none_expr();
            }
        });
}

class replace_fvars_fn {
    struct cache_hash_fn {
        std::size_t operator()(std::pair<expr, unsigned> const & p) const {
            return hash(((size_t)p.first.raw()) >> 3, p.second);
        }
    };
    struct cache_eq_fn {
        bool operator()(std::pair<expr, unsigned> const & p1, std::pair<expr, unsigned> const & p2) const {
            return p1.first.raw() == p2.first.raw() && p1.second == p2.second;
        }
    };
    struct fv_map_hash_fn {
        std::size_t operator()(expr const & e) const { return ((size_t)e.raw()) >> 3; }
    };
    struct fv_map_eq_fn {
        bool operator()(expr const & e1, expr const & e2) const { return e1.raw() == e2.raw(); }
    };

    typedef uint64 fv_set;

    std::unordered_map<std::pair<expr, unsigned>, expr, cache_hash_fn, cache_eq_fn> m_cache;
    std::unordered_map<expr, fv_set, fv_map_hash_fn, fv_map_eq_fn> m_fv_map;
    unsigned m_num_fvars;
    array_ref<expr> const * m_fvars;
    expr const * m_rev_args;
    std::vector<fv_set> m_rev_arg_fv_sets;
    fv_set m_target;

    expr save_result(expr const & e, unsigned offset, expr r, bool shared) {
        if (shared)
            m_cache.insert(mk_pair(mk_pair(e, offset), r));
        return r;
    }

    static fv_set to_fv_set(name const & n) {
        return 1 << (n.hash() & 63);
    }

    bool fv_map_contains(expr const & e) const {
        return m_fv_map.find(e) != m_fv_map.end();
    }

    bool may_contain_target(expr const &  e) const {
        if (!has_fvar(e))
            return false;
        switch (e.kind()) {
        case expr_kind::Const: case expr_kind::Sort:
        case expr_kind::BVar:  case expr_kind::Lit:
        case expr_kind::MVar:
            lean_unreachable();
        case expr_kind::FVar:
            return (to_fv_set(fvar_name(e)) & m_target) != 0;
        default: {
            auto it = m_fv_map.find(e);
            if (it != m_fv_map.end())
                return (it->second & m_target) != 0;
            else
                return true; // we don't have a cached approximation yet.
        }}
        lean_unreachable();
    }

    fv_set get_fv_set(expr const & e) {
        if (!has_fvar(e)) return 0;
        switch (e.kind()) {
        case expr_kind::Const: case expr_kind::Sort:
        case expr_kind::BVar:  case expr_kind::Lit:
        case expr_kind::MVar:
            return 0;
        case expr_kind::FVar:
            return to_fv_set(fvar_name(e));
        default: {
            auto it = m_fv_map.find(e);
            lean_assert(it != m_fv_map.end());
            return it->second;
        }}
    }

    void update_fv(expr const & e, fv_set s) {
        m_fv_map.insert(mk_pair(e, s));
    }

    void update_fv(expr const & e, expr const & c) {
        update_fv(e, get_fv_set(c));
    }

    void update_fv(expr const & e, expr const & c1, expr const & c2) {
        update_fv(e, get_fv_set(c1) | get_fv_set(c2));
    }

    void update_fv(expr const & e, expr const & c1, expr const & c2, expr const  & c3) {
        update_fv(e, get_fv_set(c1) | get_fv_set(c2) | get_fv_set(c3));
    }

    expr apply(expr const & e, unsigned offset) {
        if (!may_contain_target(e))
            return e;
        g_replace_visited++;
        bool shared = false;
        if (is_shared(e)) {
            auto it = m_cache.find(mk_pair(e, offset));
            if (it != m_cache.end())
                return it->second;
            shared = true;
        }

        switch (e.kind()) {
        case expr_kind::Const: case expr_kind::Sort:
        case expr_kind::BVar:  case expr_kind::Lit:
        case expr_kind::MVar:
            lean_unreachable();
        case expr_kind::FVar: {
            size_t i = m_num_fvars;
            lean_assert(m_num_fvars == m_fvars->size());
            name const & n = fvar_name(e);
            while (i > 0) {
                --i;
                if (fvar_name((*m_fvars)[i]) == n) {
                    // Recall that `lift_loose_bvars` does not change the set of free variables.
                    // So, we can use set cached for `m_rev_args[m_num_fvars - i - 1]`
                    expr r = lift_loose_bvars(m_rev_args[m_num_fvars - i - 1], offset);
                    update_fv(r, m_rev_arg_fv_sets[m_num_fvars - i - 1]);
                    return save_result(e, offset, r, shared);
                }
            }
            return save_result(e, offset, e, shared);
        }
        case expr_kind::MData: {
            expr new_c = apply(mdata_expr(e), offset);
            expr new_e = update_mdata(e, new_c);
            update_fv(new_e, new_c);
            return save_result(e, offset, new_e, shared);
        }
        case expr_kind::Proj: {
            expr new_c = apply(proj_expr(e), offset);
            expr new_e = update_proj(e, new_c);
            update_fv(new_e, new_c);
            return save_result(e, offset, new_e, shared);
        }
        case expr_kind::App: {
            expr new_f = apply(app_fn(e), offset);
            expr new_a = apply(app_arg(e), offset);
            expr new_e = update_app(e, new_f, new_a);
            update_fv(new_e, new_f, new_a);
            return save_result(e, offset, new_e, shared);
        }
        case expr_kind::Pi: case expr_kind::Lambda: {
            expr new_d = apply(binding_domain(e), offset);
            expr new_b = apply(binding_body(e), offset+1);
            expr new_e = update_binding(e, new_d, new_b);
            update_fv(new_e, new_d, new_b);
            return save_result(e, offset, new_e, shared);
        }
        case expr_kind::Let: {
            expr new_t = apply(let_type(e), offset);
            expr new_v = apply(let_value(e), offset);
            expr new_b = apply(let_body(e), offset+1);
            expr new_e = update_let(e, new_t, new_v, new_b);
            update_fv(new_e, new_t, new_v, new_b);
            return save_result(e, offset, new_e, shared);
        }}
        lean_unreachable();
    }

    fv_set init_fv_map(expr const & e) {
        if (!has_fvar(e))
            return 0;
        if (is_fvar(e))
            return to_fv_set(fvar_name(e));
        auto it = m_fv_map.find(e);
        if (it != m_fv_map.end())
            return it->second;
        fv_set r;
        switch (e.kind()) {
        case expr_kind::Const: case expr_kind::Sort:
        case expr_kind::BVar:  case expr_kind::Lit:
        case expr_kind::MVar:  case expr_kind::FVar:
            lean_unreachable();
        case expr_kind::MData:
            r = init_fv_map(mdata_expr(e));
            break;
        case expr_kind::Proj:
            r = init_fv_map(proj_expr(e));
            break;
        case expr_kind::App:
            r = init_fv_map(app_fn(e)) | init_fv_map(app_arg(e));
            break;
        case expr_kind::Pi: case expr_kind::Lambda:
            r = init_fv_map(binding_domain(e)) | init_fv_map(binding_body(e));
            break;
        case expr_kind::Let:
            r = init_fv_map(let_type(e)) | init_fv_map(let_value(e)) | init_fv_map(let_body(e));
            break;
        }
        update_fv(e, r);
        return r;
    }

public:
    replace_fvars_fn() {}

    expr operator()(expr const & e, array_ref<expr> const & fvars, expr const * rev_args) {
        m_cache.clear();
        // init_fv_map(e); // uncomment for better precision. The counter `g_replace_visited` will provide the number we would get if `fv_set` were a field of `Expr`
        lean_assert(m_cache.size() == 0);
        m_fvars = &fvars;
        m_num_fvars = fvars.size();
        m_rev_args = rev_args;
        m_rev_arg_fv_sets.resize(m_num_fvars, 0);
        m_target = 0;
        for (unsigned i = 0; i < m_num_fvars; i++) {
            m_target = m_target | to_fv_set(fvar_name(fvars[i]));
            if (has_fvar(rev_args[i]))
                m_rev_arg_fv_sets[i] = init_fv_map(rev_args[i]);
            else
                m_rev_arg_fv_sets[i] = 0;
        }
        return apply(e, 0);
    }
};

static size_t get_size_shared(expr const & e) {
    size_t size = 0;
    for_each(e, [&](expr const &) {
        size++;
        return true;
    });
    return size;
}

expr replace_fvars_slow(expr const & e, array_ref<expr> const & fvars, expr const * rev_args) {
    size_t sz = fvars.size();
    if (sz == 0)
        return e;
    return replace(e, [=](expr const & m, unsigned offset) -> optional<expr> {
            if (!has_fvar(m))
                return some_expr(m); // expression m does not contain free variables
            g_replace_visited++;
            if (is_fvar(m)) {
                size_t i = sz;
                name const & fid = fvar_name(m);
                while (i > 0) {
                    --i;
                    if (fvar_name(fvars[i]) == fid) {
                        return some_expr(lift_loose_bvars(rev_args[sz - i - 1], 0, offset));
                    }
                }
            }
            return none_expr();
        });
}

class instantiate_mvars_fn {
    metavar_ctx & m_mctx;
    instantiate_lmvars_fn m_level_fn;
    name_set m_already_normalized; // Store metavariables whose assignment has already been normalized.
    std::unordered_map<lean_object *, expr> m_cache;
    std::vector<expr> m_saved; // Helper vector to prevent values from being garbage collected
    replace_fvars_fn m_replace_fn;
    size_t m_visited = 0;

    expr replace_fvars(expr const & e, array_ref<expr> const & fvars, expr const * rev_args) {
        if (!has_fvar(e) || fvars.size() == 0)
            return e;
        expr r = m_replace_fn(e, fvars, rev_args);
        // expr r = replace_fvars_slow(e, fvars, rev_args);
        lean_assert(r == replace_fvars_slow(e, fvars, rev_args));
        return r;
    }

    level visit_level(level const & l) {
        return m_level_fn(l);
    }

    levels visit_levels(levels const & ls) {
        buffer<level> lsNew;
        for (auto const & l : ls)
            lsNew.push_back(visit_level(l));
        return levels(lsNew);
    }

    inline expr cache(expr const & e, expr r, bool shared) {
        if (shared) {
            m_cache.insert(mk_pair(e.raw(), r));
        }
        return r;
    }

    optional<expr> get_assignment(name const & mid) {
        option_ref<expr> r = get_mvar_assignment(m_mctx, mid);
        if (!r) {
            return optional<expr>();
        } else {
            expr a(r.get_val());
            if (!has_mvar(a) || m_already_normalized.contains(mid)) {
                return optional<expr>(a);
            } else {
                m_already_normalized.insert(mid);
                expr a_new = visit(a);
                if (!is_eqp(a, a_new)) {
                    /*
                    We save `a` to ensure it will not be garbage collected
                    after we update `mctx`. This is necessary because `m_cache`
                    may contain references to its subterms.
                    */
                    m_saved.push_back(a);
                    assign_mvar(m_mctx, mid, a_new);
                }
                return optional<expr>(a_new);
            }
        }
    }

    /*
    Given `e` of the form `f a_1 ... a_n` where `f` is not a metavariable,
    instantiate metavariables.
    */
    expr visit_app_default(expr const & e) {
        buffer<expr> args;
        expr const * curr = &e;
        while (is_app(*curr)) {
            args.push_back(visit(app_arg(*curr)));
            curr = &app_fn(*curr);
        }
        lean_assert(!is_mvar(*curr));
        expr f = visit(*curr);
        return mk_rev_app(f, args.size(), args.data());
    }

    /*
    Given `e` of the form `?m a_1 ... a_n`, return new application where
    the metavariables in the arguments `a_i` have been instantiated.
    */
    expr visit_mvar_app_args(expr const & e) {
        buffer<expr> args;
        expr const * curr = &e;
        while (is_app(*curr)) {
            args.push_back(visit(app_arg(*curr)));
            curr = &app_fn(*curr);
        }
        lean_assert(is_mvar(*curr));
        return mk_rev_app(*curr, args.size(), args.data());
    }

    /*
    Given `e` of the form `f a_1 ... a_n`, return new application `f_new a_1' ... a_n'`
    where `a_i'` is `visit(a_i)`. `args` is an accumulator for the new arguments.
    */
    expr visit_args_and_beta(expr const & f_new, expr const & e, buffer<expr> & args) {
        expr const * curr = &e;
        while (is_app(*curr)) {
            args.push_back(visit(app_arg(*curr)));
            curr = &app_fn(*curr);
        }
        /*
          Some of the arguments in `args` are irrelevant after we beta
          reduce. Also, it may be a bug to not instantiate them, since they
          may depend on free variables that are not in the context (see
          issue #4375). So we pass `useZeta := true` to ensure that they are
          instantiated.
        */
        bool preserve_data = false;
        bool zeta = true;
        return apply_beta(f_new, args.size(), args.data(), preserve_data, zeta);
    }

    /*
    Helper function for delayed assignment case at `visit_app`.
    `e` is a term of the form `?m t1 t2 t3`
    Moreover, `?m` is delayed assigned
      `?m #[x, y] := g x y`
    where, `fvars := #[x, y]` and `val := g x y`.
    `args` is an accumulator for `e`'s arguments.

    We want to return `g t1' t2' t3'` where
    `ti'`s are `visit(ti)`.
    */
    expr visit_delayed(array_ref<expr> const & fvars, expr const & val, expr const & e, buffer<expr> & args) {
        expr const * curr = &e;
        while (is_app(*curr)) {
            args.push_back(visit(app_arg(*curr)));
            curr = &app_fn(*curr);
        }
        expr val_new = replace_fvars(val, fvars, args.data() + (args.size() - fvars.size()));
        return mk_rev_app(val_new, args.size() - fvars.size(), args.data());
    }

    expr visit_app(expr const & e) {
        expr const & f = get_app_fn(e);
        if (!is_mvar(f)) {
            return visit_app_default(e);
        } else {
            name const & mid = mvar_name(f);
            /*
            Regular assignments take precedence over delayed ones.
            When an error occurs, Lean assigns `sorry` to unassigned metavariables.
            The idea is to ensure we can submit the declaration to the kernel and proceed.
            Some of the metavariables may have been delayed assigned.
            */
            if (auto f_new = get_assignment(mid)) {
                // `f` is an assigned metavariable.
                buffer<expr> args;
                return visit_args_and_beta(*f_new, e, args);
            }
            option_ref<delayed_assignment> d = get_delayed_mvar_assignment(m_mctx, mid);
            if (!d) {
                // mvar is not delayed assigned
                return visit_mvar_app_args(e);
            }
            /*
            Apply "delayed substitution" (i.e., delayed assignment + application).
            That is, `f` is some metavariable `?m`, that is delayed assigned to `val`.
            If after instantiating `val`, we obtain `newVal`, and `newVal` does not contain
            metavariables, we replace the free variables `fvars` in `newVal` with the first
            `fvars.size` elements of `args`.
            */
            array_ref<expr> fvars(cnstr_get(d.get_val().raw(), 0), true);
            name mid_pending(cnstr_get(d.get_val().raw(), 1), true);
            if (fvars.size() > get_app_num_args(e)) {
                /*
                We don't have sufficient arguments for instantiating the free variables `fvars`.
                This can only happen if a tactic or elaboration function is not implemented correctly.
                We decided to not use `panic!` here and report it as an error in the frontend
                when we are checking for unassigned metavariables in an elaborated term. */
                return visit_mvar_app_args(e);
            }
            optional<expr> val = get_assignment(mid_pending);
            if (!val)
                // mid_pending has not been assigned yet.
                return visit_mvar_app_args(e);
            if (has_expr_mvar(*val))
                // mid_pending has been assigned, but assignment contains mvars.
                return visit_mvar_app_args(e);
            buffer<expr> args;
            return visit_delayed(fvars, *val, e, args);
        }
    }

    expr visit_mvar(expr const & e) {
        name const & mid = mvar_name(e);
        if (auto r = get_assignment(mid)) {
            return *r;
        } else {
            return e;
        }
    }

public:
    instantiate_mvars_fn(metavar_ctx & mctx):m_mctx(mctx), m_level_fn(mctx) {}

    expr visit(expr const & e) {
        if (!has_mvar(e))
            return e;
        m_visited++;
        bool shared = false;
        if (is_shared(e)) {
            auto it = m_cache.find(e.raw());
            if (it != m_cache.end()) {
                return it->second;
            }
            shared = true;
        }

        switch (e.kind()) {
        case expr_kind::BVar:
        case expr_kind::Lit:  case expr_kind::FVar:
            lean_unreachable();
        case expr_kind::Sort:
            return cache(e, update_sort(e, visit_level(sort_level(e))), shared);
        case expr_kind::Const:
            return cache(e, update_const(e, visit_levels(const_levels(e))), shared);
        case expr_kind::MVar:
            return visit_mvar(e);
        case expr_kind::MData:
            return cache(e, update_mdata(e, visit(mdata_expr(e))), shared);
        case expr_kind::Proj:
            return cache(e, update_proj(e, visit(proj_expr(e))), shared);
        case expr_kind::App:
            return cache(e, visit_app(e), shared);
        case expr_kind::Pi: case expr_kind::Lambda:
            return cache(e, update_binding(e, visit(binding_domain(e)), visit(binding_body(e))), shared);
        case expr_kind::Let:
            return cache(e, update_let(e, visit(let_type(e)), visit(let_value(e)), visit(let_body(e))), shared);
        }
    }

    expr operator()(expr const & e) {
        g_replace_visited = 0;
        g_lift_visited = 0;
        expr r = visit(e);
        size_t s = get_size_shared(r);
        if (s > 1024) {
            std::cout << m_visited << " " << g_lift_visited << " " << g_replace_visited << " " << s << " " << get_size_shared(expr(sharecommon_quick_fn()(r.to_obj_arg()))) << "\n";
        }
        return r;
    }
};

extern "C" LEAN_EXPORT object * lean_instantiate_expr_mvars(object * m, object * e) {
    metavar_ctx mctx(m);
    expr e_new = instantiate_mvars_fn(mctx)(expr(e));
    object * r = alloc_cnstr(0, 2, 0);
    cnstr_set(r, 0, mctx.steal());
    cnstr_set(r, 1, e_new.steal());
    return r;
}
}
