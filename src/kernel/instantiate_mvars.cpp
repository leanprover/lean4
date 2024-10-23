/*
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura
*/
#include <vector>
#include <unordered_map>
#include "util/name_set.h"
#include "util/freset.h"
#include "runtime/flet.h"
#include "runtime/option_ref.h"
#include "runtime/sharecommon.h"
#include "runtime/array_ref.h"
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

expr replace_fvars(expr const & e, array_ref<expr> const & fvars, expr const * rev_args) {
    size_t sz = fvars.size();
    if (sz == 0)
        return e;
    return replace(e, [=](expr const & m, unsigned offset) -> optional<expr> {
            if (!has_fvar(m))
                return some_expr(m); // expression m does not contain free variables
            if (is_fvar(m)) {
                size_t i = sz;
                name const & fid = fvar_name(m);
                while (i > 0) {
                    --i;
                    if (fvar_name(fvars[i]) == fid) {
                        return some_expr(lift_loose_bvars(rev_args[sz - i - 1], offset));
                    }
                }
            }
            return none_expr();
        });
}

static name * g_ds_name = nullptr;
static expr * g_ds_const = nullptr;

static expr mk_delayed_subst_annotation(expr const & e) {
    return mk_app(*g_ds_const, e);
}

static bool is_delayed_subst(expr const & e) {
    return is_app(e) && is_eqp(app_fn(e), *g_ds_const);
}

/* Return "delayed substitution term" `e[x := c]` */
static expr mk_delayed_subst(expr const & e, expr const & x, expr const & s) {
    return mk_delayed_subst_annotation(mk_app(e, mk_app(x, s)));
}

/* Return `true` if `e` contains a delayed substitution node. */
bool has_delayed_subst(expr const & e) {
    bool found = false;
    for_each(e, [&](expr const & e) {
        if (found) return false;
        if (is_delayed_subst(e)) {
            found = true;
            return false;
        }
        return true;
     });
    return found;
}

size_t get_size_shared(expr const & e) {
    size_t size = 0;
    for_each(e, [&](expr const &) {
        size++;
        return true;
    });
    return size;
}

class apply_delayed_subst_fn {
    struct cache_hash_fn {
        std::size_t operator()(std::pair<lean_object *, unsigned> const & p) const {
            return hash((size_t)p.first >> 3, p.second);
        }
    };
    typedef std::unordered_map<std::pair<lean_object *, unsigned>, expr, cache_hash_fn> cache_t;
    typedef std::unordered_map<name, std::pair<expr, unsigned>, name_hash_fn, name_eq_fn> subst_t;
    cache_t m_cache;
    subst_t m_subst;

    expr save_result(expr const & e, unsigned offset, expr const & r, bool shared) {
        if (shared)
            m_cache.insert(mk_pair(mk_pair(e.raw(), offset), r));
        return r;
    }

    expr apply(expr const & e, unsigned offset) {
        if (!has_fvar(e))
            return e;
        bool shared = false;
        if (is_shared(e)) {
            auto it = m_cache.find(mk_pair(e.raw(), offset));
            if (it != m_cache.end())
                return it->second;
            shared = true;
        }

        switch (e.kind()) {
        case expr_kind::Const: case expr_kind::Sort:
        case expr_kind::BVar:  case expr_kind::Lit:
        case expr_kind::MVar:
            return save_result(e, offset, e, shared);
        case expr_kind::FVar: {
            auto it = m_subst.find(fvar_name(e));
            if (it != m_subst.end()) {
                expr s = it->second.first;
                unsigned offset_s = it->second.second;
                lean_assert(offset >= offset_s);
                // if (get_size_shared(s) > 128)
                // size_t sz = get_size_shared(s);
                // if (sz > 10000) {
                    // size_t sz2 = get_size_shared(expr(sharecommon_quick_fn()(s.to_obj_arg())));
                    // std::cout << s.raw() << " " << sz << " " << sz2 << " " << (offset - offset_s) << "\n";
                // }
                expr e_new = lift_loose_bvars(s, offset - offset_s);
                // if (get_size_shared(s) > 128)
                //    std::cout << fvar_name(e) << " " << get_size_shared(s) << " " << (offset - offset_s) << " := " << get_size_shared(e_new) << "\n";
                // std::cout << fvar_name(e) << " " << (offset - offset_s) << "\n";
                return save_result(e, offset, e_new, shared);
            } else {
                return save_result(e, offset, e, shared);
            }
        }
        case expr_kind::MData: {
            expr new_e = apply(mdata_expr(e), offset);
            return save_result(e, offset, update_mdata(e, new_e), shared);
        }
        case expr_kind::Proj: {
            expr new_e = apply(proj_expr(e), offset);
            return save_result(e, offset, update_proj(e, new_e), shared);
        }
        case expr_kind::App: {
            if (is_eqp(app_fn(e), *g_ds_const)) {
                expr b = app_arg(e);
                expr c = app_fn(b);
                expr p = app_arg(b);
                expr x = app_fn(p);
                expr s = apply(app_arg(p), offset);
                // if (get_size_shared(s) > 128)
                //    std::cout << "### " << get_size_shared(app_arg(p)) << " " << get_size_shared(s) << "\n";
                s = expr(sharecommon_quick_fn()(s.to_obj_arg())); // Timeout without sharecommon_quick_fn here
                expr new_e;
                {
                    freset<cache_t> save(m_cache);
                    auto it = m_subst.find(fvar_name(x));
                    if (it == m_subst.end()) {
                        // new entry
                        m_subst.insert(mk_pair(fvar_name(x), mk_pair(s, offset)));
                        new_e = apply(c, offset);
                        m_subst.erase(fvar_name(x));
                    } else {
                        // updating entry, we must save current value and restore it later
                        auto saved(it->second);
                        m_subst.insert(mk_pair(fvar_name(x), mk_pair(s, offset)));
                        new_e = apply(c, offset);
                        m_subst.insert(mk_pair(fvar_name(x), saved));
                    }
                }
                // lean_assert(!has_delayed_subst(new_e));
                return save_result(e, offset, new_e, shared);
            } else {
                expr new_f = apply(app_fn(e), offset);
                expr new_a = apply(app_arg(e), offset);
                return save_result(e, offset, update_app(e, new_f, new_a), shared);
            }
        }
        case expr_kind::Pi: case expr_kind::Lambda: {
            expr new_d = apply(binding_domain(e), offset);
            expr new_b = apply(binding_body(e), offset+1);
            return save_result(e, offset, update_binding(e, new_d, new_b), shared);
        }
        case expr_kind::Let: {
            expr new_t = apply(let_type(e), offset);
            expr new_v = apply(let_value(e), offset);
            expr new_b = apply(let_body(e), offset+1);
            return save_result(e, offset, update_let(e, new_t, new_v, new_b), shared);
        }}
        lean_unreachable();
    }
public:
    expr operator()(expr const & e) { return apply(e, 0); }
};

static expr apply_delayed_subst(expr const & e) {
    // std::cout << get_size_shared(e) << " " << get_size_shared(expr(sharecommon_quick_fn()(e.to_obj_arg()))) << "\n";
    expr r = apply_delayed_subst_fn()(e);
    // std::cout << ">> " << get_size_shared(r) << " " << get_size_shared(expr(sharecommon_quick_fn()(r.to_obj_arg()))) << "\n";
    // std::cout << e << "\n======>\n" << r << "\n------\n";
    return r;
}

class instantiate_mvars_fn {
    struct cache_hash_fn {
        size_t operator()(expr const & e) const { return ((size_t)e.raw())>>3; }
    };
    struct cache_eq_fn {
        bool operator()(expr const & e1, expr const & e2) const { return e1.raw() == e2.raw(); }
    };
    typedef std::unordered_map<name, expr, name_hash_fn, name_eq_fn> norm_assignment_t;
    typedef std::unordered_map<expr, expr, cache_hash_fn, cache_eq_fn> cache_t;
    metavar_ctx & m_mctx;
    instantiate_lmvars_fn m_level_fn;
    /*
    We set `m_created_delayed_subst` if a delayed substitution term is created.
    Recall that this kind of term should not leak outside of this module.
    */
    bool m_created_delayed_subst = false;
    cache_t m_cache;
    norm_assignment_t m_norm_assignment;

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
            m_cache.insert(mk_pair(e, r));
        }
        return r;
    }

    optional<expr> get_assignment(name const & mid) {
        option_ref<expr> r = get_mvar_assignment(m_mctx, mid);
        if (!r) {
            return optional<expr>();
        } else {
            expr a(r.get_val());
            if (!has_mvar(a))
                return optional<expr>(a);
            auto it = m_norm_assignment.find(mid);
            if (it != m_norm_assignment.end())
                return optional<expr>(it->second);
            bool save_created_delayed_subst = m_created_delayed_subst;
            m_created_delayed_subst = false;
            expr a_new = visit(a);
            m_norm_assignment.insert(mk_pair(mid, a_new));
            if (!m_created_delayed_subst && !is_eqp(a, a_new)) {
                // We don't want delayed substitutions leaking into `m_mctx`.
                lean_assert(!has_delayed_subst(a_new));
                assign_mvar(m_mctx, mid, a_new);
            }
            m_created_delayed_subst = m_created_delayed_subst || save_created_delayed_subst;
            return optional<expr>(a_new);
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
        m_created_delayed_subst = true;
        expr val_new = val;
        for (unsigned i = 0; i < fvars.size(); i++) {
            val_new = mk_delayed_subst(val_new, fvars[i], args[args.size() - i - 1]);
            // lean_assert(has_delayed_subst(val_new));
        }
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
        bool shared = false;
        if (is_shared(e)) {
            auto it = m_cache.find(e);
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
        expr r = visit(e);
        if (m_created_delayed_subst)
            return apply_delayed_subst(r);
        else
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

void initialize_instantiate_mvars() {
    g_ds_name = new name("__delayed_subst_");
    mark_persistent(g_ds_name->raw());
    g_ds_const = new expr(mk_const(*g_ds_name));
    mark_persistent(g_ds_const->raw());
}

void finalize_instantiate_mvars() {
    delete g_ds_const;
    delete g_ds_name;
}

}
