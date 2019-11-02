/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <limits>
#include <vector>
#include "kernel/replace_fn.h"
#include "kernel/declaration.h"
#include "kernel/instantiate.h"

#ifndef LEAN_INST_UNIV_CACHE_SIZE
#define LEAN_INST_UNIV_CACHE_SIZE 1023
#endif

namespace lean {
expr instantiate(expr const & a, unsigned s, unsigned n, expr const * subst) {
    if (s >= get_loose_bvar_range(a) || n == 0)
        return a;
    return replace(a, [=](expr const & m, unsigned offset) -> optional<expr> {
            unsigned s1 = s + offset;
            if (s1 < s)
                return some_expr(m); // overflow, vidx can't be >= max unsigned
            if (s1 >= get_loose_bvar_range(m))
                return some_expr(m); // expression m does not contain loose bound variables with idx >= s1
            if (is_bvar(m)) {
                nat const & vidx = bvar_idx(m);
                if (vidx >= s1) {
                    unsigned h = s1 + n;
                    if (h < s1 /* overflow, h is bigger than any vidx */ || vidx < h) {
                        return some_expr(lift_loose_bvars(subst[vidx.get_small_value() - s1], offset));
                    } else {
                        return some_expr(mk_bvar(vidx - nat(n)));
                    }
                }
            }
            return none_expr();
        });
}

expr instantiate(expr const & e, unsigned n, expr const * s) { return instantiate(e, 0, n, s); }
expr instantiate(expr const & e, std::initializer_list<expr> const & l) {  return instantiate(e, l.size(), l.begin()); }
expr instantiate(expr const & e, unsigned i, expr const & s) { return instantiate(e, i, 1, &s); }
expr instantiate(expr const & e, expr const & s) { return instantiate(e, 0, s); }

extern "C" object * lean_expr_instantiate1(object * a0, object * e0) {
    expr const & a = reinterpret_cast<expr const &>(a0);
    if (!has_loose_bvars(a)) {
        lean_inc(a0);
        return a0;
    }
    expr const & e = reinterpret_cast<expr const &>(e0);
    expr r = instantiate(a, 1, &e);
    return r.steal();
}

static object * lean_expr_instantiate_core(object * a0, size_t n, object** subst) {
    expr const & a = reinterpret_cast<expr const &>(a0);
    if (!has_loose_bvars(a) || n == 0) {
        lean_inc(a0);
        return a0;
    }
    expr r = replace(a, [=](expr const & m, unsigned offset) -> optional<expr> {
            if (offset >= get_loose_bvar_range(m))
                return some_expr(m); // expression m does not contain loose bound variables with idx >= offset
            if (is_bvar(m)) {
                nat const & vidx = bvar_idx(m);
                if (vidx >= offset) {
                    size_t h = offset + n;
                    if (h < offset /* overflow, h is bigger than any vidx */ || (vidx.is_small() && vidx.get_small_value() < h)) {
                        object * v = subst[vidx.get_small_value() - offset];
                        return some_expr(lift_loose_bvars(TO_REF(expr, v), offset));
                    } else {
                        return some_expr(mk_bvar(vidx - nat::of_size_t(n)));
                    }
                }
            }
            return none_expr();
        });
    return r.steal();
}

extern "C" object * lean_expr_instantiate(object * a, object * subst) {
    return lean_expr_instantiate_core(a, lean_array_size(subst), lean_array_cptr(subst));
}

extern "C" object * lean_expr_instantiate_range(object * a, object * begin, object * end, object * subst) {
    if (!lean_is_scalar(begin) || !lean_is_scalar(end)) {
        lean_panic("invalid range for Expr.instantiateRange");
    } else {
        usize sz = lean_array_size(subst);
        usize b  = lean_unbox(begin);
        usize e  = lean_unbox(end);
        if (b > e || e > sz) {
            lean_panic("invalid range for Expr.instantiateRange");
        }
        return lean_expr_instantiate_core(a, e - b, lean_array_cptr(subst) + b);
    }
}

expr instantiate_rev(expr const & a, unsigned n, expr const * subst) {
    if (!has_loose_bvars(a))
        return a;
    return replace(a, [=](expr const & m, unsigned offset) -> optional<expr> {
            if (offset >= get_loose_bvar_range(m))
                return some_expr(m); // expression m does not contain loose bound variables with idx >= offset
            if (is_bvar(m)) {
                nat const & vidx = bvar_idx(m);
                if (vidx >= offset) {
                    size_t h = offset + n;
                    if (h < offset /* overflow, h is bigger than any vidx */ || (vidx.is_small() && vidx.get_small_value() < h)) {
                        return some_expr(lift_loose_bvars(subst[n - (vidx.get_small_value() - offset) - 1], offset));
                    } else {
                        return some_expr(mk_bvar(vidx - nat(n)));
                    }
                }
            }
            return none_expr();
        });
}

extern "C" object * lean_expr_instantiate_rev(object * a0, object * subst0) {
    expr const & a = reinterpret_cast<expr const &>(a0);
    if (!has_loose_bvars(a)) {
        lean_inc(a0);
        return a0;
    }
    size_t n = lean_array_size(subst0);
    object ** subst = lean_array_cptr(subst0);
    expr r = replace(a, [=](expr const & m, unsigned offset) -> optional<expr> {
            if (offset >= get_loose_bvar_range(m))
                return some_expr(m); // expression m does not contain loose bound variables with idx >= offset
            if (is_bvar(m)) {
                nat const & vidx = bvar_idx(m);
                if (vidx >= offset) {
                    size_t h = offset + n;
                    if (h < offset /* overflow, h is bigger than any vidx */ || (vidx.is_small() && vidx.get_small_value() < h)) {
                        object * v = subst[n - (vidx.get_small_value() - offset) - 1];
                        return some_expr(lift_loose_bvars(TO_REF(expr, v), offset));
                    } else {
                        return some_expr(mk_bvar(vidx - nat::of_size_t(n)));
                    }
                }
            }
            return none_expr();
        });
    return r.steal();
}

bool is_head_beta(expr const & t) {
    return is_app(t) && is_lambda(get_app_fn(t));
}

expr apply_beta(expr f, unsigned num_args, expr const * args) {
    if (num_args == 0) {
        return f;
    } else if (!is_lambda(f)) {
        return mk_rev_app(f, num_args, args);
    } else {
        unsigned m = 1;
        while (is_lambda(binding_body(f)) && m < num_args) {
            f = binding_body(f);
            m++;
        }
        lean_assert(m <= num_args);
        return mk_rev_app(instantiate(binding_body(f), m, args + (num_args - m)), num_args - m, args);
    }
}

expr head_beta_reduce(expr const & t) {
    if (!is_head_beta(t)) {
        return t;
    } else {
        buffer<expr> args;
        expr const & f = get_app_rev_args(t, args);
        lean_assert(is_lambda(f));
        return head_beta_reduce(apply_beta(f, args.size(), args.data()));
    }
}

expr cheap_beta_reduce(expr const & e) {
    if (!is_app(e)) return e;
    expr fn = get_app_fn(e);
    if (!is_lambda(fn)) return e;
    buffer<expr> args;
    get_app_args(e, args);
    unsigned i = 0;
    while (is_lambda(fn) && i < args.size()) {
        i++;
        fn = binding_body(fn);
    }
    if (!has_loose_bvars(fn)) {
        return mk_app(fn, args.size() - i, args.data() + i);
    } else if (is_bvar(fn)) {
        lean_assert(bvar_idx(fn) < i);
        return mk_app(args[i - bvar_idx(fn).get_small_value() - 1], args.size() - i, args.data() + i);
    } else {
        return e;
    }
}

expr instantiate_lparams(expr const & e, names const & lps, levels const & ls) {
    if (!has_param_univ(e))
        return e;
    return replace(e, [&](expr const & e) -> optional<expr> {
            if (!has_param_univ(e))
                return some_expr(e);
            if (is_constant(e)) {
                return some_expr(update_constant(e, map_reuse(const_levels(e), [&](level const & l) { return instantiate(l, lps, ls); })));
            } else if (is_sort(e)) {
                return some_expr(update_sort(e, instantiate(sort_level(e), lps, ls)));
            } else {
                return none_expr();
            }
        });
}

extern "C" object * lean_instantiate_lparams(b_obj_arg e, b_obj_arg lps, b_obj_arg ls) {
    return instantiate_lparams(TO_REF(expr, e), TO_REF(names, lps), TO_REF(levels, ls)).steal();
}

class instantiate_univ_cache {
    typedef std::tuple<constant_info, levels, expr> entry;
    unsigned                     m_capacity;
    std::vector<optional<entry>> m_cache;
public:
    instantiate_univ_cache(unsigned capacity):m_capacity(capacity) {
        if (m_capacity == 0)
            m_capacity++;
    }

    optional<expr> is_cached(constant_info const & d, levels const & ls) {
        if (m_cache.empty())
            return none_expr();
        lean_assert(m_cache.size() == m_capacity);
        unsigned idx = d.get_name().hash() % m_capacity;
        if (auto it = m_cache[idx]) {
            constant_info info_c; levels ls_c; expr r_c;
            std::tie(info_c, ls_c, r_c) = *it;
            if (!is_eqp(info_c, d))
                return none_expr();
            if (ls == ls_c)
                return some_expr(r_c);
            else
                return none_expr();
        }
        return none_expr();
    }

    void save(constant_info const & d, levels const & ls, expr const & r) {
        if (m_cache.empty())
            m_cache.resize(m_capacity);
        lean_assert(m_cache.size() == m_capacity);
        unsigned idx = d.get_name().hash() % m_cache.size();
        m_cache[idx] = entry(d, ls, r);
    }

    void clear() {
        m_cache.clear();
        lean_assert(m_cache.empty());
    }
};

MK_THREAD_LOCAL_GET(instantiate_univ_cache, get_type_univ_cache, LEAN_INST_UNIV_CACHE_SIZE);
MK_THREAD_LOCAL_GET(instantiate_univ_cache, get_value_univ_cache, LEAN_INST_UNIV_CACHE_SIZE);

expr instantiate_type_lparams(constant_info const & info, levels const & ls) {
    if (info.get_num_lparams() != length(ls))
        lean_panic("#universes mismatch at instantiateTypeLevelParams");
    if (is_nil(ls) || !has_param_univ(info.get_type()))
        return info.get_type();
    instantiate_univ_cache & cache = get_type_univ_cache();
    if (auto r = cache.is_cached(info, ls))
        return *r;
    expr r = instantiate_lparams(info.get_type(), info.get_lparams(), ls);
    cache.save(info, ls, r);
    return r;
}

expr instantiate_value_lparams(constant_info const & info, levels const & ls) {
    if (info.get_num_lparams() != length(ls))
        lean_panic("#universes mismatch at instantiateValueLevelParams");
    if (!info.has_value())
        lean_panic("definition/theorem expected at instantiateValueLevelParams");
    if (is_nil(ls) || !has_param_univ(info.get_value()))
        return info.get_value();
    instantiate_univ_cache & cache = get_value_univ_cache();
    if (auto r = cache.is_cached(info, ls))
        return *r;
    expr r = instantiate_lparams(info.get_value(), info.get_lparams(), ls);
    cache.save(info, ls, r);
    return r;
}

extern "C" object * lean_instantiate_type_lparams(object * info, object * ls) {
    return instantiate_type_lparams(TO_REF(constant_info, info), TO_REF(levels, ls)).steal();
}

extern "C" object * lean_instantiate_value_lparams(object * info, object * ls) {
    return instantiate_value_lparams(TO_REF(constant_info, info), TO_REF(levels, ls)).steal();
}

void clear_instantiate_cache() {
    get_type_univ_cache().clear();
    get_value_univ_cache().clear();
}
}
