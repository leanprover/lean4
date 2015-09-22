/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include <unordered_set>
#include "util/interrupt.h"
#include "kernel/expr_eq_fn.h"
#include "kernel/replace_cache.h"
#include "kernel/cache_stack.h"
#include "kernel/instantiate_univ_cache.h"
#include "library/blast/expr.h"

#ifndef LEAN_DEFAULT_BLAST_REPLACE_CACHE_CAPACITY
#define LEAN_DEFAULT_BLAST_REPLACE_CACHE_CAPACITY 1024*8
#endif

#ifndef LEAN_BLAST_INST_UNIV_CACHE_SIZE
#define LEAN_BLAST_INST_UNIV_CACHE_SIZE 1023
#endif

namespace lean {
namespace blast {
/** \brief Auxiliary macro used to encode mref and lref expressions used by the blast tactic
    \remark This macro should never occur in fully elaborated terms. */
class ref_definition_cell : public macro_definition_cell {
    bool     m_local;
    unsigned m_idx;
public:
    ref_definition_cell(bool local, unsigned idx):m_local(local), m_idx(idx) {}

    bool     is_local() const { return m_local; }
    unsigned get_index() const { return m_idx; }

    virtual name get_name() const { return name("ref"); }

    virtual pair<expr, constraint_seq> check_type(expr const &, extension_context &, bool) const {
        lean_unreachable();
    }

    virtual optional<expr> expand(expr const &, extension_context &) const {
        lean_unreachable();
    }

    virtual void write(serializer &) const {
        lean_unreachable();
    }

    virtual bool operator==(macro_definition_cell const & other) const {
        return
            dynamic_cast<ref_definition_cell const *>(&other) != nullptr &&
            m_idx   == static_cast<ref_definition_cell const&>(other).m_idx &&
            m_local == static_cast<ref_definition_cell const&>(other).m_local;
    }

    virtual unsigned hash() const { return lean::hash(m_local, m_idx); }
};

static expr mk_lref_core(unsigned idx) {
    return lean::mk_macro(macro_definition(new ref_definition_cell(true, idx)), 0, nullptr);
}

static expr mk_mref_core(unsigned idx) {
    return lean::mk_macro(macro_definition(new ref_definition_cell(false, idx)), 0, nullptr);
}

bool is_lmref(expr const & e) {
    return is_macro(e) && dynamic_cast<ref_definition_cell const *>(macro_def(e).raw());
}

bool is_lref(expr const & e) {
    return is_lmref(e) && static_cast<ref_definition_cell const *>(macro_def(e).raw())->is_local();
}

bool is_mref(expr const & e) {
    return is_lmref(e) && !is_lref(e);
}

unsigned get_lmindex(expr const & e) {
    lean_assert(is_lmref(e));
    return static_cast<ref_definition_cell const *>(macro_def(e).raw())->get_index();
}

typedef typename std::unordered_set<expr, expr_hash, is_bi_equal_proc> expr_table;
typedef typename std::unordered_set<level, level_hash>                 level_table;
typedef typename std::vector<expr>                                     expr_array;

LEAN_THREAD_PTR(level_table, g_level_table);
LEAN_THREAD_PTR(expr_table,  g_expr_table);
LEAN_THREAD_PTR(expr_array,  g_var_array);
LEAN_THREAD_PTR(expr_array,  g_mref_array);
LEAN_THREAD_PTR(expr_array,  g_lref_array);

scope_hash_consing::scope_hash_consing() {
    m_level_table = g_level_table;
    m_expr_table  = g_expr_table;
    m_var_array   = g_var_array;
    m_mref_array  = g_mref_array;
    m_lref_array  = g_lref_array;
    g_level_table = new level_table();
    g_expr_table  = new expr_table();
    g_var_array   = new expr_array();
    g_mref_array  = new expr_array();
    g_lref_array  = new expr_array();
    g_level_table->insert(lean::mk_level_zero());
    g_level_table->insert(lean::mk_level_one());
}

scope_hash_consing::~scope_hash_consing() {
    delete g_level_table;
    delete g_expr_table;
    delete g_var_array;
    delete g_mref_array;
    delete g_lref_array;
    g_level_table = reinterpret_cast<level_table*>(m_level_table);
    g_expr_table  = reinterpret_cast<expr_table*>(m_expr_table);
    g_var_array   = reinterpret_cast<expr_array*>(m_var_array);
    g_mref_array  = reinterpret_cast<expr_array*>(m_mref_array);
    g_lref_array  = reinterpret_cast<expr_array*>(m_lref_array);
}

#ifdef LEAN_DEBUG
static bool is_cached(level const & l) {
    lean_assert(g_level_table);
    return g_level_table->find(l) != g_level_table->end();
}

static bool is_cached(expr const & l) {
    lean_assert(g_expr_table);
    return g_expr_table->find(l) != g_expr_table->end();
}
#endif

static level cache(level const & l) {
    lean_assert(g_level_table);
    auto r = g_level_table->find(l);
    if (r != g_level_table->end())
        return *r;
    g_level_table->insert(l);
    return l;
}

static expr cache(expr const & e) {
    lean_assert(g_expr_table);
    auto r = g_expr_table->find(e);
    if (r != g_expr_table->end())
        return *r;
    g_expr_table->insert(e);
    return e;
}

level mk_level_zero() {
    return lean::mk_level_zero();
}

level mk_level_one() {
    return lean::mk_level_one();
}

level mk_max(level const & l1, level const & l2) {
    lean_assert(is_cached(l1));
    lean_assert(is_cached(l2));
    return cache(lean::mk_max(l1, l2));
}

level mk_imax(level const & l1, level const & l2) {
    lean_assert(is_cached(l1));
    lean_assert(is_cached(l2));
    return cache(lean::mk_max(l1, l2));
}

level mk_succ(level const & l) {
    lean_assert(is_cached(l));
    return cache(lean::mk_succ(l));
}

level mk_param_univ(name const & n) {
    return cache(lean::mk_param_univ(n));
}

level mk_global_univ(name const & n) {
    return cache(lean::mk_global_univ(n));
}

level mk_meta_univ(name const & n) {
    return cache(lean::mk_meta_univ(n));
}

level update_succ(level const & l, level const & new_arg) {
    if (is_eqp(succ_of(l), new_arg))
        return l;
    else
        return blast::mk_succ(new_arg);
}

level update_max(level const & l, level const & new_lhs, level const & new_rhs) {
    if (is_max(l)) {
        if (is_eqp(max_lhs(l), new_lhs) && is_eqp(max_rhs(l), new_rhs))
            return l;
        else
            return blast::mk_max(new_lhs, new_rhs);
    } else {
        if (is_eqp(imax_lhs(l), new_lhs) && is_eqp(imax_rhs(l), new_rhs))
            return l;
        else
            return blast::mk_imax(new_lhs, new_rhs);
    }
}

expr mk_var(unsigned idx) {
    lean_assert(g_var_array);
    lean_assert(g_expr_table);
    while (g_var_array->size() <= idx) {
        unsigned j   = g_var_array->size();
        expr new_var = lean::mk_var(j);
        g_var_array->push_back(new_var);
        g_expr_table->insert(new_var);
    }
    lean_assert(idx < g_var_array->size());
    return (*g_var_array)[idx];
}

expr mk_lref(unsigned idx) {
    lean_assert(g_lref_array);
    lean_assert(g_expr_table);
    while (g_lref_array->size() <= idx) {
        unsigned j   = g_lref_array->size();
        expr new_ref = mk_lref_core(j);
        g_lref_array->push_back(new_ref);
        g_expr_table->insert(new_ref);
    }
    lean_assert(idx < g_lref_array->size());
    return (*g_lref_array)[idx];
}

expr mk_mref(unsigned idx) {
    lean_assert(g_mref_array);
    lean_assert(g_expr_table);
    while (g_mref_array->size() <= idx) {
        unsigned j   = g_mref_array->size();
        expr new_ref = mk_mref_core(j);
        g_mref_array->push_back(new_ref);
        g_expr_table->insert(new_ref);
    }
    lean_assert(idx < g_mref_array->size());
    return (*g_mref_array)[idx];
}

expr mk_app(expr const & f, expr const & a) {
    lean_assert(is_cached(f));
    lean_assert(is_cached(a));
    return cache(lean::mk_app(f, a));
}

expr mk_sort(level const & l) {
    lean_assert(is_cached(l));
    return cache(lean::mk_sort(l));
}

expr mk_constant(name const & n, levels const & ls) {
    lean_assert(std::all_of(ls.begin(), ls.end(), [](level const & l) { return is_cached(l); }));
    return cache(lean::mk_constant(n, ls));
}

expr mk_binding(expr_kind k, name const & n, expr const & t, expr const & e, binder_info const & bi) {
    lean_assert(is_cached(t));
    lean_assert(is_cached(e));
    return cache(lean::mk_binding(k, n, t, e, bi));
}

expr mk_macro(macro_definition const & m, unsigned num, expr const * args) {
    lean_assert(std::all_of(args, args+num, [](expr const & e) { return is_cached(e); }));
    return cache(lean::mk_macro(m, num, args));
}

expr update_app(expr const & e, expr const & new_fn, expr const & new_arg) {
    if (!is_eqp(app_fn(e), new_fn) || !is_eqp(app_arg(e), new_arg))
        return blast::mk_app(new_fn, new_arg);
    else
        return e;
}

expr update_binding(expr const & e, expr const & new_domain, expr const & new_body) {
    if (!is_eqp(binding_domain(e), new_domain) || !is_eqp(binding_body(e), new_body))
        return blast::mk_binding(e.kind(), binding_name(e), new_domain, new_body, binding_info(e));
    else
        return e;
}

expr update_sort(expr const & e, level const & new_level) {
    if (!is_eqp(sort_level(e), new_level))
        return blast::mk_sort(new_level);
    else
        return e;
}

expr update_constant(expr const & e, levels const & new_levels) {
    if (!is_eqp(const_levels(e), new_levels))
        return blast::mk_constant(const_name(e), new_levels);
    else
        return e;
}

expr update_macro(expr const & e, unsigned num, expr const * args) {
    if (num == macro_num_args(e)) {
        unsigned i = 0;
        for (i = 0; i < num; i++) {
            if (!is_eqp(macro_arg(e, i), args[i]))
                break;
        }
        if (i == num)
            return e;
    }
    return blast::mk_macro(to_macro(e)->get_def(), num, args);
}

MK_CACHE_STACK(replace_cache, LEAN_DEFAULT_BLAST_REPLACE_CACHE_CAPACITY)

class replace_rec_fn {
    replace_cache_ref                                     m_cache;
    std::function<optional<expr>(expr const &, unsigned)> m_f;

    expr save_result(expr const & e, unsigned offset, expr const & r) {
        m_cache->insert(e, offset, r);
        return r;
    }

    expr apply(expr const & e, unsigned offset) {
        if (auto r = m_cache->find(e, offset))
            return *r;
        check_interrupted();
        check_memory("replace");

        if (optional<expr> r = m_f(e, offset)) {
            return save_result(e, offset, *r);
        } else {
            switch (e.kind()) {
            case expr_kind::Constant: case expr_kind::Sort: case expr_kind::Var:
                return save_result(e, offset, e);
            case expr_kind::Meta:     case expr_kind::Local:
                lean_unreachable();
            case expr_kind::App: {
                expr new_f = apply(app_fn(e), offset);
                expr new_a = apply(app_arg(e), offset);
                return save_result(e, offset, blast::update_app(e, new_f, new_a));
            }
            case expr_kind::Pi: case expr_kind::Lambda: {
                expr new_d = apply(binding_domain(e), offset);
                expr new_b = apply(binding_body(e), offset+1);
                return save_result(e, offset, blast::update_binding(e, new_d, new_b));
            }
            case expr_kind::Macro:
                if (macro_num_args(e) == 0) {
                    return save_result(e, offset, e);
                } else {
                    buffer<expr> new_args;
                    unsigned nargs = macro_num_args(e);
                    for (unsigned i = 0; i < nargs; i++)
                        new_args.push_back(apply(macro_arg(e, i), offset));
                    return save_result(e, offset, blast::update_macro(e, new_args.size(), new_args.data()));
                }
            }
            lean_unreachable();
        }
    }
public:
    template<typename F>
    replace_rec_fn(F const & f):m_f(f) {}
    expr operator()(expr const & e) { return apply(e, 0); }
};

expr replace(expr const & e, std::function<optional<expr>(expr const &, unsigned)> const & f) {
    return replace_rec_fn(f)(e);
}

expr lift_free_vars(expr const & e, unsigned s, unsigned d) {
    if (d == 0 || s >= get_free_var_range(e))
        return e;
    return blast::replace(e, [=](expr const & e, unsigned offset) -> optional<expr> {
            unsigned s1 = s + offset;
            if (s1 < s)
                return some_expr(e); // overflow, vidx can't be >= max unsigned
            if (s1 >= get_free_var_range(e))
                return some_expr(e); // expression e does not contain free variables with idx >= s1
            if (is_var(e) && var_idx(e) >= s + offset) {
                unsigned new_idx = var_idx(e) + d;
                if (new_idx < var_idx(e))
                    throw exception("invalid lift_free_vars operation, index overflow");
                return some_expr(blast::mk_var(new_idx));
            } else {
                return none_expr();
            }
        });
}
expr lift_free_vars(expr const & e, unsigned d) {
    return blast::lift_free_vars(e, 0, d);
}

template<bool rev>
struct instantiate_easy_fn {
    unsigned n;
    expr const * subst;
    instantiate_easy_fn(unsigned _n, expr const * _subst):n(_n), subst(_subst) {}
    optional<expr> operator()(expr const & a, bool app) const {
        if (closed(a))
            return some_expr(a);
        if (is_var(a) && var_idx(a) < n)
            return some_expr(subst[rev ? n - var_idx(a) - 1 : var_idx(a)]);
        if (app && is_app(a))
            if (auto new_a = operator()(app_arg(a), false))
                if (auto new_f = operator()(app_fn(a), true))
                    return some_expr(blast::mk_app(*new_f, *new_a));
        return none_expr();
    }
};

expr instantiate(expr const & a, unsigned s, unsigned n, expr const * subst) {
    if (s >= get_free_var_range(a) || n == 0)
        return a;
    if (s == 0)
        if (auto r = blast::instantiate_easy_fn<false>(n, subst)(a, true))
            return *r;
    return blast::replace(a, [=](expr const & m, unsigned offset) -> optional<expr> {
            unsigned s1 = s + offset;
            if (s1 < s)
                return some_expr(m); // overflow, vidx can't be >= max unsigned
            if (s1 >= get_free_var_range(m))
                return some_expr(m); // expression m does not contain free variables with idx >= s1
            if (is_var(m)) {
                unsigned vidx = var_idx(m);
                if (vidx >= s1) {
                    unsigned h = s1 + n;
                    if (h < s1 /* overflow, h is bigger than any vidx */ || vidx < h) {
                        return some_expr(blast::lift_free_vars(subst[vidx - s1], offset));
                    } else {
                        return some_expr(blast::mk_var(vidx - n));
                    }
                }
            }
            return none_expr();
        });
}

expr instantiate(expr const & e, unsigned n, expr const * s) {
    return blast::instantiate(e, 0, n, s);
}

expr instantiate_rev(expr const & a, unsigned n, expr const * subst) {
    if (closed(a))
        return a;
    if (auto r = blast::instantiate_easy_fn<true>(n, subst)(a, true))
        return *r;
    return blast::replace(a, [=](expr const & m, unsigned offset) -> optional<expr> {
            if (offset >= get_free_var_range(m))
                return some_expr(m); // expression m does not contain free variables with idx >= offset
            if (is_var(m)) {
                unsigned vidx = var_idx(m);
                if (vidx >= offset) {
                    unsigned h = offset + n;
                    if (h < offset /* overflow, h is bigger than any vidx */ || vidx < h) {
                        return some_expr(blast::lift_free_vars(subst[n - (vidx - offset) - 1], offset));
                    } else {
                        return some_expr(blast::mk_var(vidx - n));
                    }
                }
            }
            return none_expr();
        });
}

class replace_level_fn {
    std::function<optional<level>(level const &)>  m_f;
    level apply(level const & l) {
        optional<level> r = m_f(l);
        if (r)
            return *r;
        switch (l.kind()) {
        case level_kind::Succ:
            return blast::update_succ(l, apply(succ_of(l)));
        case level_kind::Max:
            return blast::update_max(l, apply(max_lhs(l)), apply(max_rhs(l)));
        case level_kind::IMax:
            return blast::update_max(l, apply(imax_lhs(l)), apply(imax_rhs(l)));
        case level_kind::Zero: case level_kind::Param: case level_kind::Meta: case level_kind::Global:
            return l;
        }
        lean_unreachable(); // LCOV_EXCL_LINE
    }
public:
    template<typename F> replace_level_fn(F const & f):m_f(f) {}
    level operator()(level const & l) { return apply(l); }
};

level replace(level const & l, std::function<optional<level>(level const & l)> const & f) {
    return replace_level_fn(f)(l);
}

level instantiate(level const & l, level_param_names const & ps, levels const & ls) {
    lean_assert(length(ps) == length(ls));
    return blast::replace(l, [=](level const & l) {
            if (!has_param(l)) {
                return some_level(l);
            } else if (is_param(l)) {
                name const & id = param_id(l);
                list<name> const *it1 = &ps;
                list<level> const * it2 = &ls;
                while (!is_nil(*it1)) {
                    if (head(*it1) == id)
                        return some_level(head(*it2));
                    it1 = &tail(*it1);
                    it2 = &tail(*it2);
                }
                return some_level(l);
            } else {
                return none_level();
            }
        });
}

expr instantiate_univ_params(expr const & e, level_param_names const & ps, levels const & ls) {
    if (!has_param_univ(e))
        return e;
    return blast::replace(e, [&](expr const & e) -> optional<expr> {
            if (!has_param_univ(e))
                return some_expr(e);
            if (is_constant(e)) {
                levels new_ls = map_reuse(const_levels(e),
                                          [&](level const & l) { return blast::instantiate(l, ps, ls); },
                                          [](level const & l1, level const & l2) { return is_eqp(l1, l2); });
                return some_expr(blast::update_constant(e, new_ls));
            } else if (is_sort(e)) {
                return some_expr(blast::update_sort(e, blast::instantiate(sort_level(e), ps, ls)));
            } else {
                return none_expr();
            }
        });
}

MK_THREAD_LOCAL_GET(instantiate_univ_cache, get_type_univ_cache, LEAN_BLAST_INST_UNIV_CACHE_SIZE);
MK_THREAD_LOCAL_GET(instantiate_univ_cache, get_value_univ_cache, LEAN_BLAST_INST_UNIV_CACHE_SIZE);

expr instantiate_type_univ_params(declaration const & d, levels const & ls) {
    lean_assert(d.get_num_univ_params() == length(ls));
    if (is_nil(ls) || !has_param_univ(d.get_type()))
        return d.get_type();
    instantiate_univ_cache & cache = get_type_univ_cache();
    if (auto r = cache.is_cached(d, ls))
        return *r;
    expr r = blast::instantiate_univ_params(d.get_type(), d.get_univ_params(), ls);
    cache.save(d, ls, r);
    return r;
}

expr instantiate_value_univ_params(declaration const & d, levels const & ls) {
    lean_assert(d.get_num_univ_params() == length(ls));
    if (is_nil(ls) || !has_param_univ(d.get_value()))
        return d.get_value();
    instantiate_univ_cache & cache = get_value_univ_cache();
    if (auto r = cache.is_cached(d, ls))
        return *r;
    expr r = blast::instantiate_univ_params(d.get_value(), d.get_univ_params(), ls);
    cache.save(d, ls, r);
    return r;
}

expr abstract_lrefs(expr const & e, unsigned n, expr const * subst) {
    lean_assert(std::all_of(subst, subst+n, [](expr const & e) { return closed(e) && is_lref(e); }));
    return blast::replace(e, [=](expr const & m, unsigned offset) -> optional<expr> {
            if (is_lref(m)) {
                unsigned i = n;
                while (i > 0) {
                    --i;
                    if (get_lmindex(subst[i]) == get_lmindex(m))
                        return some_expr(blast::mk_var(offset + n - i - 1));
                }
                return none_expr();
            }
            return none_expr();
        });
}
}
}
