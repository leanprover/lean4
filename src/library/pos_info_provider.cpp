/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include "runtime/interrupt.h"
#include "kernel/cache_stack.h"
#include "library/pos_info_provider.h"

namespace lean {
typedef std::unordered_map<void *, pos_info> pos_table;

static pos_table * g_pos_table;
static mutex *     g_pos_table_mutex;

expr save_pos(expr const & e, pos_info const & pos) {
    lock_guard<mutex> _(*g_pos_table_mutex);
    g_pos_table->insert(mk_pair(e.raw(), pos));
    return e;
}

expr copy_pos(expr const & src, expr const & dest) {
    lock_guard<mutex> _(*g_pos_table_mutex);
    auto it = g_pos_table->find(src.raw());
    if (it != g_pos_table->end())
        g_pos_table->insert(mk_pair(dest.raw(), it->second));
    return dest;
}

void erase_pos(expr const & e) {
    lock_guard<mutex> _(*g_pos_table_mutex);
    g_pos_table->erase(e.raw());
}

optional<pos_info> get_pos(expr const & e) {
    lock_guard<mutex> _(*g_pos_table_mutex);
    auto it = g_pos_table->find(e.raw());
    if (it != g_pos_table->end())
        return optional<pos_info>(it->second);
    return optional<pos_info>();
}

void reset_positions() {
    lock_guard<mutex> _(*g_pos_table_mutex);
    g_pos_table->clear();
}

char const * pos_info_provider::get_file_name() const {
    return "unknown";
}

format pos_info_provider::pp(expr const & e) const {
    try {
        auto p = get_pos_info_or_some(e);
        return format(get_file_name()) + colon() + format(p.first) + colon() + format(p.second) + colon();
    } catch (exception &) {
        return format();
    }
}

void initialize_pos_info_provider() {
    g_pos_table = new pos_table();
    g_pos_table_mutex = new mutex;
}

void finalize_pos_info_provider() {
    delete g_pos_table;
    delete g_pos_table_mutex;
}

/* QUICK AND DIRT POSITION PROPAGATION FUNCTIONS */

struct replace_cache2 {
    struct entry {
        object  *   m_cell;
        unsigned    m_offset;
        expr        m_result;
        entry():m_cell(nullptr) {}
    };
    unsigned              m_capacity;
    std::vector<entry>    m_cache;
    std::vector<unsigned> m_used;
    replace_cache2(unsigned c):m_capacity(c), m_cache(c) {}

    expr * find(expr const & e, unsigned offset) {
        unsigned i = hash(hash(e), offset) % m_capacity;
        if (m_cache[i].m_cell == e.raw() && m_cache[i].m_offset == offset)
            return &m_cache[i].m_result;
        else
            return nullptr;
    }

    void insert(expr const & e, unsigned offset, expr const & v) {
        unsigned i = hash(hash(e), offset) % m_capacity;
        if (m_cache[i].m_cell == nullptr)
            m_used.push_back(i);
        m_cache[i].m_cell   = e.raw();
        m_cache[i].m_offset = offset;
        m_cache[i].m_result = v;
    }

    void clear() {
        for (unsigned i : m_used) {
            m_cache[i].m_cell   = nullptr;
            m_cache[i].m_result = expr();
        }
        m_used.clear();
    }
};

MK_CACHE_STACK(replace_cache2, 1024*8)

class replace_rec_fn2 {
    replace_cache2_ref                                    m_cache;
    std::function<optional<expr>(expr const &, unsigned)> m_f;
    bool                                                  m_use_cache;

    expr save_result(expr const & e, unsigned offset, expr const & r, bool shared) {
        if (shared)
            m_cache->insert(e, offset, r);
        return r;
    }

    expr apply(expr const & e, unsigned offset) {
        bool shared = false;
        if (m_use_cache && is_shared(e)) {
            if (auto r = m_cache->find(e, offset))
                return *r;
            shared = true;
        }
        check_system("replace");

        if (optional<expr> r = m_f(e, offset)) {
            return save_result(e, offset, *r, shared);
        } else {
            switch (e.kind()) {
            case expr_kind::Const: case expr_kind::Sort: case expr_kind::BVar:
            case expr_kind::Lit:
                return save_result(e, offset, e, shared);
            case expr_kind::MVar:  case expr_kind::FVar: {
                expr new_t = apply(mlocal_type(e), offset);
                return save_result(e, offset, copy_pos(e, update_mlocal(e, new_t)), shared);
            }
            case expr_kind::MData: {
                expr new_e = apply(mdata_expr(e), offset);
                return save_result(e, offset, copy_pos(e, update_mdata(e, new_e)), shared);
            }
            case expr_kind::Proj: {
                expr new_e = apply(proj_expr(e), offset);
                return save_result(e, offset, copy_pos(e, update_proj(e, new_e)), shared);
            }
            case expr_kind::App: {
                expr new_f = apply(app_fn(e), offset);
                expr new_a = apply(app_arg(e), offset);
                return save_result(e, offset, copy_pos(e, update_app(e, new_f, new_a)), shared);
            }
            case expr_kind::Pi: case expr_kind::Lambda: {
                expr new_d = apply(binding_domain(e), offset);
                expr new_b = apply(binding_body(e), offset+1);
                return save_result(e, offset, copy_pos(e, update_binding(e, new_d, new_b)), shared);
            }
            case expr_kind::Let: {
                expr new_t = apply(let_type(e), offset);
                expr new_v = apply(let_value(e), offset);
                expr new_b = apply(let_body(e), offset+1);
                return save_result(e, offset, copy_pos(e, update_let(e, new_t, new_v, new_b)), shared);
            }
            case expr_kind::Quote:
                return save_result(e, offset, e, shared);
            }
            lean_unreachable();
        }
    }
public:
    template<typename F>
    replace_rec_fn2(F const & f, bool use_cache):m_f(f), m_use_cache(use_cache) {}

    expr operator()(expr const & e) { return apply(e, 0); }
};

expr replace_propagating_pos(expr const & e, std::function<optional<expr>(expr const &, unsigned)> const & f, bool use_cache) {
    return replace_rec_fn2(f, use_cache)(e);
}


template<bool rev>
struct instantiate_easy_fn2 {
    unsigned n;
    expr const * subst;
    instantiate_easy_fn2(unsigned _n, expr const * _subst):n(_n), subst(_subst) {}
    optional<expr> operator()(expr const & a, bool app) const {
        if (!has_loose_bvars(a))
            return some_expr(a);
        if (is_bvar(a) && bvar_idx(a) < n)
            return some_expr(subst[rev ? n - bvar_idx(a).get_small_value() - 1 : bvar_idx(a).get_small_value()]);
        if (app && is_app(a))
        if (auto new_a = operator()(app_arg(a), false))
        if (auto new_f = operator()(app_fn(a), true))
            return some_expr(mk_app(*new_f, *new_a));
        return none_expr();
    }
};

expr instantiate_propagating_pos(expr const & a, unsigned s, unsigned n, expr const * subst) {
    if (
#ifndef LEAN_NO_FREE_VAR_RANGE_OPT
        s >= get_loose_bvar_range(a) ||
#endif
        n == 0)
        return a;
    if (s == 0)
        if (auto r = instantiate_easy_fn2<false>(n, subst)(a, true))
            return *r;
    return replace_propagating_pos(a, [=](expr const & m, unsigned offset) -> optional<expr> {
            unsigned s1 = s + offset;
            if (s1 < s)
                return some_expr(m); // overflow, vidx can't be >= max unsigned
#ifndef LEAN_NO_FREE_VAR_RANGE_OPT
            if (s1 >= get_loose_bvar_range(m))
                return some_expr(m); // expression m does not contain free variables with idx >= s1
#endif
            if (is_var(m)) {
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

expr instantiate_propagating_pos(expr const & e, unsigned n, expr const * s) { return instantiate_propagating_pos(e, 0, n, s); }
expr instantiate_propagating_pos(expr const & e, std::initializer_list<expr> const & l) {  return instantiate_propagating_pos(e, l.size(), l.begin()); }
expr instantiate_propagating_pos(expr const & e, unsigned i, expr const & s) { return instantiate_propagating_pos(e, i, 1, &s); }
expr instantiate_propagating_pos(expr const & e, expr const & s) { return instantiate_propagating_pos(e, 0, s); }

expr abstract_propagating_pos(expr const & e, unsigned n, expr const * subst) {
    lean_assert(std::all_of(subst, subst+n, [](expr const & e) { return !has_loose_bvars(e) && is_local(e); }));
#ifndef LEAN_NO_HAS_LOCAL_OPT
    if (!has_local(e))
        return e;
#endif
    return replace_propagating_pos(e, [=](expr const & m, unsigned offset) -> optional<expr> {
#ifndef LEAN_NO_HAS_LOCAL_OPT
            if (!has_local(m))
                return some_expr(m); // expression m does not contain local constants
#endif
            if (is_local(m)) {
                unsigned i = n;
                while (i > 0) {
                    --i;
                    if (mlocal_name(subst[i]) == mlocal_name(m))
                        return some_expr(mk_bvar(offset + n - i - 1));
                }
                return none_expr();
            }
            return none_expr();
        });
}

expr abstract_propagating_pos(expr const & e, name const & l) {
    expr dummy = mk_Prop();
    expr local = mk_local(l, dummy);
    return abstract_propagating_pos(e, 1, &local);
}

template<bool is_lambda>
expr mk_binding_p(unsigned num, expr const * locals, expr const & b) {
    expr r     = abstract_propagating_pos(b, num, locals);
    unsigned i = num;
    while (i > 0) {
        --i;
        expr const & l = locals[i];
        expr t = abstract_propagating_pos(mlocal_type(l), i, locals);
        if (is_lambda)
            r = mk_lambda(mlocal_pp_name(l), t, r, local_info(l));
        else
            r = mk_pi(mlocal_pp_name(l), t, r, local_info(l));
    }
    return r;
}

expr Pi_p(unsigned num, expr const * locals, expr const & b) { return mk_binding_p<false>(num, locals, b); }
expr Fun_p(unsigned num, expr const * locals, expr const & b) { return mk_binding_p<true>(num, locals, b); }
}
