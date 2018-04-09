/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
        Soonho Kong
*/
#include <vector>
#include <sstream>
#include <string>
#include <algorithm>
#include <limits>
#include "util/list_fn.h"
#include "util/hash.h"
#include "util/buffer.h"
#include "util/object_serializer.h"
#include "util/lru_cache.h"
#include "util/memory_pool.h"
#include "kernel/expr.h"
#include "kernel/expr_eq_fn.h"
#include "kernel/expr_sets.h"
#include "kernel/free_vars.h"
#include "kernel/for_each_fn.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"

#ifndef LEAN_INITIAL_EXPR_CACHE_CAPACITY
#define LEAN_INITIAL_EXPR_CACHE_CAPACITY 1024*16
#endif

namespace lean {
unsigned add_weight(unsigned w1, unsigned w2) {
    unsigned r = w1 + w2;
    if (r < w1)
        r = std::numeric_limits<unsigned>::max(); // overflow
    return r;
}

unsigned inc_weight(unsigned w) {
    if (w < std::numeric_limits<unsigned>::max())
        return w+1;
    else
        return w;
}

static expr * g_dummy = nullptr;
expr::expr():expr(*g_dummy) {}

unsigned hash_levels(levels const & ls) {
    unsigned r = 23;
    for (auto const & l : ls)
        r = hash(hash(l), r);
    return r;
}

#ifdef LEAN_TRACK_LIVE_EXPRS
static atomic<unsigned> g_num_live_exprs(0);
unsigned get_num_live_exprs() {
    return g_num_live_exprs;
}
#endif

expr_cell::expr_cell(expr_kind k, unsigned h, bool has_expr_mv, bool has_univ_mv,
                     bool has_local, bool has_param_univ, tag g):
    m_flags(0),
    m_kind(static_cast<unsigned>(k)),
    m_has_expr_mv(has_expr_mv),
    m_has_univ_mv(has_univ_mv),
    m_has_local(has_local),
    m_has_param_univ(has_param_univ),
    m_hash(h),
    m_tag(g),
    m_rc(0) {
    #ifdef LEAN_TRACK_LIVE_EXPRS
    atomic_fetch_add_explicit(&g_num_live_exprs, 1u, memory_order_release);
    #endif
}

expr_cell::expr_cell(expr_cell const & src):
    m_kind(src.m_kind),
    m_has_expr_mv(src.m_has_expr_mv),
    m_has_univ_mv(src.m_has_univ_mv),
    m_has_local(src.m_has_local),
    m_has_param_univ(src.m_has_param_univ),
    m_hash(src.m_hash),
    m_rc(0) {
    unsigned flgs = src.m_flags;
    unsigned tag  = src.m_tag;
    m_flags = flgs;
    m_tag   = tag;
    #ifdef LEAN_TRACK_LIVE_EXPRS
    atomic_fetch_add_explicit(&g_num_live_exprs, 1u, memory_order_release);
    #endif
}

void expr_cell::dec_ref(expr & e, buffer<expr_cell*> & todelete) {
    if (e.m_ptr) {
        expr_cell * c = e.steal_ptr();
        lean_assert(!(e.m_ptr));
        if (c->dec_ref_core())
            todelete.push_back(c);
    }
}

optional<bool> expr_cell::is_arrow() const {
    // it is stored in bits 0-1
    unsigned r = (m_flags & (1+2));
    if (r == 0) {
        return optional<bool>();
    } else if (r == 1) {
        return optional<bool>(true);
    } else {
        lean_assert(r == 2);
        return optional<bool>(false);
    }
}

void expr_cell::set_is_arrow(bool flag) {
    unsigned mask = flag ? 1 : 2;
    m_flags |= mask;
    lean_assert(is_arrow() && *is_arrow() == flag);
}

void expr_cell::set_tag(tag t) {
    m_tag = t;
}

bool is_meta(expr const & e) {
    return is_metavar(get_app_fn(e));
}

// Expr variables
DEF_THREAD_MEMORY_POOL(get_var_allocator, sizeof(expr_var));
expr_var::expr_var(unsigned idx, tag g):
    expr_cell(expr_kind::Var, idx, false, false, false, false, g),
    m_vidx(idx) {
    if (idx == std::numeric_limits<unsigned>::max())
        throw exception("invalid free variable index, de Bruijn index is too big");
}
void expr_var::dealloc() {
    this->~expr_var();
    get_var_allocator().recycle(this);
}

// Expr constants
DEF_THREAD_MEMORY_POOL(get_const_allocator, sizeof(expr_const));
expr_const::expr_const(name const & n, levels const & ls, tag g):
    expr_cell(expr_kind::Constant, ::lean::hash(n.hash(), hash_levels(ls)), false,
              has_meta(ls), false, has_param(ls), g),
    m_name(n),
    m_levels(ls) {
}
void expr_const::dealloc() {
    this->~expr_const();
    get_const_allocator().recycle(this);
}

unsigned binder_info::hash() const {
    return (m_rec << 3) |  (m_implicit << 2) | (m_strict_implicit << 1) | m_inst_implicit;
}

// Expr metavariables and local variables
DEF_THREAD_MEMORY_POOL(get_mlocal_allocator, sizeof(expr_mlocal));
expr_mlocal::expr_mlocal(bool is_meta, name const & n, name const & pp_n, expr const & t, tag g):
    expr_composite(is_meta ? expr_kind::Meta : expr_kind::Local, n.hash(), is_meta || t.has_expr_metavar(), t.has_univ_metavar(),
                   !is_meta || t.has_local(), t.has_param_univ(),
                   1, get_free_var_range(t), g),
    m_name(n),
    m_pp_name(pp_n),
    m_type(t) {}

void expr_mlocal::dealloc(buffer<expr_cell*> & todelete) {
    dec_ref(m_type, todelete);
    this->~expr_mlocal();
    get_mlocal_allocator().recycle(this);
}

expr_mlocal::expr_mlocal(expr_mlocal const & src, expr const & new_type):
    expr_composite(src), m_name(src.m_name), m_pp_name(src.m_pp_name), m_type(new_type) {}

DEF_THREAD_MEMORY_POOL(get_local_allocator, sizeof(expr_local));
expr_local::expr_local(name const & n, name const & pp_n, expr const & t, binder_info const & bi, tag g):
    expr_mlocal(false, n, pp_n, t, g), m_bi(bi) {}

expr_local::expr_local(expr_local const & src, expr const & new_type):
    expr_mlocal(src, new_type), m_bi(src.m_bi) {}

void expr_local::dealloc(buffer<expr_cell*> & todelete) {
    dec_ref(m_type, todelete);
    this->~expr_local();
    get_local_allocator().recycle(this);
}

expr_composite::expr_composite(expr_composite const & src):
    expr_cell(src),
    m_weight(src.m_weight),
    m_depth(src.m_depth),
    m_free_var_range(src.m_free_var_range) {
}

// Composite expressions
expr_composite::expr_composite(expr_kind k, unsigned h, bool has_expr_mv, bool has_univ_mv,
                               bool has_local, bool has_param_univ, unsigned w, unsigned fv_range, tag g):
    expr_cell(k, h, has_expr_mv, has_univ_mv, has_local, has_param_univ, g),
    m_weight(w),
    m_depth(0),
    m_free_var_range(fv_range) {}

// Expr applications
DEF_THREAD_MEMORY_POOL(get_app_allocator, sizeof(expr_app));
expr_app::expr_app(expr const & fn, expr const & arg, tag g):
    expr_composite(expr_kind::App, ::lean::hash(fn.hash(), arg.hash()),
                   fn.has_expr_metavar() || arg.has_expr_metavar(),
                   fn.has_univ_metavar() || arg.has_univ_metavar(),
                   fn.has_local()        || arg.has_local(),
                   fn.has_param_univ()   || arg.has_param_univ(),
                   inc_weight(add_weight(get_weight(fn), get_weight(arg))),
                   std::max(get_free_var_range(fn), get_free_var_range(arg)),
                   g),
    m_fn(fn), m_arg(arg) {
    m_depth = std::max(get_depth(fn), get_depth(arg)) + 1;
    m_hash  = ::lean::hash(m_hash, m_weight);
    m_hash  = ::lean::hash(m_hash, m_depth);
}

expr_app::expr_app(expr_app const & src, expr const & new_fn, expr const & new_arg):
    expr_composite(src), m_fn(new_fn), m_arg(new_arg) {}

void expr_app::dealloc(buffer<expr_cell*> & todelete) {
    dec_ref(m_fn, todelete);
    dec_ref(m_arg, todelete);
    this->~expr_app();
    get_app_allocator().recycle(this);
}

static unsigned dec(unsigned k) { return k == 0 ? 0 : k - 1; }

bool operator==(binder_info const & i1, binder_info const & i2) {
    return
        i1.is_implicit() == i2.is_implicit() &&
        i1.is_strict_implicit() == i2.is_strict_implicit() &&
        i1.is_inst_implicit() == i2.is_inst_implicit() &&
        i1.is_rec() == i2.is_rec();
}

// Expr binders (Lambda, Pi)
DEF_THREAD_MEMORY_POOL(get_binding_allocator, sizeof(expr_binding));
expr_binding::expr_binding(expr_kind k, name const & n, expr const & t, expr const & b, binder_info const & i, tag g):
    expr_composite(k, ::lean::hash(t.hash(), b.hash()),
                   t.has_expr_metavar()   || b.has_expr_metavar(),
                   t.has_univ_metavar()   || b.has_univ_metavar(),
                   t.has_local()          || b.has_local(),
                   t.has_param_univ()     || b.has_param_univ(),
                   inc_weight(add_weight(get_weight(t), get_weight(b))),
                   std::max(get_free_var_range(t), dec(get_free_var_range(b))),
                   g),
    m_binder(n, t, i),
    m_body(b) {
    m_depth = std::max(get_depth(t), get_depth(b)) + 1;
    m_hash  = ::lean::hash(m_hash, m_weight);
    m_hash  = ::lean::hash(m_hash, m_depth);
    lean_assert(k == expr_kind::Lambda || k == expr_kind::Pi);
}

expr_binding::expr_binding(expr_binding const & src, expr const & d, expr const & b):
    expr_composite(src), m_binder(src.m_binder, d), m_body(b) {}

void expr_binding::dealloc(buffer<expr_cell*> & todelete) {
    dec_ref(m_body, todelete);
    dec_ref(m_binder.m_type, todelete);
    this->~expr_binding();
    get_binding_allocator().recycle(this);
}

// Expr Sort
DEF_THREAD_MEMORY_POOL(get_sort_allocator, sizeof(expr_sort));
expr_sort::expr_sort(level const & l, tag g):
    expr_cell(expr_kind::Sort, ::lean::hash(l), false, has_meta(l), false, has_param(l), g),
    m_level(l) {
}
expr_sort::~expr_sort() {}
void expr_sort::dealloc() {
    this->~expr_sort();
    get_sort_allocator().recycle(this);
}

// Let expressions
DEF_THREAD_MEMORY_POOL(get_let_allocator, sizeof(expr_let));
expr_let::expr_let(name const & n, expr const & t, expr const & v, expr const & b, tag g):
    expr_composite(expr_kind::Let,
                   ::lean::hash(::lean::hash(t.hash(), v.hash()), b.hash()),
                   t.has_expr_metavar()   || v.has_expr_metavar() || b.has_expr_metavar(),
                   t.has_univ_metavar()   || v.has_univ_metavar() || b.has_univ_metavar(),
                   t.has_local()          || v.has_local() || b.has_local(),
                   t.has_param_univ()     || v.has_param_univ() || b.has_param_univ(),
                   inc_weight(add_weight(add_weight(get_weight(t), get_weight(v)), get_weight(b))),
                   std::max(std::max(get_free_var_range(t), get_free_var_range(v)), dec(get_free_var_range(b))),
                   g),
    m_name(n), m_type(t), m_value(v), m_body(b) {
    m_depth = std::max(get_depth(t), std::max(get_depth(v), get_depth(b))) + 1;
    m_hash  = ::lean::hash(m_hash, m_weight);
    m_hash  = ::lean::hash(m_hash, m_depth);
}

expr_let::expr_let(expr_let const & src, expr const & t, expr const & v, expr const & b):
    expr_composite(src), m_name(src.m_name), m_type(t), m_value(v), m_body(b) {}

void expr_let::dealloc(buffer<expr_cell*> & todelete) {
    dec_ref(m_body,  todelete);
    dec_ref(m_value, todelete);
    dec_ref(m_type,  todelete);
    this->~expr_let();
    get_let_allocator().recycle(this);
}

// Macro definition
bool macro_definition_cell::lt(macro_definition_cell const &) const { return false; }
bool macro_definition_cell::operator==(macro_definition_cell const & other) const { return typeid(*this) == typeid(other); }
unsigned macro_definition_cell::trust_level() const { return 0; }

void macro_definition_cell::display(std::ostream & out) const { out << get_name(); }
unsigned macro_definition_cell::hash() const { return get_name().hash(); }

macro_definition::macro_definition(macro_definition_cell * ptr):m_ptr(ptr) { lean_assert(m_ptr); m_ptr->inc_ref(); }
macro_definition::macro_definition(macro_definition const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
macro_definition::macro_definition(macro_definition && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
macro_definition::~macro_definition() { if (m_ptr) m_ptr->dec_ref(); }
macro_definition & macro_definition::operator=(macro_definition const & s) { LEAN_COPY_REF(s); }
macro_definition & macro_definition::operator=(macro_definition && s) { LEAN_MOVE_REF(s); }
bool macro_definition::operator<(macro_definition const & other) const {
    if (get_name() == other.get_name())
        return m_ptr->lt(*other.m_ptr);
    else
        return get_name() < other.get_name();
}

static unsigned add_weight(unsigned num, expr const * args) {
    unsigned r = 0;
    for (unsigned i = 0; i < num; i++)
        r = add_weight(r, get_weight(args[i]));
    return r;
}

static unsigned get_free_var_range(unsigned num, expr const * args) {
    unsigned r = 0;
    for (unsigned i = 0; i < num; i++) {
        unsigned d = get_free_var_range(args[i]);
        if (d > r)
            r = d;
    }
    return r;
}

expr_macro::expr_macro(expr_macro const & src, expr const * new_args):
    expr_composite(src),
    m_definition(src.m_definition),
    m_num_args(src.m_num_args) {
    expr * data = get_args_ptr();
    std::uninitialized_copy(new_args, new_args + m_num_args, data);
}

expr_macro::expr_macro(macro_definition const & m, unsigned num, expr const * args, tag g):
    expr_composite(expr_kind::Macro,
                   lean::hash(num, [&](unsigned i) { return args[i].hash(); }, m.hash()),
                   std::any_of(args, args+num, [](expr const & e) { return e.has_expr_metavar(); }),
                   std::any_of(args, args+num, [](expr const & e) { return e.has_univ_metavar(); }),
                   std::any_of(args, args+num, [](expr const & e) { return e.has_local(); }),
                   std::any_of(args, args+num, [](expr const & e) { return e.has_param_univ(); }),
                   inc_weight(add_weight(num, args)),
                   get_free_var_range(num, args),
                   g),
    m_definition(m),
    m_num_args(num) {
    expr * data = get_args_ptr();
    m_depth = 0;
    for (unsigned i = 0; i < num; i++) {
        unsigned d = get_depth(args[i]);
        if (d > m_depth)
            m_depth = d;
    }
    m_depth++;
    std::uninitialized_copy(args, args + num, data);
}
void expr_macro::dealloc(buffer<expr_cell*> & todelete) {
    expr * args = get_args_ptr();
    for (unsigned i = 0; i < m_num_args; i++) dec_ref(args[i], todelete);
    this->~expr_macro();
    char * mem = reinterpret_cast<char*>(this);
    delete[] mem;
}
expr_macro::~expr_macro() {}

// =======================================
// Constructors
LEAN_THREAD_VALUE(bool, g_expr_cache_enabled, false);
typedef typename std::unordered_set<expr, expr_hash, is_bi_equal_proc> expr_cache;
/* CACHE_RESET: NO */
MK_THREAD_LOCAL_GET_DEF(expr_cache, get_expr_cache);

struct cache_expr_insert_fn {
    expr_cache & m_cache;
    cache_expr_insert_fn(expr_cache & c):m_cache(c) {}

    expr insert_macro(expr const & e) {
        buffer<expr> new_args;
        bool updated = false;
        unsigned num = macro_num_args(e);
        for (unsigned i = 0; i < num; i++) {
            expr const & arg = macro_arg(e, i);
            new_args.push_back(insert(arg));
            if (!is_eqp(arg, new_args.back()))
                updated = true;
        }
        if (updated) {
            char * mem = new char[sizeof(expr_macro) + num*sizeof(expr const *)];
            return expr(new (mem) expr_macro(*to_macro(e), new_args.data()));
        } else {
            return e;
        }
    }

    expr insert_meta(expr const & e) {
        expr new_type = insert(mlocal_type(e));
        if (is_eqp(new_type, mlocal_type(e))) {
            return e;
        } else {
            return expr(new (get_mlocal_allocator().allocate()) expr_mlocal(*to_mlocal(e), new_type));
        }
    }

    expr insert_local(expr const & e) {
        expr new_type = insert(mlocal_type(e));
        if (is_eqp(new_type, mlocal_type(e))) {
            return e;
        } else {
            return expr(new (get_local_allocator().allocate()) expr_local(*to_local(e), new_type));
        }
    }

    expr insert_constant(expr const & e) {
        /* TODO(Leo): similar insert for levels */
        return e;
    }

    expr insert_sort(expr const & e) {
        /* TODO(Leo): similar insert for levels */
        return e;
    }

    expr insert_app(expr const & e) {
        expr new_fn  = insert(app_fn(e));
        expr new_arg = insert(app_arg(e));
        if (is_eqp(new_fn, app_fn(e)) && is_eqp(new_arg, app_arg(e))) {
            return e;
        } else {
            return expr(new (get_app_allocator().allocate()) expr_app(*to_app(e), new_fn, new_arg));
        }
    }

    expr insert_binding(expr const & e) {
        expr new_domain = insert(binding_domain(e));
        expr new_body   = insert(binding_body(e));
        if (is_eqp(new_domain, binding_domain(e)) && is_eqp(new_body, binding_body(e))) {
            return e;
        } else {
            return expr(new (get_binding_allocator().allocate()) expr_binding(*to_binding(e), new_domain, new_body));
        }
    }

    expr insert_let(expr const & e) {
        expr new_type  = insert(let_type(e));
        expr new_value = insert(let_value(e));
        expr new_body  = insert(let_body(e));
        if (is_eqp(new_type, let_type(e)) && is_eqp(new_value, let_value(e)) && is_eqp(new_body, let_body(e))) {
            return e;
        } else {
            return expr(new (get_let_allocator().allocate()) expr_let(*to_let(e), new_type, new_value, new_body));
        }
        return e;
    }

    expr insert(expr const & e) {
        auto it = m_cache.find(e);
        if (it != m_cache.end()) {
            return *it;
        }
        expr new_e;
        switch (e.kind()) {
        case expr_kind::Var:       new_e = e;                  break;
        case expr_kind::Macro:     new_e = insert_macro(e);    break;
        case expr_kind::Meta:      new_e = insert_meta(e);     break;
        case expr_kind::Local:     new_e = insert_local(e);    break;
        case expr_kind::Constant:  new_e = insert_constant(e); break;
        case expr_kind::Sort:      new_e = insert_sort(e);     break;
        case expr_kind::App:       new_e = insert_app(e);      break;
        case expr_kind::Lambda:    new_e = insert_binding(e);  break;
        case expr_kind::Pi:        new_e = insert_binding(e);  break;
        case expr_kind::Let:       new_e = insert_let(e);      break;
        }
        m_cache.insert(new_e);
        return new_e;
    }

    expr operator()(expr const & e) { return insert(e); }
};

inline expr cache(expr const & e) {
    if (g_expr_cache_enabled)
        return cache_expr_insert_fn(get_expr_cache())(e);
    else
        return e;
}
bool enable_expr_caching(bool f) {
    DEBUG_CODE(bool r1 =) enable_level_caching(f);
    bool r2 = g_expr_cache_enabled;
    lean_assert(r1 == r2);
    cache(mk_Prop());
    cache(mk_Type());
    if (f) {
        clear_abstract_cache();
        clear_instantiate_cache();
    }
    g_expr_cache_enabled = f;
    return r2;
}
bool is_cached(expr const & e) {
    return get_expr_cache().find(e) != get_expr_cache().end();
}
void flush_expr_cache() {
    flush_level_cache();
    expr_cache new_cache;
    get_expr_cache().swap(new_cache);
    clear_abstract_cache();
    clear_instantiate_cache();
}
expr mk_var(unsigned idx, tag g) {
    return cache(expr(new (get_var_allocator().allocate()) expr_var(idx, g)));
}
expr mk_constant(name const & n, levels const & ls, tag g) {
    return cache(expr(new (get_const_allocator().allocate()) expr_const(n, ls, g)));
}
expr mk_macro(macro_definition const & m, unsigned num, expr const * args, tag g) {
    char * mem = new char[sizeof(expr_macro) + num*sizeof(expr const *)];
    return cache(expr(new (mem) expr_macro(m, num, args, g)));
}
expr mk_metavar(name const & n, name const & pp_n, expr const & t, tag g) {
    return cache(expr(new (get_mlocal_allocator().allocate()) expr_mlocal(true, n, pp_n, t, g)));
}
expr mk_metavar(name const & n, expr const & t, tag g) {
    return mk_metavar(n, n, t, g);
}
expr mk_local(name const & n, name const & pp_n, expr const & t, binder_info const & bi, tag g) {
    return cache(expr(new (get_local_allocator().allocate()) expr_local(n, pp_n, t, bi, g)));
}
expr mk_app(expr const & f, expr const & a, tag g) {
    return cache(expr(new (get_app_allocator().allocate()) expr_app(f, a, g)));
}
expr mk_binding(expr_kind k, name const & n, expr const & t, expr const & e, binder_info const & i, tag g) {
    return cache(expr(new (get_binding_allocator().allocate()) expr_binding(k, n, t, e, i, g)));
}
expr mk_let(name const & n, expr const & t, expr const & v, expr const & b, tag g) {
    return cache(expr(new (get_let_allocator().allocate()) expr_let(n, t, v, b, g)));
}
expr mk_sort(level const & l, tag g) {
    return cache(expr(new (get_sort_allocator().allocate()) expr_sort(l, g)));
}
// =======================================

typedef buffer<expr_cell*> del_buffer;
void expr_cell::dealloc() {
    try {
        del_buffer todo;
        todo.push_back(this);
        while (!todo.empty()) {
            expr_cell * it = todo.back();
            todo.pop_back();
            #ifdef LEAN_TRACK_LIVE_EXPRS
            atomic_fetch_sub_explicit(&g_num_live_exprs, 1u, memory_order_release);
            #endif
            lean_assert(it->get_rc() == 0);
            switch (it->kind()) {
            case expr_kind::Var:        static_cast<expr_var*>(it)->dealloc(); break;
            case expr_kind::Macro:      static_cast<expr_macro*>(it)->dealloc(todo); break;
            case expr_kind::Meta:       static_cast<expr_mlocal*>(it)->dealloc(todo); break;
            case expr_kind::Local:      static_cast<expr_local*>(it)->dealloc(todo); break;
            case expr_kind::Constant:   static_cast<expr_const*>(it)->dealloc(); break;
            case expr_kind::Sort:       static_cast<expr_sort*>(it)->dealloc(); break;
            case expr_kind::App:        static_cast<expr_app*>(it)->dealloc(todo); break;
            case expr_kind::Lambda:
            case expr_kind::Pi:         static_cast<expr_binding*>(it)->dealloc(todo); break;
            case expr_kind::Let:        static_cast<expr_let*>(it)->dealloc(todo); break;
           }
        }
    } catch (std::bad_alloc&) {
        // We need this catch, because push_back may fail when expanding the buffer.
        // In this case, we avoid the crash, and "accept" the memory leak.
    }
}

// Auxiliary constructors
expr mk_app(expr const & f, unsigned num_args, expr const * args, tag g) {
    expr r = f;
    for (unsigned i = 0; i < num_args; i++)
        r = mk_app(r, args[i], g);
    return r;
}

expr mk_app(unsigned num_args, expr const * args, tag g) {
    lean_assert(num_args >= 2);
    return mk_app(mk_app(args[0], args[1], g), num_args - 2, args+2, g);
}

expr mk_app(expr const & f, list<expr> const & args, tag g) {
    buffer<expr> _args;
    to_buffer(args, _args);
    return mk_app(f, _args, g);
}

expr mk_rev_app(expr const & f, unsigned num_args, expr const * args, tag g) {
    expr r = f;
    unsigned i = num_args;
    while (i > 0) {
        --i;
        r = mk_app(r, args[i], g);
    }
    return r;
}

expr mk_rev_app(unsigned num_args, expr const * args, tag g) {
    lean_assert(num_args >= 2);
    return mk_rev_app(mk_app(args[num_args-1], args[num_args-2], g), num_args-2, args, g);
}

expr mk_app_vars(expr const & f, unsigned n, tag g) {
    expr r = f;
    while (n > 0) {
        --n;
        r = mk_app(r, mk_var(n, g), g);
    }
    return r;
}

expr const & get_app_args(expr const & e, buffer<expr> & args) {
    unsigned sz = args.size();
    expr const * it = &e;
    while (is_app(*it)) {
        args.push_back(app_arg(*it));
        it = &(app_fn(*it));
    }
    std::reverse(args.begin() + sz, args.end());
    return *it;
}

expr const & get_app_args_at_most(expr const & e, unsigned num, buffer<expr> & args) {
    unsigned sz = args.size();
    expr const * it = &e;
    unsigned i = 0;
    while (is_app(*it)) {
        if (i == num)
            break;
        args.push_back(app_arg(*it));
        it = &(app_fn(*it));
        i++;
    }
    std::reverse(args.begin() + sz, args.end());
    return *it;
}

expr const & get_app_rev_args(expr const & e, buffer<expr> & args) {
    expr const * it = &e;
    while (is_app(*it)) {
        args.push_back(app_arg(*it));
        it = &(app_fn(*it));
    }
    return *it;
}

expr const & get_app_fn(expr const & e) {
    expr const * it = &e;
    while (is_app(*it)) {
        it = &(app_fn(*it));
    }
    return *it;
}

unsigned get_app_num_args(expr const & e) {
    expr const * it = &e;
    unsigned n = 0;
    while (is_app(*it)) {
        it = &(app_fn(*it));
        n++;
    }
    return n;
}

static name * g_default_name = nullptr;
static name const & get_default_var_name() {
    return *g_default_name;
}

bool is_default_var_name(name const & n) { return n == get_default_var_name(); }
expr mk_arrow(expr const & t, expr const & e, tag g) {
    return mk_pi(get_default_var_name(), t, e, binder_info(), g);
}

static expr * g_Prop  = nullptr;
static expr * g_Type1 = nullptr;
expr mk_Prop() { return *g_Prop; }
expr mk_Type() { return *g_Type1; }

unsigned get_weight(expr const & e) {
    switch (e.kind()) {
    case expr_kind::Var:  case expr_kind::Constant: case expr_kind::Sort:
    case expr_kind::Meta: case expr_kind::Local:
        return 1;
    case expr_kind::Lambda: case expr_kind::Pi:  case expr_kind::Macro:
    case expr_kind::App:    case expr_kind::Let:
        return static_cast<expr_composite*>(e.raw())->m_weight;
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

unsigned get_depth(expr const & e) {
    switch (e.kind()) {
    case expr_kind::Var:  case expr_kind::Constant: case expr_kind::Sort:
    case expr_kind::Meta: case expr_kind::Local:
        return 1;
    case expr_kind::Lambda: case expr_kind::Pi:  case expr_kind::Macro:
    case expr_kind::App:    case expr_kind::Let:
        return static_cast<expr_composite*>(e.raw())->m_depth;
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

expr copy_tag(expr const & e, expr && new_e) {
    tag t = e.get_tag();
    if (t != nulltag)
        new_e.set_tag(t);
    return new_e;
}

expr update_app(expr const & e, expr const & new_fn, expr const & new_arg) {
    if (!is_eqp(app_fn(e), new_fn) || !is_eqp(app_arg(e), new_arg))
        return mk_app(new_fn, new_arg, e.get_tag());
    else
        return e;
}

expr update_binding(expr const & e, expr const & new_domain, expr const & new_body) {
    if (!is_eqp(binding_domain(e), new_domain) || !is_eqp(binding_body(e), new_body))
        return mk_binding(e.kind(), binding_name(e), new_domain, new_body, binding_info(e), e.get_tag());
    else
        return e;
}

expr update_binding(expr const & e, expr const & new_domain, expr const & new_body, binder_info const & bi) {
    if (!is_eqp(binding_domain(e), new_domain) || !is_eqp(binding_body(e), new_body) || bi != binding_info(e))
        return mk_binding(e.kind(), binding_name(e), new_domain, new_body, bi, e.get_tag());
    else
        return e;
}

expr update_mlocal(expr const & e, expr const & new_type) {
    if (is_eqp(mlocal_type(e), new_type))
        return e;
    else if (is_metavar(e))
        return mk_metavar(mlocal_name(e), mlocal_pp_name(e), new_type, e.get_tag());
    else
        return mk_local(mlocal_name(e), mlocal_pp_name(e), new_type, local_info(e), e.get_tag());
}

expr update_local(expr const & e, expr const & new_type, binder_info const & bi) {
    if (is_eqp(mlocal_type(e), new_type) && local_info(e) == bi)
        return e;
    else
        return mk_local(mlocal_name(e), mlocal_pp_name(e), new_type, bi, e.get_tag());
}

expr update_local(expr const & e, binder_info const & bi) {
    return update_local(e, mlocal_type(e), bi);
}

expr update_sort(expr const & e, level const & new_level) {
    if (!is_eqp(sort_level(e), new_level))
        return mk_sort(new_level, e.get_tag());
    else
        return e;
}

expr update_constant(expr const & e, levels const & new_levels) {
    if (!is_eqp(const_levels(e), new_levels))
        return mk_constant(const_name(e), new_levels, e.get_tag());
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
    return mk_macro(to_macro(e)->m_definition, num, args, e.get_tag());
}

expr update_let(expr const & e, expr const & new_type, expr const & new_value, expr const & new_body) {
    if (!is_eqp(let_type(e), new_type) || !is_eqp(let_value(e), new_value) || !is_eqp(let_body(e), new_body))
        return mk_let(let_name(e), new_type, new_value, new_body);
    else
        return e;
}

bool is_atomic(expr const & e) {
    switch (e.kind()) {
    case expr_kind::Constant: case expr_kind::Sort:
    case expr_kind::Var:
        return true;
    case expr_kind::Macro:
        return to_macro(e)->get_num_args() == 0;
    case expr_kind::App:      case expr_kind::Meta:
    case expr_kind::Local:    case expr_kind::Lambda:
    case expr_kind::Pi:       case expr_kind::Let:
        return false;
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

bool is_arrow(expr const & t) {
    optional<bool> r = t.raw()->is_arrow();
    if (r) {
        return *r;
    } else {
        bool res = is_pi(t) && !has_free_var(binding_body(t), 0);
        t.raw()->set_is_arrow(res);
        return res;
    }
}

optional<expr> has_expr_metavar_strict(expr const & e) {
    if (!has_expr_metavar(e))
        return none_expr();
    optional<expr> r;
    for_each(e, [&](expr const & e, unsigned) {
            if (r || !has_expr_metavar(e)) return false;
            if (is_meta(e)) { r = e; return false; }
            if (is_local(e)) return false; // do not visit type
            return true;
        });
    return r;
}

static bool has_free_var_in_domain(expr const & b, unsigned vidx, bool strict) {
    if (is_pi(b)) {
        return
            (has_free_var(binding_domain(b), vidx) && is_explicit(binding_info(b))) ||
            has_free_var_in_domain(binding_body(b), vidx+1, strict);
    } else if (!strict) {
        return has_free_var(b, vidx);
    } else {
        return false;
    }
}

expr infer_implicit(expr const & t, unsigned num_params, bool strict) {
    if (num_params == 0) {
        return t;
    } else if (is_pi(t)) {
        expr new_body = infer_implicit(binding_body(t), num_params-1, strict);
        if (binding_info(t).is_implicit() || binding_info(t).is_strict_implicit() || binding_info(t).is_inst_implicit()) {
            // argument is already marked as implicit
            return update_binding(t, binding_domain(t), new_body);
        } else if (has_free_var_in_domain(new_body, 0, strict)) {
            return update_binding(t, binding_domain(t), new_body, mk_implicit_binder_info());
        } else {
            return update_binding(t, binding_domain(t), new_body);
        }
    } else {
        return t;
    }
}

expr infer_implicit(expr const & t, bool strict) {
    return infer_implicit(t, std::numeric_limits<unsigned>::max(), strict);
}

unsigned hash_bi(expr const & e) {
    unsigned h = e.hash();
    for_each(e, [&](expr const & e, unsigned) {
            if (is_binding(e)) {
                h = hash(h, hash(binding_name(e).hash(), binding_info(e).hash()));
            } else if (is_local(e)) {
                h = hash(h, hash(mlocal_name(e).hash(), local_info(e).hash()));
                return false; // do not visit type
            } else if (is_metavar(e)) {
                return false; // do not visit type
            }
            return true;
        });
    return h;
}

std::ostream & operator<<(std::ostream & out, expr_kind const & k) {
    switch (k) {
    case expr_kind::Var:      out << "Var"; break;
    case expr_kind::Sort:     out << "Sort"; break;
    case expr_kind::Constant: out << "Constant"; break;
    case expr_kind::Meta:     out << "Meta"; break;
    case expr_kind::Local:    out << "Local"; break;
    case expr_kind::App:      out << "App"; break;
    case expr_kind::Lambda:   out << "Lambda"; break;
    case expr_kind::Pi:       out << "Pi"; break;
    case expr_kind::Macro:    out << "Macro"; break;
    case expr_kind::Let:      out << "Let"; break;
    }
    return out;
}

void initialize_expr() {
    g_dummy        = new expr(mk_constant("__expr_for_default_constructor__"));
    g_default_name = new name("a");
    g_Type1        = new expr(mk_sort(mk_level_one()));
    g_Prop         = new expr(mk_sort(mk_level_zero()));
}

void finalize_expr() {
    delete g_Prop;
    delete g_Type1;
    delete g_dummy;
    delete g_default_name;
}
}
