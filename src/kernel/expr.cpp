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
#include "kernel/expr.h"
#include "kernel/expr_eq_fn.h"
#include "kernel/expr_sets.h"
#include "kernel/for_each_fn.h"
#include "kernel/replace_fn.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"

#ifndef LEAN_INITIAL_EXPR_CACHE_CAPACITY
#define LEAN_INITIAL_EXPR_CACHE_CAPACITY 1024*16
#endif

namespace lean {
/* Expression literal values */
literal::literal(char const * v):
    object_ref(mk_cnstr(static_cast<unsigned>(literal_kind::String), mk_string(v))) {
}

literal::literal(unsigned v):
    object_ref(mk_cnstr(static_cast<unsigned>(literal_kind::Nat), mk_nat_obj(v))) {
}

literal::literal(mpz const & v):
    object_ref(mk_cnstr(static_cast<unsigned>(literal_kind::Nat), mk_nat_obj(v))) {
}

bool operator==(literal const & a, literal const & b) {
    if (a.kind() != b.kind()) return false;
    switch (a.kind()) {
    case literal_kind::String: return a.get_string() == b.get_string();
    case literal_kind::Nat:    return a.get_nat() == b.get_nat();
    }
    lean_unreachable();
}

bool operator<(literal const & a, literal const & b) {
    if (a.kind() != b.kind()) return static_cast<unsigned>(a.kind()) < static_cast<unsigned>(b.kind());
    switch (a.kind()) {
    case literal_kind::String: return a.get_string() < b.get_string();
    case literal_kind::Nat:    return a.get_nat() < b.get_nat();
    }
    lean_unreachable();
}

/* Auxiliary functions for computing scalar data offset into expression objects. */
inline constexpr unsigned num_obj_fields(expr_kind k) {
    switch (k) {
    case expr_kind::BVar:     return 1;
    case expr_kind::FVar:     return 3; // TODO(Leo): it should be 1 after we remove support for legacy code
    case expr_kind::Sort:     return 1;
    case expr_kind::Constant: return 2;
    case expr_kind::MVar:     return 3; // TODO(Leo): it should be 2 after we remove support for legacy code
    case expr_kind::App:      return 2;
    case expr_kind::Lambda:   return 3;
    case expr_kind::Pi:       return 3;
    case expr_kind::Let:      return 4;
    case expr_kind::Lit:      return 1;
    case expr_kind::MData:    return 2;
    case expr_kind::Proj:     return 2;
    case expr_kind::Quote:    return 1;
    }
    lean_unreachable();
}

/* Expression scalar data offset. */
inline constexpr unsigned scalar_offset(expr_kind k) { return num_obj_fields(k) * sizeof(object*); }

inline constexpr unsigned hash_offset(expr_kind k) {
    /* Remark: the hidden extra cached data (hash, weight, depth, loose_bvar_range) must be stored AFTER the real fields. */
    switch (k) {
    case expr_kind::FVar:     return scalar_offset(k) + sizeof(unsigned char); // for binder_info, TODO(Leo): delete after we remove support for legacy code
    case expr_kind::Lambda:   return scalar_offset(k) + sizeof(unsigned char); // for binder_info
    case expr_kind::Pi:       return scalar_offset(k) + sizeof(unsigned char); // for binder_info
    default:                  return scalar_offset(k);
    }
    lean_unreachable();
}

inline constexpr size_t flags_offset(expr_kind k) { return hash_offset(k) + sizeof(unsigned); }
inline constexpr size_t weight_offset(expr_kind k) { return flags_offset(k) + sizeof(unsigned char); }
inline constexpr size_t depth_offset(expr_kind k) { return weight_offset(k) + sizeof(unsigned); }
inline constexpr size_t loose_bvar_range_offset(expr_kind k) { return depth_offset(k) + sizeof(unsigned); }
/* Size for scalar value area for non recursive expression. */
inline constexpr size_t expr_scalar_size(expr_kind k) { return flags_offset(k) + sizeof(unsigned char); }
/* Size for scalar value area for recursive expression. */
inline constexpr size_t recursive_expr_scalar_size(expr_kind k) { return loose_bvar_range_offset(k) + sizeof(unsigned); }


/* Weight safe arith functions */
static unsigned add_weight(unsigned w1, unsigned w2) {
    unsigned r = w1 + w2;
    if (r < w1)
        r = std::numeric_limits<unsigned>::max(); // overflow
    return r;
}

static unsigned inc_weight(unsigned w) {
    if (w < std::numeric_limits<unsigned>::max())
        return w+1;
    else
        return w;
}

static expr * g_nat_type    = nullptr;
static expr * g_string_type = nullptr;

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
                     bool has_fvar, bool has_param_univ):
    m_flags(0),
    m_kind(static_cast<unsigned>(k)),
    m_has_expr_mv(has_expr_mv),
    m_has_univ_mv(has_univ_mv),
    m_has_fvar(has_fvar),
    m_has_param_univ(has_param_univ),
    m_hash(h),
    m_rc(0) {
    #ifdef LEAN_TRACK_LIVE_EXPRS
    atomic_fetch_add_explicit(&g_num_live_exprs, 1u, memory_order_release);
    #endif
}

expr_cell::expr_cell(expr_cell const & src):
    m_kind(src.m_kind),
    m_has_expr_mv(src.m_has_expr_mv),
    m_has_univ_mv(src.m_has_univ_mv),
    m_has_fvar(src.m_has_fvar),
    m_has_param_univ(src.m_has_param_univ),
    m_hash(src.m_hash),
    m_rc(0) {
    unsigned flgs = src.m_flags;
    m_flags = flgs;
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

bool is_metavar_app(expr const & e) {
    return is_metavar(get_app_fn(e));
}

// Expr variables
expr_bvar::expr_bvar(unsigned idx):
    expr_cell(expr_kind::BVar, idx, false, false, false, false),
    m_vidx(idx) {
    if (idx == std::numeric_limits<unsigned>::max())
        throw exception("invalid bound variable index, de Bruijn index is too big");
}
void expr_bvar::dealloc() {
    delete this;
}

// Expr constants
expr_const::expr_const(name const & n, levels const & ls):
    expr_cell(expr_kind::Constant, ::lean::hash(n.hash(), hash_levels(ls)), false,
              has_meta(ls), false, has_param(ls)),
    m_name(n),
    m_levels(ls) {
}
void expr_const::dealloc() {
    delete this;
}

// Expr metavariables and local variables
expr_mlocal::expr_mlocal(bool is_meta, name const & n, name const & pp_n, expr const & t):
    expr_composite(is_meta ? expr_kind::MVar : expr_kind::FVar, n.hash(), is_meta || t.has_expr_metavar(), t.has_univ_metavar(),
                   !is_meta || t.has_fvar(), t.has_param_univ(),
                   1, get_loose_bvar_range(t)),
    m_name(n),
    m_pp_name(pp_n),
    m_type(t) {}

void expr_mlocal::dealloc(buffer<expr_cell*> & todelete) {
    dec_ref(m_type, todelete);
    delete this;
}

expr_mlocal::expr_mlocal(expr_mlocal const & src, expr const & new_type):
    expr_composite(src), m_name(src.m_name), m_pp_name(src.m_pp_name), m_type(new_type) {}

expr_fvar::expr_fvar(name const & n, name const & pp_n, expr const & t, binder_info bi):
    expr_mlocal(false, n, pp_n, t), m_bi(bi) {}

expr_fvar::expr_fvar(expr_fvar const & src, expr const & new_type):
    expr_mlocal(src, new_type), m_bi(src.m_bi) {}

void expr_fvar::dealloc(buffer<expr_cell*> & todelete) {
    dec_ref(m_type, todelete);
    delete this;
}

expr_composite::expr_composite(expr_composite const & src):
    expr_cell(src),
    m_weight(src.m_weight),
    m_depth(src.m_depth),
    m_loose_bvar_range(src.m_loose_bvar_range) {
}

// Composite expressions
expr_composite::expr_composite(expr_kind k, unsigned h, bool has_expr_mv, bool has_univ_mv,
                               bool has_fvar, bool has_param_univ, unsigned w, unsigned bv_range):
    expr_cell(k, h, has_expr_mv, has_univ_mv, has_fvar, has_param_univ),
    m_weight(w),
    m_depth(0),
    m_loose_bvar_range(bv_range) {}

// Expr applications
expr_app::expr_app(expr const & fn, expr const & arg):
    expr_composite(expr_kind::App, ::lean::hash(fn.hash(), arg.hash()),
                   fn.has_expr_metavar() || arg.has_expr_metavar(),
                   fn.has_univ_metavar() || arg.has_univ_metavar(),
                   fn.has_fvar()         || arg.has_fvar(),
                   fn.has_param_univ()   || arg.has_param_univ(),
                   inc_weight(add_weight(get_weight(fn), get_weight(arg))),
                   std::max(get_loose_bvar_range(fn), get_loose_bvar_range(arg))),
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
    delete this;
}

static unsigned dec(unsigned k) { return k == 0 ? 0 : k - 1; }

// Expr binders (Lambda, Pi)
expr_binding::expr_binding(expr_kind k, name const & n, expr const & t, expr const & b, binder_info i):
    expr_composite(k, ::lean::hash(t.hash(), b.hash()),
                   t.has_expr_metavar()   || b.has_expr_metavar(),
                   t.has_univ_metavar()   || b.has_univ_metavar(),
                   t.has_fvar()           || b.has_fvar(),
                   t.has_param_univ()     || b.has_param_univ(),
                   inc_weight(add_weight(get_weight(t), get_weight(b))),
                   std::max(get_loose_bvar_range(t), dec(get_loose_bvar_range(b)))),
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
    delete this;
}

// Expr Sort
expr_sort::expr_sort(level const & l):
    expr_cell(expr_kind::Sort, ::lean::hash(l), false, has_meta(l), false, has_param(l)),
    m_level(l) {
}
expr_sort::~expr_sort() {}
void expr_sort::dealloc() {
    delete this;
}

// Expr literals

expr_lit::expr_lit(literal const & lit):
    expr_cell(expr_kind::Lit, false, false, false, false, false),
    m_lit(lit) {
}
expr_lit::~expr_lit() {}
void expr_lit::dealloc() {
    delete this;
}

expr lit_type(expr_ptr e) {
    switch (lit_value(e).kind()) {
    case literal_kind::String: return *g_string_type;
    case literal_kind::Nat:    return *g_nat_type;
    }
    lean_unreachable();
}

// Expr metadata
expr_mdata::expr_mdata(kvmap const & data, expr const & e):
    expr_composite(expr_kind::MData, e.hash(),
                   e.has_expr_metavar(),
                   e.has_univ_metavar(),
                   e.has_fvar(),
                   e.has_param_univ(),
                   inc_weight(get_weight(e)),
                   get_loose_bvar_range(e)),
    m_data(data), m_expr(e) {
    m_depth = get_depth(e) + 1;
    m_hash  = ::lean::hash(m_hash, m_weight);
    m_hash  = ::lean::hash(m_hash, m_depth);
}

void expr_mdata::dealloc(buffer<expr_cell*> & todelete) {
    dec_ref(m_expr,  todelete);
    delete this;
}

// Expr projections
expr_proj::expr_proj(nat const & idx, expr const & e):
    expr_composite(expr_kind::Proj, e.hash(),
                   e.has_expr_metavar(),
                   e.has_univ_metavar(),
                   e.has_fvar(),
                   e.has_param_univ(),
                   inc_weight(get_weight(e)),
                   get_loose_bvar_range(e)),
    m_idx(idx), m_expr(e) {
    m_depth = get_depth(e) + 1;
    m_hash  = ::lean::hash(m_hash, m_weight);
    m_hash  = ::lean::hash(m_hash, m_depth);
}

void expr_proj::dealloc(buffer<expr_cell*> & todelete) {
    dec_ref(m_expr,  todelete);
    delete this;
}

// Let expressions
expr_let::expr_let(name const & n, expr const & t, expr const & v, expr const & b):
    expr_composite(expr_kind::Let,
                   ::lean::hash(::lean::hash(t.hash(), v.hash()), b.hash()),
                   t.has_expr_metavar()   || v.has_expr_metavar() || b.has_expr_metavar(),
                   t.has_univ_metavar()   || v.has_univ_metavar() || b.has_univ_metavar(),
                   t.has_fvar()           || v.has_fvar() || b.has_fvar(),
                   t.has_param_univ()     || v.has_param_univ() || b.has_param_univ(),
                   inc_weight(add_weight(add_weight(get_weight(t), get_weight(v)), get_weight(b))),
                   std::max(std::max(get_loose_bvar_range(t), get_loose_bvar_range(v)), dec(get_loose_bvar_range(b)))),
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
    delete this;
}

// =======================================
// Constructors

expr mk_bvar(unsigned idx) {
    return expr(new expr_bvar(idx));
}
expr mk_fvar(name const & n) {
    return expr(new expr_fvar(n, n, expr(), mk_binder_info()));
}
expr mk_constant(name const & n, levels const & ls) {
    return expr(new expr_const(n, ls));
}
expr mk_metavar(name const & n, name const & pp_n, expr const & t) {
    return expr(new expr_mlocal(true, n, pp_n, t));
}
expr mk_metavar(name const & n, expr const & t) {
    return mk_metavar(n, n, t);
}
expr mk_mdata(kvmap const & d, expr const & e) {
    return expr(new expr_mdata(d, e));
}
expr mk_proj(nat const & idx, expr const & e) {
    return expr(new expr_proj(idx, e));
}
expr mk_local(name const & n, name const & pp_n, expr const & t, binder_info bi) {
    return expr(new expr_fvar(n, pp_n, t, bi));
}
expr mk_app(expr const & f, expr const & a) {
    return expr(new expr_app(f, a));
}
expr mk_binding(expr_kind k, name const & n, expr const & t, expr const & e, binder_info i) {
    return expr(new expr_binding(k, n, t, e, i));
}
expr mk_let(name const & n, expr const & t, expr const & v, expr const & b) {
    return expr(new expr_let(n, t, v, b));
}
expr mk_sort(level const & l) {
    return expr(new expr_sort(l));
}
expr mk_lit(literal const & l) {
    return expr(new expr_lit(l));
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
            case expr_kind::Lit:        static_cast<expr_lit*>(it)->dealloc(); break;
            case expr_kind::MData:      static_cast<expr_mdata*>(it)->dealloc(todo); break;
            case expr_kind::Proj:       static_cast<expr_proj*>(it)->dealloc(todo); break;
            case expr_kind::BVar:       static_cast<expr_bvar*>(it)->dealloc(); break;
            case expr_kind::MVar:       static_cast<expr_mlocal*>(it)->dealloc(todo); break;
            case expr_kind::FVar:       static_cast<expr_fvar*>(it)->dealloc(todo); break;
            case expr_kind::Constant:   static_cast<expr_const*>(it)->dealloc(); break;
            case expr_kind::Sort:       static_cast<expr_sort*>(it)->dealloc(); break;
            case expr_kind::App:        static_cast<expr_app*>(it)->dealloc(todo); break;
            case expr_kind::Lambda:
            case expr_kind::Pi:         static_cast<expr_binding*>(it)->dealloc(todo); break;
            case expr_kind::Let:        static_cast<expr_let*>(it)->dealloc(todo); break;

            case expr_kind::Quote:      static_cast<expr_quote*>(it)->dealloc(todo); break;
           }
        }
    } catch (std::bad_alloc&) {
        // We need this catch, because push_back may fail when expanding the buffer.
        // In this case, we avoid the crash, and "accept" the memory leak.
    }
}

// Auxiliary constructors
expr mk_app(expr const & f, unsigned num_args, expr const * args) {
    expr r = f;
    for (unsigned i = 0; i < num_args; i++)
        r = mk_app(r, args[i]);
    return r;
}

expr mk_app(unsigned num_args, expr const * args) {
    lean_assert(num_args >= 2);
    return mk_app(mk_app(args[0], args[1]), num_args - 2, args+2);
}

expr mk_app(expr const & f, list<expr> const & args) {
    buffer<expr> _args;
    to_buffer(args, _args);
    return mk_app(f, _args);
}

expr mk_rev_app(expr const & f, unsigned num_args, expr const * args) {
    expr r = f;
    unsigned i = num_args;
    while (i > 0) {
        --i;
        r = mk_app(r, args[i]);
    }
    return r;
}

expr mk_rev_app(unsigned num_args, expr const * args) {
    lean_assert(num_args >= 2);
    return mk_rev_app(mk_app(args[num_args-1], args[num_args-2]), num_args-2, args);
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
expr mk_arrow(expr const & t, expr const & e) {
    return mk_pi(get_default_var_name(), t, e, mk_binder_info());
}

static expr * g_Prop  = nullptr;
static expr * g_Type1 = nullptr;
expr mk_Prop() { return *g_Prop; }
expr mk_Type() { return *g_Type1; }

unsigned get_weight(expr const & e) {
    switch (e.kind()) {
    case expr_kind::BVar:  case expr_kind::Constant: case expr_kind::Sort:
    case expr_kind::MVar:  case expr_kind::FVar:     case expr_kind::Lit:
        return 1;
    case expr_kind::Lambda: case expr_kind::Pi:
    case expr_kind::App:    case expr_kind::Let:
    case expr_kind::MData:  case expr_kind::Proj:
        return static_cast<expr_composite*>(e.raw())->m_weight;

    case expr_kind::Quote:
        return 1;
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

unsigned get_depth(expr const & e) {
    switch (e.kind()) {
    case expr_kind::BVar: case expr_kind::Constant: case expr_kind::Sort:
    case expr_kind::MVar: case expr_kind::FVar:     case expr_kind::Lit:
        return 1;
    case expr_kind::Lambda: case expr_kind::Pi:
    case expr_kind::App:    case expr_kind::Let:
    case expr_kind::MData:  case expr_kind::Proj:
        return static_cast<expr_composite*>(e.raw())->m_depth;


    case expr_kind::Quote:
        return 1;
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

expr update_mdata(expr const & e, expr const & t) {
    if (!is_eqp(mdata_expr(e), t))
        return mk_mdata(mdata_data(e), t);
    else
        return e;
}

expr update_proj(expr const & e, expr const & t) {
    if (!is_eqp(proj_expr(e), t))
        return mk_proj(proj_idx(e), t);
    else
        return e;
}

expr update_app(expr const & e, expr const & new_fn, expr const & new_arg) {
    if (!is_eqp(app_fn(e), new_fn) || !is_eqp(app_arg(e), new_arg))
        return mk_app(new_fn, new_arg);
    else
        return e;
}

expr update_binding(expr const & e, expr const & new_domain, expr const & new_body) {
    if (!is_eqp(binding_domain(e), new_domain) || !is_eqp(binding_body(e), new_body))
        return mk_binding(e.kind(), binding_name(e), new_domain, new_body, binding_info(e));
    else
        return e;
}

expr update_binding(expr const & e, expr const & new_domain, expr const & new_body, binder_info bi) {
    if (!is_eqp(binding_domain(e), new_domain) || !is_eqp(binding_body(e), new_body) || bi != binding_info(e))
        return mk_binding(e.kind(), binding_name(e), new_domain, new_body, bi);
    else
        return e;
}

expr update_mlocal(expr const & e, expr const & new_type) {
    if (is_eqp(mlocal_type(e), new_type))
        return e;
    else if (is_metavar(e))
        return mk_metavar(mlocal_name(e), mlocal_pp_name(e), new_type);
    else
        return mk_local(mlocal_name(e), mlocal_pp_name(e), new_type, local_info(e));
}

expr update_local(expr const & e, expr const & new_type, binder_info bi) {
    if (is_eqp(mlocal_type(e), new_type) && local_info(e) == bi)
        return e;
    else
        return mk_local(mlocal_name(e), mlocal_pp_name(e), new_type, bi);
}

expr update_local(expr const & e, binder_info bi) {
    return update_local(e, mlocal_type(e), bi);
}

expr update_sort(expr const & e, level const & new_level) {
    if (!is_eqp(sort_level(e), new_level))
        return mk_sort(new_level);
    else
        return e;
}

expr update_constant(expr const & e, levels const & new_levels) {
    if (!is_eqp(const_levels(e), new_levels))
        return mk_constant(const_name(e), new_levels);
    else
        return e;
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
    case expr_kind::BVar:     case expr_kind::Lit:
        return true;
    case expr_kind::App:      case expr_kind::MVar:
    case expr_kind::FVar:     case expr_kind::Lambda:
    case expr_kind::Pi:       case expr_kind::Let:
    case expr_kind::MData:    case expr_kind::Proj:
        return false;


    case expr_kind::Quote:
        return true;
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

bool is_arrow(expr const & t) {
    optional<bool> r = t.raw()->is_arrow();
    if (r) {
        return *r;
    } else {
        bool res = is_pi(t) && !has_loose_bvar(binding_body(t), 0);
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
            if (is_metavar_app(e)) { r = e; return false; }
            if (is_local(e)) return false; // do not visit type
            return true;
        });
    return r;
}

static bool has_loose_bvars_in_domain(expr const & b, unsigned vidx, bool strict) {
    if (is_pi(b)) {
        return
            (has_loose_bvar(binding_domain(b), vidx) && is_explicit(binding_info(b))) ||
            has_loose_bvars_in_domain(binding_body(b), vidx+1, strict);
    } else if (!strict) {
        return has_loose_bvar(b, vidx);
    } else {
        return false;
    }
}

bool has_loose_bvar(expr const & e, unsigned i) {
    bool found = false;
    for_each(e, [&](expr const & e, unsigned offset) {
            if (found)
                return false; // already found
            unsigned n_i = i + offset;
            if (n_i < i)
                return false; // overflow, vidx can't be >= max unsigned
            if (n_i >= get_loose_bvar_range(e))
                return false; // expression e does not contain bound variables with idx >= n_i
            if (is_var(e)) {
                unsigned vidx = bvar_idx(e);
                if (vidx == n_i)
                    found = true;
            }
            return true; // continue search
        });
    return found;
}

expr lower_loose_bvars(expr const & e, unsigned s, unsigned d) {
    if (d == 0 || s >= get_loose_bvar_range(e))
        return e;
    lean_assert(s >= d);
    return replace(e, [=](expr const & e, unsigned offset) -> optional<expr> {
            unsigned s1 = s + offset;
            if (s1 < s)
                return some_expr(e); // overflow, vidx can't be >= max unsigned
            if (s1 >= get_loose_bvar_range(e))
                return some_expr(e); // expression e does not contain bound variables with idx >= s1
            if (is_var(e) && bvar_idx(e) >= s1) {
                lean_assert(bvar_idx(e) >= offset + d);
                return some_expr(mk_bvar(bvar_idx(e) - d));
            } else {
                return none_expr();
            }
        });
}
expr lower_loose_bvars(expr const & e, unsigned d) {
    return lower_loose_bvars(e, d, d);
}

expr lift_loose_bvars(expr const & e, unsigned s, unsigned d) {
    if (d == 0 || s >= get_loose_bvar_range(e))
        return e;
    return replace(e, [=](expr const & e, unsigned offset) -> optional<expr> {
            unsigned s1 = s + offset;
            if (s1 < s)
                return some_expr(e); // overflow, vidx can't be >= max unsigned
            if (s1 >= get_loose_bvar_range(e))
                return some_expr(e); // expression e does not contain bound variables with idx >= s1
            if (is_var(e) && bvar_idx(e) >= s + offset) {
                unsigned new_idx = bvar_idx(e) + d;
                if (new_idx < bvar_idx(e))
                    throw exception("invalid lift_loose_bvars operation, index overflow");
                return some_expr(mk_bvar(new_idx));
            } else {
                return none_expr();
            }
        });
}

expr lift_loose_bvars(expr const & e, unsigned d) {
    return lift_loose_bvars(e, 0, d);
}

expr infer_implicit(expr const & t, unsigned num_params, bool strict) {
    if (num_params == 0) {
        return t;
    } else if (is_pi(t)) {
        expr new_body = infer_implicit(binding_body(t), num_params-1, strict);
        if (!is_explicit(binding_info(t))) {
            // argument is already marked as implicit
            return update_binding(t, binding_domain(t), new_body);
        } else if (has_loose_bvars_in_domain(new_body, 0, strict)) {
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

std::ostream & operator<<(std::ostream & out, expr_kind const & k) {
    switch (k) {
    case expr_kind::MData:    out << "MData"; break;
    case expr_kind::Proj:     out << "Proj"; break;
    case expr_kind::Lit:      out << "Lit"; break;
    case expr_kind::BVar:     out << "BVar"; break;
    case expr_kind::FVar:     out << "FVar"; break;
    case expr_kind::MVar:     out << "MVar"; break;
    case expr_kind::Sort:     out << "Sort"; break;
    case expr_kind::Constant: out << "Constant"; break;
    case expr_kind::App:      out << "App"; break;
    case expr_kind::Lambda:   out << "Lambda"; break;
    case expr_kind::Pi:       out << "Pi"; break;
    case expr_kind::Let:      out << "Let"; break;


    case expr_kind::Quote:    out << "Quote"; break;
    }
    return out;
}

void initialize_expr() {
    g_dummy        = new expr(mk_constant("__expr_for_default_constructor__"));
    g_default_name = new name("a");
    g_Type1        = new expr(mk_sort(mk_level_one()));
    g_Prop         = new expr(mk_sort(mk_level_zero()));
    /* TODO(Leo): add support for builtin constants in the kernel.
       Something similar to what we have in the library directory. */
    g_nat_type     = new expr(mk_constant("nat"));
    g_string_type  = new expr(mk_constant("string"));
}

void finalize_expr() {
    delete g_Prop;
    delete g_Type1;
    delete g_dummy;
    delete g_default_name;
    delete g_nat_type;
    delete g_string_type;
}

/* ================ LEGACY CODE ================ */

expr_quote::expr_quote(bool r, expr const & v):
    expr_cell(expr_kind::Quote, v.hash(), false, false, false, false),
    m_reflected(r),
    m_value(v) {
}

void expr_quote::dealloc(buffer<expr_cell*> & todelete) {
    dec_ref(m_value, todelete);
    delete this;
}

expr mk_quote(bool reflected, expr const & val) {
    return expr(new expr_quote(reflected, val));
}
}
