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
#include "runtime/hash.h"
#include "util/list_fn.h"
#include "util/buffer.h"
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

literal::literal(nat const & v):
    object_ref(mk_cnstr(static_cast<unsigned>(literal_kind::Nat), v)) {
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

static inline unsigned literal_hash(b_obj_arg l) {
    switch (literal::kind(l)) {
    case literal_kind::Nat:    return nat::hash(cnstr_get(l, 0));
    case literal_kind::String: return hash_str(string_size(cnstr_get(l, 0)) - 1, string_cstr(cnstr_get(l, 0)), 17);
    }
    lean_unreachable();
}

static unsigned levels_hash(object * ls) {
    unsigned r = 23;
    while (!is_scalar(ls)) {
        r = hash(level::hash(cnstr_get(ls, 0)), r);
        ls = cnstr_get(ls, 1);
    }
    return r;
}

// =======================================
// Safe arithmetic

static unsigned safe_inc(unsigned w) {
    if (w < std::numeric_limits<unsigned>::max())
        return w+1;
    else
        return w;
}

static unsigned safe_dec(unsigned k) {
    return k == 0 ? 0 : k - 1;
}


// =======================================
// Scalar data offset calculation and setters/getters

inline constexpr unsigned num_obj_fields(expr_kind k) {
    return
        k == expr_kind::App     ?  2 :
        k == expr_kind::Const   ?  2 :
        k == expr_kind::FVar    ?  1 : // TODO(Leo): it should be 1 after we remove support for legacy code
        k == expr_kind::Lambda  ?  3 :
        k == expr_kind::Pi      ?  3 :
        k == expr_kind::BVar    ?  1 :
        k == expr_kind::Let     ?  4 :
        k == expr_kind::MVar    ?  1 :
        k == expr_kind::Sort    ?  1 :
        k == expr_kind::Lit     ?  1 :
        k == expr_kind::MData   ?  2 :
        k == expr_kind::Proj    ?  3 :
        k == expr_kind::Local   ?  3 : // TODO(Leo): delete we remove support for legacy code
        /* k == expr_kind::Quote */ 1;
}

/* Expression scalar data offset. */
inline constexpr unsigned scalar_offset(expr_kind k) { return num_obj_fields(k) * sizeof(object*); }

inline constexpr unsigned binder_info_offset(expr_kind k) {
    // Only for: k == expr_kind::Pi || k == expr_kind::Lambda || k == expr_kind::Local
    return scalar_offset(k);
}

/* Legacy support */
inline constexpr unsigned reflected_offset(expr_kind k) {
    // Only for: k == expr_kind::Quote
    return scalar_offset(k);
}

inline constexpr unsigned hash_offset(expr_kind k) {
    return
        k == expr_kind::Local  ? scalar_offset(k) + sizeof(unsigned) : // for binder_info, TODO(Leo): delete after we remove support for legacy code
        k == expr_kind::Lambda ? scalar_offset(k) + sizeof(unsigned) : // for binder_info
        k == expr_kind::Pi     ? scalar_offset(k) + sizeof(unsigned) : // for binder_info
        scalar_offset(k);
}

inline constexpr size_t flags_offset(expr_kind k) { return hash_offset(k) + sizeof(unsigned); }
inline constexpr size_t loose_bvar_range_offset(expr_kind k) { return flags_offset(k) + sizeof(unsigned); }
/* Size for scalar value area for non recursive expression. */
inline constexpr size_t expr_scalar_size(expr_kind k) { return flags_offset(k) + sizeof(unsigned); }
/* Size for scalar value area for recursive expression. */
inline constexpr size_t rec_expr_scalar_size(expr_kind k) { return loose_bvar_range_offset(k) + sizeof(unsigned); }

static inline unsigned expr_hash(object * e) { return cnstr_get_scalar<unsigned>(e, hash_offset(expr::kind(e))); }
unsigned hash(expr const & e) { return expr_hash(e.raw()); }
extern "C" size_t lean_expr_hash(object * e) { return expr_hash(e); }

/* Set expr cached hash code and flags. All expressions contain them.
   We provide the kind `k` to allow the compiler to compute offsets at compilation time. */
template<expr_kind k> void set_scalar(object * e, unsigned hash, bool has_expr_mvar, bool has_univ_mvar,
                                      bool has_fvar, bool has_univ_param) {
    lean_assert(expr::kind(e) == k);
    unsigned char d =
        (has_expr_mvar ? 1 : 0) +
        (has_univ_mvar ? 2 : 0) +
        (has_fvar ? 4 : 0) +
        (has_univ_param ? 8 : 0);
    cnstr_set_scalar<unsigned>(e, hash_offset(k), hash);
    cnstr_set_scalar<unsigned char>(e, flags_offset(k), d);
}

/* Set expr cached loose bvar range. We only store this information in recursive expr constructors.
   We provide the kind `k` to allow the compiler to compute offsets at compilation time. */
template<expr_kind k> void set_rec_scalar(object * e, unsigned loose_bvar_range) {
    lean_assert(expr::kind(e) == k);
    cnstr_set_scalar<unsigned>(e, loose_bvar_range_offset(k), loose_bvar_range);
}

template<expr_kind k> void set_binder_info(object * e, binder_info bi) {
    lean_assert(expr::kind(e) == k);
    cnstr_set_scalar<unsigned char>(e, binder_info_offset(k), static_cast<unsigned char>(bi));
}

static inline unsigned char get_flags(object * e) { return cnstr_get_scalar<unsigned char>(e, flags_offset(expr::kind(e))); }
static inline bool has_expr_mvar(object * e) { return (get_flags(e) & 1) != 0; }
static inline bool has_univ_mvar(object * e) { return (get_flags(e) & 2) != 0; }
static inline bool has_fvar(object * e) { return (get_flags(e) & 4) != 0; }
static inline bool has_univ_param(object * e) { return (get_flags(e) & 8) != 0; }
bool has_expr_mvar(expr const & e) { return has_expr_mvar(e.raw()); }
bool has_univ_mvar(expr const & e) { return has_univ_mvar(e.raw()); }
bool has_fvar(expr const & e) { return has_fvar(e.raw()); }
bool has_univ_param(expr const & e) { return has_univ_param(e.raw()); }

template<expr_kind k> unsigned get_loose_bvar_range_core(object * e) { return cnstr_get_scalar<unsigned>(e, loose_bvar_range_offset(k)); }

unsigned expr_get_loose_bvar_range(object * e) {
    switch (expr::kind(e)) {
    case expr_kind::Const: case expr_kind::Sort:
    case expr_kind::Lit:   case expr_kind::MVar:
    case expr_kind::FVar:
        return 0;
    case expr_kind::BVar:    {
        object * idx = cnstr_get(e, 0);
        if (is_scalar(idx))
            return safe_inc(unbox(idx));
        else
            return std::numeric_limits<unsigned>::max();
    }
    case expr_kind::Local:   return get_loose_bvar_range_core<expr_kind::Local>(e);
    case expr_kind::Lambda:  return get_loose_bvar_range_core<expr_kind::Lambda>(e);
    case expr_kind::Pi:      return get_loose_bvar_range_core<expr_kind::Pi>(e);
    case expr_kind::App:     return get_loose_bvar_range_core<expr_kind::App>(e);
    case expr_kind::Let:     return get_loose_bvar_range_core<expr_kind::Let>(e);
    case expr_kind::MData:   return get_loose_bvar_range_core<expr_kind::MData>(e);
    case expr_kind::Proj:    return get_loose_bvar_range_core<expr_kind::Proj>(e);
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

extern "C" object * lean_expr_get_loose_bvar_range(b_obj_arg e) { return mk_nat_obj(expr_get_loose_bvar_range(e)); }

bool is_atomic(expr const & e) {
    switch (e.kind()) {
    case expr_kind::Const: case expr_kind::Sort:
    case expr_kind::BVar:  case expr_kind::Lit:
    case expr_kind::MVar:  case expr_kind::FVar:
        return true;
    case expr_kind::App:
    case expr_kind::Lambda:
    case expr_kind::Pi:    case expr_kind::Let:
    case expr_kind::MData: case expr_kind::Proj:
    case expr_kind::Local:
        return false;
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

binder_info binding_info(expr const & e) {
    lean_assert(is_lambda(e) || is_pi(e));
    // Remark: lambda and Pi have the same memory layout
    return static_cast<binder_info>(cnstr_get_scalar<unsigned char>(e.raw(), binder_info_offset(expr_kind::Lambda)));
}

/* Legacy */
binder_info local_info(expr const & e) {
    lean_assert(is_local(e));
    return static_cast<binder_info>(cnstr_get_scalar<unsigned char>(e.raw(), binder_info_offset(expr_kind::Local)));
}

static expr * g_nat_type    = nullptr;
static expr * g_string_type = nullptr;

expr const & lit_type(expr const & e) {
    switch (lit_value(e).kind()) {
    case literal_kind::String: return *g_string_type;
    case literal_kind::Nat:    return *g_nat_type;
    }
    lean_unreachable();
}

// =======================================
// Constructors

static expr * g_dummy = nullptr;

static expr const & get_dummy() {
    if (!g_dummy) {
        g_dummy = new expr(mk_constant("__expr_for_default_constructor__"));
    }
    return *g_dummy;
}

expr::expr():expr(get_dummy()) {}

extern "C" object * lean_expr_mk_lit(obj_arg l) {
    object * r = alloc_cnstr(static_cast<unsigned>(expr_kind::Lit), 1, expr_scalar_size(expr_kind::Lit));
    cnstr_set(r, 0, l);
    set_scalar<expr_kind::Lit>(r, literal_hash(l), false, false, false, false);
    return r;
}

expr mk_lit(literal const & l) {
    inc(l.raw());
    return expr(lean_expr_mk_lit(l.raw()));
}

extern "C" object * lean_expr_mk_mdata(obj_arg m, obj_arg e) {
    object * r = alloc_cnstr(static_cast<unsigned>(expr_kind::MData), 2, expr_scalar_size(expr_kind::MData));
    cnstr_set(r, 0, m);
    cnstr_set(r, 1, e);
    unsigned h = expr_hash(e); // Include hash(m)
    set_scalar<expr_kind::MData>(r, h, has_expr_mvar(e), has_univ_mvar(e), has_fvar(e), has_univ_param(e));
    set_rec_scalar<expr_kind::MData>(r, expr_get_loose_bvar_range(e));
    return r;
}

expr mk_mdata(kvmap const & m, expr const & e) {
    inc(m.raw()); inc(e.raw());
    return expr(lean_expr_mk_mdata(m.raw(), e.raw()));
}

extern "C" object * lean_expr_mk_proj(obj_arg s, obj_arg idx, obj_arg e) {
    object * r = alloc_cnstr(static_cast<unsigned>(expr_kind::Proj), 3, rec_expr_scalar_size(expr_kind::Proj));
    cnstr_set(r, 0, s);
    cnstr_set(r, 1, idx);
    cnstr_set(r, 2, e);
    unsigned h    = hash(expr_hash(e), nat::hash(idx));
    set_scalar<expr_kind::Proj>(r, h, has_expr_mvar(e), has_univ_mvar(e), has_fvar(e), has_univ_param(e));
    set_rec_scalar<expr_kind::Proj>(r, expr_get_loose_bvar_range(e));
    return r;
}

expr mk_proj(name const & s, nat const & idx, expr const & e) {
    inc(s.raw()); inc(idx.raw()); inc(e.raw());
    return expr(lean_expr_mk_proj(s.raw(), idx.raw(), e.raw()));
}

extern "C" object * lean_expr_mk_bvar(obj_arg idx) {
    object * r = alloc_cnstr(static_cast<unsigned>(expr_kind::BVar), 1, expr_scalar_size(expr_kind::BVar));
    cnstr_set(r, 0, idx);
    set_scalar<expr_kind::BVar>(r, nat::hash(idx), false, false, false, false);
    return r;
}

expr mk_bvar(nat const & idx) {
    inc(idx.raw());
    return expr(lean_expr_mk_bvar(idx.raw()));
}

extern "C" object * lean_expr_mk_fvar(obj_arg n) {
    object * r = alloc_cnstr(static_cast<unsigned>(expr_kind::FVar), 1, rec_expr_scalar_size(expr_kind::FVar));
    cnstr_set(r, 0, n);
    set_scalar<expr_kind::FVar>(r, name::hash(n), false, false, true, false);
    return r;
}

expr mk_fvar(name const & n) {
    return expr(lean_expr_mk_fvar(n.to_obj_arg()));
}

extern "C" object * lean_expr_mk_const(obj_arg n, obj_arg ls) {
    object * r = alloc_cnstr(static_cast<unsigned>(expr_kind::Const), 2, expr_scalar_size(expr_kind::Const));
    cnstr_set(r, 0, n);
    cnstr_set(r, 1, ls);
    set_scalar<expr_kind::Const>(r, hash(name::hash(n), levels_hash(ls)), false, levels_has_mvar(ls), false, levels_has_param(ls));
    return r;
}

expr mk_const(name const & n, levels const & ls) {
    inc(n.raw()); inc(ls.raw());
    return expr(lean_expr_mk_const(n.raw(), ls.raw()));
}

extern "C" object * lean_expr_mk_app(obj_arg f, obj_arg a) {
    object * r = alloc_cnstr(static_cast<unsigned>(expr_kind::App), 2, rec_expr_scalar_size(expr_kind::App));
    cnstr_set(r, 0, f);
    cnstr_set(r, 1, a);
    unsigned h    = hash(expr_hash(f), expr_hash(a));
    set_scalar<expr_kind::App>(r, h,
                               has_expr_mvar(f) || has_expr_mvar(a),
                               has_univ_mvar(f) || has_univ_mvar(a),
                               has_fvar(f) || has_fvar(a),
                               has_univ_param(f) || has_univ_param(a));
    set_rec_scalar<expr_kind::App>(r, std::max(expr_get_loose_bvar_range(f), expr_get_loose_bvar_range(a)));
    return r;
}

expr mk_app(expr const & f, expr const & a) {
    inc(f.raw()); inc(a.raw());
    return expr(lean_expr_mk_app(f.raw(), a.raw()));
}

extern "C" object * lean_expr_mk_sort(obj_arg l) {
    object * r = alloc_cnstr(static_cast<unsigned>(expr_kind::Sort), 1, expr_scalar_size(expr_kind::Sort));
    cnstr_set(r, 0, l);
    set_scalar<expr_kind::Sort>(r, level::hash(l), false, lean_level_has_mvar(l), false, lean_level_has_param(l));
    return r;
}

expr mk_sort(level const & l) {
    inc(l.raw());
    return expr(lean_expr_mk_sort(l.raw()));
}

template<expr_kind k>
static object * mk_binding(obj_arg n, obj_arg t, obj_arg e, binder_info bi) {
    lean_assert(k == expr_kind::Pi || k == expr_kind::Lambda);
    object * r = alloc_cnstr(static_cast<unsigned>(k), 3, rec_expr_scalar_size(k));
    cnstr_set(r, 0, n);
    cnstr_set(r, 1, t);
    cnstr_set(r, 2, e);
    unsigned h    = hash(expr_hash(t), expr_hash(e));
    unsigned lbvr = std::max(expr_get_loose_bvar_range(t), safe_dec(expr_get_loose_bvar_range(e)));
    set_binder_info<k>(r, bi);
    set_scalar<k>(r, h,
                  has_expr_mvar(t)  || has_expr_mvar(e),
                  has_univ_mvar(t)  || has_univ_mvar(e),
                  has_fvar(t)       || has_fvar(e),
                  has_univ_param(t) || has_univ_param(e));
    set_rec_scalar<k>(r, lbvr);
    return r;
}

extern "C" object * lean_expr_mk_lambda(obj_arg n, uint8 bi, obj_arg t, obj_arg e) {
    return mk_binding<expr_kind::Lambda>(n, t, e, static_cast<binder_info>(bi));
}

expr mk_lambda(name const & n, expr const & t, expr const & e, binder_info bi) {
    inc(n.raw()); inc(t.raw()); inc(e.raw());
    return expr(mk_binding<expr_kind::Lambda>(n.raw(), t.raw(), e.raw(), bi));
}

extern "C" object * lean_expr_mk_forall(obj_arg n, uint8 bi, obj_arg t, obj_arg e) {
    return mk_binding<expr_kind::Pi>(n, t, e, static_cast<binder_info>(bi));
}

expr mk_pi(name const & n, expr const & t, expr const & e, binder_info bi) {
    inc(n.raw()); inc(t.raw()); inc(e.raw());
    return expr(mk_binding<expr_kind::Pi>(n.raw(), t.raw(), e.raw(), bi));
}

static name * g_default_name = nullptr;

expr mk_arrow(expr const & t, expr const & e) {
    return mk_pi(*g_default_name, t, e, mk_binder_info());
}

extern "C" object * lean_expr_mk_let(object * n, object * t, object * v, object * b) {
    object * r = alloc_cnstr(static_cast<unsigned>(expr_kind::Let), 4, rec_expr_scalar_size(expr_kind::Let));
    cnstr_set(r, 0, n);
    cnstr_set(r, 1, t);
    cnstr_set(r, 2, v);
    cnstr_set(r, 3, b);
    unsigned h    = hash(hash(expr_hash(t), expr_hash(v)), expr_hash(b));
    unsigned lbvr = std::max(expr_get_loose_bvar_range(t), std::max(expr_get_loose_bvar_range(v), safe_dec(expr_get_loose_bvar_range(b))));
    set_scalar<expr_kind::Let>(r, h,
                               has_expr_mvar(t)  || has_expr_mvar(v)  || has_expr_mvar(b),
                               has_univ_mvar(t)  || has_univ_mvar(v)  || has_univ_mvar(b),
                               has_fvar(t)       || has_fvar(v)       || has_fvar(b),
                               has_univ_param(t) || has_univ_param(v) || has_univ_param(b));
    set_rec_scalar<expr_kind::Let>(r, lbvr);
    return r;
}

expr mk_let(name const & n, expr const & t, expr const & v, expr const & b) {
    inc(n.raw()); inc(t.raw()); inc(v.raw()); inc(b.raw());
    return expr(lean_expr_mk_let(n.raw(), t.raw(), v.raw(), b.raw()));
}

extern "C" object * lean_expr_mk_mvar_core(object * n) {
    object * r = alloc_cnstr(static_cast<unsigned>(expr_kind::MVar), 1, rec_expr_scalar_size(expr_kind::MVar));
    cnstr_set(r, 0, n);
    set_scalar<expr_kind::MVar>(r, name::hash(n), true, false, false, false);
    set_rec_scalar<expr_kind::MVar>(r, 0);
    return r;
}

extern "C" object * lean_expr_mk_mvar(object * n) {
    return lean_expr_mk_mvar_core(n);
}

expr mk_mvar(name const & n) {
    inc(n.raw());
    return expr(lean_expr_mk_mvar_core(n.raw()));
}

static expr * g_Prop  = nullptr;
static expr * g_Type0 = nullptr;

expr mk_Prop() { return *g_Prop; }
expr mk_Type() { return *g_Type0; }

// Legacy
extern "C" obj_res lean_expr_local(obj_arg vm_name, obj_arg vm_pp_name, obj_arg vm_type, uint8 vm_binder_info) {
    return mk_local(name(vm_name), name(vm_pp_name), expr(vm_type), static_cast<binder_info>(vm_binder_info)).steal();
}

// =======================================
// Auxiliary constructors and accessors

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

bool is_arrow(expr const & t) {
    if (!is_pi(t)) return false;
    if (has_loose_bvars(t)) {
        return !has_loose_bvar(binding_body(t), 0);
    } else {
        lean_assert(has_loose_bvars(binding_body(t)) == has_loose_bvar(binding_body(t), 0));
        return !has_loose_bvars(binding_body(t));
    }
}

bool is_default_var_name(name const & n) {
    return n == *g_default_name;
}

/* Legacy */
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

// =======================================
// Update

expr update_mdata(expr const & e, expr const & t) {
    if (!is_eqp(mdata_expr(e), t))
        return mk_mdata(mdata_data(e), t);
    else
        return e;
}

expr update_proj(expr const & e, expr const & t) {
    if (!is_eqp(proj_expr(e), t))
        return mk_proj(proj_sname(e), proj_idx(e), t);
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

expr update_sort(expr const & e, level const & new_level) {
    if (!is_eqp(sort_level(e), new_level))
        return mk_sort(new_level);
    else
        return e;
}

expr update_const(expr const & e, levels const & new_levels) {
    if (!is_eqp(const_levels(e), new_levels))
        return mk_const(const_name(e), new_levels);
    else
        return e;
}

expr update_let(expr const & e, expr const & new_type, expr const & new_value, expr const & new_body) {
    if (!is_eqp(let_type(e), new_type) || !is_eqp(let_value(e), new_value) || !is_eqp(let_body(e), new_body))
        return mk_let(let_name(e), new_type, new_value, new_body);
    else
        return e;
}

/* Legacy */
static inline object * mk_local(obj_arg n, obj_arg pp_n, obj_arg t, binder_info bi) {
    object * r = alloc_cnstr(static_cast<unsigned>(expr_kind::Local), 3, rec_expr_scalar_size(expr_kind::Local));
    cnstr_set(r, 0, n);
    cnstr_set(r, 1, pp_n);
    cnstr_set(r, 2, t);
    set_binder_info<expr_kind::Local>(r, bi);
    set_scalar<expr_kind::Local>(r, name::hash(n), has_expr_mvar(t), has_univ_mvar(t), true, has_univ_param(t));
    set_rec_scalar<expr_kind::Local>(r, expr_get_loose_bvar_range(t));
    return r;
}

/* Legacy */
expr mk_local(name const & n, name const & pp_n, expr const & t, binder_info bi) {
    inc(n.raw()); inc(pp_n.raw()); inc(t.raw());
    return expr(mk_local(n.raw(), pp_n.raw(), t.raw(), bi));
}

/* Legacy */
expr update_local(expr const & e, expr const & new_type, binder_info bi) {
    if (is_eqp(local_type(e), new_type) && local_info(e) == bi)
        return e;
    else
        return mk_local(local_name(e), local_pp_name(e), new_type, bi);
}

/* Legacy */
expr update_local(expr const & e, binder_info bi) {
    return update_local(e, local_type(e), bi);
}

/* Legacy */
expr update_local(expr const & e, expr const & new_type) {
    if (is_eqp(local_type(e), new_type))
        return e;
    else
        return mk_local(local_name(e), local_pp_name(e), new_type, local_info(e));
}

extern "C" object * lean_expr_update_mdata(obj_arg e, obj_arg new_expr) {
    if (mdata_expr(TO_REF(expr, e)).raw() != new_expr) {
        lean_dec_ref(e);
        return lean_expr_mk_mdata(mdata_data(TO_REF(expr, e)).to_obj_arg(), new_expr);
    } else {
        lean_dec_ref(new_expr);
        return e;
    }
}

extern "C" object * lean_expr_update_const(obj_arg e, obj_arg new_levels) {
    if (const_levels(TO_REF(expr, e)).raw() != new_levels) {
        lean_dec_ref(e);
        return lean_expr_mk_const(const_name(TO_REF(expr, e)).to_obj_arg(), new_levels);
    } else {
        lean_dec(new_levels);
        return e;
    }
}

extern "C" object * lean_expr_update_sort(obj_arg e, obj_arg new_level) {
    if (sort_level(TO_REF(expr, e)).raw() != new_level) {
        lean_dec_ref(e);
        return lean_expr_mk_sort(new_level);
    } else {
        lean_dec(new_level);
        return e;
    }
}

extern "C" object * lean_expr_update_proj(obj_arg e, obj_arg new_expr) {
    if (proj_expr(TO_REF(expr, e)).raw() != new_expr) {
        lean_dec_ref(e);
        return lean_expr_mk_proj(proj_sname(TO_REF(expr, e)).to_obj_arg(), proj_idx(TO_REF(expr, e)).to_obj_arg(), new_expr);
    } else {
        lean_dec_ref(new_expr);
        return e;
    }
}

extern "C" object * lean_expr_update_app(obj_arg e, obj_arg new_fn, obj_arg new_arg) {
    if (app_fn(TO_REF(expr, e)).raw() != new_fn || app_arg(TO_REF(expr, e)).raw() != new_arg) {
        lean_dec_ref(e);
        return lean_expr_mk_app(new_fn, new_arg);
    } else {
        lean_dec_ref(new_fn); lean_dec_ref(new_arg);
        return e;
    }
}

extern "C" object * lean_expr_update_forall(obj_arg e, uint8 new_binfo, obj_arg new_domain, obj_arg new_body) {
    if (binding_domain(TO_REF(expr, e)).raw() != new_domain || binding_body(TO_REF(expr, e)).raw() != new_body ||
        binding_info(TO_REF(expr, e)) != static_cast<binder_info>(new_binfo)) {
        lean_dec_ref(e);
        return lean_expr_mk_forall(binding_name(TO_REF(expr, e)).to_obj_arg(),
                                   new_binfo, new_domain, new_body);
    } else {
        lean_dec_ref(new_domain); lean_dec_ref(new_body);
        return e;
    }
}

extern "C" object * lean_expr_update_lambda(obj_arg e, uint8 new_binfo, obj_arg new_domain, obj_arg new_body) {
    if (binding_domain(TO_REF(expr, e)).raw() != new_domain || binding_body(TO_REF(expr, e)).raw() != new_body ||
        binding_info(TO_REF(expr, e)) != static_cast<binder_info>(new_binfo)) {
        lean_dec_ref(e);
        return lean_expr_mk_lambda(binding_name(TO_REF(expr, e)).to_obj_arg(),
                                   new_binfo, new_domain, new_body);
    } else {
        lean_dec_ref(new_domain); lean_dec_ref(new_body);
        return e;
    }
}

extern "C" object * lean_expr_update_let(obj_arg e, obj_arg new_type, obj_arg new_val, obj_arg new_body) {
    if (let_type(TO_REF(expr, e)).raw() != new_type || let_value(TO_REF(expr, e)).raw() != new_val ||
        let_body(TO_REF(expr, e)).raw() != new_body) {
        lean_dec_ref(e);
        return lean_expr_mk_let(let_name(TO_REF(expr, e)).to_obj_arg(), new_type, new_val, new_body);
    } else {
        lean_dec_ref(new_type); lean_dec_ref(new_val); lean_dec_ref(new_body);
        return e;
    }
}


// =======================================
// Loose bound variable management

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
                nat const & vidx = bvar_idx(e);
                if (vidx == n_i)
                    found = true;
            }
            return true; // continue search
        });
    return found;
}

extern "C" uint8 lean_expr_has_loose_bvar(b_obj_arg e, b_obj_arg i) {
    if (!lean_is_scalar(i))
        return false;
    return has_loose_bvar(TO_REF(expr, e), lean_unbox(i));
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
            if (is_bvar(e) && bvar_idx(e) >= s1) {
                lean_assert(bvar_idx(e) >= offset + d);
                return some_expr(mk_bvar(bvar_idx(e) - nat(d)));
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
                return some_expr(mk_bvar(bvar_idx(e) + nat(d)));
            } else {
                return none_expr();
            }
        });
}

expr lift_loose_bvars(expr const & e, unsigned d) {
    return lift_loose_bvars(e, 0, d);
}

// =======================================
// Implicit argument inference

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

// =======================================
// Extra exports

extern "C" uint8 lean_expr_has_expr_mvar(b_obj_arg o) {
    return has_expr_mvar(TO_REF(expr, o));
}

extern "C" uint8 lean_expr_has_level_mvar(b_obj_arg o) {
    return has_univ_mvar(TO_REF(expr, o));
}

extern "C" uint8 lean_expr_has_fvar(b_obj_arg o) {
    return has_fvar(TO_REF(expr, o));
}

// =======================================
// Initialization & Finalization

void initialize_expr() {
    get_dummy();
    g_default_name = new name("a");
    g_Type0        = new expr(mk_sort(mk_level_one()));
    g_Prop         = new expr(mk_sort(mk_level_zero()));
    /* TODO(Leo): add support for builtin constants in the kernel.
       Something similar to what we have in the library directory. */
    g_nat_type     = new expr(mk_constant("Nat"));
    g_string_type  = new expr(mk_constant("String"));
}

void finalize_expr() {
    delete g_Prop;
    delete g_Type0;
    delete g_dummy;
    delete g_default_name;
    delete g_nat_type;
    delete g_string_type;
}
}
