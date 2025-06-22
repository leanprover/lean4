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
#include "runtime/buffer.h"
#include "util/list_fn.h"
#include "kernel/expr.h"
#include "kernel/expr_eq_fn.h"
#include "kernel/expr_sets.h"
#include "kernel/for_each_fn.h"
#include "kernel/replace_fn.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"

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
        return false;
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

extern "C" uint8 lean_expr_binder_info(object * e);
binder_info binding_info(expr const & e) { return static_cast<binder_info>(lean_expr_binder_info(e.to_obj_arg())); }

extern "C" object * lean_lit_type(obj_arg e);
expr lit_type(literal const & lit) { return expr(lean_lit_type(lit.to_obj_arg())); }

extern "C" uint64_t lean_expr_hash(obj_arg e);
unsigned hash_core(expr const & e) {
    return lean_expr_hash(e.to_obj_arg());
}

extern "C" uint8 lean_expr_has_fvar(obj_arg e);
bool has_fvar_core(expr const & e) {
    return lean_expr_has_fvar(e.to_obj_arg());
}

extern "C" uint8 lean_expr_has_expr_mvar(obj_arg e);
bool has_expr_mvar_core(expr const & e) {
    return lean_expr_has_expr_mvar(e.to_obj_arg());
}

extern "C" uint8 lean_expr_has_level_mvar(obj_arg e);
bool has_univ_mvar_core(expr const & e) { return lean_expr_has_level_mvar(e.to_obj_arg()); }

extern "C" uint8 lean_expr_has_level_param(obj_arg e);
bool has_univ_param(expr const & e) { return lean_expr_has_level_param(e.to_obj_arg()); }

extern "C" unsigned lean_expr_loose_bvar_range(object * e);
unsigned get_loose_bvar_range(expr const & e) { return lean_expr_loose_bvar_range(e.to_obj_arg()); }

extern "C" LEAN_EXPORT uint64_t lean_expr_mk_data(uint64_t hash, object * bvarRange, uint32_t approxDepth, uint8_t hasFVar, uint8_t hasExprMVar, uint8_t hasLevelMVar, uint8_t hasLevelParam) {
    if (approxDepth > 255) approxDepth = 255;
    if (!is_scalar(bvarRange)) lean_internal_panic("too many bound variables");
    size_t range = unbox(bvarRange);
    if (range > 1048575) lean_internal_panic("too many bound variables");
    uint32_t r = range;
    uint32_t h = hash;
    return ((uint64_t) h) + (((uint64_t) approxDepth) << 32) + (((uint64_t) hasFVar) << 40)
    + (((uint64_t) hasExprMVar) << 41) + (((uint64_t) hasLevelMVar) << 42) + (((uint64_t) hasLevelParam) << 43)
    + (((uint64_t) r) << 44);
}

inline uint16_t get_approx_depth(uint64_t data) { return (data >> 32) & 255; }
inline uint32_t get_bvar_range(uint64_t data) { return data >> 44; }

extern "C" LEAN_EXPORT uint64_t lean_expr_mk_app_data(uint64_t fData, uint64_t aData) {
  uint16_t depth = std::max(get_approx_depth(fData), get_approx_depth(aData)) + 1;
  if (depth > 255) depth = 255;
  uint32_t range = std::max(get_bvar_range(fData), get_bvar_range(aData));
  uint32_t h = hash(fData, aData);
  return ((fData | aData) & (((uint64_t) 15) << 40)) | ((uint64_t) h) | (((uint64_t) depth) << 32) | (((uint64_t) range) << 44);
}

// =======================================
// Constructors

static expr * g_dummy = nullptr;

static expr const & get_dummy() {
    if (!g_dummy) {
        g_dummy = new expr(mk_constant("__expr_for_default_constructor__"));
    mark_persistent(g_dummy->raw());
    }
    return *g_dummy;
}

expr::expr():expr(get_dummy()) {}

extern "C" object * lean_expr_mk_lit(obj_arg l);
expr mk_lit(literal const & l) { return expr(lean_expr_mk_lit(l.to_obj_arg())); }

extern "C" object * lean_expr_mk_mdata(obj_arg m, obj_arg e);
expr mk_mdata(kvmap const & m, expr const & e) { return expr(lean_expr_mk_mdata(m.to_obj_arg(), e.to_obj_arg())); }

extern "C" object * lean_expr_mk_proj(obj_arg s, obj_arg idx, obj_arg e);
expr mk_proj(name const & s, nat const & idx, expr const & e) { return expr(lean_expr_mk_proj(s.to_obj_arg(), idx.to_obj_arg(), e.to_obj_arg())); }

extern "C" object * lean_expr_mk_bvar(obj_arg idx);
expr mk_bvar(nat const & idx) { return expr(lean_expr_mk_bvar(idx.to_obj_arg())); }

extern "C" object * lean_expr_mk_fvar(obj_arg n);
expr mk_fvar(name const & n) { return expr(lean_expr_mk_fvar(n.to_obj_arg())); }

extern "C" object * lean_expr_mk_mvar(object * n);
expr mk_mvar(name const & n) { return expr(lean_expr_mk_mvar(n.to_obj_arg())); }

extern "C" object * lean_expr_mk_const(obj_arg n, obj_arg ls);
expr mk_const(name const & n, levels const & ls) { return expr(lean_expr_mk_const(n.to_obj_arg(), ls.to_obj_arg())); }

extern "C" object * lean_expr_mk_app(obj_arg f, obj_arg a);
expr mk_app(expr const & f, expr const & a) { return expr(lean_expr_mk_app(f.to_obj_arg(), a.to_obj_arg())); }

extern "C" object * lean_expr_mk_sort(obj_arg l);
expr mk_sort(level const & l) { return expr(lean_expr_mk_sort(l.to_obj_arg())); }

extern "C" object * lean_expr_mk_lambda(obj_arg n, obj_arg t, obj_arg e, uint8 bi);
expr mk_lambda(name const & n, expr const & t, expr const & e, binder_info bi) {
    return expr(lean_expr_mk_lambda(n.to_obj_arg(), t.to_obj_arg(), e.to_obj_arg(), static_cast<uint8>(bi)));
}

extern "C" object * lean_expr_mk_forall(obj_arg n, obj_arg t, obj_arg e, uint8 bi);
expr mk_pi(name const & n, expr const & t, expr const & e, binder_info bi) {
    return expr(lean_expr_mk_forall(n.to_obj_arg(), t.to_obj_arg(), e.to_obj_arg(), static_cast<uint8>(bi)));
}

static name * g_default_name = nullptr;
expr mk_arrow(expr const & t, expr const & e) {
    return mk_pi(*g_default_name, t, e, mk_binder_info());
}

extern "C" object * lean_expr_mk_let(object * n, object * t, object * v, object * b, uint8 nondep);
expr mk_let(name const & n, expr const & t, expr const & v, expr const & b, bool nondep) {
    return expr(lean_expr_mk_let(n.to_obj_arg(), t.to_obj_arg(), v.to_obj_arg(), b.to_obj_arg(), nondep));
}

static expr * g_Prop  = nullptr;
static expr * g_Type0 = nullptr;
expr mk_Prop() { return *g_Prop; }
expr mk_Type() { return *g_Type0; }

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

extern "C" uint8 lean_expr_is_have(object * e);
bool let_nondep_core(expr const & e) {
    lean_assert(is_let(e));
    return lean_expr_is_have(e.to_obj_arg());
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
        return mk_let(let_name(e), new_type, new_value, new_body, let_nondep(e));
    else
        return e;
}

extern "C" object * lean_expr_consume_type_annotations(obj_arg e);

expr consume_type_annotations(expr const & e) { return expr(lean_expr_consume_type_annotations(e.to_obj_arg())); }

// =======================================
// Loose bound variable management

static bool has_loose_bvars_in_domain(expr const & b, unsigned vidx, bool strict) {
    if (is_pi(b)) {
        if (has_loose_bvar(binding_domain(b), vidx)) {
            if (is_explicit(binding_info(b))) {
                return true;
            } else if (has_loose_bvars_in_domain(binding_body(b), 0, strict)) {
                // "Transitivity": vidx occurs in current implicit argument, so we search for current argument in the body.
                return true;
            }
        }
        // finally we search for vidx in the body
        return has_loose_bvars_in_domain(binding_body(b), vidx+1, strict);
    } else if (!strict) {
        return has_loose_bvar(b, vidx);
    } else {
        return false;
    }
}

bool has_loose_bvar(expr const & e, unsigned i) {
    if (!has_loose_bvars(e))
        return false;
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

extern "C" LEAN_EXPORT uint8 lean_expr_has_loose_bvar(b_obj_arg e, b_obj_arg i) {
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

extern "C" LEAN_EXPORT object * lean_expr_lower_loose_bvars(b_obj_arg e, b_obj_arg s, b_obj_arg d) {
    if (!lean_is_scalar(s) || !lean_is_scalar(d) || lean_unbox(s) < lean_unbox(d)) {
        lean_inc(e);
        return e;
    }
    return lower_loose_bvars(TO_REF(expr, e), lean_unbox(s), lean_unbox(d)).steal();
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

extern "C" LEAN_EXPORT object * lean_expr_lift_loose_bvars(b_obj_arg e, b_obj_arg s, b_obj_arg d) {
    if (!lean_is_scalar(s) || !lean_is_scalar(d)) {
        lean_inc(e);
        return e;
    }
    return lift_loose_bvars(TO_REF(expr, e), lean_unbox(s), lean_unbox(d)).steal();
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
// Initialization & Finalization

void initialize_expr() {
    get_dummy();
    g_default_name = new name("a");
    mark_persistent(g_default_name->raw());
    g_Type0        = new expr(mk_sort(mk_level_one()));
    mark_persistent(g_Type0->raw());
    g_Prop         = new expr(mk_sort(mk_level_zero()));
    mark_persistent(g_Prop->raw());
    /* TODO(Leo): add support for builtin constants in the kernel.
       Something similar to what we have in the library directory. */
}

void finalize_expr() {
    delete g_Prop;
    delete g_Type0;
    delete g_dummy;
    delete g_default_name;
}

// =======================================
// Legacy

optional<expr> has_expr_metavar_strict(expr const & e) {
    if (!has_expr_metavar(e))
        return none_expr();
    optional<expr> r;
    for_each(e, [&](expr const & e) {
            if (r || !has_expr_metavar(e)) return false;
            if (is_metavar_app(e)) { r = e; return false; }
            return true;
        });
    return r;
}
}
