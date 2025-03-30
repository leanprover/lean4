/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <unordered_set>
#include <algorithm>
#include <string>
#include <limits>
#include <cctype>
#include <vector>
#include "util/name_hash_set.h"
#include "kernel/type_checker.h"
#include "kernel/for_each_fn.h"
#include "kernel/replace_fn.h"
#include "kernel/find_fn.h"
#include "kernel/inductive.h"
#include "kernel/instantiate.h"
#include "kernel/kernel_exception.h"
#include "kernel/trace.h"
#include "library/util.h"
#include "library/suffixes.h"
#include "library/aux_recursors.h"
#include "library/replace_visitor.h"
#include "library/constants.h"
#include "library/compiler/lambda_lifting.h"
#include "library/compiler/eager_lambda_lifting.h"
#include "library/compiler/util.h"

namespace lean {
optional<unsigned> is_enum_type(environment const & env, name const & I) {
    constant_info info  = env.get(I);
    if (!info.is_inductive()) return optional<unsigned>();
    /* `decidable` is morally an enumeration type */
    if (I == get_decidable_name()) return optional<unsigned>(1);
    unsigned n = 0;
    names cs = info.to_inductive_val().get_cnstrs();
    if (length(cs) == 1) {
        /* We do not consider types such as `unit` as enumeration types.
           There is no motivation for them to be, since nobody will use them in composite datastructures.
           So, we don't save space, but we keep boxing/unboxing. Moreover `unit` is used to encode `thunks`
           which get closures. Thus, if we treat `unit` as an enumeration type, we will perform a useless
           unboxing whenever we force a thunk. */
        return optional<unsigned>();
    }
    for (name const & c : cs) {
        if (is_pi(env.get(c).get_type()))
            return optional<unsigned>();
        if (n == std::numeric_limits<unsigned>::max())
            return optional<unsigned>();
        n++;
    }
    if (n < (1u << 8)) {
        return optional<unsigned>(1);
    } else if (n < (1u << 16)) {
        return optional<unsigned>(2);
    } else {
        return optional<unsigned>(4);
    }
}

static expr * g_usize  = nullptr;
static expr * g_uint8  = nullptr;
static expr * g_uint16 = nullptr;
static expr * g_uint32 = nullptr;
static expr * g_uint64 = nullptr;

optional<expr> to_uint_type(unsigned nbytes) {
    /* Remark: we use 0 to denote the size of the type `usize` since it is platform specific, and
       we don't want the generated code to be platform specific.
       `usize` is 4 in 32-bit machines and 8 in 64-bit. */
    switch (nbytes) {
    case 0:  return some_expr(*g_usize);
    case 1:  return some_expr(*g_uint8);
    case 2:  return some_expr(*g_uint16);
    case 4:  return some_expr(*g_uint32);
    case 8:  return some_expr(*g_uint64);
    default: return none_expr();
    }
}

unsigned get_num_nested_lambdas(expr e) {
    unsigned r = 0;
    while (is_lambda(e)) {
        r++;
        e = binding_body(e);
    }
    return r;
}

extern "C" uint8 lean_has_inline_attribute(object* env, object* n);
extern "C" uint8 lean_has_inline_if_reduce_attribute(object* env, object* n);
extern "C" uint8 lean_has_macro_inline_attribute(object* env, object* n);
extern "C" uint8 lean_has_noinline_attribute(object* env, object* n);

bool has_inline_attribute(elab_environment const & env, name const & n) { return lean_has_inline_attribute(env.to_obj_arg(), n.to_obj_arg()); }
bool has_inline_if_reduce_attribute(elab_environment const & env, name const & n) { return lean_has_inline_if_reduce_attribute(env.to_obj_arg(), n.to_obj_arg()); }
bool has_macro_inline_attribute(elab_environment const & env, name const & n) { return lean_has_macro_inline_attribute(env.to_obj_arg(), n.to_obj_arg()); }
bool has_noinline_attribute(elab_environment const & env, name const & n) { return lean_has_noinline_attribute(env.to_obj_arg(), n.to_obj_arg()); }

extern "C" uint8 lean_has_never_extract_attribute(object* env, object *n);
bool has_never_extract_attribute(elab_environment const & env, name const & n) { return lean_has_never_extract_attribute(env.to_obj_arg(), n.to_obj_arg()); }

bool is_lcnf_atom(expr const & e) {
    switch (e.kind()) {
    case expr_kind::FVar: case expr_kind::Const: case expr_kind::Lit:
        return true;
    default:
        return false;
    }
}

class elim_trivial_let_decls_fn : public replace_visitor {
    virtual expr visit_let(expr const & e) override {
        if (is_lcnf_atom(let_value(e))) {
            return visit(instantiate(let_body(e), let_value(e)));
        } else {
            return replace_visitor::visit_let(e);
        }
    }
};

expr elim_trivial_let_decls(expr const & e) {
    return elim_trivial_let_decls_fn()(e);
}

struct unfold_macro_defs_fn : public replace_visitor {
    elab_environment const & m_env;
    unfold_macro_defs_fn(elab_environment const & env):m_env(env) {}


    bool should_macro_inline(name const & n) {
        if (!has_macro_inline_attribute(m_env, n)) return false;
        auto info = m_env.get(n);
        if (!info.has_value())
            return false;
        bool is_rec = static_cast<bool>(find(info.get_value(), [&](expr const & e, unsigned) { return is_const(e, n); }));
        // We do not macro_inline recursive definitions. TODO: check that when setting the attribute.
        return !is_rec;
    }

    virtual expr visit_app(expr const & e) override {
        buffer<expr> args;
        expr const & fn = get_app_args(e, args);
        bool modified = false;
        for (expr & arg : args) {
            expr new_arg = visit(arg);
            if (!is_eqp(new_arg, arg))
                modified = true;
            arg = new_arg;
        }
        if (is_constant(fn)) {
            name const & n = const_name(fn);
            if (should_macro_inline(n)) {
                expr new_fn = instantiate_value_lparams(m_env.get(n), const_levels(fn));
                std::reverse(args.begin(), args.end());
                return visit(apply_beta(new_fn, args.size(), args.data()));
            }
        }
        expr new_fn = visit(fn);
        if (!modified && is_eqp(new_fn, fn))
            return e;
        else
            return mk_app(new_fn, args);
    }

    virtual expr visit_constant(expr const & e) override {
        name const & n = const_name(e);
        if (should_macro_inline(n)) {
            return visit(instantiate_value_lparams(m_env.get(n), const_levels(e)));
        } else {
            return e;
        }
    }
};

expr unfold_macro_defs(elab_environment const & env, expr const & e) {
    return unfold_macro_defs_fn(env)(e);
}

bool is_cases_on_recursor(elab_environment const & env, name const & n) {
    return ::lean::is_aux_recursor(env, n) && n.get_string() == g_cases_on;
}

unsigned get_cases_on_arity(elab_environment const & env, name const & c, bool before_erasure) {
    lean_assert(is_cases_on_recursor(env, c));
    inductive_val I_val = get_cases_on_inductive_val(env, c);
    unsigned nminors    = I_val.get_ncnstrs();
    if (before_erasure) {
        unsigned nparams    = I_val.get_nparams();
        unsigned nindices   = I_val.get_nindices();
        return nparams + 1 /* motive */ + nindices + 1 /* major */ + nminors;
    } else {
        return 1 /* major */ + nminors;
    }
}

unsigned get_cases_on_major_idx(elab_environment const & env, name const & c, bool before_erasure) {
    if (before_erasure) {
        inductive_val I_val = get_cases_on_inductive_val(env, c);
        return I_val.get_nparams() + 1 /* motive */ + I_val.get_nindices();
    } else {
        return 0;
    }
}

expr get_cases_on_app_major(elab_environment const & env, expr const & c, bool before_erasure) {
    lean_assert(is_cases_on_app(env, c));
    buffer<expr> args;
    expr const & fn = get_app_args(c, args);
    return args[get_cases_on_major_idx(env, const_name(fn), before_erasure)];
}

pair<unsigned, unsigned> get_cases_on_minors_range(elab_environment const & env, name const & c, bool before_erasure) {
    inductive_val I_val = get_cases_on_inductive_val(env, c);
    unsigned nminors    = I_val.get_ncnstrs();
    if (before_erasure) {
        unsigned nparams    = I_val.get_nparams();
        unsigned nindices   = I_val.get_nindices();
        unsigned first_minor_idx = nparams + 1 /*motive*/ + nindices + 1 /* major */;
        return mk_pair(first_minor_idx, first_minor_idx + nminors);
    } else {
        return mk_pair(1, 1+nminors);
    }
}

expr mk_lc_unreachable(type_checker::state & s, local_ctx const & lctx, expr const & type) {
    type_checker tc(s, lctx);
    expr t    = cheap_beta_reduce(type);
    level lvl = sort_level(tc.ensure_type(t));
    return mk_app(mk_constant(get_lc_unreachable_name(), {lvl}), t);
}

bool is_join_point_name(name const & n) {
    return !n.is_atomic() && n.is_string() && strncmp(n.get_string().data(), "_join", 5) == 0;
}

bool is_pseudo_do_join_point_name(name const & n) {
    return !n.is_atomic() && n.is_string() && strncmp(n.get_string().data(), "__do_jp", 6) == 0;
}

bool has_fvar(expr const & e, expr const & fvar) {
    if (!has_fvar(e)) return false;
    bool found = false;
    for_each(e, [&](expr const & e, unsigned) {
            if (!has_fvar(e)) return false;
            if (found) return false;
            if (is_fvar(e) && fvar_name(fvar) == fvar_name(e))
                found = true;
            return true;
        });
    return found;
}

void mark_used_fvars(expr const & e, buffer<expr> const & fvars, buffer<bool> & used) {
    used.resize(fvars.size(), false);
    if (!has_fvar(e) || fvars.empty())
        return;
    bool all_used = false;
    for_each(e, [&](expr const & e, unsigned) {
            if (!has_fvar(e)) return false;
            if (all_used) return false;
            if (is_fvar(e)) {
                all_used = true;
                for (unsigned i = 0; i < fvars.size(); i++) {
                    if (!used[i]) {
                        all_used = false;
                        if (fvar_name(fvars[i]) == fvar_name(e)) {
                            used[i] = true;
                            break;
                        }
                    }
                }
            }
            return true;
        });
}

expr replace_fvar(expr const & e, expr const & fvar, expr const & new_term) {
    if (!has_fvar(e)) return e;
    return replace(e, [&](expr const & e, unsigned) {
            if (!has_fvar(e)) return some_expr(e);
            if (is_fvar(e) && fvar_name(fvar) == fvar_name(e))
                return some_expr(new_term);
            return none_expr();
        });
}

void sort_fvars(local_ctx const & lctx, buffer<expr> & fvars) {
    std::sort(fvars.begin(), fvars.end(),
              [&](expr const & x, expr const & y) {
                  return lctx.get_local_decl(x).get_idx() < lctx.get_local_decl(y).get_idx();
              });
}

unsigned get_lcnf_size(elab_environment const & env, expr e) {
    unsigned r = 0;
    switch (e.kind()) {
    case expr_kind::BVar:  case expr_kind::MVar:
    case expr_kind::Sort:
    case expr_kind::Lit:   case expr_kind::FVar:
    case expr_kind::Pi:    case expr_kind::Proj:
    case expr_kind::MData:
        return 1;
    case expr_kind::Const:
        return 1;
    case expr_kind::Lambda:
        while (is_lambda(e)) {
            e = binding_body(e);
        }
        return get_lcnf_size(env, e);
    case expr_kind::App:
        if (is_cases_on_app(env, e)) {
            expr const & c_fn   = get_app_fn(e);
            inductive_val I_val = env.get(const_name(c_fn).get_prefix()).to_inductive_val();
            unsigned nminors    = I_val.get_ncnstrs();
            r = 1;
            for (unsigned i = 0; i < nminors; i++) {
                lean_assert(is_app(e));
                r += get_lcnf_size(env, app_arg(e));
                e = app_fn(e);
            }
            return r;
        } else {
            return 1;
        }
    case expr_kind::Let:
        while (is_let(e)) {
            r += get_lcnf_size(env, let_value(e));
            e = let_body(e);
        }
        return r + get_lcnf_size(env, e);
    }
    lean_unreachable();
}

static expr * g_neutral_expr     = nullptr;
static expr * g_unreachable_expr = nullptr;
static expr * g_object_type      = nullptr;
static expr * g_void_type        = nullptr;

expr mk_enf_unreachable() {
    return *g_unreachable_expr;
}

expr mk_enf_neutral() {
    return *g_neutral_expr;
}

expr mk_enf_object_type() {
    return *g_object_type;
}

expr mk_llnf_void_type() {
    return *g_void_type;
}

expr mk_enf_neutral_type() {
    return *g_neutral_expr;
}

bool is_enf_neutral(expr const & e) {
    return e == *g_neutral_expr;
}

bool is_enf_unreachable(expr const & e) {
    return e == *g_unreachable_expr;
}

bool is_enf_object_type(expr const & e) {
    return e == *g_object_type;
}

bool is_llnf_void_type(expr const & e) {
    return e == *g_void_type;
}

bool is_runtime_builtin_type(name const & n) {
    /* TODO(Leo): use an attribute? */
    return
        n == get_string_name() ||
        n == get_uint8_name()  ||
        n == get_uint16_name() ||
        n == get_uint32_name() ||
        n == get_uint64_name() ||
        n == get_usize_name()  ||
        n == get_float_name()  ||
        n == get_float32_name() ||
        n == get_thunk_name()  ||
        n == get_task_name()   ||
        n == get_array_name()  ||
        n == get_mut_quot_name()  ||
        n == get_byte_array_name()  ||
        n == get_float_array_name()  ||
        n == get_nat_name()    ||
        n == get_int_name();
}

bool is_runtime_scalar_type(name const & n) {
    return
        n == get_uint8_name()  ||
        n == get_uint16_name() ||
        n == get_uint32_name() ||
        n == get_uint64_name() ||
        n == get_usize_name()  ||
        n == get_float_name()  ||
        n == get_float32_name();
}

bool is_llnf_unboxed_type(expr const & type) {
    return type != mk_enf_object_type() && type != mk_enf_neutral_type() && !is_pi(type);
}

bool is_irrelevant_type(type_checker::state & st, local_ctx lctx, expr const & type) {
    if (is_sort(type) || type_checker(st, lctx).is_prop(type))
        return true;
    expr type_it = type;
    if (is_pi(type_it)) {
        while (is_pi(type_it)) {
            expr fvar = lctx.mk_local_decl(st.ngen(), binding_name(type_it), binding_domain(type_it));
            type_it = type_checker(st, lctx).whnf(instantiate(binding_body(type_it), fvar));
        }
        if (is_sort(type_it))
            return true;
    }
    return false;
}

bool is_irrelevant_type(environment const & env, expr const & type) {
    type_checker::state st(env);
    return is_irrelevant_type(st, local_ctx(), type);
}

void collect_used(expr const & e, name_hash_set & S) {
    if (!has_fvar(e)) return;
    for_each(e, [&](expr const & e, unsigned) {
            if (!has_fvar(e)) return false;
            if (is_fvar(e)) { S.insert(fvar_name(e)); return false; }
            return true;
        });
}

bool depends_on(expr const & e, name_hash_set const & s) {
    if (!has_fvar(e)) return false;
    bool found = false;
    for_each(e, [&](expr const & e, unsigned) {
            if (!has_fvar(e)) return false;
            if (found) return false;
            if (is_fvar(e) && s.find(fvar_name(e)) != s.end()) {
                found = true;
            }
            return true;
        });
    return found;
}

optional<unsigned> has_trivial_structure(environment const & env, name const & I_name) {
    if (is_runtime_builtin_type(I_name))
        return optional<unsigned>();
    inductive_val I_val = env.get(I_name).to_inductive_val();
    if (I_val.is_unsafe())
        return optional<unsigned>();
    if (I_val.get_ncnstrs() != 1 || I_val.is_rec())
        return optional<unsigned>();
    buffer<bool> rel_fields;
    get_constructor_relevant_fields(env, head(I_val.get_cnstrs()), rel_fields);
    /* The following #pragma is to disable a bogus g++ 4.9 warning at `optional<unsigned> r` */
    #if defined(__GNUC__) && !defined(__CLANG__)
    #pragma GCC diagnostic ignored "-Wmaybe-uninitialized"
    #endif
    optional<unsigned> result;
    for (unsigned i = 0; i < rel_fields.size(); i++) {
        if (rel_fields[i]) {
            if (result)
                return optional<unsigned>();
            result = i;
        }
    }
    return result;
}

expr mk_runtime_type(type_checker::state & st, local_ctx const & lctx, expr e) {
    try {
        type_checker tc(st, lctx);
        e = tc.whnf(e);

        if (is_constant(e)) {
            name const & c = const_name(e);
            if (is_runtime_scalar_type(c)) {
                return e;
            } else if (c == get_char_name()) {
                return mk_constant(get_uint32_name());
            } else if (c == get_usize_name()) {
                return e;
            } else if (c == get_float_name()) {
                return e;
            } else if (c == get_float32_name()) {
                return e;
            } else if (optional<unsigned> nbytes = is_enum_type(st.env(), c)) {
                return *to_uint_type(*nbytes);
            }
        }

        if (is_app_of(e, get_decidable_name())) {
            /* Recall that `decidable A` and `bool` have the same runtime representation. */
            return *to_uint_type(1);
        }

        if (is_sort(e) || tc.is_prop(e)) {
            return mk_enf_neutral_type();
        }

        if (is_pi(e)) {
            expr it = e;
            while (is_pi(it))
                it = binding_body(it);
            if (is_sort(it)) {
                // functions that produce types are irrelevant
                return mk_enf_neutral_type();
            }
        }


        /* If `e` is a trivial structure such as `Subtype`, then convert the only relevant
           field to a runtime type. */
        expr const & fn = get_app_fn(e);
        if (is_constant(fn) && is_inductive(st.env(), const_name(fn))) {
            name const & I_name = const_name(fn);
            environment const & env = st.env();
            if (optional<unsigned> fidx = has_trivial_structure(env, I_name)) {
                /* Retrieve field `fidx` type */
                inductive_val I_val = env.get(I_name).to_inductive_val();
                name K = head(I_val.get_cnstrs());
                unsigned nparams = I_val.get_nparams();
                buffer<expr> e_args;
                get_app_args(e, e_args);
                lean_assert(nparams <= e_args.size());
                expr k_app = mk_app(mk_constant(K, const_levels(fn)), nparams, e_args.data());
                expr type = tc.whnf(tc.infer(k_app));
                local_ctx aux_lctx = lctx;
                unsigned idx = 0;
                while (is_pi(type)) {
                    if (idx == *fidx) {
                        return mk_runtime_type(st, aux_lctx, binding_domain(type));
                    }
                    expr local = aux_lctx.mk_local_decl(st.ngen(), binding_name(type), binding_domain(type), binding_info(type));
                    type       = instantiate(binding_body(type), local);
                    type       = type_checker(st, aux_lctx).whnf(type);
                    idx++;
                }
            }
        }

        return mk_enf_object_type();
    } catch (kernel_exception &) {
        return mk_enf_object_type();
    }
}

elab_environment register_stage1_decl(elab_environment const & env, name const & n, names const & ls, expr const & t, expr const & v) {
    declaration aux_decl = mk_definition(mk_cstage1_name(n), ls, t, v, reducibility_hints::mk_opaque(), definition_safety::unsafe);
    return env.add(aux_decl, false);
}

bool is_stage2_decl(elab_environment const & env, name const & n) {
    return static_cast<bool>(env.find(mk_cstage2_name(n)));
}

elab_environment register_stage2_decl(elab_environment const & env, name const & n, expr const & t, expr const & v) {
    declaration aux_decl = mk_definition(mk_cstage2_name(n), names(), t,
                                         v, reducibility_hints::mk_opaque(), definition_safety::unsafe);
    return env.add(aux_decl, false);
}

/* @[export lean.get_num_lit_core]
   def get_num_lit : expr → option nat */
extern "C" object * lean_get_num_lit(obj_arg o);

optional<nat> get_num_lit_ext(expr const & e) {
    inc(e.raw());
    return to_optional_nat(lean_get_num_lit(e.raw()));
}

optional<unsigned> is_fix_core(name const & n) {
    if (!n.is_atomic() || !n.is_string()) return optional<unsigned>();
    string_ref const & r = n.get_string();
    if (r.length() != 8) return optional<unsigned>();
    char const * s = r.data();
    if (std::strncmp(s, "fixCore", 7) != 0 || !std::isdigit(s[7])) return optional<unsigned>();
    return optional<unsigned>(s[7] - '0');
}

optional<expr> mk_enf_fix_core(unsigned n) {
    if (n == 0 || n > 6) return none_expr();
    std::ostringstream s;
    s << "fixCore" << n;
    return some_expr(mk_constant(name(s.str())));
}


/*
Auxiliary visitor used to detect let-decl LCNF violations.
In LCNF, the type `ty` in `let x : ty := v in t` must not be irrelevant.

Remark: this validator is incorrect. When specializing polymorphic code,
we can get an irrelevant `ty`.
We disabled this validator since we will delete the code generator written in C++.
*/
class lcnf_valid_let_decls_fn {
    elab_environment    m_env;
    type_checker::state m_st;
    local_ctx           m_lctx;

    elab_environment const & env() const { return m_env; }

    name_generator & ngen() { return m_st.ngen(); }

    optional<expr> visit_cases(expr const & e) {
        buffer<expr> args;
        expr const & c = get_app_args(e, args);
        unsigned minor_idx; unsigned minors_end;
        bool before_erasure = true;
        std::tie(minor_idx, minors_end) = get_cases_on_minors_range(env(), const_name(c), before_erasure);
        for (; minor_idx < minors_end; minor_idx++) {
            if (optional<expr> found = visit(args[minor_idx]))
                return found;
        }
        return none_expr();
    }

    optional<expr> visit_app(expr const & e) {
        if (is_cases_on_app(env(), e)) {
            return visit_cases(e);
        } else {
            return none_expr();
        }
    }

    optional<expr> visit_lambda(expr e) {
        buffer<expr> fvars;
        while (is_lambda(e)) {
            expr new_d    = instantiate_rev(binding_domain(e), fvars.size(), fvars.data());
            expr new_fvar = m_lctx.mk_local_decl(ngen(), binding_name(e), new_d, binding_info(e));
            fvars.push_back(new_fvar);
            e = binding_body(e);
        }
        e = instantiate_rev(e, fvars.size(), fvars.data());
        return visit(e);
    }

    optional<expr> visit_let(expr e) {
        buffer<expr> fvars;
        while (is_let(e)) {
            expr new_type = instantiate_rev(let_type(e), fvars.size(), fvars.data());
            if (is_irrelevant_type(m_st, m_lctx, new_type)) {
                return some_expr(e);
            }
            expr new_val  = instantiate_rev(let_value(e), fvars.size(), fvars.data());
            if (optional<expr> found = visit(new_val))
                return found;
            expr new_fvar = m_lctx.mk_local_decl(ngen(), let_name(e), new_type, new_val);
            fvars.push_back(new_fvar);
            e = let_body(e);
        }
        return visit(instantiate_rev(e, fvars.size(), fvars.data()));
    }

    optional<expr> visit(expr const & e) {
        switch (e.kind()) {
        case expr_kind::Lambda: return visit_lambda(e);
        case expr_kind::Let:    return visit_let(e);
        case expr_kind::App:    return visit_app(e);
        default:                return none_expr();
        }
    }

public:
    lcnf_valid_let_decls_fn(elab_environment const & env, local_ctx const & lctx):
        m_env(env), m_st(env), m_lctx(lctx) {}

    optional<expr> operator()(expr const & e) {
        return visit(e);
    }
};

optional<expr> lcnf_valid_let_decls(elab_environment const & env, expr const & e) {
    return lcnf_valid_let_decls_fn(env, local_ctx())(e);
}

bool lcnf_check_let_decls(elab_environment const & env, comp_decl const & d) {
    if (optional<expr> v = lcnf_valid_let_decls(env, d.snd())) {
        tout() << "LCNF violation at " << d.fst() << "\n" << *v << "\n";
        return false;
    } else {
        return true;
    }
}

bool lcnf_check_let_decls(elab_environment const & env, comp_decls const & ds) {
    for (comp_decl const & d : ds) {
        if (!lcnf_check_let_decls(env, d))
            return false;
    }
    return true;
}

// =======================================
// UInt and USize helper functions

std::vector<pair<name, unsigned>> * g_builtin_scalar_size = nullptr;

expr mk_usize_type() {
    return *g_usize;
}

bool is_usize_type(expr const & e) {
    return is_constant(e, get_usize_name());
}

optional<unsigned> is_builtin_scalar(expr const & type) {
    if (!is_constant(type)) return optional<unsigned>();
    for (pair<name, unsigned> const & p : *g_builtin_scalar_size) {
        if (const_name(type) == p.first) {
            return optional<unsigned>(p.second);
        }
    }
    return optional<unsigned>();
}

optional<unsigned> is_enum_type(environment const & env, expr const & type) {
    expr const & I = get_app_fn(type);
    if (!is_constant(I)) return optional<unsigned>();
    return is_enum_type(env, const_name(I));
}

// =======================================


expr lcnf_eta_expand(type_checker::state & st, local_ctx lctx, expr e) {
    /* Remark: we do not use `type_checker.eta_expand` because it does not preserve LCNF */
    try {
        buffer<expr> args;
        type_checker tc(st, lctx);
        expr e_type = tc.whnf(tc.infer(e));
        while (is_pi(e_type)) {
            expr arg = lctx.mk_local_decl(st.ngen(), binding_name(e_type), binding_domain(e_type), binding_info(e_type));
            args.push_back(arg);
            e_type = type_checker(st, lctx).whnf(instantiate(binding_body(e_type), arg));
        }
        if (args.empty())
            return e;
        buffer<expr> fvars;
        while (is_let(e)) {
            expr type = instantiate_rev(let_type(e), fvars.size(), fvars.data());
            expr val  = instantiate_rev(let_value(e), fvars.size(), fvars.data());
            expr fvar = lctx.mk_local_decl(st.ngen(), let_name(e), type, val);
            fvars.push_back(fvar);
            e         = let_body(e);
        }
        e = instantiate_rev(e, fvars.size(), fvars.data());
        if (!is_lcnf_atom(e)) {
            e = lctx.mk_local_decl(st.ngen(), "_e", type_checker(st, lctx).infer(e), e);
            fvars.push_back(e);
        }
        e = mk_app(e, args);
        return lctx.mk_lambda(args, lctx.mk_lambda(fvars, e));
    } catch (exception &) {
        /* This can happen since previous compilation steps may have
           produced type incorrect terms. */
        return e;
    }
}

bool is_quot_primitive_app(elab_environment const & env, expr const & e) {
  expr const & f = get_app_fn(e);
  return is_constant(f) && is_quot_primitive(env, const_name(f));
}

bool must_be_eta_expanded(elab_environment const & env, expr const & e) {
  return
    is_constructor_app(env, e) ||
    is_proj(e) ||
    is_matcher_app(env, e) ||
    is_cases_on_app(env, e) ||
    is_lc_unreachable_app(e) ||
    is_quot_primitive_app(env, e);
}

void initialize_compiler_util() {
    g_neutral_expr        = new expr(mk_constant("_neutral"));
    mark_persistent(g_neutral_expr->raw());
    g_unreachable_expr    = new expr(mk_constant("_unreachable"));
    mark_persistent(g_unreachable_expr->raw());
    g_object_type         = new expr(mk_constant("_obj"));
    mark_persistent(g_object_type->raw());
    g_void_type           = new expr(mk_constant("_void"));
    mark_persistent(g_void_type->raw());
    g_usize               = new expr(mk_constant(get_usize_name()));
    mark_persistent(g_usize->raw());
    g_uint8               = new expr(mk_constant(get_uint8_name()));
    mark_persistent(g_uint8->raw());
    g_uint16              = new expr(mk_constant(get_uint16_name()));
    mark_persistent(g_uint16->raw());
    g_uint32              = new expr(mk_constant(get_uint32_name()));
    mark_persistent(g_uint32->raw());
    g_uint64              = new expr(mk_constant(get_uint64_name()));
    mark_persistent(g_uint64->raw());
    g_builtin_scalar_size = new std::vector<pair<name, unsigned>>();
    g_builtin_scalar_size->emplace_back(get_uint8_name(),  1);
    g_builtin_scalar_size->emplace_back(get_uint16_name(), 2);
    g_builtin_scalar_size->emplace_back(get_uint32_name(), 4);
    g_builtin_scalar_size->emplace_back(get_uint64_name(), 8);
    g_builtin_scalar_size->emplace_back(get_float_name(),  8);
    g_builtin_scalar_size->emplace_back(get_float32_name(), 4);
}

void finalize_compiler_util() {
    delete g_neutral_expr;
    delete g_unreachable_expr;
    delete g_object_type;
    delete g_void_type;
    delete g_usize;
    delete g_uint8;
    delete g_uint16;
    delete g_uint32;
    delete g_uint64;
    delete g_builtin_scalar_size;
}
}
