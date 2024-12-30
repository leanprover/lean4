/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <limits>
#include <vector>
#include <algorithm>
#include <unordered_set>
#include "runtime/flet.h"
#include "runtime/sstream.h"
#include "util/name_hash_set.h"
#include "util/name_hash_map.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/for_each_fn.h"
#include "kernel/inductive.h"
#include "kernel/trace.h"
#include "library/util.h"
#include "library/compiler/util.h"
#include "library/compiler/llnf.h"
#include "library/compiler/ll_infer_type.h"
#include "library/compiler/cse.h"
#include "library/compiler/elim_dead_let.h"
#include "library/compiler/extern_attribute.h"
#include "library/compiler/borrowed_annotation.h"
#include "library/compiler/ir.h"

namespace lean {
static expr * g_apply       = nullptr;
static expr * g_closure     = nullptr;
static char const * g_cnstr = "_cnstr";
static name * g_reuse       = nullptr;
static name * g_reset       = nullptr;
static name * g_fset        = nullptr;
static name * g_f32set      = nullptr;
static name * g_sset        = nullptr;
static name * g_uset        = nullptr;
static name * g_proj        = nullptr;
static name * g_sproj       = nullptr;
static name * g_fproj       = nullptr;
static name * g_uproj       = nullptr;
static expr * g_jmp         = nullptr;
static name * g_box         = nullptr;
static name * g_unbox       = nullptr;
static expr * g_inc         = nullptr;
static expr * g_dec         = nullptr;

expr mk_llnf_apply() { return *g_apply; }
bool is_llnf_apply(expr const & e) { return e == *g_apply; }

expr mk_llnf_closure() { return *g_closure; }
bool is_llnf_closure(expr const & e) { return e == *g_closure; }

static bool is_llnf_unary_primitive(expr const & e, name const & prefix, unsigned & i) {
    if (!is_constant(e)) return false;
    name const & n = const_name(e);
    if (!is_internal_name(n) || n.is_atomic() || !n.is_numeral() || n.get_prefix() != prefix) return false;
    i = n.get_numeral().get_small_value();
    return true;
}

static bool is_llnf_binary_primitive(expr const & e, name const & prefix, unsigned & i1, unsigned & i2) {
    if (!is_constant(e)) return false;
    name const & n2 = const_name(e);
    if (n2.is_atomic() || !n2.is_numeral()) return false;
    i2 = n2.get_numeral().get_small_value();
    name const & n1 = n2.get_prefix();
    if (n1.is_atomic() || !n1.is_numeral() || n1.get_prefix() != prefix) return false;
    i1 = n1.get_numeral().get_small_value();
    return true;
}

static bool is_llnf_ternary_primitive(expr const & e, name const & prefix, unsigned & i1, unsigned & i2, unsigned & i3) {
    if (!is_constant(e)) return false;
    name const & n3  = const_name(e);
    if (!is_internal_name(n3)) return false;
    if (n3.is_atomic() || !n3.is_numeral()) return false;
    i3 = n3.get_numeral().get_small_value();
    name const & n2 = n3.get_prefix();
    if (n2.is_atomic() || !n2.is_numeral()) return false;
    i2 = n2.get_numeral().get_small_value();
    name const & n1 = n2.get_prefix();
    if (n1.is_atomic() || !n1.is_numeral() || n1.get_prefix() != prefix) return false;
    i1 = n1.get_numeral().get_small_value();
    return true;
}

static bool is_llnf_quaternary_primitive(expr const & e, name const & prefix, unsigned & i1, unsigned & i2, unsigned & i3, unsigned & i4) {
    if (!is_constant(e)) return false;
    name const & n4  = const_name(e);
    if (!is_internal_name(n4)) return false;
    if (n4.is_atomic() || !n4.is_numeral()) return false;
    i4 = n4.get_numeral().get_small_value();
    name const & n3  = n4.get_prefix();
    if (!is_internal_name(n3)) return false;
    if (n3.is_atomic() || !n3.is_numeral()) return false;
    i3 = n3.get_numeral().get_small_value();
    name const & n2 = n3.get_prefix();
    if (n2.is_atomic() || !n2.is_numeral()) return false;
    i2 = n2.get_numeral().get_small_value();
    name const & n1 = n2.get_prefix();
    if (n1.is_atomic() || !n1.is_numeral() || n1.get_prefix() != prefix) return false;
    i1 = n1.get_numeral().get_small_value();
    return true;
}

/*
A constructor object contains a header, then a sequence of pointers to other Lean objects,
a sequence of `usize` (i.e., `size_t`) scalar values, and a sequence of other scalar values.
We store pointer and `usize` objects before other scalar values to simplify how we compute
the position where data is stored. For example, the "instruction" `_sproj.4.2.3 o` access
a value of size 4 at offset `sizeof(void*)*2+3`.
We have considered a simpler representation where we just have the size and offset,
we decided to not used it because we would have to generate different C++ code for 32 and
64 bit machines. This would complicate the bootstrapping process.
We store the `usize` scalar values before other scalar values because their size is platform
specific. We also have custom instructions (`_uset` and `_uproj`) to set and retrieve `usize`
scalar fields.
*/

/* The `I._cnstr.<cidx>.<num_usizes>.<num_bytes>` instruction constructs a constructor object with tag `cidx`, and scalar area with space for `num_usize` `usize` values + `num_bytes` bytes. */
expr mk_llnf_cnstr(name const & I, unsigned cidx, unsigned num_usizes, unsigned num_bytes) {
    return mk_constant(name(name(name(name(I, g_cnstr), cidx), num_usizes), num_bytes));
}
bool is_llnf_cnstr(expr const & e, name & I, unsigned & cidx, unsigned & num_usizes, unsigned & num_bytes) {
    if (!is_constant(e)) return false;
    name const & n3  = const_name(e);
    if (!is_internal_name(n3)) return false;
    if (n3.is_atomic() || !n3.is_numeral()) return false;
    num_bytes = n3.get_numeral().get_small_value();
    name const & n2 = n3.get_prefix();
    if (n2.is_atomic() || !n2.is_numeral()) return false;
    num_usizes = n2.get_numeral().get_small_value();
    name const & n1 = n2.get_prefix();
    if (n1.is_atomic() || !n1.is_numeral())  return false;
    cidx = n1.get_numeral().get_small_value();
    name const & n0 = n1.get_prefix();
    if (n0.is_atomic() || !n0.is_string() || n0.get_string() != g_cnstr) return false;
    I = n0.get_prefix();
    return true;
}

/* The `_reuse.<cidx>.<num_usizes>.<num_bytes>.<updt_cidx>` is similar to `_cnstr.<cidx>.<num_usize>.<num_bytes>`, but it takes an extra argument: a memory cell that may be reused. */
expr mk_llnf_reuse(unsigned cidx, unsigned num_usizes, unsigned num_bytes, bool updt_cidx) {
    return mk_constant(name(name(name(name(*g_reuse, cidx), num_usizes), num_bytes), updt_cidx));
}
bool is_llnf_reuse(expr const & e, unsigned & cidx, unsigned & num_usizes, unsigned & num_bytes, bool & updt_cidx) {
    unsigned aux = 0;
    bool r = is_llnf_quaternary_primitive(e, *g_reuse, cidx, num_usizes, num_bytes, aux);
    updt_cidx = aux;
    return r;
}

expr mk_llnf_reset(unsigned n) { return mk_constant(name(*g_reset, n)); }
bool is_llnf_reset(expr const & e, unsigned & n) { return is_llnf_unary_primitive(e, *g_reset, n); }

/* The `_sset.<sz>.<n>.<offset>` instruction sets a scalar value of size `sz` (in bytes) at offset `sizeof(void*)*n + offset`. The value `n` is the number of pointer and `usize` fields. */
expr mk_llnf_sset(unsigned sz, unsigned n, unsigned offset) { return mk_constant(name(name(name(*g_sset, sz), n), offset)); }
bool is_llnf_sset(expr const & e, unsigned & sz, unsigned & n, unsigned & offset) { return is_llnf_ternary_primitive(e, *g_sset, sz, n, offset); }

expr mk_llnf_fset(unsigned n, unsigned offset) { return mk_constant(name(name(*g_fset, n), offset)); }
bool is_llnf_fset(expr const & e, unsigned & n, unsigned & offset) { return is_llnf_binary_primitive(e, *g_fset, n, offset); }

expr mk_llnf_f32set(unsigned n, unsigned offset) { return mk_constant(name(name(*g_f32set, n), offset)); }
bool is_llnf_f32set(expr const & e, unsigned & n, unsigned & offset) { return is_llnf_binary_primitive(e, *g_f32set, n, offset); }

/* The `_uset.<n>` instruction sets a `usize` value in a constructor object at offset `sizeof(void*)*n`. */
expr mk_llnf_uset(unsigned n) { return mk_constant(name(*g_uset, n)); }
bool is_llnf_uset(expr const & e, unsigned & n) { return is_llnf_unary_primitive(e, *g_uset, n); }

/* The `_proj.<idx>` instruction retrieves an object field in a constructor object at offset `sizeof(void*)*idx` */
expr mk_llnf_proj(unsigned idx) { return mk_constant(name(*g_proj, idx)); }
bool is_llnf_proj(expr const & e, unsigned & idx) { return is_llnf_unary_primitive(e, *g_proj, idx); }

/* The `_sproj.<sz>.<n>.<offset>` instruction retrieves a scalar field of size `sz` (in bytes) in a constructor object at offset `sizeof(void*)*n + offset`. The value `n` is the number of pointer and `usize` fields. */
expr mk_llnf_sproj(unsigned sz, unsigned n, unsigned offset) { return mk_constant(name(name(name(*g_sproj, sz), n), offset)); }
bool is_llnf_sproj(expr const & e, unsigned & sz, unsigned & n, unsigned & offset) { return is_llnf_ternary_primitive(e, *g_sproj, sz, n, offset); }

expr mk_llnf_fproj(unsigned n, unsigned offset) { return mk_constant(name(name(*g_sproj, n), offset)); }
bool is_llnf_fproj(expr const & e, unsigned & n, unsigned & offset) { return is_llnf_binary_primitive(e, *g_fproj, n, offset); }

/* The `_uproj.<idx>` instruction retrieves an `usize` field in a constructor object at offset `sizeof(void*)*idx` */
expr mk_llnf_uproj(unsigned idx) { return mk_constant(name(*g_uproj, idx)); }
bool is_llnf_uproj(expr const & e, unsigned & idx) { return is_llnf_unary_primitive(e, *g_uproj, idx); }

/* The `_jmp` instruction is a "jump" to a join point. */
expr mk_llnf_jmp() { return *g_jmp; }
bool is_llnf_jmp(expr const & e) { return e == *g_jmp; }

/* The `_box.<n>` instruction converts an unboxed value (type `uint*`) into a boxed value (type `_obj`).
   The parameter `n` specifies the number of bytes necessary to store the unboxed value.
   This information could be also retrieved from the type of the variable being boxed, but for simplicity,
   we store it in the instruction too.

   Remark: we use the instruction `_box.0` to box unboxed values of type `usize` into a boxed value (type `_obj`).
   We use `0` because the number of bytes necessary to store a `usize` is different in 32 and 64 bit machines. */
expr mk_llnf_box(unsigned n) { return mk_constant(name(*g_box, n)); }
bool is_llnf_box(expr const & e, unsigned & n) { return is_llnf_unary_primitive(e, *g_box, n); }

/* The `_unbox.<n>` instruction converts a boxed value (type `_obj`) into an unboxed value (type `uint*` or `usize`).
   The parameter `n` specifies the number of bytes necessary to store the unboxed value.
   It is not really needed, but we use to keep it consistent with `_box.<n>`.

   Remark: we use the instruction `_unbox.0` like we use `_box.0`. */
expr mk_llnf_unbox (unsigned n) { return mk_constant(name(*g_unbox, n)); }
bool is_llnf_unbox(expr const & e, unsigned & n) { return is_llnf_unary_primitive(e, *g_unbox, n); }

expr mk_llnf_inc() { return *g_inc; }
bool is_llnf_inc(expr const & e) { return e == *g_inc; }

expr mk_llnf_dec() { return *g_dec; }
bool is_llnf_dec(expr const & e) { return e == *g_dec; }

bool is_llnf_op(expr const & e) {
    return
        is_llnf_closure(e) ||
        is_llnf_apply(e)   ||
        is_llnf_cnstr(e)   ||
        is_llnf_reuse(e)   ||
        is_llnf_reset(e)   ||
        is_llnf_sset(e)    ||
        is_llnf_fset(e)    ||
        is_llnf_f32set(e)  ||
        is_llnf_uset(e)    ||
        is_llnf_proj(e)    ||
        is_llnf_sproj(e)   ||
        is_llnf_fproj(e)   ||
        is_llnf_uproj(e)   ||
        is_llnf_jmp(e)     ||
        is_llnf_box(e)     ||
        is_llnf_unbox(e)   ||
        is_llnf_inc(e)     ||
        is_llnf_dec(e);
}

cnstr_info::cnstr_info(unsigned cidx, list<field_info> const & finfo):
    m_cidx(cidx), m_field_info(finfo) {
    for (field_info const & info : finfo) {
        if (info.m_kind == field_info::Object)
            m_num_objs++;
        else if (info.m_kind == field_info::USize)
            m_num_usizes++;
        else if (info.m_kind == field_info::Scalar)
            m_scalar_sz += info.m_size;
    }
}

unsigned get_llnf_arity(elab_environment const & env, name const & n) {
    /* First, try to infer arity from `_cstage2` auxiliary definition. */
    name c = mk_cstage2_name(n);
    optional<constant_info> info = env.find(c);
    if (info && info->is_definition()) {
        return get_num_nested_lambdas(info->get_value());
    }
    optional<unsigned> arity = get_extern_constant_arity(env, n);
    if (!arity) throw exception(sstream() << "code generation failed, unknown '" << n << "'");
    return *arity;
}

static void get_cnstr_info_core(type_checker::state & st, name const & n, buffer<field_info> & result) {
    environment const & env = st.env();
    constant_info info      = env.get(n);
    lean_assert(info.is_constructor());
    constructor_val val = info.to_constructor_val();
    expr type           = info.get_type();
    name I_name         = val.get_induct();
    unsigned nparams    = val.get_nparams();
    local_ctx lctx;
    buffer<expr> telescope;
    unsigned next_object     = 0;
    unsigned max_scalar_size = 0;
    to_telescope(env, lctx, st.ngen(), type, telescope);
    lean_assert(telescope.size() >= nparams);
    for (unsigned i = nparams; i < telescope.size(); i++) {
        expr ftype = lctx.get_type(telescope[i]);
        if (is_irrelevant_type(st, lctx, ftype)) {
            result.push_back(field_info::mk_irrelevant());
        } else {
            type_checker tc(st, lctx);
            ftype = tc.whnf(ftype);
            if (is_usize_type(ftype)) {
                result.push_back(field_info::mk_usize());
            } else if (optional<unsigned> sz = is_builtin_scalar(ftype)) {
                max_scalar_size = std::max(*sz, max_scalar_size);
                result.push_back(field_info::mk_scalar(*sz, ftype));
            } else if (optional<unsigned> sz = is_enum_type(env, ftype)) {
                optional<expr> uint = to_uint_type(*sz);
                if (!uint) throw exception("code generation failed, enumeration type is too big");
                max_scalar_size = std::max(*sz, max_scalar_size);
                result.push_back(field_info::mk_scalar(*sz, *uint));
            } else {
                result.push_back(field_info::mk_object(next_object));
                next_object++;
            }
        }
    }

    unsigned next_idx = next_object;
    /* Remark:
       - usize fields are stored after object fields.
       - regular scalar fields are stored after object and usize fields,
         and are sorted by size. */
    /* Fix USize idxs */
    for (field_info & info : result) {
        if (info.m_kind == field_info::USize) {
            info.m_idx = next_idx;
            next_idx++;
        }
    }
    unsigned idx    = next_idx;
    unsigned offset = 0;
    /* Fix regular scalar offsets and idxs */
    for (unsigned sz = max_scalar_size; sz > 0; sz--) {
        for (field_info & info : result) {
            if (info.m_kind == field_info::Scalar && info.m_size == sz) {
                info.m_idx    = idx;
                info.m_offset = offset;
                offset += info.m_size;
            }
        }
    }
}

cnstr_info get_cnstr_info(type_checker::state & st, name const & n) {
    buffer<field_info> finfos;
    get_cnstr_info_core(st, n, finfos);
    unsigned cidx      = get_constructor_idx(st.env(), n);
    return cnstr_info(cidx, to_list(finfos));
}

class to_lambda_pure_fn {
    typedef name_hash_set name_set;
    typedef name_hash_map<cnstr_info> cnstr_info_cache;
    typedef name_hash_map<optional<unsigned>> enum_cache;
    elab_environment      m_env;
    type_checker::state   m_st;
    local_ctx             m_lctx;
    buffer<expr>          m_fvars;
    name                  m_x;
    name                  m_j;
    unsigned              m_next_idx{1};
    unsigned              m_next_jp_idx{1};
    cnstr_info_cache      m_cnstr_info_cache;

    elab_environment const & env() const { return m_env; }

    name_generator & ngen() { return m_st.ngen(); }

    optional<unsigned> is_enum_type(expr const & type) {
        return ::lean::is_enum_type(env(), type);
    }

    unsigned get_arity(name const & n) const {
        return ::lean::get_llnf_arity(env(), n);
    }

    bool is_join_point_app(expr const & e) {
        expr const & fn = get_app_fn(e);
        if (!is_fvar(fn)) return false;
        local_decl d = m_lctx.get_local_decl(fn);
        return is_join_point_name(d.get_user_name());
    }

    expr ensure_terminal(expr const & e) {
        lean_assert(!is_let(e) && !is_lambda(e));
        if (is_cases_on_app(env(), e) || is_fvar(e) || is_join_point_app(e) || is_enf_unreachable(e)) {
            return e;
        } else {
            expr type = ll_infer_type(env(), m_lctx, e);
            if (is_pi(type)) {
                /* It is a closure. */
                type = mk_enf_object_type();
            }
            return ::lean::mk_let("_res", type, e, mk_bvar(0));
        }
    }

    expr mk_llnf_app(expr const & fn, buffer<expr> const & args) {
        lean_assert(is_fvar(fn) || is_constant(fn));
        if (is_fvar(fn)) {
            local_decl d = m_lctx.get_local_decl(fn);
            if (is_join_point_name(d.get_user_name())) {
                return mk_app(mk_app(mk_llnf_jmp(), fn), args);
            } else {
                return mk_app(mk_app(mk_llnf_apply(), fn), args);
            }
        } else {
            lean_assert(is_constant(fn));
            if (is_enf_neutral(fn)) {
                return mk_enf_neutral();
            } else if (is_enf_unreachable(fn)) {
                return mk_enf_unreachable();
            } else {
                unsigned arity = get_arity(const_name(fn));
                if (args.size() == arity) {
                    return mk_app(fn, args);
                } else if (args.size() < arity) {
                    /* Under application: create closure. */
                    return mk_app(mk_app(mk_llnf_closure(), fn), args);
                } else {
                    /* Over application. */
                    lean_assert(args.size() > arity);
                    expr new_fn = m_lctx.mk_local_decl(ngen(), next_name(), mk_enf_object_type(), mk_app(fn, arity, args.data()));
                    m_fvars.push_back(new_fn);
                    return mk_app(mk_app(mk_llnf_apply(), new_fn), args.size() - arity, args.data() + arity);
                }
            }
        }
    }

    cnstr_info get_cnstr_info(name const & n) {
        auto it = m_cnstr_info_cache.find(n);
        if (it != m_cnstr_info_cache.end())
            return it->second;
        cnstr_info r = ::lean::get_cnstr_info(m_st, n);
        m_cnstr_info_cache.insert(mk_pair(n, r));
        return r;
    }

    name next_name() {
        name r = m_x.append_after(m_next_idx);
        m_next_idx++;
        return r;
    }

    name next_jp_name() {
        name r = m_j.append_after(m_next_jp_idx);
        m_next_jp_idx++;
        return mk_join_point_name(r);
    }

    expr mk_let(unsigned saved_fvars_size, expr r) {
        lean_assert(saved_fvars_size <= m_fvars.size());
        if (saved_fvars_size == m_fvars.size())
            return r;
        buffer<expr> used;
        name_hash_set used_fvars;
        collect_used(r, used_fvars);
        while (m_fvars.size() > saved_fvars_size) {
            expr x = m_fvars.back();
            m_fvars.pop_back();
            if (used_fvars.find(fvar_name(x)) == used_fvars.end()) {
                continue;
            }
            local_decl x_decl = m_lctx.get_local_decl(x);
            expr val          = *x_decl.get_value();
            collect_used(val,  used_fvars);
            used.push_back(x);
        }
        std::reverse(used.begin(), used.end());
        return m_lctx.mk_lambda(used, r);
    }

    expr visit_let(expr e) {
        buffer<expr> fvars;
        while (is_let(e)) {
            lean_assert(!has_loose_bvars(let_type(e)));
            expr new_val = visit(instantiate_rev(let_value(e), fvars.size(), fvars.data()));
            name n       = let_name(e);
            if (is_internal_name(n)) {
                if (is_join_point_name(n))
                    n = next_jp_name();
                else
                    n = next_name();
            }
            expr new_type = let_type(e);
            if (is_llnf_proj(get_app_fn(new_val))) {
                /* Ensure new_type is `_obj`. This is important for polymorphic types
                   instantiated with scalar values (e.g., `prod bool bool`). */
                new_type = mk_enf_object_type();
            }
            expr new_fvar = m_lctx.mk_local_decl(ngen(), n, new_type, new_val);
            fvars.push_back(new_fvar);
            m_fvars.push_back(new_fvar);
            e = let_body(e);
        }
        e = instantiate_rev(e, fvars.size(), fvars.data());
        lean_assert(!is_let(e));
        e = ensure_terminal(e);
        return visit(e);
    }

    expr visit_lambda(expr e) {
        buffer<expr> binding_fvars;
        while (is_lambda(e)) {
            lean_assert(!has_loose_bvars(binding_domain(e)));
            expr new_fvar = m_lctx.mk_local_decl(ngen(), next_name(), binding_domain(e), binding_info(e));
            binding_fvars.push_back(new_fvar);
            e = binding_body(e);
        }
        e = instantiate_rev(e, binding_fvars.size(), binding_fvars.data());
        unsigned saved_fvars_size = m_fvars.size();
        if (!is_let(e))
            e = ensure_terminal(e);
        e = visit(e);
        expr r = mk_let(saved_fvars_size, e);
        lean_assert(!is_lambda(r));
        return m_lctx.mk_lambda(binding_fvars, r);
    }

    expr mk_let_decl(expr const & type, expr const & e) {
        expr fvar = m_lctx.mk_local_decl(ngen(), next_name(), type, e);
        m_fvars.push_back(fvar);
        return fvar;
    }

    expr mk_sproj(expr const & major, unsigned size, unsigned num, unsigned offset) {
        return mk_app(mk_llnf_sproj(size, num, offset), major);
    }

    expr mk_fproj(expr const & major, unsigned num, unsigned offset) {
        return mk_app(mk_llnf_fproj(num, offset), major);
    }

    expr mk_uproj(expr const & major, unsigned idx) {
        return mk_app(mk_llnf_uproj(idx), major);
    }

    expr mk_sset(expr const & major, unsigned size, unsigned num, unsigned offset, expr const & v) {
        return mk_app(mk_llnf_sset(size, num, offset), major, v);
    }

    expr mk_fset(expr const & major, unsigned num, unsigned offset, expr const & v) {
        return mk_app(mk_llnf_fset(num, offset), major, v);
    }

    expr mk_f32set(expr const & major, unsigned num, unsigned offset, expr const & v) {
        return mk_app(mk_llnf_f32set(num, offset), major, v);
    }

    expr mk_uset(expr const & major, unsigned idx, expr const & v) {
        return mk_app(mk_llnf_uset(idx), major, v);
    }

    expr visit_cases(expr const & e) {
        buffer<expr> args;
        expr const & fn = get_app_args(e, args);
        lean_assert(is_constant(fn));
        name const & I_name = const_name(fn).get_prefix();
        if (is_inductive_predicate(env(), I_name))
            throw exception(sstream() << "code generation failed, inductive predicate '" << I_name << "' is not supported");
        buffer<name> cnames;
        get_constructor_names(env(), I_name, cnames);
        lean_assert(args.size() == cnames.size() + 1);
        /* Process major premise */
        expr major = visit(args[0]);
        args[0]    = major;
        expr reachable_case;
        unsigned num_reachable = 0;
        expr some_reachable;
        /* We use `is_id` to track whether this "g_cases_on"-application is of the form
           ```
           C.cases_on major (fun ..., _cnstr.0.0) ... (fun ..., _cnstr.(n-1).0)
           ```
           This kind of application reduces to `major`. This optimization is useful
           for code such as:
           ```
           @decidable.cases_on t _cnstr.0.0 _cnstr.1.0
           ```
           which reduces to `t`.

           TODO(Leo): extend `is_id` when there multiple nested cases_on applications.
           Example:
           ```
           @prod.cases_on _x_1 (λ fst snd,
             @except.cases_on fst
               (λ a, let _x_2 := except.error ◾ ◾ a in (_x_2, snd))
               (λ a, let _x_3 := except.ok ◾ ◾ a in (_x_3, snd)))
           ```
        */
        bool is_id  = true;
        // bool all_eq = true;
        /* Process minor premises */
        for (unsigned i = 0; i < cnames.size(); i++) {
            unsigned saved_fvars_size = m_fvars.size();
            expr minor           = args[i+1];
            if (minor == mk_enf_neutral()) {
                // This can happen when a branch returns a proposition
                num_reachable++;
                some_reachable = minor;
            } else {
                cnstr_info cinfo     = get_cnstr_info(cnames[i]);
                buffer<expr> fields;
                for (field_info const & info : cinfo.m_field_info) {
                    lean_assert(is_lambda(minor));
                    switch (info.m_kind) {
                    case field_info::Irrelevant:
                        fields.push_back(mk_enf_neutral());
                        break;
                    case field_info::Object:
                        fields.push_back(mk_let_decl(mk_enf_object_type(), mk_app(mk_llnf_proj(info.m_idx), major)));
                        break;
                    case field_info::USize:
                        fields.push_back(mk_let_decl(info.get_type(), mk_uproj(major, info.m_idx)));
                        break;
                    case field_info::Scalar:
                        if (info.is_float() || info.is_float32()) {
                            fields.push_back(mk_let_decl(info.get_type(), mk_fproj(major, info.m_idx, info.m_offset)));
                        } else {
                            fields.push_back(mk_let_decl(info.get_type(), mk_sproj(major, info.m_size, info.m_idx, info.m_offset)));
                        }
                        break;
                    }
                    minor = binding_body(minor);
                }
                minor          = instantiate_rev(minor, fields.size(), fields.data());
                if (!is_let(minor))
                    minor      = ensure_terminal(minor);
                minor          = visit(minor);
                if (!is_enf_unreachable(minor)) {
                    /* If `minor` is not the constructor `i`, then this "g_cases_on" application is not the identity. */
                    unsigned cidx, nusizes, ssz;
                    if (!(is_llnf_cnstr(minor, cidx, nusizes, ssz) && cidx == i && nusizes == 0 && ssz == 0)) {
                        is_id = false;
                    }
                    minor          = mk_let(saved_fvars_size, minor);
#if 0 // See comment below
                    if (num_reachable > 0 && minor != some_reachable) {
                        all_eq = false;
                    }
#endif
                    some_reachable = minor;
                    args[i+1]      = minor;
                    num_reachable++;
                } else {
                    args[i+1]      = minor;
                }
            }
        }
        if (num_reachable == 0) {
            return mk_enf_unreachable();
        } else if (is_id) {
            return major;
        /*
          We remove 1-reachable cases-expressions and all_eq reachable later.
          Reason: `insert_reset_reuse_fn` uses `cases_on` applications retrieve constructor layouts.
        */
#if 0
        } else if (num_reachable == 1) {
            return some_reachable;
        } else if (all_eq) {
            expr r = some_reachable;
            /* Flat `r` if it is a let-declaration */
            buffer<expr> fvars;
            while (is_let(r)) {
                expr val  = instantiate_rev(let_value(r), fvars.size(), fvars.data());
                expr fvar = m_lctx.mk_local_decl(ngen(), let_name(r), let_type(r), val);
                fvars.push_back(fvar);
                m_fvars.push_back(fvar);
                r = let_body(r);
            }
            return instantiate_rev(r, fvars.size(), fvars.data());
#endif
        } else {
            return mk_app(fn, args);
        }
    }

    expr visit_constructor(expr const & e) {
        buffer<expr> args;
        expr const & k = get_app_args(e, args);
        lean_assert(is_constant(k));
        if (is_extern_constant(env(), const_name(k)))
            return visit_app_default(e);
        constructor_val k_val  = env().get(const_name(k)).to_constructor_val();
        cnstr_info k_info      = get_cnstr_info(const_name(k));
        unsigned nparams       = k_val.get_nparams();
        unsigned cidx          = k_info.m_cidx;
        name const & I         = k_val.get_induct();
        if (optional<unsigned> r = ::lean::is_enum_type(env(), I)) {
            /* We use a literal for enumeration types. */
            expr x = mk_let_decl(*to_uint_type(*r), mk_lit(literal(nat(cidx))));
            return x;
        }
        buffer<expr> obj_args;
        unsigned j             = nparams;
        for (field_info const & info : k_info.m_field_info) {
            if (info.m_kind != field_info::Irrelevant)
                args[j] = visit(args[j]);

            if (info.m_kind == field_info::Object) {
                obj_args.push_back(args[j]);
            }
            j++;
        }
        expr r = mk_app(mk_llnf_cnstr(I, cidx, k_info.m_num_usizes, k_info.m_scalar_sz), obj_args);
        j = nparams;
        bool first      = true;
        for (field_info const & info : k_info.m_field_info) {
            switch (info.m_kind) {
            case field_info::Scalar:
                if (first) {
                    r = mk_let_decl(mk_enf_object_type(), r);
                }
                if (info.is_float()) {
                    r = mk_let_decl(mk_enf_object_type(), mk_fset(r, info.m_idx, info.m_offset, args[j]));
                } else if (info.is_float32()) {
                    r = mk_let_decl(mk_enf_object_type(), mk_f32set(r, info.m_idx, info.m_offset, args[j]));
                } else {
                    r = mk_let_decl(mk_enf_object_type(), mk_sset(r, info.m_size, info.m_idx, info.m_offset, args[j]));
                }
                first = false;
                break;
            case field_info::USize:
                if (first) {
                    r = mk_let_decl(mk_enf_object_type(), r);
                }
                lean_assert(j < args.size());
                r = mk_let_decl(mk_enf_object_type(), mk_uset(r, info.m_idx, args[j]));
                first = false;
                break;

            default:
                break;
            }
            j++;
        }
        return r;
    }

    expr visit_proj(expr const & e) {
        name S_name = proj_sname(e);
        inductive_val S_val = env().get(S_name).to_inductive_val();
        lean_assert(S_val.get_ncnstrs() == 1);
        name k_name = head(S_val.get_cnstrs());
        cnstr_info k_info = get_cnstr_info(k_name);
        unsigned i        = 0;
        for (field_info const & info : k_info.m_field_info) {
            switch (info.m_kind) {
            case field_info::Irrelevant:
                if (proj_idx(e) == i)
                    return mk_enf_neutral();
                break;
            case field_info::Object:
                if (proj_idx(e) == i)
                    return mk_app(mk_llnf_proj(info.m_idx), visit(proj_expr(e)));
                break;
            case field_info::USize:
                if (proj_idx(e) == i)
                    return mk_app(mk_llnf_uproj(info.m_idx), visit(proj_expr(e)));
                break;
            case field_info::Scalar:
                if (proj_idx(e) == i) {
                    if (info.is_float() || info.is_float32()) {
                        return mk_fproj(visit(proj_expr(e)), info.m_idx, info.m_offset);
                    } else {
                        return mk_sproj(visit(proj_expr(e)), info.m_size, info.m_idx, info.m_offset);
                    }
                }
                break;
            }
            i++;
        }
        lean_unreachable();
    }

    expr visit_constant(expr const & e) {
        if (is_constructor(env(), const_name(e))) {
            return visit_constructor(e);
        } else if (is_enf_neutral(e) || is_enf_unreachable(e) || is_llnf_op(e)) {
            return e;
        } else {
            unsigned arity = get_arity(const_name(e));
            if (arity == 0) {
                return e;
            } else {
                return mk_app(mk_llnf_closure(), e);
            }
        }
    }

    expr visit_app_default(expr const & e) {
        buffer<expr> args;
        expr const & fn = get_app_args(e, args);
        for (expr & arg : args)
            arg = visit(arg);
        return mk_llnf_app(fn, args);
    }

    expr visit_app(expr const & e) {
        expr const & fn = get_app_fn(e);
        if (is_cases_on_app(env(), e)) {
            return visit_cases(e);
        } else if (is_constructor_app(env(), e)) {
            return visit_constructor(e);
        } else if (is_llnf_op(fn)) {
            return e;
        } else {
            return visit_app_default(e);
        }
    }

    expr visit(expr const & e) {
        switch (e.kind()) {
        case expr_kind::App:    return visit_app(e);
        case expr_kind::Lambda: return visit_lambda(e);
        case expr_kind::Let:    return visit_let(e);
        case expr_kind::Proj:   return visit_proj(e);
        case expr_kind::Const:  return visit_constant(e);
        default:                return e;
        }
    }

public:
    to_lambda_pure_fn(elab_environment const & env):
        m_env(env), m_st(env), m_x("_x"), m_j("j") {
    }

    expr operator()(expr e) {
        if (!is_lambda(e) && !is_let(e))
            e = ensure_terminal(e);
        expr r = visit(e);
        return mk_let(0, r);
    }
};

expr get_constant_ll_type(elab_environment const & env, name const & c) {
    if (optional<expr> type = get_extern_constant_ll_type(env, c)) {
        return *type;
    } else {
        return env.get(mk_cstage2_name(c)).get_type();
    }
}

elab_environment compile_ir(elab_environment const & env, options const & opts, comp_decls const & ds) {
    buffer<comp_decl> new_ds;
    for (comp_decl const & d : ds) {
        expr new_v = to_lambda_pure_fn(env)(d.snd());
        new_ds.push_back(comp_decl(d.fst(), new_v));
    }
    return ir::compile(env, opts, new_ds);
}

void initialize_llnf() {
    g_apply     = new expr(mk_constant("_apply"));
    mark_persistent(g_apply->raw());
    g_closure   = new expr(mk_constant("_closure"));
    mark_persistent(g_closure->raw());
    g_reuse     = new name("_reuse");
    mark_persistent(g_reuse->raw());
    g_reset     = new name("_reset");
    mark_persistent(g_reset->raw());
    g_sset      = new name("_sset");
    mark_persistent(g_sset->raw());
    g_fset      = new name("_fset");
    mark_persistent(g_fset->raw());
    g_f32set      = new name("_f32set");
    mark_persistent(g_f32set->raw());
    g_uset      = new name("_uset");
    mark_persistent(g_uset->raw());
    g_proj      = new name("_proj");
    mark_persistent(g_proj->raw());
    g_sproj     = new name("_sproj");
    mark_persistent(g_sproj->raw());
    g_fproj     = new name("_sproj");
    mark_persistent(g_fproj->raw());
    g_uproj     = new name("_uproj");
    mark_persistent(g_uproj->raw());
    g_jmp       = new expr(mk_constant("_jmp"));
    mark_persistent(g_jmp->raw());
    g_box       = new name("_box");
    mark_persistent(g_box->raw());
    g_unbox     = new name("_unbox");
    mark_persistent(g_unbox->raw());
    g_inc       = new expr(mk_constant("_inc"));
    mark_persistent(g_inc->raw());
    g_dec       = new expr(mk_constant("_dec"));
    mark_persistent(g_dec->raw());
    register_trace_class({"compiler", "lambda_pure"});
}

void finalize_llnf() {
    delete g_closure;
    delete g_apply;
    delete g_reuse;
    delete g_reset;
    delete g_sset;
    delete g_fset;
    delete g_f32set;
    delete g_proj;
    delete g_sproj;
    delete g_fproj;
    delete g_uset;
    delete g_uproj;
    delete g_jmp;
    delete g_box;
    delete g_unbox;
    delete g_inc;
    delete g_dec;
}
}
