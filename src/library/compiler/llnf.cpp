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
#include "kernel/instantiate.h"
#include "kernel/for_each_fn.h"
#include "library/util.h"
#include "library/compiler/util.h"
#include "library/compiler/llnf.h"

#include "library/vm/vm.h" // TODO(Leo): delete after we add the new `builtin` management module

namespace lean {
static expr * g_apply     = nullptr;
static expr * g_closure   = nullptr;
static name * g_cnstr     = nullptr;
static name * g_reuse     = nullptr;
static name * g_reset     = nullptr;
static name * g_sset      = nullptr;
static name * g_uset      = nullptr;
static name * g_proj      = nullptr;
static name * g_sproj     = nullptr;
static name * g_uproj     = nullptr;
static expr * g_jmp       = nullptr;
static name * g_box       = nullptr;
static expr * g_unbox     = nullptr;

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

/* The `_cnstr.<cidx>.<num_usizes>.<num_bytes>` instruction constructs a constructor object with tag `cidx`, and scalar area with space for `num_usize` `usize` values + `num_bytes` bytes. */
expr mk_llnf_cnstr(unsigned cidx, unsigned num_usizes, unsigned num_bytes) { return mk_constant(name(name(name(*g_cnstr, cidx), num_usizes), num_bytes)); }
bool is_llnf_cnstr(expr const & e, unsigned & cidx, unsigned & num_usizes, unsigned & num_bytes) { return is_llnf_ternary_primitive(e, *g_cnstr, cidx, num_usizes, num_bytes); }

/* The `_reuse.<cidx>.<num_usizes>.<num_bytes>` is similar to `_cnstr.<cidx>.<num_usize>.<num_bytes>`, but it takes an extra argument: a memory cell that may be reused. */
expr mk_llnf_reuse(unsigned cidx, unsigned num_usizes, unsigned num_bytes) { return mk_constant(name(name(name(*g_reuse, cidx), num_usizes), num_bytes)); }
bool is_llnf_reuse(expr const & e, unsigned & cidx, unsigned & num_usizes, unsigned & num_bytes) { return is_llnf_ternary_primitive(e, *g_reuse, cidx, num_usizes, num_bytes); }

expr mk_llnf_reset(unsigned n) { return mk_constant(name(*g_reset, n)); }
bool is_llnf_reset(expr const & e, unsigned & n) { return is_llnf_unary_primitive(e, *g_reset, n); }

/* The `_sset.<sz>.<n>.<offset>` instruction sets a scalar value of size `sz` (in bytes) at offset `sizeof(void*)*n + offset`. The value `n` is the number of pointer and `usize` fields. */
expr mk_llnf_sset(unsigned sz, unsigned n, unsigned offset) { return mk_constant(name(name(name(*g_sset, sz), n), offset)); }
bool is_llnf_sset(expr const & e, unsigned & sz, unsigned & n, unsigned & offset) { return is_llnf_ternary_primitive(e, *g_sset, sz, n, offset); }

/* The `_uset.<n>` instruction sets a `usize` value in a constructor object at offset `sizeof(void*)*n`. */
expr mk_llnf_uset(unsigned n) { return mk_constant(name(*g_uset, n)); }
bool is_llnf_uset(expr const & e, unsigned & n) { return is_llnf_unary_primitive(e, *g_uset, n); }

/* The `_proj.<idx>` instruction retrieves an object field in a constructor object at offset `sizeof(void*)*idx` */
expr mk_llnf_proj(unsigned idx) { return mk_constant(name(*g_proj, idx)); }
bool is_llnf_proj(expr const & e, unsigned & idx) { return is_llnf_unary_primitive(e, *g_proj, idx); }

/* The `_sproj.<sz>.<n>.<offset>` instruction retrieves a scalar field of size `sz` (in bytes) in a constructor object at offset `sizeof(void*)*n + offset`. The value `n` is the number of pointer and `usize` fields. */
expr mk_llnf_sproj(unsigned sz, unsigned n, unsigned offset) { return mk_constant(name(name(name(*g_sproj, sz), n), offset)); }
bool is_llnf_sproj(expr const & e, unsigned & sz, unsigned & n, unsigned & offset) { return is_llnf_ternary_primitive(e, *g_sproj, sz, n, offset); }

/* The `_uproj.<idx>` instruction retrieves an `usize` field in a constructor ojbect at offset `sizeof(void*)*idx` */
expr mk_llnf_uproj(unsigned idx) { return mk_constant(name(*g_uproj, idx)); }
bool is_llnf_uproj(expr const & e, unsigned & idx) { return is_llnf_unary_primitive(e, *g_uproj, idx); }

/* The `_jmp` instruction is a "jump" to a join point. */
expr mk_llnf_jmp() { return *g_jmp; }
bool is_llnf_jmp(expr const & e) { return e == *g_jmp; }

/* The `_unbox` instruction converts a boxed value (type `_obj`) into an unboxed value (type `uint*` or `usize`).
   It is only used in let-declarations of the form `x : t := _ubox y`. So, we don't need a parameter in `_unbox` to
   specify the result type. */
expr mk_llnf_unbox () { return *g_unbox; }
bool is_llnf_unbox(expr const & e) { return e == *g_unbox; }

/* The `_box.<n>` instruction converts an unboxed value (type `uint*`) into a boxed value (type `_obj`).
   The parameter `n` specifies the number of bytes necessary to store the unboxed value.
   This information could be also retrieved from the type of the variable being boxed, but for simplicity,
   we store it in the instruction too.

   Remark: we use the instruction `_box.0` to box unboxed values of type `usize` into a boxed value (type `_obj`).
   We use `0` because the number of bytes necessary to store a `usize` is different in 32 and 64 bit machines. */
expr mk_llnf_box(unsigned n);
bool is_llnf_box(expr const & e, unsigned & n) { return is_llnf_unary_primitive(e, *g_box, n); }

bool is_llnf_op(expr const & e) {
    return
        is_llnf_closure(e) ||
        is_llnf_apply(e)   ||
        is_llnf_cnstr(e)   ||
        is_llnf_reuse(e)   ||
        is_llnf_reset(e)   ||
        is_llnf_sset(e)    ||
        is_llnf_uset(e)    ||
        is_llnf_proj(e)    ||
        is_llnf_sproj(e)   ||
        is_llnf_uproj(e)   ||
        is_llnf_jmp(e)     ||
        is_llnf_box(e)     ||
        is_llnf_unbox(e);
}

struct field_info {
    /* Remark: the position of a scalar value in
       a constructor object is: `sizeof(void*)*m_idx + m_offset` */
    enum kind { Irrelevant, Object, USize, Scalar };
    kind     m_kind;
    unsigned m_size;   // it is used only if `m_kind == Scalar`
    unsigned m_idx;
    unsigned m_offset; // it is used only if `m_kind == Scalar`
    expr     m_type;
    field_info():m_kind(Irrelevant), m_idx(0), m_type(mk_enf_neutral()) {}
    field_info(unsigned idx):m_kind(Object), m_idx(idx), m_type(mk_enf_object_type()) {}
    field_info(unsigned num, bool):m_kind(USize), m_idx(num), m_type(mk_constant(get_usize_name())) {}
    field_info(unsigned sz, unsigned num, unsigned offset, expr const & type):
        m_kind(Scalar), m_size(sz), m_idx(num), m_offset(offset), m_type(type) {}
    expr get_type() const { return m_type; }
    static field_info mk_irrelevant() { return field_info(); }
    static field_info mk_object(unsigned idx) { return field_info(idx); }
    static field_info mk_usize(unsigned n) { return field_info(n, true); }
    static field_info mk_scalar(unsigned sz, unsigned offset, expr const & type) { return field_info(sz, 0, offset, type); }
};

struct cnstr_info {
    unsigned         m_cidx;
    list<field_info> m_field_info;
    unsigned         m_num_objs{0};
    unsigned         m_num_usizes{0};
    unsigned         m_scalar_sz{0};
    cnstr_info(unsigned cidx, list<field_info> const & finfo):
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
};

std::vector<pair<name, unsigned>> * g_builtin_scalar_size = nullptr;

optional<unsigned> is_builtin_scalar(expr const & type) {
    if (!is_constant(type)) return optional<unsigned>();
    for (pair<name, unsigned> const & p : *g_builtin_scalar_size) {
        if (const_name(type) == p.first) {
            return optional<unsigned>(p.second);
        }
    }
    return optional<unsigned>();
}

class to_llnf_fn {
    typedef std::unordered_set<name, name_hash> name_set;
    typedef std::unordered_map<name, cnstr_info, name_hash> cnstr_info_cache;
    typedef std::unordered_map<name, optional<unsigned>, name_hash> enum_cache;
    type_checker::state   m_st;
    bool                  m_unboxed;
    local_ctx             m_lctx;
    buffer<expr>          m_fvars;
    name                  m_x;
    name                  m_j;
    unsigned              m_next_idx{1};
    unsigned              m_next_jp_idx{1};
    cnstr_info_cache      m_cnstr_info_cache;
    enum_cache            m_enum_cache;

    environment const & env() const { return m_st.env(); }

    name_generator & ngen() { return m_st.ngen(); }

    optional<unsigned> is_enum_type(expr const & type) {
        expr const & I = get_app_fn(type);
        if (!is_constant(I)) return optional<unsigned>();
        auto it = m_enum_cache.find(const_name(I));
        if (it != m_enum_cache.end())
            return it->second;
        optional<unsigned> r = ::lean::is_enum_type(env(), const_name(I));
        m_enum_cache.insert(mk_pair(const_name(I), r));
        return r;
    }

    void get_cnstr_info_core(name const & n, buffer<field_info> & result) {
        constant_info info  = env().get(n);
        lean_assert(info.is_constructor());
        constructor_val val = info.to_constructor_val();
        expr type           = info.get_type();
        name I_name         = val.get_induct();
        unsigned nparams    = val.get_nparams();
        local_ctx lctx;
        buffer<expr> telescope;
        unsigned next_object = 0;
        unsigned next_usize  = 0;
        unsigned next_offset = 0;
        to_telescope(env(), lctx, ngen(), type, telescope);
        lean_assert(telescope.size() >= nparams);
        for (unsigned i = nparams; i < telescope.size(); i++) {
            expr ftype = lctx.get_type(telescope[i]);
            if (is_irrelevant_type(m_st, lctx, ftype)) {
                result.push_back(field_info::mk_irrelevant());
            } else if (m_unboxed) {
                type_checker tc(m_st, lctx);
                ftype = tc.whnf(ftype);
                if (is_constant(ftype, get_usize_name())) {
                    result.push_back(field_info::mk_usize(next_usize));
                    next_usize++;
                } else if (optional<unsigned> sz = is_builtin_scalar(ftype)) {
                    result.push_back(field_info::mk_scalar(*sz, next_offset, ftype));
                    next_offset += *sz;
                } else if (optional<unsigned> sz = is_enum_type(ftype)) {
                    optional<expr> uint = to_uint_type(*sz);
                    if (!uint) throw exception("code generation failed, enumeration type is too big");
                    result.push_back(field_info::mk_scalar(*sz, next_offset, *uint));
                    next_offset += *sz;
                } else {
                    result.push_back(field_info::mk_object(next_object));
                    next_object++;
                }
            } else {
                result.push_back(field_info::mk_object(next_object));
                next_object++;
            }
        }
        unsigned nobjs     = next_object;
        unsigned nusizes   = next_usize;
        if (m_unboxed) {
            /* Remark:
               - usize fields are stored after object fields.
               - regular scalar fields are stored after object and usize fields */
            for (field_info & info : result) {
                switch (info.m_kind) {
                case field_info::Scalar:
                    info.m_offset += (nobjs + nusizes) * sizeof(void*);
                    break;
                case field_info::USize:
                    info.m_offset += nobjs * sizeof(void*);
                    break;
                default:
                    break;
                }
            }
        }
    }

    unsigned get_arity(name const & n) const {
        /* First, try to infer arity from `_cstage2` auxiliary definition. */
        name c = mk_cstage2_name(n);
        optional<constant_info> info = env().find(c);
        if (info && info->is_definition()) {
            return get_num_nested_lambdas(info->get_value());
        }

        /* If `_cstage2` declaration is not available, then use the VM decl.

           TODO(Leo): add new builtin management module. */
        optional<vm_decl> decl = get_vm_decl(env(), n);
        if (!decl) throw exception(sstream() << "code generation failed, unknown '" << n << "'");
        return decl->get_arity();
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
        buffer<field_info> finfos;
        get_cnstr_info_core(n, finfos);
        unsigned cidx      = get_constructor_idx(env(), n);
        cnstr_info r(cidx, to_list(finfos));
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
        name_set used_fvars;
        collect_used(r, used_fvars);
        while (m_fvars.size() > saved_fvars_size) {
            expr x = m_fvars.back();
            m_fvars.pop_back();
            if (used_fvars.find(fvar_name(x)) == used_fvars.end()) {
                continue;
            }
            local_decl x_decl = m_lctx.get_local_decl(x);
            expr val          = *x_decl.get_value();
            if (used.empty() && r == x) {
                /* `let x := v in x` ==> `v` */
                r = val;
                collect_used(r, used_fvars);
                continue;
            }
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
            expr new_fvar = m_lctx.mk_local_decl(ngen(), n, let_type(e), new_val);
            fvars.push_back(new_fvar);
            m_fvars.push_back(new_fvar);
            e = let_body(e);
        }
        return visit(instantiate_rev(e, fvars.size(), fvars.data()));
    }

    expr visit_lambda(expr e) {
        buffer<expr> binding_fvars;
        while (is_lambda(e)) {
            lean_assert(!has_loose_bvars(binding_domain(e)));
            expr new_fvar = m_lctx.mk_local_decl(ngen(), binding_name(e), binding_domain(e), binding_info(e));
            binding_fvars.push_back(new_fvar);
            e = binding_body(e);
        }
        e = instantiate_rev(e, binding_fvars.size(), binding_fvars.data());
        unsigned saved_fvars_size = m_fvars.size();
        expr r = mk_let(saved_fvars_size, visit(e));
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

    expr mk_uproj(expr const & major, unsigned idx) {
        return mk_app(mk_llnf_uproj(idx), major);
    }

    expr mk_sset(expr const & major, unsigned size, unsigned num, unsigned offset, expr const & v) {
        return mk_app(mk_llnf_sset(size, num, offset), major, v);
    }

    expr mk_uset(expr const & major, unsigned idx, expr const & v) {
        return mk_app(mk_llnf_uset(idx), major, v);
    }

    expr mk_reset(expr const & major, unsigned idx) {
        return mk_app(mk_llnf_reset(idx), major);
    }

    /* Auxiliary functor for replacing constructor applications with update operations. */
    class replace_cnstr_fn {
        to_llnf_fn &         m_owner;
        name const &         m_I_name;
        expr const &         m_major;
        cnstr_info const &   m_cinfo;
        /* `m_major` may be replaced/reused many times in different branches, but we
           only have to reset fields once. */
        bool                 m_reset{false};
        expr                 m_major_after_reset;
        bool                 m_replaced{false};

        environment const & env() { return m_owner.env(); }

        expr find(expr const & e) const {
            if (is_fvar(e)) {
                if (optional<local_decl> decl = m_owner.m_lctx.find_local_decl(e)) {
                    optional<expr> v = decl->get_value();
                    if (v) return find(*v);
                }
            } else if (is_mdata(e)) {
                return find(mdata_expr(e));
            }
            return e;
        }

        /* Return true if `a` is of the form `_sproj.<sz>.<num>.<offset> e` */
        bool is_sproj_of(expr a, expr const & e, unsigned sz, unsigned num, unsigned offset) {
            a = find(a);
            if (!is_app(a) || app_arg(a) != e) return false;
            unsigned a_sz, a_num, a_offset;
            return is_llnf_sproj(a, a_sz, a_num, a_offset) && a_sz == sz && a_num == num && a_offset == offset;
        }

        /* Return true if `a` is of the form `_uproj.<idx> e` */
        bool is_uproj_of(expr a, expr const & e, unsigned idx) {
            a = find(a);
            if (!is_app(a) || app_arg(a) != e) return false;
            unsigned a_idx;
            return is_llnf_uproj(a, a_idx) && a_idx == idx;
        }

        expr visit_constructor(expr const & e) {
            buffer<expr> args;
            expr const & k = get_app_args(e, args);
            lean_assert(is_constant(k));
            if (is_runtime_builtin_cnstr(const_name(k))) {
                /* Optimization is not applicable to runtime builtin constructors. */
                return e;
            }
            constructor_val k_val  = env().get(const_name(k)).to_constructor_val();
            if (k_val.get_induct() != m_I_name) {
                /* Heuristic: we don't want to reuse cells from different types even when they are compatible
                   because it produces counterintuitive behavior. Here is an example:
                   ```
                   @list.cases_on a
                     (@prod.cases_on a_1 (λ fst snd, (punit.star, snd)))
                     (λ a_hd a_tl,
                         @prod.cases_on a_1
                           (λ fst snd,
                              let _x_1 := nat.add snd a_hd,
                                  _x_2 := (punit.star, _x_1)
                              in list.mmap'._main._at.accum._spec_1 a_tl _x_2))
                   ```
                   Without this heuristic, we will try ton construct `(punit.star, _x_1)` re-using `a` instead of `a_1`. */
                return e;
            }
            cnstr_info k_info      = m_owner.get_cnstr_info(const_name(k));
            if (k_info.m_num_objs  != m_cinfo.m_num_objs || k_info.m_num_usizes != m_cinfo.m_num_usizes || k_info.m_scalar_sz != m_cinfo.m_scalar_sz) {
                /* This constructor is not compatible with major premise */
                return e;
            }
            unsigned nparams       = k_val.get_nparams();
            if (!m_reset) {
                m_major_after_reset = m_owner.mk_reset(m_major, k_info.m_num_objs);
                m_major_after_reset = m_owner.mk_let_decl(mk_enf_object_type(), m_major_after_reset);
                m_reset             = true;
            }
            expr r = m_major_after_reset;
            /* Remark: note that we do not create let-declarations here for the following updates.
               We will flatten them later when we visit the minor premise. */
            buffer<expr> obj_args;
            unsigned j      = nparams;
            for (field_info const & info : k_info.m_field_info) {
                if (info.m_kind == field_info::Object) {
                    obj_args.push_back(args[j]);
                }
                j++;
            }
            r = mk_app(mk_app(mk_llnf_reuse(k_info.m_cidx, k_info.m_num_usizes, k_info.m_scalar_sz), r), obj_args);
            unsigned uidx   = 0;
            unsigned offset = 0;
            for (field_info const & info : k_info.m_field_info) {
                switch (info.m_kind) {
                case field_info::Scalar:
                    if (!is_sproj_of(args[j], m_major, info.m_size, k_info.m_num_objs + k_info.m_num_usizes, offset)) {
                        r = m_owner.mk_sset(r, info.m_size, (k_info.m_num_objs + k_info.m_num_usizes), offset, args[j]);
                    }
                    offset += info.m_size;
                    break;
                case field_info::USize:
                    if (!is_uproj_of(args[j], m_major, (k_info.m_num_objs + uidx))) {
                        r = m_owner.mk_uset(r, k_info.m_num_objs + uidx, args[j]);
                    }
                    uidx++;
                    break;
                default:
                    break;
                }
            }
            m_replaced = true;
            return r;
        }

        expr visit_app(expr const & e) {
            if (is_constructor_app(env(), e)) {
                return visit_constructor(e);
            } else if (is_cases_on_app(env(), e)) {
                lean_assert(!m_replaced);
                buffer<expr> args;
                expr const & fn   = get_app_args(e, args);
                bool modified     = false;
                bool new_replaced = false;
                for (expr & arg : args) {
                    /* `m_major` can be reused in each branch. */
                    m_replaced   = false;
                    expr new_arg = visit(arg);
                    if (m_replaced)
                        new_replaced = true;
                    if (!is_eqp(arg, new_arg))
                        modified = true;
                    arg = new_arg;
                }
                /* We assume that `m_major` has been reused IF it was reused in one of the branches. */
                m_replaced = new_replaced;
                return modified ? mk_app(fn, args) : e;
            } else {
                return e;
            }
        }

        expr visit_lambda(expr const & e) {
            expr new_body = visit(binding_body(e));
            return update_binding(e, binding_domain(e), new_body);
        }

        expr visit_let(expr const & e) {
            expr new_value = visit(let_value(e));
            expr new_body  = visit(let_body(e));
            return update_let(e, let_type(e), new_value, new_body);
        }

        expr visit(expr const & e) {
            if (m_replaced) return e;
            switch (e.kind()) {
            case expr_kind::App:    return visit_app(e);
            case expr_kind::Let:    return visit_let(e);
            case expr_kind::Lambda: return visit_lambda(e);
            default:                return e;
            }
        }

    public:
        replace_cnstr_fn(to_llnf_fn & owner, name const & I_name, expr const & major, cnstr_info const & cinfo):
            m_owner(owner), m_I_name(I_name), m_major(major), m_cinfo(cinfo) {}
        expr operator()(expr const & e) { return visit(e); }
    };

    expr try_update_opt(name const & I_name, expr const & minor, expr const & major, cnstr_info const & cinfo) {
        if (cinfo.m_num_objs == 0 && cinfo.m_num_usizes == 0 && cinfo.m_scalar_sz == 0) return minor;
        if (!is_fvar(major)) return minor;
        if (has_fvar(minor, major)) return minor;
        return replace_cnstr_fn(*this, I_name, major, cinfo)(minor);
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
        /* We use `is_id` to track whether this "cases_on"-application is of the form
           ```
           C.cases_on major (fun ..., _cnstr.0.0) ... (fun ..., _cnstr.(n-1).0)
           ```
           This kind of application reduces to `major`. This optimization is useful
           for code such as:
           ```
           @decidable.cases_on t _cnstr.0.0 _cnstr.1.0
           ```
           which reduces to `t`. */
        bool is_id  = true;
        /* We use `all_eq` to track whether all reachable cases are equal or not. */
        bool all_eq = true;
        /* Process minor premises */
        for (unsigned i = 0; i < cnames.size(); i++) {
            unsigned saved_fvars_size = m_fvars.size();
            expr minor           = args[i+1];
            cnstr_info cinfo     = get_cnstr_info(cnames[i]);
            unsigned next_idx    = 0;
            unsigned next_usize  = 0;
            unsigned next_offset = 0;
            buffer<expr> fields;
            for (field_info const & info : cinfo.m_field_info) {
                lean_assert(is_lambda(minor));
                switch (info.m_kind) {
                case field_info::Irrelevant:
                    fields.push_back(mk_enf_neutral());
                    break;
                case field_info::Object:
                    fields.push_back(mk_let_decl(mk_enf_object_type(), mk_app(mk_llnf_proj(next_idx), major)));
                    next_idx++;
                    break;
                case field_info::USize:
                    fields.push_back(mk_let_decl(info.get_type(), mk_uproj(major, (cinfo.m_num_objs + next_usize))));
                    next_usize++;
                    break;
                case field_info::Scalar:
                    fields.push_back(mk_let_decl(info.get_type(), mk_sproj(major, info.m_size, (cinfo.m_num_objs + cinfo.m_num_usizes), next_offset)));
                    next_offset += info.m_size;
                    break;
                }
                minor = binding_body(minor);
            }
            minor     = instantiate_rev(minor, fields.size(), fields.data());
            minor     = try_update_opt(I_name, minor, major, cinfo);
            minor     = visit(minor);
            if (!is_enf_unreachable(minor)) {
                /* If `minor` is not the constructor `i`, then this "cases_on" application is not the identity. */
                unsigned cidx, nusizes, ssz;
                if (!(is_llnf_cnstr(minor, cidx, nusizes, ssz) && cidx == i && nusizes == 0 && ssz == 0)) {
                    is_id = false;
                }
                minor          = mk_let(saved_fvars_size, minor);
                if (num_reachable > 0 && minor != some_reachable) {
                    all_eq = false;
                }
                some_reachable = minor;
                args[i+1]      = minor;
                num_reachable++;
            } else {
                args[i+1]      = minor;
            }
        }
        if (num_reachable == 0) {
            return mk_enf_unreachable();
        } else if (is_id) {
            return major;
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
        } else {
            return mk_app(fn, args);
        }
    }

    expr visit_constructor(expr const & e) {
        buffer<expr> args;
        expr const & k = get_app_args(e, args);
        lean_assert(is_constant(k));
        if (is_runtime_builtin_cnstr(const_name(k)))
            return visit_app_default(e);
        constructor_val k_val  = env().get(const_name(k)).to_constructor_val();
        cnstr_info k_info      = get_cnstr_info(const_name(k));
        unsigned nparams       = k_val.get_nparams();
        unsigned cidx          = k_info.m_cidx;
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
        expr r = mk_app(mk_llnf_cnstr(cidx, k_info.m_num_usizes, k_info.m_scalar_sz), obj_args);
        j = nparams;
        unsigned offset = 0;
        unsigned uidx   = 0;
        bool first      = true;
        for (field_info const & info : k_info.m_field_info) {
            switch (info.m_kind) {
            case field_info::Scalar:
                if (first && obj_args.size() > 0) {
                    r = mk_let_decl(mk_enf_object_type(), r);
                }
                r = mk_let_decl(info.get_type(), mk_sset(r, info.m_size, (k_info.m_num_objs + k_info.m_num_usizes), offset, args[j]));
                offset += info.m_size;
                first = false;
                break;
            case field_info::USize:
                if (first && obj_args.size() > 0) {
                    r = mk_let_decl(mk_enf_object_type(), r);
                }
                r = mk_let_decl(info.get_type(), mk_uset(r, k_info.m_num_objs + uidx, args[j]));
                uidx++;
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
        unsigned idx      = 0;
        unsigned offset   = 0;
        unsigned uidx     = 0;
        unsigned i        = 0;
        for (field_info const & info : k_info.m_field_info) {
            switch (info.m_kind) {
            case field_info::Irrelevant:
                if (proj_idx(e) == i)
                    return mk_enf_neutral();
                break;
            case field_info::Object:
                if (proj_idx(e) == i)
                    return mk_app(mk_llnf_proj(idx), visit(proj_expr(e)));
                idx++;
                break;
            case field_info::USize:
                if (proj_idx(e) == i)
                    return mk_app(mk_llnf_uproj(k_info.m_num_objs + uidx), visit(proj_expr(e)));
                uidx++;
                break;
            case field_info::Scalar:
                if (proj_idx(e) == i)
                    return mk_sproj(visit(proj_expr(e)), info.m_size, (k_info.m_num_objs + k_info.m_num_usizes), offset);
                offset += info.m_size;
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

    expr flat_app(expr const & e) {
        buffer<expr> args;
        expr const & fn = get_app_args(e, args);
        for (expr & arg : args) {
            arg = visit(arg);
            if (!is_lcnf_atom(arg)) {
                arg = mk_let_decl(mk_enf_object_type(), arg);
            }
        }
        return mk_app(fn, args);
    }

    expr visit_app(expr const & e) {
        expr const & fn = get_app_fn(e);
        if (is_cases_on_app(env(), e)) {
            return visit_cases(e);
        } else if (is_constructor_app(env(), e)) {
            return visit_constructor(e);
        } else if (is_llnf_sset(fn) || is_llnf_uset(fn) || is_llnf_reuse(fn)) {
            return flat_app(e);
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
    to_llnf_fn(environment const & env, bool unboxed):
        m_st(env), m_unboxed(unboxed), m_x("_x"), m_j("j") {
    }

    expr operator()(expr const & e) {
        expr r = visit(e);
        return mk_let(0, r);
    }
};

/* Extension used to store data the name of the "boxed" version of functions that
   take unboxed values.
   TODO(Leo): use the to be implemented new module system. */
struct boxed_functions_ext : public environment_extension {
    typedef name_map<name> boxed_map;
    boxed_map m_boxed_map;
};

struct boxed_functions_reg {
    unsigned m_ext_id;
    boxed_functions_reg() { m_ext_id = environment::register_extension(std::make_shared<boxed_functions_ext>()); }
};

static boxed_functions_reg * g_ext = nullptr;
static boxed_functions_ext const & get_extension(environment const & env) {
    return static_cast<boxed_functions_ext const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, boxed_functions_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<boxed_functions_ext>(ext));
}

/* Insert explicit boxing/unboxing instructions. */
class explicit_boxing_fn {
    environment       m_env;
    name_generator    m_ngen;
    local_ctx         m_lctx;
    buffer<expr>      m_fvars;
    name              m_x;
    unsigned          m_next_idx{1};
    buffer<comp_decl> m_new_decls;

    environment const & env() const { return m_env; }

    name_generator & ngen() { return m_ngen; }

    name next_name() {
        name r = m_x.append_after(m_next_idx);
        m_next_idx++;
        return r;
    }

    expr mk_let_decl(expr const & type, expr const & e) {
        expr fvar = m_lctx.mk_local_decl(ngen(), next_name(), type, e);
        m_fvars.push_back(fvar);
        return fvar;
    }

    expr mk_let(unsigned saved_fvars_size, expr r) {
        lean_assert(saved_fvars_size <= m_fvars.size());
        if (saved_fvars_size == m_fvars.size())
            return r;
        r = m_lctx.mk_lambda(m_fvars.size() - saved_fvars_size, m_fvars.data() + saved_fvars_size, r);
        m_fvars.shrink(saved_fvars_size);
        return r;
    }

    expr visit_let(expr e) {
        buffer<expr> fvars;
        while (is_let(e)) {
            lean_assert(!has_loose_bvars(let_type(e)));
            expr new_val = visit(instantiate_rev(let_value(e), fvars.size(), fvars.data()));
            name n       = let_name(e);
            if (is_internal_name(n) && !is_join_point_name(n)) {
                n = next_name();
            }
            expr new_fvar = m_lctx.mk_local_decl(ngen(), n, let_type(e), new_val);
            fvars.push_back(new_fvar);
            m_fvars.push_back(new_fvar);
            e = let_body(e);
        }
        return visit(instantiate_rev(e, fvars.size(), fvars.data()));
    }

    expr visit_lambda(expr e) {
        buffer<expr> binding_fvars;
        while (is_lambda(e)) {
            lean_assert(!has_loose_bvars(binding_domain(e)));
            expr new_fvar = m_lctx.mk_local_decl(ngen(), binding_name(e), binding_domain(e), binding_info(e));
            binding_fvars.push_back(new_fvar);
            e = binding_body(e);
        }
        e = instantiate_rev(e, binding_fvars.size(), binding_fvars.data());
        unsigned saved_fvars_size = m_fvars.size();
        expr r = mk_let(saved_fvars_size, visit(e));
        lean_assert(!is_lambda(r));
        return m_lctx.mk_lambda(binding_fvars, r);
    }

    expr visit_app(expr const & e) {
        // TODO(Leo):
        return e;
    }

    expr visit(expr const & e) {
        switch (e.kind()) {
        case expr_kind::App:    return visit_app(e);
        case expr_kind::Lambda: return visit_lambda(e);
        case expr_kind::Let:    return visit_let(e);
        default:                return e;
        }
    }

public:
    explicit_boxing_fn(environment const & env):
        m_env(env), m_x("_x") {}

    pair<environment, comp_decls> operator()(comp_decl const & d) {
        expr new_v = visit(d.snd());
        new_v = mk_let(0, new_v);
        comp_decls new_ds(comp_decl(d.fst(), new_v), comp_decls(m_new_decls));
        return mk_pair(m_env, new_ds);
    }
};

pair<environment, comp_decls> to_llnf(environment const & env, comp_decl const & d, bool unboxed) {
    comp_decl new_d(d.fst(), to_llnf_fn(env, unboxed)(d.snd()));
    if (unboxed)
        return explicit_boxing_fn(env)(new_d);
    else
        return mk_pair(env, comp_decls(new_d));
}

pair<environment, comp_decls> to_llnf(environment const & env, comp_decls const & ds, bool unboxed) {
    environment new_env = env;
    comp_decls r;
    for (comp_decl const & d : ds) {
        comp_decls new_ds;
        std::tie(new_env, new_ds) = to_llnf(new_env, d, unboxed);
        r = append(r, new_ds);
    }
    return mk_pair(new_env, r);
}

void initialize_llnf() {
    g_apply     = new expr(mk_constant("_apply"));
    g_closure   = new expr(mk_constant("_closure"));
    g_cnstr     = new name("_cnstr");
    g_reuse     = new name("_reuse");
    g_reset     = new name("_reset");
    g_sset      = new name("_sset");
    g_uset      = new name("_uset");
    g_proj      = new name("_proj");
    g_sproj     = new name("_sproj");
    g_uproj     = new name("_uproj");
    g_jmp       = new expr(mk_constant("_jmp"));
    g_box       = new name("_box");
    g_unbox     = new expr(mk_constant("_unbox"));
    g_builtin_scalar_size = new std::vector<pair<name, unsigned>>();
    g_builtin_scalar_size->emplace_back(get_uint8_name(),  1);
    g_builtin_scalar_size->emplace_back(get_uint16_name(), 2);
    g_builtin_scalar_size->emplace_back(get_uint32_name(), 4);
    g_builtin_scalar_size->emplace_back(get_uint64_name(), 8);
    g_ext       = new boxed_functions_reg();
}

void finalize_llnf() {
    delete g_closure;
    delete g_apply;
    delete g_cnstr;
    delete g_reuse;
    delete g_reset;
    delete g_sset;
    delete g_proj;
    delete g_sproj;
    delete g_uset;
    delete g_uproj;
    delete g_jmp;
    delete g_box;
    delete g_unbox;
    delete g_ext;
}
}
