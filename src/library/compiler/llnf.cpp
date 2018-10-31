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

namespace lean {
static name * g_cnstr     = nullptr;
static name * g_reuse     = nullptr;
static name * g_reset     = nullptr;
static name * g_updt      = nullptr;
static name * g_updt_cidx = nullptr;
static name * g_updt_u8   = nullptr;
static name * g_updt_u16  = nullptr;
static name * g_updt_u32  = nullptr;
static name * g_updt_u64  = nullptr;
static name * g_proj      = nullptr;
static name * g_proj_u8   = nullptr;
static name * g_proj_u16  = nullptr;
static name * g_proj_u32  = nullptr;
static name * g_proj_u64  = nullptr;

static bool is_llnf_unary_primitive(expr const & e, name const & prefix, unsigned & i) {
    if (!is_constant(e)) return false;
    name const & n = const_name(e);
    if (!is_internal_name(n) || n.is_atomic() || !n.is_numeral() || n.get_prefix() != prefix) return false;
    i = n.get_numeral().get_small_value();
    return true;
}

static bool is_llnf_binary_primitive(expr const & e, name const & prefix, unsigned & i1, unsigned & i2) {
    if (!is_constant(e)) return false;
    name const & n = const_name(e);
    if (!is_internal_name(n) || n.is_atomic() || !n.is_numeral()) return false;
    i2 = n.get_numeral().get_small_value();
    name const & p = n.get_prefix();
    if (p.is_atomic() || !p.is_numeral() || p.get_prefix() != prefix) return false;
    i1 = p.get_numeral().get_small_value();
    return true;
}

expr mk_llnf_cnstr(unsigned cidx, unsigned scalar_sz) { return mk_constant(name(name(*g_cnstr, cidx), scalar_sz)); }
bool is_llnf_cnstr(expr const & e, unsigned & cidx, unsigned & ssz) { return is_llnf_binary_primitive(e, *g_cnstr, cidx, ssz); }

expr mk_llnf_reuse(unsigned cidx, unsigned scalar_sz) { return mk_constant(name(name(*g_reuse, cidx), scalar_sz)); }
bool is_llnf_reuse(expr const & e, unsigned & cidx, unsigned & ssz) { return is_llnf_binary_primitive(e, *g_reuse, cidx, ssz); }

expr mk_llnf_reset(unsigned n) { return mk_constant(name(*g_reset, n)); }
bool is_llnf_reset(expr const & e, unsigned & n) { return is_llnf_unary_primitive(e, *g_reset, n); }

expr mk_llnf_updt_u8(unsigned offset) { return mk_constant(name(*g_updt_u8, offset)); }
bool is_llnf_updt_u8(expr const & e, unsigned & offset) { return is_llnf_unary_primitive(e, *g_updt_u8, offset); }

expr mk_llnf_updt_u16(unsigned offset) { return mk_constant(name(*g_updt_u16, offset)); }
bool is_llnf_updt_u16(expr const & e, unsigned & offset) { return is_llnf_unary_primitive(e, *g_updt_u16, offset); }

expr mk_llnf_updt_u32(unsigned offset) { return mk_constant(name(*g_updt_u32, offset)); }
bool is_llnf_updt_u32(expr const & e, unsigned & offset) { return is_llnf_unary_primitive(e, *g_updt_u32, offset); }

expr mk_llnf_updt_u64(unsigned offset) { return mk_constant(name(*g_updt_u64, offset)); }
bool is_llnf_updt_u64(expr const & e, unsigned & offset) { return is_llnf_unary_primitive(e, *g_updt_u64, offset); }

expr mk_llnf_proj(unsigned idx) { return mk_constant(name(*g_proj, idx)); }
bool is_llnf_proj(expr const & e, unsigned & idx) { return is_llnf_unary_primitive(e, *g_proj, idx); }

expr mk_llnf_proj_u8(unsigned offset) { return mk_constant(name(*g_proj_u8, offset)); }
bool is_llnf_proj_u8(expr const & e, unsigned & offset) { return is_llnf_unary_primitive(e, *g_proj_u8, offset); }

expr mk_llnf_proj_u16(unsigned offset) { return mk_constant(name(*g_proj_u16, offset)); }
bool is_llnf_proj_u16(expr const & e, unsigned & offset) { return is_llnf_unary_primitive(e, *g_proj_u16, offset); }

expr mk_llnf_proj_u32(unsigned offset) { return mk_constant(name(*g_proj_u32, offset)); }
bool is_llnf_proj_u32(expr const & e, unsigned & offset) { return is_llnf_unary_primitive(e, *g_proj_u32, offset); }

expr mk_llnf_proj_u64(unsigned offset) { return mk_constant(name(*g_proj_u64, offset)); }
bool is_llnf_proj_u64(expr const & e, unsigned & offset) { return is_llnf_unary_primitive(e, *g_proj_u64, offset); }

[[ noreturn ]] static void throw_unsupported_field_size() {
    throw exception("code generation failed, unsupported field size");
}

struct field_info {
    enum kind { Irrelevant, Object, Scalar };
    kind     m_kind;
    union {
        unsigned m_idx;
        struct {
            unsigned m_offset;
            unsigned m_size;
        };
    };
    field_info():m_kind(Irrelevant), m_idx(0) {}
    field_info(unsigned idx):m_kind(Object), m_idx(idx) {}
    field_info(unsigned offset, unsigned sz):m_kind(Scalar), m_offset(offset), m_size(sz) {}
    expr get_type() const {
        if (m_kind == Scalar) {
            switch (m_size) {
            case 1: return mk_constant(get_uint8_name());
            case 2: return mk_constant(get_uint16_name());
            case 4: return mk_constant(get_uint32_name());
            case 8: return mk_constant(get_uint64_name());
            default: throw_unsupported_field_size();
            }
        } else {
            return mk_enf_object_type();
        }
    }
};

struct cnstr_info {
    unsigned         m_cidx;
    list<field_info> m_field_info;
    unsigned         m_num_objs;
    unsigned         m_scalar_sz;
    cnstr_info(unsigned cidx, list<field_info> const & finfo):
        m_cidx(cidx), m_field_info(finfo), m_num_objs(0), m_scalar_sz(0) {
        for (field_info const & info : finfo) {
            if (info.m_kind == field_info::Object)
                m_num_objs++;
            else if (info.m_kind == field_info::Scalar)
                m_scalar_sz += info.m_size;
        }
    }

    unsigned get_num_relevant() const {
        unsigned r = 0;
        for (field_info const & info : m_field_info) {
            if (info.m_kind != field_info::Irrelevant)
                r++;
        }
        return r;
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

    environment const & env() { return m_st.env(); }

    name_generator & ngen() { return m_st.ngen(); }

    optional<unsigned> is_enum_type_core(name const & I) {
        constant_info info  = env().get(I);
        if (!info.is_inductive()) return optional<unsigned>();
        unsigned n = 0;
        for (name const & c : info.to_inductive_val().get_cnstrs()) {
            if (is_pi(env().get(c).get_type()))
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

    optional<unsigned> is_enum_type(expr const & type) {
        expr const & I = get_app_fn(type);
        if (!is_constant(I)) return optional<unsigned>();
        auto it = m_enum_cache.find(const_name(I));
        if (it != m_enum_cache.end())
            return it->second;
        optional<unsigned> r = is_enum_type_core(const_name(I));
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
        unsigned next_idx = 0;
        unsigned next_offset = 0;
        to_telescope(env(), lctx, ngen(), type, telescope);
        lean_assert(telescope.size() >= nparams);
        for (unsigned i = nparams; i < telescope.size(); i++) {
            expr ftype = lctx.get_type(telescope[i]);
            if (is_irrelevant_type(m_st, lctx, ftype)) {
                result.push_back(field_info());
            } else if (m_unboxed) {
                type_checker tc(m_st, lctx);
                ftype = whnf_upto_runtime_type(tc, ftype);
                if (optional<unsigned> sz = is_builtin_scalar(ftype)) {
                    result.push_back(field_info(next_offset, *sz));
                    next_offset += *sz;
                } else if (optional<unsigned> sz = is_enum_type(ftype)) {
                    result.push_back(field_info(next_offset, *sz));
                    next_offset += *sz;
                } else {
                    result.push_back(field_info(next_idx));
                    next_idx++;
                }
            } else {
                result.push_back(field_info(next_idx));
                next_idx++;
            }
        }
        unsigned nobjs     = next_idx;
        if (m_unboxed) {
            /* Remark: scalar data is stored after object pointers */
            for (field_info & info : result) {
                if (info.m_kind == field_info::Scalar) {
                    info.m_offset += nobjs * sizeof(void*);
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
            expr new_val  = visit(instantiate_rev(let_value(e), fvars.size(), fvars.data()));
            if (is_lcnf_atom(new_val)) {
                fvars.push_back(new_val);
            } else {
                name n = let_name(e);
                if (is_internal_name(n)) {
                    if (is_join_point_name(n))
                        n = next_jp_name();
                    else
                        n = next_name();
                }
                expr new_fvar = m_lctx.mk_local_decl(ngen(), n, let_type(e), new_val);
                fvars.push_back(new_fvar);
                m_fvars.push_back(new_fvar);
            }
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

    expr mk_scalar_proj(expr const & major, unsigned size, unsigned offset) {
        switch (size) {
        case 1:
            return mk_app(mk_llnf_proj_u8(offset), major);
        case 2:
            return mk_app(mk_llnf_proj_u16(offset), major);
        case 4:
            return mk_app(mk_llnf_proj_u32(offset), major);
        case 8:
            return mk_app(mk_llnf_proj_u64(offset), major);
        default:
            throw_unsupported_field_size();
        }
    }

    expr mk_scalar_updt(expr const & major, unsigned size, unsigned offset, expr const & v) {
        switch (size) {
        case 1:
            return mk_app(mk_llnf_updt_u8(offset), major, v);
        case 2:
            return mk_app(mk_llnf_updt_u16(offset), major, v);
        case 4:
            return mk_app(mk_llnf_updt_u32(offset), major, v);
        case 8:
            return mk_app(mk_llnf_updt_u64(offset), major, v);
        default:
            throw_unsupported_field_size();
        }
    }

    expr mk_reset(expr const & major, unsigned idx) {
        return mk_app(mk_llnf_reset(idx), major);
    }

    bool is_reuse_app(expr const & e) {
        unsigned i, s;
        return is_llnf_reuse(get_app_fn(e), i, s) && get_app_num_args(e) == 2;
    }

    bool is_updt_scalar(expr const & e) {
        unsigned x;
        return
            is_llnf_updt_u8(e, x) ||
            is_llnf_updt_u16(e, x) ||
            is_llnf_updt_u32(e, x) ||
            is_llnf_updt_u64(e, x);
    }

    bool is_updt_scalar_app(expr const & e) {
        return is_updt_scalar(get_app_fn(e)) && get_app_num_args(e) == 1;
    }

    /* Auxiliary functor for replacing constructor applications with update operations. */
    class replace_cnstr_fn {
        to_llnf_fn &         m_owner;
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

        /* Return true if `a` is of the form `_proj_u<size>.<offset> e` */
        bool is_scalar_proj_of(expr a, expr const & e, unsigned size, unsigned offset) {
            a = find(a);
            unsigned a_offset;
            if (!is_app(a) || app_arg(a) != e) return false;
            switch (size) {
            case 1: return is_llnf_proj_u8(app_fn(a), a_offset) && a_offset == offset;
            case 2: return is_llnf_proj_u16(app_fn(a), a_offset) && a_offset == offset;
            case 4: return is_llnf_proj_u32(app_fn(a), a_offset) && a_offset == offset;
            case 8: return is_llnf_proj_u64(app_fn(a), a_offset) && a_offset == offset;
            }
            return false;
        }

        expr visit_constructor(expr const & e) {
            buffer<expr> args;
            expr const & k = get_app_args(e, args);
            lean_assert(is_constant(k));
            if (is_runtime_builtin_cnstr(const_name(k))) {
                /* Optimization is not applicable to runtime builtin constructors. */
                return e;
            }
            cnstr_info k_info      = m_owner.get_cnstr_info(const_name(k));
            if (k_info.m_num_objs  != m_cinfo.m_num_objs || k_info.m_scalar_sz != m_cinfo.m_scalar_sz) {
                /* This constructor is not compatible with major premise */
                return e;
            }
            constructor_val k_val  = env().get(const_name(k)).to_constructor_val();
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
            r = mk_app(mk_app(mk_llnf_reuse(k_info.m_cidx, k_info.m_scalar_sz), r), obj_args);
            unsigned offset = k_info.m_num_objs * sizeof(void*);
            for (field_info const & info : k_info.m_field_info) {
                if (info.m_kind == field_info::Scalar) {
                    if (!is_scalar_proj_of(args[j], m_major, info.m_size, offset)) {
                        r = m_owner.mk_scalar_updt(r, info.m_size, offset, args[j]);
                    }
                    offset += info.m_size;
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
        replace_cnstr_fn(to_llnf_fn & owner, expr const & major, cnstr_info const & cinfo):
            m_owner(owner), m_major(major), m_cinfo(cinfo) {}
        expr operator()(expr const & e) { return visit(e); }
    };

    expr try_update_opt(expr const & minor, expr const & major, cnstr_info const & cinfo) {
        if (cinfo.m_num_objs == 0 && cinfo.m_scalar_sz == 0) return minor;
        if (!is_fvar(major)) return minor;
        if (has_fvar(minor, major)) return minor;
        return replace_cnstr_fn(*this, major, cinfo)(minor);
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
            unsigned next_offset = cinfo.m_num_objs * sizeof(void*);
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
                case field_info::Scalar:
                    fields.push_back(mk_let_decl(binding_domain(minor), mk_scalar_proj(major, info.m_size, next_offset)));
                    next_offset += info.m_size;
                    break;
                }
                minor = binding_body(minor);
            }
            minor     = instantiate_rev(minor, fields.size(), fields.data());
            minor     = try_update_opt(minor, major, cinfo);
            minor     = visit(minor);
            if (!is_enf_unreachable(minor)) {
                /* If `minor` is not the constructor `i`, then this "cases_on" application is not the identity. */
                unsigned cidx, ssz;
                if (!(is_llnf_cnstr(minor, cidx, ssz) && cidx == i && ssz == 0)) {
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
        expr r = mk_app(mk_llnf_cnstr(cidx, k_info.m_scalar_sz), obj_args);
        j = nparams;
        unsigned offset = k_info.m_num_objs * sizeof(void*);
        bool first      = true;
        for (field_info const & info : k_info.m_field_info) {
            if (info.m_kind == field_info::Scalar) {
                if (first && obj_args.size() > 0) {
                    r = mk_let_decl(mk_enf_object_type(), r);
                }
                r = mk_let_decl(info.get_type(), mk_scalar_updt(r, info.m_size, offset, args[j]));
                offset += info.m_size;
                first = false;
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
        unsigned offset   = k_info.m_num_objs * sizeof(void*);
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
            case field_info::Scalar:
                if (proj_idx(e) == i)
                    return mk_scalar_proj(visit(proj_expr(e)), info.m_size, offset);
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
        } else {
            return e;
        }
    }

    expr visit_app_default(expr const & e) {
        buffer<expr> args;
        expr const & fn = get_app_args(e, args);
        for (expr & arg : args)
            arg = visit(arg);
        return mk_app(fn, args);
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
        if (is_cases_on_app(env(), e)) {
            return visit_cases(e);
        } else if (is_constructor_app(env(), e)) {
            return visit_constructor(e);
        } else if (is_updt_scalar_app(e)) {
            return flat_app(e);
        } else if (is_reuse_app(e)) {
            return flat_app(e);
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

expr to_llnf(environment const & env, expr const & e, bool unboxed) {
    return to_llnf_fn(env, unboxed)(e);
}

void initialize_llnf() {
    g_cnstr     = new name("_cnstr");
    g_reuse     = new name("_reuse");
    g_reset     = new name("_reset");
    g_updt      = new name("_updt");
    g_updt_cidx = new name("_updt_cidx");
    g_updt_u8   = new name("_updt_u8");
    g_updt_u16  = new name("_updt_u16");
    g_updt_u32  = new name("_updt_u32");
    g_updt_u64  = new name("_updt_u64");
    g_proj      = new name("_proj");
    g_proj_u8   = new name("_proj_u8");
    g_proj_u16  = new name("_proj_u16");
    g_proj_u32  = new name("_proj_u32");
    g_proj_u64  = new name("_proj_u64");
    g_builtin_scalar_size = new std::vector<pair<name, unsigned>>();
    g_builtin_scalar_size->emplace_back(get_uint8_name(),  1);
    g_builtin_scalar_size->emplace_back(get_uint16_name(), 2);
    g_builtin_scalar_size->emplace_back(get_uint32_name(), 4);
    g_builtin_scalar_size->emplace_back(get_uint64_name(), 8);
}

void finalize_llnf() {
    delete g_cnstr;
    delete g_reuse;
    delete g_reset;
    delete g_updt;
    delete g_updt_u8;
    delete g_updt_u16;
    delete g_updt_u32;
    delete g_updt_u64;
    delete g_proj;
    delete g_proj_u8;
    delete g_proj_u16;
    delete g_proj_u32;
    delete g_proj_u64;
}
}
