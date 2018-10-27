/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <unordered_set>
#include "kernel/instantiate.h"
#include "library/util.h"
#include "library/compiler/util.h"

namespace lean {
static expr * g_cases    = nullptr;
static name * g_cnstr    = nullptr;
static name * g_updt     = nullptr;
static name * g_updt_u8  = nullptr;
static name * g_updt_u16 = nullptr;
static name * g_updt_u32 = nullptr;
static name * g_updt_u64 = nullptr;
static name * g_proj_u8  = nullptr;
static name * g_proj_u16 = nullptr;
static name * g_proj_u32 = nullptr;
static name * g_proj_u64 = nullptr;

expr mk_llnf_cases() {
    return *g_cases;
}

bool is_llnf_cases(expr const & e) {
    return e == *g_cases;
}

expr mk_llnf_cnstr(unsigned cidx, unsigned scalar_sz) {
    return mk_constant(name(name(*g_cnstr, cidx), scalar_sz));
}

bool is_llnf_cnstr(expr const & e, unsigned & cidx, unsigned & ssz) {
    if (!is_constant(e)) return false;
    name const & n = const_name(e);
    if (!is_internal_name(n) || n.is_atomic() || !n.is_numeral()) return false;
    ssz = n.get_numeral().get_small_value();
    name const & p = n.get_prefix();
    if (p.is_atomic() || !p.is_numeral() || p.get_prefix() != g_cnstr) return false;
    cidx = p.get_numeral().get_small_value();
    return true;
}

static bool is_llnf_primitive(expr const & e, name const & prefix, unsigned & i) {
    if (!is_constant(e)) return false;
    name const & n = const_name(e);
    if (!is_internal_name(n) || n.is_atomic() || !n.is_numeral() || n.get_prefix() != prefix) return false;
    i = n.get_numeral().get_small_value();
    return true;
}

expr mk_llnf_updt(unsigned i) { return mk_constant(name(*g_updt, i)); }
bool is_llnf_updt(expr const & e, unsigned & i) { return is_llnf_primitive(e, *g_updt, i); }

expr mk_llnf_updt_u8(unsigned offset) { return mk_constant(name(*g_updt_u8, offset)); }
bool is_llnf_updt_u8(expr const & e, unsigned & offset) { return is_llnf_primitive(e, *g_updt_u8, offset); }

expr mk_llnf_updt_u16(unsigned offset) { return mk_constant(name(*g_updt_u16, offset)); }
bool is_llnf_updt_u16(expr const & e, unsigned & offset) { return is_llnf_primitive(e, *g_updt_u16, offset); }

expr mk_llnf_updt_u32(unsigned offset) { return mk_constant(name(*g_updt_u32, offset)); }
bool is_llnf_updt_u32(expr const & e, unsigned & offset) { return is_llnf_primitive(e, *g_updt_u32, offset); }

expr mk_llnf_updt_u64(unsigned offset) { return mk_constant(name(*g_updt_u64, offset)); }
bool is_llnf_updt_u64(expr const & e, unsigned & offset) { return is_llnf_primitive(e, *g_updt_u64, offset); }

expr mk_llnf_proj_u8(unsigned offset) { return mk_constant(name(*g_proj_u8, offset)); }
bool is_llnf_proj_u8(expr const & e, unsigned & offset) { return is_llnf_primitive(e, *g_proj_u8, offset); }

expr mk_llnf_proj_u16(unsigned offset) { return mk_constant(name(*g_proj_u16, offset)); }
bool is_llnf_proj_u16(expr const & e, unsigned & offset) { return is_llnf_primitive(e, *g_proj_u16, offset); }

expr mk_llnf_proj_u32(unsigned offset) { return mk_constant(name(*g_proj_u32, offset)); }
bool is_llnf_proj_u32(expr const & e, unsigned & offset) { return is_llnf_primitive(e, *g_proj_u32, offset); }

expr mk_llnf_proj_u64(unsigned offset) { return mk_constant(name(*g_proj_u64, offset)); }
bool is_llnf_proj_u64(expr const & e, unsigned & offset) { return is_llnf_primitive(e, *g_proj_u64, offset); }

class to_llnf_fn {
    typedef std::unordered_set<name, name_hash> name_set;
    environment const & m_env;
    name_generator      m_ngen;
    bool                m_unboxed;
    local_ctx           m_lctx;
    buffer<expr>        m_fvars;
    name                m_x;
    name                m_j;
    unsigned            m_next_idx{1};
    unsigned            m_next_jp_idx{1};

    environment const & env() { return m_env; }

    name_generator & ngen() { return m_ngen; }

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
            collect_used(val,  used_fvars);
            used.push_back(x);
        }
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

    expr visit_cases(expr const & e) {
        // TODO(Leo):
        return e;
    }

    expr visit_constructor(expr const & e) {
        // TODO(Leo):
        return e;
    }

    expr visit_proj(expr const & e) {
        // TODO(Leo):
        return e;
    }

    expr visit_constant(expr const & e) {
        if (is_constructor(env(), const_name(e))) {
            return visit_constructor(e);
        } else {
            return e;
        }
    }

    expr visit_app(expr const & e) {
        if (is_cases_on_app(env(), e)) {
            return visit_cases(e);
        } else if (is_constructor_app(env(), e)) {
            return visit_constructor(e);
        } else {
            return e;
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
        m_env(env), m_unboxed(unboxed), m_x("_x"), m_j("j") {
    }

    expr operator()(expr const & e) {
        return visit(e);
    }
};

expr to_llnf(environment const & env, expr const & e, bool unboxed) {
    return to_llnf_fn(env, unboxed)(e);
}

void initialize_llnf() {
    g_cases    = new expr(mk_constant("_cases"));
    g_cnstr    = new name("_cnstr");
    g_updt     = new name("_updt");
    g_updt_u8  = new name("_updt_u8");
    g_updt_u16 = new name("_updt_u16");
    g_updt_u32 = new name("_updt_u32");
    g_updt_u64 = new name("_updt_u64");
    g_proj_u8  = new name("_proj_u8");
    g_proj_u16 = new name("_proj_u16");
    g_proj_u32 = new name("_proj_u32");
    g_proj_u64 = new name("_proj_u64");
}

void finalize_llnf() {
    delete g_cases;
    delete g_cnstr;
    delete g_updt;
    delete g_updt_u8;
    delete g_updt_u16;
    delete g_updt_u32;
    delete g_updt_u64;
    delete g_proj_u8;
    delete g_proj_u16;
    delete g_proj_u32;
    delete g_proj_u64;
}
}
