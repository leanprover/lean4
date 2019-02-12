/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura, Max Wagner

REMARK: ******* THIS FILE WILL BE DELETED *********
        It is being replaced with extern_attribute.cpp
*/
#include <unordered_map>
#include <string>
#include "util/list.h"
#include "kernel/expr.h"
#include "library/compiler/util.h"

namespace lean {

struct native_decl {
    expr                  m_ll_type;
    unsigned              m_arity;
    std::string           m_cname;
    bool                  m_borrowed_res;
    list<bool>            m_borrowed_args;

    native_decl() {}
    native_decl(expr const & ll_type, unsigned arity, std::string cname, bool bres, list<bool> const & bargs):
        m_ll_type(ll_type), m_arity(arity), m_cname(cname), m_borrowed_res(bres), m_borrowed_args(bargs) {
    }
};

typedef name_map<native_decl> native_decl_map;
static native_decl_map * g_initial_native_decls;

bool is_builtin_constant(name const & c) {
    return g_initial_native_decls->contains(c);
}

struct native_decls_ext : public environment_extension {
    native_decl_map m_decls;

    native_decls_ext() {
        g_initial_native_decls->for_each([&](name const & n, native_decl const & d) {
           m_decls.insert(n, d);
        });
    }
};

struct native_decls_reg {
    unsigned m_ext_id;
    native_decls_reg() {
        std::shared_ptr<native_decls_ext> decl_reg = std::make_shared<native_decls_ext>();
        m_ext_id = environment::register_extension(decl_reg);
    }
};

static native_decls_reg * g_ext = nullptr;

static environment update(environment const & env, native_decls_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<native_decls_ext>(ext));
}


void register_builtin(name const & n, expr const & ll_type, unsigned arity, char const * cname,
                      bool borrowed_res, list<bool> const & borrowed_arg) {
    lean_assert(g_initial_native_decls->find(n) == nullptr);
    g_initial_native_decls->insert(n, native_decl(ll_type, arity, cname, borrowed_res, borrowed_arg));
}

void register_builtin(name const & n, expr const & ll_type, char const * cname,
                      bool borrowed_res, list<bool> const & borrowed_arg) {
    unsigned arity = get_arity(ll_type);
    return register_builtin(n, ll_type, arity, cname, borrowed_res, borrowed_arg);
}

void register_builtin(name const & n, expr const & ll_type, char const * cname, list<bool> const & borrowed_arg) {
    return register_builtin(n, ll_type, cname, false, borrowed_arg);
}

void register_builtin(name const & n, expr const & ll_type, unsigned arity, char const * cname) {
    buffer<bool> borrowed;
    borrowed.resize(arity, false);
    return register_builtin(n, ll_type, arity, cname, false, to_list(borrowed));
}

void register_builtin(name const & n, expr const & ll_type, char const * cname) {
    unsigned arity = get_arity(ll_type);
    return register_builtin(n, ll_type, arity, cname);
}

static inline native_decls_ext const & get_ext(environment const & env) {
    return static_cast<native_decls_ext const & >(env.get_extension(g_ext->m_ext_id));
}

environment add_native_constant_decl(environment const & env, name const & n, expr const & ll_type, std::string cname,
                                     bool bres, list<bool> const & bargs) {
    native_decl d(ll_type, get_arity(ll_type), cname, bres, bargs);
    native_decls_ext ext = get_ext(env);
    ext.m_decls.insert(n, d);
    return update(env, ext);
}

void for_each_native_constant(environment const & env, std::function<void(name const & n)> const & f) {
    auto ext = get_ext(env);
    ext.m_decls.for_each([&](name const & n, native_decl const &) { f(n); });
}

static inline native_decl const * get_native_constant_core(environment const & env, name const & n) {
    auto ext = get_ext(env);
    return ext.m_decls.find(n);
}

optional<name> get_native_constant_cname(environment const & env, name const & c) {
    auto d =  get_native_constant_core(env, c);
    if (d == nullptr)
        return optional<name>();
    return optional<name>(d->m_cname);
}

bool is_native_constant(environment const & env, name const & c) {
    return get_native_constant_core(env, c) != nullptr;
}

optional<expr> get_native_constant_ll_type(environment const & env, name const & c) {
    auto d = get_native_constant_core(env, c);
    if (d == nullptr)
        return none_expr();
    return some_expr(d->m_ll_type);
}

optional<unsigned> get_native_constant_arity(environment const & env, name const & c) {
    auto d = get_native_constant_core(env, c);
    if (d == nullptr)
        return optional<unsigned>();
    return optional<unsigned>(d->m_arity);
}

bool get_native_borrowed_info(environment const & env, name const & c, buffer<bool> &borrowed_args, bool &borrowed_res) {
    auto d = get_native_constant_core(env, c);
    if (d == nullptr)
        return false;

    to_buffer(d->m_borrowed_args, borrowed_args);
    borrowed_res = d->m_borrowed_res;
    return true;
}

void initialize_builtin() {
    g_initial_native_decls = new native_decl_map();

    expr o           = mk_enf_object_type();
    expr u8          = mk_constant(get_uint8_name());
    expr u16         = mk_constant(get_uint16_name());
    expr u32         = mk_constant(get_uint32_name());
    expr u64         = mk_constant(get_uint64_name());
    expr us          = mk_constant(get_usize_name());
    expr o_o         = mk_arrow(o, o);
    expr o_o_o       = mk_arrow(o, o_o);
    expr o_o_o_o     = mk_arrow(o, o_o_o);
    expr o_o_o_o_o   = mk_arrow(o, o_o_o_o);

    expr o_u8        = mk_arrow(o, u8);
    expr o_u8_u8_o_o = mk_arrow(o, mk_arrow(u8, mk_arrow(u8, o_o)));
    expr u8_u8       = mk_arrow(u8, u8);
    expr u8_u8_u8    = mk_arrow(u8, u8_u8);
    expr u8_o_u8     = mk_arrow(u8, o_u8);
    expr u8_o        = mk_arrow(u8, o);
    expr u8_u8_o     = mk_arrow(u8, u8_o);
    expr o_o_u8      = mk_arrow(o, o_u8);

    expr o_u16         = mk_arrow(o, u16);
    expr o_u16_u16_o_o = mk_arrow(o, mk_arrow(u16, mk_arrow(u16, o_o)));
    expr u16_u16       = mk_arrow(u16, u16);
    expr u16_u16_u16   = mk_arrow(u16, u16_u16);
    expr u16_o_u16     = mk_arrow(u16, o_u16);
    expr u16_o         = mk_arrow(u16, o);
    expr u16_u16_o     = mk_arrow(u16, u16_o);
    expr u16_u16_u8    = mk_arrow(u16, mk_arrow(u16, u8));

    expr o_u32         = mk_arrow(o, u32);
    expr o_u32_o       = mk_arrow(o, mk_arrow(u32, o));
    expr o_u32_u32_o_o = mk_arrow(o, mk_arrow(u32, mk_arrow(u32, o_o)));
    expr u32_u32       = mk_arrow(u32, u32);
    expr u32_u32_u32   = mk_arrow(u32, u32_u32);
    expr u32_o_u32     = mk_arrow(u32, o_u32);
    expr u32_o         = mk_arrow(u32, o);
    expr u32_u32_o     = mk_arrow(u32, u32_o);
    expr u32_u32_u8    = mk_arrow(u32, mk_arrow(u32, u8));

    expr o_u64         = mk_arrow(o, u64);
    expr o_u64_u64_o_o = mk_arrow(o, mk_arrow(u64, mk_arrow(u64, o_o)));
    expr u64_u64       = mk_arrow(u64, u64);
    expr u64_u64_u64   = mk_arrow(u64, u64_u64);
    expr u64_o_u64     = mk_arrow(u64, o_u64);
    expr u64_o         = mk_arrow(u64, o);
    expr u64_u64_o     = mk_arrow(u64, u64_o);
    expr u64_u64_u8    = mk_arrow(u64, mk_arrow(u64, u8));

    expr o_us          = mk_arrow(o, us);
    expr o_us_us_o_o   = mk_arrow(o, mk_arrow(us, mk_arrow(us, o_o)));
    expr us_us         = mk_arrow(us, us);
    expr us_us_us      = mk_arrow(us, us_us);
    expr us_o_us       = mk_arrow(us, o_us);
    expr us_o          = mk_arrow(us, o);
    expr us_us_o       = mk_arrow(us, us_o);
    expr us_us_u8      = mk_arrow(us, mk_arrow(us, u8));

    list<bool> b{true};
    list<bool> bb{true, true};
    list<bool> c{false};
    list<bool> cc{false, false};
    list<bool> cb{false, true};
    list<bool> bc{true, false};
    list<bool> bbb{true, true, true};
    list<bool> bccc{true, false, false, false};
    list<bool> bbcc{true, true, false, false};

    /* nat builtin functions */
    register_builtin(name({"nat", "add"}), o_o_o, "lean::nat_add", bb);
    register_builtin(name({"nat", "sub"}), o_o_o, "lean::nat_sub", bb);
    register_builtin(name({"nat", "mul"}), o_o_o, "lean::nat_mul", bb);
    register_builtin(name({"nat", "div"}), o_o_o, "lean::nat_div", bb);
    register_builtin(name({"nat", "mod"}), o_o_o, "lean::nat_mod", bb);
    register_builtin(name({"nat", "dec_eq"}), o_o_u8, "lean::nat_dec_eq", bb);
    register_builtin(name({"nat", "dec_lt"}), o_o_u8, "lean::nat_dec_lt", bb);
    register_builtin(name({"nat", "dec_le"}), o_o_u8, "lean::nat_dec_le", bb);

    /* int builtin functions */
    register_builtin(name({"int", "of_nat"}), o_o, "lean::nat2int", b);
    register_builtin(name({"int", "neg_succ_of_nat"}), o_o, "lean::int_neg_succ_of_nat", b);
    register_builtin(name({"int", "nat_abs"}), o_o, "lean::nat_abs", b);
    register_builtin(name({"int", "neg"}), o_o, "lean::int_neg", b);
    register_builtin(name({"int", "add"}), o_o_o, "lean::int_add", bb);
    register_builtin(name({"int", "sub"}), o_o_o, "lean::int_sub", bb);
    register_builtin(name({"int", "mul"}), o_o_o, "lean::int_mul", bb);
    register_builtin(name({"int", "quot"}), o_o_o, "lean::int_div", bb);
    register_builtin(name({"int", "rem"}), o_o_o, "lean::int_rem", bb);
    register_builtin(name({"int", "dec_eq"}), o_o_u8, "lean::int_dec_eq", bb);
    register_builtin(name({"int", "dec_lt"}), o_o_u8, "lean::int_dec_lt", bb);
    register_builtin(name({"int", "dec_le"}), o_o_u8, "lean::int_dec_le", bb);

    g_ext = new native_decls_reg();
}

void finalize_builtin() {
    delete g_ext;
    delete g_initial_native_decls;
}
}
