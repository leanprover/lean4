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
    g_ext = new native_decls_reg();
}

void finalize_builtin() {
    delete g_ext;
    delete g_initial_native_decls;
}
}
