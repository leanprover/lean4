/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/declaration.h"
#include "kernel/environment.h"
#include "kernel/for_each_fn.h"

namespace lean {
struct declaration::cell {
    MK_LEAN_RC();
    name              m_name;
    level_param_names m_params;
    expr              m_type;
    bool              m_theorem;
    optional<expr>    m_value;        // if none, then declaration is actually a postulate
    unsigned          m_height;       // definitional height
    // The following field affects the convertability checker.
    // Let f be this definition, then if the following field is true,
    // then whenever we are checking whether
    //    (f a) is convertible to (f b)
    // we will first check whether a is convertible to b.
    // If the test fails, then we perform the full check.
    bool              m_use_conv_opt;
    void dealloc() { delete this; }

    cell(name const & n, level_param_names const & params, expr const & t, bool is_axiom):
        m_rc(1), m_name(n), m_params(params), m_type(t), m_theorem(is_axiom),
        m_height(0), m_use_conv_opt(false) {}
    cell(name const & n, level_param_names const & params, expr const & t, bool is_thm, expr const & v,
         unsigned h, bool use_conv_opt):
        m_rc(1), m_name(n), m_params(params), m_type(t), m_theorem(is_thm),
        m_value(v), m_height(h), m_use_conv_opt(use_conv_opt) {}
};

static declaration * g_dummy = nullptr;

declaration::declaration():declaration(*g_dummy) {}
declaration::declaration(cell * ptr):m_ptr(ptr) {}
declaration::declaration(declaration const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
declaration::declaration(declaration && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
declaration::~declaration() { if (m_ptr) m_ptr->dec_ref(); }

declaration & declaration::operator=(declaration const & s) { LEAN_COPY_REF(s); }
declaration & declaration::operator=(declaration && s) { LEAN_MOVE_REF(s); }

bool declaration::is_definition() const    { return static_cast<bool>(m_ptr->m_value); }
bool declaration::is_constant_assumption() const { return !is_definition(); }
bool declaration::is_axiom() const         { return is_constant_assumption() && m_ptr->m_theorem; }
bool declaration::is_theorem() const       { return is_definition() && m_ptr->m_theorem; }

name const & declaration::get_name() const { return m_ptr->m_name; }
level_param_names const & declaration::get_univ_params() const { return m_ptr->m_params; }
unsigned declaration::get_num_univ_params() const { return length(get_univ_params()); }
expr const & declaration::get_type() const { return m_ptr->m_type; }

expr const & declaration::get_value() const { lean_assert(is_definition()); return *(m_ptr->m_value); }
unsigned declaration::get_height() const { return m_ptr->m_height; }
bool declaration::use_conv_opt() const { return m_ptr->m_use_conv_opt; }

declaration mk_definition(name const & n, level_param_names const & params, expr const & t, expr const & v,
                          unsigned height, bool use_conv_opt) {
    return declaration(new declaration::cell(n, params, t, false, v, height, use_conv_opt));
}
static unsigned get_max_height(environment const & env, expr const & v) {
    unsigned h = 0;
    for_each(v, [&](expr const & e, unsigned) {
            if (is_constant(e)) {
                auto d = env.find(const_name(e));
                if (d && d->get_height() > h)
                    h = d->get_height();
            }
            return true;
        });
    return h;
}

declaration mk_definition(environment const & env, name const & n, level_param_names const & params, expr const & t,
                          expr const & v, bool use_conv_opt) {
    unsigned h = get_max_height(env, v);
    return mk_definition(n, params, t, v, h+1, use_conv_opt);
}
declaration mk_theorem(environment const & env, name const & n, level_param_names const & params, expr const & t, expr const & v) {
    unsigned h = get_max_height(env, v);
    return declaration(new declaration::cell(n, params, t, true, v, h+1, true));
}
declaration mk_theorem(name const & n, level_param_names const & params, expr const & t, expr const & v, unsigned height) {
    return declaration(new declaration::cell(n, params, t, true, v, height, true));
}
declaration mk_axiom(name const & n, level_param_names const & params, expr const & t) {
    return declaration(new declaration::cell(n, params, t, true));
}
declaration mk_constant_assumption(name const & n, level_param_names const & params, expr const & t) {
    return declaration(new declaration::cell(n, params, t, false));
}

void initialize_declaration() {
    g_dummy = new declaration(mk_axiom(name(), level_param_names(), expr()));
}

void finalize_declaration() {
    delete g_dummy;
}
}
