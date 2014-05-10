/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/definition.h"
#include "kernel/environment.h"
#include "kernel/for_each_fn.h"

namespace lean {
static serializer & operator<<(serializer & s, param_names const & ps) { return write_list<name>(s, ps); }
static param_names read_params(deserializer & d) { return read_list<name>(d); }

struct definition::cell {
    MK_LEAN_RC();
    name           m_name;
    param_names    m_params;
    expr           m_type;
    bool           m_theorem;
    optional<expr> m_value;        // if none, then definition is actually a postulate
    // The following fields are only meaningful for definitions (which are not theorems)
    unsigned       m_weight;
    unsigned       m_module_idx;   // module idx where it was defined
    bool           m_opaque;
    // The following field affects the convertability checker.
    // Let f be this definition, then if the following field is true,
    // then whenever we are checking whether
    //    (f a) is convertible to (f b)
    // we will first check whether a is convertible to b.
    // If the test fails, then we perform the full check.
    bool           m_use_conv_opt;
    void dealloc() { delete this; }

    cell(name const & n, param_names const & params, expr const & t, bool is_axiom):
        m_rc(1), m_name(n), m_params(params), m_type(t), m_theorem(is_axiom),
        m_weight(0), m_module_idx(0), m_opaque(true), m_use_conv_opt(false) {}
    cell(name const & n, param_names const & params, expr const & t, bool is_thm, expr const & v,
         bool opaque, unsigned w, module_idx mod_idx, bool use_conv_opt):
        m_rc(1), m_name(n), m_params(params), m_type(t), m_theorem(is_thm),
        m_value(v), m_weight(w), m_module_idx(mod_idx), m_opaque(opaque), m_use_conv_opt(use_conv_opt) {}

    void write(serializer & s) const {
        char k = 0;
        if (m_value) {
            k |= 1;
            if (m_opaque)
                k |= 2;
            if (m_use_conv_opt)
                k |= 4;
        }
        if (m_theorem)
            k |= 8;
        s << k << m_name << m_params << m_type;
        if (m_value) {
            s << *m_value;
            if (!m_theorem)
                s << m_weight;
        }
    }
};

definition g_dummy = mk_axiom(name(), param_names(), expr());

definition::definition():definition(g_dummy) {}
definition::definition(cell * ptr):m_ptr(ptr) {}
definition::definition(definition const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
definition::definition(definition && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
definition::~definition() { if (m_ptr) m_ptr->dec_ref(); }

definition & definition::operator=(definition const & s) { LEAN_COPY_REF(s); }
definition & definition::operator=(definition && s) { LEAN_MOVE_REF(s); }

bool definition::is_definition() const { return static_cast<bool>(m_ptr->m_value); }
bool definition::is_var_decl() const   { return !is_definition(); }
bool definition::is_axiom() const      { return is_var_decl() && m_ptr->m_theorem; }
bool definition::is_theorem() const    { return is_definition() && m_ptr->m_theorem; }

name definition::get_name() const { return m_ptr->m_name; }
param_names const & definition::get_params() const { return m_ptr->m_params; }
expr definition::get_type() const { return m_ptr->m_type; }

bool definition::is_opaque() const { return m_ptr->m_opaque; }
expr definition::get_value() const { lean_assert(is_definition()); return *(m_ptr->m_value); }
unsigned definition::get_weight() const { return m_ptr->m_weight; }
module_idx definition::get_module_idx() const { return m_ptr->m_module_idx; }
bool definition::use_conv_opt() const { return m_ptr->m_use_conv_opt; }

void definition::write(serializer & s) const { m_ptr->write(s); }

definition mk_definition(name const & n, param_names const & params, expr const & t, expr const & v,
                         bool opaque, unsigned weight, module_idx mod_idx, bool use_conv_opt) {
    return definition(new definition::cell(n, params, t, false, v, opaque, weight, mod_idx, use_conv_opt));
}
definition mk_definition(environment const & env, name const & n, param_names const & params, expr const & t, expr const & v,
                         bool opaque, module_idx mod_idx, bool use_conv_opt) {
    unsigned w = 0;
    for_each(v, [&](expr const & e, unsigned) {
            if (is_constant(e)) {
                auto d = env.find(const_name(e));
                if (d && d->get_weight() > w)
                    w = d->get_weight();
            }
            return true;
        });
    return mk_definition(n, params, t, v, opaque, w+1, mod_idx, use_conv_opt);
}
definition mk_theorem(name const & n, param_names const & params, expr const & t, expr const & v) {
    return definition(new definition::cell(n, params, t, true, v, true, 0, 0, false));
}
definition mk_axiom(name const & n, param_names const & params, expr const & t) {
    return definition(new definition::cell(n, params, t, true));
}
definition mk_var_decl(name const & n, param_names const & params, expr const & t) {
    return definition(new definition::cell(n, params, t, false));
}

definition read_definition(deserializer & d, unsigned module_idx) {
    char k = d.read_char();
    bool has_value  = (k & 1) != 0;
    bool is_theorem = (k & 8) != 0;
    name n          = read_name(d);
    param_names ps  = read_params(d);
    expr t          = read_expr(d);
    if (has_value) {
        expr v      = read_expr(d);
        if (is_theorem) {
            return mk_theorem(n, ps, t, v);
        } else {
            unsigned w        = d.read_unsigned();
            bool is_opaque    = (k & 2) != 0;
            bool use_conv_opt = (k & 4) != 0;
            return mk_definition(n, ps, t, v, is_opaque, w, module_idx, use_conv_opt);
        }
    } else {
        if (is_theorem)
            return mk_axiom(n, ps, t);
        else
            return mk_var_decl(n, ps, t);
    }
}
}
