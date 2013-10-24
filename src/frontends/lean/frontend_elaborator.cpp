/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/type_checker.h"
#include "library/elaborator/elaborator.h"
#include "frontends/lean/frontend.h"
#include "frontends/lean/frontend_elaborator.h"

namespace lean {
static name g_choice_name = name::mk_internal_unique_name();
static expr g_choice = mk_constant(g_choice_name);
static format g_assignment_fmt  = format(":=");
static format g_unification_u_fmt = format("\u2248");
static format g_unification_fmt = format("=?=");

expr mk_choice(unsigned num_fs, expr const * fs) {
    lean_assert(num_fs >= 2);
    return mk_eq(g_choice, mk_app(num_fs, fs));
}

bool is_choice(expr const & e) {
    return is_eq(e) && eq_lhs(e) == g_choice;
}

unsigned get_num_choices(expr const & e) {
    lean_assert(is_choice(e));
    return num_args(eq_rhs(e));
}

expr const & get_choice(expr const & e, unsigned i) {
    lean_assert(is_choice(e));
    return arg(eq_rhs(e), i);
}

class frontend_elaborator::imp {
    frontend  const &   m_frontend;
    environment const & m_env;
    type_checker        m_type_checker;
    volatile bool       m_interrupted;
public:
    imp(frontend const & fe):
        m_frontend(fe),
        m_env(fe.get_environment()),
        m_type_checker(m_env) {
        m_interrupted = false;
    }

    expr elaborate(expr const & e) {
        // TODO(Leo)
        return e;
    }

    std::pair<expr, expr> elaborate(expr const & t, expr const & e) {
        // TODO(Leo)
        return mk_pair(t, e);
    }

    expr const & get_original(expr const & e) {
        // TODO(Leo)
        return e;
    }

    void set_interrupt(bool f) {
        m_interrupted = f;
        m_type_checker.set_interrupt(f);
    }

    void clear() {
        // TODO(Leo)
    }

    environment const & get_environment() const {
        return m_env;
    }
};

frontend_elaborator::frontend_elaborator(frontend const & fe):m_ptr(new imp(fe)) {}
frontend_elaborator::~frontend_elaborator() {}
expr frontend_elaborator::operator()(expr const & e) { return m_ptr->elaborate(e); }
std::pair<expr, expr> frontend_elaborator::operator()(expr const & t, expr const & e) { return m_ptr->elaborate(t, e); }
expr const & frontend_elaborator::get_original(expr const & e) const { return m_ptr->get_original(e); }
void frontend_elaborator::set_interrupt(bool f) { m_ptr->set_interrupt(f); }
void frontend_elaborator::clear() { m_ptr->clear(); }
environment const & frontend_elaborator::get_environment() const { return m_ptr->get_environment(); }
}
