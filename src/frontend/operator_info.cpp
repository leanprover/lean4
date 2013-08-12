
/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "operator_info.h"
#include "rc.h"
#include "options.h"

namespace lean {

struct operator_info::imp {
    void dealloc() { delete this;  }
    MK_LEAN_RC();
    fixity        m_fixity;
    associativity m_assoc;  // Relevant only for infix operators.
    unsigned      m_precedence;
    list<name>    m_op_parts;  // operator parts, > 1 only if the operator is mixfix.
    list<name>    m_names;     // internal names, > 1 only if the operator is overloaded.

    imp(name const & op, fixity f, associativity a, unsigned p):
        m_rc(1), m_fixity(f), m_assoc(a), m_precedence(p), m_op_parts(cons(op, list<name>())) {}

    imp(unsigned num_parts, name const * parts, fixity f, unsigned p):
        m_rc(1), m_fixity(f), m_assoc(associativity::None), m_precedence(p), m_op_parts(it2list<name, name const *>(parts, parts + num_parts)) {
        lean_assert(num_parts > 0);
    }

    imp(imp const & s):
        m_rc(1), m_fixity(s.m_fixity), m_assoc(s.m_assoc), m_precedence(s.m_precedence), m_op_parts(s.m_op_parts), m_names(s.m_names) {
    }
};

operator_info::operator_info(imp * p):m_ptr(p) {}

operator_info::operator_info(operator_info const & info):m_ptr(info.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }

operator_info::operator_info(operator_info && info):m_ptr(info.m_ptr) { info.m_ptr = nullptr; }

operator_info::~operator_info() { if (m_ptr) m_ptr->dec_ref(); }

operator_info & operator_info::operator=(operator_info const & s) { LEAN_COPY_REF(operator_info, s); }

operator_info & operator_info::operator=(operator_info && s) { LEAN_MOVE_REF(operator_info, s); }

void operator_info::add_internal_name(name const & n) { lean_assert(m_ptr); m_ptr->m_names = cons(n, m_ptr->m_names); }

bool operator_info::is_overloaded() const { return m_ptr && !is_nil(m_ptr->m_names) && !is_nil(cdr(m_ptr->m_names)); }

list<name> const & operator_info::get_internal_names() const { lean_assert(m_ptr); return m_ptr->m_names; }

fixity operator_info::get_fixity() const { lean_assert(m_ptr); return m_ptr->m_fixity; }

associativity operator_info::get_associativity() const { lean_assert(m_ptr); return m_ptr->m_assoc; }

unsigned operator_info::get_precedence() const { lean_assert(m_ptr); return m_ptr->m_precedence; }

name const & operator_info::get_op_name() const { lean_assert(m_ptr); return car(m_ptr->m_op_parts); }

list<name> const & operator_info::get_op_name_parts() const { lean_assert(m_ptr); return m_ptr->m_op_parts; }

operator_info operator_info::copy() const { return operator_info(new imp(*m_ptr)); }

operator_info infixr(name const & op, unsigned precedence) {
    return operator_info(new operator_info::imp(op, fixity::Infix,  associativity::Right, precedence));
}
operator_info infixl(name const & op, unsigned precedence) {
    return operator_info(new operator_info::imp(op, fixity::Infix,  associativity::Left, precedence));
}
operator_info prefix(name const & op, unsigned precedence) {
    return operator_info(new operator_info::imp(op, fixity::Prefix, associativity::None, precedence));
}
operator_info postfix(name const & op, unsigned precedence) {
    return operator_info(new operator_info::imp(op, fixity::Postfix, associativity::None, precedence));
}
operator_info mixfixl(unsigned num_parts, name const * parts, unsigned precedence) {
    lean_assert(num_parts > 1); return operator_info(new operator_info::imp(num_parts, parts, fixity::Mixfixl, precedence));
}
operator_info mixfixr(unsigned num_parts, name const * parts, unsigned precedence) {
    lean_assert(num_parts > 1); return operator_info(new operator_info::imp(num_parts, parts, fixity::Mixfixr, precedence));
}
operator_info mixfixc(unsigned num_parts, name const * parts, unsigned precedence) {
    lean_assert(num_parts > 1); return operator_info(new operator_info::imp(num_parts, parts, fixity::Mixfixc, precedence));
}

static char const * g_arrow               = "\u21a6";

format pp(operator_info const & o, options const & opt) {
    format r;
    switch (o.get_fixity()) {
    case fixity::Infix:   r = format(o.get_associativity() == associativity::Left ? "Infixl" : "Infixr"); break;
    case fixity::Prefix:  r = format("Prefix");  break;
    case fixity::Postfix: r = format("Postfix"); break;
    case fixity::Mixfixl:
    case fixity::Mixfixr:
    case fixity::Mixfixc: r = format("Mixfix"); break;
    }

    r += space();

    if (o.get_precedence() != 0)
        r += format{format(o.get_precedence()), space()};

    switch (o.get_fixity()) {
    case fixity::Infix: case fixity::Prefix: case fixity::Postfix:
        r += pp(o.get_op_name(), opt); break;
    case fixity::Mixfixl:
        for (auto p : o.get_op_name_parts()) r += format{pp(p, opt), format(" _")};
        break;
    case fixity::Mixfixr:
        for (auto p : o.get_op_name_parts()) r += format{format("_ "), pp(p, opt)};
        break;
    case fixity::Mixfixc: {
        bool first = true;
        for (auto p : o.get_op_name_parts()) {
            if (first) first = false; else r += format(" _ ");
            r += pp(p, opt);
        }
    }}

    list<name> const & l = o.get_internal_names();
    if (!is_nil(l)) {
        r += format{space(), format(g_arrow)};
        for (auto n : l) r += format{space(), pp(n, opt)};
    }
    return r;
}

format pp(operator_info const & o) {
    return pp(o, options());
}

std::ostream & operator<<(std::ostream & out, operator_info const & o) {
    out << pp(o);
    return out;
}

}
