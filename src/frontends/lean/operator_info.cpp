/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/rc.h"
#include "library/io_state_stream.h"
#include "frontends/lean/operator_info.h"
#include "frontends/lean/frontend.h"

namespace lean {
/** \brief Actual implementation of operator_info */
struct operator_info::imp {
    void dealloc() { delete this;  }
    MK_LEAN_RC();
    fixity        m_fixity;
    unsigned      m_precedence;
    list<name>    m_op_parts;  // operator parts, > 1 only if the operator is mixfix.
    list<expr>    m_exprs;     // possible interpretations for the operator.

    imp(name const & op, fixity f, unsigned p):
        m_rc(1), m_fixity(f), m_precedence(p), m_op_parts(cons(op, list<name>())) {}

    imp(unsigned num_parts, name const * parts, fixity f, unsigned p):
        m_rc(1), m_fixity(f), m_precedence(p), m_op_parts(to_list<name const *>(parts, parts + num_parts)) {
        lean_assert(num_parts > 0);
    }

    imp(imp const & s):
        m_rc(1), m_fixity(s.m_fixity), m_precedence(s.m_precedence), m_op_parts(s.m_op_parts), m_exprs(s.m_exprs) {
    }

    bool is_eq(imp const & other) const {
        return
            m_fixity == other.m_fixity &&
            m_precedence == other.m_precedence &&
            m_op_parts == other.m_op_parts;
    }
};

operator_info::operator_info(imp * p):m_ptr(p) {}

operator_info::operator_info(operator_info const & info):m_ptr(info.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }

operator_info::operator_info(operator_info && info):m_ptr(info.m_ptr) { info.m_ptr = nullptr; }

operator_info::~operator_info() { if (m_ptr) m_ptr->dec_ref(); }

operator_info & operator_info::operator=(operator_info const & s) { LEAN_COPY_REF(s); }

operator_info & operator_info::operator=(operator_info && s) { LEAN_MOVE_REF(s); }

void operator_info::add_expr(expr const & d) { lean_assert(m_ptr); m_ptr->m_exprs = cons(d, m_ptr->m_exprs); }

bool operator_info::is_overloaded() const { return m_ptr && !is_nil(m_ptr->m_exprs) && !is_nil(cdr(m_ptr->m_exprs)); }

list<expr> const & operator_info::get_denotations() const { lean_assert(m_ptr); return m_ptr->m_exprs; }

fixity operator_info::get_fixity() const { lean_assert(m_ptr); return m_ptr->m_fixity; }

unsigned operator_info::get_precedence() const { lean_assert(m_ptr); return m_ptr->m_precedence; }

name const & operator_info::get_op_name() const { lean_assert(m_ptr); return car(m_ptr->m_op_parts); }

list<name> const & operator_info::get_op_name_parts() const { lean_assert(m_ptr); return m_ptr->m_op_parts; }

bool operator_info::is_safe_ascii() const {
    auto l = get_op_name_parts();
    return std::all_of(l.begin(), l.end(), [](name const & p) { return p.is_safe_ascii(); });
}

operator_info operator_info::copy() const { return operator_info(new imp(*m_ptr)); }

bool operator==(operator_info const & op1, operator_info const & op2) {
    if ((op1.m_ptr == nullptr) != (op2.m_ptr == nullptr))
        return false;
    if (op1.m_ptr)
        return op1.m_ptr->is_eq(*(op2.m_ptr));
    else
        return true;
}

operator_info infix(name const & op, unsigned precedence) {
    return operator_info(new operator_info::imp(op, fixity::Infix, precedence));
}
operator_info infixr(name const & op, unsigned precedence) {
    return operator_info(new operator_info::imp(op, fixity::Infixr, precedence));
}
operator_info infixl(name const & op, unsigned precedence) {
    return operator_info(new operator_info::imp(op, fixity::Infixl, precedence));
}
operator_info prefix(name const & op, unsigned precedence) {
    return operator_info(new operator_info::imp(op, fixity::Prefix, precedence));
}
operator_info postfix(name const & op, unsigned precedence) {
    return operator_info(new operator_info::imp(op, fixity::Postfix, precedence));
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
operator_info mixfixo(unsigned num_parts, name const * parts, unsigned precedence) {
    lean_assert(num_parts > 1); return operator_info(new operator_info::imp(num_parts, parts, fixity::Mixfixo, precedence));
}

char const * to_string(fixity f) {
    switch (f) {
    case fixity::Infix:   return "infix";
    case fixity::Infixl:  return "infixl";
    case fixity::Infixr:  return "infixr";
    case fixity::Prefix:  return "prefix";
    case fixity::Postfix: return "postfix";
    case fixity::Mixfixl: return "mixfixl";
    case fixity::Mixfixr: return "mixfixr";
    case fixity::Mixfixc: return "mixfixc";
    case fixity::Mixfixo: return "mixfixo";
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

format pp(operator_info const & o) {
    format r;
    switch (o.get_fixity()) {
    case fixity::Infix:
    case fixity::Infixl:
    case fixity::Infixr:
        r = highlight_command(format(to_string(o.get_fixity())));
        if (o.get_precedence() > 1)
            r += format{space(), format(o.get_precedence())};
        r += format{space(), format(o.get_op_name())};
        return r;
    case fixity::Prefix:
    case fixity::Postfix:
    case fixity::Mixfixl:
    case fixity::Mixfixr:
    case fixity::Mixfixc:
    case fixity::Mixfixo:
        r = highlight_command(format("notation"));
        if (o.get_precedence() > 1)
            r += format{space(), format(o.get_precedence())};
        switch (o.get_fixity()) {
        case fixity::Prefix:
            r += format{space(), format(o.get_op_name()), space(), format("_")};
            return r;
        case fixity::Postfix:
            r += format{space(), format("_"), space(), format(o.get_op_name())};
            return r;
        case fixity::Mixfixl:
            for (auto p : o.get_op_name_parts())
                r += format{space(), format(p), space(), format("_")};
            return r;
        case fixity::Mixfixr:
            for (auto p : o.get_op_name_parts())
                r += format{space(), format("_"), space(), format(p)};
            return r;
        case fixity::Mixfixc: {
            auto parts = o.get_op_name_parts();
            r += format{space(), format(head(parts))};
            for (auto p : tail(parts))
                r += format{space(), format("_"), space(), format(p)};
            return r;
        }
        case fixity::Mixfixo:
            for (auto p : o.get_op_name_parts())
                r += format{space(), format("_"), space(), format(p)};
            r += format{space(), format("_")};
            return r;
        default: lean_unreachable(); // LCOV_EXCL_LINE
        }
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

char const * notation_declaration::keyword() const {
    return to_string(m_op.get_fixity());
}

void notation_declaration::write(serializer & s) const {
    auto parts = m_op.get_op_name_parts();
    s << "Notation" << length(parts);
    for (auto n : parts)
        s << n;
    s << static_cast<char>(m_op.get_fixity()) << m_op.get_precedence() << m_expr;
}
static void read_notation(environment const & env, io_state const & ios, deserializer & d) {
    buffer<name> parts;
    unsigned num = d.read_unsigned();
    for (unsigned i = 0; i < num; i++)
        parts.push_back(read_name(d));
    fixity fx = static_cast<fixity>(d.read_char());
    unsigned p = d.read_unsigned();
    expr e = read_expr(d);
    switch (fx) {
    case fixity::Infix:   lean_assert(parts.size() == 1); add_infix(env, ios, parts[0], p, e); return;
    case fixity::Infixl:  lean_assert(parts.size() == 1); add_infixl(env, ios, parts[0], p, e); return;
    case fixity::Infixr:  lean_assert(parts.size() == 1); add_infixr(env, ios, parts[0], p, e); return;
    case fixity::Prefix:  lean_assert(parts.size() == 1); add_prefix(env, ios, parts[0], p, e); return;
    case fixity::Postfix: lean_assert(parts.size() == 1); add_postfix(env, ios, parts[0], p, e); return;
    case fixity::Mixfixl: add_mixfixl(env, ios, parts.size(), parts.data(), p, e); return;
    case fixity::Mixfixr: add_mixfixr(env, ios, parts.size(), parts.data(), p, e); return;
    case fixity::Mixfixc: add_mixfixc(env, ios, parts.size(), parts.data(), p, e); return;
    case fixity::Mixfixo: add_mixfixo(env, ios, parts.size(), parts.data(), p, e); return;
    }
}
static object_cell::register_deserializer_fn notation_ds("Notation", read_notation);

std::ostream & operator<<(std::ostream & out, operator_info const & o) {
    out << pp(o);
    return out;
}

io_state_stream const & operator<<(io_state_stream const & out, operator_info const & o) {
    out.get_stream() << mk_pair(pp(o), out.get_options());
    return out;
}

char const * alias_declaration::keyword() const { return "alias"; }
void alias_declaration::write(serializer & s) const { s << "alias" << m_name << m_expr; }
static void read_alias(environment const & env, io_state const &, deserializer & d) {
    name n = read_name(d);
    expr e = read_expr(d);
    add_alias(env, n, e);
}
static object_cell::register_deserializer_fn add_alias_ds("alias", read_alias);
}
