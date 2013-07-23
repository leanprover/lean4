/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Soonho Kong
*/
#include <cstring>
#include "rc.h"
#include "hash.h"
#include "sexpr.h"
#include "format.h"
#include "name.h"
#include "mpz.h"
#include "mpq.h"

namespace lean {

struct format_cell {
    void dealloc();
    MK_LEAN_RC()
    format_kind  m_kind;
    sexpr        m_value;
    format_cell(format_kind k):m_rc(1), m_kind(k) {}
    format_cell(char const * v):
        format_cell(format_kind::TEXT) {
        m_value = sexpr(v);
    }
    format_cell(std::string const & v):
        format_cell(format_kind::TEXT) {
        m_value = sexpr(v);
    }
    format_cell(int v):
        format_cell(format_kind::TEXT) {
        m_value = sexpr(v);
    }
    format_cell(double v):
        format_cell(format_kind::TEXT) {
        m_value = sexpr(v);
    }
    format_cell(name const & v):
        format_cell(format_kind::TEXT) {
        m_value = sexpr(v);
    }
    format_cell(mpz const & v):
        format_cell(format_kind::TEXT) {
        m_value = sexpr(v);
    }
    format_cell(mpq const & v):
        format_cell(format_kind::TEXT) {
        m_value = sexpr(v);
    }
    format_cell(format_cell const * h, format_cell const * t):
        format_cell(format_kind::COMPOSE) {
        m_value = sexpr(h->m_value, h->m_value);
    }
};

void format_cell::dealloc() {
    switch (m_kind) {
    case format_kind::NIL:         lean_unreachable();  break;
    case format_kind::INDENT:      delete this;         break;
    case format_kind::COMPOSE:     delete this;         break;
    case format_kind::CHOICE:      delete this;         break;
    case format_kind::LINE:        delete this;         break;
    case format_kind::TEXT:        delete this;         break;
    }
}

format::format(char const * v):m_ptr(new format_cell(v)) {}
format::format(std::string const & v):m_ptr(new format_cell(v)) {}
format::format(int v):m_ptr(new format_cell(v)) {}
format::format(double v):m_ptr(new format_cell(v)) {}
format::format(name const & v):m_ptr(new format_cell(v)) {}
format::format(mpz const & v):m_ptr(new format_cell(v)) {}
format::format(mpq const & v):m_ptr(new format_cell(v)) {}
format::format(format const & h, format const & t):m_ptr(new format_cell(h.m_ptr, t.m_ptr)) {}
format::format(format const & s):m_ptr(s.m_ptr) {
    if (m_ptr)
        m_ptr->inc_ref();
}
format::format(format && s):m_ptr(s.m_ptr) {
    s.m_ptr = 0;
}
format::~format() {
    if (m_ptr)
        m_ptr->dec_ref();
}

format_kind format::kind() const { return m_ptr ? m_ptr->m_kind : format_kind::NIL; }
std::string const & format::get_string() const { return m_ptr->m_value.get_string(); }

unsigned format::hash() const { return m_ptr == nullptr ? 23 : m_ptr->m_value.hash(); }

format & format::operator=(format const & f) {
    if (f.m_ptr)
        f.m_ptr->inc_ref();
    if (m_ptr)
        m_ptr->dec_ref();
    m_ptr = f.m_ptr;
    return *this;
}

format & format::operator=(format && f) {
    if (m_ptr)
        m_ptr->dec_ref();
    m_ptr   = f.m_ptr;
    f.m_ptr = 0;
    return *this;
}

std::ostream & operator<<(std::ostream & out, format const & s) {
    switch (s.kind()) {
    case format_kind::NIL:         out << "nil";  break;
    case format_kind::INDENT:      out << "nil";  break;
    case format_kind::TEXT:        out << "TODO"; break;
    case format_kind::COMPOSE:     out << "TODO"; break;
    case format_kind::CHOICE:      out << "TODO"; break;
    case format_kind::LINE:        out << "TODO"; break;
    }
    return out;
}

}

void pp(lean::format const & n) { std::cout << n << "\n"; }
