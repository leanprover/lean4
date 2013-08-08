/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <cstring>
#include "rc.h"
#include "hash.h"
#include "sexpr.h"
#include "name.h"
#include "mpz.h"
#include "mpq.h"
#include "escaped.h"

namespace lean {
/** \brief Base class used to represent S-expression cells. */
struct sexpr_cell {
    void dealloc();
    MK_LEAN_RC()
    sexpr_kind  m_kind;
    unsigned    m_hash;

    sexpr_cell(sexpr_kind k, unsigned h):m_rc(1), m_kind(k), m_hash(h) {}
};

/** \brief S-expression cell: string atom */
struct sexpr_string : public sexpr_cell {
    std::string m_value;
    sexpr_string(char const * v):
        sexpr_cell(sexpr_kind::STRING, hash_str(strlen(v), v, 13)),
        m_value(v) {}
    sexpr_string(std::string const & v):
        sexpr_cell(sexpr_kind::STRING, hash_str(v.size(), v.c_str(), 13)),
        m_value(v) {}
};

/** \brief S-expression cell: int atom */
struct sexpr_int : public sexpr_cell {
    int m_value;
    sexpr_int(int v):
        sexpr_cell(sexpr_kind::INT, v),
        m_value(v) {}
};

/** \brief S-expression cell: bool atom */
struct sexpr_bool : public sexpr_cell {
    bool m_value;
    sexpr_bool(bool v):
        sexpr_cell(sexpr_kind::BOOL, v),
        m_value(v) {}
};

/** \brief S-expression cell: double atom */
struct sexpr_double : public sexpr_cell {
    double m_value;
    sexpr_double(double v):
        sexpr_cell(sexpr_kind::DOUBLE, static_cast<unsigned>(v)),
        m_value(v) {}
};

/** \brief S-expression cell: hierarchical name atom */
struct sexpr_name : public sexpr_cell {
    name m_value;
    sexpr_name(name const & v):
        sexpr_cell(sexpr_kind::NAME, v.hash()),
        m_value(v) {}
};

/** \brief S-expression cell: multi-precision integer atom */
struct sexpr_mpz : public sexpr_cell {
    mpz m_value;
    sexpr_mpz(mpz const & v):
        sexpr_cell(sexpr_kind::MPZ, v.hash()),
        m_value(v) {}
};

/** \brief S-expression cell: multi-precision rational atom */
struct sexpr_mpq : public sexpr_cell {
    mpq m_value;
    sexpr_mpq(mpq const & v):
        sexpr_cell(sexpr_kind::MPQ, v.hash()),
        m_value(v) {}
};

/** \brief S-expression cell: cons cell (aka pair) */
struct sexpr_cons : public sexpr_cell {
    sexpr m_head;
    sexpr m_tail;
    sexpr_cons(sexpr const & h, sexpr const & t):
        sexpr_cell(sexpr_kind::CONS, hash(h.hash(), t.hash())),
        m_head(h),
        m_tail(t) {}
};

void sexpr_cell::dealloc() {
    switch (m_kind) {
    case sexpr_kind::NIL:         lean_unreachable();                      break;
    case sexpr_kind::STRING:      delete static_cast<sexpr_string*>(this); break;
    case sexpr_kind::BOOL:        delete static_cast<sexpr_bool*>(this);   break;
    case sexpr_kind::INT:         delete static_cast<sexpr_int*>(this);    break;
    case sexpr_kind::DOUBLE:      delete static_cast<sexpr_double*>(this); break;
    case sexpr_kind::NAME:        delete static_cast<sexpr_name*>(this);   break;
    case sexpr_kind::MPZ:         delete static_cast<sexpr_mpz*>(this);    break;
    case sexpr_kind::MPQ:         delete static_cast<sexpr_mpq*>(this);    break;
    case sexpr_kind::CONS:        delete static_cast<sexpr_cons*>(this);   break;
    }
}

sexpr::sexpr(char const * v):m_ptr(new sexpr_string(v)) {}
sexpr::sexpr(std::string const & v):m_ptr(new sexpr_string(v)) {}
sexpr::sexpr(bool v):m_ptr(new sexpr_bool(v)) {}
sexpr::sexpr(int v):m_ptr(new sexpr_int(v)) {}
sexpr::sexpr(double v):m_ptr(new sexpr_double(v)) {}
sexpr::sexpr(name const & v):m_ptr(new sexpr_name(v)) {}
sexpr::sexpr(mpz const & v):m_ptr(new sexpr_mpz(v)) {}
sexpr::sexpr(mpq const & v):m_ptr(new sexpr_mpq(v)) {}
sexpr::sexpr(sexpr const & h, sexpr const & t):m_ptr(new sexpr_cons(h, t)) {}
sexpr::sexpr(sexpr const & s):m_ptr(s.m_ptr) {
    if (m_ptr)
        m_ptr->inc_ref();
}
sexpr::sexpr(sexpr && s):m_ptr(s.m_ptr) {
    s.m_ptr = nullptr;
}
sexpr::~sexpr() {
    if (m_ptr)
        m_ptr->dec_ref();
}

sexpr_kind sexpr::kind() const { return m_ptr ? m_ptr->m_kind : sexpr_kind::NIL; }
sexpr const & head(sexpr const & s) { lean_assert(is_cons(s)); return static_cast<sexpr_cons*>(s.m_ptr)->m_head; }
sexpr const & tail(sexpr const & s) { lean_assert(is_cons(s)); return static_cast<sexpr_cons*>(s.m_ptr)->m_tail; }
std::string const & sexpr::get_string() const { return static_cast<sexpr_string*>(m_ptr)->m_value; }
bool sexpr::get_bool() const { return static_cast<sexpr_bool*>(m_ptr)->m_value; }
int sexpr::get_int() const { return static_cast<sexpr_int*>(m_ptr)->m_value; }
double sexpr::get_double() const { return static_cast<sexpr_double*>(m_ptr)->m_value; }
name const & sexpr::get_name() const { return static_cast<sexpr_name*>(m_ptr)->m_value; }
mpz const & sexpr::get_mpz() const { return static_cast<sexpr_mpz*>(m_ptr)->m_value; }
mpq const & sexpr::get_mpq() const { return static_cast<sexpr_mpq*>(m_ptr)->m_value; }

unsigned sexpr::hash() const { return m_ptr == nullptr ? 23 : m_ptr->m_hash; }

sexpr & sexpr::operator=(sexpr const & s) { LEAN_COPY_REF(sexpr, s); }
sexpr & sexpr::operator=(sexpr && s) { LEAN_MOVE_REF(sexpr, s); }

bool is_list(sexpr const & s) {
    if (is_nil(s))
        return true;
    if (!is_cons(s))
        return false;
    sexpr const * curr = &s;
    while (true) {
        lean_assert(is_cons(*curr));
        curr = &tail(*curr);
        if (is_nil(*curr))
            return true;
        if (!is_cons(*curr))
            return false;
    }
}

unsigned length(sexpr const & s) {
    unsigned r = 0;
    sexpr const * curr = &s;
    while (true) {
        if (is_nil(*curr))
            return r;
        lean_assert(is_cons(*curr));
        r++;
        curr = &tail(*curr);
    }
}

bool operator==(sexpr const & a, sexpr const & b) {
    if (eqp(a, b))
        return true;
    sexpr_kind ka = a.kind();
    sexpr_kind kb = b.kind();
    if (ka != kb)
        return false;
    if (a.hash() != b.hash())
        return false;
    switch (ka) {
    case sexpr_kind::NIL:         return true;
    case sexpr_kind::STRING:      return to_string(a) == to_string(b);
    case sexpr_kind::BOOL:        return to_bool(a) == to_bool(b);
    case sexpr_kind::INT:         return to_int(a) == to_int(b);
    case sexpr_kind::DOUBLE:      return to_double(a) == to_double(b);
    case sexpr_kind::NAME:        return to_name(a) == to_name(b);
    case sexpr_kind::MPZ:         return to_mpz(a) == to_mpz(b);
    case sexpr_kind::MPQ:         return to_mpq(a) == to_mpq(b);
    case sexpr_kind::CONS:        return head(a) == head(b) && tail(a) == tail(b);
    }
    return false;
}

int cmp(sexpr const & a, sexpr const & b) {
    if (eqp(a, b))
        return 0;
    sexpr_kind ka = a.kind();
    sexpr_kind kb = b.kind();
    if (ka != kb)
        return ka < kb ? -1 : 1;
    if (a.hash() == b.hash()) {
        if (a == b)
            return 0;
    }
    switch (ka) {
    case sexpr_kind::NIL:         return 0;
    case sexpr_kind::STRING:      return strcmp(to_string(a).c_str(), to_string(b).c_str());
    case sexpr_kind::BOOL:        return to_bool(a) == to_bool(b) ? 0 : (!to_bool(a) && to_bool(b) ? -1 : 1);
    case sexpr_kind::INT:         return to_int(a) == to_int(b) ? 0 : (to_int(a) < to_int(b) ? -1 : 1);
    case sexpr_kind::DOUBLE:      return to_double(a) == to_double(b) ? 0 : (to_double(a) < to_double(b) ? -1 : 1);
    case sexpr_kind::NAME:        return cmp(to_name(a), to_name(b));
    case sexpr_kind::MPZ:         return cmp(to_mpz(a), to_mpz(b));
    case sexpr_kind::MPQ:         return cmp(to_mpq(a), to_mpq(b));
    case sexpr_kind::CONS:        {
        int r = cmp(head(a), head(b));
        if (r != 0)
            return r;
        return cmp(tail(a), tail(b));
    }}
    return 0;
}

std::ostream & operator<<(std::ostream & out, sexpr const & s) {
    switch (s.kind()) {
    case sexpr_kind::NIL:         out << "nil"; break;
    case sexpr_kind::STRING:      out << "\"" << escaped(to_string(s).c_str()) << "\""; break;
    case sexpr_kind::BOOL:        out << (to_bool(s) ? "true" : "false"); break;
    case sexpr_kind::INT:         out << to_int(s); break;
    case sexpr_kind::DOUBLE:      out << to_double(s); break;
    case sexpr_kind::NAME:        out << to_name(s); break;
    case sexpr_kind::MPZ:         out << to_mpz(s); break;
    case sexpr_kind::MPQ:         out << to_mpq(s); break;
    case sexpr_kind::CONS: {
        out << "(";
        sexpr const * curr = &s;
        while (true) {
            out << head(*curr);
            curr = &tail(*curr);
            if (is_nil(*curr)) {
                break;
            } else if (!is_cons(*curr)) {
                out << " . ";
                out << *curr;
                break;
            } else {
                out << " ";
            }
        }
        out << ")";
    }}
    return out;
}

bool operator==(sexpr const & a, name const & b) { return is_name(a) && to_name(a) == b; }
bool operator==(sexpr const & a, mpz const & b) { return is_mpz(a) && to_mpz(a) == b; }
bool operator==(sexpr const & a, mpq const & b) { return is_mpq(a) && to_mpq(a) == b; }

}

void print(lean::sexpr const & n) { std::cout << n << "\n"; }
