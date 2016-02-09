/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <sstream>
#include <cstring>
#include <string>
#include "util/rc.h"
#include "util/hash.h"
#include "util/name.h"
#include "util/escaped.h"
#include "util/buffer.h"
#include "util/sstream.h"
#include "util/object_serializer.h"
#include "util/numerics/mpz.h"
#include "util/numerics/mpq.h"
#include "util/sexpr/sexpr.h"

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
        sexpr_cell(sexpr_kind::String, hash_str(strlen(v), v, 13)),
        m_value(v) {}
    sexpr_string(std::string const & v):
        sexpr_cell(sexpr_kind::String, hash_str(v.size(), v.c_str(), 13)),
        m_value(v) {}
};

/** \brief S-expression cell: int atom */
struct sexpr_int : public sexpr_cell {
    int m_value;
    sexpr_int(int v):
        sexpr_cell(sexpr_kind::Int, v),
        m_value(v) {}
};

/** \brief S-expression cell: bool atom */
struct sexpr_bool : public sexpr_cell {
    bool m_value;
    sexpr_bool(bool v):
        sexpr_cell(sexpr_kind::Bool, v),
        m_value(v) {}
};

/** \brief S-expression cell: double atom */
struct sexpr_double : public sexpr_cell {
    double m_value;
    sexpr_double(double v):
        sexpr_cell(sexpr_kind::Double, static_cast<unsigned>(v)),
        m_value(v) {}
};

/** \brief S-expression cell: hierarchical name atom */
struct sexpr_name : public sexpr_cell {
    name m_value;
    sexpr_name(name const & v):
        sexpr_cell(sexpr_kind::Name, v.hash()),
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

/** \brief S-expression cell: external atom */
struct sexpr_ext : public sexpr_cell {
    std::unique_ptr<sexpr_ext_atom> m_value;
    sexpr_ext(std::unique_ptr<sexpr_ext_atom> && v):
        sexpr_cell(sexpr_kind::Ext, v->hash()),
        m_value(std::move(v)) {
        lean_assert(m_value);
    }
};

/** \brief S-expression cell: cons cell (aka pair) */
struct sexpr_cons : public sexpr_cell {
    sexpr m_head;
    sexpr m_tail;
    sexpr_cons(sexpr const & h, sexpr const & t):
        sexpr_cell(sexpr_kind::Cons, hash(h.hash(), t.hash())),
        m_head(h),
        m_tail(t) {}

    void dealloc_cons() {
        buffer<sexpr_cons *> tmp;
        try {
            tmp.push_back(this);
            while (!tmp.empty()) {
                sexpr_cons * it = tmp.back();
                tmp.pop_back();
                sexpr_cell * head = it->m_head.steal_ptr();
                sexpr_cell * tail = it->m_tail.steal_ptr();
                delete it;
                if (head && head->dec_ref_core()) {
                    if (head->m_kind == sexpr_kind::Cons)
                        tmp.push_back(static_cast<sexpr_cons*>(head));
                    else
                        head->dealloc();
                }
                if (tail && tail->dec_ref_core()) {
                    if (tail->m_kind == sexpr_kind::Cons)
                        tmp.push_back(static_cast<sexpr_cons*>(tail));
                    else
                        tail->dealloc();
                }
            }
        } catch (std::bad_alloc &) {
            // We need this catch, because push_back may fail when expanding the buffer size.
            // In this case, we avoid the crash, and "accept" the memory leak.
        }
    }
};

void sexpr_cell::dealloc() {
    switch (m_kind) {
    case sexpr_kind::Nil:         lean_unreachable(); // LCOV_EXCL_LINE
    case sexpr_kind::String:      delete static_cast<sexpr_string*>(this); break;
    case sexpr_kind::Bool:        delete static_cast<sexpr_bool*>(this);   break;
    case sexpr_kind::Int:         delete static_cast<sexpr_int*>(this);    break;
    case sexpr_kind::Double:      delete static_cast<sexpr_double*>(this); break;
    case sexpr_kind::Name:        delete static_cast<sexpr_name*>(this);   break;
    case sexpr_kind::MPZ:         delete static_cast<sexpr_mpz*>(this);    break;
    case sexpr_kind::MPQ:         delete static_cast<sexpr_mpq*>(this);    break;
    case sexpr_kind::Ext:         delete static_cast<sexpr_ext*>(this);    break;
    case sexpr_kind::Cons:        static_cast<sexpr_cons*>(this)->dealloc_cons(); break;
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
sexpr::sexpr(std::unique_ptr<sexpr_ext_atom> && v):m_ptr(new sexpr_ext(std::move(v))) {}
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

sexpr_kind sexpr::kind() const { return m_ptr ? m_ptr->m_kind : sexpr_kind::Nil; }
sexpr const & head(sexpr const & s) { lean_assert(is_cons(s)); return static_cast<sexpr_cons*>(s.m_ptr)->m_head; }
sexpr const & tail(sexpr const & s) { lean_assert(is_cons(s)); return static_cast<sexpr_cons*>(s.m_ptr)->m_tail; }
std::string const & sexpr::get_string() const { return static_cast<sexpr_string*>(m_ptr)->m_value; }
bool sexpr::get_bool() const { return static_cast<sexpr_bool*>(m_ptr)->m_value; }
int sexpr::get_int() const { return static_cast<sexpr_int*>(m_ptr)->m_value; }
double sexpr::get_double() const { return static_cast<sexpr_double*>(m_ptr)->m_value; }
name const & sexpr::get_name() const { return static_cast<sexpr_name*>(m_ptr)->m_value; }
mpz const & sexpr::get_mpz() const { return static_cast<sexpr_mpz*>(m_ptr)->m_value; }
mpq const & sexpr::get_mpq() const { return static_cast<sexpr_mpq*>(m_ptr)->m_value; }
sexpr_ext_atom const & sexpr::get_ext() const { return *static_cast<sexpr_ext*>(m_ptr)->m_value; }

unsigned sexpr::hash() const { return m_ptr == nullptr ? 23 : m_ptr->m_hash; }

sexpr & sexpr::operator=(sexpr const & s) { LEAN_COPY_REF(s); }
sexpr & sexpr::operator=(sexpr && s) { LEAN_MOVE_REF(s); }

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
    if (is_eqp(a, b))
        return true;
    sexpr_kind ka = a.kind();
    sexpr_kind kb = b.kind();
    if (ka != kb)
        return false;
    if (a.hash() != b.hash())
        return false;
    switch (ka) {
    case sexpr_kind::Nil:         return true;
    case sexpr_kind::String:      return to_string(a) == to_string(b);
    case sexpr_kind::Bool:        return to_bool(a) == to_bool(b);
    case sexpr_kind::Int:         return to_int(a) == to_int(b);
    case sexpr_kind::Double:      return to_double(a) == to_double(b);
    case sexpr_kind::Name:        return to_name(a) == to_name(b);
    case sexpr_kind::MPZ:         return to_mpz(a) == to_mpz(b);
    case sexpr_kind::MPQ:         return to_mpq(a) == to_mpq(b);
    case sexpr_kind::Ext:         return to_ext(a).cmp(to_ext(b)) == 0;
    case sexpr_kind::Cons:        return head(a) == head(b) && tail(a) == tail(b);
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

int cmp(sexpr const & a, sexpr const & b) {
    if (is_eqp(a, b))
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
    case sexpr_kind::Nil:         return 0;
    case sexpr_kind::String:      return strcmp(to_string(a).c_str(), to_string(b).c_str());
    case sexpr_kind::Bool:        return to_bool(a) == to_bool(b) ? 0 : (!to_bool(a) && to_bool(b) ? -1 : 1);
    case sexpr_kind::Int:         return to_int(a) == to_int(b) ? 0 : (to_int(a) < to_int(b) ? -1 : 1);
    case sexpr_kind::Double:      return to_double(a) == to_double(b) ? 0 : (to_double(a) < to_double(b) ? -1 : 1);
    case sexpr_kind::Name:        return cmp(to_name(a), to_name(b));
    case sexpr_kind::MPZ:         return cmp(to_mpz(a), to_mpz(b));
    case sexpr_kind::MPQ:         return cmp(to_mpq(a), to_mpq(b));
    case sexpr_kind::Ext:         return to_ext(a).cmp(to_ext(b));
    case sexpr_kind::Cons:        {
        int r = cmp(head(a), head(b));
        if (r != 0)
            return r;
        return cmp(tail(a), tail(b));
    }}
    lean_unreachable(); // LCOV_EXCL_LINE
}

std::ostream & operator<<(std::ostream & out, sexpr const & s) {
    switch (s.kind()) {
    case sexpr_kind::Nil:         out << "nil"; break;
    case sexpr_kind::String:      out << "\"" << escaped(to_string(s).c_str()) << "\""; break;
    case sexpr_kind::Bool:        out << (to_bool(s) ? "true" : "false"); break;
    case sexpr_kind::Int:         out << to_int(s); break;
    case sexpr_kind::Double:      out << to_double(s); break;
    case sexpr_kind::Name:        out << to_name(s); break;
    case sexpr_kind::MPZ:         out << to_mpz(s); break;
    case sexpr_kind::MPQ:         out << to_mpq(s); break;
    case sexpr_kind::Ext:         to_ext(s).display(out); break;
    case sexpr_kind::Cons: {
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

class sexpr_serializer : public object_serializer<sexpr, sexpr::ptr_hash, sexpr::ptr_eq> {
    typedef object_serializer<sexpr, sexpr::ptr_hash, sexpr::ptr_eq> super;
public:
    void write(sexpr const & a) {
        super::write(a, [&]() {
                serializer & s = get_owner();
                auto k = a.kind();
                s << static_cast<char>(k);
                switch (k) {
                case sexpr_kind::Nil:                                  break;
                case sexpr_kind::String: s << to_string(a);            break;
                case sexpr_kind::Bool:   s << to_bool(a);              break;
                case sexpr_kind::Int:    s << to_int(a);               break;
                case sexpr_kind::Double: s << to_double(a);            break;
                case sexpr_kind::Name:   s << to_name(a);              break;
                case sexpr_kind::MPZ:    s << to_mpz(a);               break;
                case sexpr_kind::MPQ:    s << to_mpq(a);               break;
                case sexpr_kind::Cons:   write(car(a)); write(cdr(a)); break;
                case sexpr_kind::Ext:
                    throw exception("s-expressions constaining external atoms cannot be serialized");
                }
            });
    }
};

class sexpr_deserializer : public object_deserializer<sexpr> {
    typedef object_deserializer<sexpr> super;
public:
    sexpr read() {
        return super::read([&]() {
                deserializer & d = get_owner();
                auto k = static_cast<sexpr_kind>(d.read_char());
                switch (k) {
                case sexpr_kind::Nil:    return sexpr();
                case sexpr_kind::String: return sexpr(d.read_string());
                case sexpr_kind::Bool:   return sexpr(d.read_bool());
                case sexpr_kind::Int:    return sexpr(d.read_int());
                case sexpr_kind::Double: return sexpr(d.read_double());
                case sexpr_kind::Name:   return sexpr(read_name(d));
                case sexpr_kind::MPZ:    return sexpr(read_mpz(d));
                case sexpr_kind::MPQ:    return sexpr(read_mpq(d));
                case sexpr_kind::Ext:    lean_unreachable(); // LCOV_EXCL_LINE
                case sexpr_kind::Cons:   {
                    sexpr h = read();
                    sexpr t = read();
                    return sexpr(h, t);
                }}
                throw corrupted_stream_exception();
            });
    }
};

struct sexpr_sd {
    unsigned m_s_extid;
    unsigned m_d_extid;
    sexpr_sd() {
        m_s_extid = serializer::register_extension([](){ return std::unique_ptr<serializer::extension>(new sexpr_serializer()); });
        m_d_extid = deserializer::register_extension([](){ return std::unique_ptr<deserializer::extension>(new sexpr_deserializer()); });
    }
};
static sexpr_sd * g_sexpr_sd = nullptr;

void initialize_sexpr() {
    g_sexpr_sd = new sexpr_sd();
}

void finalize_sexpr() {
    delete g_sexpr_sd;
}

serializer & operator<<(serializer & s, sexpr const & n) {
    s.get_extension<sexpr_serializer>(g_sexpr_sd->m_s_extid).write(n);
    return s;
}

sexpr read_sexpr(deserializer & d) {
    return d.get_extension<sexpr_deserializer>(g_sexpr_sd->m_d_extid).read();
}
}

void print(lean::sexpr const & n) { std::cout << n << "\n"; }
