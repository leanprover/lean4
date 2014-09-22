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
#include "util/luaref.h"
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

DECL_UDATA(sexpr)

class lua_sexpr_atom : public sexpr_ext_atom {
    luaref m_ref;
public:
    lua_sexpr_atom(luaref && r):m_ref(r) {}
    virtual ~lua_sexpr_atom() {}
    virtual int cmp(sexpr_ext_atom const & e) const {
        if (dynamic_cast<lua_sexpr_atom const *>(&e) == nullptr) {
            return strcmp(typeid(*this).name(), typeid(e).name());
        } else {
            luaref other  = static_cast<lua_sexpr_atom const &>(e).m_ref;
            lua_State * L = m_ref.get_state();
            if (other.get_state() != L)
                throw exception("missing Lua objects from different Lua states");
            m_ref.push();
            other.push();
            int r;
            if (equal(L, -2, -1))
                r = 0;
            else if (lessthan(L, -2, -1))
                r = -1;
            else
                r = 0;
            lua_pop(L, 2);
            return r;
        }
    }

    virtual unsigned hash() const {
        lua_State * L = m_ref.get_state();
        m_ref.push();
        lua_getfield(L, -1, "hash");
        if (lua_isnil(L, -1)) {
            lua_pop(L, 2);
            return 0;
        } else {
            m_ref.push();
            pcall(L, 1, 1, 0);
            if (lua_isnumber(L, -1)) {
                unsigned r = lua_tointeger(L, -1);
                lua_pop(L, 1);
                return r;
            } else {
                lua_pop(L, 1);
                return 0;
            }
        }
    }

    virtual int push_lua(lua_State * L) const {
        if (m_ref.get_state() != L)
            throw exception("using Lua object in a different Lua state");
        m_ref.push();
        return 1;
    }

    virtual void display(std::ostream & out) const {
        lua_State * L = m_ref.get_state();
        m_ref.push();
        out << tostring(L, -1);
        lua_pop(L, 1);
    }
};


static int sexpr_tostring(lua_State * L) {
    std::ostringstream out;
    out << to_sexpr(L, 1);
    return push_string(L, out.str().c_str());
}

static sexpr to_sexpr_elem(lua_State * L, int idx) {
    if (lua_isnil(L, idx)) {
        return sexpr();
    } else if (lua_isboolean(L, idx)) {
        return sexpr(static_cast<bool>(lua_toboolean(L, idx)));
    } else if (lua_isnumber(L, idx)) {
        // Remark: we convert to integer by default
        return sexpr(static_cast<int>(lua_tointeger(L, idx)));
    } else if (is_name(L, idx)) {
        return sexpr(to_name(L, idx));
    } else if (is_sexpr(L, idx)) {
        return *static_cast<sexpr*>(lua_touserdata(L, idx));
    } else if (is_mpz(L, idx)) {
        return sexpr(to_mpz(L, idx));
    } else if (is_mpq(L, idx)) {
        return sexpr(to_mpq(L, idx));
    } else if (lua_isstring(L, idx)) {
        std::string str = lua_tostring(L, idx);
        return sexpr(str);
    } else {
        return sexpr(std::unique_ptr<sexpr_ext_atom>(new lua_sexpr_atom(luaref(L, idx))));
    }
}

static int mk_sexpr(lua_State * L) {
    sexpr r;
    int nargs = lua_gettop(L);
    if (nargs == 0) {
        r = sexpr();
    } else {
        int i = nargs;
        r = to_sexpr_elem(L, i);
        i--;
        for (; i >= 1; i--) {
            r = sexpr(to_sexpr_elem(L, i), r);
        }
    }
    return push_sexpr(L, r);
}

static int sexpr_eq(lua_State * L)        { return push_boolean(L, to_sexpr(L, 1) == to_sexpr(L, 2)); }
static int sexpr_lt(lua_State * L)        { return push_boolean(L, to_sexpr(L, 1) < to_sexpr(L, 2)); }

#define SEXPR_PRED(P) static int sexpr_ ## P(lua_State * L) { check_num_args(L, 1); return push_boolean(L, P(to_sexpr(L, 1))); }

SEXPR_PRED(is_nil)
SEXPR_PRED(is_cons)
SEXPR_PRED(is_list)
SEXPR_PRED(is_atom)
SEXPR_PRED(is_string)
SEXPR_PRED(is_bool)
SEXPR_PRED(is_int)
SEXPR_PRED(is_double)
SEXPR_PRED(is_name)
SEXPR_PRED(is_mpz)
SEXPR_PRED(is_mpq)
SEXPR_PRED(is_external)

static int sexpr_length(lua_State * L) {
    sexpr const & e = to_sexpr(L, 1);
    if (!is_list(e))
        throw exception("s-expression is not a list");
    return push_integer(L, length(e));
}

static int sexpr_head(lua_State * L) {
    sexpr const & e = to_sexpr(L, 1);
    if (!is_cons(e))
        throw exception("s-expression is not a cons cell");
    return push_sexpr(L, head(e));
}

static int sexpr_tail(lua_State * L) {
    sexpr const & e = to_sexpr(L, 1);
    if (!is_cons(e))
        throw exception("s-expression is not a cons cell");
    return push_sexpr(L, tail(e));
}

static int sexpr_to_bool(lua_State * L) {
    sexpr const & e = to_sexpr(L, 1);
    if (!is_bool(e))
        throw exception("s-expression is not a Boolean");
    return push_boolean(L, to_bool(e));
}

static int sexpr_to_string(lua_State * L) {
    sexpr const & e = to_sexpr(L, 1);
    if (!is_string(e))
        throw exception("s-expression is not a string");
    return push_string(L, to_string(e).c_str());
}

static int sexpr_to_int(lua_State * L) {
    sexpr const & e = to_sexpr(L, 1);
    if (!is_int(e))
        throw exception("s-expression is not an integer");
    return push_integer(L, to_int(e));
}

static int sexpr_to_double(lua_State * L) {
    sexpr const & e = to_sexpr(L, 1);
    if (!is_double(e))
        throw exception("s-expression is not a double");
    return push_number(L, to_double(e));
}

static int sexpr_to_name(lua_State * L) {
    sexpr const & e = to_sexpr(L, 1);
    if (!is_name(e))
        throw exception("s-expression is not a name");
    return push_name(L, to_name(e));
}

static int sexpr_to_mpz(lua_State * L) {
    sexpr const & e = to_sexpr(L, 1);
    if (!is_mpz(e))
        throw exception("s-expression is not a multi-precision integer");
    return push_mpz(L, to_mpz(e));
}

static int sexpr_to_mpq(lua_State * L) {
    sexpr const & e = to_sexpr(L, 1);
    if (!is_mpq(e))
        throw exception("s-expression is not a multi-precision rational");
    return push_mpq(L, to_mpq(e));
}

static int sexpr_to_external(lua_State * L) {
    sexpr const & e = to_sexpr(L, 1);
    if (!is_external(e))
        throw exception("s-expression is not an external atom");
    return to_ext(e).push_lua(L);
}

static int sexpr_get_kind(lua_State * L) {
    return push_integer(L, static_cast<int>(to_sexpr(L, 1).kind()));
}

static int sexpr_fields(lua_State * L) {
    sexpr const & e = to_sexpr(L, 1);
    switch (e.kind()) {
    case sexpr_kind::Nil:         return 0;
    case sexpr_kind::String:      return sexpr_to_string(L);
    case sexpr_kind::Bool:        return sexpr_to_bool(L);
    case sexpr_kind::Int:         return sexpr_to_int(L);
    case sexpr_kind::Double:      return sexpr_to_double(L);
    case sexpr_kind::Name:        return sexpr_to_name(L);
    case sexpr_kind::MPZ:         return sexpr_to_mpz(L);
    case sexpr_kind::MPQ:         return sexpr_to_mpq(L);
    case sexpr_kind::Ext:         return sexpr_to_external(L);
    case sexpr_kind::Cons:        sexpr_head(L); sexpr_tail(L); return 2;
    }
    lean_unreachable(); // LCOV_EXCL_LINE
    return 0;           // LCOV_EXCL_LINE
}

static const struct luaL_Reg sexpr_m[] = {
    {"__gc",        sexpr_gc}, // never throws
    {"__tostring",  safe_function<sexpr_tostring>},
    {"__eq",        safe_function<sexpr_eq>},
    {"__lt",        safe_function<sexpr_lt>},
    {"kind",        safe_function<sexpr_get_kind>},
    {"is_nil",      safe_function<sexpr_is_nil>},
    {"is_cons",     safe_function<sexpr_is_cons>},
    {"is_pair",     safe_function<sexpr_is_cons>},
    {"is_list",     safe_function<sexpr_is_list>},
    {"is_atom",     safe_function<sexpr_is_atom>},
    {"is_string",   safe_function<sexpr_is_string>},
    {"is_bool",     safe_function<sexpr_is_bool>},
    {"is_int",      safe_function<sexpr_is_int>},
    {"is_double",   safe_function<sexpr_is_double>},
    {"is_name",     safe_function<sexpr_is_name>},
    {"is_mpz",      safe_function<sexpr_is_mpz>},
    {"is_mpq",      safe_function<sexpr_is_mpq>},
    {"is_external", safe_function<sexpr_is_external>},
    {"head",        safe_function<sexpr_head>},
    {"tail",        safe_function<sexpr_tail>},
    {"length",      safe_function<sexpr_length>},
    {"to_bool",     safe_function<sexpr_to_bool>},
    {"to_string",   safe_function<sexpr_to_string>},
    {"to_int",      safe_function<sexpr_to_int>},
    {"to_double",   safe_function<sexpr_to_double>},
    {"to_name",     safe_function<sexpr_to_name>},
    {"to_mpz",      safe_function<sexpr_to_mpz>},
    {"to_mpq",      safe_function<sexpr_to_mpq>},
    {"to_external", safe_function<sexpr_to_external>},
    {"fields",      safe_function<sexpr_fields>},
    {0, 0}
};

void open_sexpr(lua_State * L) {
    luaL_newmetatable(L, sexpr_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, sexpr_m, 0);

    SET_GLOBAL_FUN(mk_sexpr,   "sexpr");
    SET_GLOBAL_FUN(sexpr_pred, "is_sexpr");

    lua_newtable(L);
    SET_ENUM("Nil",         sexpr_kind::Nil);
    SET_ENUM("String",      sexpr_kind::String);
    SET_ENUM("Bool",        sexpr_kind::Bool);
    SET_ENUM("Int",         sexpr_kind::Int);
    SET_ENUM("Double",      sexpr_kind::Double);
    SET_ENUM("Name",        sexpr_kind::Name);
    SET_ENUM("MPZ",         sexpr_kind::MPZ);
    SET_ENUM("MPQ",         sexpr_kind::MPQ);
    SET_ENUM("Cons",        sexpr_kind::Cons);
    SET_ENUM("Ext",         sexpr_kind::Ext);
    lua_setglobal(L, "sexpr_kind");
}
}

void print(lean::sexpr const & n) { std::cout << n << "\n"; }
