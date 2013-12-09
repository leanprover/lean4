/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <cstring>
#include <vector>
#include <algorithm>
#include <sstream>
#include <string>
#include "util/thread.h"
#include "util/name.h"
#include "util/sstream.h"
#include "util/debug.h"
#include "util/rc.h"
#include "util/buffer.h"
#include "util/hash.h"
#include "util/trace.h"
#include "util/ascii.h"

namespace lean {
constexpr char const * anonymous_str = "[anonymous]";

/**
   \brief Actual implementation of hierarchical names.
*/
struct name::imp {
    MK_LEAN_RC()
    bool     m_is_string;
    unsigned m_hash;
    imp *    m_prefix;
    union {
        char * m_str;
        unsigned m_k;
    };

    void dealloc() {
        imp * curr = this;
        while (true) {
            lean_assert(curr->get_rc() == 0);
            imp * p = curr->m_prefix;
            if (curr->m_is_string)
                delete[] reinterpret_cast<char*>(curr);
            else
                delete curr;
            curr = p;
            if (!curr || !curr->dec_ref_core())
                break;
        }
    }

    imp(bool s, imp * p):m_rc(1), m_is_string(s), m_hash(0), m_prefix(p) { if (p) p->inc_ref(); }

    static void display_core(std::ostream & out, imp * p) {
        lean_assert(p != nullptr);
        if (p->m_prefix) {
            display_core(out, p->m_prefix);
            out << lean_name_separator;
        }
        if (p->m_is_string)
            out << p->m_str;
        else
            out << p->m_k;
    }

    static void display(std::ostream & out, imp * p) {
        if (p == nullptr)
            out << anonymous_str;
        else
            display_core(out, p);
    }

    friend void copy_limbs(imp * p, buffer<name::imp *> & limbs) {
        limbs.clear();
        while (p != nullptr) {
            limbs.push_back(p);
            p = p->m_prefix;
        }
        std::reverse(limbs.begin(), limbs.end());
    }
};

name::name(imp * p) {
    m_ptr = p;
    if (m_ptr)
        m_ptr->inc_ref();
}

name::name() {
    m_ptr = nullptr;
}

name::name(name const & prefix, char const * name) {
    size_t sz  = strlen(name);
    lean_assert(sz < (1u << 31));
    char * mem = new char[sizeof(imp) + sz + 1];
    m_ptr      = new (mem) imp(true, prefix.m_ptr);
    std::memcpy(mem + sizeof(imp), name, sz + 1);
    m_ptr->m_str       = mem + sizeof(imp);
    if (m_ptr->m_prefix)
        m_ptr->m_hash = hash_str(sz, name, m_ptr->m_prefix->m_hash);
    else
        m_ptr->m_hash = hash_str(sz, name, 0);
}

name::name(name const & prefix, unsigned k, bool) {
    m_ptr      = new imp(false, prefix.m_ptr);
    m_ptr->m_k = k;
    if (m_ptr->m_prefix)
        m_ptr->m_hash = ::lean::hash(m_ptr->m_prefix->m_hash, k);
    else
        m_ptr->m_hash = k;
}

name::name(name const & prefix, unsigned k):name(prefix, k, true) {
    lean_assert(prefix.m_ptr);
}

name::name(char const * n):name(name(), n) {
}

name::name(unsigned k):name(name(), k, true) {
}

name::name(name const & other):m_ptr(other.m_ptr) {
    if (m_ptr)
        m_ptr->inc_ref();
}

name::name(name && other):m_ptr(other.m_ptr) {
    other.m_ptr = nullptr;
}

name::name(std::initializer_list<char const *> const & l):name() {
    if (l.size() == 0) {
        return;
    } else {
        auto it = l.begin();
        *this = name(*it);
        ++it;
        for (; it != l.end(); ++it)
            *this = name(*this, *it);
    }
}

name::~name() {
    if (m_ptr)
        m_ptr->dec_ref();
}

static name g_anonymous;

name const & name::anonymous() {
    lean_assert(g_anonymous.is_anonymous());
    return g_anonymous;
}

static atomic<unsigned> g_next_id(0);

name name::mk_internal_unique_name() {
    unsigned id = g_next_id++;
    return name(id);
}

name & name::operator=(name const & other) { LEAN_COPY_REF(name, other); }

name & name::operator=(name && other) { LEAN_MOVE_REF(name, other); }

name_kind name::kind() const {
    if (m_ptr == nullptr)
        return name_kind::ANONYMOUS;
    else
        return m_ptr->m_is_string ? name_kind::STRING : name_kind::NUMERAL;
}

unsigned name::get_numeral() const {
    lean_assert(is_numeral());
    return m_ptr->m_k;
}

char const * name::get_string() const {
    lean_assert(is_string());
    return m_ptr->m_str;
}

bool operator==(name const & a, name const & b) {
    name::imp * i1 = a.m_ptr;
    name::imp * i2 = b.m_ptr;
    while (true) {
        if (i1 == i2)
            return true;
        if ((i1 == nullptr) != (i2 == nullptr))
            return false;
        if (i1->m_hash != i2->m_hash)
            return false;
        lean_assert(i1 != nullptr);
        lean_assert(i2 != nullptr);
        if (i1->m_is_string != i2->m_is_string)
            return false;
        if (i1->m_is_string) {
            if (strcmp(i1->m_str, i2->m_str) != 0)
                return false;
        } else {
            if (i1->m_k != i2->m_k)
                return false;
        }
        i1 = i1->m_prefix;
        i2 = i2->m_prefix;
    }
}

bool is_prefix_of(name const & n1, name const & n2) {
    buffer<name::imp*> limbs1, limbs2;
    name::imp* i1 = n1.m_ptr;
    name::imp* i2 = n2.m_ptr;
    copy_limbs(i1, limbs1);
    copy_limbs(i2, limbs2);
    unsigned sz1 = limbs1.size();
    unsigned sz2 = limbs2.size();
    if (sz1 > sz2)
        return false;
    else if (sz1 == sz2 && n1.hash() != n2.hash())
        return false;
    auto it1 = limbs1.begin();
    auto it2 = limbs2.begin();
    for (; it1 != limbs1.end(); ++it1, ++it2) {
        i1 = *it1;
        i2 = *it2;
        if (i1->m_is_string != i2->m_is_string)
            return false;
        if (i1->m_is_string) {
            if (strcmp(i1->m_str, i2->m_str) != 0)
                return false;
        } else if (i1->m_k != i2->m_k) {
            return false;
        }
    }
    return true;
}

bool operator==(name const & a, char const * b) {
    return a.m_ptr->m_is_string && strcmp(a.m_ptr->m_str, b) == 0;
}

int cmp(name::imp * i1, name::imp * i2) {
    buffer<name::imp *> limbs1, limbs2;
    copy_limbs(i1, limbs1);
    copy_limbs(i2, limbs2);
    auto it1 = limbs1.begin();
    auto it2 = limbs2.begin();
    for (; it1 != limbs1.end() && it2 != limbs2.end(); ++it1, ++it2) {
        i1 = *it1;
        i2 = *it2;

        if (i1->m_is_string != i2->m_is_string)
            return i1->m_is_string ? 1 : -1;

        if (i1->m_is_string) {
            int c = strcmp(i1->m_str, i2->m_str);
            if (c != 0)
                return c;
        } else if (i1->m_k != i2->m_k) {
            return i1->m_k < i2->m_k ? -1 : 1;
        }
    }
    if (it1 == limbs1.end() && it2 == limbs2.end())
        return 0;
    else return it1 == limbs1.end() ? -1 : 1;
}

bool name::is_atomic() const {
    return m_ptr == nullptr || m_ptr->m_prefix == nullptr;
}

name name::get_prefix() const {
    lean_assert(!is_atomic());
    return name(m_ptr->m_prefix);
}

static unsigned num_digits(unsigned k) {
    if (k == 0)
        return 1;
    int r = 0;
    while (k != 0) {
        k /= 10;
        r++;
    }
    return r;
}

size_t name::size() const {
    if (m_ptr == nullptr) {
        return strlen(anonymous_str);
    } else {
        imp * i       = m_ptr;
        size_t sep_sz = strlen(lean_name_separator);
        size_t r      = 0;
        while (true) {
            if (i->m_is_string) {
                r += strlen(i->m_str);
            } else {
                r += num_digits(i->m_k);
            }
            if (i->m_prefix) {
                r += sep_sz;
                i  = i->m_prefix;
            } else {
                break;
            }
        }
        return r;
    }
}

unsigned name::hash() const {
    return m_ptr ? m_ptr->m_hash : 11;
}

bool name::is_safe_ascii() const {
    imp * i       = m_ptr;
    while (i) {
        if (i->m_is_string) {
            if (!::lean::is_safe_ascii(i->m_str))
                return false;
        }
        i  = i->m_prefix;
    }
    return true;
}

std::string name::to_string() const {
    std::ostringstream s;
    imp::display(s, m_ptr);
    return s.str();
}

std::ostream & operator<<(std::ostream & out, name const & n) {
    name::imp::display(out, n.m_ptr);
    return out;
}

name operator+(name const & n1, name const & n2) {
    if (n2.is_anonymous()) {
        return n1;
    } else {
        name prefix;
        if (!n2.is_atomic())
            prefix = n1 + name(n2.m_ptr->m_prefix);
        else
            prefix = n1;
        if (n2.m_ptr->m_is_string)
            return name(prefix, n2.m_ptr->m_str);
        else
            return name(prefix, n2.m_ptr->m_k);
    }
}

DECL_UDATA(name)

static int mk_name(lua_State * L) {
    int nargs = lua_gettop(L);
    name r;
    for (int i = 1; i <= nargs; i++) {
        switch (lua_type(L, i)) {
        case LUA_TNIL:      break; // skip
        case LUA_TNUMBER:   r = name(r, lua_tointeger(L, i)); break;
        case LUA_TSTRING:   r = name(r, lua_tostring(L, i)); break;
        case LUA_TUSERDATA: r = r + to_name(L, i); break;
        default:            throw exception(sstream() << "arg #" << i << " must be a hierarchical name, string, or integer");
        }
    }
    return push_name(L, r);
}

name to_name_ext(lua_State * L, int idx) {
    if (lua_isstring(L, idx)) {
        return luaL_checkstring(L, idx);
    } else if (lua_istable(L, idx)) {
        name r;
        int n = objlen(L, idx);
        for (int i = 1; i <= n; i++) {
            lua_rawgeti(L, idx, i);
            switch (lua_type(L, -1)) {
            case LUA_TNIL:      break; // skip
            case LUA_TNUMBER:   r = name(r, lua_tointeger(L, -1)); break;
            case LUA_TSTRING:   r = name(r, lua_tostring(L, -1));  break;
            case LUA_TUSERDATA: r = r + to_name(L, -1); break;
            default:            throw exception("invalid array arguments, elements must be a hierarchical name, string, or integer");
            }
            lua_pop(L, 1);
        }
        return r;
    } else {
        return to_name(L, idx);
    }
}

static int name_tostring(lua_State * L) {
    lua_pushstring(L, to_name(L, 1).to_string().c_str());
    return 1;
}

static int name_eq(lua_State * L) {
    lua_pushboolean(L, to_name(L, 1) == to_name(L, 2));
    return 1;
}

static int name_lt(lua_State * L) {
    lua_pushboolean(L, to_name(L, 1) < to_name(L, 2));
    return 1;
}

static int name_hash(lua_State * L) {
    lua_pushinteger(L, to_name(L, 1).hash());
    return 1;
}

static const struct luaL_Reg name_m[] = {
    {"__gc",       name_gc}, // never throws
    {"__tostring", safe_function<name_tostring>},
    {"__eq",       safe_function<name_eq>},
    {"__lt",       safe_function<name_lt>},
    {"hash",       safe_function<name_hash>},
    {0, 0}
};

static void name_migrate(lua_State * src, int i, lua_State * tgt) {
    push_name(tgt, to_name(src, i));
}

void open_name(lua_State * L) {
    luaL_newmetatable(L, name_mt);
    set_migrate_fn_field(L, -1, name_migrate);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, name_m, 0);

    SET_GLOBAL_FUN(mk_name,   "name");
    SET_GLOBAL_FUN(name_pred, "is_name");
}
}
void print(lean::name const & n) { std::cout << n << std::endl; }
