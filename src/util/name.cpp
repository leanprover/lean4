/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <cstring>
#include <vector>
#include <algorithm>
#include <sstream>
#include "name.h"
#include "debug.h"
#include "rc.h"
#include "buffer.h"
#include "hash.h"
#include "trace.h"
#include "ascii.h"

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
    lean_assert(sz < 1u<<31);
    char * mem = new char[sizeof(imp) + sz + 1];
    m_ptr      = new (mem) imp(true, prefix.m_ptr);
    std::memcpy(mem + sizeof(imp), name, sz + 1);
    m_ptr->m_str       = mem + sizeof(imp);
    if (m_ptr->m_prefix)
        m_ptr->m_hash = hash_str(sz, name, m_ptr->m_prefix->m_hash);
    else
        m_ptr->m_hash = hash_str(sz, name, 0);
}

name::name(name const & prefix, unsigned k) {
    m_ptr      = new imp(false, prefix.m_ptr);
    m_ptr->m_k = k;
    if (m_ptr->m_prefix)
        m_ptr->m_hash = ::lean::hash(m_ptr->m_prefix->m_hash, k);
    else
        m_ptr->m_hash = k;
}

name::name(char const * n):name(name(), n) {
}

name::name(unsigned k):name(name(), k) {
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
}
void print(lean::name const & n) { std::cout << n << std::endl; }
