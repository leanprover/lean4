/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <cctype>
#include <cstring>
#include <vector>
#include <algorithm>
#include <sstream>
#include <string>
#include "util/thread.h"
#include "util/name.h"
#include "util/sstream.h"
#include "util/debug.h"
#include "util/buffer.h"
#include "util/memory_pool.h"
#include "util/hash.h"
#include "util/ascii.h"
#include "util/utf8.h"
#include "util/object_serializer.h"

namespace lean {
constexpr char const * anonymous_str = "[anonymous]";

bool is_greek_unicode(unsigned u) { return 0x391 <= u && u <= 0x3DD; }
bool is_letter_like_unicode(unsigned u) {
    return
            (0x3b1  <= u && u <= 0x3c9 && u != 0x3bb) || // Lower greek, but lambda
            (0x391  <= u && u <= 0x3A9 && u != 0x3A0 && u != 0x3A3) || // Upper greek, but Pi and Sigma
            (0x3ca  <= u && u <= 0x3fb) ||               // Coptic letters
            (0x1f00 <= u && u <= 0x1ffe) ||              // Polytonic Greek Extended Character Set
            (0x2100 <= u && u <= 0x214f) ||              // Letter like block
            (0x1d49c <= u && u <= 0x1d59f);              // Latin letters, Script, Double-struck, Fractur
}
bool is_sub_script_alnum_unicode(unsigned u) {
    return
            (0x207f <= u && u <= 0x2089) || // n superscript and numberic subscripts
            (0x2090 <= u && u <= 0x209c) || // letter-like subscripts
            (0x1d62 <= u && u <= 0x1d6a);   // letter-like subscripts
}

bool is_id_first(unsigned char const * begin, unsigned char const * end) {
    if (std::isalpha(*begin) || *begin == '_')
        return true;
    unsigned u = utf8_to_unicode(begin, end);
    return u == id_begin_escape || is_letter_like_unicode(u);
}

bool is_id_rest(unsigned char const * begin, unsigned char const * end) {
    if (std::isalnum(*begin) || *begin == '_' || *begin == '\'')
        return true;
    unsigned u = utf8_to_unicode(begin, end);
    return is_letter_like_unicode(u) || is_sub_script_alnum_unicode(u);
}

void name::imp::display_core(std::ostream & out, imp * p, bool escape, char const * sep) {
    lean_assert(p != nullptr);
    if (p->m_prefix) {
        display_core(out, p->m_prefix, escape, sep);
        out << sep;
    }
    if (p->m_is_string) {
        size_t sz = strlen(p->m_str);
        bool must_escape = false;
        if (escape && *p->m_str) {
            if (!is_id_first(p->m_str, p->m_str + sz))
                must_escape = true;
            // don't escape names produced by server::display_decl
            if (must_escape && p->m_str[0] == '?')
                must_escape = false;
            if (escape) {
                for (char * s = p->m_str + get_utf8_size(p->m_str[0]); !must_escape && *s; s += get_utf8_size(*s)) {
                    if (!is_id_rest(s, p->m_str + sz))
                        must_escape = true;
                }
            }
        }
        if (must_escape || sz == 0)
            out << "«" << p->m_str << "»";
        else
            out << p->m_str;
    } else {
        out << p->m_k;
    }
}

void name::imp::display(std::ostream & out, imp * p, bool escape, char const * sep) {
    if (p == nullptr)
        out << anonymous_str;
    else
        display_core(out, p, escape, sep);
}

void copy_limbs(name::imp * p, buffer<name::imp *> & limbs) {
    limbs.clear();
    while (p != nullptr) {
        limbs.push_back(p);
        p = p->m_prefix;
    }
    std::reverse(limbs.begin(), limbs.end());
}

DEF_THREAD_MEMORY_POOL(get_numeric_name_allocator, sizeof(name::imp));

void name::imp::dealloc() {
    imp * curr = this;
    while (true) {
        lean_assert(curr->get_rc() == 0);
        imp * p = curr->m_prefix;
        if (curr->m_is_string)
            delete[] reinterpret_cast<char*>(curr);
        else
            get_numeric_name_allocator().recycle(curr);
        curr = p;
        if (!curr || !curr->dec_ref_core())
            break;
    }
}

name::name(imp * p) {
    m_ptr = p;
    if (m_ptr)
        m_ptr->inc_ref();
}

name::name() {
    m_ptr = nullptr;
}

name::name(name const & prefix, char const * nam) {
    size_t sz  = strlen(nam);
    lean_assert(sz < (1u << 31));
    char * mem = new char[sizeof(imp) + sz + 1];
    m_ptr      = new (mem) imp(true, prefix.m_ptr);
    std::memcpy(mem + sizeof(imp), nam, sz + 1);
    m_ptr->m_str       = mem + sizeof(imp);
    // Emscripten easily breaks with small changes here.  The main fix seems to be to use m_ptr->m_str instead of name.
    m_ptr->m_hash = hash_str(static_cast<unsigned>(sz), m_ptr->m_str, prefix.hash());
}

name::name(name const & prefix, unsigned k, bool) {
    m_ptr      = new (get_numeric_name_allocator().allocate()) imp(false, prefix.m_ptr);
    m_ptr->m_k = k;
    if (m_ptr->m_prefix)
        m_ptr->m_hash = ::lean::hash(m_ptr->m_prefix->m_hash, k);
    else
        m_ptr->m_hash = k;
}

name::name(name const & prefix, unsigned k):name(prefix, k, true) {
}

name::name(char const * n):name(name(), n) {
}

name::name(unsigned k):name(name(), k, true) {
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

static name * g_anonymous = nullptr;

name const & name::anonymous() {
    lean_assert(g_anonymous->is_anonymous());
    return *g_anonymous;
}

static atomic<unsigned> * g_next_id = nullptr;

name name::mk_internal_unique_name() {
    unsigned id = (*g_next_id)++;
    return name(id);
}

name & name::operator=(name const & other) { LEAN_COPY_REF(other); }

name & name::operator=(name && other) { LEAN_MOVE_REF(other); }

name_kind name::kind() const {
    if (m_ptr == nullptr)
        return name_kind::ANONYMOUS;
    else
        return m_ptr->m_is_string ? name_kind::STRING : name_kind::NUMERAL;
}

/* Equality test core procedure, it is invoked by operator== */
bool eq_core(name::imp * i1, name::imp * i2) {
    while (true) {
        lean_assert(i1 != nullptr);
        lean_assert(i2 != nullptr);
        lean_assert(i1 && i2);
        lean_assert(i1->m_hash == i2->m_hash);
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
        if (i1 == i2)
            return true;
        if ((i1 == nullptr) != (i2 == nullptr))
            return false;
        if (i1->m_hash != i2->m_hash)
            return false;
    }
}

bool is_prefix_of(name const & n1, name const & n2) {
    if (n2.is_atomic())
        return n1 == n2;
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
    return a.m_ptr && a.m_ptr->m_is_string && strcmp(a.m_ptr->m_str, b) == 0;
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

size_t name::size_core(bool unicode) const {
    if (m_ptr == nullptr) {
        return strlen(anonymous_str);
    } else {
        imp * i       = m_ptr;
        size_t sep_sz = strlen(lean_name_separator);
        size_t r      = 0;
        while (true) {
            if (i->m_is_string) {
                r += unicode ? utf8_strlen(i->m_str) : strlen(i->m_str);
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

size_t name::size() const {
    return size_core(false);
}

size_t name::utf8_size() const {
    return size_core(true);
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

name name::get_root() const {
    name n = *this;
    while (n.get_prefix()) {
        n = n.get_prefix();
    }
    return n;
}

std::string name::to_string(char const * sep) const {
    std::ostringstream s;
    imp::display(s, m_ptr, false, sep);
    return s.str();
}

std::string name::escape(char const * sep) const {
    std::ostringstream s;
    imp::display(s, m_ptr, true, sep);
    return s.str();
}

std::ostream & operator<<(std::ostream & out, name const & n) {
    name::imp::display(out, n.m_ptr, false);
    return out;
}

name operator+(name const & n1, name const & n2) {
    if (n2.is_anonymous()) {
        return n1;
    } else if (n1.is_anonymous()) {
        return n2;
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

name name::append_before(char const * p) const {
    if (is_anonymous()) {
        return name(p);
    } else if (is_string()) {
        return name(get_prefix(), (std::string(p) + std::string(get_string())).c_str());
    } else {
        return name(name(get_prefix(), p), get_numeral());
    }
}

name name::append_after(char const * s) const {
    if (is_anonymous()) {
        return name(s);
    } else if (is_string()) {
        return name(get_prefix(), (std::string(get_string()) + std::string(s)).c_str());
    } else {
        return name(*this, s);
    }
}

name name::get_subscript_base() const {
    if (is_string()) {
        return *this;
    } else {
        return name(*this, "");
    }
}

name name::append_after(unsigned i) const {
    name b = get_subscript_base();
    std::ostringstream s;
    s << b.get_string() << "_" << i;
    return name(b.get_prefix(), s.str().c_str());
}

optional<pair<name, unsigned>> name::is_subscripted() const {
    optional<pair<name, unsigned>> none;
    if (!is_string()) return none;

    std::string s = get_string();
    auto underscore_pos = s.find_last_of('_');
    if (underscore_pos == std::string::npos) return none;

    std::string::iterator it = s.begin() + underscore_pos + 1;
    if (it == s.end() || *it == '0') return none;
    unsigned idx = 0;
    for (; it != s.end() && '0' <= *it && *it <= '9'; it++)
        idx = 10*idx + (*it - '0');
    if (it != s.end()) return none;

    name prefix(get_prefix(), s.substr(0, underscore_pos).c_str());
    return optional<pair<name, unsigned>>(prefix, idx);
}

name name::replace_prefix(name const & prefix, name const & new_prefix) const {
    if (*this == prefix)
        return new_prefix;
    if (is_anonymous())
        return *this;
    name p = get_prefix().replace_prefix(prefix, new_prefix);
    if (p.m_ptr == m_ptr)
        return *this;
    if (is_string())
        return name(p, get_string());
    else
        return name(p, get_numeral());
}

bool is_part_of(std::string const & p, name n) {
    while (true) {
        if (n.is_string()) {
            std::string s(n.get_string());
            if (s.find(p) != std::string::npos)
                return true;
        }
        if (n.is_atomic() || n.is_anonymous())
            return false;
        n = n.get_prefix();
    }
}

name string_to_name(std::string const & str) {
    static_assert(*(lean_name_separator+1) == 0, "this function assumes the length of lean_name_separator is 1");
    name result;
    std::string id_part;
    for (unsigned i = 0; i < str.size(); i++) {
        if (str[i] == lean_name_separator[0]) {
            result = name(result, id_part.c_str());
            id_part.clear();
        } else {
            id_part.push_back(str[i]);
        }
    }
    return name(result, id_part.c_str());
}

enum name_ll_kind { LL_ANON = 0, LL_STRING = 1, LL_INT = 2, LL_STRING_PREFIX = 3, LL_INT_PREFIX = 4 };
name_ll_kind ll_kind(name const & n) {
    if (n.is_anonymous())
        return LL_ANON;
    if (n.is_atomic())
        return n.is_string() ? LL_STRING : LL_INT;
    else
        return n.is_string() ? LL_STRING_PREFIX : LL_INT_PREFIX;
}

class name_serializer : public object_serializer<name, name::ptr_hash, name::ptr_eq> {
    typedef object_serializer<name, name::ptr_hash, name::ptr_eq> super;
public:
    void write(name const & n) {
        name_ll_kind k = ll_kind(n);
        super::write_core(n, k, [&]() {
                serializer & s = get_owner();
                switch (k) {
                case LL_ANON:            break;
                case LL_STRING:          s.write_string(n.get_string()); break;
                case LL_INT:             s.write_unsigned(n.get_numeral()); break;
                case LL_STRING_PREFIX:   write(n.get_prefix()); s.write_string(n.get_string()); break;
                case LL_INT_PREFIX:      write(n.get_prefix()); s.write_unsigned(n.get_numeral()); break;
                }
            });
    }
};

class name_deserializer : public object_deserializer<name> {
    typedef object_deserializer<name> super;
public:
    name read() {
        return super::read_core([&](char c) {
                deserializer & d = get_owner();
                name_ll_kind k = static_cast<name_ll_kind>(c);
                switch (k) {
                case LL_ANON:          return name();
                case LL_STRING:        return name(d.read_string().c_str());
                case LL_INT:           return name(name(), d.read_unsigned(), true);
                case LL_STRING_PREFIX: {
                    name prefix = read();
                    return name(prefix, d.read_string().c_str());
                }
                case LL_INT_PREFIX: {
                    name prefix = read();
                    return name(prefix, d.read_unsigned());
                }}
                throw corrupted_stream_exception();
            });
    }
};

struct name_sd {
    unsigned m_serializer_extid;
    unsigned m_deserializer_extid;
    name_sd() {
        m_serializer_extid   = serializer::register_extension([](){ return std::unique_ptr<serializer::extension>(new name_serializer()); });
        m_deserializer_extid = deserializer::register_extension([](){ return std::unique_ptr<deserializer::extension>(new name_deserializer()); });
    }
};
static name_sd * g_name_sd = nullptr;

serializer & operator<<(serializer & s, name const & n) {
    s.get_extension<name_serializer>(g_name_sd->m_serializer_extid).write(n);
    return s;
}

name read_name(deserializer & d) {
    return d.get_extension<name_deserializer>(g_name_sd->m_deserializer_extid).read();
}

bool is_internal_name(name const & n) {
    name it = n;
    while (!it.is_anonymous()) {
        if (!it.is_anonymous() && it.is_string() && it.get_string() && it.get_string()[0] == '_')
            return true;
        it = it.get_prefix();
    }
    return false;
}

void initialize_name() {
    g_anonymous = new name();
    g_name_sd   = new name_sd();
    g_next_id   = new atomic<unsigned>(0);
}

void finalize_name() {
    delete g_next_id;
    delete g_name_sd;
    delete g_anonymous;
}
}
void print(lean::name const & n) { std::cout << n << std::endl; }
