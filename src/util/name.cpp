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
#include "runtime/thread.h"
#include "runtime/debug.h"
#include "runtime/sstream.h"
#include "runtime/utf8.h"
#include "util/name.h"
#include "util/buffer.h"
#include "util/hash.h"
#include "util/ascii.h"
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

static void display_name_core(std::ostream & out, name const & n, bool escape, char const * sep) {
    lean_assert(!n.is_anonymous());
    name pre = n.get_prefix();
    if (pre) {
        display_name_core(out, pre, escape, sep);
        out << sep;
    }
    if (n.is_string()) {
        char const * str = n.get_string();
        size_t sz = strlen(str);
        bool must_escape = false;
        if (escape && *str) {
            if (!is_id_first(str, str + sz))
                must_escape = true;
            // don't escape names produced by server::display_decl
            if (must_escape && str[0] == '?')
                must_escape = false;
            if (escape) {
                for (char const * s = str + get_utf8_size(str[0]); !must_escape && *s; s += get_utf8_size(*s)) {
                    if (!is_id_rest(s, str + sz))
                        must_escape = true;
                }
            }
        }
        if (must_escape || sz == 0)
            out << "«" << str << "»";
        else
            out << str;
    } else {
        out << n.get_numeral();
    }
}

static void display_name(std::ostream & out, name const & n, bool escape, char const * sep) {
    if (n.is_anonymous())
        out << anonymous_str;
    else
        display_name_core(out, n, escape, sep);
}

name::name(name const & prefix, char const * n):
    object_ref(mk_cnstr(static_cast<unsigned>(name_kind::STRING),
                        prefix.raw(), mk_string(n), sizeof(unsigned))) {
    inc(prefix.raw());
    size_t sz  = strlen(n);
    unsigned h = hash_str(static_cast<unsigned>(sz), n, prefix.hash());
    cnstr_set_scalar<unsigned>(raw(), 2*sizeof(object*), h); // NOLINT
}

name::name(name const & prefix, unsigned k):
    object_ref(mk_cnstr(static_cast<unsigned>(name_kind::NUMERAL),
                        prefix.raw(), mk_nat_obj(k), sizeof(unsigned))) {
    inc(prefix.raw());
    unsigned h = ::lean::hash(k, prefix.hash());
    cnstr_set_scalar<unsigned>(raw(), 2*sizeof(object*), h); // NOLINT
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

static void copy_limbs(object * p, buffer<object *> & limbs) {
    limbs.clear();
    while (!is_scalar(p)) {
        limbs.push_back(p);
        p = name::get_prefix(p);
    }
    std::reverse(limbs.begin(), limbs.end());
}

/* Equality test core procedure, it is invoked by operator== */
bool name::eq_core(object * i1, object * i2) {
    while (true) {
        lean_assert(!is_scalar(i1));
        lean_assert(!is_scalar(i2));
        lean_assert(i1 && i2);
        lean_assert(hash(i1) == hash(i2));
        if (cnstr_tag(i1) != cnstr_tag(i2))
            return false;
        if (static_cast<name_kind>(cnstr_tag(i1)) == name_kind::STRING) {
            if (strcmp(get_string(i1), get_string(i2)) != 0)
                return false;
        } else {
            if (!nat_eq(get_num_obj(i1), get_num_obj(i2)))
                return false;
        }
        i1 = get_prefix(i1);
        i2 = get_prefix(i2);
        if (i1 == i2)
            return true;
        if (is_scalar(i1) != is_scalar(i2))
            return false;
        if (hash(i1) != hash(i2))
            return false;
    }
}

bool is_prefix_of(name const & n1, name const & n2) {
    if (n2.is_atomic())
        return n1 == n2;
    buffer<object*> limbs1, limbs2;
    object* i1 = n1.raw();
    object* i2 = n2.raw();
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
        if (cnstr_tag(i1) != cnstr_tag(i2))
            return false;
        if (static_cast<name_kind>(cnstr_tag(i1)) == name_kind::STRING) {
            if (strcmp(name::get_string(i1), name::get_string(i2)) != 0)
                return false;
        } else if (!nat_eq(name::get_num_obj(i1), name::get_num_obj(i2))) {
            return false;
        }
    }
    return true;
}

bool operator==(name const & a, char const * b) {
    return
        a.kind() == name_kind::STRING &&
        is_scalar(name::get_prefix(a.raw())) &&
        strcmp(a.get_string(), b) == 0;
}

int name::cmp(object * i1, object * i2) {
    buffer<object*> limbs1, limbs2;
    copy_limbs(i1, limbs1);
    copy_limbs(i2, limbs2);
    auto it1 = limbs1.begin();
    auto it2 = limbs2.begin();
    for (; it1 != limbs1.end() && it2 != limbs2.end(); ++it1, ++it2) {
        i1 = *it1;
        i2 = *it2;
        name_kind k1 = static_cast<name_kind>(cnstr_tag(i1));
        name_kind k2 = static_cast<name_kind>(cnstr_tag(i2));
        if (k1 != k2)
            return k1 == name_kind::STRING ? 1 : -1;

        if (k1 == name_kind::STRING) {
            int c = strcmp(get_string(i1), get_string(i2));
            if (c != 0)
                return c;
        } else {
            object * n1 = get_num_obj(i1);
            object * n2 = get_num_obj(i2);
            if (nat_ne(n1, n2))
                return nat_lt(n1, n2) ? -1 : 1;
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
    if (is_scalar(raw())) {
        return strlen(anonymous_str);
    } else {
        object * i    = raw();
        size_t sep_sz = strlen(lean_name_separator);
        size_t r      = 0;
        while (true) {
            lean_assert(!is_scalar(i));
            if (kind(i) == name_kind::STRING) {
                r += unicode ? string_len(get_string_obj(i)) : strlen(get_string(i));
            } else {
                // TODO(Leo): we are ignoring the case the numeral is not small.
                r += num_digits(get_numeral(i));
            }
            i = get_prefix(i);
            if (is_scalar(i))
                break;
            r += sep_sz;
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
    object * i = raw();
    while (!is_scalar(i)) {
        if (kind(i) == name_kind::STRING) {
            if (!::lean::is_safe_ascii(get_string(i)))
                return false;
        }
        i  = get_prefix(i);
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
    display_name(s, *this, false, sep);
    return s.str();
}

std::string name::escape(char const * sep) const {
    std::ostringstream s;
    display_name(s, *this, true, sep);
    return s.str();
}

std::ostream & operator<<(std::ostream & out, name const & n) {
    display_name(out, n, false, lean_name_separator);
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
            prefix = n1 + n2.get_prefix();
        else
            prefix = n1;
        if (n2.is_string())
            return name(prefix, n2.get_string());
        else
            return name(prefix, n2.get_numeral()); // <<< TODO(Leo): ignoring the case the numeral is not small.
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
    if (p.raw() == raw())
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

bool is_internal_name(name const & n) {
    name it = n;
    while (!it.is_anonymous()) {
        if (!it.is_anonymous() && it.is_string() && it.get_string() && it.get_string()[0] == '_')
            return true;
        it = it.get_prefix();
    }
    return false;
}

static atomic<unsigned> * g_next_id = nullptr;

name name::mk_internal_unique_name() {
    unsigned id = (*g_next_id)++;
    return name(name(), id);
}

void initialize_name() {
    g_anonymous = new name();
    g_next_id   = new atomic<unsigned>(0);
}

void finalize_name() {
    delete g_next_id;
    delete g_anonymous;
}
}
void print(lean::name const & n) { std::cout << n << std::endl; }
