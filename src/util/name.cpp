/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include <algorithm>
#include <string>
#include "runtime/thread.h"
#include "runtime/debug.h"
#include "runtime/sstream.h"
#include "runtime/hash.h"
#include "runtime/buffer.h"
#include "util/name.h"

namespace lean {
extern "C" obj_res lean_name_mk_string(obj_arg p, obj_arg s);
extern "C" obj_res lean_name_mk_numeral(obj_arg p, obj_arg n);

static inline obj_res name_mk_string_of_cstr(obj_arg p, char const * s) {
    return lean_name_mk_string(p, mk_string(s));
}

constexpr char const * anonymous_str = "[anonymous]";

static void display_name_core(std::ostream & out, name const & n) {
    lean_assert(!n.is_anonymous());
    name pre = n.get_prefix();
    if (pre) {
        display_name_core(out, pre);
        out << lean_name_separator;
    }
    if (n.is_string()) {
        std::string str = n.get_string().to_std_string();
        if (str.empty())
            out << "«" << str << "»";
        else
            out << str;
    } else {
        out << n.get_numeral().to_std_string();
    }
}

static void display_name(std::ostream & out, name const & n) {
    if (n.is_anonymous())
        out << anonymous_str;
    else
        display_name_core(out, n);
}

name::name(name const & prefix, char const * n):
    object_ref(name_mk_string_of_cstr(prefix.raw(), n)) {
    inc(prefix.raw());
}

name::name(name const & prefix, unsigned k):
    object_ref(lean_name_mk_numeral(prefix.raw(), mk_nat_obj(k))) {
    inc(prefix.raw());
}

name::name(name const & prefix, string_ref const & s):
    object_ref(lean_name_mk_string(prefix.raw(), s.raw())) {
    inc(prefix.raw());
    inc(s.raw());
}

name::name(name const & prefix, nat const & k):
    object_ref(lean_name_mk_numeral(prefix.raw(), k.raw())) {
    inc(prefix.raw());
    inc(k.raw());
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

static void copy_limbs(object * p, buffer<object *> & limbs) {
    limbs.clear();
    while (!is_scalar(p)) {
        limbs.push_back(p);
        p = name::get_prefix(p);
    }
    std::reverse(limbs.begin(), limbs.end());
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
            if (name::get_string(i1) != name::get_string(i2))
                return false;
        } else if (name::get_numeral(i1) != name::get_numeral(i2)) {
            return false;
        }
    }
    return true;
}

int name::cmp_core(object * i1, object * i2) {
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
            if (get_string(i1) < get_string(i2))
                return -1;
            if (get_string(i2) < get_string(i1))
                return 1;
        } else {
            if (get_numeral(i1) < get_numeral(i2))
                return -1;
            if (get_numeral(i2) < get_numeral(i1))
                return 1;
        }
    }
    if (it1 == limbs1.end() && it2 == limbs2.end())
        return 0;
    else return it1 == limbs1.end() ? -1 : 1;
}

name name::get_root() const {
    name n = *this;
    while (n.get_prefix()) {
        n = n.get_prefix();
    }
    return n;
}

LEAN_EXPORT std::ostream & operator<<(std::ostream & out, name const & n) {
    display_name(out, n);
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

extern "C" obj_res lean_name_append_after(obj_arg n, obj_arg s);
extern "C" obj_res lean_name_append_index_after(obj_arg n, obj_arg i);

name name::append_after(char const * s) const {
    return name(lean_name_append_after(to_obj_arg(), lean_mk_string(s)));
}

name name::append_after(unsigned i) const {
    return name(lean_name_append_index_after(to_obj_arg(), lean_unsigned_to_nat(i)));
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

void initialize_name() {}
void finalize_name() {}
}
void print(lean::name const & n) { std::cout << n << std::endl; }
