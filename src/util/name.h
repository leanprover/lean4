/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include <iostream>
#include <functional>
#include <algorithm>
#include <utility>
#include "runtime/optional.h"
#include "runtime/string_ref.h"
#include "runtime/list_ref.h"
#include "runtime/buffer.h"
#include "util/pair.h"
#include "util/nat.h"


namespace lean {
constexpr char const * lean_name_separator = ".";
#ifdef _MSC_VER
constexpr char16_t id_begin_escape = L'\xab';
constexpr char16_t id_end_escape = L'\xbb';
#else
constexpr char16_t id_begin_escape = u'«';
constexpr char16_t id_end_escape = u'»';
#endif

bool is_id_first(unsigned char const * begin, unsigned char const * end);
inline bool is_id_first(char const * begin, char const * end) {
    return is_id_first(reinterpret_cast<unsigned char const *>(begin),
                      reinterpret_cast<unsigned char const *>(end));
}

bool is_id_rest(unsigned char const * begin, unsigned char const * end);
inline bool is_id_rest(char const * begin, char const * end) {
    return is_id_rest(reinterpret_cast<unsigned char const *>(begin),
                      reinterpret_cast<unsigned char const *>(end));
}

extern "C" uint64_t lean_name_hash_exported(lean_obj_arg n);

inline uint64_t lean_name_hash_exported_b(b_lean_obj_arg n) {
    lean_inc(n);
    return lean_name_hash_exported(n);
}

enum class name_kind { ANONYMOUS, STRING, NUMERAL };
/** \brief Hierarchical names. */
class LEAN_EXPORT name : public object_ref {
public:
    /* Low level primitives */
    static bool eq(b_obj_arg n1, b_obj_arg n2) { return lean_name_eq(n1, n2); }
    static name_kind kind(object * o) { return static_cast<name_kind>(obj_tag(o)); }
    static bool is_anonymous(object * o) { return is_scalar(o); }
    static object * get_prefix(object * o) { return cnstr_get(o, 0); }
    static string_ref const & get_string(object * o) { return static_cast<string_ref const &>(cnstr_get_ref(o, 1)); }
    static nat const & get_numeral(object * o) { return static_cast<nat const &>(cnstr_get_ref(o, 1)); }
    static int cmp_core(object * o1, object * o2);
    size_t size_core(bool unicode) const;
private:
    explicit name(object_ref && r):object_ref(r) {}
public:
    name():object_ref(box(static_cast<unsigned>(name_kind::ANONYMOUS))) {}
    explicit name(obj_arg o):object_ref(o) {}
    name(b_obj_arg r, bool b):object_ref(r, b) {}
    name(name const & prefix, char const * name);
    name(name const & prefix, unsigned k);
    name(name const & prefix, nat const & n);
    name(name const & prefix, string_ref const & s);
    name(char const * n):name(name(), n) {}
    name(std::string const & s):name(name(), string_ref(s)) {}
    name(string_ref const & s):name(name(), s) {}
    name(name const & other):object_ref(other) {}
    name(name && other):object_ref(std::move(other)) {}
    /**
       \brief Create a hierarchical name using the given strings.
       Example: <code>name{"foo", "bla", "tst"}</code> creates the hierarchical
       name <tt>foo::bla::tst</tt>.
    */
    name(std::initializer_list<char const *> const & l);
    static name const & anonymous();
    /**
        \brief Create a unique internal name that is not meant to exposed
        to the user. Different modules require a unique name.
        The unique name is created using a numeric prefix.
        A module that needs to create several unique names should
        the following idiom:
        <code>
            name unique_prefix = name::mk_internal_unique_name();
            name unique_name_1(unique_prefix, 1);
            ...
            name unique_name_k(unique_prefix, k);
        </code>
    */
    static name mk_internal_unique_name();
    name & operator=(name const & other) { object_ref::operator=(other); return *this; }
    name & operator=(name && other) { object_ref::operator=(std::move(other)); return *this; }
    static uint64_t hash(b_obj_arg n) {
       lean_assert(lean_name_hash(n) == lean_name_hash_exported_b(n));
       return lean_name_hash(n);
    }
    uint64_t hash() const { return hash(raw()); }
    /** \brief Return true iff \c n1 is a prefix of \c n2. */
    friend bool is_prefix_of(name const & n1, name const & n2);
    friend bool operator==(name const & a, name const & b) { return name::eq(a.raw(), b.raw()); }
    friend bool operator!=(name const & a, name const & b) { return !(a == b); }
    friend bool operator==(name const & a, char const * b);
    friend bool operator!=(name const & a, char const * b) { return !(a == b); }
    /** \brief Total order on hierarchical names. */
    friend int cmp(name const & a, name const & b) { return cmp_core(a.raw(), b.raw()); }
    friend bool operator<(name const & a, name const & b) { return cmp(a, b) < 0; }
    friend bool operator>(name const & a, name const & b) { return cmp(a, b) > 0; }
    friend bool operator<=(name const & a, name const & b) { return cmp(a, b) <= 0; }
    friend bool operator>=(name const & a, name const & b) { return cmp(a, b) >= 0; }
    name_kind kind() const { return kind(raw()); }
    bool is_anonymous() const { return kind() == name_kind::ANONYMOUS; }
    bool is_string() const    { return kind() == name_kind::STRING; }
    bool is_numeral() const   { return kind() == name_kind::NUMERAL; }
    explicit operator bool() const { return kind() != name_kind::ANONYMOUS; }
    nat const & get_numeral() const { lean_assert(is_numeral()); return get_numeral(raw()); }
    string_ref const & get_string() const { lean_assert(is_string()); return get_string(raw()); }
    name const & get_prefix() const {
        if (is_anonymous()) return *this;
        else return static_cast<name const &>(cnstr_get_ref(*this, 0));
    }
    bool is_atomic() const { return is_anonymous() || kind(get_prefix(raw())) == name_kind::ANONYMOUS; }
    /** \brief Given a name of the form a_1.a_2. ... .a_k, return a_1 if k >= 1, or the empty name otherwise. */
    name get_root() const;
    /** \brief Convert this hierarchical name into a string. */
    std::string to_string(char const * sep = lean_name_separator) const;
    std::string escape(char const * sep = lean_name_separator) const;
    /** \brief Size of the this name (in characters). */
    size_t size() const;
    /** \brief Size of the this name in unicode. */
    size_t utf8_size() const;
    /** \brief Return true iff the name contains only safe ASCII chars */
    bool is_safe_ascii() const;
    friend LEAN_EXPORT std::ostream & operator<<(std::ostream & out, name const & n);
    /** \brief Concatenate the two given names. */
    friend name operator+(name const & n1, name const & n2);

    /**
        \brief Given a name of the form a_1.a_2. ... .a_k,
           If a_k is a string,  return a_1.a_2. ... .a_k', where a_k' is the string p concatenated with a_k.
           If a_k is a numeral, return a_1.a_2. ... .p.a_k
    */
    name append_before(char const * p) const;
    /**
        \brief Given a name of the form a_1.a_2. ... .a_k,
           If a_k is a string,  return a_1.a_2. ... .a_k', where a_k' is the string a_k concatenated with s.
           If a_k is a numeral, return a_1.a_2. ... .a_k.s
    */
    name append_after(char const * s) const;

    /**
        \brief Given a name of the form a_1.a_2. ... .a_k,
           If a_k is a string,  return a_1.a_2. ... .a_k', where a_k' is the string a_k concatenated with _i.
           Otherwise add _i as the last component.
    */
    name append_after(unsigned i) const;

    /**
        \brief Given a name of the form a_1.a_2. ... .a_k,
           If a_k is a string, return the name itself.
           Otherwise add the empty string as the last component.
    */
    name get_subscript_base() const;

    /**
        \brief Given a name of the form a_1.a_2. ... .a_k, determine whether it was produced by append_after(unsigned).
    */
    optional<pair<name, unsigned>> is_subscripted() const;

    /**
        \brief If prefix is a prefix of this name, then return a new name where the prefix is replaced with new_prefix.
        Otherwise, return this name.
    */
    name replace_prefix(name const & prefix, name const & new_prefix) const;

    friend void swap(name & a, name & b) { object_ref::swap(a, b); }
    /**
       \brief Quicker version of \c cmp that uses the hashcode.
       Remark: we should not use it when we want to order names using
       lexicographical order.
    */
    friend int quick_cmp(name const & a, name const & b) {
        if (a.raw() == b.raw())
            return 0;
        unsigned h1 = a.hash();
        unsigned h2 = b.hash();
        if (h1 != h2) {
            return h1 < h2 ? -1 : 1;
        } else if (a == b) {
            return 0;
        } else {
            return cmp(a, b);
        }
    }
};

LEAN_EXPORT name string_to_name(std::string const & str);

struct name_hash_fn { unsigned operator()(name const & n) const { return n.hash(); } };
struct name_eq_fn { bool operator()(name const & n1, name const & n2) const { return n1 == n2; } };
struct name_cmp {
    typedef name type;
    int operator()(name const & n1, name const & n2) const { return cmp(n1, n2); }
};
struct name_quick_cmp {
    typedef name type;
    int operator()(name const & n1, name const & n2) const { return quick_cmp(n1, n2); }
};

/** \brief Return true if \c p is part of \c n */
bool is_part_of(std::string const & p, name n);

/**
   \brief Return true iff the two given names are independent.
   That \c a is not a prefix of \c b, nor \c b is a prefix of \c a

   \remark forall a b c d,
               independent(a, b) => independent(join(a, c), join(b, d))
*/
inline bool independent(name const & a, name const & b) {
    return !is_prefix_of(a, b) && !is_prefix_of(b, a);
}

typedef pair<name, name> name_pair;
struct name_pair_quick_cmp {
    int operator()(name_pair const & p1, name_pair const & p2) const {
        int r = quick_cmp(p1.first, p2.first);
        if (r != 0) return r;
        return quick_cmp(p1.second, p2.second);
    }
};

typedef std::function<bool(name const &)> name_predicate; // NOLINT

/** \brief Return true if it is a lean internal name, i.e., the name starts with a `_` */
bool is_internal_name(name const & n);

typedef list_ref<name> names;

void initialize_name();
void finalize_name();
}
