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
#include "util/rc.h"
#include "util/pair.h"
#include "util/serializer.h"
#include "util/optional.h"
#include "util/list.h"

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

enum class name_kind { ANONYMOUS, STRING, NUMERAL };
/**
   \brief Hierarchical names.
*/
class name {
public:
    /** \brief Actual implementation of hierarchical names. */
    struct imp {
        MK_LEAN_RC()
        bool     m_is_string;
        unsigned m_hash;
        imp *    m_prefix;
        union {
            char * m_str;
            unsigned m_k;
        };
        void dealloc();
        imp(bool s, imp * p):m_rc(1), m_is_string(s), m_hash(0), m_prefix(p) { if (p) p->inc_ref(); }
        static void display_core(std::ostream & out, imp * p, bool escape, char const * sep);
        static void display(std::ostream & out, imp * p, bool escape, char const * sep = lean_name_separator);
        friend void copy_limbs(imp * p, buffer<name::imp *> & limbs);
    };
private:
    friend int cmp(imp * i1, imp * i2);
    friend class name_deserializer;
    imp * m_ptr;
    explicit name(imp * p);
    explicit name(unsigned k);
    // the parameter bool is only used to distinguish this constructor from the public one.
    name(name const & prefix, unsigned k, bool);

    size_t size_core(bool unicode) const;
public:
    name();
    name(char const * name);
    name(std::string const & s):name(s.c_str()) {}
    name(name const & prefix, char const * name);
    name(name const & prefix, unsigned k);
    name(name const & other):m_ptr(other.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
    name(name && other):m_ptr(other.m_ptr) { other.m_ptr = nullptr; }
    /**
       \brief Create a hierarchical name using the given strings.
       Example: <code>name{"foo", "bla", "tst"}</code> creates the hierarchical
       name <tt>foo::bla::tst</tt>.
    */
    name(std::initializer_list<char const *> const & l);
    ~name() { if (m_ptr) m_ptr->dec_ref(); }
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
    name & operator=(name const & other);
    name & operator=(name && other);
    /** \brief Return true iff \c n1 is a prefix of \c n2. */
    friend bool is_prefix_of(name const & n1, name const & n2);
    friend bool eq_core(name::imp * i1, name::imp * i2);
    friend bool operator==(name const & a, name const & b) {
        if (a.m_ptr == b.m_ptr)
            return true;
        if ((a.m_ptr == nullptr) != (b.m_ptr == nullptr))
            return false;
        if (a.m_ptr->m_hash != b.m_ptr->m_hash)
            return false;
        return eq_core(a.m_ptr, b.m_ptr);
    }
    friend bool operator!=(name const & a, name const & b) { return !(a == b); }
    friend bool operator==(name const & a, char const * b);
    friend bool operator!=(name const & a, char const * b) { return !(a == b); }
    /**
        \brief Total order on hierarchical names.
    */
    friend int cmp(name const & a, name const & b) { return cmp(a.m_ptr, b.m_ptr); }
    friend bool operator<(name const & a, name const & b) { return cmp(a, b) < 0; }
    friend bool operator>(name const & a, name const & b) { return cmp(a, b) > 0; }
    friend bool operator<=(name const & a, name const & b) { return cmp(a, b) <= 0; }
    friend bool operator>=(name const & a, name const & b) { return cmp(a, b) >= 0; }
    name_kind kind() const;
    bool is_anonymous() const { return m_ptr == nullptr; }
    bool is_string() const    { return m_ptr != nullptr && m_ptr->m_is_string; }
    bool is_numeral() const   { return m_ptr != nullptr && !m_ptr->m_is_string; }
    explicit operator bool() const { return m_ptr != nullptr; }
    unsigned get_numeral() const { lean_assert(is_numeral()); return m_ptr->m_k; }
    /**
       \brief If the tail of the given hierarchical name is a string, then it returns this string.
       \pre is_string()
    */
    char const * get_string() const { lean_assert(is_string()); return m_ptr->m_str; }
    bool is_atomic() const { return m_ptr == nullptr || m_ptr->m_prefix == nullptr; }
    /**
        \brief Return the prefix of a hierarchical name
    */
    name get_prefix() const { return is_atomic() ? name() : name(m_ptr->m_prefix); }
    /** \brief Given a name of the form a_1.a_2. ... .a_k, return a_1 if k >= 1, or the empty name otherwise. */
    name get_root() const;
    /** \brief Convert this hierarchical name into a string. */
    std::string to_string(char const * sep = lean_name_separator) const;
    std::string escape(char const * sep = lean_name_separator) const;
    /** \brief Size of the this name (in characters). */
    size_t size() const;
    /** \brief Size of the this name in unicode. */
    size_t utf8_size() const;
    unsigned hash() const { return m_ptr ? m_ptr->m_hash : 11; }
    /** \brief Return true iff the name contains only safe ASCII chars */
    bool is_safe_ascii() const;
    friend std::ostream & operator<<(std::ostream & out, name const & n);
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

    friend void swap(name & a, name & b) {
        std::swap(a.m_ptr, b.m_ptr);
    }

    /**
       \brief Quicker version of \c cmp that uses the hashcode.
       Remark: we should not use it when we want to order names using
       lexicographical order.
    */
    friend int quick_cmp(name const & a, name const & b) {
        if (a.m_ptr == b.m_ptr)
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

    struct ptr_hash { unsigned operator()(name const & n) const { return std::hash<imp*>()(n.m_ptr); } };
    struct ptr_eq { bool operator()(name const & n1, name const & n2) const { return n1.m_ptr == n2.m_ptr; } };
};

name string_to_name(std::string const & str);

struct name_hash { unsigned operator()(name const & n) const { return n.hash(); } };
struct name_eq { bool operator()(name const & n1, name const & n2) const { return n1 == n2; } };
struct name_cmp { int operator()(name const & n1, name const & n2) const { return cmp(n1, n2); } };
struct name_quick_cmp { int operator()(name const & n1, name const & n2) const { return quick_cmp(n1, n2); } };

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

serializer & operator<<(serializer & s, name const & n);
name read_name(deserializer & d);
inline deserializer & operator>>(deserializer & d, name & n) { n = read_name(d); return d; }

/** \brief Return true if it is a lean internal name, i.e., the name starts with a `_` */
bool is_internal_name(name const & n);

void initialize_name();
void finalize_name();
}
