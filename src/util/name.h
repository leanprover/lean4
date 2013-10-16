/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include <iostream>
#include <algorithm>

namespace lean {
constexpr char const * lean_name_separator = "::";
enum class name_kind { ANONYMOUS, STRING, NUMERAL };
/**
   \brief Hierarchical names.
*/
class name {
    struct imp;
    friend int cmp(imp * i1, imp * i2);
    imp * m_ptr;
    explicit name(imp * p);
    explicit name(unsigned k);
    // the parameter bool is only used to distinguish this constructor from the public one.
    name(name const & prefix, unsigned k, bool);
public:
    name();
    name(char const * name);
    name(name const & prefix, char const * name);
    name(name const & prefix, unsigned k);
    name(name const & other);
    name(name && other);
    /**
       \brief Create a hierarchical name using the given strings.
       Example: <code>name{"foo", "bla", "tst"}</code> creates the hierarchical
       name <tt>foo::bla::tst</tt>.
    */
    name(std::initializer_list<char const *> const & l);
    ~name();
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
    friend bool operator==(name const & a, name const & b);
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
    bool is_anonymous() const { return kind() == name_kind::ANONYMOUS; }
    bool is_string() const    { return kind() == name_kind::STRING; }
    bool is_numeral() const   { return kind() == name_kind::NUMERAL; }
    operator bool() const     { return !is_anonymous(); }
    unsigned get_numeral() const;
    /**
       \brief If the tail of the given hierarchical name is a string, then it returns this string.
       \pre is_string()
    */
    char const * get_string() const;
    bool is_atomic() const;
    /**
        \brief Return the prefix of a hierarchical name
        \pre !is_atomic()
    */
    name get_prefix() const;
    /** \brief Convert this hierarchical name into a string. */
    std::string to_string() const;
    /** \brief Size of the this name (in characters). */
    size_t size() const;
    unsigned hash() const;
    /** \brief Return true iff the name contains only safe ASCII chars */
    bool is_safe_ascii() const;
    friend std::ostream & operator<<(std::ostream & out, name const & n);
    /** \brief Concatenate the two given names. */
    friend name operator+(name const & n1, name const & n2);

    friend void swap(name & a, name & b) {
        std::swap(a.m_ptr, b.m_ptr);
    }
};
struct name_hash { unsigned operator()(name const & n) const { return n.hash(); } };
struct name_eq { bool operator()(name const & n1, name const & n2) const { return n1 == n2; } };
struct name_cmp { int operator()(name const & n1, name const & n2) const { return cmp(n1, n2); } };
}
