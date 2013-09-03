/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <iostream>

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
public:
    name();
    name(char const * name);
    explicit name(unsigned k);
    name(name const & prefix, char const * name);
    name(name const & prefix, unsigned k);
    name(name const & other);
    name(name && other);
    name(std::initializer_list<char const *> const & l);
    ~name();
    static name const & anonymous();
    name & operator=(name const & other);
    name & operator=(name && other);
    /** \brief Return true iff \c n1 is a prefix of \c n2. */
    friend bool is_prefix_of(name const & n1, name const & n2);
    friend bool operator==(name const & a, name const & b);
    friend bool operator!=(name const & a, name const & b) { return !(a == b); }
    friend bool operator==(name const & a, char const * b);
    friend bool operator!=(name const & a, char const * b) { return !(a == b); }
    // total order on hierarchical names.
    friend int cmp(name const & a, name const & b) { return cmp(a.m_ptr, b.m_ptr); }
    friend bool operator<(name const & a, name const & b) { return cmp(a, b) < 0; }
    friend bool operator>(name const & a, name const & b) { return cmp(a, b) > 0; }
    friend bool operator<=(name const & a, name const & b) { return cmp(a, b) <= 0; }
    friend bool operator>=(name const & a, name const & b) { return cmp(a, b) >= 0; }
    name_kind kind() const;
    bool is_anonymous() const { return kind() == name_kind::ANONYMOUS; }
    bool is_string() const    { return kind() == name_kind::STRING; }
    bool is_numeral() const   { return kind() == name_kind::NUMERAL; }
    unsigned get_numeral() const;
    char const * get_string() const;
    bool is_atomic() const;
    name get_prefix() const;
    /**
       \brief Convert this hierarchical name into a string.
    */
    std::string to_string() const;
    /** \brief Size of the this name (in characters). */
    size_t size() const;
    unsigned hash() const;
    /** \brief Return true iff the name contains only safe ASCII chars */
    bool is_safe_ascii() const;
    friend std::ostream & operator<<(std::ostream & out, name const & n);
};
struct name_hash { unsigned operator()(name const & n) const { return n.hash(); } };
struct name_eq { bool operator()(name const & n1, name const & n2) const { return n1 == n2; } };
}
