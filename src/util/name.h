/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <iostream>

namespace lean {

constexpr char const * default_name_separator = "\u2055";
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
    explicit name(char const * name);
    explicit name(unsigned k);
    name(name const & prefix, char const * name);
    name(name const & prefix, unsigned k);
    name(name const & other);
    name(name && other);
    ~name();
    name & operator=(name const & other);
    name & operator=(name && other);
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
       \brief Convert this hierarchical name into a string using the given separator to "glue" the different limbs.
    */
    std::string to_string(char const * sep = default_name_separator) const;
    /**
       \brief Size of the this name (in characters) when using the given separator.
    */
    size_t size(char const * sep = default_name_separator) const;
    unsigned hash() const;
    friend std::ostream & operator<<(std::ostream & out, name const & n);
    class sep {
        name const & m_name;
        char const * m_sep;
    public:
        sep(name const & n, char const * s);
        friend std::ostream & operator<<(std::ostream & out, sep const & s);
    };
    friend std::ostream & operator<<(std::ostream & out, sep const & s);
};
struct name_hash { unsigned operator()(name const & n) const { return n.hash(); } };
struct name_eq { bool operator()(name const & n1, name const & n2) const { return n1 == n2; } };
}
