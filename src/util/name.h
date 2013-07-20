/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <iostream>

namespace lean {

constexpr char const * default_name_separator = "::";

/**
   \brief Hierarchical names.
*/
class name {
    enum class kind { ANONYMOUS, STRING, NUMERAL };
    struct imp;
    imp * m_imp;
    name(imp * p);
public:
    name();
    name(char const * name);
    name(unsigned k);
    name(name const & prefix, char const * name);
    name(name const & prefix, unsigned k);
    name(name const & other);
    name(name && other);
    ~name();
    name & operator=(name const & other);
    name & operator=(name && other);
    bool operator==(name const & other) const;
    bool operator!=(name const & other) const { return !operator==(other); }
    kind get_kind() const;
    bool is_anonymous() const { return get_kind() == kind::ANONYMOUS; }
    bool is_string() const { return get_kind() == kind::STRING; }
    bool is_numeral() const { return get_kind() == kind::NUMERAL; }
    unsigned get_numeral() const;
    char const * get_string() const;
    bool is_atomic() const;
    name get_prefix() const;
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

}
