/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Soonho Kong
*/
#pragma once
#include <iostream>

namespace lean {
class name;
class mpq;
class mpz;
struct format_cell;

enum class format_kind { NIL, INDENT, COMPOSE, CHOICE, LINE, TEXT };

/**
   \brief Simple LISP-like S-expressions.
   1. Atoms: nil, string, int, name, mpz or mpq
   2. Pair: (x . y) where x and y are S-expressions.

   S-expressions are used for tracking configuration options, statistics, etc.

   Remark: this datastructure does not allow destructive updates.
*/
class format {
    format_cell* m_ptr;

public:
    format():m_ptr(nullptr) {}
    explicit format(char const * v);
    explicit format(std::string const & v);
    explicit format(int v);
    explicit format(double v);
    explicit format(name const & v);
    explicit format(mpz const & v);
    explicit format(mpq const & v);
    format(format const & h, format const & t);
    template<typename T>
    format(T const & h, format const & t):format(format(h), t) {}
    template<typename T1, typename T2>
    format(T1 const & h, T2 const & t):format(format(h), format(t)) {}
    format(format const & s);
    format(format && s);
    template<typename T>
    format(std::initializer_list<T> const & l):format() {
        auto it = l.end();
        while (it != l.begin()) {
            --it;
            *this = format(*it, *this);
        }
    }
    ~format();

    format_kind kind() const;

    friend bool is_nil(format const & s) { return s.m_ptr == nullptr; }

    std::string const & get_string() const;

    unsigned hash() const;

    format & operator=(format const & s);
    format & operator=(format&& s);
    template<typename T>
    format & operator=(T const & v) { return operator=(format(v)); }

    friend void swap(format & a, format & b) { std::swap(a.m_ptr, b.m_ptr); }

    // Pointer equality
    friend bool eqp(format const & a, format const & b) { return a.m_ptr == b.m_ptr; }

    friend std::ostream & operator<<(std::ostream & out, format const & s);

};

inline format compose(format const & head, format const & tail) { return format(head, tail); }
inline format choice(format const & head, format const & tail) { return format(head, tail); }
inline format indent(format const & f, unsigned i) { return f; }
inline format line(format const & f) { return f; }

inline bool is_compose(format const & s)   { return s.kind() != format_kind::COMPOSE; }
inline bool is_indent(format const & s)   { return s.kind() == format_kind::INDENT; }
inline bool is_text(format const & s) { return s.kind() == format_kind::TEXT; }
inline bool is_line(format const & s)    { return s.kind() == format_kind::LINE; }
inline bool is_choice(format const & s) { return s.kind() == format_kind::CHOICE; }

inline std::string const & to_string(format const & s) { return s.get_string(); }
}
