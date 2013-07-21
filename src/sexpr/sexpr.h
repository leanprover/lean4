/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <iostream>

namespace lean {
class name;
class mpq;
class mpz;
struct sexpr_cell;

/**
   \brief Simple LISP-like S-expressions.
   1. Atoms: nil, string, int, name, mpz or mpq
   2. Pair: (x . y) where x and y are S-expressions.

   S-expressions are used for tracking configuration options, statistics, etc.

   Remark: this datastructure does not allow destructive updates.
*/
class sexpr {
    sexpr_cell * m_ptr;
public:
    enum class kind { NIL, STRING, INT, DOUBLE, NAME, MPZ, MPQ, CONS };
    sexpr():m_ptr(nullptr) {}
    explicit sexpr(char const * v);
    explicit sexpr(std::string const & v);
    explicit sexpr(int v);
    explicit sexpr(double v);
    explicit sexpr(name const & v);
    explicit sexpr(mpz const & v);
    explicit sexpr(mpq const & v);
    sexpr(sexpr const & h, sexpr const & t);
    template<typename T>
    sexpr(T const & h, sexpr const & t):sexpr(sexpr(h), t) {}
    template<typename T1, typename T2>
    sexpr(T1 const & h, T2 const & t):sexpr(sexpr(h), sexpr(t)) {}
    sexpr(sexpr const & s);
    sexpr(sexpr && s);
    template<typename T>
    sexpr(std::initializer_list<T> const & l):sexpr() {
        auto it = l.end();
        while (it != l.begin()) {
            --it;
            *this = sexpr(*it, *this);
        }
    }
    ~sexpr();

    kind get_kind() const;

    friend bool is_nil(sexpr const & s) { return s.m_ptr == nullptr; }
    friend sexpr const & head(sexpr const & s);
    friend sexpr const & tail(sexpr const & s);

    std::string const & get_string() const;
    int get_int() const;
    double get_double() const;
    name const & get_name() const;
    mpz const & get_mpz() const;
    mpq const & get_mpq() const;

    unsigned hash() const;

    sexpr & operator=(sexpr const & s);
    sexpr & operator=(sexpr&& s);
    template<typename T>
    sexpr & operator=(T const & v) { return operator=(sexpr(v)); }

    friend void swap(sexpr & a, sexpr & b) { std::swap(a.m_ptr, b.m_ptr); }

    // Pointer equality
    friend bool eqp(sexpr const & a, sexpr const & b) { return a.m_ptr == b.m_ptr; }

    friend std::ostream & operator<<(std::ostream & out, sexpr const & s);

};

inline sexpr nil() { return sexpr(); }
inline sexpr cons(sexpr const & head, sexpr const & tail) { return sexpr(head, tail); }
inline sexpr const & car(sexpr const & s) { return head(s); }
inline sexpr const & cdr(sexpr const & s) { return tail(s); }
inline bool is_atom(sexpr const & s) { return s.get_kind() != sexpr::kind::CONS; }
inline bool is_cons(sexpr const & s) { return s.get_kind() == sexpr::kind::CONS; }

inline bool is_string(sexpr const & s) { return s.get_kind() == sexpr::kind::STRING; }
inline bool is_int(sexpr const & s) { return s.get_kind() == sexpr::kind::INT; }
inline bool is_double(sexpr const & s) { return s.get_kind() == sexpr::kind::DOUBLE; }
inline bool is_name(sexpr const & s) { return s.get_kind() == sexpr::kind::NAME; }
inline bool is_mpz(sexpr const & s) { return s.get_kind() == sexpr::kind::MPZ; }
inline bool is_mpq(sexpr const & s) { return s.get_kind() == sexpr::kind::MPQ; }

inline std::string const & to_string(sexpr const & s) { return s.get_string(); }
inline int to_int(sexpr const & s) { return s.get_int(); }
inline double to_double(sexpr const & s) { return s.get_double(); }
inline name const & to_name(sexpr const & s) { return s.get_name(); }
inline mpz const & to_mpz(sexpr const & s) { return s.get_mpz(); }
inline mpq const & to_mpq(sexpr const & s) { return s.get_mpq(); }

bool is_list(sexpr const & s);
unsigned length(sexpr const & s);
inline unsigned len(sexpr const & s) { return length(s); }

bool operator==(sexpr const & a, sexpr const & b);
inline bool operator==(sexpr const & a, int b) { return is_int(a) && to_int(a) == b; }
inline bool operator==(sexpr const & a, double b) { return is_double(a) && to_double(a) == b; }
inline bool operator==(sexpr const & a, std::string const & b) { return is_string(a) && to_string(a) == b; }
bool operator==(sexpr const & a, name const & b);
bool operator==(sexpr const & a, mpz const & b);
bool operator==(sexpr const & a, mpq const & b);
template<typename T> inline bool operator==(T const & a, sexpr const & b) { return b == a; }
inline bool operator!=(sexpr const & a, sexpr const & b) { return !(a == b); }
template<typename T> inline bool operator!=(sexpr const & a, T const & b) { return !(a == b); }
template<typename T> inline bool operator!=(T const & a, sexpr const & b) { return !(a == b); }
bool operator<(sexpr const & a, sexpr const & b);
inline bool operator>(sexpr const & a, sexpr const & b) { return b < a; }
inline bool operator<=(sexpr const & a, sexpr const & b) { return !(a > b); }
inline bool operator>=(sexpr const & a, sexpr const & b) { return !(a < b); }

}
