/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <iostream>
#include <string>
#include <algorithm>
#include <functional>
#include <memory>
#include "util/serializer.h"

namespace lean {
class name;
struct sexpr_cell;

enum class sexpr_kind { Nil, String, Bool, Int, Double, Name, Cons, Ext };

class sexpr_ext_atom;

/**
   \brief Simple LISP-like S-expressions.
   1. Atoms: nil, string, int, name
   2. Pair: (x . y) where x and y are S-expressions.

   S-expressions are used for tracking configuration options, statistics, etc.

   Remark: this datastructure does not allow destructive updates.
*/
class sexpr {
    sexpr_cell * m_ptr;
    sexpr_cell * steal_ptr() { sexpr_cell * r = m_ptr; m_ptr = nullptr; return r; }
    friend struct sexpr_cons;
public:
    sexpr():m_ptr(nullptr) {}
    explicit sexpr(char const * v);
    explicit sexpr(std::string const & v);
    explicit sexpr(bool v);
    explicit sexpr(int v);
    explicit sexpr(double v);
    explicit sexpr(name const & v);
    explicit sexpr(std::unique_ptr<sexpr_ext_atom> && v);
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

    sexpr_kind kind() const;
    sexpr_cell const * raw() const { return m_ptr; }

    explicit operator bool() const { return m_ptr != nullptr; }

    friend bool is_nil(sexpr const & s) { return s.m_ptr == nullptr; }
    friend sexpr const & head(sexpr const & s);
    friend sexpr const & tail(sexpr const & s);

    std::string const & get_string() const;
    int get_int() const;
    bool get_bool() const;
    double get_double() const;
    name const & get_name() const;
    sexpr_ext_atom const & get_ext() const;

    /** \brief Hash code for this S-expression*/
    unsigned hash() const;

    sexpr & operator=(sexpr const & s);
    sexpr & operator=(sexpr&& s);
    template<typename T>
    sexpr & operator=(T const & v) { return operator=(sexpr(v)); }

    friend void swap(sexpr & a, sexpr & b) { std::swap(a.m_ptr, b.m_ptr); }

    /** \brief Pointer equality */
    friend bool is_eqp(sexpr const & a, sexpr const & b) { return a.m_ptr == b.m_ptr; }

    struct ptr_hash { unsigned operator()(sexpr const & a) const { return std::hash<sexpr_cell*>()(a.m_ptr); } };
    struct ptr_eq { unsigned operator()(sexpr const & a1, sexpr const & a2) const { return is_eqp(a1, a2); } };

    friend std::ostream & operator<<(std::ostream & out, sexpr const & s);
};

class sexpr_ext_atom {
public:
    virtual ~sexpr_ext_atom() {}
    virtual int cmp(sexpr_ext_atom const & e) const = 0;
    virtual unsigned hash() const = 0;
    virtual void display(std::ostream & out) const = 0;
};

/** \brief Return the nil S-expression */
inline sexpr nil() { return sexpr(); }
/** \brief Return a cons-cell (aka pair) composed of \c head and \c tail */
inline sexpr cons(sexpr const & head, sexpr const & tail) { return sexpr(head, tail); }
/**
    \brief Return the first argument of the given cons cell (aka pair).
    \pre is_cons(s)
*/
inline sexpr const & car(sexpr const & s) { return head(s); }
/**
    \brief Return the second argument of the given cons cell (aka pair).
    \pre is_cons(s)
*/
inline sexpr const & cdr(sexpr const & s) { return tail(s); }
/** \brief Return true iff \c s is not an atom (i.e., it is not a cons cell). */
inline bool is_atom(sexpr const & s)     { return s.kind() != sexpr_kind::Cons; }
/** \brief Return true iff \c s is not a cons cell. */
inline bool is_cons(sexpr const & s)     { return s.kind() == sexpr_kind::Cons; }
inline bool is_string(sexpr const & s)   { return s.kind() == sexpr_kind::String; }
inline bool is_bool(sexpr const & s)     { return s.kind() == sexpr_kind::Bool; }
inline bool is_int(sexpr const & s)      { return s.kind() == sexpr_kind::Int; }
inline bool is_double(sexpr const & s)   { return s.kind() == sexpr_kind::Double; }
inline bool is_name(sexpr const & s)     { return s.kind() == sexpr_kind::Name; }
inline bool is_external(sexpr const & s) { return s.kind() == sexpr_kind::Ext; }

inline std::string const & to_string(sexpr const & s) { return s.get_string(); }
inline bool to_bool(sexpr const & s) { return s.get_bool(); }
inline int to_int(sexpr const & s) { return s.get_int(); }
inline double to_double(sexpr const & s) { return s.get_double(); }
inline name const & to_name(sexpr const & s) { return s.get_name(); }
inline sexpr_ext_atom const & to_ext(sexpr const & s) { return s.get_ext(); }

/** \brief Return true iff \c s is nil or \c s is a cons cell where \c is_list(tail(s)). */
bool is_list(sexpr const & s);
/**
    \brief Return the length of the given list.
    \pre is_list(s)
*/
unsigned length(sexpr const & s);
/** \brief Alias for #length. */
inline unsigned len(sexpr const & s) { return length(s); }

/** \brief Return true iff the two given S-expressions are structurally identical.
    \warning This is not pointer equality.
*/
bool operator==(sexpr const & a, sexpr const & b);
inline bool operator==(sexpr const & a, bool b) { return is_int(a) && to_bool(a) == b; }
inline bool operator==(sexpr const & a, int b) { return is_int(a) && to_int(a) == b; }
inline bool operator==(sexpr const & a, double b) { return is_double(a) && to_double(a) == b; }
inline bool operator==(sexpr const & a, std::string const & b) { return is_string(a) && to_string(a) == b; }
inline bool operator==(sexpr const & a, char const * b) { return is_string(a) && to_string(a) == b; }
bool operator==(sexpr const & a, name const & b);
template<typename T> inline bool operator==(T const & a, sexpr const & b) { return b == a; }
inline bool operator!=(sexpr const & a, sexpr const & b) { return !(a == b); }
template<typename T> inline bool operator!=(sexpr const & a, T const & b) { return !(a == b); }
template<typename T> inline bool operator!=(T const & a, sexpr const & b) { return !(a == b); }
/**
   \brief Total order on S-expressions.
*/
int cmp(sexpr const & a, sexpr const & b);
inline bool operator<(sexpr const & a, sexpr const & b) { return cmp(a, b) < 0; }
inline bool operator>(sexpr const & a, sexpr const & b) { return cmp(a, b) > 0; }
inline bool operator<=(sexpr const & a, sexpr const & b) { return cmp(a, b) <= 0; }
inline bool operator>=(sexpr const & a, sexpr const & b) { return cmp(a, b) >= 0; }

serializer & operator<<(serializer & s, sexpr const & a);
sexpr read_sexpr(deserializer & d);
inline deserializer & operator>>(deserializer & d, sexpr & a) { a = read_sexpr(d); return d; }

void initialize_sexpr();
void finalize_sexpr();
}
