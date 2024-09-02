/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <lean/lean.h>
#include "runtime/debug.h"

namespace lean {
/**
   \brief Simple optional template. This is a naive replacement for C++14 optional.
   We will delete it as soon optional is supported in g++ and clang++.
*/
template<typename T>
class optional {
    bool m_some;
    union {
        T m_value;
    };
public:
    optional():m_some(false) {}
    optional(optional & other):m_some(other.m_some) {
        if (m_some)
            new (&m_value) T(other.m_value);
    }
    optional(optional const & other):m_some(other.m_some) {
        if (m_some)
            new (&m_value) T(other.m_value);
    }
    optional(optional && other):m_some(other.m_some) {
        if (other.m_some)
            new (&m_value) T(std::move(other.m_value));
    }
    explicit optional(T const & v):m_some(true) {
        new (&m_value) T(v);
    }
    explicit optional(T && v):m_some(true) {
        new (&m_value) T(std::move(v));
    }
    template<typename... Args>
    explicit optional(Args&&... args):m_some(true) {
        new (&m_value) T(std::forward<Args>(args)...);
    }
    ~optional() {
        if (m_some)
            m_value.~T();
    }

    explicit operator bool() const { return m_some; }
    T const * operator->() const { lean_assert(m_some); return &m_value; }
    T * operator->() { lean_assert(m_some); return &m_value; }
    T const & operator*() const { lean_assert(m_some); return m_value; }
    T & operator*() { lean_assert(m_some); return m_value; }
    T const & value() const { lean_assert(m_some); return m_value; }
    T & value() { lean_assert(m_some); return m_value; }

    T const & value_or(T const & default_value) const {
        return m_some ? m_value : default_value;
    }

    template<typename... Args>
    void emplace(Args&&... args) {
        if (m_some)
            m_value.~T();
        m_some = true;
        new (&m_value) T(args...);
    }

    optional& operator=(optional const & other) {
        if (this == &other)
            return *this;
        if (m_some)
            m_value.~T();
        m_some = other.m_some;
        if (m_some)
            new (&m_value) T(other.m_value);
        return *this;
    }
    optional& operator=(optional && other) {
        lean_assert(this != &other);
        if (m_some)
            m_value.~T();
        m_some = other.m_some;
        if (m_some)
            new (&m_value) T(std::move(other.m_value));
        return *this;
    }
    optional& operator=(T const & other) {
        if (m_some)
            m_value.~T();
        m_some = true;
        new (&m_value) T(other);
        return *this;
    }
    optional& operator=(T && other) {
        if (m_some)
            m_value.~T();
        m_some = true;
        new (&m_value) T(std::move(other));
        return *this;
    }

    friend bool operator==(optional const & o1, optional const & o2) {
        if (o1.m_some != o2.m_some)
            return false;
        else
            return !o1.m_some || o1.m_value == o2.m_value;
    }

    friend bool operator!=(optional const & o1, optional const & o2) {
        return !operator==(o1, o2);
    }
};

template<typename T> optional<T> some(T const & t) { return optional<T>(t); }
template<typename T> optional<T> some(T && t) { return optional<T>(std::forward<T>(t)); }

// The following macro creates a template specialization optional<P>, where P
// is an intrusive smart pointer that does not let "customers" point to nullptr.
// That is, if a customer have 'P x', then x is not a pointer to nullptr.
// Requirements:
//  -  P must declare optional<P> as a friend.
//  -  P must handle the nullptr case even if it does not let "customers" point to nullptr
//  -  P must have a field m_ptr a pointer to the actual value.
#define SPECIALIZE_OPTIONAL_FOR_SMART_PTR(P)                            \
template<> class optional<P> {                                          \
    P m_value;                                                          \
public:                                                                 \
    optional():m_value(nullptr) {}                                      \
    optional(optional const & other):m_value(other.m_value) {}          \
    optional(optional && other):m_value(std::move(other.m_value)) {} \
    explicit optional(P const & v):m_value(v) {}                        \
    explicit optional(P && v):m_value(std::move(v)) {}            \
                                                                        \
    explicit operator bool() const { return m_value.m_ptr != nullptr; } \
    P const * operator->() const { lean_assert(m_value.m_ptr); return &m_value; } \
    P * operator->() { lean_assert(m_value.m_ptr); return &m_value; }   \
    P const & operator*() const { lean_assert(m_value.m_ptr); return m_value; } \
    P & operator*() { lean_assert(m_value.m_ptr); return m_value; }     \
    P const & value() const { lean_assert(m_value.m_ptr); return m_value; } \
    P & value() { lean_assert(m_value.m_ptr); return m_value; }         \
    optional & operator=(optional const & other) { m_value = other.m_value; return *this; } \
    optional& operator=(optional && other) { m_value = std::move(other.m_value); return *this; } \
    optional& operator=(P const & other) { m_value = other; return *this; } \
    optional& operator=(P && other) { m_value = std::move(other); return *this; } \
    friend bool operator==(optional const & o1, optional const & o2) {  \
        return static_cast<bool>(o1) == static_cast<bool>(o2) && (!o1 || o1.m_value == o2.m_value); \
    }                                                                   \
    friend bool operator!=(optional const & o1, optional const & o2) {  \
        return !operator==(o1, o2);                                     \
    }                                                                   \
};
}
