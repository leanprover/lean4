/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/debug.h"

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
    optional(T const & v):m_some(true) {
        new (&m_value) T(v);
    }
    template<typename... Args>
    optional(Args&&... args):m_some(true) {
        new (&m_value) T(args...);
    }
    optional(optional const & other):m_some(other.m_some) {
        if (m_some)
            new (&m_value) T(other.m_value);
    }
    optional(optional && other):m_some(other.m_some) {
        if (m_some)
            m_value = std::move(other.m_value);
    }
    ~optional() {
        if (m_some)
            m_value.~T();
    }

    operator bool() const { return m_some; }
    T const * operator->() const { lean_assert(m_some); return &m_value; }
    T * operator->() { lean_assert(m_some); return &m_value; }
    T const & operator*() const { lean_assert(m_some); return m_value; }
    T & operator*() { lean_assert(m_some); return m_value; }
    T const & value() const { lean_assert(m_some); return m_value; }
    T & value() { lean_assert(m_some); return m_value; }

    template<typename... Args>
    void emplace(Args&&... args) {
        if (m_some)
            m_value.~T();
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
            new (&m_value) T(std::forward<T>(other.m_value));
        return *this;
    }
    optional& operator=(T const & other) {
        if (m_some)
            m_value.~T();
        m_some = true;
        new (&m_value) T(other.m_value);
        return *this;
    }
    optional& operator=(T && other) {
        if (m_some)
            m_value.~T();
        m_some = true;
        new (&m_value) T(std::forward<T>(other));
        return *this;
    }

    friend bool operator==(optional const & o1, optional const & o2) {
        if (o1.m_some != o2.m_some)
            return false;
        else
            return !o1.m_some || o1.m_value == o2.m_value;
    }
};

template<typename T>
optional<T> some(T && t) {
    return optional<T>(std::forward<T>(t));
}
}
