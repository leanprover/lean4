/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <vector>
#include <memory>
#include "util/debug.h"

/** \brief Macro for creating a stack of objects of type Cache in thread local storage.
    The argument \c Arg is provided to every new instance of Cache.
    The macro provides the helper class Cache_ref that "reuses" cache objects from the stack.
*/
#define MK_CACHE_STACK(Cache, Arg)                                      \
struct Cache ## _stack {                                                \
    unsigned                                     m_top;                 \
    std::vector<std::unique_ptr<Cache>> m_cache_stack;                  \
    Cache ## _stack():m_top(0) {}                                       \
};                                                                      \
MK_THREAD_LOCAL_GET_DEF(Cache ## _stack, get_ ## Cache ## _stack);      \
class Cache ## _ref {                                                   \
    Cache * m_cache;                                                    \
public:                                                                 \
    Cache ## _ref() {                                                   \
        Cache ## _stack & s = get_ ## Cache ## _stack();                \
        lean_assert(s.m_top <= s.m_cache_stack.size());                 \
        if (s.m_top == s.m_cache_stack.size())                          \
            s.m_cache_stack.push_back(std::unique_ptr<Cache>(new Cache(Arg))); \
        m_cache = s.m_cache_stack[s.m_top].get();                       \
        s.m_top++;                                                      \
    }                                                                   \
    ~Cache ## _ref() {                                                  \
        Cache ## _stack & s = get_ ## Cache ## _stack();                \
        lean_assert(s.m_top > 0);                                       \
        s.m_top--;                                                      \
        m_cache->clear();                                               \
    }                                                                   \
    Cache * operator->() const { return m_cache; }                      \
};                                                                      \

