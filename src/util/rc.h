/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once

// Goodies for reference counting
#ifdef LEAN_THREAD_UNSAFE
#define MK_LEAN_RC()                                                    \
private:                                                                \
unsigned m_rc;                                                          \
public:                                                                 \
unsigned get_rc() const { return m_rc; }                                \
void inc_ref() { m_rc++; }                                              \
bool dec_ref_core() { lean_assert(get_rc() > 0);  m_rc--; return m_rc == 0; } \
void dec_ref() { if (dec_ref_core()) dealloc(); }
#else
#include <atomic>
#define MK_LEAN_RC()                                                    \
private:                                                                \
std::atomic<unsigned> m_rc;                                             \
public:                                                                 \
unsigned get_rc() const { return std::atomic_load(&m_rc); }             \
void inc_ref() { std::atomic_fetch_add_explicit(&m_rc, 1u, std::memory_order_relaxed); } \
bool dec_ref_core() { lean_assert(get_rc() > 0); return std::atomic_fetch_sub_explicit(&m_rc, 1u, std::memory_order_relaxed) == 1u; } \
void dec_ref() { if (dec_ref_core()) dealloc(); }
#endif
#include "util/debug.h"

#define LEAN_COPY_REF(T, Arg)                   \
    if (Arg.m_ptr)                              \
        Arg.m_ptr->inc_ref();                   \
    auto new_ptr = Arg.m_ptr;                   \
    if (m_ptr)                                  \
        m_ptr->dec_ref();                       \
    m_ptr = new_ptr;                            \
    return *this;

#define LEAN_MOVE_REF(T, Arg)                   \
    if (m_ptr)                                  \
        m_ptr->dec_ref();                       \
    m_ptr   = Arg.m_ptr;                        \
    Arg.m_ptr = nullptr;                        \
    return *this;
