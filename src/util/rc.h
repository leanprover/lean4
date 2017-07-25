/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once

// Goodies for reference counting
#include "util/thread.h"
#include "util/debug.h"

#define MK_LEAN_RC()                                                    \
private:                                                                \
atomic<unsigned> m_rc;                                                  \
public:                                                                 \
unsigned get_rc() const { return atomic_load_explicit(&m_rc, memory_order_acquire); } \
void inc_ref() { atomic_fetch_add_explicit(&m_rc, 1u, memory_order_relaxed); } \
bool dec_ref_core() {                                                   \
    lean_assert(get_rc() > 0);                                          \
    if (atomic_fetch_sub_explicit(&m_rc, 1u, memory_order_acq_rel) == 1u) { \
        return true;                                                    \
    } else {                                                            \
        return false;                                                   \
    }                                                                   \
}                                                                       \
void dec_ref() { if (dec_ref_core()) { dealloc(); } }

#define LEAN_COPY_REF(Arg)                      \
    if (Arg.m_ptr)                              \
        Arg.m_ptr->inc_ref();                   \
    auto new_ptr = Arg.m_ptr;                   \
    if (m_ptr)                                  \
        m_ptr->dec_ref();                       \
    m_ptr = new_ptr;                            \
    return *this;

#define LEAN_MOVE_REF(Arg)                      \
    if (m_ptr)                                  \
        m_ptr->dec_ref();                       \
    m_ptr   = Arg.m_ptr;                        \
    Arg.m_ptr = nullptr;                        \
    return *this;
