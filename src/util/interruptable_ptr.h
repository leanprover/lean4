/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/thread.h"

namespace lean {
/**
    \brief Auxiliary class that wraps a pointer to a type that has a
    set_interrupt method. The set_interrupt can be invoked from a different
    execution thread. To prevent race conditions, we use mutex whenever we
    reset the pointer, or invoke the set_interrupt method.

    The common usage scenario is:
    1) Thread A creates creates a new object Obj and invokes set(Obj)
    2) Thread B invokes set_interrupt, which invokes Obj->set_interrupt
    3) Thread A invokes set(nullptr) before deleting Obj.

    We use the mutex to avoid a race condition in 2&3.
*/
template<typename T>
class interruptable_ptr {
    T *   m_ptr;
    mutex m_mutex;
public:
    interruptable_ptr():m_ptr(nullptr) {}

    T * set(T * ptr) {
        lock_guard<mutex> lock(m_mutex);
        T * old = m_ptr;
        m_ptr = ptr;
        return old;
    }

    void set_interrupt(bool flag) {
        lock_guard<mutex> lock(m_mutex);
        if (m_ptr)
            m_ptr->set_interrupt(flag);
    }
};

/**
   \brief Auxiliary class for setting/resetting  a interruptable_ptr.
*/
template<typename T>
struct scoped_set_interruptable_ptr {
    interruptable_ptr<T> & m_ptr;
    T *                    m_old_p;
public:
    scoped_set_interruptable_ptr(interruptable_ptr<T> & ptr, T * p):m_ptr(ptr) {
        m_old_p = m_ptr.set(p);
    }
    ~scoped_set_interruptable_ptr() {
        m_ptr.set(m_old_p);
    }
};
}
