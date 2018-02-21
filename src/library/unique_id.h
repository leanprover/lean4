/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
*/
#pragma once
#include "util/pair.h"

namespace lean {
class unique_id {
    unsigned m_thread_id;
    unsigned m_id;
    unique_id(unsigned i1, unsigned i2):m_thread_id(i1), m_id(i2) {}
    friend unique_id mk_unique_id();
    friend bool operator==(unique_id const & t1, unique_id const & t2) {
        return t1.m_thread_id == t2.m_thread_id && t1.m_id == t2.m_id;
    }
public:
    /* Use `mk_unique_id()`, this constructor produces and invalid id.
       It can be used to represent uninitialized ids. */
    unique_id();
    bool is_valid() const;
};

inline bool operator!=(unique_id const & t1, unique_id const & t2) {
    return !(t1 == t2);
}

/* Create a global unique id (modulo reset_thread_local).

   Assumptions:
   - We do not create more than 2^32 - 1 threads.
     This is fine because we create a small set of threads
     when we start the process, and then we create only tasks.

   - Each thread does not create more than 2^32 ids.
     This is fine because we reset the thread local counters
     after each \c reset_thread_local operation.

   That being said, if the assumptions above are violated
   \c mk_unique_id throws an exception */
unique_id mk_unique_id();

void initialize_unique_id();
void finalize_unique_id();
}
