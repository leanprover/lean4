/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/thread.h"
namespace lean {
/**
   \brief The class \c unlock_guard is a mutex wrapper that provides a
   convenient RAII-style mechanism for releasing a mutex for the
   duration of a scoped block.

   It is the dual of lock_guard in the standard library.

   Example:
   <code>
      {
         lock_guard<mutex> lock(m);
         ...
         {
             unlock_guard unlock(m);
             ...
         }
         ...
     }
   </code>

   \warning The calling thread must own the lock to m_mutex
*/
class unlock_guard {
    mutex & m_mutex;
public:
    explicit unlock_guard(mutex & m):m_mutex(m) { m_mutex.unlock(); }
    unlock_guard(unlock_guard const &) = delete;
    unlock_guard(unlock_guard &&) = delete;
    unlock_guard & operator=(unlock_guard const &) = delete;
    unlock_guard & operator=(unlock_guard &&) = delete;
    ~unlock_guard() { m_mutex.lock(); }
};
}
