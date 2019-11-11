/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
namespace lean {
/**
   \brief Template for simulating "fluid-resets".
   Example:
   <code>
   {
     freset<cache> reset(m_cache); // reset the cache inside this scope

   } // restore original value of m_cache
   </code>

   \remark The reset is performed by creating a fresh value and performing a swap.
*/
template<typename T>
class freset {
    T & m_ref;
    T   m_saved_value;
public:
    freset(T & ref):
        m_ref(ref) {
        using std::swap;
        swap(m_ref, m_saved_value);
    }

    ~freset() {
        using std::swap;
        swap(m_ref, m_saved_value);
    }
};
}
