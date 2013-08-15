/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <unordered_map>

namespace lean {
/**
   \brief Helper function for inserting k->v into the map \c m.
*/
template<typename M>
void insert(M & m, typename M::key_type const & k, typename M::mapped_type const & v) {
    auto p = m.insert(std::make_pair(k, v));
    if (!p.second) {
        // m already contains an entry with key \c k.
        p.first->second = v;
    }
}
}
