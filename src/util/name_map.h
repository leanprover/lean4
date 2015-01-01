/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/rb_map.h"
#include "util/name.h"
namespace lean {
template<typename T> using name_map = rb_map<name, T, name_quick_cmp>;

class rename_map : public name_map<name> {
public:
    // Similar to name_map::find, but it "follows" the sequence of renames.
    // Example, if map contains "A->B" and "B->C", then find(A) returns C.
    // Moreover, if k is not in the map, the result is \c k
    name const & find(name const & k) const;
};
}
