/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Henrik Böving
*/
#pragma once
#include <absl/container/flat_hash_map.h>
#include "util/alloc.h"
#include "util/name.h"

namespace lean {
/* Open-addressing hash map. Unlike `lean::unordered_map`, inserting may move existing entries, so
   references and iterators into the map are invalidated by every insertion. */
template<
    class Key,
    class T,
    class Hash,
    class KeyEqual,
    class Allocator = lean::allocator<std::pair<const Key, T>>
> using flat_hash_map = absl::flat_hash_map<Key, T, Hash, KeyEqual, Allocator>;

// `name_hash_fn` truncates to 32 bits but `flat_hash_map` derives both its probe position and the
// per-slot control bits from the hash, so use all of it.
struct name_full_hash_fn { size_t operator()(name const & n) const { return n.hash(); } };

template<typename T> using name_flat_hash_map = flat_hash_map<name, T, name_full_hash_fn, name_eq_fn>;
}
