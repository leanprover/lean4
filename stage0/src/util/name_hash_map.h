/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/alloc.h"
#include "util/name.h"
namespace lean {
template<typename T> using name_hash_map = lean::unordered_map<name, T, name_hash_fn, name_eq_fn>;
}
