/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <unordered_map>
#include "util/name.h"
namespace lean {
template<typename T> using name_hash_map = std::unordered_map<name, T, name_hash, name_eq>;
}
