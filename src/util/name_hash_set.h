/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#pragma once
#include <unordered_set>
#include "util/name.h"
namespace lean {
typedef std::unordered_set<name, name_hash, name_eq> name_hash_set;
}
