/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/name.h"
#include "kernel/level.h"
#include "api/exception.h"
#include "api/options.h"
#include "api/lean_univ.h"
namespace lean {
inline level * to_level(lean_univ n) { return reinterpret_cast<level *>(n); }
inline level const & to_level_ref(lean_univ n) { return *reinterpret_cast<level *>(n); }
inline lean_univ of_level(level * n) { return reinterpret_cast<lean_univ>(n); }
void to_buffer(unsigned sz, lean_univ const * us, buffer<level> & r);

inline list<level> * to_list_level(lean_list_univ n) { return reinterpret_cast<list<level> *>(n); }
inline list<level> const & to_list_level_ref(lean_list_univ n) { return *reinterpret_cast<list<level> *>(n); }
inline lean_list_univ of_list_level(list<level> * n) { return reinterpret_cast<lean_list_univ>(n); }
}
