/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/name.h"
#include "util/splay_map.h"

namespace lean {
inline void open_util_module(lua_State * L) {
    open_name(L);
    open_splay_map(L);
}
}
