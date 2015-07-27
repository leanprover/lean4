/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/rb_tree.h"
#include "util/name.h"
#include "util/lua.h"
namespace lean {
typedef rb_tree<name, name_quick_cmp> name_set;
/** \brief Make a name that does not occur in \c s, based on the given suggestion. */
name mk_unique(name_set const & s, name const & suggestion);

name_set to_name_set(buffer<name> const & ns);

UDATA_DEFS_CORE(name_set)
void open_name_set(lua_State * L);
}
