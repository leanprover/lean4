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
}
