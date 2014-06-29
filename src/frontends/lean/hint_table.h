/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/rb_map.h"
#include "library/tactic/tactic.h"

namespace lean {
typedef rb_map<unsigned, tactic, unsigned_cmp> hint_table;
}
