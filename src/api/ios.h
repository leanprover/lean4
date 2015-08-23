/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/io_state.h"
#include "api/expr.h"
#include "api/lean_ios.h"
namespace lean {
inline io_state * to_io_state(lean_ios n) { return reinterpret_cast<io_state *>(n); }
inline io_state const & to_io_state_ref(lean_ios n) { return *reinterpret_cast<io_state *>(n); }
inline lean_ios of_io_state(io_state * n) { return reinterpret_cast<lean_ios>(n); }
}
