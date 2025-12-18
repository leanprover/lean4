/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <lean/lean.h>

namespace lean {
LEAN_EXPORT void initialize_runtime_module();
LEAN_EXPORT void finalize_runtime_module();
}
