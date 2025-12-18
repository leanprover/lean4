/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <lean/lean.h>

namespace lean {
LEAN_EXPORT void initialize_library_core_module();
LEAN_EXPORT void finalize_library_core_module();
LEAN_EXPORT void initialize_library_module();
LEAN_EXPORT void finalize_library_module();
}
