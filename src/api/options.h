/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/sexpr/options.h"
#include "api/exception.h"
#include "api/name.h"
#include "api/lean_options.h"
namespace lean {
inline options * to_options(lean_options n) { return reinterpret_cast<options *>(n); }
inline options const & to_options_ref(lean_options n) { return *reinterpret_cast<options *>(n); }
inline lean_options of_options(options * n) { return reinterpret_cast<lean_options>(n); }
}
