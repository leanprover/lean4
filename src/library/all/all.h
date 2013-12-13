/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
/** \brief Import all builtin libraries and theorems */
void import_all(environment const & env);
/** \brief Create top-level environment with all builtin libraries and theorems */
environment mk_toplevel();
}
