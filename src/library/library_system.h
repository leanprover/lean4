/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/name.h"

namespace lean {
/** \brief Return true iff \c n is the name of a builtin constant from the library.system folder. */
bool is_system_builtin(name const & n);
}
