/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/elab_environment.h"
namespace lean {
elab_environment compile(elab_environment const & env, options const & opts, names cs);
inline elab_environment compile(elab_environment const & env, options const & opts, name const & c) {
    return compile(env, opts, names(c));
}
void initialize_compiler();
void finalize_compiler();
}
