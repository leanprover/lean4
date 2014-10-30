/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/kernel_exception.h"
#include "frontends/lean/elaborator_exception.h"

namespace lean {
[[ noreturn ]] void throw_elaborator_exception(environment const & env, char const * msg, expr const & m) {
    throw_kernel_exception(env, msg, m);
}

[[ noreturn ]] void throw_elaborator_exception(environment const & env, sstream const & strm, expr const & m) {
    throw_kernel_exception(env, strm, m);
}

[[ noreturn ]] void throw_elaborator_exception(environment const & env, char const * msg, expr const & m, pp_fn const & fn) {
    throw_kernel_exception(env, msg, m, fn);
}

[[ noreturn ]] void throw_elaborator_exception(environment const & env, expr const & m, pp_fn const & fn) {
    throw_kernel_exception(env, m, fn);
}
}
