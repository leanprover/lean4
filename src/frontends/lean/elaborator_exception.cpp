/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/generic_exception.h"
#include "frontends/lean/elaborator_exception.h"

namespace lean {
[[ noreturn ]] void throw_elaborator_exception(char const * msg, expr const & m) {
    throw_generic_exception(msg, m);
}

[[ noreturn ]] void throw_elaborator_exception(sstream const & strm, expr const & m) {
    throw_generic_exception(strm, m);
}

[[ noreturn ]] void throw_elaborator_exception(char const * msg, expr const & m, pp_fn const & fn) {
    throw_generic_exception(msg, m, fn);
}

[[ noreturn ]] void throw_elaborator_exception(expr const & m, pp_fn const & fn) {
    throw_generic_exception(m, fn);
}
}
