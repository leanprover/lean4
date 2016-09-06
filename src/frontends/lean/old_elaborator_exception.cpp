/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/exception.h"
#include "frontends/lean/old_elaborator_exception.h"

namespace lean {
[[ noreturn ]] void throw_elaborator_exception(char const * msg, expr const & m) {
    throw generic_exception(m, msg);
}

[[ noreturn ]] void throw_elaborator_exception(sstream const & strm, expr const & m) {
    throw generic_exception(m, strm);
}

[[ noreturn ]] void throw_elaborator_exception(expr const & m, pp_fn const & fn) {
    throw generic_exception(m, fn);
}

[[ noreturn ]] void throw_elaborator_exception(expr const & m, format const & msg) {
    throw_elaborator_exception(m, [=](formatter const &) { return msg; });
}
}
