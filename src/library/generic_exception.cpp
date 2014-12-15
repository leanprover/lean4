/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "library/generic_exception.h"

namespace lean {

[[ noreturn ]] void throw_generic_exception(char const * msg, optional<expr> const & m) {
    std::string msg_str = msg;
    throw generic_exception(msg, m, [=](formatter const &) { return format(msg_str); });
}

[[ noreturn ]] void throw_generic_exception(sstream const & strm, optional<expr> const & m) {
    throw_generic_exception(strm.str().c_str(), m);
}

[[ noreturn ]] void throw_generic_exception(char const * msg, expr const & m) {
    throw_generic_exception(msg, some_expr(m));
}

[[ noreturn ]] void throw_generic_exception(sstream const & strm, expr const & m) {
    throw_generic_exception(strm, some_expr(m));
}

[[ noreturn ]] void throw_generic_exception(char const * msg, optional<expr> const & m, pp_fn const & fn) {
    throw generic_exception(msg, m, fn);
}

[[ noreturn ]] void throw_generic_exception(char const * msg, expr const & m, pp_fn const & fn) {
    throw_generic_exception(msg, some_expr(m), fn);
}

[[ noreturn ]] void throw_generic_exception(optional<expr> const & m, pp_fn const & fn) {
    throw generic_exception(m, fn);
}

[[ noreturn ]] void throw_generic_exception(expr const & m, pp_fn const & fn) {
    throw_generic_exception(some_expr(m), fn);
}
}
