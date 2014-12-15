/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
#include "kernel/formatter.h"

namespace lean {
[[ noreturn ]] void throw_elaborator_exception(char const * msg, expr const & m);
[[ noreturn ]] void throw_elaborator_exception(sstream const & strm, expr const & m);
[[ noreturn ]] void throw_elaborator_exception(char const * msg, expr const & m, pp_fn const & fn);
[[ noreturn ]] void throw_elaborator_exception(expr const & m, pp_fn const & fn);
}
