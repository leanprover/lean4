/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/name.h"
#include "library/constants.h"

namespace lean {
bool is_system_builtin(name const & n) {
    return
        n == get_io_name() ||
        n == get_io_functor_name() ||
        n == get_io_monad_name() ||
        n == get_put_str_name() ||
        n == get_put_nat_name() ||
        n == get_get_line_name();
}
}
