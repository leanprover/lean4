/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "frontends/lean/elaborator.h"

namespace lean {
std::tuple<expr, level_param_names> elaborate(elaborator_context const & /* ectx */, local_context const & /* lctx */,
                                              expr const & e) {
    // TODO(Leo)
    return std::make_tuple(e, level_param_names());
}
}
