/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/pos_info_provider.h"
#include "library/local_context.h"
#include "frontends/lean/elaborator_context.h"

namespace lean {
std::tuple<expr, level_param_names> elaborate(elaborator_context const & ectx, local_context const & lctx, expr const & e);
}
