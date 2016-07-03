/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/type_context.h"

namespace lean {
pair<expr, optional<expr>> flat_assoc(type_context & ctx, expr const & op, expr const & assoc, expr const & e);
void initialize_ac_tactics();
void finalize_ac_tactics();
}
