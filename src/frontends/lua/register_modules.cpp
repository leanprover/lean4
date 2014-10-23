/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/script_state.h"
#include "util/numerics/register_module.h"
#include "util/sexpr/register_module.h"
#include "library/register_module.h"
#include "library/tactic/register_module.h"
#include "frontends/lean/register_module.h"

namespace lean {
void register_modules() {
    register_numerics_module();
    register_sexpr_module();
    register_core_module();
    register_tactic_module();
    register_frontend_lean_module();
}
}
