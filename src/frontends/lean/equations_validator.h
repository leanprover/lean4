/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "frontends/lean/elaborator.h"
namespace lean {
bool validate_equation_lhs(elaborator & elab, expr const & lhs, expr const & ref);
}
