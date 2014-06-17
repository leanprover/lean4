/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
environment add_calc_subst(environment const & env, name const & subst);
environment add_calc_refl(environment const & env, name const & refl);
environment add_calc_trans(environment const & env, name const & trans);
}
