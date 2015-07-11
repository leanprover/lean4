/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
#include "library/tactic/location.h"

namespace lean {
optional<expr> unfold_rec(environment const & env, name_generator && ngen, bool force_unfold, expr const & e,
                          list<name> const & to_unfold, occurrence const & occs);
}
