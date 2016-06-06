/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/tactic/tactic.h"

namespace lean {
tactic clear_tactic(name const & n);
void initialize_clear_tactic();
void finalize_clear_tactic();
}
