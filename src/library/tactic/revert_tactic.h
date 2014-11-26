/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/tactic/tactic.h"

namespace lean {
tactic revert_tactic(name const & n);
void initialize_revert_tactic();
void finalize_revert_tactic();
}
