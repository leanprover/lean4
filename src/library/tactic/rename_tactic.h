/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/tactic/tactic.h"

namespace lean {
tactic rename_tactic(name const & from, name const & to);
void initialize_rename_tactic();
void finalize_rename_tactic();
}
