 /*
Copyright (c) 2015 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Robert Y. Lewis
*/
#pragma once
#include "library/tactic/tactic.h"
#include "library/tactic/location.h"

namespace lean {

void initialize_replace_tactic();
void finalize_replace_tactic();
}
