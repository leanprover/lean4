/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/
#pragma once
#include "library/vm/vm.h"
#include "library/tactic/tactic_state.h"

namespace lean {
vm_obj user_attribute_get_cache(vm_state & S, tactic_state const & s, name const & attr_name);
void initialize_user_attribute();
void finalize_user_attribute();
}
