/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/vm/vm.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/smt/congruence_closure.h"
#include "library/tactic/smt/ematch.h"

namespace lean {
bool is_cc_state(vm_obj const & o);
congruence_closure::state const & to_cc_state(vm_obj const & o);
vm_obj to_obj(congruence_closure::state const & s);

tactic_state update_defeq_canonizer_state(tactic_state const & s, congruence_closure const & cc);

void initialize_congruence_tactics();
void finalize_congruence_tactics();
}
