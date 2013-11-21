/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/test.h"
#include "library/tactic/goal.h"
#include "library/tactic/proof_builder.h"
#include "library/tactic/justification_builder.h"
#include "library/tactic/proof_state.h"
#include "library/tactic/tactic.h"
using namespace lean;

int main() {
    return has_violations() ? 1 : 0;
}
