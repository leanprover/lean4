/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/tactic/tactic_state.h"
namespace lean {
vm_obj assert_define_core(bool is_assert, name const & n, expr const & t, tactic_state const & s);
vm_obj assertv_definev_core(bool is_assert, name const & n, expr const & t, expr const & v, tactic_state const & s);
vm_obj assertv_definev(bool is_assert, name const & n, expr const & t, expr const & v, tactic_state const & s);
void initialize_assert_tactic();
void finalize_assert_tactic();
}
