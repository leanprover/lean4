/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
environment add_subst(environment const & env, name const & n, bool persistent = true);
environment add_refl(environment const & env, name const & n, bool persistent = true);
environment add_symm(environment const & env, name const & n, bool persistent = true);
environment add_trans(environment const & env, name const & n, bool persistent = true);
optional<std::tuple<name, unsigned, unsigned>> get_refl_extra_info(environment const & env, name const & op);
optional<std::tuple<name, unsigned, unsigned>> get_subst_extra_info(environment const & env, name const & op);
optional<std::tuple<name, unsigned, unsigned>> get_symm_extra_info(environment const & env, name const & op);
optional<std::tuple<name, name, unsigned>> get_trans_extra_info(environment const & env, name const & op1, name const & op2);
optional<name> get_refl_info(environment const & env, name const & op);
optional<name> get_symm_info(environment const & env, name const & op);
optional<name> get_trans_info(environment const & env, name const & op);
void initialize_equivalence_manager();
void finalize_equivalence_manager();
}
