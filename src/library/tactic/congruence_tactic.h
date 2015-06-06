/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/type_checker.h"
namespace lean {
enum class congr_arg_kind { Fixed, Singleton, Eq };
optional<expr> mk_congr_subsingleton_thm(type_checker & tc, io_state const & ios,
                                         expr const & fn, optional<unsigned> const & expected_num_args,
                                         buffer<congr_arg_kind> & arg_kinds, constraint_seq & cs);
void initialize_congruence_tactic();
void finalize_congruence_tactic();
}
