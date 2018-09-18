/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
namespace lean {
name const & get_aux_match_suffix();
name mk_aux_match_suffix(unsigned idx);
expr unfold_aux_match(environment const & env, expr const & e);
bool is_aux_match(name const & n);
void initialize_aux_match();
void finalize_aux_match();
}
