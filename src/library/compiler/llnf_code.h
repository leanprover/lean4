/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/compiler/util.h"

namespace lean {
/* Store `ds` in the current module LLNF code sequence. */
environment save_llnf_code(environment const & env, comp_decls const & ds);
/* Return the LLNF code for the current module. */
comp_decls get_llnf_code(environment const & env);
void initialize_llnf_code();
void finalize_llnf_code();
}
