/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/elab_environment.h"
#include "library/compiler/util.h"
namespace lean {
bool is_extract_closed_aux_fn(name const & n);
pair<elab_environment, comp_decls> extract_closed(elab_environment env, comp_decls const & ds);
}
