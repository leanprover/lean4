/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
#include "library/compiler/util.h"
namespace lean {
pair<environment, comp_decls> extract_closed(environment env, comp_decls const & ds);
void initialize_extract_closed();
void finalize_extract_closed();
}
