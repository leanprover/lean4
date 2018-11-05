/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/compiler/util.h"

namespace lean {
pair<environment, comp_decls> to_ir(environment env, comp_decls const & ds);
void initialize_ir();
void finalize_ir();
}
