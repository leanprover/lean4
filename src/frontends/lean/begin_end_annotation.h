/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
#include "frontends/lean/cmd_table.h"

namespace lean {
expr mk_begin_end_annotation(expr const & e);
expr mk_begin_end_element_annotation(expr const & e);
bool is_begin_end_annotation(expr const & e);
bool is_begin_end_element_annotation(expr const & e);

void initialize_begin_end_annotation();
void finalize_begin_end_annotation();
}
