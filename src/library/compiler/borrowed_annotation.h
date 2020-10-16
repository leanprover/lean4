/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/compiler/util.h"
namespace lean {
expr mk_borrowed(expr const & e);
bool is_borrowed(expr const & e);
expr get_borrowed_arg(expr const & e);
void initialize_borrowed_annotation();
void finalize_borrowed_annotation();
}
