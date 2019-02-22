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
expr const & get_borrowed_arg(expr const & e);
bool get_inferred_borrowed_info(environment const & env, name const & fn, buffer<bool> & borrowed_args, bool & borrowed_res);
environment infer_borrowed_annotations(environment const & env, buffer<comp_decl> const &);
void initialize_borrowed_annotation();
void finalize_borrowed_annotation();
}
