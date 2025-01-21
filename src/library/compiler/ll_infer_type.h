/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/elab_environment.h"
namespace lean {
expr ll_infer_type(elab_environment const & env, local_ctx const & lctx, expr const & e);
inline expr ll_infer_type(elab_environment const & env, expr const & e) { return ll_infer_type(env, local_ctx(), e); }
void ll_infer_type(elab_environment const & env, comp_decls const & ds, buffer<expr> & ts);
void initialize_ll_infer_type();
void finalize_ll_infer_type();
}
