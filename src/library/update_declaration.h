/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/declaration.h"
namespace lean {
// Helper function for updating "declaration fields"
declaration update_declaration_univ_params(declaration const & d, level_param_names const & ps);
declaration update_declaration_type(declaration const & d, expr const & type);
declaration update_declaration_value(declaration const & d, expr const & value);
declaration update_declaration(declaration const & d, level_param_names const & ps, expr const & type, expr const & value);
declaration update_declaration(declaration const & d, level_param_names const & ps, expr const & type);
}
