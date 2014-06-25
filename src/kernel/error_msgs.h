/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
#include "kernel/formatter.h"
namespace lean {
format pp_indent_expr(formatter const & fmt, environment const & env, options const & opts, expr const & e);
format pp_type_expected(formatter const & fmt, environment const & env, options const & opts, expr const & e);
format pp_function_expected(formatter const & fmt, environment const & env, options const & opts, expr const & e);
format pp_app_type_mismatch(formatter const & fmt, environment const & env, options const & opts, expr const & app,
                            expr const & expected_type, expr const & given_type);
format pp_def_type_mismatch(formatter const & fmt, environment const & env, options const & opts, name const & n,
                            expr const & expected_type, expr const & given_type);
format pp_decl_has_metavars(formatter const & fmt, environment const & env, options const & opts, name const & n,
                            expr const & e, bool is_type);
}
