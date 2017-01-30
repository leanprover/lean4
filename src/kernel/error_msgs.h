/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
#include "kernel/formatter.h"
namespace lean {
format pp_indent_expr(formatter const & fmt, expr const & e);
format pp_type_expected(formatter const & fmt, expr const & e);
format pp_function_expected(formatter const & fmt, expr const & e);
format pp_app_type_mismatch(formatter const & fmt, expr const & app, expr const & fn_type, expr const & arg, expr const & given_type, bool as_error);
format pp_def_type_mismatch(formatter const & fmt, name const & n, expr const & expected_type, expr const & given_type, bool as_error);
format pp_decl_has_metavars(formatter const & fmt, name const & n, expr const & e, bool is_type);

/** \brief Set a list extra configuration options that are used to try to distinguish error such as given/expected type mismatch
    This is a trick used to avoid cryptic error messages when to types seem identical because the pretty printer is suppressing
    universes and/or implicit arguments. The error messages will keep using these extra options until it finds one that
    can distinguish given/expected type. The extra options do not override user provided options.
*/
void set_distinguishing_pp_options(list<options> const & opts);
list<options> const & get_distinguishing_pp_options();

expr erase_binder_info(expr const & e);

std::tuple<format, format> pp_until_different(formatter const & fmt, expr const & e1, expr const & e2);
format pp_until_meta_visible(formatter const & fmt, expr const & e);

void initialize_error_msgs();
void finalize_error_msgs();
}
