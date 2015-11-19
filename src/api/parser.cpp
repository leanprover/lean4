/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "frontends/lean/parser.h"
#include "api/string.h"
#include "api/exception.h"
#include "api/decl.h"
#include "api/ios.h"
#include "api/lean_parser.h"
using namespace lean; // NOLINT

lean_bool lean_parse_file(lean_env env, lean_ios ios, char const * fname, lean_env * new_env, lean_ios * new_ios, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(env);
    check_nonnull(ios);
    check_nonnull(fname);
    environment _env     = to_env_ref(env);
    io_state    _ios     = to_io_state_ref(ios);
    bool use_exceptions  = true;
    unsigned num_threads = 1;
    parse_commands(_env, _ios, fname, optional<std::string>(), use_exceptions, num_threads);
    *new_env = of_env(new environment(_env));
    *new_ios = of_io_state(new io_state(_ios));
    LEAN_CATCH;
}

lean_bool lean_parse_commands(lean_env env, lean_ios ios, char const * str, lean_env * new_env, lean_ios * new_ios, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(env);
    check_nonnull(ios);
    check_nonnull(str);
    std::istringstream in(str);
    char const * strname = "[string]";
    environment _env     = to_env_ref(env);
    io_state    _ios     = to_io_state_ref(ios);
    bool use_exceptions  = true;
    unsigned num_threads = 1;
    parse_commands(_env, _ios, in, strname, optional<std::string>(), use_exceptions, num_threads);
    *new_env = of_env(new environment(_env));
    *new_ios = of_io_state(new io_state(_ios));
    LEAN_CATCH;
}

lean_bool lean_parse_expr(lean_env env, lean_ios ios, char const * str, lean_expr * new_expr, lean_list_name * new_ps, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(env);
    check_nonnull(ios);
    check_nonnull(str);
    std::istringstream in(str);
    char const * strname = "[string]";
    environment _env     = to_env_ref(env);
    io_state    _ios     = to_io_state_ref(ios);
    bool use_exceptions  = true;
    unsigned num_threads = 1;
    parser p(_env, _ios, in, strname, optional<std::string>(), use_exceptions, num_threads);
    expr e = p.parse_expr();
    expr _e; level_param_names _ps;
    std::tie(_e, _ps) = p.elaborate(e, list<expr>());
    *new_expr = of_expr(new expr(_e));
    *new_ps   = of_list_name(new list<name>(_ps));
    LEAN_CATCH;
}
