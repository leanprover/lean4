/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <sstream>
#include "util/lua.h"
#include "util/script_state.h"
#include "util/sexpr/options.h"
#include "kernel/io_state.h"
#include "library/kernel_bindings.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/frontend.h"
#include "frontends/lean/pp.h"

namespace lean {
/** \see parse_lean_expr */
static int parse_lean_expr_core(lua_State * L, rw_shared_environment const & env, io_state & st) {
    char const * src = luaL_checkstring(L, 1);
    std::istringstream in(src);
    script_state S   = to_script_state(L);
    expr r;
    S.exec_unprotected([&]() {
            r = parse_expr(env, st, in, &S);
        });
    return push_expr(L, r);
}

/** \see parse_lean_expr */
static int parse_lean_expr_core(lua_State * L, rw_shared_environment const & env) {
    io_state * io = get_io_state(L);
    if (io == nullptr) {
        io_state s(get_global_options(L), mk_pp_formatter(env));
        return parse_lean_expr_core(L, env, s);
    } else {
        return parse_lean_expr_core(L, env, *io);
    }
}

static int parse_lean_expr(lua_State * L) {
    /*
      The parse_lean_expr function in the Lua API supports different calling arguments:
      1. (string) : simplest form, it is just a string in Lean default syntax.
         The string is parsed using the global environment in the Lua registry.
         If the Lua registry does not contain an environment, then commands fails.

         It also uses the global state object in the registry. If there is no
         state object, it will tries to create one using the global options and formatter
         in the registry.

         It returns a Lean expression.

      2. (string, env) : similar to the previous one, but the environment is explicitly
         provided.

      3. (string, env, options, formatter?) : Everything is explicitly provided in this
         version. We also support a variation where the formmater is omitted.
    */
    int nargs = get_nonnil_top(L);
    if (nargs == 1) {
        rw_shared_environment env(L); // get global environment
        return parse_lean_expr_core(L, env);
    } else {
        rw_shared_environment env(L, 2);
        if (nargs == 2) {
            return parse_lean_expr_core(L, env);
        } else {
            options opts    = to_options(L, 3);
            formatter fmt   = nargs == 3 ? mk_pp_formatter(env) : to_formatter(L, 4);
            io_state st(opts, fmt);
            return parse_lean_expr_core(L, env, st);
        }
    }
}

/** \see parse_lean_cmds */
static void parse_lean_cmds_core(lua_State * L, rw_shared_environment const & env, io_state & st) {
    char const * src = luaL_checkstring(L, 1);
    std::istringstream in(src);
    script_state S   = to_script_state(L);
    S.exec_unprotected([&]() {
            parse_commands(env, st, in, &S);
        });
}

/** \see parse_lean_cmds */
static void parse_lean_cmds_core(lua_State * L, rw_shared_environment const & env) {
    io_state * io = get_io_state(L);
    if (io == nullptr) {
        io_state s(get_global_options(L), mk_pp_formatter(env));
        parse_lean_cmds_core(L, env, s);
        set_global_options(L, s.get_options());
    } else {
        parse_lean_cmds_core(L, env, *io);
    }
}

static int parse_lean_cmds(lua_State * L) {
    /*
      The parse_lean_cmds function reads a sequence of Lean commands from the input string.
      The supported calling arguments are equal to the ones used in parse_lean_expr.
      The main difference is the function result. When calling with explicit options
      the function returns an updated set of options. Otherwise it does not return anything.
    */
    int nargs = get_nonnil_top(L);
    if (nargs == 1) {
        rw_shared_environment env(L); // get global environment
        parse_lean_cmds_core(L, env);
        return 0;
    } else {
        rw_shared_environment env(L, 2);
        if (nargs == 2) {
            parse_lean_cmds_core(L, env);
            return 0;
        } else {
            options opts    = to_options(L, 3);
            formatter fmt   = nargs == 3 ? mk_pp_formatter(env) : to_formatter(L, 4);
            io_state st(opts, fmt);
            parse_lean_cmds_core(L, env, st);
            push_options(L, st.get_options());
            return 1;
        }
    }
}

static int mk_environment(lua_State * L) {
    environment env;
    io_state ios;
    init_frontend(env, ios);
    return push_environment(L, env);
}

static int mk_lean_formatter(lua_State * L) {
    return push_formatter(L, mk_pp_formatter(to_environment(L, 1)));
}

void open_frontend_lean(lua_State * L) {
    open_macros(L);
    SET_GLOBAL_FUN(mk_environment,    "environment");
    SET_GLOBAL_FUN(mk_lean_formatter, "lean_formatter");
    SET_GLOBAL_FUN(parse_lean_expr,   "parse_lean");
    SET_GLOBAL_FUN(parse_lean_cmds,   "parse_lean_cmds");
}

void register_frontend_lean_module() {
    script_state::register_module(open_frontend_lean);
}
}
