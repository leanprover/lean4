/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
// Very simple read-eval-print for Lua

#if LUA_VERSION_NUM >= 520
static char const * g_lua_repl =
    "local function trim(s)\n"
    "   return s:gsub('^%s+', ''):gsub('%s+$', '')\n"
    "end\n"
    "local function show_results(...)\n"
    "   if select('#', ...) > 1 then\n"
    "      print(select(2, ...))\n"
    "   end\n"
    "end\n"
    "print([[Type 'Exit' to exit.]])\n"
    "repeat\n"
    "    io.write'lean > '\n"
    "    local s = io.read()\n"
    "    if s == nil then print(""); break end\n"
    "    if trim(s) == 'Exit' then break end\n"
    "    local f, err = load(s, 'stdin')\n"
    "    if err then\n"
    "        f = load('return (' .. s .. ')', 'stdin')\n"
    "    end\n"
    "    if f then\n"
    "        local ok, err = pcall(f)\n"
    "        if not ok then\n"
    "           if is_exception(err) then\n"
    "               print(err:what())\n"
    "           else\n"
    "               print(err)\n"
    "           end\n"
    "        else\n"
    "           if err then print(err) end\n"
    "        end\n"
    "    else\n"
    "        print(err)\n"
    "    end\n"
    "until false\n";
#else /* For Lua 5.1, we  uses loadstring instead of load */
static char const * g_lua_repl =
    "local function trim(s)\n"
    "   return s:gsub('^%s+', ''):gsub('%s+$', '')\n"
    "end\n"
    "local function show_results(...)\n"
    "   if select('#', ...) > 1 then\n"
    "      print(select(2, ...))\n"
    "   end\n"
    "end\n"
    "print([[Type 'Exit' to exit.]])\n"
    "repeat\n"
    "    io.write'lean > '\n"
    "    local s = io.read()\n"
    "    if s == nil then print(""); break end\n"
    "    if trim(s) == 'Exit' then break end\n"
    "    local f, err = loadstring(s, 'stdin')\n"
    "    if err then\n"
    "        f = loadstring('return (' .. s .. ')', 'stdin')\n"
    "    end\n"
    "    if f then\n"
    "        local ok, err = pcall(f)\n"
    "        if not ok then\n"
    "           if is_exception(err) then\n"
    "               print(err:what())\n"
    "           else\n"
    "               print(err)\n"
    "           end\n"
    "        else\n"
    "           if err then print(err) end\n"
    "        end\n"
    "    else\n"
    "        print(err)\n"
    "    end\n"
    "until false\n";
#endif
