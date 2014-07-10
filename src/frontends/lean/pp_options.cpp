/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "frontends/lean/pp_options.h"

#ifndef LEAN_DEFAULT_PP_MAX_DEPTH
#define LEAN_DEFAULT_PP_MAX_DEPTH std::numeric_limits<unsigned>::max()
#endif

#ifndef LEAN_DEFAULT_PP_MAX_STEPS
#define LEAN_DEFAULT_PP_MAX_STEPS std::numeric_limits<unsigned>::max()
#endif

#ifndef LEAN_DEFAULT_PP_NOTATION
#define LEAN_DEFAULT_PP_NOTATION true
#endif

#ifndef LEAN_DEFAULT_PP_IMPLICIT
#define LEAN_DEFAULT_PP_IMPLICIT false
#endif

#ifndef LEAN_DEFAULT_PP_COERCION
#define LEAN_DEFAULT_PP_COERCION false
#endif

#ifndef LEAN_DEFAULT_PP_UNIVERSES
#define LEAN_DEFAULT_PP_UNIVERSES false
#endif

#ifndef LEAN_DEFAULT_PP_FULL_NAMES
#define LEAN_DEFAULT_PP_FULL_NAMES false
#endif

namespace lean {
static name g_pp_max_depth        {"pp", "max_depth"};
static name g_pp_max_steps        {"pp", "max_steps"};
static name g_pp_notation         {"pp", "notation"};
static name g_pp_implicit         {"pp", "implicit"};
static name g_pp_coercion         {"pp", "coercion"};
static name g_pp_universes        {"pp", "universes"};
static name g_pp_full_names       {"pp", "full_names"};

RegisterUnsignedOption(g_pp_max_depth, LEAN_DEFAULT_PP_MAX_DEPTH,
                       "(pretty printer) maximum expression depth, after that it will use ellipsis");
RegisterUnsignedOption(g_pp_max_steps, LEAN_DEFAULT_PP_MAX_STEPS,
                       "(pretty printer) maximum number of visited expressions, after that it will use ellipsis");
RegisterBoolOption(g_pp_notation,  LEAN_DEFAULT_PP_NOTATION,
                   "(pretty printer) disable/enable notation (infix, mixfix, postfix operators and unicode characters)");
RegisterBoolOption(g_pp_implicit,  LEAN_DEFAULT_PP_IMPLICIT,
                   "(pretty printer) display implicit parameters");
RegisterBoolOption(g_pp_coercion,  LEAN_DEFAULT_PP_COERCION,
                   "(pretty printer) display coercions");
RegisterBoolOption(g_pp_universes,  LEAN_DEFAULT_PP_UNIVERSES,
                   "(pretty printer) display universes");
RegisterBoolOption(g_pp_full_names,  LEAN_DEFAULT_PP_FULL_NAMES,
                   "(pretty printer) display fully qualified names");

unsigned get_pp_max_depth(options const & opts)  { return opts.get_unsigned(g_pp_max_depth, LEAN_DEFAULT_PP_MAX_DEPTH); }
unsigned get_pp_max_steps(options const & opts)  { return opts.get_unsigned(g_pp_max_steps, LEAN_DEFAULT_PP_MAX_STEPS); }
bool     get_pp_notation(options const & opts)   { return opts.get_bool(g_pp_notation, LEAN_DEFAULT_PP_NOTATION); }
bool     get_pp_implicit(options const & opts)   { return opts.get_bool(g_pp_implicit, LEAN_DEFAULT_PP_IMPLICIT); }
bool     get_pp_coercion(options const & opts)   { return opts.get_bool(g_pp_coercion, LEAN_DEFAULT_PP_COERCION); }
bool     get_pp_universes(options const & opts)  { return opts.get_bool(g_pp_universes, LEAN_DEFAULT_PP_UNIVERSES); }
bool     get_pp_full_names(options const & opts) { return opts.get_bool(g_pp_full_names, LEAN_DEFAULT_PP_FULL_NAMES); }
}
