/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "frontends/lean/pp_options.h"

#ifndef LEAN_DEFAULT_PP_MAX_DEPTH
#define LEAN_DEFAULT_PP_MAX_DEPTH 1000000
#endif

#ifndef LEAN_DEFAULT_PP_MAX_STEPS
#define LEAN_DEFAULT_PP_MAX_STEPS 10000000
#endif

#ifndef LEAN_DEFAULT_PP_NOTATION
#define LEAN_DEFAULT_PP_NOTATION true
#endif

#ifndef LEAN_DEFAULT_PP_IMPLICIT
#define LEAN_DEFAULT_PP_IMPLICIT false
#endif

#ifndef LEAN_DEFAULT_PP_COERCIONS
#define LEAN_DEFAULT_PP_COERCIONS false
#endif

#ifndef LEAN_DEFAULT_PP_UNIVERSES
#define LEAN_DEFAULT_PP_UNIVERSES false
#endif

#ifndef LEAN_DEFAULT_PP_FULL_NAMES
#define LEAN_DEFAULT_PP_FULL_NAMES false
#endif

#ifndef LEAN_DEFAULT_PP_PRIVATE_NAMES
#define LEAN_DEFAULT_PP_PRIVATE_NAMES false
#endif

#ifndef LEAN_DEFAULT_PP_METAVAR_ARGS
#define LEAN_DEFAULT_PP_METAVAR_ARGS false
#endif

#ifndef LEAN_DEFAULT_PP_BETA
#define LEAN_DEFAULT_PP_BETA false
#endif

namespace lean {
static name g_pp_max_depth        {"pp", "max_depth"};
static name g_pp_max_steps        {"pp", "max_steps"};
static name g_pp_notation         {"pp", "notation"};
static name g_pp_implicit         {"pp", "implicit"};
static name g_pp_coercions        {"pp", "coercions"};
static name g_pp_universes        {"pp", "universes"};
static name g_pp_full_names       {"pp", "full_names"};
static name g_pp_private_names    {"pp", "private_names"};
static name g_pp_metavar_args     {"pp", "metavar_args"};
static name g_pp_beta             {"pp", "beta"};

name const & get_pp_coercions_option_name() { return g_pp_coercions; }
name const & get_pp_full_names_option_name() { return g_pp_full_names; }

list<options> const & get_distinguishing_pp_options() {
    static options g_universes_true(g_pp_universes, true);
    static options g_implicit_true(g_pp_implicit, true);
    static options g_coercions_true(g_pp_coercions, true);
    static options g_notation_false(g_pp_notation, false);
    static options g_implicit_coercions = join(g_coercions_true, g_implicit_true);
    static options g_implicit_notation = join(g_notation_false, g_implicit_true);
    static options g_all = join(join(g_universes_true, g_implicit_true), join(g_coercions_true, g_notation_false));
    static list<options> g_distinguishing_pp_options({g_implicit_true, g_coercions_true, g_implicit_coercions, g_implicit_notation, g_universes_true, g_all});
    return g_distinguishing_pp_options;
}

RegisterUnsignedOption(g_pp_max_depth, LEAN_DEFAULT_PP_MAX_DEPTH,
                       "(pretty printer) maximum expression depth, after that it will use ellipsis");
RegisterUnsignedOption(g_pp_max_steps, LEAN_DEFAULT_PP_MAX_STEPS,
                       "(pretty printer) maximum number of visited expressions, after that it will use ellipsis");
RegisterBoolOption(g_pp_notation,  LEAN_DEFAULT_PP_NOTATION,
                   "(pretty printer) disable/enable notation (infix, mixfix, postfix operators and unicode characters)");
RegisterBoolOption(g_pp_implicit,  LEAN_DEFAULT_PP_IMPLICIT,
                   "(pretty printer) display implicit parameters");
RegisterBoolOption(g_pp_coercions,  LEAN_DEFAULT_PP_COERCIONS,
                   "(pretty printer) display coercionss");
RegisterBoolOption(g_pp_universes,  LEAN_DEFAULT_PP_UNIVERSES,
                   "(pretty printer) display universes");
RegisterBoolOption(g_pp_full_names,  LEAN_DEFAULT_PP_FULL_NAMES,
                   "(pretty printer) display fully qualified names");
RegisterBoolOption(g_pp_private_names,  LEAN_DEFAULT_PP_PRIVATE_NAMES,
                   "(pretty printer) display internal names assigned to private declarations");
RegisterBoolOption(g_pp_metavar_args,  LEAN_DEFAULT_PP_METAVAR_ARGS,
                   "(pretty printer) display metavariable arguments");
RegisterBoolOption(g_pp_beta,  LEAN_DEFAULT_PP_BETA,
                   "(pretty printer) apply beta-reduction when pretty printing");

unsigned get_pp_max_depth(options const & opts)     { return opts.get_unsigned(g_pp_max_depth, LEAN_DEFAULT_PP_MAX_DEPTH); }
unsigned get_pp_max_steps(options const & opts)     { return opts.get_unsigned(g_pp_max_steps, LEAN_DEFAULT_PP_MAX_STEPS); }
bool     get_pp_notation(options const & opts)      { return opts.get_bool(g_pp_notation, LEAN_DEFAULT_PP_NOTATION); }
bool     get_pp_implicit(options const & opts)      { return opts.get_bool(g_pp_implicit, LEAN_DEFAULT_PP_IMPLICIT); }
bool     get_pp_coercions(options const & opts)     { return opts.get_bool(g_pp_coercions, LEAN_DEFAULT_PP_COERCIONS); }
bool     get_pp_universes(options const & opts)     { return opts.get_bool(g_pp_universes, LEAN_DEFAULT_PP_UNIVERSES); }
bool     get_pp_full_names(options const & opts)    { return opts.get_bool(g_pp_full_names, LEAN_DEFAULT_PP_FULL_NAMES); }
bool     get_pp_private_names(options const & opts) { return opts.get_bool(g_pp_private_names, LEAN_DEFAULT_PP_PRIVATE_NAMES); }
bool     get_pp_metavar_args(options const & opts)  { return opts.get_bool(g_pp_metavar_args, LEAN_DEFAULT_PP_METAVAR_ARGS); }
bool     get_pp_beta(options const & opts)          { return opts.get_bool(g_pp_beta, LEAN_DEFAULT_PP_BETA); }
}
