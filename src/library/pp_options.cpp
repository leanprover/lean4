/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sexpr/option_declarations.h"
#include "library/pp_options.h"

#ifndef LEAN_DEFAULT_PP_MAX_DEPTH
#define LEAN_DEFAULT_PP_MAX_DEPTH 10000
#endif

#ifndef LEAN_DEFAULT_PP_MAX_STEPS
#define LEAN_DEFAULT_PP_MAX_STEPS 50000
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

#ifndef LEAN_DEFAULT_PP_PURIFY_METAVARS
#define LEAN_DEFAULT_PP_PURIFY_METAVARS true
#endif

#ifndef LEAN_DEFAULT_PP_PURIFY_LOCALS
#define LEAN_DEFAULT_PP_PURIFY_LOCALS true
#endif

#ifndef LEAN_DEFAULT_PP_BETA
#define LEAN_DEFAULT_PP_BETA true
#endif

#ifndef LEAN_DEFAULT_PP_NUMERALS
#define LEAN_DEFAULT_PP_NUMERALS true
#endif

#ifndef LEAN_DEFAULT_PP_ABBREVIATIONS
#define LEAN_DEFAULT_PP_ABBREVIATIONS true
#endif

#ifndef LEAN_DEFAULT_PP_PRETERM
#define LEAN_DEFAULT_PP_PRETERM false
#endif

#ifndef LEAN_DEFAULT_PP_COMPACT_GOALS
#define LEAN_DEFAULT_PP_COMPACT_GOALS false
#endif

#ifndef LEAN_DEFAULT_PP_ALL
#define LEAN_DEFAULT_PP_ALL false
#endif

namespace lean {
static name * g_pp_max_depth       = nullptr;
static name * g_pp_max_steps       = nullptr;
static name * g_pp_notation        = nullptr;
static name * g_pp_implicit        = nullptr;
static name * g_pp_coercions       = nullptr;
static name * g_pp_universes       = nullptr;
static name * g_pp_full_names      = nullptr;
static name * g_pp_private_names   = nullptr;
static name * g_pp_metavar_args    = nullptr;
static name * g_pp_purify_metavars = nullptr;
static name * g_pp_purify_locals   = nullptr;
static name * g_pp_beta            = nullptr;
static name * g_pp_numerals        = nullptr;
static name * g_pp_abbreviations   = nullptr;
static name * g_pp_preterm         = nullptr;
static name * g_pp_compact_goals   = nullptr;
static name * g_pp_all             = nullptr;
static list<options> * g_distinguishing_pp_options = nullptr;

void initialize_pp_options() {
    g_pp_max_depth       = new name{"pp", "max_depth"};
    g_pp_max_steps       = new name{"pp", "max_steps"};
    g_pp_notation        = new name{"pp", "notation"};
    g_pp_implicit        = new name{"pp", "implicit"};
    g_pp_coercions       = new name{"pp", "coercions"};
    g_pp_universes       = new name{"pp", "universes"};
    g_pp_full_names      = new name{"pp", "full_names"};
    g_pp_private_names   = new name{"pp", "private_names"};
    g_pp_metavar_args    = new name{"pp", "metavar_args"};
    g_pp_purify_metavars = new name{"pp", "purify_metavars"};
    g_pp_purify_locals   = new name{"pp", "purify_locals"};
    g_pp_beta            = new name{"pp", "beta"};
    g_pp_numerals        = new name{"pp", "numerals"};
    g_pp_abbreviations   = new name{"pp", "abbreviations"};
    g_pp_preterm         = new name{"pp", "preterm"};
    g_pp_all             = new name{"pp", "all"};
    g_pp_compact_goals   = new name{"pp", "compact_goals"};
    register_unsigned_option(*g_pp_max_depth, LEAN_DEFAULT_PP_MAX_DEPTH,
                             "(pretty printer) maximum expression depth, after that it will use ellipsis");
    register_unsigned_option(*g_pp_max_steps, LEAN_DEFAULT_PP_MAX_STEPS,
                             "(pretty printer) maximum number of visited expressions, after that it will use ellipsis");
    register_bool_option(*g_pp_notation,  LEAN_DEFAULT_PP_NOTATION,
                         "(pretty printer) disable/enable notation (infix, mixfix, postfix operators and unicode characters)");
    register_bool_option(*g_pp_implicit,  LEAN_DEFAULT_PP_IMPLICIT,
                         "(pretty printer) display implicit parameters");
    register_bool_option(*g_pp_coercions,  LEAN_DEFAULT_PP_COERCIONS,
                         "(pretty printer) display coercionss");
    register_bool_option(*g_pp_universes,  LEAN_DEFAULT_PP_UNIVERSES,
                         "(pretty printer) display universes");
    register_bool_option(*g_pp_full_names,  LEAN_DEFAULT_PP_FULL_NAMES,
                         "(pretty printer) display fully qualified names");
    register_bool_option(*g_pp_private_names,  LEAN_DEFAULT_PP_PRIVATE_NAMES,
                         "(pretty printer) display internal names assigned to private declarations");
    register_bool_option(*g_pp_metavar_args,  LEAN_DEFAULT_PP_METAVAR_ARGS,
                         "(pretty printer) display metavariable arguments");
    register_bool_option(*g_pp_purify_metavars, LEAN_DEFAULT_PP_PURIFY_METAVARS,
                         "(pretty printer) rename internal metavariable names (with \"user-friendly\" ones) "
                         "before pretty printing");
    register_bool_option(*g_pp_purify_locals, LEAN_DEFAULT_PP_PURIFY_LOCALS,
                         "(pretty printer) rename local names to avoid name capture, "
                         "before pretty printing");
    register_bool_option(*g_pp_beta,  LEAN_DEFAULT_PP_BETA,
                         "(pretty printer) apply beta-reduction when pretty printing");
    register_bool_option(*g_pp_numerals, LEAN_DEFAULT_PP_NUMERALS,
                         "(pretty printer) display nat/num numerals in decimal notation");
    register_bool_option(*g_pp_abbreviations, LEAN_DEFAULT_PP_ABBREVIATIONS,
                         "(pretty printer) display abbreviations (i.e., revert abbreviation expansion when pretty printing)");
    register_bool_option(*g_pp_preterm, LEAN_DEFAULT_PP_PRETERM,
                         "(pretty printer) assume the term is a preterm (i.e., a term before elaboration)");
    register_bool_option(*g_pp_compact_goals, LEAN_DEFAULT_PP_COMPACT_GOALS,
                         "(pretty printer) try to display goal in a single line when possible");
    register_bool_option(*g_pp_all, LEAN_DEFAULT_PP_ALL,
                         "(pretty printer) display coercions, implicit parameters, fully qualified names, universes, "
                         "and disable abbreviations, beta reduction and notation during pretty printing");
    options universes_true(*g_pp_universes, true);
    options full_names_true(*g_pp_full_names, true);
    options implicit_true(*g_pp_implicit, true);
    options coercions_true(*g_pp_coercions, true);
    options notation_false(*g_pp_notation, false);
    options implicit_coercions = join(coercions_true, implicit_true);
    options implicit_notation  = join(notation_false, implicit_true);
    options all = universes_true + implicit_true + coercions_true + notation_false + full_names_true;
    g_distinguishing_pp_options = new list<options>({implicit_true, full_names_true, coercions_true, implicit_coercions,
                implicit_notation, universes_true, all});
}

void finalize_pp_options() {
    delete g_pp_preterm;
    delete g_pp_abbreviations;
    delete g_pp_numerals;
    delete g_pp_max_depth;
    delete g_pp_max_steps;
    delete g_pp_notation;
    delete g_pp_implicit;
    delete g_pp_coercions;
    delete g_pp_universes;
    delete g_pp_full_names;
    delete g_pp_private_names;
    delete g_pp_metavar_args;
    delete g_pp_purify_metavars;
    delete g_pp_purify_locals;
    delete g_pp_beta;
    delete g_pp_compact_goals;
    delete g_pp_all;
    delete g_distinguishing_pp_options;
}

name const & get_pp_implicit_name() { return *g_pp_implicit; }
name const & get_pp_coercions_name() { return *g_pp_coercions; }
name const & get_pp_full_names_name() { return *g_pp_full_names; }
name const & get_pp_universes_name() { return *g_pp_universes; }
name const & get_pp_notation_name() { return *g_pp_notation; }
name const & get_pp_metavar_args_name() { return *g_pp_metavar_args; }
name const & get_pp_purify_metavars_name() { return *g_pp_purify_metavars; }
name const & get_pp_purify_locals_name() { return *g_pp_purify_locals; }
name const & get_pp_beta_name() { return *g_pp_beta; }
name const & get_pp_preterm_name() { return *g_pp_preterm; }
name const & get_pp_numerals_name() { return *g_pp_numerals; }
name const & get_pp_abbreviations_name() { return *g_pp_abbreviations; }

unsigned get_pp_max_depth(options const & opts)       { return opts.get_unsigned(*g_pp_max_depth, LEAN_DEFAULT_PP_MAX_DEPTH); }
unsigned get_pp_max_steps(options const & opts)       { return opts.get_unsigned(*g_pp_max_steps, LEAN_DEFAULT_PP_MAX_STEPS); }
bool     get_pp_notation(options const & opts)        { return opts.get_bool(*g_pp_notation, LEAN_DEFAULT_PP_NOTATION); }
bool     get_pp_implicit(options const & opts)        { return opts.get_bool(*g_pp_implicit, LEAN_DEFAULT_PP_IMPLICIT); }
bool     get_pp_coercions(options const & opts)       { return opts.get_bool(*g_pp_coercions, LEAN_DEFAULT_PP_COERCIONS); }
bool     get_pp_universes(options const & opts)       { return opts.get_bool(*g_pp_universes, LEAN_DEFAULT_PP_UNIVERSES); }
bool     get_pp_full_names(options const & opts)      { return opts.get_bool(*g_pp_full_names, LEAN_DEFAULT_PP_FULL_NAMES); }
bool     get_pp_private_names(options const & opts)   { return opts.get_bool(*g_pp_private_names, LEAN_DEFAULT_PP_PRIVATE_NAMES); }
bool     get_pp_metavar_args(options const & opts)    { return opts.get_bool(*g_pp_metavar_args, LEAN_DEFAULT_PP_METAVAR_ARGS); }
bool     get_pp_purify_metavars(options const & opts) { return opts.get_bool(*g_pp_purify_metavars, LEAN_DEFAULT_PP_PURIFY_METAVARS); }
bool     get_pp_purify_locals(options const & opts)   { return opts.get_bool(*g_pp_purify_locals, LEAN_DEFAULT_PP_PURIFY_LOCALS); }
bool     get_pp_beta(options const & opts)            { return opts.get_bool(*g_pp_beta, LEAN_DEFAULT_PP_BETA); }
bool     get_pp_numerals(options const & opts)        { return opts.get_bool(*g_pp_numerals, LEAN_DEFAULT_PP_NUMERALS); }
bool     get_pp_abbreviations(options const & opts)   { return opts.get_bool(*g_pp_abbreviations, LEAN_DEFAULT_PP_ABBREVIATIONS); }
bool     get_pp_preterm(options const & opts)         { return opts.get_bool(*g_pp_preterm, LEAN_DEFAULT_PP_PRETERM); }
bool     get_pp_compact_goals(options const & opts)   { return opts.get_bool(*g_pp_compact_goals, LEAN_DEFAULT_PP_COMPACT_GOALS); }
bool     get_pp_all(options const & opts)             { return opts.get_bool(*g_pp_all, LEAN_DEFAULT_PP_ALL); }

list<options> const & get_distinguishing_pp_options() { return *g_distinguishing_pp_options; }
}
