/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/sexpr/options.h"
namespace lean {
name const & get_pp_implicit_name();
name const & get_pp_coercions_option_name();
name const & get_pp_full_names_option_name();
name const & get_pp_universes_option_name();
name const & get_pp_notation_option_name();
name const & get_pp_metavar_args_name();
name const & get_pp_purify_metavars_name();
name const & get_pp_purify_locals_name();
name const & get_pp_beta_name();
name const & get_pp_preterm_name();

unsigned get_pp_max_depth(options const & opts);
unsigned get_pp_max_steps(options const & opts);
bool     get_pp_notation(options const & opts);
bool     get_pp_implicit(options const & opts);
bool     get_pp_coercions(options const & opts);
bool     get_pp_universes(options const & opts);
bool     get_pp_full_names(options const & opts);
bool     get_pp_private_names(options const & opts);
bool     get_pp_metavar_args(options const & opts);
bool     get_pp_beta(options const & opts);
bool     get_pp_purify_metavars(options const & opts);
bool     get_pp_purify_locals(options const & opts);
bool     get_pp_numerals(options const & opts);
bool     get_pp_abbreviations(options const & opts);
bool     get_pp_extra_spaces(options const & opts);
bool     get_pp_preterm(options const & opts);
list<options> const & get_distinguishing_pp_options();

void initialize_pp_options();
void finalize_pp_options();
}
