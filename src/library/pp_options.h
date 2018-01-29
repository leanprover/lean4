/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/sexpr/options.h"
namespace lean {
name const & get_pp_implicit_name();
name const & get_pp_proofs_name();
name const & get_pp_coercions_name();
name const & get_pp_full_names_name();
name const & get_pp_universes_name();
name const & get_pp_notation_name();
name const & get_pp_purify_metavars_name();
name const & get_pp_purify_locals_name();
name const & get_pp_locals_full_names_name();
name const & get_pp_beta_name();
name const & get_pp_preterm_name();
name const & get_pp_numerals_name();
name const & get_pp_strings_name();
name const & get_pp_binder_types_name();
name const & get_pp_use_holes_name();

unsigned get_pp_max_depth(options const & opts);
unsigned get_pp_max_steps(options const & opts);
bool     get_pp_notation(options const & opts);
bool     get_pp_implicit(options const & opts);
bool     get_pp_proofs(options const & opts);
bool     get_pp_coercions(options const & opts);
bool     get_pp_universes(options const & opts);
bool     get_pp_full_names(options const & opts);
bool     get_pp_private_names(options const & opts);
bool     get_pp_beta(options const & opts);
bool     get_pp_purify_metavars(options const & opts);
bool     get_pp_purify_locals(options const & opts);
bool     get_pp_locals_full_names(options const & opts);
bool     get_pp_numerals(options const & opts);
bool     get_pp_strings(options const & opts);
bool     get_pp_preterm(options const & opts);
bool     get_pp_goal_compact(options const & opts);
unsigned get_pp_goal_max_hyps(options const & opts);
bool     get_pp_binder_types(options const & opts);
bool     get_pp_hide_comp_irrel(options const & opts);
bool     get_pp_delayed_abstraction(options const & opts);
bool     get_pp_structure_instances(options const & opts);
bool     get_pp_structure_instances_qualifier(options const & opts);
bool     get_pp_structure_projections(options const & opts);
bool     get_pp_instantiate_mvars(options const & o);
bool     get_pp_use_holes(options const & o);
bool     get_pp_annotations(options const & o);
bool     get_pp_all(options const & opts);

void initialize_pp_options();
void finalize_pp_options();
}
