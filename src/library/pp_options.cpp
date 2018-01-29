/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sexpr/option_declarations.h"
#include "kernel/error_msgs.h"
#include "library/pp_options.h"

#ifndef LEAN_DEFAULT_PP_MAX_DEPTH
#define LEAN_DEFAULT_PP_MAX_DEPTH 64
#endif

#ifndef LEAN_DEFAULT_PP_MAX_STEPS
#define LEAN_DEFAULT_PP_MAX_STEPS 5000
#endif

#ifndef LEAN_DEFAULT_PP_NOTATION
#define LEAN_DEFAULT_PP_NOTATION true
#endif

#ifndef LEAN_DEFAULT_PP_IMPLICIT
#define LEAN_DEFAULT_PP_IMPLICIT false
#endif

#ifndef LEAN_DEFAULT_PP_PROOFS
#define LEAN_DEFAULT_PP_PROOFS true
#endif

#ifndef LEAN_DEFAULT_PP_COERCIONS
#define LEAN_DEFAULT_PP_COERCIONS true
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

#ifndef LEAN_DEFAULT_PP_PURIFY_METAVARS
#define LEAN_DEFAULT_PP_PURIFY_METAVARS true
#endif

#ifndef LEAN_DEFAULT_PP_PURIFY_LOCALS
#define LEAN_DEFAULT_PP_PURIFY_LOCALS true
#endif

#ifndef LEAN_DEFAULT_PP_LOCALS_FULL_NAMES
#define LEAN_DEFAULT_PP_LOCALS_FULL_NAMES false
#endif

#ifndef LEAN_DEFAULT_PP_BETA
#define LEAN_DEFAULT_PP_BETA false
#endif

#ifndef LEAN_DEFAULT_PP_NUMERALS
#define LEAN_DEFAULT_PP_NUMERALS true
#endif

#ifndef LEAN_DEFAULT_PP_STRINGSS
#define LEAN_DEFAULT_PP_STRINGS true
#endif

#ifndef LEAN_DEFAULT_PP_PRETERM
#define LEAN_DEFAULT_PP_PRETERM false
#endif

#ifndef LEAN_DEFAULT_PP_GOAL_COMPACT
#define LEAN_DEFAULT_PP_GOAL_COMPACT false
#endif

#ifndef LEAN_DEFAULT_PP_GOAL_MAX_HYPS
#define LEAN_DEFAULT_PP_GOAL_MAX_HYPS 200
#endif

#ifndef LEAN_DEFAULT_PP_HIDE_COMP_IRRELEVANT
#define LEAN_DEFAULT_PP_HIDE_COMP_IRRELEVANT true
#endif

#ifndef LEAN_DEFAULT_PP_BINDER_TYPES
#define LEAN_DEFAULT_PP_BINDER_TYPES true
#endif

#ifndef LEAN_DEFAULT_PP_DELAYED_ABSTRACTION
#define LEAN_DEFAULT_PP_DELAYED_ABSTRACTION true
#endif

#ifndef LEAN_DEFAULT_PP_ALL
#define LEAN_DEFAULT_PP_ALL false
#endif

#ifndef LEAN_DEFAULT_PP_STRUCTURE_INSTANCES
#define LEAN_DEFAULT_PP_STRUCTURE_INSTANCES true
#endif

#ifndef LEAN_DEFAULT_PP_STRUCTURE_INSTANCES_QUALIFIER
#define LEAN_DEFAULT_PP_STRUCTURE_INSTANCES_QUALIFIER false
#endif

#ifndef LEAN_DEFAULT_PP_STRUCTURE_PROJECTIONS
#define LEAN_DEFAULT_PP_STRUCTURE_PROJECTIONS true
#endif

#ifndef LEAN_DEFAULT_PP_INSTANTIATE_MVARS
#define LEAN_DEFAULT_PP_INSTANTIATE_MVARS true
#endif

#ifndef LEAN_DEFAULT_PP_USE_HOLES
#define LEAN_DEFAULT_PP_USE_HOLES false
#endif

#ifndef LEAN_DEFAULT_PP_ANNOTATIONS
#define LEAN_DEFAULT_PP_ANNOTATIONS false
#endif

namespace lean {
static name * g_pp_max_depth         = nullptr;
static name * g_pp_max_steps         = nullptr;
static name * g_pp_notation          = nullptr;
static name * g_pp_implicit          = nullptr;
static name * g_pp_proofs            = nullptr;
static name * g_pp_coercions         = nullptr;
static name * g_pp_universes         = nullptr;
static name * g_pp_full_names        = nullptr;
static name * g_pp_private_names     = nullptr;
static name * g_pp_purify_metavars   = nullptr;
static name * g_pp_purify_locals     = nullptr;
static name * g_pp_locals_full_names = nullptr;
static name * g_pp_beta              = nullptr;
static name * g_pp_numerals          = nullptr;
static name * g_pp_strings           = nullptr;
static name * g_pp_preterm           = nullptr;
static name * g_pp_goal_compact      = nullptr;
static name * g_pp_goal_max_hyps     = nullptr;
static name * g_pp_binder_types      = nullptr;
static name * g_pp_hide_comp_irrel   = nullptr;
static name * g_pp_delayed_abstraction = nullptr;
static name * g_pp_structure_instances = nullptr;
static name * g_pp_structure_instances_qualifier = nullptr;
static name * g_pp_structure_projections    = nullptr;
static name * g_pp_instantiate_mvars = nullptr;
static name * g_pp_use_holes         = nullptr;
static name * g_pp_annotations       = nullptr;
static name * g_pp_all               = nullptr;
static list<options> * g_distinguishing_pp_options = nullptr;

void initialize_pp_options() {
    g_pp_max_depth         = new name{"pp", "max_depth"};
    g_pp_max_steps         = new name{"pp", "max_steps"};
    g_pp_notation          = new name{"pp", "notation"};
    g_pp_implicit          = new name{"pp", "implicit"};
    g_pp_proofs            = new name{"pp", "proofs"};
    g_pp_coercions         = new name{"pp", "coercions"};
    g_pp_universes         = new name{"pp", "universes"};
    g_pp_full_names        = new name{"pp", "full_names"};
    g_pp_private_names     = new name{"pp", "private_names"};
    g_pp_purify_metavars   = new name{"pp", "purify_metavars"};
    g_pp_purify_locals     = new name{"pp", "purify_locals"};
    g_pp_locals_full_names = new name{"pp", "locals_full_names"};
    g_pp_beta              = new name{"pp", "beta"};
    g_pp_numerals          = new name{"pp", "numerals"};
    g_pp_strings           = new name{"pp", "strings"};
    g_pp_preterm           = new name{"pp", "preterm"};
    g_pp_binder_types      = new name{"pp", "binder_types"};
    g_pp_hide_comp_irrel   = new name{"pp", "hide_comp_irrelevant"};
    g_pp_all               = new name{"pp", "all"};
    g_pp_delayed_abstraction  = new name{"pp", "delayed_abstraction"};
    g_pp_goal_compact      = new name{"pp", "goal", "compact"};
    g_pp_goal_max_hyps     = new name{"pp", "goal", "max_hypotheses"};
    g_pp_structure_instances = new name{"pp", "structure_instances"};
    g_pp_structure_instances_qualifier = new name{"pp", "structure_instances_qualifier"};
    g_pp_structure_projections = new name{"pp", "structure_projections"};
    g_pp_instantiate_mvars = new name{"pp", "instantiate_mvars"};
    g_pp_use_holes         = new name{"pp", "use_holes"};
    g_pp_annotations       = new name{"pp", "annotations"};

    register_unsigned_option(*g_pp_max_depth, LEAN_DEFAULT_PP_MAX_DEPTH,
                             "(pretty printer) maximum expression depth, after that it will use ellipsis");
    register_unsigned_option(*g_pp_max_steps, LEAN_DEFAULT_PP_MAX_STEPS,
                             "(pretty printer) maximum number of visited expressions, after that it will use ellipsis");
    register_bool_option(*g_pp_notation,  LEAN_DEFAULT_PP_NOTATION,
                         "(pretty printer) disable/enable notation (infix, mixfix, postfix operators and unicode characters)");
    register_bool_option(*g_pp_implicit,  LEAN_DEFAULT_PP_IMPLICIT,
                         "(pretty printer) display implicit parameters");
    register_bool_option(*g_pp_proofs,  LEAN_DEFAULT_PP_PROOFS,
                         "(pretty printer) if set to false, the type will be displayed instead of the value for every proof appearing as an argument to a function");
    register_bool_option(*g_pp_coercions,  LEAN_DEFAULT_PP_COERCIONS,
                         "(pretty printer) display coercionss");
    register_bool_option(*g_pp_universes,  LEAN_DEFAULT_PP_UNIVERSES,
                         "(pretty printer) display universes");
    register_bool_option(*g_pp_full_names,  LEAN_DEFAULT_PP_FULL_NAMES,
                         "(pretty printer) display fully qualified names");
    register_bool_option(*g_pp_private_names,  LEAN_DEFAULT_PP_PRIVATE_NAMES,
                         "(pretty printer) display internal names assigned to private declarations");
    register_bool_option(*g_pp_purify_metavars, LEAN_DEFAULT_PP_PURIFY_METAVARS,
                         "(pretty printer) rename internal metavariable names (with \"user-friendly\" ones) "
                         "before pretty printing");
    register_bool_option(*g_pp_purify_locals, LEAN_DEFAULT_PP_PURIFY_LOCALS,
                         "(pretty printer) rename local names to avoid name capture, "
                         "before pretty printing");
    register_bool_option(*g_pp_locals_full_names, LEAN_DEFAULT_PP_LOCALS_FULL_NAMES,
                         "(pretty printer) show full names of locals");
    register_bool_option(*g_pp_beta,  LEAN_DEFAULT_PP_BETA,
                         "(pretty printer) apply beta-reduction when pretty printing");
    register_bool_option(*g_pp_numerals, LEAN_DEFAULT_PP_NUMERALS,
                         "(pretty printer) display nat/num numerals in decimal notation");
    register_bool_option(*g_pp_strings, LEAN_DEFAULT_PP_STRINGS,
                         "(pretty printer) pretty print string and character literals");
    register_bool_option(*g_pp_preterm, LEAN_DEFAULT_PP_PRETERM,
                         "(pretty printer) assume the term is a preterm (i.e., a term before elaboration)");
    register_bool_option(*g_pp_goal_compact, LEAN_DEFAULT_PP_GOAL_COMPACT,
                         "(pretty printer) try to display goal in a single line when possible");
    register_unsigned_option(*g_pp_goal_max_hyps, LEAN_DEFAULT_PP_GOAL_MAX_HYPS,
                             "(pretty printer) maximum number of hypotheses to be displayed");
    register_bool_option(*g_pp_hide_comp_irrel, LEAN_DEFAULT_PP_HIDE_COMP_IRRELEVANT,
                         "(pretty printer) hide terms marked as computationally irrelevant, these marks are introduced by the code generator");
    register_bool_option(*g_pp_binder_types, LEAN_DEFAULT_PP_BINDER_TYPES,
                         "(pretty printer) display types of lambda and Pi parameters");
    register_bool_option(*g_pp_delayed_abstraction, LEAN_DEFAULT_PP_DELAYED_ABSTRACTION,
                         "(pretty printer) display the location of delayed-abstractions (for debugging purposes)");
    register_bool_option(*g_pp_structure_instances, LEAN_DEFAULT_PP_STRUCTURE_INSTANCES,
                         "(pretty printer) display structure instances using the '{ field_name := field_value, ... }' notation "
                         "or '⟨field_value, ... ⟩' if structure is tagged with [pp_using_anonymous_constructor] attribute");
    register_bool_option(*g_pp_structure_instances_qualifier, LEAN_DEFAULT_PP_STRUCTURE_INSTANCES_QUALIFIER,
                         "(pretty printer) include qualifier 'struct_name .' "
                         "when displaying structure instances using the '{ struct_name . field_name := field_value, ... }' notation, "
                         "this option is ignored when pp.structure_instances is false");
    register_bool_option(*g_pp_structure_projections, LEAN_DEFAULT_PP_STRUCTURE_PROJECTIONS,
                         "(pretty printer) display structure projections using field notation");
    register_bool_option(*g_pp_all, LEAN_DEFAULT_PP_ALL,
                         "(pretty printer) display coercions, implicit parameters, proof terms, fully qualified names, universes, "
                         "and disable beta reduction and notation during pretty printing");
    register_bool_option(*g_pp_instantiate_mvars, LEAN_DEFAULT_PP_INSTANTIATE_MVARS,
                         "(pretty printer) instantiate assigned metavariables before pretty printing terms and goals");
    register_bool_option(*g_pp_use_holes, LEAN_DEFAULT_PP_USE_HOLES,
                         "(pretty printer) use holes '{! !}' when pretty printing metavariables and `sorry`");
    register_bool_option(*g_pp_annotations, LEAN_DEFAULT_PP_ANNOTATIONS,
                         "(pretty printer) display internal annotations (for debugging purposes only)");

    options universes_true(*g_pp_universes, true);
    options full_names_true(*g_pp_full_names, true);
    options implicit_true(*g_pp_implicit, true);
    options proofs_true(*g_pp_proofs, true);
    options coercions_true(*g_pp_coercions, true);
    options notation_false(*g_pp_notation, false);
    options binder_types_true(*g_pp_binder_types, true);
    options implicit_coercions = join(coercions_true, implicit_true);
    options implicit_notation  = join(notation_false, implicit_true);
    options all = universes_true + implicit_true + proofs_true + coercions_true + notation_false + full_names_true + binder_types_true;
    g_distinguishing_pp_options = new list<options>({implicit_true, full_names_true, coercions_true, implicit_coercions,
                implicit_notation, universes_true, all});

    set_distinguishing_pp_options(*g_distinguishing_pp_options);
}

void finalize_pp_options() {
    delete g_pp_preterm;
    delete g_pp_numerals;
    delete g_pp_strings;
    delete g_pp_max_depth;
    delete g_pp_max_steps;
    delete g_pp_notation;
    delete g_pp_implicit;
    delete g_pp_proofs;
    delete g_pp_coercions;
    delete g_pp_universes;
    delete g_pp_full_names;
    delete g_pp_private_names;
    delete g_pp_purify_metavars;
    delete g_pp_purify_locals;
    delete g_pp_locals_full_names;
    delete g_pp_beta;
    delete g_pp_goal_compact;
    delete g_pp_goal_max_hyps;
    delete g_pp_binder_types;
    delete g_pp_hide_comp_irrel;
    delete g_pp_structure_instances;
    delete g_pp_structure_instances_qualifier;
    delete g_pp_structure_projections;
    delete g_pp_all;
    delete g_pp_delayed_abstraction;
    delete g_pp_instantiate_mvars;
    delete g_pp_use_holes;
    delete g_pp_annotations;
    delete g_distinguishing_pp_options;
}

name const & get_pp_implicit_name() { return *g_pp_implicit; }
name const & get_pp_proofs_name() { return *g_pp_proofs; }
name const & get_pp_coercions_name() { return *g_pp_coercions; }
name const & get_pp_full_names_name() { return *g_pp_full_names; }
name const & get_pp_universes_name() { return *g_pp_universes; }
name const & get_pp_notation_name() { return *g_pp_notation; }
name const & get_pp_purify_metavars_name() { return *g_pp_purify_metavars; }
name const & get_pp_purify_locals_name() { return *g_pp_purify_locals; }
name const & get_pp_locals_full_names_name() { return *g_pp_locals_full_names; }
name const & get_pp_beta_name() { return *g_pp_beta; }
name const & get_pp_preterm_name() { return *g_pp_preterm; }
name const & get_pp_numerals_name() { return *g_pp_numerals; }
name const & get_pp_strings_name() { return *g_pp_strings; }
name const & get_pp_use_holes_name() { return *g_pp_use_holes; }
name const & get_pp_binder_types_name() { return *g_pp_binder_types; }

unsigned get_pp_max_depth(options const & opts)         { return opts.get_unsigned(*g_pp_max_depth, LEAN_DEFAULT_PP_MAX_DEPTH); }
unsigned get_pp_max_steps(options const & opts)         { return opts.get_unsigned(*g_pp_max_steps, LEAN_DEFAULT_PP_MAX_STEPS); }
bool     get_pp_notation(options const & opts)          { return opts.get_bool(*g_pp_notation, LEAN_DEFAULT_PP_NOTATION); }
bool     get_pp_implicit(options const & opts)          { return opts.get_bool(*g_pp_implicit, LEAN_DEFAULT_PP_IMPLICIT); }
bool     get_pp_proofs(options const & opts)            { return opts.get_bool(*g_pp_proofs, LEAN_DEFAULT_PP_PROOFS); }
bool     get_pp_coercions(options const & opts)         { return opts.get_bool(*g_pp_coercions, LEAN_DEFAULT_PP_COERCIONS); }
bool     get_pp_universes(options const & opts)         { return opts.get_bool(*g_pp_universes, LEAN_DEFAULT_PP_UNIVERSES); }
bool     get_pp_full_names(options const & opts)        { return opts.get_bool(*g_pp_full_names, LEAN_DEFAULT_PP_FULL_NAMES); }
bool     get_pp_private_names(options const & opts)     { return opts.get_bool(*g_pp_private_names, LEAN_DEFAULT_PP_PRIVATE_NAMES); }
bool     get_pp_purify_metavars(options const & opts)   { return opts.get_bool(*g_pp_purify_metavars, LEAN_DEFAULT_PP_PURIFY_METAVARS); }
bool     get_pp_purify_locals(options const & opts)     { return opts.get_bool(*g_pp_purify_locals, LEAN_DEFAULT_PP_PURIFY_LOCALS); }
bool     get_pp_locals_full_names(options const & opts) { return opts.get_bool(*g_pp_locals_full_names, LEAN_DEFAULT_PP_LOCALS_FULL_NAMES); }
bool     get_pp_beta(options const & opts)              { return opts.get_bool(*g_pp_beta, LEAN_DEFAULT_PP_BETA); }
bool     get_pp_numerals(options const & opts)          { return opts.get_bool(*g_pp_numerals, LEAN_DEFAULT_PP_NUMERALS); }
bool     get_pp_strings(options const & opts)           { return opts.get_bool(*g_pp_strings, LEAN_DEFAULT_PP_STRINGS); }
bool     get_pp_preterm(options const & opts)           { return opts.get_bool(*g_pp_preterm, LEAN_DEFAULT_PP_PRETERM); }
bool     get_pp_goal_compact(options const & opts)      { return opts.get_bool(*g_pp_goal_compact, LEAN_DEFAULT_PP_GOAL_COMPACT); }
unsigned get_pp_goal_max_hyps(options const & opts)     { return opts.get_unsigned(*g_pp_goal_max_hyps, LEAN_DEFAULT_PP_GOAL_MAX_HYPS); }
bool     get_pp_binder_types(options const & opts)      { return opts.get_bool(*g_pp_binder_types, LEAN_DEFAULT_PP_BINDER_TYPES); }
bool     get_pp_hide_comp_irrel(options const & opts)   { return opts.get_bool(*g_pp_hide_comp_irrel, LEAN_DEFAULT_PP_HIDE_COMP_IRRELEVANT); }
bool     get_pp_delayed_abstraction(options const & opts) { return opts.get_bool(*g_pp_delayed_abstraction, LEAN_DEFAULT_PP_DELAYED_ABSTRACTION); }
bool     get_pp_structure_instances(options const & opts) { return opts.get_bool(*g_pp_structure_instances, LEAN_DEFAULT_PP_STRUCTURE_INSTANCES); }
bool     get_pp_structure_instances_qualifier(options const & opts) { return opts.get_bool(*g_pp_structure_instances_qualifier, LEAN_DEFAULT_PP_STRUCTURE_INSTANCES_QUALIFIER); }
bool     get_pp_structure_projections(options const & opts) { return opts.get_bool(*g_pp_structure_projections, LEAN_DEFAULT_PP_STRUCTURE_PROJECTIONS); }
bool     get_pp_instantiate_mvars(options const & o)    { return o.get_bool(*g_pp_instantiate_mvars, LEAN_DEFAULT_PP_INSTANTIATE_MVARS); }
bool     get_pp_use_holes(options const & o)            { return o.get_bool(*g_pp_use_holes, LEAN_DEFAULT_PP_USE_HOLES); }
bool     get_pp_annotations(options const & o)          { return o.get_bool(*g_pp_annotations, LEAN_DEFAULT_PP_ANNOTATIONS); }
bool     get_pp_all(options const & opts)               { return opts.get_bool(*g_pp_all, LEAN_DEFAULT_PP_ALL); }
}
