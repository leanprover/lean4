/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/constants.h"
#include "library/unifier.h"
#include "library/kernel_serializer.h"
#include "library/let.h"
#include "library/typed_expr.h"
#include "library/choice.h"
#include "library/class.h"
#include "library/string.h"
#include "library/num.h"
#include "library/resolve_macro.h"
#include "library/annotation.h"
#include "library/explicit.h"
#include "library/module.h"
#include "library/protected.h"
#include "library/private.h"
#include "library/scoped_ext.h"
#include "library/reducible.h"
#include "library/aliases.h"
#include "library/coercion.h"
#include "library/unifier_plugin.h"
#include "library/io_state.h"
#include "library/kernel_bindings.h"
#include "library/idx_metavar.h"
#include "library/sorry.h"
#include "library/placeholder.h"
#include "library/print.h"
#include "library/fingerprint.h"
#include "library/util.h"
#include "library/pp_options.h"
#include "library/projection.h"
#include "library/normalize.h"
#include "library/abbreviation.h"
#include "library/relation_manager.h"
#include "library/user_recursors.h"
#include "library/class_instance_synth.h"
#include "library/composition_manager.h"
#include "library/noncomputable.h"

namespace lean {
void initialize_library_module() {
    initialize_constants();
    initialize_fingerprint();
    initialize_print();
    initialize_placeholder();
    initialize_idx_metavar();
    initialize_kernel_bindings();
    initialize_io_state();
    initialize_unifier();
    initialize_kernel_serializer();
    initialize_let();
    initialize_typed_expr();
    initialize_choice();
    initialize_num();
    initialize_string();
    initialize_resolve_macro();
    initialize_annotation();
    initialize_explicit();
    initialize_module();
    initialize_protected();
    initialize_private();
    initialize_scoped_ext();
    initialize_reducible();
    initialize_aliases();
    initialize_coercion();
    initialize_unifier_plugin();
    initialize_sorry();
    initialize_class();
    initialize_library_util();
    initialize_pp_options();
    initialize_projection();
    initialize_normalize();
    initialize_abbreviation();
    initialize_relation_manager();
    initialize_user_recursors();
    initialize_class_instance_elaborator();
    initialize_composition_manager();
    initialize_noncomputable();
}

void finalize_library_module() {
    finalize_noncomputable();
    finalize_composition_manager();
    finalize_class_instance_elaborator();
    finalize_user_recursors();
    finalize_relation_manager();
    finalize_abbreviation();
    finalize_normalize();
    finalize_projection();
    finalize_pp_options();
    finalize_library_util();
    finalize_class();
    finalize_sorry();
    finalize_unifier_plugin();
    finalize_coercion();
    finalize_aliases();
    finalize_reducible();
    finalize_scoped_ext();
    finalize_private();
    finalize_protected();
    finalize_module();
    finalize_explicit();
    finalize_annotation();
    finalize_resolve_macro();
    finalize_string();
    finalize_num();
    finalize_choice();
    finalize_typed_expr();
    finalize_let();
    finalize_kernel_serializer();
    finalize_unifier();
    finalize_io_state();
    finalize_kernel_bindings();
    finalize_idx_metavar();
    finalize_placeholder();
    finalize_print();
    finalize_fingerprint();
    finalize_constants();
}
}
