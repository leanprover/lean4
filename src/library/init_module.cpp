/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/unifier.h"
#include "library/kernel_serializer.h"
#include "library/let.h"
#include "library/typed_expr.h"
#include "library/choice.h"
#include "library/string.h"
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

namespace lean {
void initialize_library_module() {
    initialize_unifier();
    initialize_kernel_serializer();
    initialize_let();
    initialize_typed_expr();
    initialize_choice();
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
}

void finalize_library_module() {
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
    finalize_choice();
    finalize_typed_expr();
    finalize_let();
    finalize_kernel_serializer();
    finalize_unifier();
}
}
