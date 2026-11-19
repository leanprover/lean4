/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <memory>
#include <string>
#include "runtime/sstream.h"
#include "util/options.h"
#include "util/option_declarations.h"
#include "stdlib_flags.h"

#ifndef LEAN_DEFAULT_VERBOSE
#define LEAN_DEFAULT_VERBOSE true
#endif

namespace lean {
void initialize_options() {
}

void finalize_options() {
}

/* getDefaultVerbose (_ : Unit) : Bool */
extern "C" LEAN_EXPORT uint8 lean_internal_get_default_verbose(obj_arg) {
    return LEAN_DEFAULT_VERBOSE;
}

/* getOptionOverrides (_ : Unit) : Options */
extern "C" LEAN_EXPORT obj_res lean_internal_get_option_overrides(obj_arg) {
    return get_option_overrides().steal();
}

extern "C" LEAN_EXPORT obj_res lean_options_get_empty(obj_arg u);
options::options(): object_ref(lean_options_get_empty(box(0))) {}

extern "C" LEAN_EXPORT bool lean_options_get_bool(obj_arg opts, obj_arg n, bool default_value);
bool options::get_bool(name const & n, bool default_value) const {
    return lean_options_get_bool(this->to_obj_arg(), n.to_obj_arg(), default_value);
}

extern "C" LEAN_EXPORT obj_res lean_options_update_bool(obj_arg opts, obj_arg n, bool v);
options options::update(name const & n, bool v) const {
    return options(lean_options_update_bool(this->to_obj_arg(), n.to_obj_arg(), v));
}
}
