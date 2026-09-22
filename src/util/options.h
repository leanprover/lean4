/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <algorithm>
#include "util/name.h"
#include "util/kvmap.h"

namespace lean {
/** \brief Configuration options. */
class options : public object_ref {
public:
    options();
    explicit options(obj_arg o): object_ref(o) {}
    bool get_bool(name const & n, bool default_value = false) const;
    friend bool is_eqp(options const & a, options const & b) { return a.raw() == b.raw(); }
};

void initialize_options();
void finalize_options();
}
