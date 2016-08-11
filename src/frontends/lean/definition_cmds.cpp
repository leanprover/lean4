/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "frontends/lean/parser.h"

namespace lean {
struct mutual_definition_cmd_fn {
    parser & m_p;
    bool     m_is_private;
    bool     m_is_protected;
    bool     m_is_noncomputable;

    mutual_definition_cmd_fn(parser & p, bool is_private, bool is_protected, bool is_noncomputable):
        m_p(p), m_is_private(is_private), m_is_protected(is_protected), m_is_noncomputable(is_noncomputable) {
    }

    environment operator()() {
        // TODO(Leo)
        lean_unreachable();
    }
};

environment mutual_definition_cmd_core(parser & p, bool is_private, bool is_protected, bool is_noncomputable) {
    return mutual_definition_cmd_fn(p, is_private, is_protected, is_noncomputable)();
}
}
