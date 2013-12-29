/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "frontends/lean/coercion.h"
#include "frontends/lean/frontend.h"

namespace lean {
void coercion_declaration::write(serializer & s) const {
    s << "Coercion" << m_coercion;
}
static void read_coercion(environment const & env, io_state const &, deserializer & d) {
    add_coercion(env, read_expr(d));
}
static object_cell::register_deserializer_fn coercion_ds("Coercion", read_coercion);
}
