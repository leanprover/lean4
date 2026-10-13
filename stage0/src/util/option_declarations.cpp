/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/option_declarations.h"
#include "util/io.h"

namespace lean {
data_value mk_data_value(data_value_kind k, char const * val) {
    switch (k) {
    case data_value_kind::String:
        return data_value(val);
    case data_value_kind::Bool:
        return strcmp(val, "true") == 0 ? data_value(true) : data_value(false);
    case data_value_kind::Nat:
        return data_value(nat(atoi(val)));
    case data_value_kind::Name:
        return data_value(name(val));
    default:
        lean_unreachable();
    }
}

extern "C" object * lean_register_option(obj_arg name, obj_arg decl);

void register_option(name const & n, name const & decl_name, data_value_kind k, char const * default_value, char const * description) {
    object_ref decl = mk_cnstr(0, n, decl_name, mk_data_value(k, default_value), string_ref(description), object_ref(lean_box(0)));
    consume_io_result(lean_register_option(n.to_obj_arg(), decl.to_obj_arg()));
}
}
