/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/kvmap.h"

namespace lean {
extern "C" object * lean_mk_bool_data_value(uint8 b);
extern "C" uint8 lean_data_value_bool(object * v);
extern "C" uint8 lean_data_value_beq(object * a, object * b);

data_value::data_value(bool v):
    object_ref(lean_mk_bool_data_value(v)) {
}

bool data_value::get_bool() const {
    lean_assert(kind() == data_value_kind::Bool);
    return lean_data_value_bool(to_obj_arg());
}

bool operator==(data_value const & a, data_value const & b) {
    if (a.raw() == b.raw()) return true;
    return lean_data_value_beq(a.to_obj_arg(), b.to_obj_arg());
}

bool operator<(data_value const & a, data_value const & b) {
    if (a.kind() != b.kind()) return static_cast<unsigned>(a.kind()) < static_cast<unsigned>(b.kind());
    switch (a.kind()) {
    case data_value_kind::String:   return a.get_string() < b.get_string();
    case data_value_kind::Nat:      return a.get_nat() < b.get_nat();
    case data_value_kind::Bool:     return !a.get_bool() && b.get_bool();
    case data_value_kind::Name:     return a.get_name() < b.get_name();
    }
    /* TODO: compare Int and Syntax values */
    return false;
}
}
