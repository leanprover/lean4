/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/kvmap.h"

namespace lean {
extern "C" object * lean_mk_bool_data_value(bool b);
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

optional<data_value> find(kvmap m, name const & k) {
    while (!is_nil(m)) {
        if (head(m).fst() == k)
            return optional<data_value>(head(m).snd());
        m = tail(m);
    }
    return optional<data_value>();
}

optional<string_ref> get_string(kvmap const & m, name const & k) {
    optional<data_value> r = find(m, k);
    if (r && r->kind() == data_value_kind::String)
        return optional<string_ref>(r->get_string());
    else
        return optional<string_ref>();
}

optional<nat> get_nat(kvmap const & m, name const & k) {
    optional<data_value> r = find(m, k);
    if (r && r->kind() == data_value_kind::Nat)
        return optional<nat>(r->get_nat());
    else
        return optional<nat>();
}

optional<bool> get_bool(kvmap const & m, name const & k) {
    optional<data_value> r = find(m, k);
    if (r && r->kind() == data_value_kind::Bool)
        return optional<bool>(r->get_bool());
    else
        return optional<bool>();
}

optional<name> get_name(kvmap const & m, name const & k) {
    optional<data_value> r = find(m, k);
    if (r && r->kind() == data_value_kind::Name)
        return optional<name>(r->get_name());
    else
        return optional<name>();
}

static kvmap insert(kvmap const & m, name const & k, data_value const & v) {
    if (is_nil(m))
        return kvmap(kvmap_entry(k, v));
    else if (head(m).fst() == k)
        return kvmap(kvmap_entry(k, v), tail(m));
    else
        return kvmap(head(m), insert(tail(m), k, v));
}

kvmap set_string(kvmap const & m, name const & k, string_ref const & v) {
    return insert(m, k, data_value(v));
}

kvmap set_bool(kvmap const & m, name const & k, bool v) {
    return insert(m, k, data_value(v));
}

kvmap set_name(kvmap const & m, name const & k, name const & v) {
    return insert(m, k, data_value(v));
}

kvmap set_nat(kvmap const & m, name const & k, nat const & v) {
    return insert(m, k, data_value(v));
}
}
