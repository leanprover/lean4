/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "runtime/pair_ref.h"
#include "util/name.h"

namespace lean {
enum class data_value_kind { String, Bool, Name, Nat, /* Int, Syntax */ };
/*
inductive DataValue
| ofString (v : String)
| ofBool   (v : Bool)
| ofName   (v : Name)
| ofNat    (v : Nat)
| ofInt    (v : Int)
| ofSyntax (v : Syntax)
*/
class data_value : public object_ref {
    data_value(b_obj_arg o, bool b):object_ref(o, b) {}
public:
    explicit data_value(char const * v):object_ref(mk_cnstr(static_cast<unsigned>(data_value_kind::String), mk_string(v))) {}
    explicit data_value(string_ref const & v):object_ref(mk_cnstr(static_cast<unsigned>(data_value_kind::String), v.raw())) { inc(v.raw()); }
    explicit data_value(nat const & v):object_ref(mk_cnstr(static_cast<unsigned>(data_value_kind::Nat), v.raw())) { inc(v.raw()); }
    explicit data_value(bool v);
    explicit data_value(name const & v):object_ref(mk_cnstr(static_cast<unsigned>(data_value_kind::Name), v.raw())) { inc(v.raw()); }
    data_value():data_value(false) {}
    data_value(data_value const & other):object_ref(other) {}
    data_value(data_value && other) noexcept:object_ref(std::move(other)) {}
    data_value & operator=(data_value const & other) { object_ref::operator=(other); return *this; }
    data_value & operator=(data_value && other) noexcept { object_ref::operator=(std::move(other)); return *this; }

    data_value_kind kind() const { return static_cast<data_value_kind>(cnstr_tag(raw())); }
    string_ref const & get_string() const { lean_assert(kind() == data_value_kind::String); return static_cast<string_ref const &>(cnstr_get_ref(*this, 0)); }
    nat const & get_nat() const { lean_assert(kind() == data_value_kind::Nat); return static_cast<nat const &>(cnstr_get_ref(*this, 0)); }
    name const & get_name() const { lean_assert(kind() == data_value_kind::Name); return static_cast<name const &>(cnstr_get_ref(*this, 0)); }
    bool get_bool() const;

    friend bool operator==(data_value const & a, data_value const & b);
    friend bool operator<(data_value const & a, data_value const & b);
};

bool operator==(data_value const & a, data_value const & b);
inline bool operator!=(data_value const & a, data_value const & b) { return !(a == b); }
bool operator<(data_value const & a, data_value const & b);

typedef pair_ref<name, data_value> kvmap_entry;
typedef list_ref<kvmap_entry> kvmap;
}
