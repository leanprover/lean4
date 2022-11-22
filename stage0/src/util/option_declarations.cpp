/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "runtime/array_ref.h"
#include "runtime/pair_ref.h"
#include "util/option_declarations.h"
#include "util/io.h"

namespace lean {
typedef object_ref option_decl;

extern "C" object * lean_data_value_to_string (obj_arg d);

extern "C" object * lean_get_option_decls_array(obj_arg w);

option_declarations get_option_declarations() {
    auto decl_array = get_io_result<array_ref<pair_ref<name, option_decl> > > (lean_get_option_decls_array(io_mk_world()));
    option_declarations r;
    for (pair_ref<name, option_decl> const & p : decl_array) {
        option_decl decl = p.snd();
        data_value def_val = cnstr_get_ref_t<data_value>(decl, 1);
        string_ref def_str(lean_data_value_to_string(def_val.to_obj_arg()));
        string_ref descr = cnstr_get_ref_t<string_ref>(decl, 3);
        data_value_kind kind = static_cast<data_value_kind>(lean_obj_tag(def_val.raw()));
        option_declaration d(p.fst(), kind, def_str.data(), descr.data());
        r.insert(p.fst(), d);
    }
    return r;
}

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

extern "C" object * lean_register_option(obj_arg name, obj_arg decl, obj_arg w);

void register_option(name const & n, name const & decl_name, data_value_kind k, char const * default_value, char const * description) {
    object_ref decl = mk_cnstr(0, decl_name, mk_data_value(k, default_value), string_ref(""), string_ref(description));
    consume_io_result(lean_register_option(n.to_obj_arg(), decl.to_obj_arg(), io_mk_world()));
}
}
