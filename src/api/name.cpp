/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "api/name.h"
#include "api/string.h"
#include "api/exception.h"
using namespace lean;

lean_bool lean_mk_anonymous_name(lean_name * r, lean_exception * ex) {
    LEAN_TRY;
    *r = of_name(new name());
    LEAN_CATCH;
}

lean_bool lean_mk_str_name(lean_name pre, char const * s, lean_name * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(pre);
    check_nonnull(s);
    *r = of_name(new name(to_name_ref(pre), s));
    LEAN_CATCH;
}

lean_bool lean_mk_idx_name(lean_name pre, unsigned i, lean_name * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(pre);
    name const & p = to_name_ref(pre);
    if (p.is_anonymous())
        throw lean::exception("invalid argument, prefix is an anonymous name");
    *r = of_name(new name(to_name_ref(pre), i));
    LEAN_CATCH;
}

void lean_del_name(lean_name n) {
    delete to_name(n);
}

lean_bool lean_is_anonymous_name(lean_name n) {
    return n && to_name_ref(n).is_anonymous();
}

lean_bool lean_is_str_name(lean_name n) {
    return n && to_name_ref(n).is_string();
}

lean_bool lean_is_idx_name(lean_name n) {
    return n && to_name_ref(n).is_numeral();
}

lean_bool lean_name_eq(lean_name n1, lean_name n2) {
    return n1 && n2 && to_name_ref(n1) == to_name_ref(n2);
}

lean_bool lean_get_name_prefix(lean_name n, lean_name * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(n);
    if (to_name_ref(n).is_anonymous())
        throw lean::exception("invalid argument, argument is an anonymous name");
    else if (to_name_ref(n).is_atomic())
        *r = of_name(new name());
    else
        *r = of_name(new name(to_name_ref(n).get_prefix()));
    LEAN_CATCH;
}

lean_bool lean_get_name_str(lean_name n, char const ** r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(n);
    if (!lean_is_str_name(n))
        throw lean::exception("invalid argument, it is not a string name");
    *r = mk_string(to_name_ref(n).get_string());
    LEAN_CATCH;
}

lean_bool lean_get_name_idx(lean_name n, unsigned * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(n);
    if (!lean_is_idx_name(n))
        throw lean::exception("invalid argument, it is not an indexed name");
    *r = to_name_ref(n).get_numeral();
    LEAN_CATCH;
}

lean_bool lean_name_to_string(lean_name n, char const **r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(n);
    *r = mk_string(to_name_ref(n).to_string());
    LEAN_CATCH;
}
