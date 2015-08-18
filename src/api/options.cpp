/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/sstream.h"
#include "api/name.h"
#include "api/string.h"
#include "api/options.h"
using namespace lean; // NOLINT

lean_bool lean_options_mk_empty(lean_options * r, lean_exception * ex) {
    LEAN_TRY;
    *r = of_options(new options());
    LEAN_CATCH;
}

lean_bool lean_options_set_bool(lean_options o, lean_name n, lean_bool v, lean_options * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(o);
    check_nonnull(n);
    *r = of_options(new options(to_options_ref(o).update(to_name_ref(n), static_cast<bool>(v))));
    LEAN_CATCH;
}

lean_bool lean_options_set_int(lean_options o, lean_name n, int v, lean_options * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(o);
    check_nonnull(n);
    *r = of_options(new options(to_options_ref(o).update(to_name_ref(n), v)));
    LEAN_CATCH;
}

lean_bool lean_options_set_unsigned(lean_options o, lean_name n, unsigned v, lean_options * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(o);
    check_nonnull(n);
    *r = of_options(new options(to_options_ref(o).update(to_name_ref(n), v)));
    LEAN_CATCH;
}

lean_bool lean_options_set_double(lean_options o, lean_name n, double v, lean_options * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(o);
    check_nonnull(n);
    *r = of_options(new options(to_options_ref(o).update(to_name_ref(n), v)));
    LEAN_CATCH;
}

lean_bool lean_options_set_string(lean_options o, lean_name n, char const * v, lean_options * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(o);
    check_nonnull(n);
    check_nonnull(v);
    *r = of_options(new options(to_options_ref(o).update(to_name_ref(n), std::string(v).c_str())));
    LEAN_CATCH;
}

lean_bool lean_options_join(lean_options o1, lean_options o2, lean_options * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(o1);
    check_nonnull(o2);
    *r = of_options(new options(join(to_options_ref(o1), to_options_ref(o2))));
    LEAN_CATCH;
}

void lean_options_del(lean_options o) {
    delete to_options(o);
}

lean_bool lean_options_to_string(lean_options o, char const ** r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(o);
    std::ostringstream out;
    out << to_options_ref(o);
    *r = mk_string(out.str());
    LEAN_CATCH;
}

lean_bool lean_options_eq(lean_options o1, lean_options o2) {
    return o1 && o2 && to_options_ref(o1) == to_options_ref(o2);
}

lean_bool lean_options_empty(lean_options o) {
    return o && to_options_ref(o).empty();
}

lean_bool lean_options_contains(lean_options o, lean_name n) {
    return o && n && to_options_ref(o).contains(to_name_ref(n));
}

static void check_entry(lean_options o, lean_name n) {
    check_nonnull(o);
    check_nonnull(n);
    if (!lean_options_contains(o, n))
        throw exception(sstream() << "options object does not contain entry '" << to_name_ref(n) << "'");
}

lean_bool lean_options_get_bool(lean_options o, lean_name n, lean_bool * r, lean_exception * ex) {
    LEAN_TRY;
    check_entry(o, n);
    *r = to_options_ref(o).get_bool(to_name_ref(n), false);
    LEAN_CATCH;
}

lean_bool lean_options_get_int(lean_options o, lean_name n, int * r, lean_exception * ex) {
    LEAN_TRY;
    check_entry(o, n);
    *r = to_options_ref(o).get_int(to_name_ref(n), 0);
    LEAN_CATCH;
}

lean_bool lean_options_get_unsigned(lean_options o, lean_name n, unsigned * r, lean_exception * ex) {
    LEAN_TRY;
    check_entry(o, n);
    *r = to_options_ref(o).get_unsigned(to_name_ref(n), 0);
    LEAN_CATCH;
}

lean_bool lean_options_get_double(lean_options o, lean_name n, double * r, lean_exception * ex) {
    LEAN_TRY;
    check_entry(o, n);
    *r = to_options_ref(o).get_double(to_name_ref(n), 0.0);
    LEAN_CATCH;
}

lean_bool lean_options_get_string(lean_options o, lean_name n, char const ** r, lean_exception * ex) {
    LEAN_TRY;
    check_entry(o, n);
    *r = mk_string(to_options_ref(o).get_string(to_name_ref(n), ""));
    LEAN_CATCH;
}
