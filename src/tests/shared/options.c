/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include "api/lean.h"

void check_core(int v, unsigned l) {
    if (!v) {
        printf("Test failed at line %d\n", l);
        exit(1);
    }
}

#define check(v) check_core(v, __LINE__)

int main() {
    lean_exception ex;
    lean_name an, verbose, pp, pp_unicode, seed, output;
    lean_options o1, o2, o3, o4, o5, o6;
    char const * s1;
    char const * s2;
    lean_bool b; unsigned u;

    check(lean_name_mk_anonymous(&an, &ex));
    check(lean_name_mk_str(an, "verbose", &verbose, &ex));
    check(lean_name_mk_str(an, "pp", &pp, &ex));
    check(lean_name_mk_str(pp, "unicode", &pp_unicode, &ex));
    check(lean_name_mk_str(an, "seed", &seed, &ex));
    check(lean_name_mk_str(an, "output", &output, &ex));

    check(lean_options_mk_empty(&o1, &ex));
    check(lean_options_set_bool(o1, pp_unicode, lean_true, &o2, &ex));
    check(lean_options_set_unsigned(o2, verbose, 10, &o3, &ex));
    check(lean_options_set_double(o3, seed, 1.23, &o4, &ex));

    check(lean_options_set_bool(o1, pp_unicode, lean_true, &o5, &ex));
    check(lean_options_eq(o2, o5));

    check(lean_options_to_string(o4, &s1, &ex));

    printf("Lean options: %s\n", s1);

    check(lean_options_get_bool(o3, pp_unicode, &b, &ex));
    check(b == lean_true);

    check(lean_options_get_unsigned(o4, verbose, &u, &ex));
    check(u == 10);

    check(lean_options_set_string(o4, output, "~/tmp/file.olean", &o6, &ex));

    check(lean_options_get_string(o6, output, &s2, &ex));
    check(strcmp("~/tmp/file.olean", s2) == 0);

    lean_name_del(an);
    lean_name_del(verbose);
    lean_name_del(pp);
    lean_name_del(pp_unicode);
    lean_name_del(seed);
    lean_name_del(output);

    lean_options_del(o1);
    lean_options_del(o2);
    lean_options_del(o3);
    lean_options_del(o4);
    lean_options_del(o5);
    lean_options_del(o6);

    lean_string_del(s1);
    lean_string_del(s2);
    return 0;
}
