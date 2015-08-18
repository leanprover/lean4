#include <stdlib.h>
#include <stdio.h>
#include "api/lean.h"

void check(int v) {
    if (!v) {
        printf("test failed\n");
        exit(1);
    }
}

void anonymous_unique() {
    lean_exception ex;
    lean_name a1, a2;
    check(lean_name_mk_anonymous(&a1, &ex));
    check(lean_name_mk_anonymous(&a2, &ex));
    check(lean_name_eq(a1, a2));
    lean_name_del(a1);
    lean_name_del(a2);
    lean_exception_del(ex);
}

int main() {
    lean_exception ex;
    lean_name a, n1, n2, n3, n4, n5;
    char const * s1;
    char const * s2;
    char const * s3;
    unsigned idx;
    printf("Started name test\n");
    check(lean_name_mk_anonymous(&a, &ex));
    check(lean_name_is_anonymous(a));
    check(lean_name_mk_str(a, "foo", &n1, &ex));
    check(lean_name_mk_str(n1, "bla", &n2, &ex));
    check(lean_name_to_string(n2, &s1, &ex));
    printf("Lean name: %s\n", s1);
    check(lean_name_is_str(n2));
    check(!lean_name_is_anonymous(n2));
    check(!lean_name_is_idx(n2));
    check(lean_name_mk_idx(n2, 1, &n3, &ex));
    check(lean_name_to_string(n3, &s2, &ex));
    printf("Lean name: %s\n", s2);
    check(lean_name_is_idx(n3));
    check(lean_name_get_prefix(n3, &n4, &ex));
    check(lean_name_eq(n2, n4));
    check(lean_name_get_idx(n3, &idx, &ex));
    check(idx == 1);
    check(!lean_name_get_prefix(a, &n5, &ex));
    s3 = lean_exception_get_message(ex);
    printf("Lean exception: %s\n", s3);
    anonymous_unique();
    lean_name_del(a);
    lean_name_del(n1);
    lean_name_del(n2);
    lean_name_del(n3);
    lean_name_del(n4);
    lean_string_del(s1);
    lean_string_del(s2);
    lean_string_del(s3);
    lean_exception_del(ex);
    return 0;
}
