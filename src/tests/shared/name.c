#include <stdlib.h>
#include <stdio.h>
#include "api/lean.h"

void check(int v) {
    if (!v) {
        printf("test failed\n");
        exit(1);
    }
}

int main() {
    lean_exception ex;
    lean_name a, n1, n2, n3, n4, n5;
    char const * s1;
    char const * s2;
    char const * s3;
    unsigned idx;
    printf("Started name test\n");
    check(lean_mk_anonymous_name(&a, &ex));
    check(lean_is_anonymous_name(a));
    check(lean_mk_str_name(a, "foo", &n1, &ex));
    check(lean_mk_str_name(n1, "bla", &n2, &ex));
    check(lean_name_to_string(n2, &s1, &ex));
    printf("Lean name: %s\n", s1);
    check(lean_is_str_name(n2));
    check(!lean_is_anonymous_name(n2));
    check(!lean_is_idx_name(n2));
    check(lean_mk_idx_name(n2, 1, &n3, &ex));
    check(lean_name_to_string(n3, &s2, &ex));
    printf("Lean name: %s\n", s2);
    check(lean_is_idx_name(n3));
    check(lean_get_name_prefix(n3, &n4, &ex));
    check(lean_name_eq(n2, n4));
    check(lean_get_name_idx(n3, &idx, &ex));
    check(idx == 1);
    check(!lean_get_name_prefix(a, &n5, &ex));
    s3 = lean_get_exception_message(ex);
    printf("Lean exception: %s\n", s3);
    lean_del_name(a);
    lean_del_name(n1);
    lean_del_name(n2);
    lean_del_name(n3);
    lean_del_name(n4);
    lean_del_string(s1);
    lean_del_string(s2);
    lean_del_string(s3);
    lean_del_exception(ex);
    return 0;
}
