/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "util/test.h"
#include "util/init_module.h"
#include "library/blast/union_find.h"
using namespace lean;

typedef union_find<unsigned, unsigned, unsigned_cmp> uf;

static void check_explain(uf const & m, unsigned n1, unsigned n2, std::initializer_list<unsigned> const & expected_js) {
    buffer<unsigned> js1;
    bool r = m.explain(n1, n2, js1);
    lean_assert(r);
    lean_assert(m.rep(n1) == m.rep(n2));
    std::sort(js1.begin(), js1.end());
    buffer<unsigned> js2;
    js2.append(expected_js.size(), expected_js.begin());
    std::sort(js2.begin(), js2.end());
    lean_assert(js1.size() == js2.size());
    for (unsigned i = 0; i < js1.size(); i++) {
        lean_assert(js1[i] == js2[i]);
    }
}

static void tst1() {
    uf m;
    m.join(1, 2, 0);
    lean_assert(m.is_eq(1, 1));
    lean_assert(m.is_eq(1, 2));
    m.join(1, 3, 1);
    lean_assert(m.is_eq(2, 3));
    check_explain(m, 2, 3, {0, 1});
    check_explain(m, 2, 1, {0});
    check_explain(m, 1, 3, {1});
    m.join(3, 4, 2);
    m.join(5, 1, 3);
    m.join(6, 2, 4);
    lean_assert(m.rep(6) == m.rep(4));
    check_explain(m, 2, 3, {0, 1});
    check_explain(m, 6, 4, {0, 1, 2, 4});
    check_explain(m, 5, 6, {0, 3, 4});
    lean_assert_eq(m.size(1), 6);

    for (unsigned i = 10; i < 30; i++)
        m.join(i, i+1, i);
    check_explain(m, 10, 15, {10, 11, 12, 13, 14});
    lean_assert_eq(m.size(10), 21);
}

int main() {
    save_stack_info();
    initialize_util_module();
    tst1();
    finalize_util_module();
    return has_violations() ? 1 : 0;
}
