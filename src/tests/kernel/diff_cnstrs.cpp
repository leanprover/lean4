/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/test.h"
#include "kernel/diff_cnstrs.h"
using namespace lean;
typedef diff_cnstrs::node node;
static void tst1() {
    diff_cnstrs c([](node n1, node n2) { std::cout << "New equality: n" << n1 << " n" << n2 << "\n";});
    node n0 = c.mk_node();
    node n1 = c.mk_node();
    node n2 = c.mk_node();
    int  j1; int j2;
    c.add_edge(n0, n1, 10, &j1);
    c.display(std::cout);
    std::cout << "====\n";
    c.add_edge(n1, n2, 20, &j2);
    c.push();
    c.display(std::cout);
    node n3 = c.mk_node();
    node n4 = c.mk_node();
    int j3, j4, j5;
    c.add_edge(n2, n3, 0, &j3);
    c.add_edge(n3, n4, 0, &j4);
    c.add_edge(n4, n2, 0, &j5);
    std::cout << "====\n";
    c.display(std::cout);
    buffer<void *> js;
    c.explain(n2, n4, js);
    lean_assert(js.size() == 2);
    lean_assert(js[0] == &j3 || js[0] == &j4);
    lean_assert(js[1] == &j3 || js[1] == &j4);
    lean_assert(c.is_implied(n1, n4, 10));
    lean_assert(c.is_consistent(n1, n4, 100));
    lean_assert(!c.is_consistent(n4, n1, 0));
    c.disable_node(n1);
    lean_assert(c.is_enabled(n0));
    lean_assert(!c.is_enabled(n1));
    node n5 = c.mk_node();
    c.add_edge(n2, n5, 100, &j5);
    std::cout << "====\n";
    c.display(std::cout);
    c.pop();
    std::cout << "====\n";
    c.display(std::cout);
}

int main() {
    save_stack_info();
    tst1();
    return has_violations() ? 1 : 0;
}

