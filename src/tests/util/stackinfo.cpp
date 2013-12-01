/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include "util/test.h"
#include "util/stackinfo.h"
using namespace lean;

static char foo(int i) {
    #define SZ 1000000
    char buffer[SZ];
    buffer[i] = i;
    std::cout << get_available_stack_size() << "\n";
    return buffer[i];
}

static void tst1() {
    std::cout << get_available_stack_size() << "\n";
    foo(10);
    std::cout << get_available_stack_size() << "\n";
}

int main() {
    save_stack_info();
    tst1();
    return has_violations() ? 1 : 0;
}
