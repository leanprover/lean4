/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <cstdlib>
#include <thread>
#include <iostream>
#include <mutex>
#include <vector>

static void foo() {
    static thread_local std::vector<int> v(1024);
    if (v.size() != 1024) {
        std::cerr << "Error\n";
        exit(1);
    }
}

static void tst1() {
    unsigned n = 5;
    for (unsigned i = 0; i < n; i++) {
        std::thread t([](){ foo(); });
        t.join();
    }
}

int main() {
    tst1();
}
