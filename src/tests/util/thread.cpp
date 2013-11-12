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
#include "util/shared_mutex.h"

void foo() {
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

static void tst2() {
    unsigned N = 10;
    unsigned n = 1;
    lean::shared_mutex mut;
    std::vector<std::thread> threads;
    for (unsigned i = 0; i < N; i++) {
        threads.emplace_back([&]() {
                unsigned sum = 0;
                {
                    lean::shared_lock lock(mut);
                    for (unsigned i = 0; i < 1000000; i++)
                        sum += n;
                }
                {
                   lean::unique_lock lock(mut);
                   std::cout << sum << "\n";
                }
            });
    }
    for (unsigned i = 0; i < N; i++)
        threads[i].join();
}

int main() {
    tst2(); return 0;
    tst1();
}
