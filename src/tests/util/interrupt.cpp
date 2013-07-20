/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <chrono>
#include <mutex>
#include "interrupt.h"
#include "test.h"

std::mutex g_stdout_mutex;

static void loop(unsigned i) {
    try {
        while (true) {
            lean::check_interrupt();
        }
    }
    catch (lean::interrupt) {
        std::lock_guard<std::mutex> lock(g_stdout_mutex);
        std::cout << "interrupted " << i << ".\n";
    }
}

static void tst1() {
    lean::interruptible_thread t1([](){ loop(1); });
    lean::interruptible_thread t2([](){ loop(2); });

    std::chrono::milliseconds dura(200);
    std::this_thread::sleep_for(dura);
    t2.request_interrupt();

    std::this_thread::sleep_for(dura);
    t1.request_interrupt();

    t1.join();
    t2.join();
}

int main() {
    tst1();
    return 0;
}
