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
#include <atomic>
#include "util/debug.h"
#include "util/shared_mutex.h"
using namespace lean;

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

#ifndef __APPLE__
static void tst3() {
    shared_mutex      mutex;
    std::atomic<bool> t2_started(false);
    std::atomic<bool> t2_done(false);
    std::chrono::milliseconds small_delay(10);

    std::thread t1([&]() {
            while (!t2_started) {
                std::this_thread::sleep_for(small_delay);
            }
            while (!mutex.try_lock()) {
                std::this_thread::sleep_for(small_delay);
            }
            // test recursive try_lock
            lean_verify(mutex.try_lock());
            mutex.unlock();
            // we can only succeed getting the lock if t2 is done
            lean_assert(t2_done);
            mutex.unlock();
        });

    std::thread t2([&]() {
            {
                unique_lock lock(mutex);
                t2_started = true;
                std::this_thread::sleep_for(small_delay);
            }
            t2_done = true;
        });

    t1.join();
    t2.join();
    lean_assert(t2_done);
}

static void tst4() {
    shared_mutex      mutex;
    std::atomic<bool> t2_started(false);
    std::atomic<bool> t2_done(false);
    std::chrono::milliseconds small_delay(10);

    std::thread t1([&]() {
            while (!t2_started) {
                std::this_thread::sleep_for(small_delay);
            }
            while (!mutex.try_lock_shared()) {
                std::this_thread::sleep_for(small_delay);
            }
            // test recursive try_lock_shared
            lean_verify(mutex.try_lock_shared());
            mutex.unlock_shared();
            // we can only succeed getting the lock if t2 is done
            lean_assert(t2_done);
            mutex.unlock_shared();
        });

    std::thread t2([&]() {
            {
                unique_lock lock(mutex);
                t2_started = true;
                std::this_thread::sleep_for(small_delay);
            }
            t2_done = true;
        });

    t1.join();
    t2.join();
    lean_assert(t2_done);
}


static void tst5() {
    shared_mutex      mutex;
    std::atomic<bool> t2_started(false);
    std::atomic<bool> t1_done(false);
    std::chrono::milliseconds small_delay(10);

    std::thread t1([&]() {
            while (!t2_started) {
                std::this_thread::sleep_for(small_delay);
            }
            lean_verify(mutex.try_lock_shared()); // t2 is also using a shared lock
            std::this_thread::sleep_for(small_delay);
            lean_verify(mutex.try_lock_shared());
            std::this_thread::sleep_for(small_delay);
            t1_done = true;
            mutex.unlock_shared();
            std::this_thread::sleep_for(small_delay);
            mutex.unlock_shared();
        });

    std::thread t2([&]() {
            {
                shared_lock lock(mutex);
                t2_started = true;
                while (!t1_done) {
                    std::this_thread::sleep_for(small_delay);
                }
            }
        });

    t1.join();
    t2.join();
}
#else
static void tst3() {}
static void tst4() {}
static void tst5() {}
#endif

int main() {
    tst1();
    tst2();
    tst3();
    tst4();
    tst5();
    return has_violations() ? 1 : 0;
}
