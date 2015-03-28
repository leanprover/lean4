/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <cstdlib>
#include <iostream>
#include <vector>
#include "util/thread.h"
#include "util/debug.h"
#include "util/shared_mutex.h"
#include "util/interrupt.h"
#include "util/thread_script_state.h"
#include "util/init_module.h"
using namespace lean;

#if defined(LEAN_MULTI_THREAD) && !defined(__APPLE__)
LEAN_THREAD_PTR(std::vector<int>, g_v);
void finalize_vector() {
    delete g_v;
    g_v = nullptr;
}
void foo() {
    if (!g_v) {
        g_v = new std::vector<int>(1024);
        register_thread_finalizer(finalize_vector);
    }
    if (g_v->size() != 1024) {
        std::cerr << "Error\n";
        exit(1);
    }
}

static void tst1() {
    unsigned n = 5;
    for (unsigned i = 0; i < n; i++) {
        thread t([](){
                foo();
                run_thread_finalizers();
            });
        t.join();
    }
}

static void tst2() {
    unsigned N = 10;
    unsigned n = 1;
    shared_mutex mut;
    std::vector<thread> threads;
    for (unsigned i = 0; i < N; i++) {
        threads.emplace_back([&]() {
                unsigned sum = 0;
                {
                    shared_lock lock(mut);
                    for (unsigned i = 0; i < 1000000; i++)
                        sum += n;
                }
                {
                    exclusive_lock lock(mut);
                    std::cout << sum << "\n";
                }
            });
    }
    for (unsigned i = 0; i < N; i++)
        threads[i].join();
}

static void tst3() {
    shared_mutex      mutex;
    atomic<bool>      t2_started(false);
    atomic<bool>      t2_done(false);
    chrono::milliseconds small_delay(10);

    thread t1([&]() {
            while (!t2_started) {
                this_thread::sleep_for(small_delay);
            }
            while (!mutex.try_lock()) {
                this_thread::sleep_for(small_delay);
            }
            // test recursive try_lock
            lean_verify(mutex.try_lock());
            mutex.unlock();
            // we can only succeed getting the lock if t2 is done
            lean_assert(t2_done);
            mutex.unlock();
        });

    thread t2([&]() {
            {
                exclusive_lock lock(mutex);
                t2_started = true;
                this_thread::sleep_for(small_delay);
            }
            t2_done = true;
        });

    t1.join();
    t2.join();
    lean_assert(t2_done);
}

static void tst4() {
    shared_mutex      mutex;
    atomic<bool>      t2_started(false);
    atomic<bool>      t2_done(false);
    chrono::milliseconds small_delay(10);

    thread t1([&]() {
            while (!t2_started) {
                this_thread::sleep_for(small_delay);
            }
            while (!mutex.try_lock_shared()) {
                this_thread::sleep_for(small_delay);
            }
            // test recursive try_lock_shared
            lean_verify(mutex.try_lock_shared());
            mutex.unlock_shared();
            // we can only succeed getting the lock if t2 is done
            lean_assert(t2_done);
            mutex.unlock_shared();
        });

    thread t2([&]() {
            {
                exclusive_lock lock(mutex);
                t2_started = true;
                this_thread::sleep_for(small_delay);
            }
            t2_done = true;
        });

    t1.join();
    t2.join();
    lean_assert(t2_done);
}

static void tst5() {
    shared_mutex mutex;
    atomic<bool> t2_started(false);
    atomic<bool> t1_done(false);
    chrono::milliseconds small_delay(10);

    thread t1([&]() {
            while (!t2_started) {
                this_thread::sleep_for(small_delay);
            }
            lean_verify(mutex.try_lock_shared()); // t2 is also using a shared lock
            this_thread::sleep_for(small_delay);
            lean_verify(mutex.try_lock_shared());
            this_thread::sleep_for(small_delay);
            t1_done = true;
            mutex.unlock_shared();
            this_thread::sleep_for(small_delay);
            mutex.unlock_shared();
        });

    thread t2([&]() {
            {
                shared_lock lock(mutex);
                t2_started = true;
                while (!t1_done) {
                    this_thread::sleep_for(small_delay);
                }
            }
        });

    t1.join();
    t2.join();
}

static void tst6() {
    interruptible_thread t1([]() {
            try {
                // Remark: this_thread::sleep_for does not check whether the thread has been interrupted or not.
                // this_thread::sleep_for(chrono::milliseconds(1000000));
                sleep_for(1000000);
            } catch (interrupted &) {
                std::cout << "interrupted...\n";
            }
        });
    sleep_for(20);
    t1.request_interrupt();
    t1.join();
}

static __thread script_state * g_state = nullptr;

static void tst7() {
    std::cout << "start\n";
    system_import("import_test.lua");
    system_dostring("print('hello'); x = 10;");
    interruptible_thread t1([]() {
            g_state = new script_state();
            g_state->dostring("x = 1");
            script_state S = get_thread_script_state();
            S.dostring("print(x)\n"
                       "for i = 1, 100000 do\n"
                       "  x = x + 1\n"
                       "end\n"
                       "print(x)\n");
            delete g_state;
        });
    interruptible_thread t2([]() {
            g_state = new script_state();
            g_state->dostring("x = 0");
            script_state S = get_thread_script_state();
            S.dostring("print(x)\n"
                       "for i = 1, 20000 do\n"
                       "  x = x + 1\n"
                       "end\n"
                       "print(x)\n");
            delete g_state;
        });
    t1.join(); t2.join();
    std::cout << "done\n";
}

static void tst8() {
    std::cout << "starting tst8\n";
    interruptible_thread t1([]() {
            script_state S = get_thread_script_state();
            S.dostring("print(x)\n"
                       "for i = 1, 10000 do\n"
                       "  x = x + 1\n"
                       "end\n"
                       "print(x)\n"
                       "print(fact(10))\n");
        });
    t1.join();
}

int main() {
    save_stack_info();
    initialize_util_module();
    tst1();
    tst2();
    tst3();
    tst4();
    tst5();
    tst6();
    tst7();
    tst8();
    run_thread_finalizers();
    finalize_util_module();
    run_post_thread_finalizers();
    return has_violations() ? 1 : 0;
}
#else
int main() { std::cout << "foo\n"; return 0; }
#endif
