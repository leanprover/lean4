#include <iostream>
#include <thread>
#include "version.h"
#include "name.h"
#include "mpq.h"
#include "mpbq.h"

void tst1() {
    lean::name n1("foo");
    lean::name n2(n1, 1);
    std::cout << n2 << "\n";
}

void tst2() {
    lean::mpq n1("10000000000000000000000000000000000000000");
    lean::mpq n2(317, 511);
    std::cout << n1*n2 << "\n";
}

void tst3() {
    std::cout << "Binary rationals...\n";
    lean::mpbq n1(12, 3);
    std::cout << n1 << "\n";
    lean::mpbq n2(2);
    lean_assert(n1 < n2);

    std::thread t1([](){
            for (unsigned i = 0; i < 10000000; i++) {
                lean::mpbq n1(13, 3);
                lean::mpbq n2(2);
                lean_assert(n1 < n2);
            }});

    std::thread t2([](){
            for (unsigned i = 0; i < 10000000; i++) {
                lean::mpbq n1(500000001,3);
                lean::mpbq n2(20000000);
                lean_assert(n2 < n1);
            }});

    std::thread t3([](){
            for (unsigned i = 0; i < 10000000; i++) {
                lean::mpbq n1(1200001, 6);
                lean::mpbq n2(22221, 7);
                lean_assert(n1 > n2);
            }});

    t1.join();
    t2.join();
    t3.join();
}

void tst4() {
    for (unsigned i = 0; i < 10000000; i++) {
        lean::mpbq n1(1200001, 6);
        lean::mpbq n2(22221, 7);
        lean_assert(n1 > n2);
    }
}

void tst5() {
    lean::mpbq n(7,4);
    std::cout << lean::mpbq::decimal(n) << "\n";
    lean::mpq r(4, 3);
    std::cout << lean::mpq::decimal(r) << "\n";
}

int main() {
    std::cout << "Lean (version " << LEAN_VERSION_MAJOR << "." << LEAN_VERSION_MINOR << ")\n";
    tst1();
    tst2();
    tst5();
    std::cout << "done\n";
    return 0;
}
