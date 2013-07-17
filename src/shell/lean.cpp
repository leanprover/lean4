#include <iostream>
#include "version.h"
#include "name.h"
#include "mpq.h"

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

int main() {
    std::cout << "Lean (version " << LEAN_VERSION_MAJOR << "." << LEAN_VERSION_MINOR << ")\n";
    tst1();
    tst2();
    return 0;
}
