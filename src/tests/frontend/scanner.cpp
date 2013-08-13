/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <sstream>
#include "scanner.h"
#include "test.h"
using namespace lean;

static void tst1() {
    char tst[] = "fun(x: pi A : Type, A -> A), (* (* test *) *) x+1 = 2.0 λ";
    std::istringstream in(tst);
    scanner s(in);
    while (true) {
        scanner::token t = s.scan();
        if (t == scanner::token::Eof)
            break;
        std::cout << t << " ";
    }
    std::cout << "\n";
}

int main() {
    continue_on_violation(true);
    tst1();
    return has_violations() ? 1 : 0;
}
