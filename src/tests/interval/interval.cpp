/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved. 
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura 
*/
#include "interval_def.h"
#include "test.h"
#include "mpq.h"
using namespace lean;

void tst1() {
    interval<mpq> t(1, 3);
    std::cout << t + interval<mpq>(2, 4, false, true) << "\n";
}

int main() {
    continue_on_violation(true);
    tst1();
    return 0;
}
