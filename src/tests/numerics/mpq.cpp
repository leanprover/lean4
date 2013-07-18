/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved. 
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura 
*/
#include <iostream>
#include "test.h"
#include "mpq.h"

int main() {
    lean::abort_on_violation(true);
    lean_assert(false);
    std::cout << "PASSED\n";
    return 0;
}
