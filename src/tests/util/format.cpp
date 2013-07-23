/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Soonho Kong
*/
#include "format.h"
#include "test.h"

using namespace lean;

static void tst1() {
    format f_atom1("foo");
    format f_atom2("bar");
    format f_atom3(1);
    format f_atom4(3.1415);
    format f1(f_atom1, f_atom2);
    format f2(f1);
    format f3 = choice(f1, f2);
    format f4 = nest(3, f3);
    format f5 = line();
    format f6(f4, f5);
    format f7(f6, f3);

    std::cout << "f_atom1 = " << f_atom1 << std::endl
              << "f_atom2 = " << f_atom2 << std::endl
              << "f_atom3 = " << f_atom3 << std::endl
              << "f_atom4 = " << f_atom4 << std::endl
        ;

    std::cout << "f1 = " << f1 << std::endl
              << "f2 = " << f2 << std::endl
              << "f3 = " << f3 << std::endl
              << "f4 = " << f4 << std::endl
              << "f5 = " << f5 << std::endl
              << "f6 = " << f6 << std::endl
              << "f7 = " << f7 << std::endl
        ;
}

int main() {
    continue_on_violation(true);
    tst1();
    return has_violations() ? 1 : 0;
}
