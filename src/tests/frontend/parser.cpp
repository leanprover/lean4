/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <sstream>
#include "parser.h"
#include "pp.h"
#include "printer.h"
#include "test.h"
using namespace lean;

static void parse(frontend & fe, char const * msg) {
    frontend child = fe.mk_child();
    std::istringstream in(msg);
    if (parse_commands(child, in)) {
        formatter fmt = mk_pp_formatter(child);
        std::for_each(child.begin_local_objects(),
                      child.end_local_objects(),
                      [&](object const & obj) {
                          std::cout << fmt(obj) << "\n";
                          std::cout << obj << "\n";
                      });
    }
}

static void tst1() {
    frontend fe;
    parse(fe,
"Variable x : Bool Variable y : Bool Axiom H : x && y || x => x");
}

int main() {
    tst1();
    return has_violations() ? 1 : 0;
}
