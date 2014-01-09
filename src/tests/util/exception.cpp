/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/test.h"
#include "util/exception.h"
#include "util/sstream.h"
using namespace lean;

static void tst1() {
    try {
        throw exception(std::string("foo"));
    } catch (exception & ex) {
        lean_assert(std::string("foo") == ex.what());
    }
}

static void tst2() {
    try {
        throw parser_exception(std::string("foo"), "[string]", 10, 100);
    } catch (parser_exception & ex) {
        lean_assert(std::string("[string]:10:100: error: foo") == ex.what());
    }
}

static void tst3() {
    try {
        throw parser_exception(sstream() << "msg " << 10 << " " << 20, "[stream]", 10, 100);
    } catch (parser_exception & ex) {
        lean_assert(std::string("[stream]:10:100: error: msg 10 20") == ex.what());
    }
}

static void tst4() {
    try {
        throw interrupted();
    } catch (exception & ex) {
        lean_assert(std::string("interrupted") == ex.what());
    }
}

int main() {
    tst1();
    tst2();
    tst3();
    tst4();
    return has_violations() ? 1 : 0;
}
