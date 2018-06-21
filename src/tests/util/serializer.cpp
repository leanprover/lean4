/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <sstream>
#include <string>
#include <cstring>
#include <vector>
#include <functional>
#include <cmath>
#include "runtime/debug.h"
#include "util/test.h"
#include "util/list.h"
#include "util/name.h"
#include "util/init_module.h"
using namespace lean;

void display(std::ostringstream const & out) {
    std::cout << "OUT: ";
    auto str = out.str();
    for (auto c : str) {
        std::cout << static_cast<int>(static_cast<unsigned char>(c)) << " ";
    }
    std::cout << "\n";
}

static void tst1() {
    std::ostringstream out;
    serializer s(out);
    s.write_int(10); s.write_int(-20); s.write_bool(false); s.write_string("hello"); s.write_int(30);
    display(out);
    std::istringstream in(out.str());
    deserializer d(in);
    lean_assert(d.read_int() == 10);
    lean_assert(d.read_int() == -20);
    lean_assert(!d.read_bool());
    lean_assert(d.read_string() == "hello");
    lean_assert(d.read_int() == 30);
}

static void tst2() {
}

static void tst3() {
    std::ostringstream out;
    serializer s(out);
    name n1{"foo", "bla"};
    name n2(n1, 10);
    name n3(n2, "tst");
    name n4(n1, "hello");
    name n5("simple");
    s << n1 << n2 << n3 << n4 << n2 << n5;
    display(out);
    std::istringstream in(out.str());
    deserializer d(in);
    name m1, m2, m3, m4, m5, m6;
    d >> m1 >> m2 >> m3 >> m4 >> m5 >> m6;
    lean_assert(n1 == m1);
    lean_assert(n2 == m2);
    lean_assert(n3 == m3);
    lean_assert(n4 == m4);
    lean_assert(n2 == m5);
    lean_assert(n5 == m6);
}

static void tst4() {
    std::ostringstream out;
    serializer s(out);
    double d1, d2, d3, d4, d5;
    d1 = 0.1;
    d2 = -0.3;
    d3 = 0.0;
    d4 = 12317.123;
    d5 = std::atan(1.0)*4;
    s << d1 << d2 << d3 << d4 << d5;
    std::istringstream in(out.str());
    deserializer d(in);
    double o1, o2, o3, o4, o5;
    d >> o1 >> o2 >> o3 >> o4 >> o5;
    lean_assert_eq(d1, o1);
    lean_assert_eq(d2, o2);
    lean_assert_eq(d3, o3);
    lean_assert_eq(d4, o4);
    lean_assert_eq(d5, o5);
}

int main() {
    save_stack_info();
    initialize_util_module();
    tst1();
    tst2();
    tst3();
    tst4();
    finalize_util_module();
    return has_violations() ? 1 : 0;
}
