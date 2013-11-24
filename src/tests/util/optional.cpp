/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <string>
#include "util/test.h"
#include "util/optional.h"
using namespace lean;

struct point {
    std::string m_msg;
    int m_x;
    int m_y;
    point(char const * msg, int x, int y):m_msg(msg), m_x(x), m_y(y) {}
    point(point const & p):m_msg(p.m_msg), m_x(p.m_x), m_y(p.m_y) {}
    point(point && p):m_msg(std::move(p.m_msg)), m_x(p.m_x), m_y(p.m_y) {}
    ~point() { std::cout << "destructed... " << m_msg << " " << m_x << " " << m_y << "\n"; }
};

static void tst1() {
    optional<int> i;
    lean_assert(!i);
    i = 10;
    lean_assert(i);
    lean_assert(*i == 10);
}

static void tst2() {
    optional<point> p1;
    lean_assert(!p1);
    optional<point> p2("p2", 10, 20);
    lean_assert(p2->m_x == 10);
    p2 = point("p3", 20, 30);
    lean_assert(p2->m_y == 30);
    lean_assert((*p2).m_x == 20);
    p1 = p2;
    lean_assert(p1);
    lean_assert(p1.value().m_x == 20);
    p1.emplace("p4", 2, 3);
}

int main() {
    tst1();
    tst2();
    return has_violations() ? 1 : 0;
}
