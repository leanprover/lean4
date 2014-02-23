/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <algorithm>
#include <vector>
#include <utility>
#include <set>
#include "util/test.h"
#include "util/buffer.h"
#include "kernel/metavar.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
using namespace lean;

void collect_assumptions(justification const & j, buffer<unsigned> & r) {
    std::set<unsigned> already_found;
    buffer<justification> todo;
    todo.push_back(j);
    while (!todo.empty()) {
        justification j = todo.back();
        todo.pop_back();
        if (j.is_assumption()) {
            unsigned idx = assumption_idx(j);
            if (already_found.find(idx) == already_found.end()) {
                already_found.insert(idx);
                r.push_back(idx);
            }
        } else if (j.is_composite()) {
            todo.push_back(composite_child1(j));
            todo.push_back(composite_child2(j));
        }
    }
}

void display_assumptions(std::ostream & out, justification const & j) {
    buffer<unsigned> ids;
    collect_assumptions(j, ids);
    for (unsigned i = 0; i < ids.size(); i++) {
        if (i > 0) out << " ";
        out << ids[i];
    }
}

static std::ostream & operator<<(std::ostream & out, substitution const & s) {
    bool first = true;
    s.for_each([&](name const & n, expr const & v, justification const & j) {
            if (first) first = false; else out << "\n";
            out << "?" << n << " <- " << v << " {";
            display_assumptions(out, j);
            out << "}";
        });
    return out;
}

static bool check_assumptions(justification const & j, std::initializer_list<unsigned> const & ls) {
    buffer<unsigned> ids;
    collect_assumptions(j, ids);
    lean_assert(ids.size() == ls.size());
    for (unsigned id : ls) {
        lean_assert(std::find(ids.begin(), ids.end(), id) != ids.end());
    }
    return true;
}

static void tst1() {
    substitution subst;
    expr m1 = mk_metavar("m1", Bool);
    lean_assert(!subst.is_assigned(m1));
    expr m2 = mk_metavar("m2", Bool);
    lean_assert(!is_eqp(m1, m2));
    lean_assert(m1 != m2);
    expr f = Const("f");
    expr a = Const("a");
    subst.assign(m1, f(a));
    lean_assert(subst.is_assigned(m1));
    lean_assert(!subst.is_assigned(m2));
    lean_assert(*subst.get_expr(m1) == f(a));
    lean_assert(subst.instantiate_metavars(f(m1)).first == f(f(a)));
    std::cout << subst << "\n";
}

static void tst2() {
    substitution s;
    expr m1 = mk_metavar("m1", Bool);
    expr m2 = mk_metavar("m2", Bool);
    expr m3 = mk_metavar("m3", Bool);
    expr f = Const("f");
    expr g = Const("g");
    expr a = Const("a");
    s.assign(m1, f(m2), mk_assumption_justification(1));
    s.assign(m2, g(a),  mk_assumption_justification(2));
    lean_assert(check_assumptions(s.get_assignment(m1)->second, {1}));
    lean_assert(s.occurs(m1, f(m1)));
    lean_assert(s.occurs(m2, f(m1)));
    lean_assert(!s.occurs(m1, f(m2)));
    lean_assert(!s.occurs(m1, f(a)));
    lean_assert(!s.occurs(m3, f(m1)));
    std::cout << s << "\n";
    auto p1 = s.instantiate_metavars(g(m1));
    check_assumptions(p1.second, {1, 2});
    lean_assert(check_assumptions(s.get_assignment(m1)->second, {1}));
    lean_assert(p1.first == g(f(g(a))));
    auto p2 = s.d_instantiate_metavars(g(m1, m3));
    check_assumptions(p2.second, {1, 2});
    std::cout << p2.first << "\n";
    std::cout << s << "\n";
    lean_assert(check_assumptions(s.get_assignment(m1)->second, {1, 2}));
    lean_assert(p2.first == g(f(g(a)), m3));
    s.assign(m3, f(m1, m2), mk_assumption_justification(3));
    auto p3 = s.instantiate_metavars(g(m1, m3));
    lean_assert(check_assumptions(p3.second, {1, 2, 3}));
    std::cout << p3.first << "\n";
    std::cout << p3.second << "\n";
    std::cout << s << "\n";
    lean_assert_eq(p3.first, g(f(g(a)), f(f(g(a)), g(a))));
}

static void tst3() {
    expr m1 = mk_metavar("m1", Bool >> (Bool >> Bool));
    substitution s;
    expr f  = Const("f");
    expr g  = Const("g");
    expr x  = Const("x");
    expr y  = Const("y");
    expr a  = Const("a");
    expr b  = Const("b");
    s.assign(m1, Fun({{x, Bool}, {y, Bool}}, f(y, x)));
    lean_assert_eq(s.instantiate_metavars(m1(a, b, g(a))).first, f(b, a, g(a)));
    lean_assert_eq(s.instantiate_metavars(m1(a)).first, Fun({y, Bool}, f(y, a)));
    lean_assert_eq(s.instantiate_metavars(m1(a, b)).first, f(b, a));
    std::cout << s.instantiate_metavars(m1(a, b, g(a))).first << "\n";
}

int main() {
    save_stack_info();
    tst1();
    tst2();
    tst3();
    return has_violations() ? 1 : 0;
}
