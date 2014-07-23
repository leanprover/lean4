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
    s.for_each_expr([&](name const & n, expr const & v, justification const & j) {
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
    expr m1 = mk_metavar("m1", Prop);
    lean_assert(!subst.is_assigned(m1));
    expr m2 = mk_metavar("m2", Prop);
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
    expr m1 = mk_metavar("m1", Prop);
    expr m2 = mk_metavar("m2", Prop);
    expr m3 = mk_metavar("m3", Prop);
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
    lean_assert(check_assumptions(s.get_assignment(m1)->second, {1, 2}));
    lean_assert(p1.first == g(f(g(a))));
}

static void tst3() {
    expr m1 = mk_metavar("m1", Prop >> (Prop >> Prop));
    substitution s;
    expr f  = Const("f");
    expr g  = Const("g");
    expr a  = Const("a");
    expr b  = Const("b");
    expr x  = Local("x", Prop);
    expr y  = Local("y", Prop);
    s.assign(m1, Fun({x, y}, f(y, x)));
    lean_assert_eq(s.instantiate_metavars(m1(a, b, g(a))).first, f(b, a, g(a)));
    lean_assert_eq(s.instantiate_metavars(m1(a)).first, Fun(y, f(y, a)));
    lean_assert_eq(s.instantiate_metavars(m1(a, b)).first, f(b, a));
    std::cout << s.instantiate_metavars(m1(a, b, g(a))).first << "\n";
}

static void tst4() {
    expr m1  = mk_metavar("m1", Prop);
    expr m2  = mk_metavar("m2", Prop);
    expr m3  = mk_metavar("m3", Prop);
    level l1 = mk_meta_univ("l1");
    level u  = mk_global_univ("u");
    substitution s;
    expr f  = Const("f");
    expr g  = Const("g");
    expr a  = Const("a");
    expr T1 = mk_sort(l1);
    expr T2 = mk_sort(u);
    expr t  = f(T1, T2, m1, m2);
    lean_assert(s.instantiate_metavars(t).first == t);
    s.assign(m1, a, justification());
    s.assign(m2, m3, justification());
    lean_assert(s.instantiate_metavars(t).first == f(T1, T2, a, m3));
    s.assign(l1, level(), justification());
    lean_assert(s.instantiate_metavars(t).first == f(Prop, T2, a, m3));
}

int main() {
    save_stack_info();
    tst1();
    tst2();
    tst3();
    tst4();
    return has_violations() ? 1 : 0;
}
