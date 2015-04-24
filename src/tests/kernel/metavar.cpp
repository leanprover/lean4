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
#include "util/init_module.h"
#include "util/sexpr/init_module.h"
#include "kernel/metavar.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/init_module.h"
#include "library/init_module.h"
#include "library/print.h"
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
        } else if (j.is_wrapper()) {
            todo.push_back(wrapper_child(j));
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
    expr Prop = mk_Prop();
    expr m1 = mk_metavar("m1", Prop);
    lean_assert(!subst.is_assigned(m1));
    expr m2 = mk_metavar("m2", Prop);
    lean_assert(!is_eqp(m1, m2));
    lean_assert(m1 != m2);
    expr f = Const("f");
    expr a = Const("a");
    subst.assign(m1, mk_app(f, a));
    lean_assert(subst.is_assigned(m1));
    lean_assert(!subst.is_assigned(m2));
    lean_assert(*subst.get_expr(m1) == mk_app(f, a));
    lean_assert(subst.instantiate_metavars(mk_app(f, m1)).first == mk_app(f, mk_app(f, a)));
    std::cout << subst << "\n";
}

static void tst2() {
    substitution s;
    expr Prop = mk_Prop();
    expr m1 = mk_metavar("m1", Prop);
    expr m2 = mk_metavar("m2", Prop);
    expr m3 = mk_metavar("m3", Prop);
    expr f = Const("f");
    expr g = Const("g");
    expr a = Const("a");
    s.assign(m1, mk_app(f, m2), mk_assumption_justification(1));
    lean_assert(check_assumptions(s.get_assignment(m1)->second, {1}));
    lean_assert(!s.occurs(m1, mk_app(f, m1)));
    lean_assert(s.occurs(m2, mk_app(f, m1)));
    s.assign(m2, mk_app(g, a),  mk_assumption_justification(2));
    lean_assert(!s.occurs(m2, mk_app(f, m1)));
    lean_assert(!s.occurs(m1, mk_app(f, m2)));
    lean_assert(!s.occurs(m1, mk_app(f, a)));
    lean_assert(!s.occurs(m3, mk_app(f, m1)));
    std::cout << s << "\n";
    auto p1 = s.instantiate_metavars(mk_app(g, m1));
    check_assumptions(p1.second, {1, 2});
    lean_assert(check_assumptions(s.get_assignment(m1)->second, {1, 2}));
    lean_assert(p1.first == mk_app(g, mk_app(f, mk_app(g, a))));
}

static void tst3() {
    expr Prop = mk_Prop();
    expr m1 = mk_metavar("m1", Prop >> (Prop >> Prop));
    substitution s;
    expr f  = Const("f");
    expr g  = Const("g");
    expr a  = Const("a");
    expr b  = Const("b");
    expr x  = Local("x", Prop);
    expr y  = Local("y", Prop);
    s.assign(m1, Fun({x, y}, mk_app(f, y, x)));
    lean_assert_eq(s.instantiate_metavars(mk_app(m1, a, b, mk_app(g, a))).first, mk_app(f, b, a, mk_app(g, a)));
    lean_assert_eq(s.instantiate_metavars(mk_app(m1, a)).first, Fun(y, mk_app(f, y, a)));
    lean_assert_eq(s.instantiate_metavars(mk_app(m1, a, b)).first, mk_app(f, b, a));
    std::cout << s.instantiate_metavars(mk_app(m1, a, b, mk_app(g, a))).first << "\n";
}

static void tst4() {
    expr Prop = mk_Prop();
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
    expr t  = mk_app(f, T1, T2, m1, m2);
    lean_assert(s.instantiate_metavars(t).first == t);
    s.assign(m1, a, justification());
    s.assign(m2, m3, justification());
    lean_assert(s.instantiate_metavars(t).first == mk_app(f, T1, T2, a, m3));
    s.assign(l1, level(), justification());
    lean_assert(s.instantiate_metavars(t).first == mk_app(f, Prop, T2, a, m3));
}

int main() {
    save_stack_info();
    initialize_util_module();
    initialize_sexpr_module();
    initialize_kernel_module();
    initialize_library_module();
    init_default_print_fn();
    tst1();
    tst2();
    tst3();
    tst4();
    finalize_library_module();
    finalize_kernel_module();
    finalize_sexpr_module();
    finalize_util_module();
    return has_violations() ? 1 : 0;
}
