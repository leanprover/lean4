/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "environment.h"
#include "type_check.h"
#include "builtin.h"
#include "arith.h"
#include "normalize.h"
#include "abstract.h"
#include "exception.h"
#include "test.h"
using namespace lean;

static void tst1() {
    environment env;
    level u = env.define_uvar("u", level() + 1);
    level w = env.define_uvar("w", u + 1);
    lean_assert(!env.has_children());
    lean_assert(!env.has_parent());
    {
        environment child = env.mk_child();
        lean_assert(child.is_ge(w, u));
        lean_assert(child.is_ge(w, level() + 2));
        lean_assert(env.is_ge(w, level() + 2));
        lean_assert(env.has_children());
        lean_assert(child.has_parent());
        lean_assert(!env.has_parent());
        try {
            level o = env.define_uvar("o", w + 1);
            lean_unreachable();
        } catch (exception const & ex) {
            std::cout << "expected error: " << ex.what() << "\n";
        }
    }
    std::cout << "tst1 checkpoint" << std::endl;
    level o = env.define_uvar("o", w + 1);
    lean_assert(!env.has_children());
    env.display_uvars(std::cout);
}

static environment mk_child() {
    environment env;
    level u = env.define_uvar("u", level() + 1);
    return env.mk_child();
}

static void tst2() {
    environment child = mk_child();
    lean_assert(child.has_parent());
    lean_assert(!child.has_children());
    environment parent = child.parent();
    parent.display_uvars(std::cout);
    lean_assert(parent.has_children());
    std::cout << "uvar: " << child.get_uvar("u") << "\n";
}

static void tst3() {
    environment env;
    try {
        env.add_definition("a", int_type(), constant("a"));
        lean_unreachable();
    } catch (exception ex) {
        std::cout << "expected error: " << ex.what() << "\n";
    }
    env.add_definition("a", int_type(), app(int_add(), int_value(1), int_value(2)));
    expr t = app(int_add(), constant("a"), int_value(1));
    std::cout << t << " --> " << normalize(t, env) << "\n";
    lean_assert(normalize(t, env) == int_value(4));
    env.add_definition("b", int_type(), app(int_mul(), int_value(2), constant("a")));
    std::cout << "b --> " << normalize(constant("b"), env) << "\n";
    lean_assert(normalize(constant("b"), env) == int_value(6));
    try {
        env.add_definition("c", arrow(int_type(), int_type()), constant("a"));
        lean_unreachable();
    } catch (exception ex) {
        std::cout << "expected error: " << ex.what() << "\n";
    }
    try {
        env.add_definition("a", int_type(), int_value(10));
        lean_unreachable();
    } catch (exception ex) {
        std::cout << "expected error: " << ex.what() << "\n";
    }
    environment c_env = env.mk_child();
    try {
        env.add_definition("c", int_type(), constant("a"));
        lean_unreachable();
    } catch (exception ex) {
        std::cout << "expected error: " << ex.what() << "\n";
    }
    lean_assert(normalize(constant("b"), env) == int_value(6));
    lean_assert(normalize(constant("b"), c_env) == int_value(6));
    c_env.add_definition("c", int_type(), constant("a"));
    lean_assert(normalize(constant("c"), c_env) == int_value(3));
    try {
        lean_assert(normalize(constant("c"), env) == int_value(3));
        lean_unreachable();
    } catch (exception ex) {
        std::cout << "expected error: " << ex.what() << "\n";
    }
}

int main() {
    continue_on_violation(true);
    tst1();
    tst2();
    tst3();
    return has_violations() ? 1 : 0;
}
