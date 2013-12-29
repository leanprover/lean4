/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/test.h"
#include "util/exception.h"
#include "util/trace.h"
#include "kernel/kernel_exception.h"
#include "kernel/environment.h"
#include "kernel/type_checker.h"
#include "kernel/builtin.h"
#include "kernel/normalizer.h"
#include "kernel/abstract.h"
#include "kernel/printer.h"
#include "library/arith/arith.h"
#include "frontends/lean/frontend.h"
using namespace lean;

static void tst1() {
    environment env;
    level u = env->add_uvar("u", level() + 1);
    level w = env->add_uvar("w", u + 1);
    lean_assert(!env->has_children());
    lean_assert(!env->has_parent());
    {
        environment child = env->mk_child();
        lean_assert(child->is_ge(w, u));
        lean_assert(child->is_ge(w, level() + 2));
        lean_assert(env->is_ge(w, level() + 2));
        lean_assert(env->has_children());
        lean_assert(child->has_parent());
        lean_assert(!env->has_parent());
        try {
            level o = env->add_uvar("o", w + 1);
            lean_unreachable();
        } catch (exception const & ex) {
            std::cout << "expected error: " << ex.what() << "\n";
        }
    }
    std::cout << "tst1 checkpoint" << std::endl;
    level o = env->add_uvar("o", w + 1);
    lean_assert(!env->has_children());
    std::cout << env;
}

static environment mk_child() {
    environment env;
    level u = env->add_uvar("u", level() + 1);
    return env->mk_child();
}

static void tst2() {
    environment child = mk_child();
    lean_assert(child->has_parent());
    lean_assert(!child->has_children());
    environment parent = child->parent();
    std::cout << parent;
    lean_assert(parent->has_children());
    std::cout << "uvar: " << child->get_uvar("u") << "\n";
}

static void tst3() {
    std::cout << "tst3\n";
    environment env; init_frontend(env);
    try {
        env->add_definition("a", Int, Const("a"));
        lean_unreachable();
    } catch (exception const & ex) {
        std::cout << "expected error: " << ex.what() << "\n";
    }
    env->add_definition("a", Int, iAdd(iVal(1), iVal(2)));
    std::cout << env << "\n";
    expr t = iAdd(Const("a"), iVal(1));
    std::cout << t << " --> " << normalize(t, env) << "\n";
    lean_assert(normalize(t, env) == iVal(4));
    env->add_definition("b", Int, iMul(iVal(2), Const("a")));
    std::cout << "b --> " << normalize(Const("b"), env) << "\n";
    lean_assert(normalize(Const("b"), env) == iVal(6));
    try {
        env->add_definition("c", mk_arrow(Int, Int), Const("a"));
        lean_unreachable();
    } catch (exception const & ex) {
        std::cout << "expected error: " << ex.what() << "\n";
    }
    try {
        env->add_definition("a", Int, iVal(10));
        lean_unreachable();
    } catch (exception const & ex) {
        std::cout << "expected error: " << ex.what() << "\n";
    }
    environment c_env = env->mk_child();
    try {
        env->add_definition("c", Int, Const("a"));
        lean_unreachable();
    } catch (exception const & ex) {
        std::cout << "expected error: " << ex.what() << "\n";
    }
    lean_assert(normalize(Const("b"), env) == iVal(6));
    lean_assert(normalize(Const("b"), c_env) == iVal(6));
    c_env->add_definition("c", Int, Const("a"));
    lean_assert(normalize(Const("c"), c_env) == iVal(3));
    expr r = normalize(Const("c"), env);
    lean_assert(r == Const("c"));
    std::cout << "end tst3" << std::endl;
}

static void tst4() {
    std::cout << "tst4\n";
    environment env; init_frontend(env);
    env->add_definition("a", Int, iVal(1), true); // add opaque definition
    expr t = iAdd(Const("a"), iVal(1));
    std::cout << t << " --> " << normalize(t, env) << "\n";
    lean_assert(normalize(t, env) == t);
    env->add_definition("b", Int, iAdd(Const("a"), iVal(1)));
    expr t2 = iSub(Const("b"), iVal(9));
    std::cout << t2 << " --> " << normalize(t2, env) << "\n";
    lean_assert_eq(normalize(t2, env, context()),
                   iSub(iAdd(Const("a"), iVal(1)), iVal(9)));
}

static void tst5() {
    environment env; init_frontend(env);
    env->add_definition("a", Int, iVal(1), true); // add opaque definition
    try {
        std::cout << type_check(iAdd(Const("a"), Int), env) << "\n";
        lean_unreachable();
    } catch (exception const & ex) {
        std::cout << "expected error: " << ex.what() << "\n";
    }
}

static void tst6() {
    environment env; init_frontend(env);
    level u = env->add_uvar("u", level() + 1);
    level w = env->add_uvar("w", u + 1);
    env->add_var("f", mk_arrow(Type(u), Type(u)));
    expr t = Const("f")(Int);
    std::cout << "type of " << t << " is " << type_check(t, env) << "\n";
    try {
        type_check(Const("f")(Type(w)), env);
        lean_unreachable();
    } catch (exception const & ex) {
        std::cout << "expected error: " << ex.what() << "\n";
    }
    try {
        type_check(Const("f")(Type(u)), env);
        lean_unreachable();
    } catch (exception const & ex) {
        std::cout << "expected error: " << ex.what() << "\n";
    }
    t = Const("f")(Type());
    std::cout << "type of " << t << " is " << type_check(t, env) << "\n";
    std::cout << type_check(mk_arrow(Type(u), Type(w)), env) << "\n";
    lean_assert(type_check(mk_arrow(Type(u), Type(w)), env) == Type(max(u+1, w+1)));
    std::cout << type_check(mk_arrow(Int, Int), env) << "\n";
    lean_assert(type_check(mk_arrow(Int, Int), env) == Type());
}

static void tst7() {
    environment env; init_frontend(env);
    env->add_var("a", Int);
    env->add_var("b", Int);
    expr t = If(Int, True, Const("a"), Const("b"));
    std::cout << t << " --> " << normalize(t, env) << "\n";
    std::cout << type_check(t, env) << "\n";
    std::cout << "Environment\n" << env;
}

static void tst8() {
    environment env;
    std::cout << "=======================\n";
    env->add_var("a", Type());
    env->add_var("b", Type());
    environment env2 = env->mk_child();
    env2->add_var("c", Type());
    env2->add_var("d", Type());
    env2->add_var("e", Type());
    unsigned counter = 0;
    std::for_each(env2->begin_local_objects(), env2->end_local_objects(), [&](object const & obj) { std::cout << obj.keyword() << " " << obj.get_name() << "\n"; counter++; });
    lean_assert(counter == 3);
    std::cout << "=======================\n";
    counter = 0;
    std::for_each(env2->begin_objects(), env2->end_objects(), [&](object const & obj) { std::cout << obj.keyword() << " " << obj.get_name() << "\n"; counter++; });
    lean_assert(counter == 5);
    environment env3 = env2->mk_child();
    env3->add_var("f", Type() >> Type());
    std::cout << "=======================\n";
    counter = 0;
    std::for_each(env3->begin_objects(), env3->end_objects(), [&](object const & obj) { std::cout << obj.keyword() << " " << obj.get_name() << "\n"; counter++; });
    lean_assert(counter == 6);
}

static void tst9() {
    try {
        environment env;
        env->add_uvar("u1", level());
        env->add_uvar("u2", level());
        env->add_uvar("u1", level("u2"));
    } catch (already_declared_exception & ex) {
        std::cout << ex.what() << "\n";
        level l = ex.get_environment()->get_uvar(ex.get_name());
        std::cout << l << "\n";
    }
}

static void tst10() {
    environment env;
    init_frontend(env);
    env->add_definition("a", Int, iVal(1));
    lean_assert(env->get_object("a").get_weight() == 1);
    expr a = Const("a");
    expr b = Const("b");
    expr c = Const("c");
    env->add_definition("b", Int, iAdd(a, a));
    lean_assert(env->get_object("b").get_weight() == 2);
    env->add_definition("c", Int, iAdd(a, b));
    lean_assert(env->get_object("c").get_weight() == 3);
    env->add_definition("d", Int, iAdd(b, b));
    lean_assert(env->get_object("d").get_weight() == 3);
}

struct my_extension : public environment_extension {
    unsigned m_value1;
    unsigned m_value2;
    my_extension():m_value1(0), m_value2(0) {}
};

struct my_extension_reg {
    unsigned m_extid;
    my_extension_reg() {
        m_extid = environment_cell::register_extension([](){ return std::unique_ptr<environment_extension>(new my_extension()); });
    }
};

static my_extension_reg R;

static void tst11() {
    unsigned extid = R.m_extid;
    environment env;
    my_extension & ext  = env->get_extension<my_extension>(extid);
    ext.m_value1 = 10;
    ext.m_value2 = 20;
    my_extension & ext2 = env->get_extension<my_extension>(extid);
    lean_assert(ext2.m_value1 == 10);
    lean_assert(ext2.m_value2 == 20);
    environment child = env->mk_child();
    my_extension & ext3 = child->get_extension<my_extension>(extid);
    lean_assert(ext3.m_value1 == 0);
    lean_assert(ext3.m_value2 == 0);
    my_extension const * ext4 = ext3.get_parent<my_extension>();
    lean_assert(ext4);
    lean_assert(ext4->m_value1 == 10);
    lean_assert(ext4->m_value2 == 20);
    lean_assert(ext4->get_parent<my_extension>() == nullptr);
}

static void tst12() {
    unsigned extid = R.m_extid;
    environment env;
    environment child = env->mk_child();
    my_extension & ext = child->get_extension<my_extension>(extid);
    lean_assert(ext.m_value1 == 0);
    lean_assert(ext.m_value2 == 0);
    lean_assert(ext.get_parent<my_extension>() == nullptr);
}

static void tst13() {
    ro_environment::weak_ref wref;
    {
        environment env;
        ro_environment roenv(env);
        wref = roenv.to_weak_ref();
    }
    try {
        ro_environment env2(wref);
        lean_unreachable();
    } catch (exception &) {}
}

int main() {
    save_stack_info();
    enable_trace("is_convertible");
    tst1();
    tst2();
    tst3();
    tst4();
    tst5();
    tst6();
    tst7();
    tst8();
    tst9();
    tst10();
    tst11();
    tst12();
    tst13();
    return has_violations() ? 1 : 0;
}
