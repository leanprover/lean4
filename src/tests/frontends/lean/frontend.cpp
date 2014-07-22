/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include "util/test.h"
#include "kernel/environment.h"
#include "kernel/kernel_exception.h"
#include "kernel/kernel.h"
#include "kernel/abstract.h"
#include "library/printer.h"
#include "library/bin_op.h"
#include "library/io_state_stream.h"
#include "frontends/lean/frontend.h"
#include "frontends/lean/operator_info.h"
#include "frontends/lean/pp.h"
#include "frontends/lua/register_modules.h"
using namespace lean;

static void tst1() {
    environment env; io_state ios = init_frontend(env);
    env->add_uvar_cnstr("tst");
    environment c = env->mk_child();
    lean_assert(c->get_uvar("tst") == env->get_uvar("tst"));
    lean_assert(env->has_children());
}

static void tst2() {
    operator_info op1 = infixl(name("and"), 10);
    operator_info op2 = infixr(name("implies"), 20);
    lean_assert(op1.get_precedence() == 10);
    lean_assert(op1.get_fixity() == fixity::Infixl);
    op1.add_expr(mk_and_fn());
    operator_info op3 = infixl(name("+"), 10);
    op3.add_expr(Const(name{"Int", "plus"}));
    op3.add_expr(Const(name{"Real", "plus"}));
    std::cout << op3.get_denotations() << "\n";
    lean_assert(length(op3.get_denotations()) == 2);
    operator_info op4 = op3.copy();
    op4.add_expr(Const(name{"Complex", "plus"}));
    std::cout << op4.get_denotations() << "\n";
    lean_assert(length(op3.get_denotations()) == 2);
    lean_assert(length(op4.get_denotations()) == 3);
    lean_assert(op4.get_fixity() == fixity::Infixl);
    lean_assert(op4.get_op_name() == op3.get_op_name());
    lean_assert(prefix("tst", 20).get_fixity() == fixity::Prefix);
    lean_assert(postfix("!", 20).get_fixity() == fixity::Postfix);
    lean_assert(length(mixfixl({"if", "then", "else"}, 10).get_op_name_parts()) == 3);
    lean_assert(mixfixc({"if", "then", "else", "endif"}, 10).get_fixity() == fixity::Mixfixc);
    std::cout << mixfixc({"if", "then", "else", "endif"}, 10).get_op_name_parts() << "\n";
    std::cout << op4 << "\n";
    std::cout << op2 << "\n";
    std::cout << mixfixc({"if", "then", "else", "endif"}, 10) << "\n";
}

static void tst3() {
    environment env;
    std::cout << "====================\n";
    std::cout << env << "\n";
}

static void tst4() {
    environment env; io_state ios = init_frontend(env);
    formatter fmt = mk_pp_formatter(env);
    context c;
    c = extend(c, "x", Prop);
    c = extend(c, "y", Prop);
    c = extend(c, "x", Prop, Var(1));
    c = extend(c, "x", Prop, Var(2));
    c = extend(c, "z", Prop, Var(1));
    c = extend(c, "x", Prop, Var(4));
    std::cout << fmt(c) << "\n";
}

static void tst5() {
    std::cout << "=================\n";
    environment env; io_state ios = init_frontend(env);
    formatter fmt = mk_pp_formatter(env);
    env->add_var("A", Type());
    env->add_var("x", Const("A"));
    optional<object> obj = env->find_object("x");
    lean_assert(obj);
    lean_assert(obj->get_name() == "x");
    std::cout << fmt(*obj) << "\n";
    optional<object> obj2 = env->find_object("y");
    lean_assert(!obj2);
    try {
        env->get_object("y");
        lean_unreachable();
    } catch (unknown_name_exception & ex) {
        std::cout << ex.what() << " " << ex.get_name() << "\n";
    }
}

class alien_cell : public neutral_object_cell {
    unsigned m_data[128];
public:
    alien_cell() {}
    unsigned & get_data(unsigned i) { return m_data[i]; }
    virtual char const * keyword() const { return "alien"; }
    virtual void write(serializer & ) const { lean_unreachable(); } // LCOV_EXCL_LINE
};

static void tst6() {
    std::cout << "=================\n";
    environment env; io_state ios = init_frontend(env);
    env->add_neutral_object(new alien_cell());
    formatter fmt = mk_pp_formatter(env);
    std::cout << fmt(env) << "\n";
}

static void tst7() {
    environment env; io_state ios = init_frontend(env);
    formatter fmt = mk_pp_formatter(env);
    std::cout << fmt(And(Const("x"), Const("y"))) << "\n";
}

static void tst8() {
    environment env; io_state ios = init_frontend(env);
    formatter fmt = mk_pp_formatter(env);
    add_infixl(env, ios, "<-$->", 10, mk_refl_fn());
    std::cout << fmt(*(env->find_object("trivial"))) << "\n";
}

static void tst9() {
    environment env; io_state ios = init_frontend(env);
    lean_assert(!env->has_children());
    {
        environment c = env->mk_child();
        lean_assert(env->has_children());
    }
    lean_assert(!env->has_children());
    env->add_uvar_cnstr("l", level()+1);
    lean_assert(env->get_uvar("l") == level("l"));
    try { env->get_uvar("l2"); lean_unreachable(); }
    catch (exception &) {}
    env->add_definition("x", Prop, True);
    object const & obj = env->get_object("x");
    lean_assert(obj.get_name() == "x");
    lean_assert(is_bool(obj.get_type()));
    lean_assert(obj.get_value() == True);
    try { env->get_object("y"); lean_unreachable(); }
    catch (exception &) {}
    lean_assert(!env->find_object("y"));
    env->add_definition("y", False);
    lean_assert(is_bool(env->find_object("y")->get_type()));
    lean_assert(env->has_object("y"));
    lean_assert(!env->has_object("z"));
    bool found = false;
    std::for_each(env->begin_objects(), env->end_objects(), [&](object const & obj) { if (obj.has_name() && obj.get_name() == "y") found = true; });
    lean_assert(found);
    add_postfix(env, ios, "!", 10, Const("factorial"));
    name parts[] = {"if", "then", "else"};
    add_mixfixl(env, ios, 3, parts, 10, Const("if"));
}

static void tst10() {
    environment env; io_state ios = init_frontend(env);
    formatter fmt = mk_pp_formatter(env);
    expr x = Const("xxxxxxxxxxxx");
    expr y = Const("y");
    expr z = Const("foo");
    expr e = Let({{x, True}, {y, And({x, x, x, x, x, x, x, x})}, {z, And(x, y)}}, Or({x, x, x, x, x, x, x, x, x, z, z, z, z, z, z, z}));
    std::cout << e << "\n";
    std::cout << fmt(e) << "\n";
}

static void tst11() {
    environment env; io_state ios = init_frontend(env);
    expr A = Const("A");
    env->add_var("g", Pi({A, Type()}, A >> (A >> A)));
    lean_assert(!has_implicit_arguments(env, "g"));
    mark_implicit_arguments(env, "g", {true, false, false});
    lean_assert(has_implicit_arguments(env, "g"))
        name gexp = get_explicit_version(env, "g");
    lean_assert(env->find_object(gexp));
    lean_assert(env->find_object("g")->get_type() == env->find_object(gexp)->get_type());
    lean_assert(get_implicit_arguments(env, "g") == std::vector<bool>({true})); // the trailing "false" marks are removed
    try {
        mark_implicit_arguments(env, "g", {true, false, false});
        lean_unreachable();
    } catch (exception & ex) {
        std::cout << "Expected error: " << ex.what() << std::endl;
    }
    env->add_var("s", Pi({A, Type()}, A >> (A >> A)));
    try {
        mark_implicit_arguments(env, "s", {true, true, true, true});
        lean_unreachable();
    } catch (exception & ex) {
        std::cout << "Expected error: " << ex.what() << std::endl;
    }
    env->add_var(name("@h"), Pi({A, Type()}, A >> (A >> A)));
    env->add_var("h", Pi({A, Type()}, A >> (A >> A)));
    try {
        mark_implicit_arguments(env, "h", {true, false, false});
        lean_unreachable();
    } catch (exception & ex) {
        std::cout << "Expected error: " << ex.what() << std::endl;
    }
    try {
        mark_implicit_arguments(env, "u", {true, false});
        lean_unreachable();
    } catch (exception & ex) {
        std::cout << "Expected error: " << ex.what() << std::endl;
    }
}

int main() {
    save_stack_info();
    register_modules();
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
    return has_violations() ? 1 : 0;
}
