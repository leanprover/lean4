/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "test.h"
#include "environment.h"
#include "kernel_exception.h"
#include "builtin.h"
#include "printer.h"
#include "abstract.h"
#include "lean_frontend.h"
#include "lean_operator_info.h"
#include "lean_pp.h"
using namespace lean;

static void tst1() {
    frontend f;
    f.add_uvar("tst");
    frontend c = f.mk_child();
    lean_assert(c.get_uvar("tst") == f.get_uvar("tst"));
    lean_assert(f.get_environment().has_children());
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
    std::cout << op3.get_exprs() << "\n";
    lean_assert(length(op3.get_exprs()) == 2);
    operator_info op4 = op3.copy();
    op4.add_expr(Const(name{"Complex", "plus"}));
    std::cout << op4.get_exprs() << "\n";
    lean_assert(length(op3.get_exprs()) == 2);
    lean_assert(length(op4.get_exprs()) == 3);
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
    frontend f;
    std::cout << "====================\n";
    std::cout << f << "\n";
}

static void tst4() {
    frontend f;
    formatter fmt = mk_pp_formatter(f);
    context c;
    c = extend(c, "x", Bool);
    c = extend(c, "y", Bool);
    c = extend(c, "x", Bool, Var(1));
    c = extend(c, "x", Bool, Var(2));
    c = extend(c, "z", Bool, Var(1));
    c = extend(c, "x", Bool, Var(4));
    std::cout << fmt(c) << "\n";
}

static void tst5() {
    std::cout << "=================\n";
    frontend f;
    formatter fmt = mk_pp_formatter(f);
    f.add_var("A", Type());
    f.add_var("x", Const("A"));
    object const & obj = f.find_object("x");
    lean_assert(obj);
    lean_assert(obj.get_name() == "x");
    std::cout << fmt(obj) << "\n";
    object const & obj2 = f.find_object("y");
    lean_assert(!obj2);
    try {
        f.get_object("y");
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
};

static void tst6() {
    std::cout << "=================\n";
    frontend f;
    environment env;
    env.add_neutral_object(new alien_cell());
    formatter fmt = mk_pp_formatter(f);
    std::cout << fmt(env) << "\n";
}

static void tst7() {
    frontend f;
    formatter fmt = mk_pp_formatter(f);
    std::cout << fmt(And(Const("x"), Const("y"))) << "\n";
}

static void tst8() {
    frontend fe;
    formatter fmt = mk_pp_formatter(fe);
    fe.add_infixl("<-$->", 10, mk_refl_fn());
    std::cout << fmt(fe.find_object("Trivial")) << "\n";
}

static void tst9() {
    frontend f;
    lean_assert(!f.has_children());
    {
        frontend c = f.mk_child();
        lean_assert(f.has_children());
        lean_assert(c.parent().has_children());
    }
    lean_assert(!f.has_children());
    f.add_uvar("l", level()+1);
    lean_assert(f.get_uvar("l") == level("l"));
    try { f.get_uvar("l2"); lean_unreachable(); }
    catch (exception &) {}
    f.add_definition("x", Bool, True);
    object const & obj = f.get_object("x");
    lean_assert(obj.get_name() == "x");
    lean_assert(obj.get_type() == Bool);
    lean_assert(obj.get_value() == True);
    try { f.get_object("y"); lean_unreachable(); }
    catch (exception &) {}
    lean_assert(!f.find_object("y"));
    f.add_definition("y", False);
    lean_assert(f.find_object("y").get_type() == Bool);
    lean_assert(f.has_object("y"));
    lean_assert(!f.has_object("z"));
    bool found = false;
    std::for_each(f.begin_objects(), f.end_objects(), [&](object const & obj) { if (obj.has_name() && obj.get_name() == "y") found = true; });
    lean_assert(found);
    f.add_postfix("!", 10, Const("factorial"));
    name parts[] = {"if", "then", "else"};
    f.add_mixfixl(3, parts, 10, Const("if"));
}

static void tst10() {
    frontend f;
    formatter fmt = mk_pp_formatter(f);
    expr x = Const("xxxxxxxxxxxx");
    expr y = Const("y");
    expr z = Const("foo");
    expr e = Let({{x, True}, {y, And({x,x,x,x,x,x,x,x})}, {z, And(x, y)}}, Or({x, x, x, x, x, x, x, x, x, z, z, z, z, z, z, z}));
    std::cout << e << "\n";
    std::cout << fmt(e) << "\n";
}

int main() {
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
    return has_violations() ? 1 : 0;
}
