/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/test.h"
#include "util/exception.h"
#include "util/trace.h"
#include "kernel/environment.h"
#include "kernel/type_checker.h"
#include "kernel/abstract.h"
#include "kernel/kernel_exception.h"
using namespace lean;

static environment add_def(environment const & env, definition const & d) {
    auto cd = check(env, name_generator("test"), d, true, name_set());
    return env.add(cd);
}

static void tst1() {
    environment env1;
    auto env2 = add_def(env1, mk_definition("Bool", param_names(), level_cnstrs(), mk_Type(), mk_Bool()));
    lean_assert(!env1.find("Bool"));
    lean_assert(env2.find("Bool"));
    lean_assert(env2.find("Bool")->get_value() == mk_Bool());
    try {
        auto env3 = add_def(env2, mk_definition("Bool", param_names(), level_cnstrs(), mk_Type(), mk_Bool()));
        lean_unreachable();
    } catch (kernel_exception & ex) {
        std::cout << "expected error: " << ex.pp(mk_simple_formatter(), options()) << "\n";
    }
    try {
        auto env4 = add_def(env2, mk_definition("BuggyBool", param_names(), level_cnstrs(), mk_Bool(), mk_Bool()));
        lean_unreachable();
    } catch (kernel_exception & ex) {
        std::cout << "expected error: " << ex.pp(mk_simple_formatter(), options()) << "\n";
    }
    try {
        auto env5 = add_def(env2, mk_definition("Type1", param_names(), level_cnstrs(), mk_metavar("T", mk_sort(mk_meta_univ("l"))), mk_Type()));
        lean_unreachable();
    } catch (kernel_exception & ex) {
        std::cout << "expected error: " << ex.pp(mk_simple_formatter(), options()) << "\n";
    }
    try {
        auto env6 = add_def(env2, mk_definition("Type1", param_names(), level_cnstrs(), mk_Type(), mk_metavar("T", mk_sort(mk_meta_univ("l")))));
        lean_unreachable();
    } catch (kernel_exception & ex) {
        std::cout << "expected error: " << ex.pp(mk_simple_formatter(), options()) << "\n";
    }
    try {
        auto env7 = add_def(env2, mk_definition("foo", param_names(), level_cnstrs(), mk_Type() >> mk_Type(), mk_Bool()));
        lean_unreachable();
    } catch (kernel_exception & ex) {
        std::cout << "expected error: " << ex.pp(mk_simple_formatter(), options()) << "\n";
    }
    expr A = Const("A");
    expr x = Const("x");
    auto env3 = add_def(env2, mk_definition("id", param_names(), level_cnstrs(),
                                            Pi(A, mk_Type(), A >> A),
                                            Fun({{A, mk_Type()}, {x, A}}, x)));
    expr c  = mk_local("c", Bool);
    expr id = Const("id");
    type_checker checker(env3, name_generator("tmp"));
    lean_assert(checker.check(id(Bool)) == Bool >> Bool);
    lean_assert(checker.whnf(id(Bool, c)) == c);
    lean_assert(checker.whnf(id(Bool, id(Bool, id(Bool, c)))) == c);

    type_checker checker2(env2, name_generator("tmp"));
    lean_assert(checker2.whnf(id(Bool, id(Bool, id(Bool, c)))) == id(Bool, id(Bool, id(Bool, c))));
}

static void tst2() {
    environment env;
    name base("base");
    env = add_def(env, mk_var_decl(name(base, 0u), param_names(), level_cnstrs(), Bool >> (Bool >> Bool)));
    expr x = Const("x");
    expr y = Const("y");
    for (unsigned i = 1; i <= 100; i++) {
        expr prev = Const(name(base, i-1));
        env = add_def(env, mk_definition(env, name(base, i), param_names(), level_cnstrs(), Bool >> (Bool >> Bool),
                                         Fun({{x, Bool}, {y, Bool}}, prev(prev(x, y), prev(y, x)))));
    }
    expr A = Const("A");
    env = add_def(env, mk_definition("id", param_names(), level_cnstrs(),
                                     Pi(A, mk_Type(), A >> A),
                                     Fun({{A, mk_Type()}, {x, A}}, x)));
    type_checker checker(env, name_generator("tmp"));
    expr f96 = Const(name(base, 96));
    expr f97 = Const(name(base, 97));
    expr f98 = Const(name(base, 98));
    expr f3  = Const(name(base, 3));
    expr c1  =  mk_local("c1", Bool);
    expr c2  = mk_local("c2", Bool);
    expr id = Const("id");
    std::cout << checker.whnf(f3(c1, c2)) << "\n";
    lean_assert_eq(env.find(name(base, 98))->get_weight(), 98);
    lean_assert(checker.is_conv(f98(c1, c2), f97(f97(c1, c2), f97(c2, c1))));
    lean_assert(checker.is_conv(f98(c1, id(Bool, id(Bool, c2))), f97(f97(c1, id(Bool, c2)), f97(c2, c1))));
    name_set s;
    s.insert(name(base, 96));
    type_checker checker2(env, name_generator("tmp"), mk_default_converter(env, optional<module_idx>(), true, s));
    lean_assert_eq(checker2.whnf(f98(c1, c2)),
                   f96(f96(f97(c1, c2), f97(c2, c1)), f96(f97(c2, c1), f97(c1, c2))));
}

class normalizer_extension_tst : public normalizer_extension {
public:
    virtual optional<expr> operator()(expr const & e, extension_context & ctx) const {
        if (!is_app(e))
            return none_expr();
        expr const & f = app_fn(e);
        expr const & a = app_arg(e);
        if (!is_constant(f) || const_name(f) != name("proj1"))
            return none_expr();
        expr a_n = ctx.whnf(a);
        if (!is_app(a_n) || !is_app(app_fn(a_n)) || !is_constant(app_fn(app_fn(a_n))))
            return none_expr();
        expr const & mk = app_fn(app_fn(a_n));
        if (const_name(mk) != name("mk"))
            return none_expr();
        // In a real implementation, we must check if proj1 and mk were defined in the environment.
        return some_expr(app_arg(app_fn(a_n)));
    }
};

static void tst3() {
    environment env(0, true, true, std::unique_ptr<normalizer_extension>(new normalizer_extension_tst()));
    expr A = Const("A");
    expr x = Const("x");
    expr id = Const("id");
    env = add_def(env, mk_definition("id", param_names(), level_cnstrs(),
                                     Pi(A, mk_Type(), A >> A),
                                     Fun({{A, mk_Type()}, {x, A}}, x)));
    expr mk = Const("mk");
    expr proj1 = Const("proj1");
    expr a = Const("a");
    expr b = Const("b");
    type_checker checker(env, name_generator("tmp"));
    lean_assert_eq(checker.whnf(proj1(proj1(mk(id(A, mk(a, b)), b)))), a);
}

int main() {
    save_stack_info();
    tst1();
    tst2();
    tst3();
    return has_violations() ? 1 : 0;
}
