/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include "util/test.h"
#include "util/exception.h"
#include "util/trace.h"
#include "kernel/environment.h"
#include "kernel/type_checker.h"
#include "kernel/abstract.h"
#include "kernel/kernel_exception.h"
using namespace lean;

static environment add_decl(environment const & env, declaration const & d) {
    auto cd = check(env, d, name_generator("test"));
    return env.add(cd);
}

static void tst1() {
    environment env1;
    auto env2 = add_decl(env1, mk_definition("Bool", level_param_names(), mk_Type(), mk_Bool()));
    lean_assert(!env1.find("Bool"));
    lean_assert(env2.find("Bool"));
    lean_assert(env2.find("Bool")->get_value() == mk_Bool());
    try {
        auto env3 = add_decl(env2, mk_definition("Bool", level_param_names(), mk_Type(), mk_Bool()));
        lean_unreachable();
    } catch (kernel_exception & ex) {
        std::cout << "expected error: " << ex.pp(mk_simple_formatter(), options()) << "\n";
    }
    try {
        auto env4 = add_decl(env2, mk_definition("BuggyBool", level_param_names(), mk_Bool(), mk_Bool()));
        lean_unreachable();
    } catch (kernel_exception & ex) {
        std::cout << "expected error: " << ex.pp(mk_simple_formatter(), options()) << "\n";
    }
    try {
        auto env5 = add_decl(env2, mk_definition("Type1", level_param_names(), mk_metavar("T", mk_sort(mk_meta_univ("l"))), mk_Type()));
        lean_unreachable();
    } catch (kernel_exception & ex) {
        std::cout << "expected error: " << ex.pp(mk_simple_formatter(), options()) << "\n";
    }
    try {
        auto env6 = add_decl(env2, mk_definition("Type1", level_param_names(), mk_Type(), mk_metavar("T", mk_sort(mk_meta_univ("l")))));
        lean_unreachable();
    } catch (kernel_exception & ex) {
        std::cout << "expected error: " << ex.pp(mk_simple_formatter(), options()) << "\n";
    }
    try {
        auto env7 = add_decl(env2, mk_definition("foo", level_param_names(), mk_Type() >> mk_Type(), mk_Bool()));
        lean_unreachable();
    } catch (kernel_exception & ex) {
        std::cout << "expected error: " << ex.pp(mk_simple_formatter(), options()) << "\n";
    }
    expr A = Local("A", Type);
    expr x = Local("x", A);
    auto env3 = add_decl(env2, mk_definition("id", level_param_names(),
                                             Pi(A, A >> A),
                                             Fun({A, x}, x)));
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
    env = add_decl(env, mk_var_decl(name(base, 0u), level_param_names(), Bool >> (Bool >> Bool)));
    expr x = Local("x", Bool);
    expr y = Local("y", Bool);
    for (unsigned i = 1; i <= 100; i++) {
        expr prev = Const(name(base, i-1));
        env = add_decl(env, mk_definition(env, name(base, i), level_param_names(), Bool >> (Bool >> Bool),
                                          Fun({x, y}, prev(prev(x, y), prev(y, x)))));
    }
    expr A = Local("A", Type);
    expr a = Local("a", A);
    env = add_decl(env, mk_definition("id", level_param_names(),
                                      Pi(A, A >> A),
                                      Fun({A, a}, a)));
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
    lean_assert(checker.is_def_eq(f98(c1, c2), f97(f97(c1, c2), f97(c2, c1))));
    lean_assert(checker.is_def_eq(f98(c1, id(Bool, id(Bool, c2))), f97(f97(c1, id(Bool, c2)), f97(c2, c1))));
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
    virtual bool may_reduce_later(expr const &, extension_context &) const { return false; }
};

static void tst3() {
    environment env(0, true, true, true, list<name>(), std::unique_ptr<normalizer_extension>(new normalizer_extension_tst()));
    expr A = Local("A", Type);
    expr x = Local("x", A);
    expr id = Const("id");
    env = add_decl(env, mk_definition("id", level_param_names(),
                                      Pi(A, A >> A),
                                      Fun({A, x}, x)));
    expr mk = Const("mk");
    expr proj1 = Const("proj1");
    expr a = Const("a");
    expr b = Const("b");
    type_checker checker(env, name_generator("tmp"));
    lean_assert_eq(checker.whnf(proj1(proj1(mk(id(A, mk(a, b)), b)))), a);
}

class dummy_ext : public environment_extension {};

static void tst4() {
    environment env;
    try {
        env.get_extension(10000);
        lean_unreachable();
    } catch (kernel_exception & ex) {
        std::cout << "expected error: " << ex.what() << "\n";
    }
    try {
        env.update(10000, std::make_shared<dummy_ext>());
        lean_unreachable();
    } catch (kernel_exception & ex) {
        std::cout << "expected error: " << ex.what() << "\n";
    }
}

namespace lean {
class environment_id_tester {
public:
    static void tst1() {
        environment_id id1;
        environment_id id2 = environment_id::mk_descendant(id1);
        environment_id id3 = environment_id::mk_descendant(id2);
        environment_id id4 = environment_id::mk_descendant(id1);
        environment_id id5 = environment_id::mk_descendant(id3);
        environment_id id6 = environment_id::mk_descendant(id4);
        environment_id id7 = environment_id::mk_descendant(id3);
        environment_id id8 = environment_id::mk_descendant(id7);
        lean_assert(id1.is_descendant(id1));
        lean_assert(id2.is_descendant(id1));
        lean_assert(!id1.is_descendant(id2));
        lean_assert(id3.is_descendant(id1));
        lean_assert(id3.is_descendant(id2));
        lean_assert(id4.is_descendant(id1));
        lean_assert(!id4.is_descendant(id2));
        lean_assert(!id4.is_descendant(id3));
        lean_assert(id5.is_descendant(id3));
        lean_assert(!id5.is_descendant(id4));
        lean_assert(id6.is_descendant(id4));
        lean_assert(!id6.is_descendant(id5));
        lean_assert(id5.is_descendant(id1));
        lean_assert(id6.is_descendant(id1));
        lean_assert(id7.is_descendant(id3));
        lean_assert(id7.is_descendant(id2));
        lean_assert(id7.is_descendant(id1));
        lean_assert(!id7.is_descendant(id4));
        lean_assert(!id7.is_descendant(id5));
        lean_assert(!id7.is_descendant(id6));
        lean_assert(id8.is_descendant(id7));
        lean_assert(id8.is_descendant(id3));
        lean_assert(id8.is_descendant(id2));
        lean_assert(id8.is_descendant(id1));
        lean_assert(!id8.is_descendant(id4));
        lean_assert(!id8.is_descendant(id5));
        lean_assert(!id8.is_descendant(id6));
    }

    static void tst2() {
        constexpr unsigned num_paths = 50;
        constexpr unsigned path_len  = 100;
        std::vector<environment_id> ids[num_paths];
        for (unsigned i = 0; i < num_paths; i++) {
            if (i == 0)
                ids[i].push_back(environment_id());
            else
                ids[i].push_back(environment_id::mk_descendant(ids[i-1][1]));
            for (unsigned j = 0; j < path_len; j++) {
                ids[i].push_back(environment_id::mk_descendant(ids[i].back()));
            }
        }
        for (unsigned i = 0; i < num_paths; i++) {
            for (unsigned j = 0; j < path_len; j++) {
                for (unsigned k = 0; k < i; k++) {
                    lean_assert(ids[i][j].is_descendant(ids[k][1]));
                    lean_assert(ids[i][j].is_descendant(ids[k][0]));
                    lean_assert(!ids[k][1].is_descendant(ids[i][j]));
                    lean_assert(!ids[k][0].is_descendant(ids[i][j]));
                    for (unsigned s = 2; s < path_len; s++) {
                        lean_assert(!ids[i][j].is_descendant(ids[k][s]));
                    }
                }
                for (unsigned k = 0; k < j; k++) {
                    lean_assert(ids[i][j].is_descendant(ids[i][k]));
                    lean_assert(!ids[i][k].is_descendant(ids[i][j]));
                }
            }
        }
    }
};
}

int main() {
    save_stack_info();
    tst1();
    tst2();
    tst3();
    tst4();
    environment_id_tester::tst1();
    environment_id_tester::tst2();
    return has_violations() ? 1 : 0;
}
