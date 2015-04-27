/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include "util/test.h"
#include "util/exception.h"
#include "util/trace.h"
#include "util/init_module.h"
#include "util/sexpr/init_module.h"
#include "kernel/environment.h"
#include "kernel/type_checker.h"
#include "kernel/abstract.h"
#include "kernel/kernel_exception.h"
#include "kernel/init_module.h"
#include "library/init_module.h"
#include "library/print.h"
using namespace lean;

static environment add_decl(environment const & env, declaration const & d) {
    auto cd = check(env, d, name_generator("test"));
    return env.add(cd);
}

formatter mk_formatter(environment const & env) {
    return mk_print_formatter_factory()(env, options());
}

static void tst1() {
    environment env1;
    auto env2 = add_decl(env1, mk_definition("Prop", level_param_names(), mk_Type(), mk_Prop()));
    lean_assert(!env1.find("Prop"));
    lean_assert(env2.find("Prop"));
    lean_assert(env2.find("Prop")->get_value() == mk_Prop());
    try {
        auto env3 = add_decl(env2, mk_definition("Prop", level_param_names(), mk_Type(), mk_Prop()));
        lean_unreachable();
    } catch (kernel_exception & ex) {
        std::cout << "expected error: " << ex.pp(mk_formatter(ex.get_environment())) << "\n";
    }
    try {
        auto env4 = add_decl(env2, mk_definition("BuggyProp", level_param_names(), mk_Prop(), mk_Prop()));
        lean_unreachable();
    } catch (kernel_exception & ex) {
        std::cout << "expected error: " << ex.pp(mk_formatter(ex.get_environment())) << "\n";
    }
    try {
        auto env5 = add_decl(env2, mk_definition("Type1", level_param_names(), mk_metavar("T", mk_sort(mk_meta_univ("l"))), mk_Type()));
        lean_unreachable();
    } catch (kernel_exception & ex) {
        std::cout << "expected error: " << ex.pp(mk_formatter(ex.get_environment())) << "\n";
    }
    try {
        auto env6 = add_decl(env2, mk_definition("Type1", level_param_names(), mk_Type(), mk_metavar("T", mk_sort(mk_meta_univ("l")))));
        lean_unreachable();
    } catch (kernel_exception & ex) {
        std::cout << "expected error: " << ex.pp(mk_formatter(ex.get_environment())) << "\n";
    }
    try {
        auto env7 = add_decl(env2, mk_definition("foo", level_param_names(), mk_Type() >> mk_Type(), mk_Prop()));
        lean_unreachable();
    } catch (kernel_exception & ex) {
        std::cout << "expected error: " << ex.pp(mk_formatter(ex.get_environment())) << "\n";
    }
    expr Type = mk_Type();
    expr A = Local("A", Type);
    expr x = Local("x", A);
    auto env3 = add_decl(env2, mk_definition("id", level_param_names(),
                                             Pi(A, A >> A),
                                             Fun({A, x}, x)));
    expr Prop = mk_Prop();
    expr c  = mk_local("c", Prop);
    expr id = Const("id");
    type_checker checker(env3, name_generator("tmp"));
    lean_assert(checker.check(mk_app(id, Prop)).first == Prop >> Prop);
    lean_assert(checker.whnf(mk_app(id, Prop, c)).first == c);
    lean_assert(checker.whnf(mk_app(id, Prop, mk_app(id, Prop, mk_app(id, Prop, c)))).first == c);

    type_checker checker2(env2, name_generator("tmp"));
    lean_assert(checker2.whnf(mk_app(id, Prop, mk_app(id, Prop, mk_app(id, Prop, c)))).first == mk_app(id, Prop, mk_app(id, Prop, mk_app(id, Prop, c))));
}

static void tst2() {
    environment env;
    name base("base");
    expr Prop = mk_Prop();
    env = add_decl(env, mk_constant_assumption(name(base, 0u), level_param_names(), Prop >> (Prop >> Prop)));
    expr x = Local("x", Prop);
    expr y = Local("y", Prop);
    for (unsigned i = 1; i <= 100; i++) {
        expr prev = Const(name(base, i-1));
        env = add_decl(env, mk_definition(env, name(base, i), level_param_names(), Prop >> (Prop >> Prop),
                                          Fun({x, y}, mk_app(prev, mk_app(prev, x, y), mk_app(prev, y, x)))));
    }
    expr Type = mk_Type();
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
    expr c1  =  mk_local("c1", Prop);
    expr c2  = mk_local("c2", Prop);
    expr id = Const("id");
    std::cout << checker.whnf(mk_app(f3, c1, c2)).first << "\n";
    lean_assert_eq(env.find(name(base, 98))->get_weight(), 98);
    lean_assert(checker.is_def_eq(mk_app(f98, c1, c2), mk_app(f97, mk_app(f97, c1, c2), mk_app(f97, c2, c1))).first);
    lean_assert(checker.is_def_eq(mk_app(f98, c1, mk_app(id, Prop, mk_app(id, Prop, c2))), mk_app(f97, mk_app(f97, c1, mk_app(id, Prop, c2)), mk_app(f97, c2, c1))).first);
    name_set s;
    s.insert(name(base, 96));
}

class normalizer_extension_tst : public normalizer_extension {
public:
    virtual optional<pair<expr, constraint_seq>> operator()(expr const & e, extension_context & ctx) const {
        if (!is_app(e))
            return optional<pair<expr, constraint_seq>>();
        expr const & f = app_fn(e);
        expr const & a = app_arg(e);
        if (!is_constant(f) || const_name(f) != name("proj1"))
            return optional<pair<expr, constraint_seq>>();
        expr a_n = ctx.whnf(a).first;
        if (!is_app(a_n) || !is_app(app_fn(a_n)) || !is_constant(app_fn(app_fn(a_n))))
            return optional<pair<expr, constraint_seq>>();
        expr const & mk = app_fn(app_fn(a_n));
        if (const_name(mk) != name("mk"))
            return optional<pair<expr, constraint_seq>>();
        // In a real implementation, we must check if proj1 and mk were defined in the environment.
        return optional<pair<expr, constraint_seq>>(app_arg(app_fn(a_n)), constraint_seq());
    }
    virtual optional<expr> is_stuck(expr const &, extension_context &) const { return none_expr(); }
    virtual bool supports(name const &) const { return false; }
};

static void tst3() {
    environment env(0, true, true, true, std::unique_ptr<normalizer_extension>(new normalizer_extension_tst()));
    expr Type = mk_Type();
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
    lean_assert_eq(checker.whnf(mk_app(proj1, mk_app(proj1, mk_app(mk, mk_app(id, A, mk_app(mk, a, b)), b)))).first, a);
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
    initialize_util_module();
    initialize_sexpr_module();
    initialize_kernel_module();
    initialize_library_module();
    init_default_print_fn();
    tst1();
    tst2();
    tst3();
    tst4();
    environment_id_tester::tst1();
    environment_id_tester::tst2();
    finalize_library_module();
    finalize_kernel_module();
    finalize_sexpr_module();
    finalize_util_module();
    return has_violations() ? 1 : 0;
}
