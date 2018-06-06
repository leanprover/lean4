/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include "runtime/exception.h"
#include "util/test.h"
#include "util/init_module.h"
#include "util/sexpr/init_module.h"
#include "kernel/environment.h"
#include "kernel/old_type_checker.h"
#include "kernel/abstract.h"
#include "kernel/kernel_exception.h"
#include "kernel/init_module.h"
#include "library/init_module.h"
#include "library/print.h"
using namespace lean;

static environment add_decl(environment const & env, declaration const & d) {
    auto cd = check(env, d);
    return env.add(cd);
}

static void tst1() {
    environment env1;
    reducibility_hints hints = reducibility_hints::mk_abbreviation();
    auto env2 = add_decl(env1, mk_definition("Prop", level_param_names(), mk_Type(), mk_Prop(), hints));
    lean_assert(!env1.find("Prop"));
    lean_assert(env2.find("Prop"));
    lean_assert(env2.find("Prop")->get_value() == mk_Prop());
    try {
        auto env3 = add_decl(env2, mk_definition("Prop", level_param_names(), mk_Type(), mk_Prop(), hints));
        lean_unreachable();
    } catch (kernel_exception & ex) {
        std::cout << "expected error: " << ex.what() << "\n";
    }
    try {
        auto env4 = add_decl(env2, mk_definition("BuggyProp", level_param_names(), mk_Prop(), mk_Prop(), hints));
        lean_unreachable();
    } catch (kernel_exception & ex) {
        std::cout << "expected error: " << ex.what() << "\n";
    }
    try {
        auto env5 = add_decl(env2, mk_definition("Type1", level_param_names(), mk_metavar("T", mk_sort(mk_meta_univ("l"))), mk_Type(), hints));
        lean_unreachable();
    } catch (kernel_exception & ex) {
        std::cout << "expected error: " << ex.what() << "\n";
    }
    try {
        auto env6 = add_decl(env2, mk_definition("Type1", level_param_names(), mk_Type(), mk_metavar("T", mk_sort(mk_meta_univ("l"))), hints));
        lean_unreachable();
    } catch (kernel_exception & ex) {
        std::cout << "expected error: " << ex.what() << "\n";
    }
    try {
        auto env7 = add_decl(env2, mk_definition("foo", level_param_names(), mk_Type() >> mk_Type(), mk_Prop(), hints));
        lean_unreachable();
    } catch (kernel_exception & ex) {
        std::cout << "expected error: " << ex.what() << "\n";
    }
    expr Type = mk_Type();
    expr A = Local("A", Type);
    expr x = Local("x", A);
    auto env3 = add_decl(env2, mk_definition("id", level_param_names(),
                                             Pi(A, A >> A),
                                             Fun({A, x}, x), hints));
    expr Prop = mk_Prop();
    expr c  = mk_local("c", Prop);
    expr id = Const("id");
    old_type_checker checker(env3);
    lean_assert(checker.check(mk_app(id, Prop)) == Prop >> Prop);
    lean_assert(checker.whnf(mk_app(id, Prop, c)) == c);
    lean_assert(checker.whnf(mk_app(id, Prop, mk_app(id, Prop, mk_app(id, Prop, c)))) == c);

    old_type_checker checker2(env2);
    lean_assert(checker2.whnf(mk_app(id, Prop, mk_app(id, Prop, mk_app(id, Prop, c)))) == mk_app(id, Prop, mk_app(id, Prop, mk_app(id, Prop, c))));
}

static void tst2() {
    environment env;
    reducibility_hints hints = reducibility_hints::mk_abbreviation();
    expr Type = mk_Type();
    expr A = Local("A", Type);
    expr x = Local("x", A);
    expr id = Const("id");
    env = add_decl(env, mk_definition("id", level_param_names(),
                                      Pi(A, A >> A),
                                      Fun({A, x}, x), hints));
    expr mk = Const("mk");
    expr proj1 = Const("proj1");
    expr a = Const("a");
    expr b = Const("b");
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
    initialize_library_core_module();
    initialize_library_module();
    init_default_print_fn();
    tst1();
    tst2();
    environment_id_tester::tst1();
    environment_id_tester::tst2();
    finalize_library_module();
    finalize_library_core_module();
    finalize_kernel_module();
    finalize_sexpr_module();
    finalize_util_module();
    return has_violations() ? 1 : 0;
}
