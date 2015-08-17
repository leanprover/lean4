/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/environment.h"
#include "kernel/type_checker.h"
#include "kernel/abstract.h"
#include "init/init.h"
using namespace lean;

static environment add_decl(environment const & env, declaration const & d) {
    auto cd = check(env, d);
    return env.add(cd);
}

int main() {
    environment env;
    std::cout << "Lean (empty) environment was successfully created\n";
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
    return 0;
}
