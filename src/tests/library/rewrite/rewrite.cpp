/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Soonho Kong
*/
#include "kernel/abstract.h"
#include "kernel/context.h"
#include "kernel/expr.h"
#include "library/all/all.h"
#include "library/arith/arith.h"
#include "library/arith/nat.h"
#include "library/rewrite/fo_match.h"
#include "library/rewrite/rewrite.h"
#include "library/printer.h"
using namespace lean;

using std::cout;
using std::endl;

int main() {
    environment env = mk_toplevel();
    env.add_var("x", Nat);
    expr x    = Const("x");                  // x  : Nat
    expr y    = Const("y");                  // y  : Nat
    expr zero = nVal(0);                     // 0  : Nat
    expr x_plus_zero = nAdd(x, zero);        // x_plus_zero := x + 0
    expr y_plus_zero = nAdd(y, zero);        // y_plus_zero  := y + 0
    cout << "x := " << x << endl;
    cout << "y := " << y << endl;
    cout << "x + 0 := " << x_plus_zero << endl;
    cout << "x + 0 := " << y_plus_zero << endl;
    //env.display(cout);

    expr thm_t = Pi("x", Nat, Eq(nAdd(Const("x"), nVal(0)), Const("x"))); // Pi (x : Z), x + 0 = x
    cout << "theorem := " << thm_t << endl;
    env.add_axiom("H1", thm_t); // H1 : Pi (x : N), x = x + 0
    expr thm_v = Const("H1");
    cout << "axiom := " << thm_v << endl;

    theorem_rw trw(thm_t, thm_v);
    context ctx;
    trw(ctx, y_plus_zero);
    return 0;
}
