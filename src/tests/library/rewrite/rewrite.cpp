/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Soonho Kong
*/
#include "util/trace.h"
#include "kernel/abstract.h"
#include "kernel/context.h"
#include "kernel/expr.h"
#include "kernel/type_checker.h"
#include "library/all/all.h"
#include "library/arith/arith.h"
#include "library/arith/nat.h"
#include "library/rewrite/fo_match.h"
#include "library/rewrite/rewrite.h"
#include "library/basic_thms.h"
#include "library/printer.h"
using namespace lean;

using std::cout;
using std::pair;
using std::endl;

static void theorem_rewrite1_tst() {
    cout << "=== theorem_rewrite1_tst() ===" << endl;
    // Theorem:     Pi(x y : N), x + y = y + x := ADD_COMM x y
    // Term   :     a + b
    // Result :     (b + a, ADD_COMM a b)
    expr a        = Const("a");                  // a  : Nat
    expr b        = Const("b");                  // b  : Nat
    expr a_plus_b = nAdd(a, b);
    expr b_plus_a = nAdd(b, a);
    expr add_comm_thm_type = Pi("x", Nat,
                                Pi("y", Nat,
                                   Eq(nAdd(Const("x"), Const("y")), nAdd(Const("y"), Const("x")))));
    expr add_comm_thm_body = Const("ADD_COMM");

    environment env = mk_toplevel();
    env.add_var("a", Nat);
    env.add_var("b", Nat);
    env.add_axiom("ADD_COMM", add_comm_thm_type); // ADD_COMM : Pi (x, y: N), x + y = y + z

    // Rewriting
    theorem_rewrite add_comm_thm_rewriter(add_comm_thm_type, add_comm_thm_body);
    context ctx;
    pair<expr, expr> result = add_comm_thm_rewriter(ctx, a_plus_b, Nat);
    expr concl = mk_eq(a_plus_b, result.first);
    expr proof = result.second;

    cout << "Theorem: " << add_comm_thm_type << " := " << add_comm_thm_body << endl;
    cout << "         " << concl << " := " << proof << endl;

    lean_assert(concl == mk_eq(a_plus_b, b_plus_a));
    lean_assert(proof == mk_app(mk_app(Const("ADD_COMM"), a), b));
    env.add_theorem("New_theorem1", concl, proof);
}

static void theorem_rewrite2_tst() {
    cout << "=== theorem_rewrite2_tst() ===" << endl;
    // Theorem:     Pi(x : N), x + 0 = x := ADD_ID x
    // Term   :     a + 0
    // Result :     (a, ADD_ID a)
    expr a           = Const("a");                  // a    : at
    expr zero        = nVal(0);                     // zero : Nat
    expr a_plus_zero = nAdd(a, zero);
    expr add_id_thm_type = Pi("x", Nat,
                           Eq(nAdd(Const("x"), zero), Const("x")));
    expr add_id_thm_body = Const("ADD_ID");

    environment env = mk_toplevel();
    env.add_var("a", Nat);
    env.add_axiom("ADD_ID", add_id_thm_type); // ADD_ID : Pi (x : N), x = x + 0

    // Rewriting
    theorem_rewrite add_id_thm_rewriter(add_id_thm_type, add_id_thm_body);
    context ctx;
    pair<expr, expr> result = add_id_thm_rewriter(ctx, a_plus_zero, Nat);
    expr concl = mk_eq(a_plus_zero, result.first);
    expr proof = result.second;

    cout << "Theorem: " << add_id_thm_type << " := " << add_id_thm_body << endl;
    cout << "         " << concl << " := " << proof << endl;

    lean_assert(concl == mk_eq(a_plus_zero, a));
    lean_assert(proof == mk_app(Const("ADD_ID"), a));
    env.add_theorem("New_theorem2", concl, proof);
}

static void then_rewrite1_tst() {
    cout << "=== then_rewrite1_tst() ===" << endl;
    // Theorem1:     Pi(x y : N), x + y = y + x := ADD_COMM x y
    // Theorem2:     Pi(x : N)  , x + 0 = x     := ADD_ID x
    // Term    :     0 + a
    // Result :      (a, TRANS (ADD_COMM 0 a) (ADD_ID a))

    expr a           = Const("a");                  // a  : Nat
    expr zero        = nVal(0);                     // zero : Nat
    expr a_plus_zero = nAdd(a, zero);
    expr zero_plus_a = nAdd(zero, a);
    expr add_comm_thm_type = Pi("x", Nat,
                                Pi("y", Nat,
                                   Eq(nAdd(Const("x"), Const("y")), nAdd(Const("y"), Const("x")))));
    expr add_comm_thm_body = Const("ADD_COMM");
    expr add_id_thm_type = Pi("x", Nat,
                           Eq(nAdd(Const("x"), zero), Const("x")));
    expr add_id_thm_body = Const("ADD_ID");

    environment env = mk_toplevel();
    env.add_var("a", Nat);
    env.add_axiom("ADD_COMM", add_comm_thm_type); // ADD_COMM : Pi (x, y: N), x + y = y + z
    env.add_axiom("ADD_ID", add_id_thm_type); // ADD_ID : Pi (x : N), x = x + 0

    // Rewriting
    theorem_rewrite add_comm_thm_rewriter(add_comm_thm_type, add_comm_thm_body);
    theorem_rewrite add_id_thm_rewriter(add_id_thm_type, add_id_thm_body);
    then_rewrite    then_rewriter1(add_comm_thm_rewriter, add_id_thm_rewriter);
    context ctx;
    pair<expr, expr> result = then_rewriter1(ctx, zero_plus_a, Nat);
    expr concl = mk_eq(zero_plus_a, result.first);
    expr proof = result.second;

    cout << "Theorem: " << add_comm_thm_type << " := " << add_comm_thm_body << endl;
    cout << "Theorem: " << add_id_thm_type << " := " << add_id_thm_body << endl;
    cout << "         " << concl << " := " << proof << endl;

    lean_assert(concl == mk_eq(zero_plus_a, a));
    lean_assert(proof == Trans(Nat, zero_plus_a, a_plus_zero, a,
                               mk_app(mk_app(Const("ADD_COMM"), zero), a), mk_app(Const("ADD_ID"), a)));

    env.add_theorem("New_theorem3", concl, proof);
}

static void then_rewrite2_tst() {
    cout << "=== then_rewrite2_tst() ===" << endl;
    // Theorem1:     Pi(x y z: N), x + (y + z) = (x + y) + z := ADD_ASSOC x y z
    // Theorem2:     Pi(x y : N),  x + y       = y + x       := ADD_COMM x y
    // Theorem3:     Pi(x : N),    x + 0       = x           := ADD_ID x
    // Term    :     0 + (a + 0)
    // Result :      (a, TRANS (ADD_ASSOC 0 a 0)         // (0 + a) + 0
    //                         (ADD_ID (0 + a))          // 0 + a
    //                         (ADD_COMM 0 a)            // a + 0
    //                         (ADD_ID a))               // a

    expr a           = Const("a");                  // a  : Nat
    expr zero        = nVal(0);                     // zero : Nat
    expr zero_plus_a  = nAdd(zero, a);
    expr a_plus_zero  = nAdd(a, zero);
    expr zero_plus_a_plus_zero  = nAdd(zero, nAdd(a, zero));
    expr zero_plus_a_plus_zero_ = nAdd(nAdd(zero, a), zero);
    expr add_assoc_thm_type = Pi("x", Nat,
                                Pi("y", Nat,
                                   Pi("z", Nat,
                                      Eq(nAdd(Const("x"), nAdd(Const("y"), Const("z"))),
                                         nAdd(nAdd(Const("x"), Const("y")), Const("z"))))));
    expr add_assoc_thm_body = Const("ADD_ASSOC");
    expr add_comm_thm_type = Pi("x", Nat,
                                Pi("y", Nat,
                                   Eq(nAdd(Const("x"), Const("y")), nAdd(Const("y"), Const("x")))));
    expr add_comm_thm_body = Const("ADD_COMM");
    expr add_id_thm_type = Pi("x", Nat,
                           Eq(nAdd(Const("x"), zero), Const("x")));
    expr add_id_thm_body = Const("ADD_ID");

    environment env = mk_toplevel();
    env.add_var("a", Nat);
    env.add_axiom("ADD_ASSOC", add_assoc_thm_type); // ADD_ASSOC : Pi (x, y, z : N), x + (y + z) = (x + y) + z
    env.add_axiom("ADD_COMM", add_comm_thm_type);   // ADD_COMM  : Pi (x, y: N), x + y = y + z
    env.add_axiom("ADD_ID", add_id_thm_type);       // ADD_ID    : Pi (x : N), x = x + 0

    // Rewriting
    theorem_rewrite add_assoc_thm_rewriter(add_assoc_thm_type, add_assoc_thm_body);
    theorem_rewrite add_comm_thm_rewriter(add_comm_thm_type, add_comm_thm_body);
    theorem_rewrite add_id_thm_rewriter(add_id_thm_type, add_id_thm_body);
    then_rewrite    then_rewriter2(then_rewrite(add_assoc_thm_rewriter, add_id_thm_rewriter),
                                   then_rewrite(add_comm_thm_rewriter, add_id_thm_rewriter));
    context ctx;
    pair<expr, expr> result = then_rewriter2(ctx, zero_plus_a_plus_zero, Nat);
    expr concl = mk_eq(zero_plus_a_plus_zero, result.first);
    expr proof = result.second;
    cout << "Theorem: " << add_assoc_thm_type << " := " << add_assoc_thm_body << endl;
    cout << "Theorem: " << add_comm_thm_type << " := " << add_comm_thm_body << endl;
    cout << "Theorem: " << add_id_thm_type << " := " << add_id_thm_body << endl;
    cout << "         " << concl << " := " << proof << endl;

    lean_assert(concl == mk_eq(zero_plus_a_plus_zero, a));
    lean_assert(proof == Trans(Nat, zero_plus_a_plus_zero, zero_plus_a, a,
                               Trans(Nat, zero_plus_a_plus_zero, zero_plus_a_plus_zero_, zero_plus_a,
                                     mk_app(mk_app(mk_app(Const("ADD_ASSOC"), zero), a), zero),
                                     mk_app(Const("ADD_ID"), zero_plus_a)),
                               Trans(Nat, zero_plus_a, a_plus_zero, a,
                                     mk_app(mk_app(Const("ADD_COMM"), zero), a),
                                     mk_app(Const("ADD_ID"), a))));

    env.add_theorem("New_theorem4", concl, proof);
}


static void orelse_rewrite1_tst() {
    cout << "=== orelse_rewrite1_tst() ===" << endl;
    // Theorem1:     Pi(x y z: N), x + (y + z) = (x + y) + z := ADD_ASSOC x y z
    // Theorem2:     Pi(x y : N),  x + y       = y + x       := ADD_COMM x y
    // Term   :     a + b
    // Result :     (b + a, ADD_COMM a b)
    expr a        = Const("a");                  // a  : Nat
    expr b        = Const("b");                  // b  : Nat
    expr a_plus_b = nAdd(a, b);
    expr b_plus_a = nAdd(b, a);
    expr add_assoc_thm_type = Pi("x", Nat,
                                Pi("y", Nat,
                                   Pi("z", Nat,
                                      Eq(nAdd(Const("x"), nAdd(Const("y"), Const("z"))),
                                         nAdd(nAdd(Const("x"), Const("y")), Const("z"))))));
    expr add_assoc_thm_body = Const("ADD_ASSOC");
    expr add_comm_thm_type = Pi("x", Nat,
                                Pi("y", Nat,
                                   Eq(nAdd(Const("x"), Const("y")), nAdd(Const("y"), Const("x")))));
    expr add_comm_thm_body = Const("ADD_COMM");

    environment env = mk_toplevel();
    env.add_var("a", Nat);
    env.add_var("b", Nat);
    env.add_axiom("ADD_COMM", add_comm_thm_type); // ADD_COMM : Pi (x, y: N), x + y = y + z

    // Rewriting
    theorem_rewrite add_assoc_thm_rewriter(add_assoc_thm_type, add_assoc_thm_body);
    theorem_rewrite add_comm_thm_rewriter(add_comm_thm_type, add_comm_thm_body);
    orelse_rewrite  add_assoc_or_comm_thm_rewriter(add_assoc_thm_rewriter, add_comm_thm_rewriter);
    context ctx;
    pair<expr, expr> result = add_assoc_or_comm_thm_rewriter(ctx, a_plus_b, Nat);
    expr concl = mk_eq(a_plus_b, result.first);
    expr proof = result.second;

    cout << "Theorem: " << add_assoc_thm_type << " := " << add_assoc_thm_body << endl;
    cout << "Theorem: " << add_comm_thm_type << " := " << add_comm_thm_body << endl;
    cout << "         " << concl << " := " << proof << endl;

    lean_assert(concl == mk_eq(a_plus_b, b_plus_a));
    lean_assert(proof == mk_app(mk_app(Const("ADD_COMM"), a), b));
    env.add_theorem("New_theorem5", concl, proof);
}

int main() {
    theorem_rewrite1_tst();
    theorem_rewrite2_tst();
    then_rewrite1_tst();
    then_rewrite2_tst();
    orelse_rewrite1_tst();
    return has_violations() ? 1 : 0;
}
