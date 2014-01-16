/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Soonho Kong
*/
#include "util/test.h"
#include "util/trace.h"
#include "kernel/abstract.h"
#include "kernel/context.h"
#include "kernel/expr.h"
#include "kernel/io_state.h"
#include "kernel/kernel.h"
#include "kernel/kernel_exception.h"
#include "library/printer.h"
#include "library/io_state_stream.h"
#include "library/arith/arith.h"
#include "library/arith/nat.h"
#include "library/rewriter/fo_match.h"
#include "library/rewriter/rewriter.h"
#include "frontends/lean/frontend.h"
using namespace lean;

#if 0
// TODO(Leo): migrate to homogeneous equality

using std::cout;
using std::pair;
using lean::endl;

static void theorem_rewriter1_tst() {
    cout << "=== theorem_rewriter1_tst() ===" << std::endl;
    // Theorem:     Pi(x y : N), x + y = y + x := ADD_COMM x y
    // Term   :     a + b
    // Result :     (b + a, ADD_COMM a b)
    expr a        = Const("a");                  // a  : Nat
    expr b        = Const("b");                  // b  : Nat
    expr a_plus_b = mk_Nat_add(a, b);
    expr b_plus_a = mk_Nat_add(b, a);
    expr add_comm_thm_type = Pi("x", Nat,
                                Pi("y", Nat,
                                   HEq(mk_Nat_add(Const("x"), Const("y")), mk_Nat_add(Const("y"), Const("x")))));
    expr add_comm_thm_body = Const("ADD_COMM");

    environment env; init_test_frontend(env);
    env->add_var("a", Nat);
    env->add_var("b", Nat);
    env->add_axiom("ADD_COMM", add_comm_thm_type); // ADD_COMM : Pi (x, y: N), x + y = y + z

    // Rewriting
    rewriter add_comm_thm_rewriter = mk_theorem_rewriter(add_comm_thm_type, add_comm_thm_body);
    context ctx;
    pair<expr, expr> result = add_comm_thm_rewriter(env, ctx, a_plus_b);
    expr concl = mk_heq(a_plus_b, result.first);
    expr proof = result.second;

    cout << "Theorem: " << add_comm_thm_type << " := " << add_comm_thm_body << std::endl;
    cout << "         " << concl << " := " << proof << std::endl;

    lean_assert_eq(concl, mk_eq(Nat, a_plus_b, b_plus_a));
    lean_assert_eq(proof, Const("ADD_COMM")(a, b));
    env->add_theorem("New_theorem1", concl, proof);
}

static void theorem_rewriter2_tst() {
    cout << "=== theorem_rewriter2_tst() ===" << std::endl;
    // Theorem:     Pi(x : N), x + 0 = x := ADD_ID x
    // Term   :     a + 0
    // Result :     (a, ADD_ID a)
    expr a           = Const("a");                  // a    : at
    expr zero        = nVal(0);                     // zero : Nat
    expr a_plus_zero = mk_Nat_add(a, zero);
    expr add_id_thm_type = Pi("x", Nat,
                           HEq(mk_Nat_add(Const("x"), zero), Const("x")));
    expr add_id_thm_body = Const("ADD_ID");

    environment env; init_test_frontend(env);
    env->add_var("a", Nat);
    env->add_axiom("ADD_ID", add_id_thm_type); // ADD_ID : Pi (x : N), x = x + 0

    // Rewriting
    rewriter add_id_thm_rewriter = mk_theorem_rewriter(add_id_thm_type, add_id_thm_body);
    context ctx;
    pair<expr, expr> result = add_id_thm_rewriter(env, ctx, a_plus_zero);
    expr concl = mk_heq(a_plus_zero, result.first);
    expr proof = result.second;

    cout << "Theorem: " << add_id_thm_type << " := " << add_id_thm_body << std::endl;
    cout << "         " << concl << " := " << proof << std::endl;

    lean_assert_eq(concl, mk_heq(a_plus_zero, a));
    lean_assert_eq(proof, Const("ADD_ID")(a));
    env->add_theorem("New_theorem2", concl, proof);
}

static void then_rewriter1_tst() {
    cout << "=== then_rewriter1_tst() ===" << std::endl;
    // Theorem1:     Pi(x y : N), x + y = y + x := ADD_COMM x y
    // Theorem2:     Pi(x : N)  , x + 0 = x     := ADD_ID x
    // Term    :     0 + a
    // Result :      (a, TRANS (ADD_COMM 0 a) (ADD_ID a))

    expr a           = Const("a");                  // a  : Nat
    expr zero        = nVal(0);                     // zero : Nat
    expr a_plus_zero = mk_Nat_add(a, zero);
    expr zero_plus_a = mk_Nat_add(zero, a);
    expr add_comm_thm_type = Pi("x", Nat,
                                Pi("y", Nat,
                                   HEq(mk_Nat_add(Const("x"), Const("y")), mk_Nat_add(Const("y"), Const("x")))));
    expr add_comm_thm_body = Const("ADD_COMM");
    expr add_id_thm_type = Pi("x", Nat,
                           HEq(mk_Nat_add(Const("x"), zero), Const("x")));
    expr add_id_thm_body = Const("ADD_ID");

    environment env; init_test_frontend(env);
    env->add_var("a", Nat);
    env->add_axiom("ADD_COMM", add_comm_thm_type); // ADD_COMM : Pi (x, y: N), x + y = y + z
    env->add_axiom("ADD_ID", add_id_thm_type); // ADD_ID : Pi (x : N), x = x + 0

    // Rewriting
    rewriter add_comm_thm_rewriter = mk_theorem_rewriter(add_comm_thm_type, add_comm_thm_body);
    rewriter add_id_thm_rewriter = mk_theorem_rewriter(add_id_thm_type, add_id_thm_body);
    rewriter then_rewriter1 = mk_then_rewriter(add_comm_thm_rewriter, add_id_thm_rewriter);
    context ctx;
    pair<expr, expr> result = then_rewriter1(env, ctx, zero_plus_a);
    expr concl = mk_heq(zero_plus_a, result.first);
    expr proof = result.second;

    cout << "Theorem: " << add_comm_thm_type << " := " << add_comm_thm_body << std::endl;
    cout << "Theorem: " << add_id_thm_type << " := " << add_id_thm_body << std::endl;
    cout << "         " << concl << " := " << proof << std::endl;

    lean_assert_eq(concl, mk_heq(zero_plus_a, a));
    lean_assert(proof == mk_trans_th(Nat, zero_plus_a, a_plus_zero, a,
                               Const("ADD_COMM")(zero, a), Const("ADD_ID")(a)));

    env->add_theorem("New_theorem3", concl, proof);
}

static void then_rewriter2_tst() {
    cout << "=== then_rewriter2_tst() ===" << std::endl;
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
    expr zero_plus_a  = mk_Nat_add(zero, a);
    expr a_plus_zero  = mk_Nat_add(a, zero);
    expr zero_plus_a_plus_zero  = mk_Nat_add(zero, mk_Nat_add(a, zero));
    expr zero_plus_a_plus_zero_ = mk_Nat_add(mk_Nat_add(zero, a), zero);
    expr add_assoc_thm_type = Pi("x", Nat,
                                Pi("y", Nat,
                                   Pi("z", Nat,
                                      HEq(mk_Nat_add(Const("x"), mk_Nat_add(Const("y"), Const("z"))),
                                         mk_Nat_add(mk_Nat_add(Const("x"), Const("y")), Const("z"))))));
    expr add_assoc_thm_body = Const("ADD_ASSOC");
    expr add_comm_thm_type = Pi("x", Nat,
                                Pi("y", Nat,
                                   HEq(mk_Nat_add(Const("x"), Const("y")), mk_Nat_add(Const("y"), Const("x")))));
    expr add_comm_thm_body = Const("ADD_COMM");
    expr add_id_thm_type = Pi("x", Nat,
                           HEq(mk_Nat_add(Const("x"), zero), Const("x")));
    expr add_id_thm_body = Const("ADD_ID");

    environment env; init_test_frontend(env);
    env->add_var("a", Nat);
    env->add_axiom("ADD_ASSOC", add_assoc_thm_type); // ADD_ASSOC : Pi (x, y, z : N), x + (y + z) = (x + y) + z
    env->add_axiom("ADD_COMM", add_comm_thm_type);   // ADD_COMM  : Pi (x, y: N), x + y = y + z
    env->add_axiom("ADD_ID", add_id_thm_type);       // ADD_ID    : Pi (x : N), x = x + 0

    // Rewriting
    rewriter add_assoc_thm_rewriter = mk_theorem_rewriter(add_assoc_thm_type, add_assoc_thm_body);
    rewriter add_comm_thm_rewriter = mk_theorem_rewriter(add_comm_thm_type, add_comm_thm_body);
    rewriter add_id_thm_rewriter = mk_theorem_rewriter(add_id_thm_type, add_id_thm_body);
    rewriter then_rewriter2 = mk_then_rewriter({add_assoc_thm_rewriter,
                                                add_id_thm_rewriter,
                                                add_comm_thm_rewriter,
                                                add_id_thm_rewriter});
    context ctx;
    pair<expr, expr> result = then_rewriter2(env, ctx, zero_plus_a_plus_zero);
    expr concl = mk_heq(zero_plus_a_plus_zero, result.first);
    expr proof = result.second;
    cout << "Theorem: " << add_assoc_thm_type << " := " << add_assoc_thm_body << std::endl;
    cout << "Theorem: " << add_comm_thm_type << " := " << add_comm_thm_body << std::endl;
    cout << "Theorem: " << add_id_thm_type << " := " << add_id_thm_body << std::endl;
    cout << "         " << concl << " := " << proof << std::endl;

    lean_assert_eq(concl, mk_heq(zero_plus_a_plus_zero, a));
    lean_assert(proof == mk_trans_th(Nat, zero_plus_a_plus_zero, a_plus_zero, a,
                               mk_trans_th(Nat, zero_plus_a_plus_zero, zero_plus_a, a_plus_zero,
                                     mk_trans_th(Nat, zero_plus_a_plus_zero, zero_plus_a_plus_zero_, zero_plus_a,
                                           Const("ADD_ASSOC")(zero, a, zero), Const("ADD_ID")(zero_plus_a)),
                                     Const("ADD_COMM")(zero, a)),
                               Const("ADD_ID")(a)));

    env->add_theorem("New_theorem4", concl, proof);
}

static void orelse_rewriter1_tst() {
    cout << "=== orelse_rewriter1_tst() ===" << std::endl;
    // Theorem1:    Pi(x y z: N), x + (y + z) = (x + y) + z := ADD_ASSOC x y z
    // Theorem2:    Pi(x y : N),  x + y       = y + x       := ADD_COMM x y
    // Term   :     a + b
    // Result :     (b + a, ADD_COMM a b)
    expr a        = Const("a");                  // a  : Nat
    expr b        = Const("b");                  // b  : Nat
    expr zero     = nVal(0);                     // zero : Nat
    expr a_plus_b = mk_Nat_add(a, b);
    expr b_plus_a = mk_Nat_add(b, a);
    expr add_assoc_thm_type = Pi("x", Nat,
                                Pi("y", Nat,
                                   Pi("z", Nat,
                                      HEq(mk_Nat_add(Const("x"), mk_Nat_add(Const("y"), Const("z"))),
                                         mk_Nat_add(mk_Nat_add(Const("x"), Const("y")), Const("z"))))));
    expr add_assoc_thm_body = Const("ADD_ASSOC");
    expr add_comm_thm_type = Pi("x", Nat,
                                Pi("y", Nat,
                                   HEq(mk_Nat_add(Const("x"), Const("y")), mk_Nat_add(Const("y"), Const("x")))));
    expr add_comm_thm_body = Const("ADD_COMM");
    expr add_id_thm_type = Pi("x", Nat,
                              HEq(mk_Nat_add(Const("x"), zero), Const("x")));
    expr add_id_thm_body = Const("ADD_ID");

    environment env; init_test_frontend(env);
    env->add_var("a", Nat);
    env->add_var("b", Nat);
    env->add_axiom("ADD_COMM", add_comm_thm_type); // ADD_COMM : Pi (x, y: N), x + y = y + z

    // Rewriting
    rewriter add_assoc_thm_rewriter = mk_theorem_rewriter(add_assoc_thm_type, add_assoc_thm_body);
    rewriter add_comm_thm_rewriter = mk_theorem_rewriter(add_comm_thm_type, add_comm_thm_body);
    rewriter add_id_thm_rewriter = mk_theorem_rewriter(add_id_thm_type, add_id_thm_body);
    rewriter add_assoc_or_comm_thm_rewriter = mk_orelse_rewriter({add_assoc_thm_rewriter,
                                                                  add_comm_thm_rewriter,
                                                                  add_id_thm_rewriter});
    context ctx;
    pair<expr, expr> result = add_assoc_or_comm_thm_rewriter(env, ctx, a_plus_b);
    expr concl = mk_heq(a_plus_b, result.first);
    expr proof = result.second;

    cout << "Theorem: " << add_assoc_thm_type << " := " << add_assoc_thm_body << std::endl;
    cout << "Theorem: " << add_comm_thm_type << " := " << add_comm_thm_body << std::endl;
    cout << "Theorem: " << add_id_thm_type << " := " << add_id_thm_body << std::endl;
    cout << "         " << concl << " := " << proof << std::endl;

    lean_assert_eq(concl, mk_heq(a_plus_b, b_plus_a));
    lean_assert_eq(proof, Const("ADD_COMM")(a, b));
    env->add_theorem("New_theorem5", concl, proof);
}

static void orelse_rewriter2_tst() {
    cout << "=== orelse_rewriter2_tst() ===" << std::endl;
    // Theorem1:    Pi(x y z: N), x + (y + z) = (x + y) + z := ADD_ASSOC x y z
    // Term   :     a + b
    // Result :     Fail
    expr a        = Const("a");                  // a  : Nat
    expr b        = Const("b");                  // b  : Nat
    expr zero     = nVal(0);                     // zero : Nat
    expr a_plus_b = mk_Nat_add(a, b);
    expr b_plus_a = mk_Nat_add(b, a);
    expr add_assoc_thm_type = Pi("x", Nat,
                                Pi("y", Nat,
                                   Pi("z", Nat,
                                      HEq(mk_Nat_add(Const("x"), mk_Nat_add(Const("y"), Const("z"))),
                                         mk_Nat_add(mk_Nat_add(Const("x"), Const("y")), Const("z"))))));
    expr add_assoc_thm_body = Const("ADD_ASSOC");
    expr add_id_thm_type = Pi("x", Nat,
                              HEq(mk_Nat_add(Const("x"), zero), Const("x")));
    expr add_id_thm_body = Const("ADD_ID");

    environment env; init_test_frontend(env);
    env->add_var("a", Nat);
    env->add_var("b", Nat);
    env->add_axiom("ADD_ASSOC", add_assoc_thm_type);
    env->add_axiom("ADD_ID", add_id_thm_type);

    // Rewriting
    rewriter add_assoc_thm_rewriter = mk_theorem_rewriter(add_assoc_thm_type, add_assoc_thm_body);
    rewriter add_id_thm_rewriter    = mk_theorem_rewriter(add_id_thm_type, add_id_thm_body);
    rewriter add_orelse_rewriter = mk_orelse_rewriter(add_assoc_thm_rewriter, add_id_thm_rewriter);

    context ctx;
    try {
        pair<expr, expr> result = add_orelse_rewriter(env, ctx, a_plus_b);
        lean_unreachable();
    } catch (rewriter_exception & ) {
        // Do nothing
        cout << "Exception Caught!" << std::endl;
        return;
    }
    lean_unreachable();
}

static void try_rewriter1_tst() {
    cout << "=== try_rewriter1_tst() ===" << std::endl;
    // Theorem1:    Pi(x y z: N), x + (y + z) = (x + y) + z := ADD_ASSOC x y z
    // Theorem2:    Pi(x y : N),  x + y       = y + x       := ADD_COMM x y
    // Theorem3:    Pi (x : N),   x           = x + 0       := ADD_ID x
    // Term   :     a + b
    // Result :     (b + a, ADD_COMM a b)
    expr a        = Const("a");                  // a  : Nat
    expr b        = Const("b");                  // b  : Nat
    expr zero     = nVal(0);                     // zero : Nat
    expr a_plus_b = mk_Nat_add(a, b);
    expr b_plus_a = mk_Nat_add(b, a);
    expr add_assoc_thm_type = Pi("x", Nat,
                                Pi("y", Nat,
                                   Pi("z", Nat,
                                      HEq(mk_Nat_add(Const("x"), mk_Nat_add(Const("y"), Const("z"))),
                                         mk_Nat_add(mk_Nat_add(Const("x"), Const("y")), Const("z"))))));
    expr add_assoc_thm_body = Const("ADD_ASSOC");
    expr add_comm_thm_type = Pi("x", Nat,
                                Pi("y", Nat,
                                   HEq(mk_Nat_add(Const("x"), Const("y")), mk_Nat_add(Const("y"), Const("x")))));
    expr add_comm_thm_body = Const("ADD_COMM");
    expr add_id_thm_type = Pi("x", Nat,
                              HEq(mk_Nat_add(Const("x"), zero), Const("x")));
    expr add_id_thm_body = Const("ADD_ID");

    environment env; init_test_frontend(env);
    env->add_var("a", Nat);
    env->add_var("b", Nat);
    env->add_axiom("ADD_COMM", add_comm_thm_type); // ADD_COMM : Pi (x, y: N), x + y = y + z

    // Rewriting
    rewriter add_assoc_thm_rewriter = mk_theorem_rewriter(add_assoc_thm_type, add_assoc_thm_body);
    rewriter add_comm_thm_rewriter = mk_theorem_rewriter(add_comm_thm_type, add_comm_thm_body);
    rewriter add_id_thm_rewriter = mk_theorem_rewriter(add_id_thm_type, add_id_thm_body);
    rewriter add_try_rewriter = mk_try_rewriter({add_assoc_thm_rewriter,
                                                 add_id_thm_rewriter});
    context ctx;
    pair<expr, expr> result = add_try_rewriter(env, ctx, a_plus_b);
    expr concl = mk_heq(a_plus_b, result.first);
    expr proof = result.second;

    cout << "Theorem: " << add_assoc_thm_type << " := " << add_assoc_thm_body << std::endl;
    cout << "Theorem: " << add_comm_thm_type << " := " << add_comm_thm_body << std::endl;
    cout << "Theorem: " << add_id_thm_type << " := " << add_id_thm_body << std::endl;
    cout << "         " << concl << " := " << proof << std::endl;

    lean_assert_eq(concl, mk_heq(a_plus_b, a_plus_b));
    lean_assert_eq(proof, Const("refl")(Nat, a_plus_b));
    env->add_theorem("New_theorem6", concl, proof);
}

static void try_rewriter2_tst() {
    cout << "=== try_rewriter2_tst() ===" << std::endl;
    // Theorem1:     Pi(x y z: N), x + (y + z) = (x + y) + z := ADD_ASSOC x y z
    // Theorem2:     Pi(x y : N),  x + y       = y + x       := ADD_COMM x y
    // Term   :     a + b
    // Result :     (b + a, ADD_COMM a b)
    expr a        = Const("a");                  // a  : Nat
    expr b        = Const("b");                  // b  : Nat
    expr zero     = nVal(0);                     // zero : Nat
    expr a_plus_b = mk_Nat_add(a, b);
    expr b_plus_a = mk_Nat_add(b, a);
    expr add_assoc_thm_type = Pi("x", Nat,
                                Pi("y", Nat,
                                   Pi("z", Nat,
                                      HEq(mk_Nat_add(Const("x"), mk_Nat_add(Const("y"), Const("z"))),
                                         mk_Nat_add(mk_Nat_add(Const("x"), Const("y")), Const("z"))))));
    expr add_assoc_thm_body = Const("ADD_ASSOC");
    expr add_comm_thm_type = Pi("x", Nat,
                                Pi("y", Nat,
                                   HEq(mk_Nat_add(Const("x"), Const("y")), mk_Nat_add(Const("y"), Const("x")))));
    expr add_comm_thm_body = Const("ADD_COMM");
    expr add_id_thm_type = Pi("x", Nat,
                              HEq(mk_Nat_add(Const("x"), zero), Const("x")));
    expr add_id_thm_body = Const("ADD_ID");

    environment env; init_test_frontend(env);
    env->add_var("a", Nat);
    env->add_var("b", Nat);
    env->add_axiom("ADD_COMM", add_comm_thm_type); // ADD_COMM : Pi (x, y: N), x + y = y + z

    // Rewriting
    rewriter add_assoc_thm_rewriter = mk_theorem_rewriter(add_assoc_thm_type, add_assoc_thm_body);
    rewriter add_comm_thm_rewriter = mk_theorem_rewriter(add_comm_thm_type, add_comm_thm_body);
    rewriter add_id_thm_rewriter = mk_theorem_rewriter(add_id_thm_type, add_id_thm_body);
    rewriter add_try_rewriter = mk_try_rewriter({add_assoc_thm_rewriter,
                                                 add_comm_thm_rewriter,
                                                 add_id_thm_rewriter});
    context ctx;
    pair<expr, expr> result = add_try_rewriter(env, ctx, a_plus_b);
    expr concl = mk_heq(a_plus_b, result.first);
    expr proof = result.second;

    cout << "Theorem: " << add_assoc_thm_type << " := " << add_assoc_thm_body << std::endl;
    cout << "Theorem: " << add_comm_thm_type << " := " << add_comm_thm_body << std::endl;
    cout << "Theorem: " << add_id_thm_type << " := " << add_id_thm_body << std::endl;
    cout << "         " << concl << " := " << proof << std::endl;

    lean_assert_eq(concl, mk_heq(a_plus_b, b_plus_a));
    lean_assert_eq(proof, Const("ADD_COMM")(a, b));
    env->add_theorem("try2", concl, proof);
}

static void app_rewriter1_tst() {
    cout << "=== app_rewriter1_tst() ===" << std::endl;
    // Theorem:     Pi(x y : N),  x + y       = y + x       := ADD_COMM x y
    // Term   :     f (a + b)
    // Result :     (f (b + a), ADD_COMM a b)
    expr a        = Const("a");   // a  : Nat
    expr b        = Const("b");   // b  : Nat
    expr f1       = Const("f1");  // f  : Nat -> Nat
    expr f2       = Const("f2");  // f  : Nat -> Nat -> Nat
    expr f3       = Const("f3");  // f  : Nat -> Nat -> Nat -> Nat
    expr f4       = Const("f4");  // f  : Nat -> Nat -> Nat -> Nat -> Nat
    expr zero     = nVal(0);      // zero : Nat
    expr a_plus_b = mk_Nat_add(a, b);
    expr b_plus_a = mk_Nat_add(b, a);
    expr add_comm_thm_type = Pi("x", Nat,
                                Pi("y", Nat,
                                   HEq(mk_Nat_add(Const("x"), Const("y")), mk_Nat_add(Const("y"), Const("x")))));
    expr add_comm_thm_body = Const("ADD_COMM");

    environment env; init_test_frontend(env);
    env->add_var("f1", Nat >> Nat);
    env->add_var("f2", Nat >> (Nat >> Nat));
    env->add_var("f3", Nat >> (Nat >> (Nat >> Nat)));
    env->add_var("f4", Nat >> (Nat >> (Nat >> (Nat >> Nat))));
    env->add_var("a", Nat);
    env->add_var("b", Nat);
    env->add_axiom("ADD_COMM", add_comm_thm_type); // ADD_COMM : Pi (x, y: N), x + y = y + z

    // Rewriting
    rewriter add_comm_thm_rewriter = mk_theorem_rewriter(add_comm_thm_type, add_comm_thm_body);
    rewriter add_try_comm_rewriter = mk_try_rewriter(add_comm_thm_rewriter);
    rewriter app_try_comm_rewriter = mk_app_rewriter(add_try_comm_rewriter);
    context ctx;

    cout << "RW = " << app_try_comm_rewriter << std::endl;

    expr v = f1(nVal(0));
    pair<expr, expr> result = app_try_comm_rewriter(env, ctx, v);
    expr concl = mk_heq(v, result.first);
    expr proof = result.second;
    cout << "Concl = " << concl << std::endl
         << "Proof = " << proof << std::endl;
    lean_assert_eq(concl, mk_heq(v, f1(nVal(0))));
    lean_assert_eq(proof, mk_refl_th(Nat, f1(nVal(0))));
    env->add_theorem("app_rewriter1", concl, proof);
    cout << "====================================================" << std::endl;
    v = f1(a_plus_b);
    result = app_try_comm_rewriter(env, ctx, v);
    concl = mk_heq(v, result.first);
    proof = result.second;
    cout << "Concl = " << concl << std::endl
         << "Proof = " << proof << std::endl;
    lean_assert_eq(concl, mk_heq(v, f1(b_plus_a)));
    lean_assert_eq(proof,
                   Const("congr2")(Nat, Fun(name("_"), Nat, Nat), a_plus_b, b_plus_a, f1, Const("ADD_COMM")(a, b)));
    env->add_theorem("app_rewriter2", concl, proof);
    cout << "====================================================" << std::endl;
    v = f4(nVal(0), a_plus_b, nVal(0), b_plus_a);
    result = app_try_comm_rewriter(env, ctx, v);
    concl = mk_heq(v, result.first);
    proof = result.second;
    cout << "Concl = " << concl << std::endl
         << "Proof = " << proof << std::endl;
    lean_assert_eq(concl, mk_heq(v, f4(nVal(0), b_plus_a, nVal(0), a_plus_b)));
    // Congr Nat (fun _ : Nat, Nat) (f4 0 (Nat::add a b) 0) (f4 0 (Nat::add b a) 0) (Nat::add b a) (Nat::add a b) (Congr1 Nat (fun _ : Nat, (Nat -> Nat)) (f4 0 (Nat::add a b)) (f4 0 (Nat::add b a)) 0 (Congr2 Nat (fun _ : Nat, (Nat -> Nat -> Nat)) (Nat::add a b) (Nat::add b a) (f4 0) (ADD_COMM a b))) (ADD_COMM b a)

    lean_assert_eq(proof,
                   Const("congr")(Nat, Fun(name("_"), Nat, Nat), f4(zero, a_plus_b, zero), f4(zero, b_plus_a, zero),
                                  b_plus_a, a_plus_b,
                                  Const("congr1")(Nat, Fun(name("_"), Nat, Nat >> Nat), f4(zero, a_plus_b),
                                                  f4(zero, b_plus_a), zero,
                                                  Const("congr2")(Nat, Fun(name("_"), Nat, Nat >> (Nat >> Nat)),
                                                                  a_plus_b, b_plus_a, f4(zero),
                                                                  Const("ADD_COMM")(a, b))),
                                  Const("ADD_COMM")(b, a)));
    env->add_theorem("app_rewriter3", concl, proof);
}

static void repeat_rewriter1_tst() {
    cout << "=== repeat_rewriter1_tst() ===" << std::endl;
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
    expr zero_plus_a  = mk_Nat_add(zero, a);
    expr a_plus_zero  = mk_Nat_add(a, zero);
    expr zero_plus_a_plus_zero  = mk_Nat_add(zero, mk_Nat_add(a, zero));
    expr zero_plus_a_plus_zero_ = mk_Nat_add(mk_Nat_add(zero, a), zero);
    expr add_assoc_thm_type = Pi("x", Nat,
                                Pi("y", Nat,
                                   Pi("z", Nat,
                                      HEq(mk_Nat_add(Const("x"), mk_Nat_add(Const("y"), Const("z"))),
                                         mk_Nat_add(mk_Nat_add(Const("x"), Const("y")), Const("z"))))));
    expr add_assoc_thm_body = Const("ADD_ASSOC");
    expr add_comm_thm_type = Pi("x", Nat,
                                Pi("y", Nat,
                                   HEq(mk_Nat_add(Const("x"), Const("y")), mk_Nat_add(Const("y"), Const("x")))));
    expr add_comm_thm_body = Const("ADD_COMM");
    expr add_id_thm_type = Pi("x", Nat,
                           HEq(mk_Nat_add(Const("x"), zero), Const("x")));
    expr add_id_thm_body = Const("ADD_ID");

    environment env; init_test_frontend(env);
    env->add_var("a", Nat);
    env->add_axiom("ADD_ASSOC", add_assoc_thm_type); // ADD_ASSOC : Pi (x, y, z : N), x + (y + z) = (x + y) + z
    env->add_axiom("ADD_COMM", add_comm_thm_type);   // ADD_COMM  : Pi (x, y: N), x + y = y + z
    env->add_axiom("ADD_ID", add_id_thm_type);       // ADD_ID    : Pi (x : N), x = x + 0

    // Rewriting
    rewriter add_assoc_thm_rewriter = mk_theorem_rewriter(add_assoc_thm_type, add_assoc_thm_body);
    rewriter add_comm_thm_rewriter = mk_theorem_rewriter(add_comm_thm_type, add_comm_thm_body);
    rewriter add_id_thm_rewriter = mk_theorem_rewriter(add_id_thm_type, add_id_thm_body);
    rewriter or_rewriter = mk_orelse_rewriter({add_assoc_thm_rewriter,
                                               add_id_thm_rewriter,
                                               add_comm_thm_rewriter});
    rewriter repeat_rw = mk_repeat_rewriter(or_rewriter);
    context ctx;
    pair<expr, expr> result = repeat_rw(env, ctx, zero_plus_a_plus_zero);
    expr concl = mk_heq(zero_plus_a_plus_zero, result.first);
    expr proof = result.second;
    cout << "Theorem: " << add_assoc_thm_type << " := " << add_assoc_thm_body << std::endl;
    cout << "Theorem: " << add_comm_thm_type << " := " << add_comm_thm_body << std::endl;
    cout << "Theorem: " << add_id_thm_type << " := " << add_id_thm_body << std::endl;
    cout << "         " << concl << " := " << proof << std::endl;

    lean_assert_eq(concl, mk_heq(zero_plus_a_plus_zero, a));
    env->add_theorem("repeat_thm1", concl, proof);
}

static void repeat_rewriter2_tst() {
    cout << "=== repeat_rewriter2_tst() ===" << std::endl;
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
    expr zero_plus_a  = mk_Nat_add(zero, a);
    expr a_plus_zero  = mk_Nat_add(a, zero);
    expr zero_plus_a_plus_zero  = mk_Nat_add(zero, mk_Nat_add(a, zero));
    expr zero_plus_a_plus_zero_ = mk_Nat_add(mk_Nat_add(zero, a), zero);
    expr add_assoc_thm_type = Pi("x", Nat,
                                Pi("y", Nat,
                                   Pi("z", Nat,
                                      HEq(mk_Nat_add(Const("x"), mk_Nat_add(Const("y"), Const("z"))),
                                         mk_Nat_add(mk_Nat_add(Const("x"), Const("y")), Const("z"))))));
    expr add_assoc_thm_body = Const("ADD_ASSOC");
    expr add_comm_thm_type = Pi("x", Nat,
                                Pi("y", Nat,
                                   HEq(mk_Nat_add(Const("x"), Const("y")), mk_Nat_add(Const("y"), Const("x")))));
    expr add_comm_thm_body = Const("ADD_COMM");
    expr add_id_thm_type = Pi("x", Nat,
                           HEq(mk_Nat_add(Const("x"), zero), Const("x")));
    expr add_id_thm_body = Const("ADD_ID");

    environment env; init_test_frontend(env);
    env->add_var("a", Nat);
    env->add_axiom("ADD_ASSOC", add_assoc_thm_type); // ADD_ASSOC : Pi (x, y, z : N), x + (y + z) = (x + y) + z
    env->add_axiom("ADD_COMM", add_comm_thm_type);   // ADD_COMM  : Pi (x, y: N), x + y = y + z
    env->add_axiom("ADD_ID", add_id_thm_type);       // ADD_ID    : Pi (x : N), x = x + 0

    // Rewriting
    rewriter add_assoc_thm_rewriter = mk_theorem_rewriter(add_assoc_thm_type, add_assoc_thm_body);
    rewriter add_comm_thm_rewriter = mk_theorem_rewriter(add_comm_thm_type, add_comm_thm_body);
    rewriter add_id_thm_rewriter = mk_theorem_rewriter(add_id_thm_type, add_id_thm_body);
    rewriter or_rewriter = mk_orelse_rewriter({add_assoc_thm_rewriter,
                                               add_id_thm_rewriter,
                                               add_comm_thm_rewriter});
    rewriter try_rw = mk_try_rewriter(or_rewriter);
    rewriter repeat_rw = mk_repeat_rewriter(try_rw);
    context ctx;
    pair<expr, expr> result = repeat_rw(env, ctx, zero_plus_a_plus_zero);
    expr concl = mk_heq(zero_plus_a_plus_zero, result.first);
    expr proof = result.second;
    cout << "Theorem: " << add_assoc_thm_type << " := " << add_assoc_thm_body << std::endl;
    cout << "Theorem: " << add_comm_thm_type << " := " << add_comm_thm_body << std::endl;
    cout << "Theorem: " << add_id_thm_type << " := " << add_id_thm_body << std::endl;
    cout << "         " << concl << " := " << proof << std::endl;

    lean_assert_eq(concl, mk_heq(zero_plus_a_plus_zero, a));
    env->add_theorem("repeat_thm2", concl, proof);
}

static void depth_rewriter1_tst() {
    cout << "=== depth_rewriter1_tst() ===" << std::endl;
    // Theorem:     Pi(x y : N),  x + y       = y + x       := ADD_COMM x y
    // Term   :     f (a + b)
    // Result :     (f (b + a), ADD_COMM a b)
    expr a        = Const("a");   // a  : Nat
    expr b        = Const("b");   // b  : Nat
    expr f1       = Const("f1");  // f  : Nat -> Nat
    expr f2       = Const("f2");  // f  : Nat -> Nat -> Nat
    expr f3       = Const("f3");  // f  : Nat -> Nat -> Nat -> Nat
    expr f4       = Const("f4");  // f  : Nat -> Nat -> Nat -> Nat -> Nat
    expr zero     = nVal(0);      // zero : Nat
    expr a_plus_b = mk_Nat_add(a, b);
    expr b_plus_a = mk_Nat_add(b, a);
    expr add_comm_thm_type = Pi("x", Nat,
                                Pi("y", Nat,
                                   HEq(mk_Nat_add(Const("x"), Const("y")), mk_Nat_add(Const("y"), Const("x")))));
    expr add_comm_thm_body = Const("ADD_COMM");

    environment env; init_test_frontend(env);
    env->add_var("f1", Nat >> Nat);
    env->add_var("f2", Nat >> (Nat >> Nat));
    env->add_var("f3", Nat >> (Nat >> (Nat >> Nat)));
    env->add_var("f4", Nat >> (Nat >> (Nat >> (Nat >> Nat))));
    env->add_var("a", Nat);
    env->add_var("b", Nat);
    env->add_axiom("ADD_COMM", add_comm_thm_type); // ADD_COMM : Pi (x, y: N), x + y = y + z

    // Rewriting
    rewriter add_comm_thm_rewriter = mk_theorem_rewriter(add_comm_thm_type, add_comm_thm_body);
    rewriter try_rewriter = mk_try_rewriter(add_comm_thm_rewriter);
    rewriter depth_rewriter = mk_depth_rewriter(try_rewriter);
    context ctx;

    cout << "RW = " << depth_rewriter << std::endl;

    expr v = mk_Nat_add(f1(mk_Nat_add(a, b)), f3(a, b, mk_Nat_add(a, b)));
    pair<expr, expr> result = depth_rewriter(env, ctx, v);
    expr concl = mk_heq(v, result.first);
    expr proof = result.second;
    cout << "Concl = " << concl << std::endl
         << "Proof = " << proof << std::endl;
    lean_assert_eq(concl, mk_heq(v, mk_Nat_add(f3(a, b, mk_Nat_add(b, a)), f1(mk_Nat_add(b, a)))));
    env->add_theorem("depth_rewriter1", concl, proof);
    cout << "====================================================" << std::endl;
}

static void lambda_body_rewriter_tst() {
    cout << "=== lambda_body_rewriter_tst() ===" << std::endl;
    // Theorem:     Pi(x y : N),  x + y       = y + x       := ADD_COMM x y
    // Term   :     fun (x : Nat), (a + b)
    // Result :     fun (x : Nat), (b + a)
    expr a        = Const("a");   // a  : Nat
    expr b        = Const("b");   // b  : Nat
    expr f1       = Const("f1");  // f  : Nat -> Nat
    expr f2       = Const("f2");  // f  : Nat -> Nat -> Nat
    expr f3       = Const("f3");  // f  : Nat -> Nat -> Nat -> Nat
    expr f4       = Const("f4");  // f  : Nat -> Nat -> Nat -> Nat -> Nat
    expr zero     = nVal(0);      // zero : Nat
    expr a_plus_b = mk_Nat_add(a, b);
    expr b_plus_a = mk_Nat_add(b, a);
    expr add_comm_thm_type = Pi("x", Nat,
                                Pi("y", Nat,
                                   HEq(mk_Nat_add(Const("x"), Const("y")), mk_Nat_add(Const("y"), Const("x")))));
    expr add_comm_thm_body = Const("ADD_COMM");

    environment env; init_test_frontend(env);
    env->add_var("f1", Nat >> Nat);
    env->add_var("f2", Nat >> (Nat >> Nat));
    env->add_var("f3", Nat >> (Nat >> (Nat >> Nat)));
    env->add_var("f4", Nat >> (Nat >> (Nat >> (Nat >> Nat))));
    env->add_var("a", Nat);
    env->add_var("b", Nat);
    env->add_axiom("ADD_COMM", add_comm_thm_type); // ADD_COMM : Pi (x, y: N), x + y = y + z

    // Rewriting
    rewriter add_comm_thm_rewriter = mk_theorem_rewriter(add_comm_thm_type, add_comm_thm_body);
    rewriter lambda_rewriter = mk_lambda_body_rewriter(add_comm_thm_rewriter);
    context ctx;
    cout << "RW = " << lambda_rewriter << std::endl;
    expr v = mk_lambda("x", Nat, mk_Nat_add(b, a));
    pair<expr, expr> result = lambda_rewriter(env, ctx, v);
    expr concl = mk_heq(v, result.first);
    expr proof = result.second;
    cout << "v     = " << v     << std::endl;
    cout << "Concl = " << concl << std::endl
         << "Proof = " << proof << std::endl;
    lean_assert_eq(concl, mk_heq(v, mk_lambda("x", Nat, mk_Nat_add(a, b))));
    env->add_theorem("lambda_rewriter1", concl, proof);

    // Theorem:     Pi(x y : N),  x + y       = y + x       := ADD_COMM x y
    // Term   :     fun (x : Nat), (x + a)
    // Result :     fun (x : Nat), (a + x)
    v = mk_lambda("x", Nat, mk_Nat_add(Var(0), a));
    result = lambda_rewriter(env, ctx, v);
    concl = mk_heq(v, result.first);
    proof = result.second;
    cout << "v     = " << v     << std::endl;
    cout << "Concl = " << concl << std::endl
         << "Proof = " << proof << std::endl;
    lean_assert_eq(concl, mk_heq(v, mk_lambda("x", Nat, mk_Nat_add(a, Var(0)))));
    env->add_theorem("lambda_rewriter2", concl, proof);
    cout << "====================================================" << std::endl;
}

static void lambda_type_rewriter_tst() {
    // Theorem:     Pi(x y : N),  x + y       = y + x       := ADD_COMM x y
    // Term   :     fun (x : vec(Nat, a + b)), x
    // Result :     fun (x : vec(Nat, b + a)), x
    cout << "=== lambda_type_rewriter_tst() ===" << std::endl;
    context ctx;
    environment env; init_test_frontend(env);
    expr a = Const("a");   // a  : Nat
    env->add_var("a", Nat);
    expr b = Const("b");   // b  : Nat
    env->add_var("b", Nat);
    expr vec = Const("vec");
    env->add_var("vec", Type() >> (Nat >> Type())); // vec : Type -> Nat -> Type
    expr add_comm_thm_type = Pi("x", Nat, Pi("y", Nat, HEq(mk_Nat_add(Const("x"), Const("y")), mk_Nat_add(Const("y"), Const("x")))));
    expr add_comm_thm_body = Const("ADD_COMM");
    env->add_axiom("ADD_COMM", add_comm_thm_type); // ADD_COMM : Pi (x, y: N), x + y = y + z
    rewriter add_comm_thm_rewriter = mk_theorem_rewriter(add_comm_thm_type, add_comm_thm_body);
    rewriter try_rewriter = mk_try_rewriter(add_comm_thm_rewriter);
    rewriter depth_rewriter = mk_depth_rewriter(try_rewriter);
    rewriter lambda_rewriter = mk_lambda_type_rewriter(depth_rewriter);

    expr v = mk_lambda("x", vec(Nat, mk_Nat_add(a, b)), Var(0));
    pair<expr, expr> result = lambda_rewriter(env, ctx, v);
    expr concl = mk_heq(v, result.first);
    expr proof = result.second;
    cout << "v     = " << v     << std::endl;
    cout << "Concl = " << concl << std::endl
         << "Proof = " << proof << std::endl;
    lean_assert_eq(concl, mk_heq(v, mk_lambda("x", vec(Nat, mk_Nat_add(b, a)), Var(0))));
    env->add_theorem("lambda_type_rewriter", concl, proof);
    cout << "====================================================" << std::endl;
}

int main() {
    save_stack_info();
    theorem_rewriter1_tst();
    theorem_rewriter2_tst();
    then_rewriter1_tst();
    then_rewriter2_tst();
    orelse_rewriter1_tst();
    orelse_rewriter2_tst();
    try_rewriter1_tst();
    try_rewriter2_tst();
    app_rewriter1_tst();
    repeat_rewriter1_tst();
    repeat_rewriter2_tst();
    depth_rewriter1_tst();
    lambda_body_rewriter_tst();
    lambda_type_rewriter_tst();
    return has_violations() ? 1 : 0;
}
#else
int main() {
    save_stack_info();
    return has_violations() ? 1 : 0;
}
#endif
