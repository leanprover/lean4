import Lean

/-!
`Sym.Arith.normalize?` evaluates ground `Nat`, `Int` and `Rat` subterms to numerals with `Eq.refl`
steps, which the kernel checks by evaluation, instead of proving them with a reflection
certificate. Each test prints the normal form and its proof, and the kernel checks the proof.
-/

open Lean Meta Sym Arith

def getDefValue (n : Name) : MetaM Expr := do
  let some (.defnInfo info) := (← getEnv).find? n
    | throwError "expected definition: {n}"
  return info.value

def test (n : Name) : SymM Unit := do
  let e ← preprocessExpr (← getDefValue n)
  match (← normalize? e (fun _ => return .rfl)) with
  | .rfl false _ => logInfo m!"{n}: unchanged"
  | .rfl true _ => logInfo m!"{n}: {e} (normal)"
  | .step e' h _ _ =>
    addDecl <| .thmDecl { name := n ++ `norm, levelParams := [], type := ← mkEq e e', value := h }
    logInfo m!"{n}: {e'}\nproof: {h}"

opaque a : Nat
opaque x : Int
opaque y : Int
opaque q : Rat

def n1 : Nat := 2 ^ 64
def n2 : Nat := 128 * 4 + 1
def n3 : Nat := a + (2 + 3)
def n4 : Nat := (2 + 3) * a
def n5 : Prop := a = 2 + 3
def n6 : Prop := a + 1 ≤ 2 ^ 8
def i1 : Int := 2 ^ 10 - 1
def i2 : Int := -(2 * 3)
def i3 : Int := x + (2 - 3) * y
def i4 : Int := ((2 : Nat) : Int) + 3
def i5 : Prop := x = 3 * 4 - 1
def i6 : Int := x - x
def r1 : Rat := 2 * 3 - 10
def r2 : Rat := q + 2 ^ 10
def r3 : Prop := q = 2 * 3

/--
info: n1: 18446744073709551616
proof: id (Eq.refl 18446744073709551616)
-/
#guard_msgs in
run_meta SymM.run do test ``n1

/--
info: n2: 513
proof: Eq.trans (congrFun' (congrArg HAdd.hAdd (id (Eq.refl 512))) 1) (id (Eq.refl 513))
-/
#guard_msgs in
run_meta SymM.run do test ``n2

/--
info: n3: a + 5
proof: congrArg (HAdd.hAdd a) (id (Eq.refl 5))
-/
#guard_msgs in
run_meta SymM.run do test ``n3

/--
info: n4: 5 * a
proof: congrFun' (congrArg HMul.hMul (id (Eq.refl 5))) a
-/
#guard_msgs in
run_meta SymM.run do test ``n4

/--
info: n5: a = 5
proof: congrArg (Eq a) (id (Eq.refl 5))
-/
#guard_msgs in
run_meta SymM.run do test ``n5

/--
info: n6: a ≤ 255
proof: Eq.trans (congrArg (LE.le (a + 1)) (id (Eq.refl 256)))
  (id
    (Grind.CommRing.le_cancel_of_kronLinS (RArray.leaf a) 11
      ((Grind.CommRing.Expr.var 0).add (Grind.CommRing.Expr.num (Int.ofNat 1)))
      (Grind.CommRing.Expr.num (Int.ofNat 256)) (Grind.CommRing.Expr.var 0) (Grind.CommRing.Expr.num (Int.ofNat 255))
      (Grind.CommRing.Expr.num (Int.ofNat 1)) (eagerReduce (Eq.refl true)) (eagerReduce (Eq.refl true))
      (Eq.refl
        (Grind.CommRing.Expr.kronLinEval_k 11
          ((Grind.CommRing.Expr.var 0).add (Grind.CommRing.Expr.num (Int.ofNat 1)))))
      (eagerReduce (Eq.refl true)) (eagerReduce (Eq.refl true))
      (Eq.refl (Grind.CommRing.Expr.kronLinEval_k 11 (Grind.CommRing.Expr.num (Int.ofNat 256))))))
-/
#guard_msgs in
run_meta SymM.run do test ``n6

/--
info: i1: 1023
proof: Eq.trans (congrFun' (congrArg HSub.hSub (id (Eq.refl 1024))) 1) (id (Eq.refl 1023))
-/
#guard_msgs in
run_meta SymM.run do test ``i1

/--
info: i2: -6
proof: congrArg Neg.neg (id (Eq.refl 6))
-/
#guard_msgs in
run_meta SymM.run do test ``i2

/--
info: i3: x + -1 * y
proof: congrArg (HAdd.hAdd x) (congrFun' (congrArg HMul.hMul (id (Eq.refl (-1)))) y)
-/
#guard_msgs in
run_meta SymM.run do test ``i3

/--
info: i4: 5
proof: Eq.trans (congrFun' (congrArg HAdd.hAdd (id (Grind.Semiring.natCast_eq_ofNat 2))) 3) (id (Eq.refl 5))
-/
#guard_msgs in
run_meta SymM.run do test ``i4

/--
info: i5: x = 11
proof: congrArg (Eq x) (Eq.trans (congrFun' (congrArg HSub.hSub (id (Eq.refl 12))) 1) (id (Eq.refl 11)))
-/
#guard_msgs in
run_meta SymM.run do test ``i5

/--
info: i6: 0
proof: id
  (Int.Internal.Linear.Expr.eq_of_norm_expr_k (RArray.leaf x)
    ((Int.Internal.Linear.Expr.var 0).sub (Int.Internal.Linear.Expr.var 0)) (Int.Internal.Linear.Expr.num 0)
    (eagerReduce (Eq.refl true)))
-/
#guard_msgs in
run_meta SymM.run do test ``i6

/--
info: r1: -4
proof: Eq.trans (congrFun' (congrArg HSub.hSub (id (Eq.refl 6))) 10) (id (Eq.refl (-4)))
-/
#guard_msgs in
run_meta SymM.run do test ``r1

/--
info: r2: q + 1024
proof: congrArg (HAdd.hAdd q) (id (Eq.refl 1024))
-/
#guard_msgs in
run_meta SymM.run do test ``r2

/--
info: r3: q = 6
proof: congrArg (Eq q) (id (Eq.refl 6))
-/
#guard_msgs in
run_meta SymM.run do test ``r3
