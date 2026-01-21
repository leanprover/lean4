import Lean
open Lean Meta Elab Tactic

elab "sym_simp" "[" declNames:ident,* "]" : tactic => do
  let rewrite ← Sym.mkSimprocFor (← declNames.getElems.mapM fun s => realizeGlobalConstNoOverload s.raw) Sym.Simp.dischargeSimpSelf
  let methods : Sym.Simp.Methods := {
    pre  := Sym.Simp.simpControl
    post := Sym.Simp.evalGround.andThen rewrite
  }
  liftMetaTactic1 <| Sym.simpWith (Sym.simp · methods)

example : (1-1) + x*1 + (2-1)*0 = x := by
  sym_simp [Nat.add_zero, Nat.zero_add, Nat.mul_one]

opaque f : Nat → Nat
axiom fax : x > 10 → f x = 0

example : f 12 = 0 := by
 sym_simp [fax]

example : (if true then a else b) = a := by
  sym_simp []

example : (if True then a else b) = a := by
  sym_simp []

example : (if False then a else b) = b := by
  sym_simp []

example (f g : Nat → Nat) : (if a + 0 = a then f else g) a = f a := by
  sym_simp [Nat.add_zero]

example (f g : Nat → Nat → Nat) : (if a + 0 ≠ a then f else g) a (b + 0) = g a b := by
  sym_simp [Nat.add_zero]

/--
trace: a b : Nat
f g : Nat → Nat → Nat
h : a = b
⊢ (if ¬a = b then id f else id (id g)) a (b + 0) = g a b
-/
#guard_msgs in
example (f g : Nat → Nat → Nat) (h : a = b) : (if a + 0 ≠ b then id f else id (id g)) a (b + 0) = g a b := by
  sym_simp [Nat.add_zero, id_eq]
  trace_state -- `if-then-else` branches should not have been simplified
  subst h
  sym_simp [Nat.add_zero, id_eq]

def isNil (xs : List α) : Bool :=
  match xs with
  | [] => true
  | _::_ => false

example : isNil ([] : List Nat) = true := by
  sym_simp [isNil.eq_def]

inductive Kind where
  | a | b | c

def pick : Kind → Nat → Nat
  | .a => Nat.succ
  | .b => (2 * ·)
  | .c => id

example : pick .a 2 = 3 := by
  sym_simp [pick.eq_def]

example : pick .b 2 = 4 := by
  sym_simp [pick.eq_def]

example : pick .c 2 = 2 := by
  sym_simp [pick.eq_def, id_eq]

example : (match 1 - 1 with | 0 => 1 | _ => 2) = 1 := by
  sym_simp []

/--
trace: c : Bool
h : c = false
⊢ (match 0, c with
    | 0, true => 1 + 0
    | 0, false => 2 + 1
    | x, x_1 => 3 + 1) =
    3
-/
#guard_msgs in
example (h : c = false) : (match 1 - 1, c with | 0, true => 1+0 | 0, false => 2+1 | _, _ => 3+1) = 3 := by
  sym_simp [] -- Only discriminant should have been simplified, simplifier must not visit branches
  trace_state
  subst c
  sym_simp []

/--
trace: a : Nat
h : a = 0
⊢ (match a, false with
    | 0, true => 1 + 0
    | 0, false => 2 + 1
    | x, x_1 => 3 + 1) =
    3
-/
#guard_msgs in
example (h : a = 0) : (match a, !true with | 0, true => 1+0 | 0, false => 2+1 | _, _ => 3+1) = 3 := by
  sym_simp [Bool.not_true] -- Only discriminant should have been simplified, simplifier must not visit branches
  trace_state
  subst a
  sym_simp []

inductive Foo where
  | mk1 (a : Nat)
  | mk2 (b : Bool)
  | mk3 (c : Int)

example : (match Foo.mk3 c, Foo.mk2 b with | .mk1 _, _ => 1+0 | _, .mk2 _ => 2+1 | _, _ => id 4) = 3 := by
  sym_simp [id_eq]

example : (match (true, false, true) with | (false, _, _) => 1 | (_, false, _) => 2 | _ => 3) = 2 := by
  sym_simp []

example : (if _ : true then a else b) = a := by
  sym_simp []

example : (if _ : True then a else b) = a := by
  sym_simp []

example : (if _ : False then a else b) = b := by
  sym_simp []

example (f g : Nat → Nat) : (if _ : a + 0 = a then f else g) a = f a := by
  sym_simp [Nat.add_zero]

example (f g : Nat → Nat → Nat) : (if _ : a + 0 ≠ a then f else g) a (b + 0) = g a b := by
  sym_simp [Nat.add_zero]

/--
trace: a b : Nat
f g : Nat → Nat → Nat
h : a = b
⊢ (if h : ¬a = b then id f else id (id g)) a (b + 0) = g a b
-/
#guard_msgs in
example (f g : Nat → Nat → Nat) (h : a = b) : (if _ : a + 0 ≠ b then id f else id (id g)) a (b + 0) = g a b := by
  sym_simp [Nat.add_zero, id_eq]
  trace_state -- `if-then-else` branches should not have been simplified
  subst h
  sym_simp [Nat.add_zero, id_eq]

example : (bif true then a else b) = a := by
  sym_simp []

example : (bif false then a else b) = b := by
  sym_simp []

example (f g : Nat → Nat) : (bif a + 0 == a then f else g) a = f a := by
  sym_simp [Nat.add_zero, beq_self_eq_true]

example (f g : Nat → Nat → Nat) : (bif a + 0 != a then f else g) a (b + 0) = g a b := by
  sym_simp [Nat.add_zero, bne_self_eq_false]

/--
trace: a b : Nat
f g : Nat → Nat → Nat
h : a = b
⊢ (bif a != b then id f else id (id g)) a (b + 0) = g a b
-/
#guard_msgs in
example (f g : Nat → Nat → Nat) (h : a = b) : (bif a + 0 != b then id f else id (id g)) a (b + 0) = g a b := by
  sym_simp [Nat.add_zero, id_eq]
  trace_state -- `cond` branches should not have been simplified
  subst h
  sym_simp [Nat.add_zero, bne_self_eq_false, id_eq]

def pw (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | n+1 => 2 * pw n

example : pw 0 = 1 := by
  sym_simp [pw.eq_1]

example : pw 2 = 4 := by
  sym_simp [pw.eq_1, pw.eq_2]

example : pw 4 = 16 := by
  sym_simp [pw.eq_1, pw.eq_2]

example : pw (a + 2) = 2 * (2 * pw a) := by
  sym_simp [pw.eq_2]

example : pw (Nat.succ a) = 2 * pw a := by
  sym_simp [pw.eq_2]

example : pw (a + 3) = 2 * (2 * (2 * pw a)) := by
  sym_simp [pw.eq_2]

example : pw (Nat.succ (Nat.succ a)) = 2 * (2 * pw a) := by
  sym_simp [pw.eq_2]
