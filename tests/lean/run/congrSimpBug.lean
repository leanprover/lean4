set_option warn.sorry false
set_option pp.proofs true

inductive Expr (Identifier : Type) : Type where
  | mk (c : String)

def fv {I:Type} (e : Expr I) : List I := sorry

def eql {I:Type} [inst : DecidableEq I] (e : Expr I) (_h1 : fv e == []) : Nat := sorry

def eval {I:Type} [inst : DecidableEq I] (n : Nat) (e : Expr I) : Nat :=
  match n with
  | 0 => 0
  | Nat.succ n' =>
    let e2' := eval n' e
    eql e sorry
  termination_by n

/--
info: eql.congr_simp {I : Type} {inst : DecidableEq I} [inst✝ : DecidableEq I] (e e✝ : Expr I) (e_e : e = e✝)
  (_h1 : (fv e == []) = true) : eql e _h1 = eql e✝ (Subsingleton.elim inst inst✝ ▸ e_e ▸ _h1)
-/
#guard_msgs in
#check eql.congr_simp

/--
info: eval.congr_simp {I : Type} {inst : DecidableEq I} [inst✝ : DecidableEq I] (n n✝ : Nat) (e_n : n = n✝) (e e✝ : Expr I)
  (e_e : e = e✝) : eval n e = eval n✝ e✝
-/
#guard_msgs in
#check eval.congr_simp

def test4 {α} [DecidableEq α] (x : Nat) : Nat := sorry
/--
info: test4.congr_simp.{u_1} {α α✝ : Sort u_1} (e_α : α = α✝) {inst✝ : DecidableEq α} [DecidableEq α✝] (x x✝ : Nat)
  (e_x : x = x✝) : test4 x = test4 x✝
-/
#guard_msgs in
#check test4.congr_simp

structure Dep (p : Prop) [Decidable p] : Type where
def test5 {p} [Decidable p] (x : Dep p) : Nat := sorry

/--
info: test5.congr_simp {p : Prop} [Decidable p] (x x✝ : Dep p) (e_x : x = x✝) : test5 x = test5 x✝
-/
#guard_msgs in
#check test5.congr_simp

def test6 (x y : Nat) : Fin x := sorry
/-- info: test6.congr_simp (x y y✝ : Nat) (e_y : y = y✝) : test6 x y = test6 x y✝ -/
#guard_msgs in
#check test6.congr_simp

def test7 {α : Type u} [i : DecidableEq α] {x : α} (h : (x == x) = true) : Nat := sorry
/--
info: test7.congr_simp.{u} {α : Type u} {i : DecidableEq α} [i✝ : DecidableEq α] {x x✝ : α} (e_x : x = x✝)
  (h : (x == x) = true) : test7 h = test7 (Subsingleton.elim i i✝ ▸ e_x ▸ h)
-/
#guard_msgs in
#check test7.congr_simp

def test8 (p : Prop) [Decidable p] (_ : decide p = true) : Nat := 3

/--
info: test8.congr_simp (p p✝ : Prop) (e_p : p = p✝) {inst✝ : Decidable p} [Decidable p✝] (x✝ : decide p = true) :
  test8 p x✝ =
    test8 p✝
      (Eq.ndrec (motive := fun p => ∀ [inst : Decidable p], decide p = true)
        (fun [inst : Decidable p] => Subsingleton.elim inst✝ inst ▸ x✝) e_p)
-/
#guard_msgs in
#check test8.congr_simp
