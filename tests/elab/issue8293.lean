set_option linter.unusedVariables false

inductive MyVec (α : Type u) : Nat → Type u where
  | nil : MyVec α 0
  | cons : α → MyVec α n → MyVec α (n + 1)

def test (f : Unit → MyVec α n) : Nat :=
  match f () with
  | .nil => 52
  | .cons _ _ => 421

/--
info: test.fun_cases_unfolding.{u_1} {α : Type u_1} (motive : {n : Nat} → (Unit → MyVec α n) → Nat → Prop)
  (case1 :
    ∀ (f : Unit → MyVec α 0),
      f () = MyVec.nil →
        motive f
          (match 0, f (), f with
          | .(0), MyVec.nil, f => 52
          | .(n + 1), MyVec.cons a a_1, f => 421))
  (case2 :
    ∀ (n : Nat) (a : α) (a_1 : MyVec α n) (f : Unit → MyVec α (n + 1)),
      f () = MyVec.cons a a_1 →
        motive f
          (match n + 1, f (), f with
          | .(0), MyVec.nil, f => 52
          | .(n + 1), MyVec.cons a a_2, f => 421))
  {n : Nat} (f : Unit → MyVec α n) : motive f (test f)
-/
#guard_msgs(pass trace, all) in
#check test.fun_cases_unfolding

def alsoTest (f : Unit → MyVec α n) : Nat :=
  match h : f () with
  | .nil => 52
  | .cons _ _ => 421

/--
info: alsoTest.fun_cases_unfolding.{u_1} {α : Type u_1} (motive : {n : Nat} → (Unit → MyVec α n) → Nat → Prop)
  (case1 :
    ∀ (f : Unit → MyVec α 0),
      f () = MyVec.nil →
        motive f
          (match h : 0, h : f (), f with
          | .(0), MyVec.nil, f_1 => 52
          | .(n + 1), MyVec.cons a a_1, f_1 => 421))
  (case2 :
    ∀ (n : Nat) (a : α) (a_1 : MyVec α n) (f : Unit → MyVec α (n + 1)),
      f () = MyVec.cons a a_1 →
        motive f
          (match h : n + 1, h : f (), f with
          | .(0), MyVec.nil, f_1 => 52
          | .(n_1 + 1), MyVec.cons a a_2, f_1 => 421))
  {n : Nat} (f : Unit → MyVec α n) : motive f (alsoTest f)
-/
#guard_msgs(pass trace, all) in
#check alsoTest.fun_cases_unfolding
