-- set_option trace.Meta.FunInd true

def test (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | x :: l =>
    match x == 3 with
    | false => test l
    | true => test l


/--
info: test.induct_unfolding (motive : List Nat → Nat → Prop) (case1 : motive [] 0)
  (case2 :
    ∀ (x : Nat) (l : List Nat),
      (x == 3) = false →
        motive l (test l) →
          motive (x :: l)
            (match x == 3 with
            | false => test l
            | true => test l))
  (case3 :
    ∀ (x : Nat) (l : List Nat),
      (x == 3) = true →
        motive l (test l) →
          motive (x :: l)
            (match x == 3 with
            | false => test l
            | true => test l))
  (l : List Nat) : motive l (test l)
-/
#guard_msgs in
#check test.induct_unfolding

example (l : List Nat) : test l = sorry := by
  induction l using test.induct_unfolding with
  | case1 => sorry
  | case2 x l h ih =>
    simp [h]
    assumption
  | case3 x l h ih =>
    simp [h]
    assumption


opaque someFunction (x : Nat) (h : (x == 3) = false) : Nat
opaque someOtherFunction (x : Nat) (h : (x == 3) = true) : Nat

def deptest (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | x :: l =>
    match h : x == 3 with
    | false => deptest l + someFunction x h
    | true => deptest l + someOtherFunction x h

/--
info: test.induct_unfolding (motive : List Nat → Nat → Prop) (case1 : motive [] 0)
  (case2 :
    ∀ (x : Nat) (l : List Nat),
      (x == 3) = false →
        motive l (test l) →
          motive (x :: l)
            (match x == 3 with
            | false => test l
            | true => test l))
  (case3 :
    ∀ (x : Nat) (l : List Nat),
      (x == 3) = true →
        motive l (test l) →
          motive (x :: l)
            (match x == 3 with
            | false => test l
            | true => test l))
  (l : List Nat) : motive l (test l)
-/
#guard_msgs in
#check test.induct_unfolding

example (l : List Nat) : deptest l = sorry := by
  induction l using deptest.induct_unfolding with
  | case1 => sorry
  | case2 x l h ih =>
    sorry
    -- simp [h] -- fails
    -- set_option trace.split.debug true in
    -- split
  | case3 x l h ih =>
    -- simp [h] -- fails
    sorry


#print test.match_2
#check test.match_1.fun_cases_unfolding
