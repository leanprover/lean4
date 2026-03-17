import Std
set_option cbv.warning false

def function (n : Nat) : Nat := match n with
  | 0 => 0 + 1
  | Nat.succ n => function n + 1
termination_by (n,0)

example : function 150 = 151 := by
  conv =>
    lhs
    cbv

example : ((1,1).1,1).1 = 1 := by
  conv =>
    lhs
    cbv


def f : Unit -> Nat × Nat := fun _ => (1, 2)

example : (f ()).2 = 2 := by
  conv =>
    lhs
    cbv

def g : Unit → (Nat → Nat) × (Nat → Nat) := fun _ => (fun x => x + 1, fun x => x + 3)

example : (g ()).1 6 = 7 := by
  conv =>
    lhs
    cbv

example : "abx" ++ "c" = "a" ++ "bxc" := by
  conv =>
    lhs
    cbv
  conv =>
    rhs
    cbv

example : instHAdd.1 2 2 = 4 := by
  conv =>
    lhs
    cbv

example : (fun y : Nat → Nat => (fun x => y x)) Nat.succ 1 = 2 := by
  conv =>
    lhs
    cbv

example : (Std.TreeMap.empty.insert "a" "b" : Std.TreeMap String String).toList = [("a", "b")] := by
  conv =>
    lhs
    cbv

theorem array_test : (List.replicate 200 5 : List Nat).reverse = List.replicate 200 5 := by
  conv =>
    lhs
    cbv
  conv =>
    rhs
    cbv

def testFun (l : List Nat) : Nat := Id.run do
  let mut i := 0
  for _ in l do
    i := i + 1
  return i

-- Possibly a good benchmark for dealing with let expressions
example : testFun [1,2,3,4,5] = 5 := by
  conv =>
    lhs
    cbv

example : "ab".length + "ab".length = ("ab" ++ "ab").length := by
  conv =>
    lhs
    cbv
  conv =>
    rhs
    cbv

example : (((Std.TreeMap.empty : Std.TreeMap Nat Nat).insert 2 4).toList ++ [(5, 6)]).reverse = [(5,6), (2,4)] := by
  conv =>
    lhs
    cbv

def h := ()

example : h = () := by
  conv =>
    lhs
    cbv

def IsSubseq (s₁ : String) (s₂ : String) : Prop :=
  List.Sublist s₁.toList s₂.toList

def vowels : List Char := ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U']

def removeVowels (s : String) : String :=
    String.ofList (s.toList.filter (· ∉ vowels))

example : removeVowels "abcdef" = "bcdf" := by
  conv =>
    lhs
    cbv

example : removeVowels "abcdef\nghijklm" = "bcdf\nghjklm" := by
  conv =>
    lhs
    cbv

example : removeVowels "aaaaa" = "" := by
  conv =>
    lhs
    cbv

example : removeVowels "aaBAA" = "B" := by
  conv =>
    lhs
    cbv

example : removeVowels "zbcd" = "zbcd" := by
  conv =>
    lhs
    cbv

def Nat.factorial : Nat → Nat
  | 0 => 1
  | .succ n => Nat.succ n * factorial n

notation:10000 n "!" => Nat.factorial n

def Nat.brazilianFactorial : Nat → Nat
  | .zero => 1
  | .succ n => (Nat.succ n)! * brazilianFactorial n

def special_factorial (n : Nat) : Nat :=
  special_factorial.go n 1 1 0
where
  go (n fact brazilFact curr : Nat) : Nat :=
    if _h: curr >= n
    then brazilFact
    else
      let fact' := (curr + 1) * fact
      let brazilFact' := fact' * brazilFact
      special_factorial.go n fact' brazilFact' (Nat.succ curr)
  termination_by n - curr

example : Nat.brazilianFactorial 4 = 288 := by
  conv =>
    lhs
    cbv

example : special_factorial 4 = 288 := by
  conv =>
    lhs
    cbv

example : Nat.brazilianFactorial 5 = 34560 := by
  conv =>
    lhs
    cbv

example : Nat.brazilianFactorial 7 = 125411328000 := by
  conv =>
    lhs
    cbv

attribute [cbv_opaque] Std.DHashMap.emptyWithCapacity
attribute [cbv_opaque] Std.DHashMap.insert
attribute [cbv_eval] Std.DHashMap.contains_emptyWithCapacity
attribute [cbv_eval] Std.DHashMap.contains_insert

example : ((Std.DHashMap.emptyWithCapacity : Std.DHashMap Nat (fun _ => Nat)).insert 5 3).contains 5 = true := by
  conv =>
    lhs
    cbv

def myConst : Nat := Nat.zero

@[cbv_eval] theorem myConst_spec : myConst = 0 := by rfl

example : myConst = 0 := by conv => lhs; cbv

def myAdd (m n : Nat) := match m with
| 0 => n
| m' + 1 => (myAdd m' n) + 1

@[cbv_eval] theorem myAdd_test : myAdd 22 23 = 45 := by rfl

theorem fast_path : myAdd 22 23 = 45 := by conv => lhs; cbv

/--
info: theorem fast_path : myAdd 22 23 = 45 :=
Eq.mpr
  (id
    ((fun a a_1 e_a =>
        Eq.rec (motive := fun a_2 e_a => ∀ (a_3 : Nat), (a = a_3) = (a_2 = a_3)) (fun a_2 => Eq.refl (a = a_2)) e_a)
      (myAdd 22 23) 45 (Eq.trans myAdd_test (Eq.refl 45)) 45))
  (Eq.refl 45)
-/
#guard_msgs in
#print fast_path

theorem slow_path : myAdd 0 1 = 1 := by conv => lhs; cbv

/--
info: theorem slow_path : myAdd 0 1 = 1 :=
Eq.mpr
  (id
    ((fun a a_1 e_a =>
        Eq.rec (motive := fun a_2 e_a => ∀ (a_3 : Nat), (a = a_3) = (a_2 = a_3)) (fun a_2 => Eq.refl (a = a_2)) e_a)
      (myAdd 0 1) 1 (Eq.trans (myAdd.eq_1 1) (Eq.refl 1)) 1))
  (Eq.refl 1)
-/
#guard_msgs in
#print slow_path

/-! ## Or/And short-circuit evaluation -/

theorem or_test_1 : (1 < 2 ∨ (10000).factorial = 0) = True := by cbv

/--
info: theorem or_test_1 : (1 < 2 ∨ 10000! = 0) = True :=
of_eq_true
  (Eq.trans
    (congrFun'
      (congrArg Eq
        (Lean.Sym.or_eq_true_left (1 < 2) (10000! = 0) (Lean.Sym.Nat.lt_eq_true 1 2 (eagerReduce (Eq.refl true)))))
      True)
    (eq_self True))
-/
#guard_msgs in
#print or_test_1

theorem or_test_2 : (3 < 2 ∨ 1 < 2) = True := by cbv

/--
info: theorem or_test_2 : (3 < 2 ∨ 1 < 2) = True :=
of_eq_true
  (Eq.trans
    (congrFun'
      (congrArg Eq
        (Eq.trans (Lean.Sym.or_eq_right (3 < 2) (1 < 2) (Lean.Sym.Nat.lt_eq_false 3 2 (eagerReduce (Eq.refl false))))
          (Lean.Sym.Nat.lt_eq_true 1 2 (eagerReduce (Eq.refl true)))))
      True)
    (eq_self True))
-/
#guard_msgs in
#print or_test_2

theorem or_test_3 : (3 < 2 ∨ 5 < 4) = False := by cbv

/--
info: theorem or_test_3 : (3 < 2 ∨ 5 < 4) = False :=
of_eq_true
  (Eq.trans
    (congrFun'
      (congrArg Eq
        (Eq.trans (Lean.Sym.or_eq_right (3 < 2) (5 < 4) (Lean.Sym.Nat.lt_eq_false 3 2 (eagerReduce (Eq.refl false))))
          (Lean.Sym.Nat.lt_eq_false 5 4 (eagerReduce (Eq.refl false)))))
      False)
    (eq_self False))
-/
#guard_msgs in
#print or_test_3

theorem and_test_1 : (3 < 2 ∧ (10000).factorial = 0) = False := by cbv

/--
info: theorem and_test_1 : (3 < 2 ∧ 10000! = 0) = False :=
of_eq_true
  (Eq.trans
    (congrFun'
      (congrArg Eq
        (Lean.Sym.and_eq_false_left (3 < 2) (10000! = 0) (Lean.Sym.Nat.lt_eq_false 3 2 (eagerReduce (Eq.refl false)))))
      False)
    (eq_self False))
-/
#guard_msgs in
#print and_test_1

theorem and_test_2 : (1 < 2 ∧ 3 < 4) = True := by cbv

/--
info: theorem and_test_2 : (1 < 2 ∧ 3 < 4) = True :=
of_eq_true
  (Eq.trans
    (congrFun'
      (congrArg Eq
        (Eq.trans (Lean.Sym.and_eq_left (1 < 2) (3 < 4) (Lean.Sym.Nat.lt_eq_true 1 2 (eagerReduce (Eq.refl true))))
          (Lean.Sym.Nat.lt_eq_true 3 4 (eagerReduce (Eq.refl true)))))
      True)
    (eq_self True))
-/
#guard_msgs in
#print and_test_2

theorem and_test_3 : (1 < 2 ∧ 5 < 4) = False := by cbv

/--
info: theorem and_test_3 : (1 < 2 ∧ 5 < 4) = False :=
of_eq_true
  (Eq.trans
    (congrFun'
      (congrArg Eq
        (Eq.trans (Lean.Sym.and_eq_left (1 < 2) (5 < 4) (Lean.Sym.Nat.lt_eq_true 1 2 (eagerReduce (Eq.refl true))))
          (Lean.Sym.Nat.lt_eq_false 5 4 (eagerReduce (Eq.refl false)))))
      False)
    (eq_self False))
-/
#guard_msgs in
#print and_test_3

theorem or_and : (1 < 2 ∨ (3 < 2 ∧ (10000).factorial = 0)) = True := by cbv

/--
info: theorem or_and : (1 < 2 ∨ 3 < 2 ∧ 10000! = 0) = True :=
of_eq_true
  (Eq.trans
    (congrFun'
      (congrArg Eq
        (Lean.Sym.or_eq_true_left (1 < 2) (3 < 2 ∧ 10000! = 0)
          (Lean.Sym.Nat.lt_eq_true 1 2 (eagerReduce (Eq.refl true)))))
      True)
    (eq_self True))
-/
#guard_msgs in
#print or_and

theorem and_or : (3 < 2 ∧ (1 < 2 ∨ (10000).factorial = 0)) = False := by cbv

/--
info: theorem and_or : (3 < 2 ∧ (1 < 2 ∨ 10000! = 0)) = False :=
of_eq_true
  (Eq.trans
    (congrFun'
      (congrArg Eq
        (Lean.Sym.and_eq_false_left (3 < 2) (1 < 2 ∨ 10000! = 0)
          (Lean.Sym.Nat.lt_eq_false 3 2 (eagerReduce (Eq.refl false)))))
      False)
    (eq_self False))
-/
#guard_msgs in
#print and_or
