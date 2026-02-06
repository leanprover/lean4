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
  rfl

example : removeVowels "abcdef\nghijklm" = "bcdf\nghjklm" := by
  conv =>
    lhs
    cbv
  rfl
example : removeVowels "aaaaa" = "" := by
  conv =>
    lhs
    cbv
  rfl
example : removeVowels "aaBAA" = "B" := by
  conv =>
    lhs
    cbv
  rfl

example : removeVowels "zbcd" = "zbcd" := by
  conv =>
    lhs
    cbv
  rfl

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
attribute [cbv_opaque] Std.DHashMap.getEntry
attribute [cbv_opaque] Std.DHashMap.contains
attribute [cbv_eval Std.DHashMap.contains] Std.DHashMap.contains_emptyWithCapacity
attribute [cbv_eval Std.DHashMap.contains] Std.DHashMap.contains_insert

example : ((Std.DHashMap.emptyWithCapacity : Std.DHashMap Nat (fun _ => Nat)).insert 5 3).contains 5 = true := by
  conv =>
    lhs
    cbv

@[cbv_opaque] def opaque_const : Nat := Nat.zero

@[cbv_eval] theorem opaque_fn_spec : opaque_const = 0 := by rfl

example : opaque_const = 0 := by conv => lhs; cbv

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
