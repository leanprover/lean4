abbrev Word := List Nat
abbrev Alphabet := Nat

inductive Regex where
  | none: Regex

axiom inter: Regex → (Word → Prop)
axiom concatenate (a b: Word → Prop) : (Word → Prop)
axiom eps: Word → Prop

def conc (a: Array Regex) (i: Nat): Word → Prop :=
  if h: i < a.size then
    concatenate (inter a[i]) (conc a (i + 1))
  else
    eps

/--
info: conc.induct (a : Array Regex) (motive : Nat → Prop) (case1 : ∀ (x : Nat), x < a.size → motive (x + 1) → motive x)
  (case2 : ∀ (x : Nat), ¬x < a.size → motive x) (i : Nat) : motive i
-/
#guard_msgs in
#check conc.induct
