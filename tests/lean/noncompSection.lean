noncomputable section

theorem ex : ∃ x : Nat, x > 0 :=
  ⟨1, by decide⟩

def a : Nat := Classical.choose ex

def b : Nat := 0

abbrev c : Nat := Classical.choose ex

abbrev d : Nat := 1

instance e : Inhabited Nat :=
 ⟨a⟩

instance f : Inhabited Nat :=
 ⟨b⟩

#eval b + d + f.default

section Foo

def g : Nat := Classical.choose ex

def h (x : Nat) : Nat :=
  match x with
  | 0 => a
  | x+1 => h x + 1

end Foo

end

def i : Nat := Classical.choose ex -- Error
