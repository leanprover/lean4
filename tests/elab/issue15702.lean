/-!
Regression test for #15702: `fun_cases` and `induct` failed with a kernel error when a function
matches with a named pattern on a literal or on a constructor without arguments.
-/

def g : Nat → Nat
  | n@5 => n
  | _ => 0

/--
info: g.fun_cases : ∀ (motive : Nat → Prop), motive 5 → (∀ (x : Nat), (x = 5 → False) → motive x) → ∀ (x : Nat), motive x
-/
#guard_msgs in
#check @g.fun_cases

example (x : Nat) : g x ≤ 5 := by
  fun_cases g x <;> simp_all

def gi : Int → Int
  | n@5 => n
  | _ => 0

example (x : Int) : gi x ≤ 5 := by
  fun_cases gi x <;> simp_all

def gs : String → String
  | s@"a" => s
  | _ => "b"

example (x : String) : gs x ≠ "" := by
  fun_cases gs x <;> simp_all

def gc : Char → Nat
  | c@'a' => c.toNat
  | _ => 0

example (x : Char) : gc x ≤ 97 := by
  fun_cases gc x <;> simp_all

def gb : Bool → Nat
  | b@true => b.toNat
  | _ => 0

example (x : Bool) : gb x ≤ 1 := by
  fun_cases gb x <;> simp_all

def go : Option Nat → Nat
  | o@none => o.getD 5
  | _ => 0

example (x : Option Nat) : go x ≤ 5 := by
  fun_cases go x <;> simp_all

def g2 : Nat → Nat → Nat
  | _, 7 => 2
  | 3, m@5 => m
  | _, _ => 0

example (x y : Nat) : g2 x y ≤ 5 := by
  fun_cases g2 x y <;> simp_all

def r : Nat → Nat
  | n@5 => n
  | n+1 => r n
  | 0 => 0

/--
info: r.induct : ∀ (motive : Nat → Prop),
  motive 5 → (∀ (n : Nat), (n = 4 → False) → motive n → motive n.succ) → motive 0 → ∀ (a : Nat), motive a
-/
#guard_msgs in
#check @r.induct

example (x : Nat) : r x ≤ 5 := by
  fun_induction r x <;> simp_all
