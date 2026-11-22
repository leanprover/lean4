/-!
The `Sym.simp`-based `grind` normalizer must not eta-reduce `fun x y => x + y` to the partial
application `HAdd.hAdd`: `grind` instantiates `f a = b[x := a]` from `f = fun x => b` only when
the equivalence class of `f` contains a lambda.
-/
set_option backward.grind.normalizer false
set_option warn.sorry false

example (f : Nat → Nat → Nat) : f 2 3 ≠ 5 → f = (fun x y : Nat => x + y) → False := by
  grind

def g (x : Nat) : Nat → Nat → Nat :=
  match x with
  | 0 => fun _ _ => 0
  | _+1 => fun a b => a + b

example : g (a+1) b c = b + c := by
  grind [g]

example (p : (Nat → Nat → Nat) → Prop) : p (fun x y => x + y) := by
  grind_norm sym; guard_target =ₛ p (fun x y => x + y); sorry

example (p : (Nat → Nat) → Prop) (h : Nat → Nat → Nat) (a : Nat) : p (fun x => h a x) := by
  grind_norm sym; guard_target =ₛ p (fun x => h a x); sorry
