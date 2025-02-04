abbrev Multiseries : List Nat → Type
  | [] => Nat
  | _ :: _ => Int

opaque maxExp (n : Nat) (ns : List Nat) (li : List (Multiseries (n :: ns))) : Nat

/-
Previously, this lemma couldn't simplify itself, because the discrimination tree
keys were computed with `iota := false`.
Because `simp` uses `iota := true`, `Multiseries (n :: ns)` reduces to `Int`,
so the discrimination tree keys didn't match.
-/

@[simp]
axiom bad_simp_lemma (n : Nat) (ns : List Nat) : maxExp n ns [] = 8

example (n : Nat) (ns : List Nat) : maxExp n ns [] = 8 := by
  simp -- previously, simp made no progress

/-- error: simp made no progress -/
#guard_msgs in
example (n : Nat) (ns : List Nat) : maxExp n ns [] = 8 := by
  simp -iota -- previously, succeeded
