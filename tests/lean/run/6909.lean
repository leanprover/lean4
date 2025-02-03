abbrev Multiseries : List Nat → Type
  | [] => Nat
  | _ :: _ => Int

opaque maxExp (n : Nat) (ns : List Nat) (li : List (Multiseries (n :: ns))) : Nat

@[simp]
axiom bad_simp_lemma (n : Nat) (ns : List Nat) : maxExp n ns [] = 8

example (n : Nat) (ns : List Nat) : maxExp n ns [] = 8 := by
  simp -- previously, simp made no progress

example (n : Nat) (ns : List Nat) : maxExp n ns [] = 8 := by
  simp -iota -- previously, succeeded
