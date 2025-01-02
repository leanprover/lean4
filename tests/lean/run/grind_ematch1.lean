set_option trace.grind.ematch.pattern true
grind_pattern Array.size_set => Array.set a i v h

set_option grind.debug true

example (as bs : Array α) (v : α)
        (i : Nat)
        (h₁ : i < as.size)
        (h₂ : bs = as.set i v)
        : as.size = bs.size := by
  grind

example (as bs : Array α) (v : α)
        (i : Nat)
        (h₁ : i < as.size)
        (h₂ : bs = as.set i v)
        : as.size = bs.size := by
  have : as.size = bs.size := by
    grind
  exact this

set_option trace.grind.ematch.instance true

grind_pattern Array.get_set_eq  => a.set i v h
grind_pattern Array.get_set_ne => (a.set i v hi)[j]

/--
info: [grind.ematch.instance] Array.get_set_eq: (as.set i v ⋯)[i] = v
[grind.ematch.instance] Array.size_set: (as.set i v ⋯).size = as.size
[grind.ematch.instance] Array.get_set_ne: ∀ (hj : j < as.size), i ≠ j → (as.set i v ⋯)[j] = as[j]
-/
#guard_msgs (info) in
example (as bs cs : Array α) (v : α)
        (i : Nat)
        (h₁ : i < as.size)
        (h₂ : bs = as.set i v)
        (h₃ : cs = bs)
        (h₄ : i ≠ j)
        (h₅ : j < cs.size)
        (h₆ : j < as.size)
        : cs[j] = as[j] := by
  grind


opaque R : Nat → Nat → Prop
theorem Rtrans (a b c : Nat) : R a b → R b c → R a c := sorry

grind_pattern Rtrans => R a b, R b c

/--
info: [grind.ematch.instance] Rtrans: R a b → R b c → R a c
-/
#guard_msgs (info) in
example : R a b → R b c → R a c := by
  grind


/--
info: [grind.ematch.instance] Rtrans: R a d → R d e → R a e
[grind.ematch.instance] Rtrans: R c d → R d e → R c e
[grind.ematch.instance] Rtrans: R b c → R c d → R b d
[grind.ematch.instance] Rtrans: R a b → R b c → R a c
[grind.ematch.instance] Rtrans: R a c → R c d → R a d
[grind.ematch.instance] Rtrans: R a c → R c e → R a e
[grind.ematch.instance] Rtrans: R b d → R d e → R b e
[grind.ematch.instance] Rtrans: R a b → R b d → R a d
[grind.ematch.instance] Rtrans: R b c → R c e → R b e
-/
#guard_msgs (info) in
example : R a b → R b c → R c d → R d e → R a d := by
  grind
