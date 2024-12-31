set_option trace.grind.ematch.pattern true
grind_pattern Array.get_set_eq  => a.set i v h
grind_pattern Array.get_set_ne => (a.set i v hi)[j]

-- Trace instances of the theorems above found using ematching

set_option trace.grind.ematch.instance true

/--
info: [grind.ematch.instance] Array.get_set_eq : [α, bs, j, w, Lean.Grind.nestedProof (j < bs.toList.length) h₂]
[grind.ematch.instance] Array.get_set_eq : [α, as, i, v, Lean.Grind.nestedProof (i < as.toList.length) h₁]
[grind.ematch.instance] Array.get_set_ne : [α, bs, j, Lean.Grind.nestedProof (j < bs.toList.length) h₂, i, w, _, _]
-/
#guard_msgs (info) in
example (as : Array α)
        (i : Nat)
        (h₁ : i < as.size)
        (h₂ : bs = as.set i v)
        (_  : ds = bs)
        (h₂ : j < bs.size)
        (h₃ : cs = bs.set j w)
        (h₄ : i ≠ j)
        (h₅ : i < cs.size)
        : p ↔ (cs[i] = as[i]) := by
  fail_if_success grind
  sorry

opaque R : Nat → Nat → Prop
theorem Rtrans (a b c : Nat) : R a b → R b c → R a c := sorry

grind_pattern Rtrans => R a b, R b c

/--
info: [grind.ematch.instance] Rtrans : [b, c, d, _, _]
[grind.ematch.instance] Rtrans : [a, b, c, _, _]
-/
#guard_msgs (info) in
example : R a b → R b c → R c d → False := by
  fail_if_success grind
  sorry

-- In the following test we are performing one round of ematching only
/--
info: [grind.ematch.instance] Rtrans : [c, d, e, _, _]
[grind.ematch.instance] Rtrans : [c, d, n, _, _]
[grind.ematch.instance] Rtrans : [b, c, d, _, _]
[grind.ematch.instance] Rtrans : [a, b, c, _, _]
-/
#guard_msgs (info) in
example : R a b → R b c → R c d → R d e → R d n → False := by
  fail_if_success grind
  sorry
