
opaque f [Nonempty α] (a : α) : α := a

-- Note: The following test should not generate any issues.
/--
error: `grind` failed
case grind
α : Sort u_1
a b : α
h : ¬f a = b
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] ¬f a = b
  [eqc] True propositions
    [prop] Nonempty α
  [eqc] False propositions
    [prop] f a = b
-/
#guard_msgs in
example (a b : α) :
    (haveI : Nonempty α := ⟨a⟩
     f a)
    = b := by
  grind

/--
trace: [grind.assert] @Eq α c (@f α (@Lean.Grind.nestedProof (Nonempty α) (@Nonempty.intro α a)) a)
[grind.assert] Not (@Eq α c (@f α (@Lean.Grind.nestedProof (Nonempty α) (@Nonempty.intro α b)) a))
-/
#guard_msgs in
set_option trace.grind.assert true in
set_option pp.proofs true in
set_option pp.explicit true in
example (a b c : α) :
    c = (haveI : Nonempty α := ⟨a⟩; f a)
    →
    c = (haveI : Nonempty α := ⟨b⟩; f a) := by
  grind

-- Must preserve `Grind.nestedProof`
/--
trace: [grind.assert] Nonempty α
[grind.assert] @Eq α c (@f α (@Lean.Grind.nestedProof (Nonempty α) inst) a)
[grind.assert] Not (@Eq α c (@f α (@Lean.Grind.nestedProof (Nonempty α) inst) a))
-/
#guard_msgs in
set_option trace.grind.assert true in
set_option pp.proofs true in
set_option pp.explicit true in
example [Nonempty α] (a b c : α) :
    c = (haveI : Nonempty α := ⟨a⟩; f a)
    →
    c = (haveI : Nonempty α := ⟨b⟩; f a) := by
  grind
