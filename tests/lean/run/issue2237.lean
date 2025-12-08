inductive Ty where
| star: Ty
notation " ✶ " => Ty.star

abbrev Context : Type := List Ty

inductive Lookup : Context → Ty → Type where
| z : Lookup (t :: Γ) t

inductive Term : Context → Ty → Type where
| var : Lookup Γ a → Term Γ a
| lam : Term (✶ :: Γ) ✶ → Term Γ ✶
| ap : Term Γ ✶ → Term Γ ✶ → Term Γ ✶

abbrev plus : Term Γ a → Term Γ a
| .var i => .var i
| .lam n => .lam (plus n)
| .ap (.lam _) m => plus m -- This case takes precedence over the next one.
| .ap l m => (plus l).ap (plus m)

/--
error: failed to generate equational theorem for `plus`
  Application type mismatch: The argument
    l.ap m
  has type
    Term Γ ✶
  but is expected to have type
    Term Γ a
  in the application
    @HEq (Term Γ a) (l.ap m)
-/
#guard_msgs in
#print equations plus


/--
error: Failed to realize constant plus.match_1.eq_1:
  Application type mismatch: The argument
    l.ap m
  has type
    Term Γ ✶
  but is expected to have type
    Term Γ a
  in the application
    @HEq (Term Γ a) (l.ap m)
---
error: Unknown constant `plus.match_1.eq_1`
-/
#guard_msgs in #print sig plus.match_1.eq_1

/--
error: Failed to realize constant plus.match_1.congr_eq_1:
  Tactic `subst` failed: did not find equation for eliminating 'heq✝'
  ⏎
  Γ : Context
  a : Ty
  x✝ : Term Γ a
  l m : Term Γ ✶
  heq✝ : x✝ ≍ l.ap m
  ⊢ (∀ (a_1 : Term ( ✶ :: Γ) ✶ ) (m_1 : Term Γ ✶ ), l.ap m ≍ a_1.lam.ap m_1 → False) →
      ∀ (a_1 : Term ( ✶ :: Γ) ✶ ) (m : Term Γ ✶ ), x✝ ≍ a_1.lam.ap m → False
---
error: Unknown constant `plus.match_1.congr_eq_1`
-/
#guard_msgs in #print sig plus.match_1.congr_eq_1
