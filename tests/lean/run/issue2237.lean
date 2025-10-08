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
  failed to generate equality theorems for `match` expression `plus.match_1`
  Γ✝ : Context
  a✝ : Ty
  motive✝ : Term Γ✝ a✝ → Sort u_1
  n✝ : Term ( ✶ :: Γ✝) ✶
  h_1✝ : (i : Lookup Γ✝ a✝) → motive✝ (Term.var i)
  h_2✝ : (n : Term ( ✶ :: Γ✝) ✶ ) → motive✝ n.lam
  h_3✝ : (a : Term ( ✶ :: Γ✝) ✶ ) → (m : Term Γ✝ ✶ ) → motive✝ (a.lam.ap m)
  h_4✝ : (l m : Term Γ✝ ✶ ) → motive✝ (l.ap m)
  ⊢ (⋯ ▸ fun x motive h_1 h_2 h_3 h_4 h => ⋯ ▸ h_2 n✝) n✝.lam motive✝ h_1✝ h_2✝ h_3✝ h_4✝ ⋯ = h_2✝ n✝
-/
#guard_msgs in
#print equations plus
