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
info: equations:
@[defeq] theorem plus.eq_1 : ∀ {Γ : Context} {a : Ty} (i : Lookup Γ a), plus (Term.var i) = Term.var i
@[defeq] theorem plus.eq_2 : ∀ {Γ : Context} {a : Ty} (n : Term ( ✶ :: Γ) ✶ ), plus n.lam = (plus n).lam
@[defeq] theorem plus.eq_3 : ∀ {Γ : Context} {a : Ty} (a_1 : Term ( ✶ :: Γ) ✶ ) (m : Term Γ ✶ ),
  plus (a_1.lam.ap m) = plus m
theorem plus.eq_4 : ∀ {Γ : Context} {a : Ty} (l m : Term Γ ✶ ),
  (∀ (a : Term ( ✶ :: Γ) ✶ ), l = a.lam → False) → plus (l.ap m) = (plus l).ap (plus m)
-/
#guard_msgs in
#print equations plus
