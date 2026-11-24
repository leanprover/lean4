def Family (α : Type _) (n : Nat) := Inhabited (Fin n → α)

set_option backward.elab.instanceTypes false in
def all_but_last {α} {n} (f : Family α (n + 1)) : Family α n :=
Inhabited.mk λ k => f.default ⟨k.val, Nat.lt_trans k.isLt n.lt_succ_self⟩

def all : {n : Nat} → Family Prop n → Prop
| 0, _ => True
| n + 1, f => all (all_but_last f)

set_option backward.elab.instanceTypes false in
def th : (n : Nat) → (f : Family Prop n) → Decidable (all f)
| 0, f => isTrue ⟨⟩
| n + 1, f => th n (all_but_last f)
