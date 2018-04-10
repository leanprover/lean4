inductive term : Type
| var : string → term
| app : string → list term → term

def cidx : term → nat
| (term.var _)   := 1
| (term.app _ _) := 2

def to_list : term → list term
| (term.app _ ts) := ts
| (term.var _)    := []

def tid : term → string
| (term.var id)   := id
| (term.app id _) := id

lemma ex (t : term) (h : cidx t = 2) : term.app (tid t) (to_list t) = t :=
begin
  cases t,
  {simp [cidx] at h,
   have h : 1 ≠ 2, tactic.comp_val,
   contradiction},
  {simp [tid, to_list]}
end
