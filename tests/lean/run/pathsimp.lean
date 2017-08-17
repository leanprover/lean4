universes u v

inductive path {α : Type u} (a : α) : α → Type u
| refl : path a

namespace path

attribute [refl] path.refl

@[symm] def symm {α : Type u} {a b : α} (h : path a b) : path b a :=
by induction h; refl

@[trans] def trans {α : Type u} {a b c : α} (h : path a b) (h' : path b c) : path a c :=
by induction h; induction h'; refl

@[congr] def congr {α : Type u} {β : Type v} (f f' : α → β) (a a' : α)
    (hf : path f f') (ha : path a a') : path (f a) (f' a') :=
by induction hf; induction ha; refl

def mp {α β : Type u} (h : path α β) : α → β :=
by intro; induction h; assumption

open tactic expr
lemma nat_zero_add_step (n : ℕ) (h : path (0 + n) n) : path (0 + n).succ n.succ := by do
tgt ← target,

let sls := simp_lemmas.mk,
sls ← sls.add_congr `path.congr,
sls ← get_local `h >>= sls.add,
(tgt', prf) ← simplify sls [] tgt {lift_eq:=ff} `path,

prf ← mk_mapp `path.symm [none, tgt, tgt', prf],
mk_mapp `path.mp [tgt', tgt, prf] >>= apply,
reflexivity

end path