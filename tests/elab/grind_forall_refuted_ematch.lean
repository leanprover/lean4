/-!
`grind` proof from the λ-calculus development reported in leanprover/cslib#1141 (the
`append_singleton` case of `multiapp_headneutral` after `simp`). The universally quantified
antecedent of `ih` is refuted by propagation, which introduces the witness `w ∈ l`, `¬ LC w`.
The E-matching round counter must be reset at that point, as it is after a case split, since the
witness needs two more rounds (`h_lc w` and `List.mem_append`).
-/

inductive Term where
  | fvar : String → Term
  | app  : Term → Term → Term

namespace Term

inductive LC : Term → Prop
  | fvar (x : String) : LC (fvar x)
  | app {l r} : LC l → LC r → LC (app l r)

attribute [grind .] LC.fvar LC.app

@[grind]
inductive HeadNeutral : Term → Prop
  | fvar (x : String) : HeadNeutral (fvar x)
  | app {M N : Term} : HeadNeutral M → LC N → HeadNeutral (app M N)

example (l : List Term) (a : Term) (x : String)
    (ih : (∀ t ∈ l, LC t) → HeadNeutral (List.foldl app (fvar x) l))
    (h_lc : ∀ t ∈ l ++ [a], LC t) :
    HeadNeutral (app (List.foldl app (fvar x) l) a) := by
  grind

end Term
