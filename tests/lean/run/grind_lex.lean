module
-- From Mathlib.Data.List.Defs
-- These needed `attribute [grind =] Prod.lex_def`

theorem List.permutationsAux.rec.extracted_1 {α : Type u_1} (ts is : List α) :
  Prod.Lex (fun x1 x2 ↦ x1 < x2) (fun x1 x2 ↦ x1 < x2) (ts.length + (is.length + 1), ts.length)
    (ts.length + 1 + is.length, ts.length + 1) := by
  grind

theorem List.permutationsAux.rec.extracted_4 {α : Type u_1} (ts is : List α) :
  Prod.Lex (fun x1 x2 ↦ x1 < x2) (fun x1 x2 ↦ x1 < x2) (is.length, is.length)
    (ts.length + 1 + is.length, ts.length + 1) := by
  grind
