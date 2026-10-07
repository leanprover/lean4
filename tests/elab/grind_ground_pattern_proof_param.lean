module

/-!
A `grind` hint whose only hole is a proof parameter (`h _ _ ⋯` below) used to be activated
through the ground-pattern path with the parameter's free variable left inside the nested
proofs of the pattern. The internalized ground term then recorded a proof mentioning that
free variable in the e-graph, which surfaced as `unknown free variable` once that proof was
used. Reported by the Mathlib adaptation of `List.pairwise_iff_forall_infix`.
-/

namespace List

#guard_msgs in
theorem test {α : Type u} {l : List α} {R : α → α → Prop} :
    l.Pairwise R ↔
      ∀ l', (h : 1 < l'.length) → l' <:+: l → R (l'.head <| by grind) (l'.getLast <| by grind) := by
  refine l.pairwise_iff_getElem.trans ⟨fun h l' hne ⟨l₁, l₂, hl⟩ ↦ ?_, fun h i j hi hj hij ↦ ?_⟩
  · grind [getElem_append_left', getElem_append_right']
  · grind [h _ _ <| List.drop_suffix i _ |>.isInfix.trans <| l.take_prefix (j + 1) |>.isInfix]

end List
