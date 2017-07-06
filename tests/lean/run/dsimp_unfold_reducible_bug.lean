open tactic

example ( a b : nat → nat ) ( p : (a ∘ b) 0 = 0 ) : a ( b 0 ) = 0 :=
begin
  dsimp [function.comp] at p,
  (do t ← get_local `p >>= infer_type, e ← to_expr ```(a (b 0) = 0), guard (t = e)),
  assumption
end

example ( a b : nat → nat ) ( p : (a ∘ b) 0 = 0 ) : a ( b 0 ) = 0 :=
begin
  dsimp at p {unfold_reducible := tt},
  (do t ← get_local `p >>= infer_type, e ← to_expr ```(a (b 0) = 0), guard (t = e)),
  assumption
end

example ( a b : nat → nat ) ( p : (a ∘ b) 0 = 0 ) : a (b 0)  = 0 :=
begin
  dsimp at p {unfold_reducible := tt, single_pass := tt},
  (do t ← get_local `p >>= infer_type, e ← to_expr ```(a (b 0) = 0), guard (t = e)),
  assumption
end
