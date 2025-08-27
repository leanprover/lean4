open Lean Grind AC
example {α : Type u} (op : α → α → α) [Std.Associative op] (a b c : α)
    : op a (op b c) = op (op a b) c := by
  grind only

example {α : Sort u} (op : α → α → α) [Std.Associative op] (a b c : α)
    : op a (op b c) = op (op a b) c := by
  grind only

example {α : Sort u} (op : α → α → α) (u : α) [Std.Associative op] [Std.LawfulIdentity op u] (a b c : α)
    : op a (op b c) = op (op a b) (op c u) := by
  grind only

example {α : Sort u} (op : α → α → α) [Std.Associative op] [Std.Commutative op] (a b c : α)
    : op c (op b a) = op (op b a) c := by
  grind only

example {α : Sort u} (op : α → α → α) (u : α) [Std.Associative op] [Std.Commutative op] [Std.LawfulIdentity op u] (a b c : α)
    : op a (op b c) = op (op b a) c := by
  grind only

example {α : Sort u} (op : α → α → α) (u : α) [Std.Associative op] [Std.Commutative op] [Std.LawfulIdentity op u] (a b c : α)
    : op a (op b (op u c)) = op (op b a) (op u c) := by
  grind only

example {α : Sort u} (op : α → α → α) [Std.Associative op] [Std.IdempotentOp op] (a b c : α)
    : op (op a a) (op b c) = op (op a (op b b)) c := by
  grind only

example {α : Sort u} (op : α → α → α) [Std.Associative op] [Std.Commutative op] [Std.IdempotentOp op] (a b c : α)
    : op (op a a) (op b c) = op (op (op b a) (op b b)) c := by
  grind only

example {α : Sort u} (op : α → α → α) (u : α) [Std.Associative op] [Std.Commutative op] [Std.IdempotentOp op] [Std.LawfulIdentity op u] (a b c : α)
    : op (op a a) (op b c) = op (op (op b a) (op (op u b) b)) c := by
  grind only

example {α : Type u} (op : α → α → α) [Std.Associative op] [Std.Commutative op] [Std.IdempotentOp op] (a b c : α)
    : op (op a a) (op b c) = op (op (op b a) (op b b)) c := by
  grind only

example {α : Type u} (op : α → α → α) (u : α) [Std.Associative op] [Std.Commutative op] [Std.IdempotentOp op] [Std.LawfulIdentity op u] (a b c : α)
    : op (op a a) (op b c) = op (op (op b a) (op (op u b) b)) c := by
  grind only

example {α} (as bs cs : List α) : as ++ (bs ++ cs) = ((as ++ []) ++ bs) ++ (cs ++ []) := by
  grind only

example (a b c : Nat) : max a (max b c) = max (max b 0) (max a c) := by
  grind only

/--
trace: [grind.debug.proof] Classical.byContradiction
      (intro_with_eq (¬(max a (max b c) = max (max b 0) (max a c) ∧ min a b = min b a))
        (¬max a (max b c) = max (max b 0) (max a c) ∨ ¬min a b = min b a) False
        (Grind.not_and (max a (max b c) = max (max b 0) (max a c)) (min a b = min b a)) fun h =>
        Or.casesOn h
          (fun h_1 =>
            let ctx :=
              Context.mk
                (RArray.branch 2 (RArray.branch 1 (RArray.leaf (PLift.up 0)) (RArray.leaf (PLift.up a)))
                  (RArray.branch 3 (RArray.leaf (PLift.up b)) (RArray.leaf (PLift.up c))))
                max;
            let e_1 := ((Expr.var 2).op (Expr.var 0)).op ((Expr.var 1).op (Expr.var 3));
            let e_2 := (Expr.var 1).op ((Expr.var 2).op (Expr.var 3));
            let p_1 := Seq.cons 1 (Seq.cons 2 (Seq.var 3));
            diseq_unsat ctx p_1 p_1 (eagerReduce (Eq.refl true))
              (diseq_norm_aci ctx e_2 e_1 p_1 p_1 (eagerReduce (Eq.refl true)) h_1))
          fun h_1 =>
          let ctx := Context.mk (RArray.branch 1 (RArray.leaf (PLift.up a)) (RArray.leaf (PLift.up b))) min;
          let e_1 := (Expr.var 1).op (Expr.var 0);
          let e_2 := (Expr.var 0).op (Expr.var 1);
          let p_1 := Seq.cons 0 (Seq.var 1);
          diseq_unsat ctx p_1 p_1 (eagerReduce (Eq.refl true))
            (diseq_norm_ac ctx e_2 e_1 p_1 p_1 (eagerReduce (Eq.refl true)) h_1))
-/
#guard_msgs in
set_option pp.structureInstances false in
set_option trace.grind.debug.proof true in
example (a b c : Nat) : max a (max b c) = max (max b 0) (max a c) ∧ min a b = min b a := by
  grind only [cases Or]
