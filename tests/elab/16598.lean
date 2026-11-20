/-! Ensures `isMajorProof` functions correctly on nested recursors.
  See https://github.com/leanprover/lean4/issues/16598.-/

inductive T where
  | node (cs : List T)

mutual
  def T.size : T → Nat
    | .node cs => T.sizes cs + 1
  def T.sizes : List T → Nat
    | [] => 0
    | t :: ts => t.size + T.sizes ts
end

theorem t : T.sizes ([.node []].map id) = 1 := rfl
