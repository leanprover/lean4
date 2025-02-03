structure Tree (α : Type) where
  cs : List (Tree α)

def Tree.revrev : (n : Nat) → (t : Tree α) → Tree α
  | 0, t => t
  | n + 1, Tree.mk cs => revrev n (Tree.mk (cs.attach.map (fun ⟨x, h⟩ => x.revrev (n + 1))))
termination_by n t => (n, t)
decreasing_by
  · apply Prod.Lex.right
    simp
    have := List.sizeOf_lt_of_mem h
    omega
  · apply Prod.Lex.left
    decreasing_tactic


-- set_option trace.Meta.FunInd true

-- The induction principle here should have two IHs in the second case, and none mentioning `x.val`

/--
info: Tree.revrev.induct {α : Type} (motive : Nat → Tree α → Prop) (case1 : ∀ (t : Tree α), motive 0 t)
  (case2 :
    ∀ (n : Nat) (cs : List (Tree α)),
      (∀ (x : Tree α), x ∈ cs → motive (n + 1) x) →
        motive n
            {
              cs :=
                List.map
                  (fun x =>
                    match x with
                    | ⟨x, h⟩ => Tree.revrev (n + 1) x)
                  cs.attach } →
          motive n.succ { cs := cs })
  (n : Nat) (t : Tree α) : motive n t
-/
#guard_msgs in
#check Tree.revrev.induct
