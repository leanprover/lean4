/-! This tests demonstrates where and how wf preprocessing leaks to the user -/

structure Tree (α : Type) where
  cs : List (Tree α)

def Tree.isLeaf (t : Tree α) := t.cs.isEmpty

-- The `cs.map` in the outer call to `revrev` gets the `attach`-attaching treatment and shows up in
-- the proof state:

/--
info: α : Type
n : Nat
cs : List (Tree α)
x✝ :
  (y : (_ : Nat) ×' Tree α) →
    (invImage (fun x => PSigma.casesOn x fun n t => (n, t)) Prod.instWellFoundedRelation).1 y ⟨n.succ, { cs := cs }⟩ →
      Tree α
⊢ Prod.Lex (fun a₁ a₂ => a₁ < a₂) (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (n, { cs := List.map (fun x => x✝ ⟨n + 1, x.val⟩ ⋯) cs.attach }) (n.succ, { cs := cs })
-/
#guard_msgs in
def Tree.revrev : (n : Nat) → (t : Tree α) → Tree α
  | 0, t => t
  | n + 1, Tree.mk cs => revrev n (Tree.mk (cs.map (·.revrev (n + 1))))
termination_by n t => (n, t)
decreasing_by
  · apply Prod.Lex.right
    simp
    have := List.sizeOf_lt_of_mem ‹_ ∈ _›
    omega
  · trace_state
    apply Prod.Lex.left
    decreasing_tactic

-- as well as in the induction principle:

-- set_option trace.Meta.FunInd true

/--
info: Tree.revrev.induct {α : Type} (motive : Nat → Tree α → Prop) (case1 : ∀ (t : Tree α), motive 0 t)
  (case2 :
    ∀ (n : Nat) (cs : List (Tree α)),
      (∀ (x : Tree α), x ∈ cs → motive (n + 1) x) →
        (∀ (x : Subtype (Membership.mem cs)), motive (n + 1) x.val) →
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

-- Tangent: Why three IHs here? Because in the termination proof, the `
--    match x with | ⟨x, h⟩ => Tree.revrev (n + 1) x)
-- was replaced by
--    Tree.revrev (n + 1) ↑x
-- (maybe due to split/simpMatch) and funind picks up that recursive call as a separate one.
-- See
-- set_option pp.proofs true in #print Tree.revrev._unary
-- set_option pp.proofs true in #print Tree.revrev._unary.proof_3


-- It does not show up in the equational theorems:

/--
info: equations:
theorem Tree.revrev.eq_1 : ∀ {α : Type} (x : Tree α), Tree.revrev 0 x = x
theorem Tree.revrev.eq_2 : ∀ {α : Type} (n : Nat) (cs : List (Tree α)),
  Tree.revrev n.succ { cs := cs } = Tree.revrev n { cs := List.map (fun x => Tree.revrev (n + 1) x) cs }
-/
#guard_msgs in
#print equations Tree.revrev

theorem sizeOf_map {α β : Type} [SizeOf α] [SizeOf β]
    (f : α → β) (xs : List α) (hf : ∀ x, x ∈ xs → sizeOf (f x) = sizeOf x) :
    sizeOf (List.map f xs) = sizeOf xs := by
  induction xs with
  | nil =>
    simp
  | cons x xs ih =>
    simp [List.map]
    simp [hf]
    apply ih
    intro x hx
    apply hf
    apply List.mem_cons.2
    exact Or.inr hx


-- Lets see how tedious it is to use the functional induction principle:
example (n : Nat) (t : Tree α) : sizeOf (Tree.revrev n t) = sizeOf t := by
  induction n, t using Tree.revrev.induct with
  | case1 =>
    simp [Tree.revrev]
  | case2 n cs ih1 ih2 ih3 =>
    simp [Tree.revrev]
    simp only [Subtype.forall, List.map_subtype, List.unattach_attach, Tree.mk.sizeOf_spec] at *
    rw [ih3]; clear ih3
    rw [sizeOf_map]
    · assumption
