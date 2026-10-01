abbrev Sequent : Type := List Nat
abbrev History : Type := List Sequent
def rep (H : History) (N : Sequent) : Prop := N ∈ H
def Sequent.basic (N : Sequent) := N = [1,2,3]
def LocalTableau (X : Sequent) : Type := Subtype (· = X.sum)
def endNodesOf {X} : LocalTableau X → List Sequent := fun _ => [X,X]

inductive Tableau : History → Sequent → Type
  | loc {Hist X} (nrep : ¬ rep Hist X) (nbas : ¬ X.basic) (lt : LocalTableau X)
            (next : ∀ Y ∈ endNodesOf lt, Tableau (X :: Hist) Y) : Tableau Hist X

-- the new `DecidableEq` does not support injectivity in the result type, i.e.
-- being able to omit comparing `nrep`, `nbas`, `lt` and `next`
set_option backward.deriving.comparisons.old true

inductive PathIn : ∀ {Hist X}, Tableau Hist X → Type
| nil : PathIn _
| loc {nrep nbas lt next Y} (Y_in : Y ∈ endNodesOf lt) (tail : PathIn (next Y Y_in))
    : PathIn (Tableau.loc nrep nbas lt next)
deriving DecidableEq
