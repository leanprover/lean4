-- Port of Lean 3 code by Oliver Nash
-- https://gist.github.com/ocfnash/fb61a17d0f1598edcc752999f17b70c6

import Lean.Widget.ToHtmlFormat

open Lean.Widget (ToHtmlFormat Html)

def List.product : List α → List β → List (α × β)
  | [], _     => []
  | a::as, bs => bs.map ((a, ·)) ++ as.product bs

def Matrix (n m α : Type) := n → m → α

namespace Matrix

variable {n : Nat} (A : Matrix (Fin n) (Fin n) Int)

def nat_index (i j : Nat) : Int :=
  if h : i < n ∧ j < n then A ⟨i, h.1⟩ ⟨j, h.2⟩ else 999

/-- TODO Delete me once `get_node_pos` smart enough to infer layout from values in `A`. -/
def get_node_pos_E : Nat → Nat × Nat
  | 0     => ⟨0, 0⟩
  | 1     => ⟨2, 1⟩
  | (i+1) => ⟨i, 0⟩

/-- TODO Use `A` to infer sensible layout. -/
def get_node_pos (n : Nat) : Nat → Nat × Nat := if n < 6 then ((·, 0)) else get_node_pos_E

def get_node_cx (n i : Nat) : Int := 20 + (get_node_pos n i).1 * 40

def get_node_cy (n i : Nat) : Int := 20 + (get_node_pos n i).2 * 40

def get_node_html (n i : Nat) : Html :=
  <circle
    cx={toString <| get_node_cx n i}
    cy={toString <| get_node_cy n i}
    r="10"
    fill="white"
    stroke="black" />

/-- TODO
 * Error if `j ≤ i`
 * Error if `(A i j, A j i) ∉ [((0 : Int), (0 : Int)), (-1, -1), (-1, -2), (-2, -1), (-1, -3), (-3, -1)]`
 * Render `(A i j) * (A j i)` edges
 * Render arrow on double or triple edge with direction decided by `A i j < A j i` -/
def get_edge_html : Nat × Nat → List Html
  | (i, j) => if A.nat_index i j = 0 then [] else
  [<line
     x1={toString <| get_node_cx n i}
     y1={toString <| get_node_cy n i}
     x2={toString <| get_node_cx n j}
     y2={toString <| get_node_cy n j}
     fill="black"
     stroke="black" />]

def get_nodes_html (n : Nat) : List Html :=
  (List.range n).map (get_node_html n)

def get_edges_html : List Html := do
  let mut out := []
  for j in [:n] do
    for i in [:j] do
      out := A.get_edge_html (i, j) ++ out
  return out

end Matrix

def cartanMatrix.E₈ : Matrix (Fin 8) (Fin 8) Int :=
  fun i j =>
    [[ 2,  0, -1,  0,  0,  0,  0,  0],
     [ 0,  2,  0, -1,  0,  0,  0,  0],
     [-1,  0,  2, -1,  0,  0,  0,  0],
     [ 0, -1, -1,  2, -1,  0,  0,  0],
     [ 0,  0,  0, -1,  2, -1,  0,  0],
     [ 0,  0,  0,  0, -1,  2, -1,  0],
     [ 0,  0,  0,  0,  0, -1,  2, -1],
     [ 0,  0,  0,  0,  0,  0, -1,  2]].get! i |>.get! j

instance : ToHtmlFormat (Matrix (Fin n) (Fin n) Int) where
  formatHtml M :=
    <div style="height: 100px; width: 300px; background: grey">
      {Html.element "svg" #[] (M.get_edges_html ++ Matrix.get_nodes_html n).toArray}
    </div>

#check cartanMatrix.E₈
