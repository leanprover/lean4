/-!
Regression test for #6332
-/

open Function (uncurry)
open Std.Legacy (Range)

section Matrix

  structure Matrix (α) where
    array : Array α
    width : Nat
  deriving
    BEq, DecidableEq, Hashable, Inhabited, Nonempty, Repr

  instance : GetElem (Matrix α) (Nat × Nat) α
    (fun mat (i, j) => i * mat.width + j < mat.array.size)
  where
    getElem
    | mat, (i, j), h => mat.array[i * mat.width + j]

  instance : GetElem? (Matrix α) (Nat × Nat) α
    (fun mat (i, j) => i * mat.width + j < mat.array.size)
  where
    getElem?
    | mat, (i, j) => mat.array[i * mat.width + j]?
    getElem!
    | mat, (i, j) => mat.array[i * mat.width + j]!

  namespace Matrix
    def height (mat : Matrix α) := mat.array.size / mat.width

    def set! [Inhabited α] (mat : Matrix α) : Nat × Nat -> α -> Matrix α
    | (i, j), x => Matrix.mk (mat.array.set! (i * mat.width + j) x) mat.width
  end Matrix

end Matrix

section Prod

  instance [HAdd α1 β1 γ1] [HAdd α2 β2 γ2]
  : HAdd (α1 × α2) (β1 × β2) (γ1 × γ2) where
    hAdd := fun (a1, a2) (b1, b2) => (a1 + b1, a2 + b2)

  instance [HSub α1 β1 γ1] [HSub α2 β2 γ2]
  : HSub (α1 × α2) (β1 × β2) (γ1 × γ2) where
    hSub := fun (a1, a2) (b1, b2) => (a1 - b1, a2 - b2)

  instance [HAdd α1 β γ1] [HAdd α2 β γ2]
  : HAdd (α1 × α2) β (γ1 × γ2) where
    hAdd := fun (a1, a2) b => (a1 + b, a2 + b)

  instance [HSub α1 β γ1] [HSub α2 β γ2]
  : HSub (α1 × α2) β (γ1 × γ2) where
    hSub := fun (a1, a2) b => (a1 - b, a2 - b)

  instance [Membership α1 γ1] [Membership α2 γ2]
  : Membership (α1 × α2) (γ1 × γ2) where
    mem | (xs, ys), (x, y) => x ∈ xs /\ y ∈ ys

  instance [Membership α1 γ1] [Membership α2 γ2]
    (pair : α1 × α2) (coll : γ1 × γ2)
    [Decidable (pair.fst ∈ coll.fst)]
    [Decidable (pair.snd ∈ coll.snd)]
  : Decidable (pair ∈ coll) :=
    inferInstanceAs (Decidable (pair.fst ∈ coll.fst /\ pair.snd ∈ coll.snd))

end Prod

section Offset

  @[unbox]
  structure Offset where
    inner : Int
  deriving
    BEq, DecidableEq, Hashable, Inhabited,
    Nonempty, Ord, TypeName

  instance : ToString Offset where
    toString a := toString a.inner

  instance (n : Nat) : OfNat Offset n where
    ofNat := Offset.mk $ Int.ofNat n

  instance : Neg Offset where
    neg a := Offset.mk $ -a.inner

  instance : HSub Nat Offset Nat where
    hSub a b := match b.inner with
      | .ofNat b => a - b
      | .negSucc b => a + b.succ

end Offset

section Range

  instance : ToString Range where
    toString r := s!"[{r.start}:{r.stop}:{r.step}]"

  instance : Membership Nat Range where
    mem r i := r.start <= i && i < r.stop && (i - r.start) % r.step == 0

  instance (i : Nat) (r : Range) : Decidable (i ∈ r) :=
    inferInstanceAs (Decidable (r.start <= i && i < r.stop && (i - r.start) % r.step == 0))

  instance : HAdd Range Nat Range where
    hAdd r d := { r with start := r.start + d, stop := r.stop + d }

end Range

namespace Prod

  @[inline]
  def turnRight : Offset × Offset -> Offset × Offset
  | (di, dj) => (dj, -di)

  @[inline]
  def turnLeft : Offset × Offset -> Offset × Offset
  | (di, dj) => (-dj, di)

end Prod

inductive Tile
| space
| obstruction
| path (step : Nat)
deriving Inhabited, BEq

open Tile

def solve (mat : Matrix Tile) (guard : Nat × Nat) : IO Unit := do
  let mut mat := mat
  let mut pos := guard + (1 : Nat)
  let mut dir : Offset × Offset := (-1, 0)
  while pos ∈ borders do
    match mat[pos - (1 : Nat)]! with
    | obstruction =>
      pos := pos - dir
      dir := dir.turnRight
    | _ => pure ()
    let orig := mat[pos - (1 : Nat)]!
    mat := mat.set! (pos - (1 : Nat)) obstruction
    _ <- searchLoop pos dir.turnLeft
    mat := mat.set! (pos - (1 : Nat)) orig
    break
where
  borders := ([:mat.height], [:mat.width]) + 1
  searchLoop (pos : Nat × Nat) (dir : Offset × Offset) := do
    let mut pos := pos
    println!"{pos}"
    println!"{dir}"
    println!"{borders}"
    let mut i := 0
    -- segfault
    while pos ∈ borders do
      println!"{pos}"
      pos := pos - dir
      i := i + 1
    pure false

def main := do
  _ <- solve (
    Matrix.mk (Array.range 100 |>.map fun _ => space) 10
  ) (6, 4)

/--
info: (7, 5)
(0, -1)
([1:11:1], [1:11:1])
(7, 5)
(7, 6)
(7, 7)
(7, 8)
(7, 9)
(7, 10)
-/
#guard_msgs in
#eval! main
