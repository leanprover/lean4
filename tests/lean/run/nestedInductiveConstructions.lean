/-!
Checks the `.below` and `.brecOn` constructions for nested inductives.
-/

set_option pp.universes true

namespace Ex1

inductive Tree where | node  : List Tree → Tree

/--
info: @[reducible] protected def Ex1.Tree.below.{u} : {motive_1 : Tree → Sort u} →
  {motive_2 : List.{0} Tree → Sort u} → Tree → Sort (max 1 u) :=
fun {motive_1} {motive_2} t =>
  Tree.rec.{(max 1 u) + 1} (fun a a_ih => PProd.{u, max 1 u} (motive_2 a) a_ih) PUnit.{max 1 u}
    (fun head tail head_ih tail_ih =>
      PProd.{max 1 u, max 1 u} (PProd.{u, max 1 u} (motive_1 head) head_ih)
        (PProd.{u, max 1 u} (motive_2 tail) tail_ih))
    t
-/
#guard_msgs in
#print Tree.below

/--
info: @[reducible] protected def Ex1.Tree.below_1.{u} : {motive_1 : Tree → Sort u} →
  {motive_2 : List.{0} Tree → Sort u} → List.{0} Tree → Sort (max 1 u) :=
fun {motive_1} {motive_2} t =>
  Tree.rec_1.{(max 1 u) + 1} (fun a a_ih => PProd.{u, max 1 u} (motive_2 a) a_ih) PUnit.{max 1 u}
    (fun head tail head_ih tail_ih =>
      PProd.{max 1 u, max 1 u} (PProd.{u, max 1 u} (motive_1 head) head_ih)
        (PProd.{u, max 1 u} (motive_2 tail) tail_ih))
    t
-/
#guard_msgs in
#print Tree.below_1

/--
info: Ex1.Tree.brecOn.{u} {motive_1 : Tree → Sort u} {motive_2 : List.{0} Tree → Sort u} (t : Tree)
  (F_1 : (t : Tree) → Tree.below.{u} t → motive_1 t) (F_2 : (t : List.{0} Tree) → Tree.below_1.{u} t → motive_2 t) :
  motive_1 t
-/
#guard_msgs in
#check Tree.brecOn

/--
info: Ex1.Tree.brecOn_1.{u} {motive_1 : Tree → Sort u} {motive_2 : List.{0} Tree → Sort u} (t : List.{0} Tree)
  (F_1 : (t : Tree) → Tree.below.{u} t → motive_1 t) (F_2 : (t : List.{0} Tree) → Tree.below_1.{u} t → motive_2 t) :
  motive_2 t
-/
#guard_msgs in
#check Tree.brecOn_1

end Ex1

namespace Ex2

inductive Tree where | node  : List (List Tree) → List Tree → Tree

/--
info: @[reducible] protected def Ex2.Tree.below.{u} : {motive_1 : Tree → Sort u} →
  {motive_2 : List.{0} (List.{0} Tree) → Sort u} → {motive_3 : List.{0} Tree → Sort u} → Tree → Sort (max 1 u) :=
fun {motive_1} {motive_2} {motive_3} t =>
  Tree.rec.{(max 1 u) + 1}
    (fun a a_1 a_ih a_ih_1 =>
      PProd.{max 1 u, max 1 u} (PProd.{u, max 1 u} (motive_2 a) a_ih) (PProd.{u, max 1 u} (motive_3 a_1) a_ih_1))
    PUnit.{max 1 u}
    (fun head tail head_ih tail_ih =>
      PProd.{max 1 u, max 1 u} (PProd.{u, max 1 u} (motive_3 head) head_ih)
        (PProd.{u, max 1 u} (motive_2 tail) tail_ih))
    PUnit.{max 1 u}
    (fun head tail head_ih tail_ih =>
      PProd.{max 1 u, max 1 u} (PProd.{u, max 1 u} (motive_1 head) head_ih)
        (PProd.{u, max 1 u} (motive_3 tail) tail_ih))
    t
-/
#guard_msgs in
#print Tree.below

/--
info: @[reducible] protected def Ex2.Tree.below_1.{u} : {motive_1 : Tree → Sort u} →
  {motive_2 : List.{0} (List.{0} Tree) → Sort u} →
    {motive_3 : List.{0} Tree → Sort u} → List.{0} (List.{0} Tree) → Sort (max 1 u) :=
fun {motive_1} {motive_2} {motive_3} t =>
  Tree.rec_1.{(max 1 u) + 1}
    (fun a a_1 a_ih a_ih_1 =>
      PProd.{max 1 u, max 1 u} (PProd.{u, max 1 u} (motive_2 a) a_ih) (PProd.{u, max 1 u} (motive_3 a_1) a_ih_1))
    PUnit.{max 1 u}
    (fun head tail head_ih tail_ih =>
      PProd.{max 1 u, max 1 u} (PProd.{u, max 1 u} (motive_3 head) head_ih)
        (PProd.{u, max 1 u} (motive_2 tail) tail_ih))
    PUnit.{max 1 u}
    (fun head tail head_ih tail_ih =>
      PProd.{max 1 u, max 1 u} (PProd.{u, max 1 u} (motive_1 head) head_ih)
        (PProd.{u, max 1 u} (motive_3 tail) tail_ih))
    t
-/
#guard_msgs in
#print Tree.below_1

/--
info: @[reducible] protected def Ex2.Tree.below_2.{u} : {motive_1 : Tree → Sort u} →
  {motive_2 : List.{0} (List.{0} Tree) → Sort u} →
    {motive_3 : List.{0} Tree → Sort u} → List.{0} Tree → Sort (max 1 u) :=
fun {motive_1} {motive_2} {motive_3} t =>
  Tree.rec_2.{(max 1 u) + 1}
    (fun a a_1 a_ih a_ih_1 =>
      PProd.{max 1 u, max 1 u} (PProd.{u, max 1 u} (motive_2 a) a_ih) (PProd.{u, max 1 u} (motive_3 a_1) a_ih_1))
    PUnit.{max 1 u}
    (fun head tail head_ih tail_ih =>
      PProd.{max 1 u, max 1 u} (PProd.{u, max 1 u} (motive_3 head) head_ih)
        (PProd.{u, max 1 u} (motive_2 tail) tail_ih))
    PUnit.{max 1 u}
    (fun head tail head_ih tail_ih =>
      PProd.{max 1 u, max 1 u} (PProd.{u, max 1 u} (motive_1 head) head_ih)
        (PProd.{u, max 1 u} (motive_3 tail) tail_ih))
    t
-/
#guard_msgs in
#print Tree.below_2

/--
info: Ex2.Tree.brecOn_2.{u} {motive_1 : Tree → Sort u} {motive_2 : List.{0} (List.{0} Tree) → Sort u}
  {motive_3 : List.{0} Tree → Sort u} (t : List.{0} Tree) (F_1 : (t : Tree) → Tree.below.{u} t → motive_1 t)
  (F_2 : (t : List.{0} (List.{0} Tree)) → Tree.below_1.{u} t → motive_2 t)
  (F_3 : (t : List.{0} Tree) → Tree.below_2.{u} t → motive_3 t) : motive_3 t
-/
#guard_msgs in
#check Tree.brecOn_2

end Ex2

namespace Ex3

inductive Tree : Type u where | node : List Tree → Tree

/--
info: @[reducible] protected def Ex3.Tree.below.{u_1, u} : {motive_1 : Tree.{u} → Sort u_1} →
  {motive_2 : List.{u} Tree.{u} → Sort u_1} → Tree.{u} → Sort (max 1 u_1) :=
fun {motive_1} {motive_2} t =>
  Tree.rec.{(max 1 u_1) + 1, u} (fun a a_ih => PProd.{u_1, max 1 u_1} (motive_2 a) a_ih) PUnit.{max 1 u_1}
    (fun head tail head_ih tail_ih =>
      PProd.{max 1 u_1, max 1 u_1} (PProd.{u_1, max 1 u_1} (motive_1 head) head_ih)
        (PProd.{u_1, max 1 u_1} (motive_2 tail) tail_ih))
    t
-/
#guard_msgs in
#print Tree.below

/--
info: @[reducible] protected def Ex3.Tree.below_1.{u_1, u} : {motive_1 : Tree.{u} → Sort u_1} →
  {motive_2 : List.{u} Tree.{u} → Sort u_1} → List.{u} Tree.{u} → Sort (max 1 u_1) :=
fun {motive_1} {motive_2} t =>
  Tree.rec_1.{(max 1 u_1) + 1, u} (fun a a_ih => PProd.{u_1, max 1 u_1} (motive_2 a) a_ih) PUnit.{max 1 u_1}
    (fun head tail head_ih tail_ih =>
      PProd.{max 1 u_1, max 1 u_1} (PProd.{u_1, max 1 u_1} (motive_1 head) head_ih)
        (PProd.{u_1, max 1 u_1} (motive_2 tail) tail_ih))
    t
-/
#guard_msgs in
#print Tree.below_1

/--
info: Ex3.Tree.brecOn_1.{u_1, u} {motive_1 : Tree.{u} → Sort u_1} {motive_2 : List.{u} Tree.{u} → Sort u_1}
  (t : List.{u} Tree.{u}) (F_1 : (t : Tree.{u}) → Tree.below.{u_1, u} t → motive_1 t)
  (F_2 : (t : List.{u} Tree.{u}) → Tree.below_1.{u_1, u} t → motive_2 t) : motive_2 t
-/
#guard_msgs in
#check Tree.brecOn_1

end Ex3
