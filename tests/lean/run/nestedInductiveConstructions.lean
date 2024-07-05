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
  Tree.rec.{(max 1 u) + 1}
    (fun a a_ih => PProd.{max 1 u, max 1 u} (PProd.{u, max 1 u} (motive_2 a) a_ih) PUnit.{max 1 u}) PUnit.{max 1 u}
    (fun head tail head_ih tail_ih =>
      PProd.{max 1 u, max 1 u} (PProd.{u, max 1 u} (motive_1 head) head_ih)
        (PProd.{max 1 u, max 1 u} (PProd.{u, max 1 u} (motive_2 tail) tail_ih) PUnit.{max 1 u}))
    t
-/
#guard_msgs in
#print Tree.below

/--
info: @[reducible] protected def Ex1.Tree.below_1 : {motive_1 : Tree → Prop} →
  {motive_2 : List.{0} Tree → Prop} → List.{0} Tree → Prop :=
fun {motive_1} {motive_2} t =>
  Tree.rec_1.{1} (fun a a_ih => And (And (motive_2 a) a_ih) True) True
    (fun head tail head_ih tail_ih => And (And (motive_1 head) head_ih) (And (And (motive_2 tail) tail_ih) True)) t
-/
#guard_msgs in
#print Tree.below_1

end Ex1

namespace Ex2

inductive Tree where | node  : List (List Tree) → List Tree → Tree

/--
info: @[reducible] protected def Ex2.Tree.below.{u} : {motive_1 : Tree → Sort u} →
  {motive_2 : List.{0} (List.{0} Tree) → Sort u} → {motive_3 : List.{0} Tree → Sort u} → Tree → Sort (max 1 u) :=
fun {motive_1} {motive_2} {motive_3} t =>
  Tree.rec.{(max 1 u) + 1}
    (fun a a_1 a_ih a_ih_1 =>
      PProd.{max 1 u, max 1 u} (PProd.{u, max 1 u} (motive_2 a) a_ih)
        (PProd.{max 1 u, max 1 u} (PProd.{u, max 1 u} (motive_3 a_1) a_ih_1) PUnit.{max 1 u}))
    PUnit.{max 1 u}
    (fun head tail head_ih tail_ih =>
      PProd.{max 1 u, max 1 u} (PProd.{u, max 1 u} (motive_3 head) head_ih)
        (PProd.{max 1 u, max 1 u} (PProd.{u, max 1 u} (motive_2 tail) tail_ih) PUnit.{max 1 u}))
    PUnit.{max 1 u}
    (fun head tail head_ih tail_ih =>
      PProd.{max 1 u, max 1 u} (PProd.{u, max 1 u} (motive_1 head) head_ih)
        (PProd.{max 1 u, max 1 u} (PProd.{u, max 1 u} (motive_3 tail) tail_ih) PUnit.{max 1 u}))
    t
-/
#guard_msgs in
#print Tree.below

/--
info: @[reducible] protected def Ex2.Tree.below_1 : {motive_1 : Tree → Prop} →
  {motive_2 : List.{0} (List.{0} Tree) → Prop} → {motive_3 : List.{0} Tree → Prop} → List.{0} (List.{0} Tree) → Prop :=
fun {motive_1} {motive_2} {motive_3} t =>
  Tree.rec_1.{1} (fun a a_1 a_ih a_ih_1 => And (And (motive_2 a) a_ih) (And (And (motive_3 a_1) a_ih_1) True)) True
    (fun head tail head_ih tail_ih => And (And (motive_3 head) head_ih) (And (And (motive_2 tail) tail_ih) True)) True
    (fun head tail head_ih tail_ih => And (And (motive_1 head) head_ih) (And (And (motive_3 tail) tail_ih) True)) t
-/
#guard_msgs in
#print Tree.below_1

/--
info: @[reducible] protected def Ex2.Tree.below_2 : {motive_1 : Tree → Prop} →
  {motive_2 : List.{0} (List.{0} Tree) → Prop} → {motive_3 : List.{0} Tree → Prop} → List.{0} Tree → Prop :=
fun {motive_1} {motive_2} {motive_3} t =>
  Tree.rec_2.{1} (fun a a_1 a_ih a_ih_1 => And (And (motive_2 a) a_ih) (And (And (motive_3 a_1) a_ih_1) True)) True
    (fun head tail head_ih tail_ih => And (And (motive_3 head) head_ih) (And (And (motive_2 tail) tail_ih) True)) True
    (fun head tail head_ih tail_ih => And (And (motive_1 head) head_ih) (And (And (motive_3 tail) tail_ih) True)) t
-/
#guard_msgs in
#print Tree.below_2

end Ex2

namespace Ex3

inductive Tree : Type u where | node : List Tree → Tree

/--
info: @[reducible] protected def Ex3.Tree.below.{u_1, u} : {motive_1 : Tree.{u} → Sort u_1} →
  {motive_2 : List.{u} Tree.{u} → Sort u_1} → Tree.{u} → Sort (max 1 u_1) :=
fun {motive_1} {motive_2} t =>
  Tree.rec.{(max 1 u_1) + 1, u}
    (fun a a_ih => PProd.{max 1 u_1, max 1 u_1} (PProd.{u_1, max 1 u_1} (motive_2 a) a_ih) PUnit.{max 1 u_1})
    PUnit.{max 1 u_1}
    (fun head tail head_ih tail_ih =>
      PProd.{max 1 u_1, max 1 u_1} (PProd.{u_1, max 1 u_1} (motive_1 head) head_ih)
        (PProd.{max 1 u_1, max 1 u_1} (PProd.{u_1, max 1 u_1} (motive_2 tail) tail_ih) PUnit.{max 1 u_1}))
    t
-/
#guard_msgs in
#print Tree.below

/--
info: @[reducible] protected def Ex3.Tree.below_1.{u} : {motive_1 : Tree.{u} → Prop} →
  {motive_2 : List.{u} Tree.{u} → Prop} → List.{u} Tree.{u} → Prop :=
fun {motive_1} {motive_2} t =>
  Tree.rec_1.{1, u} (fun a a_ih => And (And (motive_2 a) a_ih) True) True
    (fun head tail head_ih tail_ih => And (And (motive_1 head) head_ih) (And (And (motive_2 tail) tail_ih) True)) t
-/
#guard_msgs in
#print Tree.below_1

end Ex3
