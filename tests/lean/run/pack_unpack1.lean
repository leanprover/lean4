inductive tree_core (A : Type*) : bool → Type*
| leaf'    : A → tree_core ff
| node'    : tree_core tt → tree_core ff
| nil' {}  : tree_core tt
| cons'    : tree_core ff → tree_core tt → tree_core tt

attribute [reducible]
definition tree (A : Type*) := tree_core A ff

attribute [reducible]
definition tree_list (A : Type*) := tree_core A tt

open tree_core

definition pack {A : Type*} : list (tree A) → tree_core A tt
| []     := nil'
| (a::l) := cons' a (pack l)

definition unpack {A : Type*} : ∀ {b}, tree_core A b → list (tree A)
| .tt nil'         := []
| .tt (cons' a t)  := a :: unpack t
| .ff (leaf' a)    := []
| .ff (node' l)    := []

attribute [inverse]
lemma unpack_pack {A : Type*} : ∀ (l : list (tree A)), unpack (pack l) = l
| []     := rfl
| (a::l) :=
  show a :: unpack (pack l) = a :: l, from
  congr_arg (λ x, a :: x) (unpack_pack l)

attribute [inverse]
lemma pack_unpack {A : Type*} : ∀ t : tree_core A tt, pack (unpack t) = t :=
λ t,
  @tree_core.rec_on
    A
    (λ b, bool.cases_on b (λ t, true) (λ t, pack (unpack t) = t))
    tt t
    (λ a, trivial)
    (λ t ih, trivial)
    rfl
    (λ h t ih1 ih2,
     show cons' h (pack (unpack t)) = cons' h t, from
     congr_arg (λ x, cons' h x) ih2)

attribute [pattern]
definition tree.node {A : Type*} (l : list (tree A)) : tree A :=
tree_core.node' (pack l)

attribute [pattern]
definition tree.leaf {A : Type*} : A → tree A :=
tree_core.leaf'

set_option trace.eqn_compiler true

definition sz {A : Type*} : tree A → nat
| (tree.leaf a) := 1
| (tree.node l) := list.length l + 1

constant P {A : Type*} : tree A → Type 1
constant mk1 {A : Type*} (a : A) : P (tree.leaf a)
constant mk2 {A : Type*} (l : list (tree A)) : P (tree.node l)

noncomputable definition bla {A : Type*} : ∀ n : tree A, P n
| (tree.leaf a) := mk1 a
| (tree.node l) := mk2 l

check bla._main.equations._eqn_1
check bla._main.equations._eqn_2

definition foo {A : Type*} : nat → tree A → nat
| 0     _                   := 0
| (n+1) (tree.leaf a)       := 0
| (n+1) (tree.node [])      := foo n (tree.node [])
| (n+1) (tree.node (x::xs)) := foo n x

check @foo._main.equations._eqn_1
check @foo._main.equations._eqn_2
check @foo._main.equations._eqn_3
check @foo._main.equations._eqn_4
