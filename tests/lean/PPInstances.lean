class Semiring (α : Type) where add : α → α → α
class Ring (α : Type) where add : α → α → α

class AddCommMonoid (α : Type) where
class AddCommGroup (α : Type) where

class Module (α β : Type) [Semiring α] [AddCommMonoid β] where

class NormedField (α : Type) where
  add : α → α → α
  add_comm  : ∀ (x y : α), @Add.add _ ⟨add⟩ x y = @Add.add _ ⟨add⟩ y x

class SemiNormedGroup (α : Type) where
class SemiNormedSpace (α β : Type) [NormedField α] [SemiNormedGroup β] where

instance SemiNormedGroup.toAddCommMonoid [SemiNormedGroup α] : AddCommMonoid α := {}
instance Ring.toSemiring [instR : Ring α] : Semiring α := { add := instR.add }
instance NormedField.toRing [instNF : NormedField α] : Ring α := { add := instNF.add }

instance SemiNormedSpace.toModule [NormedField α] [SemiNormedGroup β] [SemiNormedSpace α β] : Module α β := {}

constant R : Type := Unit
constant foo (a b : R) : R := a

instance R.NormedField : NormedField R := { add := foo, add_comm := sorry }
instance R.Ring : Ring R := { add := foo }

variable {E : Type} [instSNG : SemiNormedGroup E] [instSNS : SemiNormedSpace R E]

set_option pp.all true
set_option pp.instances false in
set_option pp.instanceTypes false in
#check Module R E

set_option pp.instances false in
set_option pp.instanceTypes true in
#check Module R E

set_option pp.instances true in
set_option pp.instanceTypes false in
#check Module R E

set_option pp.instances true in
set_option pp.instanceTypes true in
#check Module R E
