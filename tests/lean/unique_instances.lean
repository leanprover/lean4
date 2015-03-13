import logic data.prod
open prod

set_option class.unique_instances true set_option pp.implicit true
theorem tst (A : Type) (H₁ : inhabited A) (H₂ : inhabited A) : inhabited (A × A) :=
_

set_option class.unique_instances false
theorem tst2 (A : Type) (H₁ : inhabited A) (H₂ : inhabited A) : inhabited (A × A) :=
_
