import logic data.prod
open prod

set_option class.unique_instances true
theorem tst (A : Type) (H₁ : inhabited A) (H₂ : inhabited A) : inhabited (A × A) :=
_

set_option class.unique_instances false
theorem tst (A : Type) (H₁ : inhabited A) (H₂ : inhabited A) : inhabited (A × A) :=
_
