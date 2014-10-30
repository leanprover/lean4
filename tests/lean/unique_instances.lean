import logic data.prod
open prod

set_option elaborator.unique_class_instances true
theorem tst (A : Type) (H₁ : inhabited A) (H₂ : inhabited A) : inhabited (A × A) :=
_

set_option elaborator.unique_class_instances false
theorem tst (A : Type) (H₁ : inhabited A) (H₂ : inhabited A) : inhabited (A × A) :=
_
