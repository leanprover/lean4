import macros

---
--- Classes of structures, and axiomatic classes of structures
---

--- A "structure" consists of a carrier, and some data (whose type depends on the carrier)

definition StructClass : (Type 1) := Type → Type   -- the type of the data

definition structure (S : StructClass) : (Type 1)
:= sig T : Type, S T

definition carrier {S : StructClass} (M : structure S) : Type
:= proj1 M

definition data {S : StructClass} (M : structure S) : S (carrier M)
:= proj2 M

--- An "axiomatic class" is a class of structures satisfying some predicate (the "axioms")

definition AxClass : (Type 1)
:= sig S : StructClass, structure S → Bool

-- Coercion from AxClass to StructClass
definition struct_class (C : AxClass) : StructClass
:= proj1 C

definition axioms {C : AxClass} (M : structure (struct_class C))
:= proj2 C M

definition instance (C : AxClass) : (Type 1)
:= sig M : structure (struct_class C), axioms M

definition struct {C : AxClass} (M : instance C)
:= proj1 M

definition hyps {C : AxClass} (M : instance C) : axioms (struct M)
:= proj2 M

---
--- Examples
---

--- multiplication (for overloading *)

definition MulStruct : StructClass
:= λ T, T → T → T

definition mul {M : structure MulStruct} (x y : carrier M) : carrier M
:= data M x y

infixl 70 * : mul

definition mul_is_assoc (M : structure MulStruct) : Bool
:= ∀ x y z : carrier M, (x * y) * z = x * (y * z)

definition mul_is_comm (M : structure MulStruct) : Bool
:= ∀ x y z : carrier M, x * y = y * x

--- semigroups

definition Semigroup : AxClass
:= pair MulStruct mul_is_assoc

--- to fill the hole above automatically
theorem semigroup_mul_is_assoc (M : instance Semigroup) : mul_is_assoc (struct M)
:= hyps M

definition OneStruct : StructClass
:= λ T, T

definition one {M : structure OneStruct} : carrier M
:= data M

-- structures with mult and one

definition MonoidStruct : StructClass
:= λ T, OneStruct T # MulStruct T

definition MonoidStruct_to_OneStruct (M : structure MonoidStruct) : (structure OneStruct)
:= pair (carrier M) (proj1 (data M))

definition MonoidStruct_to_MulStruct (M : structure MonoidStruct) : (structure MulStruct)
:= pair (carrier M) (proj2 (data M))

variable M : structure MonoidStruct
check carrier M = carrier (MonoidStruct_to_OneStruct M)

theorem test1 (M : structure MonoidStruct) : carrier M = carrier (MonoidStruct_to_OneStruct M)
:= refl (carrier M)

definition is_mul_right_id (M : structure MonoidStruct) : Bool
:= let m : carrier M → carrier M → carrier M := @mul (MonoidStruct_to_MulStruct M),
       o : carrier M                            := @one (MonoidStruct_to_OneStruct M)
   in ∀ x : carrier M, m x o = x

definition is_monoid (M : structure MonoidStruct) : Bool
:= mul_is_assoc (MonoidStruct_to_MulStruct M) ∧ is_mul_right_id M

definition Monoid : AxClass
:= pair MonoidStruct is_monoid

theorem monoid_is_mul_right_id (M : instance Monoid) : is_mul_right_id (struct M)
:= and_elimr (proj2 M)

theorem monoid_mul_is_assoc (M : instance Monoid) : mul_is_assoc (MonoidStruct_to_MulStruct (struct M))
:= and_eliml (proj2 M)
