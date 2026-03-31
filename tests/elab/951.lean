/-!
# Names of inferred instances clash (issue 951)
-/

inductive ThingA where
| mkA
deriving Ord
instance : LE ThingA where
  le a b := (compare a b).isLE

instance (t₁ t₂ : ThingA) : Decidable (t₁ <= t₂) := inferInstance
#check instDecidableLeThingA

inductive ThingB where
| mkB
deriving Ord
instance : LE ThingB where
  le a b := (compare a b).isLE
instance (t₁ t₂ : ThingB) : Decidable (t₁ <= t₂) := inferInstance
#check instDecidableLeThingB
