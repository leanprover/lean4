structure presheaf_of_types (α : Type*) :=
(F : Π U : set α,  Type*)
(res : ∀ (U V : set α) ,
  (F U) → (F V))
(Hidem : ∀ U : set α, res U U = (res U U) ∘ (res U U))

-- set_option trace.type_context.is_def_eq true
-- set_option trace.type_context.is_def_eq_detail true

definition presheaf_of_types_pushforward
  {β : Type*}
  : presheaf_of_types β :=
  { Hidem := λ U, rfl,
}
