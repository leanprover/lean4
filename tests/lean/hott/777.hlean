namespace sum
  definition code.{u v} {A : Type.{u}} {B : Type.{v}} : A + B → A + B → Type.{max u v}
  | code (inl a) (inl a') := lift (a = a')
  | code (inr b) (inr b') := lift (b = b')
  | code _       _        := lift empty
end sum
