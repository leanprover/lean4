prelude
definition Prop := Type.{0} inductive true : Prop := intro : true inductive false : Prop constant num : Type
inductive prod (A B : Type) := mk : A → B → prod A B infixl `×`:30 := prod
variables a b c : num

context
  notation `(` t:(foldr `,` (e r, prod.mk e r)) `)` := t
  check (a, false, b, true, c)
  set_option pp.notation false
  check (a, false, b, true, c)
end

context
  notation `(` t:(foldr `,` (e r, prod.mk r e)) `)` := t
  check (a, false, b, true, c)
  set_option pp.notation false
  check (a, false, b, true, c)
end

context
  notation `(` t:(foldl `,` (e r, prod.mk r e)) `)` := t
  check (a, false, b, true, c)
  set_option pp.notation false
  check (a, false, b, true, c)
end

context
  notation `(` t:(foldl `,` (e r, prod.mk e r)) `)` := t
  check (a, false, b, true, c)
  set_option pp.notation false
  check (a, false, b, true, c)
end
