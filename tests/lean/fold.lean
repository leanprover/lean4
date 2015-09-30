prelude
definition Prop := Type.{0} inductive true : Prop := intro : true inductive false : Prop constant num : Type
inductive prod (A B : Type) := mk : A → B → prod A B infixl ` × `:30 := prod
variables a b c : num

section
  local notation `(` t:(foldr `, ` (e r, prod.mk e r)) `)` := t
  check (a, false, b, true, c)
  set_option pp.notation false
  check (a, false, b, true, c)
end

section
  local notation `(` t:(foldr `, ` (e r, prod.mk r e)) `)` := t
  set_option pp.notation true
  check (a, false, b, true, c)
  set_option pp.notation false
  check (a, false, b, true, c)
end

section
  local notation `(` t:(foldl `, ` (e r, prod.mk r e)) `)` := t
  set_option pp.notation true
  check (a, false, b, true, c)
  set_option pp.notation false
  check (a, false, b, true, c)
end

section
  local notation `(` t:(foldl `, ` (e r, prod.mk e r)) `)` := t
  set_option pp.notation true
  check (a, false, b, true, c)
  set_option pp.notation false
  check (a, false, b, true, c)
end
