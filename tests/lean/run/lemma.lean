macro mods:declModifiers "lemma" n:declId sig:declSig val:declVal : command => `($mods:declModifiers theorem $n $sig $val)

lemma FooSimple (n : Nat) : Prop :=
  if n = 0 then True else False

lemma FooPat : Nat → Prop
  | 0   => True
  | n+1 => False
