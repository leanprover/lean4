macro mods:declModifiers "lemma" n:declId sig:declSig val:declVal : command => `($mods:declModifiers theorem $n $sig $val)

lemma fooSimple (n : Nat) : Prop :=
  if n = 0 then True else False

lemma fooPat : Nat → Prop
  | 0   => True
  | n+1 => False
