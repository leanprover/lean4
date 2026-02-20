macro mods:declModifiers "lemma" n:declId sig:declSig val:declVal : command => `($mods:declModifiers theorem $n $sig $val)

def fooSimple (n : Nat) : Prop :=
  if n = 0 then True else False

lemma fooSimple' : fooSimple 0 :=
  by constructor

def fooPat : Nat → Prop
  | 0   => True
  | _+1 => False

lemma fooPat' : (x : Nat) → fooPat x → x = 0
  | 0, _ => rfl
