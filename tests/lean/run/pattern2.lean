constant f : nat → nat → nat
constant g : nat → nat → nat
attribute g [no_pattern]

namespace foo

definition lemma1 [forward] {a b : nat} : f a b = g a b :=
sorry

end foo

print foo.lemma1
open foo
print foo.lemma1
attribute foo.lemma1 [forward]

print foo.lemma1
