constant f : nat → nat → nat

definition lemma1 [forward] {a b : nat} : f a b = a :=
sorry

print lemma1

-- TODO(Leo): remove patterns that are permutations of of other patterns
definition lemma2 [forward] {a b : nat} : f a b = f b a :=
sorry

definition lemma3 [forward] {a b : nat} : (:f a b:) = f b a :=
sorry

print lemma2
print lemma3

definition lemma4 [forward] {a b c : nat} : f a b = f a c :=
sorry

print lemma4
