import data.list

set_option blast.strategy "unit"

definition lemma1 : true :=
by blast

open perm

definition lemma2 (l : list nat) : l ~ l :=
by blast

print lemma1
print lemma2
