import data.set.basic
open set

definition preimage {X Y : Type} (f : X → Y) (b : set Y) : set X := λ x, f x ∈ b

example {X Y : Type} {b : set Y} (f : X → Y) (x : X) (H : x ∈ preimage f b) : f x ∈ b :=
H

theorem preimage_subset {X Y : Type} {a b : set Y} (f : X → Y) (H : a ⊆ b) : preimage f a ⊆ preimage f b :=
λ (x : X) (H' : x ∈ preimage f a), show x ∈ preimage f b,
from @H (f x) H'

example {X Y : Type} {a b : set Y} (f : X → Y) (H : a ⊆ b) : preimage f a ⊆ preimage f b :=
λ (x : X) (H' : x ∈ preimage f a),
have f x ∈ a, from H',
have f x ∈ b, from mem_of_subset_of_mem H this,
this

example {X Y : Type} {a b : set Y} (f : X → Y) (H : a ⊆ b) : preimage f a ⊆ preimage f b :=
λ (x : X) (H' : x ∈ preimage f a),
have f x ∈ b, from mem_of_subset_of_mem H H',
this

example {X Y : Type} {a b : set Y} (f : X → Y) (H : a ⊆ b) : preimage f a ⊆ preimage f b :=
λ (x : X) (H' : x ∈ preimage f a),
@H (f x) H'

lemma mem_preimage_of_mem {X Y : Type} {f : X → Y} {s : set Y} {x : X} : f x ∈ s → x ∈ preimage f s :=
assume H, H

lemma mem_of_mem_preimage {X Y : Type} {f : X → Y} {s : set Y} {x : X} : x ∈ preimage f s → f x ∈ s :=
assume H, H

example {X Y : Type} {a b : set Y} (f : X → Y) (H : a ⊆ b) : preimage f a ⊆ preimage f b :=
take x, assume H',
mem_preimage_of_mem (mem_of_subset_of_mem H (mem_of_mem_preimage H'))
