theorem {u} not_mem_empty1 {A : Type u} (x : A) : x ∉ (∅ : set A) :=
assume h, h

theorem {u} not_mem_empty2 {A : Type u} (x : A) : x ∉ ∅ :=  -- ERROR here
assume h, h

theorem {u} not_mem_empty3 {A : Type u} (x : A) : x ∉ (∅ : set A) :=
assume h : x ∈ ∅, h

theorem {u} not_mem_empty4 {A : Type u} (x : A) : x ∉ (∅ : set A) :=
assume h : x ∈ (∅ : set A), h

theorem {u} not_mem_empty5 {A : Type u} (x : A) : x ∉ (∅ : set A) :=
begin intro h, exact h end

open tactic

theorem {u} not_mem_empty6 {A : Type u} (x : A) : x ∉ (∅ : set A) :=
by do h ← intro `h, exact h
