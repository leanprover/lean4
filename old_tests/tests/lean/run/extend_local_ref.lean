section
universe u

structure a :=
(a : Type u)

structure b extends a
end

section
parameter α : Type

structure c :=
(a : α)

structure d extends c
end
