meta def mk_c := `[exact 1]

structure foo (α : Type) :=
(a : α)
(b : α := a)
(c : α . mk_c)

def f : foo ℕ := {a := 1}
#check ({a := 1} : foo ℕ)
#check ({foo . a := 1} : foo ℕ)
#check ({..} : foo ℕ)
#check ({foo . ..} : foo ℕ)
#check {c := 1, ..f}
#check {..f}

#check {.., a := 1} -- ".." must be last item
#check {..f, a := 1} -- "..f" cannot be followed by key-value pair

structure bar :=
(a : ℕ := 0)
(b : ℕ := 0)

structure baz :=
(b : ℕ := 2)
(c : ℕ := 2)

#check ({.} : bar)
#check ({a := 1, ..{bar.}, ..{baz.}} : foo ℕ)
