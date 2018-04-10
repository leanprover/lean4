meta def mk_c := `[exact 1]

structure foo (α : Type) :=
(a : α)
(b : α := a)
(c : α . mk_c)

example : foo ℕ → ℕ | {a := a} := a
example : foo ℕ → ℕ | {foo . a := a} := a
example : foo ℕ → ℕ | {a := nat.succ n} := n
example : foo ℕ → ℕ | {..} := 0
example : foo ℕ → ℕ | {b:=b, ..} := b
example : foo ℕ → ℕ | {..f} := 0 -- error
