import Lean.Level

open Lean Level

instance : Coe Name Level := ⟨Level.param⟩
instance : HAdd Level Nat Level := ⟨fun l n => n.repeat Level.succ l⟩
instance : HAdd Name Nat Level := ⟨fun l n => n.repeat Level.succ l⟩

#guard isEquiv (max `a `b) (max `b `a)
#guard isEquiv (max 0 `a) `a
#guard !isEquiv (max 1 `a) `a
#guard isEquiv (imax 0 `a) `a
#guard isEquiv (imax 1 `a) `a
#guard isEquiv (imax `a 0) 0
#guard isEquiv (imax `a (imax `b `c)) (imax (max `a `b) `c)
#guard isEquiv (max (`a + 2) (`a + 3)) (`a + 3)
#guard isEquiv (max (`a + 2) (max `b (`a + 3))) (max (`a + 3) `b)
#guard !isEquiv (max (`a + 2) (max `b (`a + 3))) (`a + 3)
#guard isEquiv (max `u (imax `u `v)) (max `u `v)
#guard isEquiv (imax (max `u `v) `v) (imax `u `v)
#guard isEquiv (imax `u `u) `u
#guard isEquiv (imax `u (imax `v `v)) (imax `u `v)
#guard !isEquiv `u `v
#guard !isEquiv (`u + 3) (`u + 5)
#guard isEquiv (imax (imax `u `v) (imax `u `v)) (imax `u `v)
#guard isEquiv (max (imax `u `v) (max `u `v)) (max `u `v)

universe u v w

example : Sort (max u v) = Sort (max v u) := rfl
example : Sort (max 0 u) = Sort u := rfl
example : Sort (imax 0 u) = Sort u := rfl
example : Sort (imax 1 u) = Sort u := rfl
example : Sort (imax u 0) = Sort 0 := rfl
example : Sort (imax u (imax v w)) = Sort (imax (max u v) w) := rfl
example : Sort (max (u + 2) (u + 3)) = Sort (u + 3) := rfl
example : Sort (max (u + 2) v (u + 3)) = Sort (max v (u + 3)) := rfl
example : Sort (max u (imax u v)) = Sort (max u v) := rfl
example : Sort (imax u (max u v)) = Sort (max u v) := rfl
example : Sort (imax (max u v) v) = Sort (imax u v) := rfl
example : Sort (imax (max u v) u) = Sort (imax v u) := rfl
example : Sort (imax u u) = Sort u := rfl
example : Sort (imax u v v) = Sort (imax u v) := rfl
example : Sort (imax (imax u v) (imax u v)) = Sort (imax u v) := rfl
example : Sort (max (imax u v) (max u v)) = Sort (max u v) := rfl
