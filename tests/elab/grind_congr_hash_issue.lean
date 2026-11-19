module
set_option grind.debug true

opaque f : Nat → Nat
opaque g : (Nat → Nat) → Prop

example
    : f a = x →
      -- At this point `f` has not been internalized
      g f →
      -- Since `f` has now occurred as the argument of `f`, it is internalized
      f b = y →
      -- The congruence hash for `f a` must not depend on whether `f` has been internalized or not
      b = a →
      x = y := by
  grind

-- Same example with `a = b` to ensure the previous issue does not depend on how we break
-- ties when merging equivalence classes of the same size
example
    : f a = x →
      g f →
      f b = y →
      a = b →
      x = y := by
  grind

-- funCC congruence: `h a` and `k` are in the same equivalence class as functions,
-- so `h a b c = k b c` should follow.
example (h : Nat → Nat → Nat → Nat) (k : Nat → Nat → Nat)
    : h a = k → h a b c = k b c := by
  grind
