/-!
# `lia` and `grobner` accept a `[...]` parameter list

Both tactics are thin wrappers around `grind`, and take the same `[...]` parameter list. Proof
terms are asserted as extra facts, and lemmas are added to the E-matching lemma set.
-/

private def clamp (n : Int) : Int := if n ≤ 0 then 0 else n
private theorem clamp_def (n : Int) : clamp n = if n ≤ 0 then 0 else n := rfl

-- Without extra facts, `lia` treats `clamp` as opaque and cannot finish.
example (n : Int) : 0 ≤ clamp n := by
  fail_if_success lia
  lia [clamp_def n]

-- A quantified lemma is instantiated via E-matching, as in `grind`.
example (n : Int) : 0 ≤ clamp n := by
  lia [= clamp_def]

-- Arguments can be arbitrary proof terms.
private opaque f : Nat → Nat
private axiom f_pos (n : Nat) : 0 < f n
example (n : Nat) : 1 ≤ f n + f (n + 1) := by
  fail_if_success lia
  lia [f_pos n, f_pos (n + 1)]

-- Config options still combine with the parameter list.
example (n : Int) : 0 ≤ clamp n := by
  lia -order [= clamp_def]

-- Naming a `grind` attribute adds its whole lemma set, so `@[grind]`-only lemmas become visible.
private def g (n : Int) : Int := n + 1
@[grind =] private theorem g_def (n : Int) : g n = n + 1 := rfl
example (n : Int) : g n = n + 1 := by
  fail_if_success lia
  lia [grind]

-- `-` removes a lemma from the `@[lia]` set.
example (a b : Nat) (h : a ≤ b) : max a b = b := by
  fail_if_success lia [- Nat.max_def]
  lia
example (a b : Nat) (h : a ≤ b) : min a b = a := by
  lia [- Nat.max_def]

-- `grobner` accepts proof terms as extra facts.
private def sq (x : Int) : Int := x * x
private theorem sq_def (x : Int) : sq x = x * x := rfl
example (x y : Int) (h : x = y) : sq x = y * y := by
  fail_if_success grobner
  grobner [sq_def x]

example (x y : Int) (h : x + y = 0) : sq x = sq y := by
  grobner [sq_def x, sq_def y]

-- Quantified lemmas are instantiated via E-matching, while the `@[grind]` set stays disabled.
example (x y : Int) (h : x = y) : sq x = y * y := by
  grobner [= sq_def]
example (n : Int) : g n = n + 1 := by
  fail_if_success grobner [= sq_def]
  grobner [= g_def]

-- Local hypotheses are used automatically, so passing one is an error, as for `grind`.
/-- error: redundant parameter `h`, `grind` uses local hypotheses automatically -/
#guard_msgs in
example (x y : Int) (h : x = y) : x * x = y * y := by
  grobner [h]
