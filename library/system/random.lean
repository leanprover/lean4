/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
universes u

/-
Basic random number generator support based on the one
available on the Haskell library
-/

/- Interface for random number generators. -/
class random_gen (g : Type u) :=
/- `range` returns the range of values returned by
    the generator. -/
(range : g → nat × nat)
/- `next` operation returns a natural number that is uniformly distributed
    the range returned by `range` (including both end points),
   and a new generator. -/
(next  : g → nat × g)
/-
  The 'split' operation allows one to obtain two distinct random number
  generators. This is very useful in functional programs (for example, when
  passing a random number generator down to recursive calls). -/
(split : g → g × g)

/- "Standard" random number generator. -/
structure std_gen :=
(s1 : nat) (s2 : nat)

def std_range := (1, 2147483562)

instance : has_repr std_gen :=
{ repr := λ ⟨s1, s2⟩, "⟨" ++ to_string s1 ++ ", " ++ to_string s2 ++ "⟩" }

def std_next : std_gen → nat × std_gen
| ⟨s1, s2⟩ :=
  let k    : int := s1 / 53668,
      s1'  : int := 40014 * ((s1 : int) - k * 53668) - k * 12211,
      s1'' : int := if s1' < 0 then s1' + 2147483563 else s1',
      k'   : int := s2 / 52774,
      s2'  : int := 40692 * ((s2 : int) - k' * 52774) - k' * 3791,
      s2'' : int := if s2' < 0 then s2' + 2147483399 else s2',
      z    : int := s1'' - s2'',
      z'   : int := if z < 1 then z + 2147483562 else z % 2147483562
  in (z'.to_nat, ⟨s1''.to_nat, s2''.to_nat⟩)

def std_split : std_gen → std_gen × std_gen
| g@⟨s1, s2⟩ :=
  let new_s1  := if s1 = 2147483562 then 1 else s1 + 1,
      new_s2  := if s2 = 1          then 2147483398 else s2 - 1,
      new_g   := (std_next g).2,
      left_g  := std_gen.mk new_s1 new_g.2,
      right_g := std_gen.mk new_g.1 new_s2
in (left_g, right_g)

instance : random_gen std_gen :=
{range  := λ _, std_range,
 next   := std_next,
 split  := std_split}

/-- Return a standard number generator. -/
def mk_std_gen (s : nat := 0) : std_gen :=
let q  := s / 2147483562,
    s1 := s % 2147483562,
    s2 := q % 2147483398 in
⟨s1 + 1, s2 + 1⟩

/-
Auxiliary function for random_nat_val.
Generate random values until we exceed the target magnitude.
`gen_lo` and `gen_mag` are the generator lower bound and magnitude.
The parameter `r` is the "remaining" magnitude.
-/
private def rand_nat_aux {gen : Type u} [random_gen gen] (gen_lo gen_mag : nat) (h : gen_mag > 0) : nat → nat → gen → nat × gen
| 0        v g := (v, g)
| r'@(r+1) v g :=
  let (x, g') := random_gen.next g,
      v'      := v*gen_mag + (x - gen_lo)
  in have r' / gen_mag - 1 < r',
     begin
       by_cases h : (r + 1) / gen_mag = 0,
       { rw [h], simp, apply nat.zero_lt_succ },
       { have : (r + 1) / gen_mag > 0, from nat.pos_of_ne_zero h,
         have h₁ : (r + 1) / gen_mag - 1 < (r + 1) / gen_mag, { apply nat.sub_lt, assumption, tactic.comp_val },
         have h₂ : (r + 1) / gen_mag ≤ r + 1, { apply nat.div_le_self },
         exact lt_of_lt_of_le h₁ h₂ }
     end,
     rand_nat_aux (r' / gen_mag - 1) v' g'

/-- Generate a random natural number in the interval [lo, hi]. -/
def rand_nat {gen : Type u} [random_gen gen] (g : gen) (lo hi : nat) : nat × gen :=
let lo'              := if lo > hi then hi else lo,
    hi'              := if lo > hi then lo else hi,
    (gen_lo, gen_hi) := random_gen.range g,
    gen_mag          := gen_hi - gen_lo + 1,
    /-
      Probabilities of the most likely and least likely result
      will differ at most by a factor of (1 +- 1/q).  Assuming the RandomGen
      is uniform, of course
    -/
    q       := 1000,
    k       := hi' - lo' + 1,
    tgt_mag := k * q,
    (v, g') := rand_nat_aux gen_lo gen_mag (nat.zero_lt_succ _) tgt_mag 0 g,
    v'      := lo' + (v % k)
in (v', g')

/-- Generate a random Boolean. -/
def rand_bool {gen : Type u} [random_gen gen] (g : gen) : bool × gen :=
let (v, g') := rand_nat g 0 1
in (v = 1, g')
