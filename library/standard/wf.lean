-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
import logic classical

-- Well-founded relation definition
-- We are essentially saying that a relation R is well-founded
--    if every non-empty "set" P, has a R-minimal element
definition wf {A : Type} (R : A → A → Prop) : Prop :=
∀P, (∃w, P w) → ∃min, P min ∧ ∀b, R b min → ¬P b

-- Well-founded induction theorem
theorem wf_induction {A : Type} {R : A → A → Prop} {P : A → Prop} (Hwf : wf R) (iH : ∀x, (∀y, R y x → P y) → P x)
                     : ∀x, P x :=
by_contradiction (assume N : ¬∀x, P x,
  obtain (w : A) (Hw : ¬P w), from not_forall_exists N,
  -- The main "trick" is to define Q x as ¬P x.
  -- Since R is well-founded, there must be a R-minimal element r s.t. Q r (which is ¬P r)
  let Q [inline] x := ¬P x in
  have Qw  : ∃w, Q w, from exists_intro w Hw,
  have Qwf : ∃min, Q min ∧ ∀b, R b min → ¬Q b, from Hwf Q Qw,
  obtain (r : A) (Hr : Q r ∧ ∀b, R b r → ¬Q b), from Qwf,
  -- Using the inductive hypothesis iH and Hr, we show P r, and derive the contradiction.
  have s1 : ∀b, R b r → P b, from
    take b : A, assume H : R b r,
    -- We are using Hr to derive ¬¬P b
      not_not_elim (and_elim_right Hr b H),
  have s2 : P r,   from iH r s1,
  have s3 : ¬P r,  from and_elim_left Hr,
  absurd s2 s3)

