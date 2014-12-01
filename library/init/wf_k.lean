-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
prelude
import init.nat

namespace well_founded
  -- This is an auxiliary definition that useful for generating a new "proof" for (well_founded R)
  -- that allows us to use well_founded.fix and execute the definitions up to k nested recursive
  -- calls without "computing" with the proofs in Hwf.
  definition intro_k {A : Type} {R : A → A → Prop} (Hwf : well_founded R) (k : nat) : well_founded R :=
  well_founded.intro
  (nat.rec_on k
     (λ n : A, well_founded.apply Hwf n)
     (λ (k' : nat) (f : Πa, acc R a), (λ n : A, acc.intro n (λ y H, f y))))

end well_founded
