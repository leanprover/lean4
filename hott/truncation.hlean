-- Copyright (c) 2014 Jakob von Raumer. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Jakob von Raumer

open truncation

-- Axiomatize the truncation operator as long as we do not have
-- Higher inductive types

axiom truncate (A : Type) (n : trunc_index) : Type

axiom truncate.mk {A : Type} (n : trunc_index) (a : A) : truncate A n

axiom truncate.is_trunc (A : Type) (n : trunc_index) : is_trunc n (truncate A n)

axiom truncate.rec_on {A : Type} {n : trunc_index} {C : truncate A n → Type}
  (ta : truncate A n)
  [H : Π (ta : truncate A n), is_trunc n (C ta)]
  (CC : Π (a : A), C (truncate.mk n a)) : C ta
