/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

Small example showing that (nat → nat) is not encodable.
-/
import data.encodable
open nat encodable option

section
hypothesis nat_nat_encodable : encodable (nat → nat)

private definition decode_fun (n : nat) : option (nat → nat) :=
@decode (nat → nat) nat_nat_encodable n

private definition encode_fun (f : nat → nat) : nat :=
@encode (nat → nat) nat_nat_encodable f

private lemma encodek_fun : ∀ f : nat → nat, decode_fun (encode_fun f) = some f :=
λ f, !encodek

private definition f (n : nat) : nat :=
match decode_fun n with
| some g := succ (g n)
| none   := 0
end

private definition v : nat := encode_fun f

private lemma f_eq : succ (f v) = f v :=
begin
  change succ (f v) =
         match decode_fun (encode_fun f) with
         | some g := succ (g v)
         | none   := 0
         end,
  rewrite encodek_fun
end
end

theorem not_encodable_nat_arrow_nat : (encodable (nat → nat)) → false :=
assume h, absurd (f_eq h) succ_ne_self
