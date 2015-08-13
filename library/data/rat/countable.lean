/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import data.rat.basic data.countable data.encodable data.int.countable
open encodable nat int option quot

namespace rat
definition encode_prerat : prerat → nat
| (prerat.mk n d h) := mkpair (encode n) (encode d)

definition decode_prerat (a : nat) : option prerat :=
match unpair a with
| (cn, cd) :=
  match decode int cn with
  | some n :=
    match decode int cd with
    | some d := if h : d > 0 then some (prerat.mk n d h) else none
    | none   := none
    end
  | none   := none
  end
end

lemma decode_encode_prerat (p : prerat) : decode_prerat (encode_prerat p) = some p :=
begin
  cases p with n d h, unfold [encode_prerat, decode_prerat],
  rewrite unpair_mkpair, esimp, rewrite [*encodek, dif_pos h]
end

definition encodable_prerat [instance] : encodable prerat :=
encodable.mk
  encode_prerat
  decode_prerat
  decode_encode_prerat

definition decidable_equiv [instance] : ∀ a b : prerat, decidable (prerat.equiv a b)
| (prerat.mk n₁ d₁ h₁) (prerat.mk n₂ d₂ h₂) := begin unfold prerat.equiv, exact _ end


definition encodable_rat [instance] : encodable rat :=
@encodable_quot _ _ decidable_equiv encodable_prerat

lemma countable_rat : countable rat :=
countable_of_encodable encodable_rat
end rat
