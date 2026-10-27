/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Julia M. Himmel
-/
module

prelude
public import Init.Data.UInt.Basic
public import Init.PropLemmas
public import Init.Data.BitVec.Decidable

public section

set_option hygiene false in
macro "declare_decidable_uint_quantifiers" typeName:ident bits:term:arg : command => `(
namespace $typeName

theorem forall_iff_forall_ofBitVec {P : $typeName → Prop} :
    (∀ x, P x) ↔ ∀ (x : BitVec $bits), P (ofBitVec x) :=
  ⟨fun h x => h (ofBitVec x), fun h x => h x.toBitVec⟩

instance instDecidableForall (P : $typeName → Prop) [DecidablePred P] :
    Decidable (∀ x, P x) :=
  decidable_of_iff' _ forall_iff_forall_ofBitVec

theorem exists_iff_exists_ofBitVec {P : $typeName → Prop} :
    (∃ x, P x) ↔ ∃ (x : BitVec $bits), P (ofBitVec x) :=
  ⟨fun ⟨x, hx⟩ => ⟨x.toBitVec, hx⟩, fun ⟨x, hx⟩ => ⟨ofBitVec x, hx⟩⟩

instance instDecidableExists (P : $typeName → Prop) [DecidablePred P] :
    Decidable (∃ x, P x) :=
  decidable_of_iff' _ exists_iff_exists_ofBitVec

end $typeName
)

declare_decidable_uint_quantifiers UInt8 8
declare_decidable_uint_quantifiers UInt16 16
declare_decidable_uint_quantifiers UInt32 32
declare_decidable_uint_quantifiers UInt64 64
