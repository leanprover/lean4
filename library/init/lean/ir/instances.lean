/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.ir.ir

namespace lean
namespace ir
/- TEMPORARY HACK for defining (decidable_eq type) until we bootstrap new compiler -/
def type2id : type → nat
| type.bool   := 0  | type.byte   := 1
| type.uint16 := 2  | type.uint32 := 3  | type.uint64 := 4 | type.usize := 5
| type.int16  := 6  | type.int32  := 7  | type.int64  := 8
| type.float  := 9  | type.double := 10 | type.object := 11

def id2type : nat → type
| 0 := type.bool   | 1 := type.byte
| 2 := type.uint16 | 3 := type.uint32  | 4 := type.uint64 | 5 := type.usize
| 6 := type.int16  | 7 := type.int32   | 8 := type.int64
| 9 := type.float  | 10 := type.double | _       := type.object

theorem id2type_type2id_eq : ∀ (ty : type), id2type (type2id ty) = ty
| type.bool   := rfl  | type.byte   := rfl
| type.uint16 := rfl  | type.uint32 := rfl  | type.uint64 := rfl | type.usize := rfl
| type.int16  := rfl  | type.int32  := rfl  | type.int64  := rfl
| type.float  := rfl  | type.double := rfl  | type.object := rfl

instance type_has_dec_eq : decidable_eq type :=
λ t₁ t₂,
 if h : type2id t₁ = type2id t₂
 then is_true (id2type_type2id_eq t₁ ▸ id2type_type2id_eq t₂ ▸ h ▸ rfl)
 else is_false (λ h', absurd rfl (@eq.subst _ (λ t, ¬ type2id t = type2id t₂) _ _ h' h))
/- END of TEMPORARY HACK for (decidable_eq type) -/

instance : has_coe string fnid :=
⟨mk_simple_name⟩

-- TODO: move collection declarations to another file
instance var_has_lt : has_lt var := (name.has_lt_quick : has_lt name)
instance blockid_has_lt : has_lt blockid := (name.has_lt_quick : has_lt name)
instance fnid_has_lt : has_lt fnid := (name.has_lt_quick : has_lt name)

instance var_has_dec_eq : decidable_eq var := infer_instance_as (decidable_eq name)
instance blockid_has_dec_eq : decidable_eq blockid := infer_instance_as (decidable_eq name)
instance fnid_has_dec_eq : decidable_eq fnid := infer_instance_as (decidable_eq name)

instance var_hashable : hashable var := infer_instance_as (hashable name)
instance blockid_hashable : hashable blockid := infer_instance_as (hashable name)
instance fnid_hashable : hashable fnid := infer_instance_as (hashable name)

def var_set        := rbtree var (<)
def blockid_set    := rbtree blockid (<)
def context        := rbmap var type (<)
def var2blockid    := rbmap var blockid (<)
def fnid2string    := rbmap fnid string (<)
def fnid_set       := rbtree fnid (<)
def mk_var_set     : var_set     := mk_rbtree var (<)
def mk_blockid_set : blockid_set := mk_rbtree blockid (<)
def mk_var2blockid : var2blockid := mk_rbmap var blockid (<)
def mk_context     : context     := mk_rbmap var type (<)
def mk_fnid2string : fnid2string := mk_rbmap fnid string (<)
def mk_fnid_set    : fnid_set    := mk_rbtree fnid (<)

instance : inhabited result :=
⟨⟨type.bool⟩⟩

end ir
end lean
