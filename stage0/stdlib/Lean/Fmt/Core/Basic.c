// Lean compiler output
// Module: Lean.Fmt.Core.Basic
// Imports: public import Init.Data.Hashable public import Init.Data.Ord.Basic public import Std.Data.HashMap.Basic import Init.Data
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint16_t lean_uint16_of_nat(lean_object*);
uint16_t lean_uint16_shift_left(uint16_t, uint16_t);
uint16_t lean_uint16_lor(uint16_t, uint16_t);
uint8_t lean_uint8_of_nat(lean_object*);
uint8_t lean_uint8_land(uint8_t, uint8_t);
uint8_t lean_bool_to_uint8(uint8_t);
uint8_t lean_uint8_lor(uint8_t, uint8_t);
uint8_t lean_uint8_shift_left(uint8_t, uint8_t);
uint16_t lean_uint8_to_uint16(uint8_t);
uint16_t lean_uint16_shift_right(uint16_t, uint16_t);
uint16_t lean_uint16_land(uint16_t, uint16_t);
lean_object* l_Nat_add___boxed(lean_object*, lean_object*);
lean_object* l_Option_merge___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint16_t lean_uint16_complement(uint16_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_usize_to_nat(size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* l_UInt8_toUInt64___boxed(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_array_mk(lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_UInt8_decEq___boxed(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Nat_decEq___boxed(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Array_zipIdx___redArg(lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_UInt64_ofNat___boxed(lean_object*);
uint64_t lean_uint8_to_uint64(uint8_t);
lean_object* lean_array_to_list(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_instInhabitedFullnessState___aux__1;
LEAN_EXPORT uint8_t l_Lean_Fmt_instInhabitedFullnessState;
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqFullnessState___aux__1(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqFullnessState___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_instBEqFullnessState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt8_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instBEqFullnessState___closed__0 = (const lean_object*)&l_Lean_Fmt_instBEqFullnessState___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instBEqFullnessState = (const lean_object*)&l_Lean_Fmt_instBEqFullnessState___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_Fmt_instHashableFullnessState___aux__1(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableFullnessState___aux__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Fmt_instHashableFullnessState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt8_toUInt64___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instHashableFullnessState___closed__0 = (const lean_object*)&l_Lean_Fmt_instHashableFullnessState___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instHashableFullnessState = (const lean_object*)&l_Lean_Fmt_instHashableFullnessState___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessState_mk(uint8_t, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessState_mk___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessState_isFullBefore(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessState_isFullBefore___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessState_isFullAfter(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessState_isFullAfter___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessState_isInitialBefore(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessState_isInitialBefore___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessState_isInitialAfter(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessState_isInitialAfter___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessState_setFullBefore(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessState_setFullBefore___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessState_setFullAfter(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessState_setFullAfter___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessState_setInitialBefore(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessState_setInitialBefore___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessState_setInitialAfter(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessState_setInitialAfter___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessStateSet_contains(uint16_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_contains___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_ofPredBelow(lean_object*, lean_object*, uint16_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_ofPred(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPred___boxed(lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_finalAny(uint16_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_finalAny___boxed(lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_finalAll(uint16_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_finalAll___boxed(lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_initialAny(uint16_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_initialAny___boxed(lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_initialAll(uint16_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_initialAll___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessStateSet_anySplit___lam__0(uint8_t, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_anySplit___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessStateSet_anySplit___lam__1(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_anySplit___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_anySplit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_anySplit___boxed(lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_newlineFailureSet_spec__0(lean_object*, uint16_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_newlineFailureSet_spec__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_newlineFailureSet___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l_Lean_Fmt_newlineFailureSet___closed__0;
LEAN_EXPORT uint16_t l_Lean_Fmt_newlineFailureSet;
LEAN_EXPORT uint8_t l_Lean_Fmt_textFails___lam__0(uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_textFails___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_textFails(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_textFails___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_emptyTextFailureSet_spec__0(lean_object*, uint16_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_emptyTextFailureSet_spec__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_emptyTextFailureSet___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_emptyTextFailureSet___closed__0;
LEAN_EXPORT uint16_t l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_emptyTextFailureSet;
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_nonEmptyTextFailureSet_spec__0(lean_object*, uint16_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_nonEmptyTextFailureSet_spec__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_nonEmptyTextFailureSet___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_nonEmptyTextFailureSet___closed__0;
LEAN_EXPORT uint16_t l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_nonEmptyTextFailureSet;
LEAN_EXPORT uint16_t l_Lean_Fmt_textFailureSet(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_textFailureSet___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTagId___aux__1;
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTagId;
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqTagId___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqTagId___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_instBEqTagId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instBEqTagId___closed__0 = (const lean_object*)&l_Lean_Fmt_instBEqTagId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instBEqTagId = (const lean_object*)&l_Lean_Fmt_instBEqTagId___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_Fmt_instHashableTagId___aux__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableTagId___aux__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Fmt_instHashableTagId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_ofNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instHashableTagId___closed__0 = (const lean_object*)&l_Lean_Fmt_instHashableTagId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instHashableTagId = (const lean_object*)&l_Lean_Fmt_instHashableTagId___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Fmt_instOrdTagId___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instOrdTagId___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_instOrdTagId___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instOrdTagId___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_instOrdTagId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_instOrdTagId___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instOrdTagId___closed__0 = (const lean_object*)&l_Lean_Fmt_instOrdTagId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instOrdTagId = (const lean_object*)&l_Lean_Fmt_instOrdTagId___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprTagId___aux__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprTagId___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprTagId___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprTagId___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprTagId___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_instReprTagId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_instReprTagId___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instReprTagId___closed__0 = (const lean_object*)&l_Lean_Fmt_instReprTagId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instReprTagId = (const lean_object*)&l_Lean_Fmt_instReprTagId___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_instToStringTagId___aux__1(lean_object*);
static const lean_closure_object l_Lean_Fmt_instToStringTagId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_reprFast, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instToStringTagId___closed__0 = (const lean_object*)&l_Lean_Fmt_instToStringTagId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instToStringTagId = (const lean_object*)&l_Lean_Fmt_instToStringTagId___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_instHAddTagIdNat___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instHAddTagIdNat___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_instHAddTagIdNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instHAddTagIdNat___closed__0 = (const lean_object*)&l_Lean_Fmt_instHAddTagIdNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instHAddTagIdNat = (const lean_object*)&l_Lean_Fmt_instHAddTagIdNat___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmpty_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmpty_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmpty_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmpty_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmptyIfFlattened_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmptyIfFlattened_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmptyIfFlattened_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmptyIfFlattened_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_sometimesNonEmpty_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_sometimesNonEmpty_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_sometimesNonEmpty_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_sometimesNonEmpty_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_max___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_max___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_AlwaysEmptiness_max(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_max___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_alwaysNonEmpty_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_alwaysNonEmpty_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_alwaysNonEmpty_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_alwaysNonEmpty_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_sometimesEmpty_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_sometimesEmpty_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_sometimesEmpty_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_sometimesEmpty_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_max___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_max___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_AlwaysNonEmptiness_max(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_max___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomic_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomic_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomic_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomic_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomicIfFlattened_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomicIfFlattened_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomicIfFlattened_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomicIfFlattened_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomic_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomic_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomic_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomic_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomicIfFlattened_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomicIfFlattened_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomicIfFlattened_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomicIfFlattened_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_nonAtomic_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_nonAtomic_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_nonAtomic_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_nonAtomic_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_max___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_max___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_Atomicness_max(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_max___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_instReprAssertion___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "<assertion>"};
static const lean_object* l_Lean_Fmt_instReprAssertion___lam__0___closed__0 = (const lean_object*)&l_Lean_Fmt_instReprAssertion___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_instReprAssertion___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprAssertion___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Fmt_instReprAssertion___lam__0___closed__1 = (const lean_object*)&l_Lean_Fmt_instReprAssertion___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprAssertion___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprAssertion___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_instReprAssertion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_instReprAssertion___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instReprAssertion___closed__0 = (const lean_object*)&l_Lean_Fmt_instReprAssertion___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instReprAssertion = (const lean_object*)&l_Lean_Fmt_instReprAssertion___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_ctorIdx___impl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_failure_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_failure_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_newline_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_newline_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_text_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_text_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_tagged_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_tagged_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_flattened_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_flattened_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unflattenable_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unflattenable_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_indented_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_indented_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_aligned_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_aligned_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unindented_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unindented_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_final_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_final_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_initial_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_initial_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_free_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_free_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_guarded_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_guarded_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_costing_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_costing_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_either_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_either_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_append_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_append_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_failureSet_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_failureSet_match__1_splitter___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_failureSet_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_failureSet_match__1_splitter___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_maxNewlineCount_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_maxNewlineCount_x3f_match__1_splitter___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_maxNewlineCount_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_maxNewlineCount_x3f_match__1_splitter___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__2_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__2_splitter___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__2_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__2_splitter___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__4_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__4_splitter___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__4_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__4_splitter___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_casesOn___override___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_casesOn___override___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_casesOn___override(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_casesOn___override___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_failure___override___redArg();
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_failure___override___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_failure___override(lean_object*);
static const lean_ctor_object l_Lean_Fmt_Doc_newline___override___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_Doc_newline___override___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_Doc_newline___override___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Fmt_Doc_newline___override___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l_Lean_Fmt_Doc_newline___override___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_newline___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_newline___override(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Fmt_Doc_text___override___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_Doc_text___override___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_Doc_text___override___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_text___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_text___override(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_atomicness___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_atomicness___override___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg___boxed(lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_Doc_neverFailsSet___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_neverFailsSet___override___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg___boxed(lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_Doc_failureSet___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_failureSet___override___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_tagged___override___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_tagged___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_flattened___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_flattened___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unflattenable___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unflattenable___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_indented___override___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_indented___override___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_indented___override(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_indented___override___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_aligned___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_aligned___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unindented___override___redArg(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unindented___override___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unindented___override(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unindented___override___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_final___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_final___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_initial___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_initial___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_free___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_free___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_guarded___override___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_guarded___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_costing___override___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_costing___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_either___override___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_either___override___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_Doc_either___override___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Doc_either___override___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_Doc_either___override___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_Doc_either___override___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_either___override___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_either___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_Doc_failureSet___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_failureSet___override___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maxNewlineCount_x3f___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_alwaysEmptiness___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_alwaysEmptiness___override___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_alwaysNonEmptiness___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_alwaysNonEmptiness___override___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_atomicness___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_atomicness___override___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_Doc_neverFailsSet___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_neverFailsSet___override___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg___lam__0(uint8_t, uint16_t, uint8_t, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg(uint16_t, uint8_t, lean_object*, lean_object*, uint16_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16___redArg(uint16_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15_spec__21___redArg___lam__0(uint8_t, uint16_t, uint16_t, lean_object*, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15_spec__21___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15_spec__21___redArg(uint16_t, lean_object*, uint16_t, lean_object*, uint16_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15___redArg(uint16_t, lean_object*, uint16_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_append___override___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_append___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15(uint16_t, lean_object*, lean_object*, uint16_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16(uint16_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15_spec__21(uint16_t, lean_object*, lean_object*, uint16_t, lean_object*, uint16_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23(uint16_t, uint8_t, lean_object*, lean_object*, lean_object*, uint16_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedDoc_default___redArg();
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedDoc_default___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedDoc_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedDoc___redArg();
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedDoc___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedDoc(lean_object*);
static const lean_string_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Fmt.Doc.failure"};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__2;
static lean_once_cell_t l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__3;
static const lean_string_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Fmt.Doc.newline"};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__5_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__6_value;
static const lean_string_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.Fmt.Doc.text"};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__7 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__7_value)}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__8_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__9_value;
static const lean_string_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Fmt.Doc.tagged"};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__10 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__10_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__10_value)}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__11_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__11_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__12 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__12_value;
static const lean_string_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Fmt.Doc.flattened"};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__13 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__13_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__13_value)}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__14 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__14_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__14_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__15 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__15_value;
static const lean_string_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.Fmt.Doc.unflattenable"};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__16 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__16_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__16_value)}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__17 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__17_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__17_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__18 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__18_value;
static const lean_string_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Fmt.Doc.indented"};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__19 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__19_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__19_value)}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__20 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__20_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__20_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__21 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__21_value;
static const lean_string_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Fmt.Doc.aligned"};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__22 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__22_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__22_value)}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__23 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__23_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__23_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__24 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__24_value;
static const lean_string_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Fmt.Doc.unindented"};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__25 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__25_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__25_value)}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__26 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__26_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__26_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__27 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__27_value;
static const lean_string_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Lean.Fmt.Doc.final"};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__28 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__28_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__28_value)}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__29 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__29_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__29_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__30 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__30_value;
static const lean_string_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Fmt.Doc.initial"};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__31 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__31_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__31_value)}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__32 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__32_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__32_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__33 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__33_value;
static const lean_string_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.Fmt.Doc.free"};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__34 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__34_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__34_value)}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__35 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__35_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__35_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__36 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__36_value;
static const lean_string_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Fmt.Doc.guarded"};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__37 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__37_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__37_value)}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__38 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__38_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__38_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__39 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__39_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__39_value),((lean_object*)&l_Lean_Fmt_instReprAssertion___lam__0___closed__1_value)}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__40 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__40_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__40_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__41 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__41_value;
static const lean_string_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Fmt.Doc.costing"};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__42 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__42_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__42_value)}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__43 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__43_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__43_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__44 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__44_value;
static const lean_string_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Fmt.Doc.either"};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__45 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__45_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__45_value)}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__46 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__46_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__46_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__47 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__47_value;
static const lean_string_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Fmt.Doc.append"};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__48 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__48_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__48_value)}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__49 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__49_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__49_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__50 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__50_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprDoc_repr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprDoc_repr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprDoc_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprDoc___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprDoc(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isFailure___redArg(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isFailure___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isFailure(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isFailure___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_neverFails___redArg(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_neverFails___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_neverFails(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_neverFails___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_hasContextDependentFailure___redArg(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_hasContextDependentFailure___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_hasContextDependentFailure(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_hasContextDependentFailure___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isAlwaysEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isAlwaysEmpty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isAlwaysEmpty___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isAlwaysNonEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isAlwaysNonEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isAlwaysNonEmpty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isAlwaysNonEmpty___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isCompoundAtomic___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isCompoundAtomic___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isCompoundAtomic(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isCompoundAtomic___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isAtomic___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isAtomic___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isAtomic(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isAtomic___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_Doc_empty___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Fmt_Doc_empty___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_Doc_empty___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Fmt_Doc_empty___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Doc_empty___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_empty___redArg();
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_empty___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Fmt_Doc_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Doc_empty___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maybeFlattened___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maybeFlattened(lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_Doc_nl___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_Fmt_Doc_nl___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_Doc_nl___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Fmt_Doc_nl___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Doc_nl___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_nl___redArg();
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_nl___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Fmt_Doc_nl___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Doc_nl___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_nl(lean_object*);
static lean_once_cell_t l_Lean_Fmt_Doc_break___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Doc_break___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_break___redArg();
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_break___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Fmt_Doc_break___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Doc_break___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_break(lean_object*);
static lean_once_cell_t l_Lean_Fmt_Doc_hardNl___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Doc_hardNl___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_hardNl___redArg();
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_hardNl___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Fmt_Doc_hardNl___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Doc_hardNl___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_hardNl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_nested___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_nested(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_hardNested___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_hardNested(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_oneOf_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_oneOf___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_oneOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_oneOf_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instAppendDoc___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_instAppendDoc___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_instAppendDoc___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instAppendDoc___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_instAppendDoc___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_instAppendDoc___redArg();
LEAN_EXPORT lean_object* l_Lean_Fmt_instAppendDoc___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instAppendDoc(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_join_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_join___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_join(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_join_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_joinUsing_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_joinUsing___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_joinUsing(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_joinUsing_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillWith_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillWith_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillWith___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillWith___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillWith(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillWith___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillWith_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillWith_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_Doc_fill___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Doc_fill___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fill___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fill___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Fmt_Doc_fill___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Doc_fill___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_Doc_fill___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_Doc_fill___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fill___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fill___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fill(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fill___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsing___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsing___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsing___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsing___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsing(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsing___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_Doc_fillUsingSpace___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Doc_fillUsingSpace___redArg___lam__0___closed__0;
static lean_once_cell_t l_Lean_Fmt_Doc_fillUsingSpace___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Doc_fillUsingSpace___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpace___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpace___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Fmt_Doc_fillUsingSpace___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Doc_fillUsingSpace___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_Doc_fillUsingSpace___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_Doc_fillUsingSpace___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpace___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpace___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpace___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__0___redArg(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__2___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__1___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg___closed__0_value;
static const lean_array_object l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg___closed__1 = (const lean_object*)&l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrappingWith_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrappingWith_spec__0___redArg___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrappingWith_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrappingWith_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrappingWith_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrappingWith_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillWrappingWith___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillWrappingWith(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrappingWith_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrappingWith_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_Doc_fillWrapping___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Doc_fillWrapping___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillWrapping___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillWrapping___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Fmt_Doc_fillWrapping___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Doc_fillWrapping___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_Doc_fillWrapping___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_Doc_fillWrapping___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillWrapping___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillWrapping(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWrapping(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedFillable_default___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedFillable_default(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedFillable___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedFillable(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0___redArg(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3___redArg(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Fmt_Doc_splitFillGroups_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_splitBy_loop___at___00List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_splitFillGroups___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_splitFillGroups(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Fmt_Doc_splitFillGroups_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_splitBy_loop___at___00List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0___redArg(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillSomeUsingSpace___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillSomeUsingSpace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_instInhabitedPtrKey_default___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_Fmt_instInhabitedPtrKey_default___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedPtrKey_default___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedPtrKey_default(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedPtrKey___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedPtrKey(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_PtrKey_ofKey___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_PtrKey_ofKey(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqPtrKey___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqPtrKey___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_instBEqPtrKey___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_instBEqPtrKey___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instBEqPtrKey___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_instBEqPtrKey___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqPtrKey___redArg();
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqPtrKey___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqPtrKey(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Fmt_instHashablePtrKey___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashablePtrKey___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Fmt_instHashablePtrKey___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_instHashablePtrKey___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instHashablePtrKey___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_instHashablePtrKey___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashablePtrKey___redArg();
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashablePtrKey___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashablePtrKey(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqBEqCacheKey_beq___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqBEqCacheKey_beq___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqBEqCacheKey_beq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqBEqCacheKey_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqBEqCacheKey___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqBEqCacheKey(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Fmt_instHashableBEqCacheKey_hash___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableBEqCacheKey_hash___redArg___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Fmt_instHashableBEqCacheKey_hash(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableBEqCacheKey_hash___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableBEqCacheKey___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableBEqCacheKey(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized_unsafe__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized_unsafe__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized_unsafe__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized_unsafe__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_Doc_beq___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Doc_beq___redArg___closed__0;
static lean_once_cell_t l_Lean_Fmt_Doc_beq___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Doc_beq___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_beq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqDocOfHashable___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqDocOfHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqDocOfHashable(lean_object*, lean_object*, lean_object*);
static uint8_t _init_l_Lean_Fmt_instInhabitedFullnessState___aux__1(void){
_start:
{
uint8_t v___x_1_; 
v___x_1_ = 0;
return v___x_1_;
}
}
static uint8_t _init_l_Lean_Fmt_instInhabitedFullnessState(void){
_start:
{
uint8_t v___x_2_; 
v___x_2_ = 0;
return v___x_2_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqFullnessState___aux__1(uint8_t v_a_3_, uint8_t v_b_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = lean_uint8_dec_eq(v_a_3_, v_b_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqFullnessState___aux__1___boxed(lean_object* v_a_6_, lean_object* v_b_7_){
_start:
{
uint8_t v_a_boxed_8_; uint8_t v_b_boxed_9_; uint8_t v_res_10_; lean_object* v_r_11_; 
v_a_boxed_8_ = lean_unbox(v_a_6_);
v_b_boxed_9_ = lean_unbox(v_b_7_);
v_res_10_ = l_Lean_Fmt_instBEqFullnessState___aux__1(v_a_boxed_8_, v_b_boxed_9_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
LEAN_EXPORT uint64_t l_Lean_Fmt_instHashableFullnessState___aux__1(uint8_t v_n_14_){
_start:
{
uint64_t v___x_15_; 
v___x_15_ = lean_uint8_to_uint64(v_n_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableFullnessState___aux__1___boxed(lean_object* v_n_16_){
_start:
{
uint8_t v_n_boxed_17_; uint64_t v_res_18_; lean_object* v_r_19_; 
v_n_boxed_17_ = lean_unbox(v_n_16_);
v_res_18_ = l_Lean_Fmt_instHashableFullnessState___aux__1(v_n_boxed_17_);
v_r_19_ = lean_box_uint64(v_res_18_);
return v_r_19_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessState_mk(uint8_t v_isFullBefore_22_, uint8_t v_isFullAfter_23_, uint8_t v_isInitialBefore_24_, uint8_t v_isInitialAfter_25_){
_start:
{
uint8_t v___x_26_; uint8_t v___x_27_; uint8_t v___x_28_; uint8_t v___x_29_; uint8_t v___x_30_; uint8_t v___x_31_; uint8_t v___x_32_; uint8_t v___x_33_; uint8_t v___x_34_; uint8_t v___x_35_; uint8_t v___x_36_; uint8_t v___x_37_; uint8_t v___x_38_; 
v___x_26_ = lean_bool_to_uint8(v_isInitialBefore_24_);
v___x_27_ = 3;
v___x_28_ = lean_uint8_shift_left(v___x_26_, v___x_27_);
v___x_29_ = lean_bool_to_uint8(v_isInitialAfter_25_);
v___x_30_ = 2;
v___x_31_ = lean_uint8_shift_left(v___x_29_, v___x_30_);
v___x_32_ = lean_uint8_lor(v___x_28_, v___x_31_);
v___x_33_ = lean_bool_to_uint8(v_isFullBefore_22_);
v___x_34_ = 1;
v___x_35_ = lean_uint8_shift_left(v___x_33_, v___x_34_);
v___x_36_ = lean_uint8_lor(v___x_32_, v___x_35_);
v___x_37_ = lean_bool_to_uint8(v_isFullAfter_23_);
v___x_38_ = lean_uint8_lor(v___x_36_, v___x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessState_mk___boxed(lean_object* v_isFullBefore_39_, lean_object* v_isFullAfter_40_, lean_object* v_isInitialBefore_41_, lean_object* v_isInitialAfter_42_){
_start:
{
uint8_t v_isFullBefore_boxed_43_; uint8_t v_isFullAfter_boxed_44_; uint8_t v_isInitialBefore_boxed_45_; uint8_t v_isInitialAfter_boxed_46_; uint8_t v_res_47_; lean_object* v_r_48_; 
v_isFullBefore_boxed_43_ = lean_unbox(v_isFullBefore_39_);
v_isFullAfter_boxed_44_ = lean_unbox(v_isFullAfter_40_);
v_isInitialBefore_boxed_45_ = lean_unbox(v_isInitialBefore_41_);
v_isInitialAfter_boxed_46_ = lean_unbox(v_isInitialAfter_42_);
v_res_47_ = l_Lean_Fmt_FullnessState_mk(v_isFullBefore_boxed_43_, v_isFullAfter_boxed_44_, v_isInitialBefore_boxed_45_, v_isInitialAfter_boxed_46_);
v_r_48_ = lean_box(v_res_47_);
return v_r_48_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessState_isFullBefore(uint8_t v_s_49_){
_start:
{
uint8_t v___x_50_; uint8_t v___x_51_; uint8_t v___x_52_; uint8_t v___x_53_; 
v___x_50_ = 2;
v___x_51_ = lean_uint8_land(v_s_49_, v___x_50_);
v___x_52_ = 0;
v___x_53_ = lean_uint8_dec_eq(v___x_51_, v___x_52_);
if (v___x_53_ == 0)
{
uint8_t v___x_54_; 
v___x_54_ = 1;
return v___x_54_;
}
else
{
uint8_t v___x_55_; 
v___x_55_ = 0;
return v___x_55_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessState_isFullBefore___boxed(lean_object* v_s_56_){
_start:
{
uint8_t v_s_boxed_57_; uint8_t v_res_58_; lean_object* v_r_59_; 
v_s_boxed_57_ = lean_unbox(v_s_56_);
v_res_58_ = l_Lean_Fmt_FullnessState_isFullBefore(v_s_boxed_57_);
v_r_59_ = lean_box(v_res_58_);
return v_r_59_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessState_isFullAfter(uint8_t v_s_60_){
_start:
{
uint8_t v___x_61_; uint8_t v___x_62_; uint8_t v___x_63_; uint8_t v___x_64_; 
v___x_61_ = 1;
v___x_62_ = lean_uint8_land(v_s_60_, v___x_61_);
v___x_63_ = 0;
v___x_64_ = lean_uint8_dec_eq(v___x_62_, v___x_63_);
if (v___x_64_ == 0)
{
uint8_t v___x_65_; 
v___x_65_ = 1;
return v___x_65_;
}
else
{
uint8_t v___x_66_; 
v___x_66_ = 0;
return v___x_66_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessState_isFullAfter___boxed(lean_object* v_s_67_){
_start:
{
uint8_t v_s_boxed_68_; uint8_t v_res_69_; lean_object* v_r_70_; 
v_s_boxed_68_ = lean_unbox(v_s_67_);
v_res_69_ = l_Lean_Fmt_FullnessState_isFullAfter(v_s_boxed_68_);
v_r_70_ = lean_box(v_res_69_);
return v_r_70_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessState_isInitialBefore(uint8_t v_s_71_){
_start:
{
uint8_t v___x_72_; uint8_t v___x_73_; uint8_t v___x_74_; uint8_t v___x_75_; 
v___x_72_ = 8;
v___x_73_ = lean_uint8_land(v_s_71_, v___x_72_);
v___x_74_ = 0;
v___x_75_ = lean_uint8_dec_eq(v___x_73_, v___x_74_);
if (v___x_75_ == 0)
{
uint8_t v___x_76_; 
v___x_76_ = 1;
return v___x_76_;
}
else
{
uint8_t v___x_77_; 
v___x_77_ = 0;
return v___x_77_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessState_isInitialBefore___boxed(lean_object* v_s_78_){
_start:
{
uint8_t v_s_boxed_79_; uint8_t v_res_80_; lean_object* v_r_81_; 
v_s_boxed_79_ = lean_unbox(v_s_78_);
v_res_80_ = l_Lean_Fmt_FullnessState_isInitialBefore(v_s_boxed_79_);
v_r_81_ = lean_box(v_res_80_);
return v_r_81_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessState_isInitialAfter(uint8_t v_s_82_){
_start:
{
uint8_t v___x_83_; uint8_t v___x_84_; uint8_t v___x_85_; uint8_t v___x_86_; 
v___x_83_ = 4;
v___x_84_ = lean_uint8_land(v_s_82_, v___x_83_);
v___x_85_ = 0;
v___x_86_ = lean_uint8_dec_eq(v___x_84_, v___x_85_);
if (v___x_86_ == 0)
{
uint8_t v___x_87_; 
v___x_87_ = 1;
return v___x_87_;
}
else
{
uint8_t v___x_88_; 
v___x_88_ = 0;
return v___x_88_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessState_isInitialAfter___boxed(lean_object* v_s_89_){
_start:
{
uint8_t v_s_boxed_90_; uint8_t v_res_91_; lean_object* v_r_92_; 
v_s_boxed_90_ = lean_unbox(v_s_89_);
v_res_91_ = l_Lean_Fmt_FullnessState_isInitialAfter(v_s_boxed_90_);
v_r_92_ = lean_box(v_res_91_);
return v_r_92_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessState_setFullBefore(uint8_t v_s_93_, uint8_t v_isFullBefore_94_){
_start:
{
uint8_t v___x_95_; uint8_t v___x_96_; uint8_t v___x_97_; uint8_t v___x_98_; uint8_t v___x_99_; uint8_t v___x_100_; 
v___x_95_ = 253;
v___x_96_ = lean_uint8_land(v_s_93_, v___x_95_);
v___x_97_ = lean_bool_to_uint8(v_isFullBefore_94_);
v___x_98_ = 1;
v___x_99_ = lean_uint8_shift_left(v___x_97_, v___x_98_);
v___x_100_ = lean_uint8_lor(v___x_96_, v___x_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessState_setFullBefore___boxed(lean_object* v_s_101_, lean_object* v_isFullBefore_102_){
_start:
{
uint8_t v_s_boxed_103_; uint8_t v_isFullBefore_boxed_104_; uint8_t v_res_105_; lean_object* v_r_106_; 
v_s_boxed_103_ = lean_unbox(v_s_101_);
v_isFullBefore_boxed_104_ = lean_unbox(v_isFullBefore_102_);
v_res_105_ = l_Lean_Fmt_FullnessState_setFullBefore(v_s_boxed_103_, v_isFullBefore_boxed_104_);
v_r_106_ = lean_box(v_res_105_);
return v_r_106_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessState_setFullAfter(uint8_t v_s_107_, uint8_t v_isFullAfter_108_){
_start:
{
uint8_t v___x_109_; uint8_t v___x_110_; uint8_t v___x_111_; uint8_t v___x_112_; 
v___x_109_ = 254;
v___x_110_ = lean_uint8_land(v_s_107_, v___x_109_);
v___x_111_ = lean_bool_to_uint8(v_isFullAfter_108_);
v___x_112_ = lean_uint8_lor(v___x_110_, v___x_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessState_setFullAfter___boxed(lean_object* v_s_113_, lean_object* v_isFullAfter_114_){
_start:
{
uint8_t v_s_boxed_115_; uint8_t v_isFullAfter_boxed_116_; uint8_t v_res_117_; lean_object* v_r_118_; 
v_s_boxed_115_ = lean_unbox(v_s_113_);
v_isFullAfter_boxed_116_ = lean_unbox(v_isFullAfter_114_);
v_res_117_ = l_Lean_Fmt_FullnessState_setFullAfter(v_s_boxed_115_, v_isFullAfter_boxed_116_);
v_r_118_ = lean_box(v_res_117_);
return v_r_118_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessState_setInitialBefore(uint8_t v_s_119_, uint8_t v_isInitialBefore_120_){
_start:
{
uint8_t v___x_121_; uint8_t v___x_122_; uint8_t v___x_123_; uint8_t v___x_124_; uint8_t v___x_125_; uint8_t v___x_126_; 
v___x_121_ = 247;
v___x_122_ = lean_uint8_land(v_s_119_, v___x_121_);
v___x_123_ = lean_bool_to_uint8(v_isInitialBefore_120_);
v___x_124_ = 3;
v___x_125_ = lean_uint8_shift_left(v___x_123_, v___x_124_);
v___x_126_ = lean_uint8_lor(v___x_122_, v___x_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessState_setInitialBefore___boxed(lean_object* v_s_127_, lean_object* v_isInitialBefore_128_){
_start:
{
uint8_t v_s_boxed_129_; uint8_t v_isInitialBefore_boxed_130_; uint8_t v_res_131_; lean_object* v_r_132_; 
v_s_boxed_129_ = lean_unbox(v_s_127_);
v_isInitialBefore_boxed_130_ = lean_unbox(v_isInitialBefore_128_);
v_res_131_ = l_Lean_Fmt_FullnessState_setInitialBefore(v_s_boxed_129_, v_isInitialBefore_boxed_130_);
v_r_132_ = lean_box(v_res_131_);
return v_r_132_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessState_setInitialAfter(uint8_t v_s_133_, uint8_t v_isInitialAfter_134_){
_start:
{
uint8_t v___x_135_; uint8_t v___x_136_; uint8_t v___x_137_; uint8_t v___x_138_; uint8_t v___x_139_; uint8_t v___x_140_; 
v___x_135_ = 251;
v___x_136_ = lean_uint8_land(v_s_133_, v___x_135_);
v___x_137_ = lean_bool_to_uint8(v_isInitialAfter_134_);
v___x_138_ = 2;
v___x_139_ = lean_uint8_shift_left(v___x_137_, v___x_138_);
v___x_140_ = lean_uint8_lor(v___x_136_, v___x_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessState_setInitialAfter___boxed(lean_object* v_s_141_, lean_object* v_isInitialAfter_142_){
_start:
{
uint8_t v_s_boxed_143_; uint8_t v_isInitialAfter_boxed_144_; uint8_t v_res_145_; lean_object* v_r_146_; 
v_s_boxed_143_ = lean_unbox(v_s_141_);
v_isInitialAfter_boxed_144_ = lean_unbox(v_isInitialAfter_142_);
v_res_145_ = l_Lean_Fmt_FullnessState_setInitialAfter(v_s_boxed_143_, v_isInitialAfter_boxed_144_);
v_r_146_ = lean_box(v_res_145_);
return v_r_146_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessStateSet_contains(uint16_t v_set_147_, uint8_t v_s_148_){
_start:
{
uint16_t v___x_149_; uint16_t v___x_150_; uint16_t v___x_151_; uint16_t v___x_152_; uint16_t v___x_153_; uint8_t v___x_154_; 
v___x_149_ = lean_uint8_to_uint16(v_s_148_);
v___x_150_ = lean_uint16_shift_right(v_set_147_, v___x_149_);
v___x_151_ = 1;
v___x_152_ = lean_uint16_land(v___x_150_, v___x_151_);
v___x_153_ = 0;
v___x_154_ = lean_uint16_dec_eq(v___x_152_, v___x_153_);
if (v___x_154_ == 0)
{
uint8_t v___x_155_; 
v___x_155_ = 1;
return v___x_155_;
}
else
{
uint8_t v___x_156_; 
v___x_156_ = 0;
return v___x_156_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_contains___boxed(lean_object* v_set_157_, lean_object* v_s_158_){
_start:
{
uint16_t v_set_boxed_159_; uint8_t v_s_boxed_160_; uint8_t v_res_161_; lean_object* v_r_162_; 
v_set_boxed_159_ = lean_unbox(v_set_157_);
v_s_boxed_160_ = lean_unbox(v_s_158_);
v_res_161_ = l_Lean_Fmt_FullnessStateSet_contains(v_set_boxed_159_, v_s_boxed_160_);
v_r_162_ = lean_box(v_res_161_);
return v_r_162_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_ofPredBelow(lean_object* v_p_163_, lean_object* v_x_164_, uint16_t v_x_165_){
_start:
{
lean_object* v_zero_166_; uint8_t v_isZero_167_; 
v_zero_166_ = lean_unsigned_to_nat(0u);
v_isZero_167_ = lean_nat_dec_eq(v_x_164_, v_zero_166_);
if (v_isZero_167_ == 1)
{
lean_dec(v_x_164_);
lean_dec_ref(v_p_163_);
return v_x_165_;
}
else
{
lean_object* v_one_168_; lean_object* v_n_169_; uint8_t v_s_170_; lean_object* v___x_171_; lean_object* v___x_172_; uint8_t v___x_173_; 
v_one_168_ = lean_unsigned_to_nat(1u);
v_n_169_ = lean_nat_sub(v_x_164_, v_one_168_);
lean_dec(v_x_164_);
v_s_170_ = lean_uint8_of_nat(v_n_169_);
v___x_171_ = lean_box(v_s_170_);
lean_inc_ref(v_p_163_);
v___x_172_ = lean_apply_1(v_p_163_, v___x_171_);
v___x_173_ = lean_unbox(v___x_172_);
if (v___x_173_ == 0)
{
v_x_164_ = v_n_169_;
goto _start;
}
else
{
uint16_t v___x_175_; uint16_t v___x_176_; uint16_t v___x_177_; uint16_t v___x_178_; 
v___x_175_ = 1;
v___x_176_ = lean_uint16_of_nat(v_n_169_);
v___x_177_ = lean_uint16_shift_left(v___x_175_, v___x_176_);
v___x_178_ = lean_uint16_lor(v_x_165_, v___x_177_);
v_x_164_ = v_n_169_;
v_x_165_ = v___x_178_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___boxed(lean_object* v_p_180_, lean_object* v_x_181_, lean_object* v_x_182_){
_start:
{
uint16_t v_x_68__boxed_183_; uint16_t v_res_184_; lean_object* v_r_185_; 
v_x_68__boxed_183_ = lean_unbox(v_x_182_);
v_res_184_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow(v_p_180_, v_x_181_, v_x_68__boxed_183_);
v_r_185_ = lean_box(v_res_184_);
return v_r_185_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_ofPred(lean_object* v_p_186_){
_start:
{
lean_object* v___x_187_; uint16_t v___x_188_; uint16_t v___x_189_; 
v___x_187_ = lean_unsigned_to_nat(16u);
v___x_188_ = 0;
v___x_189_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow(v_p_186_, v___x_187_, v___x_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPred___boxed(lean_object* v_p_190_){
_start:
{
uint16_t v_res_191_; lean_object* v_r_192_; 
v_res_191_ = l_Lean_Fmt_FullnessStateSet_ofPred(v_p_190_);
v_r_192_ = lean_box(v_res_191_);
return v_r_192_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_finalAny(uint16_t v_inner_193_){
_start:
{
uint16_t v___x_194_; uint16_t v___x_195_; uint16_t v___x_196_; uint16_t v___x_197_; uint16_t v___x_198_; 
v___x_194_ = 1;
v___x_195_ = lean_uint16_shift_left(v_inner_193_, v___x_194_);
v___x_196_ = lean_uint16_lor(v___x_195_, v_inner_193_);
v___x_197_ = 43690;
v___x_198_ = lean_uint16_land(v___x_196_, v___x_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_finalAny___boxed(lean_object* v_inner_199_){
_start:
{
uint16_t v_inner_boxed_200_; uint16_t v_res_201_; lean_object* v_r_202_; 
v_inner_boxed_200_ = lean_unbox(v_inner_199_);
v_res_201_ = l_Lean_Fmt_FullnessStateSet_finalAny(v_inner_boxed_200_);
v_r_202_ = lean_box(v_res_201_);
return v_r_202_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_finalAll(uint16_t v_inner_203_){
_start:
{
uint16_t v___x_204_; uint16_t v___x_205_; uint16_t v___x_206_; uint16_t v___x_207_; uint16_t v___x_208_; 
v___x_204_ = 1;
v___x_205_ = lean_uint16_shift_left(v_inner_203_, v___x_204_);
v___x_206_ = lean_uint16_land(v___x_205_, v_inner_203_);
v___x_207_ = 43690;
v___x_208_ = lean_uint16_land(v___x_206_, v___x_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_finalAll___boxed(lean_object* v_inner_209_){
_start:
{
uint16_t v_inner_boxed_210_; uint16_t v_res_211_; lean_object* v_r_212_; 
v_inner_boxed_210_ = lean_unbox(v_inner_209_);
v_res_211_ = l_Lean_Fmt_FullnessStateSet_finalAll(v_inner_boxed_210_);
v_r_212_ = lean_box(v_res_211_);
return v_r_212_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_initialAny(uint16_t v_inner_213_){
_start:
{
uint16_t v___x_214_; uint16_t v___x_215_; uint16_t v___x_216_; uint16_t v___x_217_; uint16_t v___x_218_; 
v___x_214_ = 8;
v___x_215_ = lean_uint16_shift_left(v_inner_213_, v___x_214_);
v___x_216_ = lean_uint16_lor(v___x_215_, v_inner_213_);
v___x_217_ = 65280;
v___x_218_ = lean_uint16_land(v___x_216_, v___x_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_initialAny___boxed(lean_object* v_inner_219_){
_start:
{
uint16_t v_inner_boxed_220_; uint16_t v_res_221_; lean_object* v_r_222_; 
v_inner_boxed_220_ = lean_unbox(v_inner_219_);
v_res_221_ = l_Lean_Fmt_FullnessStateSet_initialAny(v_inner_boxed_220_);
v_r_222_ = lean_box(v_res_221_);
return v_r_222_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_initialAll(uint16_t v_inner_223_){
_start:
{
uint16_t v___x_224_; uint16_t v___x_225_; uint16_t v___x_226_; uint16_t v___x_227_; uint16_t v___x_228_; 
v___x_224_ = 8;
v___x_225_ = lean_uint16_shift_left(v_inner_223_, v___x_224_);
v___x_226_ = lean_uint16_land(v___x_225_, v_inner_223_);
v___x_227_ = 65280;
v___x_228_ = lean_uint16_land(v___x_226_, v___x_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_initialAll___boxed(lean_object* v_inner_229_){
_start:
{
uint16_t v_inner_boxed_230_; uint16_t v_res_231_; lean_object* v_r_232_; 
v_inner_boxed_230_ = lean_unbox(v_inner_229_);
v_res_231_ = l_Lean_Fmt_FullnessStateSet_initialAll(v_inner_boxed_230_);
v_r_232_ = lean_box(v_res_231_);
return v_r_232_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessStateSet_anySplit___lam__0(uint8_t v_s_233_, lean_object* v_p_234_, uint8_t v_isMidFull_235_, uint8_t v_isMidInitial_236_){
_start:
{
uint8_t v___x_237_; uint8_t v___x_238_; uint8_t v___x_239_; uint8_t v___x_240_; uint8_t v___x_241_; uint8_t v___x_242_; uint8_t v___x_243_; uint8_t v___x_244_; uint8_t v___x_245_; uint8_t v___x_246_; uint8_t v___x_247_; uint8_t v___x_248_; uint8_t v___x_249_; uint8_t v___x_250_; uint8_t v___x_251_; uint8_t v___x_252_; uint8_t v___x_253_; uint8_t v___x_254_; uint8_t v___x_255_; uint8_t v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_237_ = 254;
v___x_238_ = lean_uint8_land(v_s_233_, v___x_237_);
v___x_239_ = lean_bool_to_uint8(v_isMidFull_235_);
v___x_240_ = lean_uint8_lor(v___x_238_, v___x_239_);
v___x_241_ = 251;
v___x_242_ = lean_uint8_land(v___x_240_, v___x_241_);
v___x_243_ = lean_bool_to_uint8(v_isMidInitial_236_);
v___x_244_ = 2;
v___x_245_ = lean_uint8_shift_left(v___x_243_, v___x_244_);
v___x_246_ = lean_uint8_lor(v___x_242_, v___x_245_);
v___x_247_ = 253;
v___x_248_ = lean_uint8_land(v_s_233_, v___x_247_);
v___x_249_ = 1;
v___x_250_ = lean_uint8_shift_left(v___x_239_, v___x_249_);
v___x_251_ = lean_uint8_lor(v___x_248_, v___x_250_);
v___x_252_ = 247;
v___x_253_ = lean_uint8_land(v___x_251_, v___x_252_);
v___x_254_ = 3;
v___x_255_ = lean_uint8_shift_left(v___x_243_, v___x_254_);
v___x_256_ = lean_uint8_lor(v___x_253_, v___x_255_);
v___x_257_ = lean_box(v___x_246_);
v___x_258_ = lean_box(v___x_256_);
v___x_259_ = lean_apply_2(v_p_234_, v___x_257_, v___x_258_);
v___x_260_ = lean_unbox(v___x_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_anySplit___lam__0___boxed(lean_object* v_s_261_, lean_object* v_p_262_, lean_object* v_isMidFull_263_, lean_object* v_isMidInitial_264_){
_start:
{
uint8_t v_s_boxed_265_; uint8_t v_isMidFull_boxed_266_; uint8_t v_isMidInitial_boxed_267_; uint8_t v_res_268_; lean_object* v_r_269_; 
v_s_boxed_265_ = lean_unbox(v_s_261_);
v_isMidFull_boxed_266_ = lean_unbox(v_isMidFull_263_);
v_isMidInitial_boxed_267_ = lean_unbox(v_isMidInitial_264_);
v_res_268_ = l_Lean_Fmt_FullnessStateSet_anySplit___lam__0(v_s_boxed_265_, v_p_262_, v_isMidFull_boxed_266_, v_isMidInitial_boxed_267_);
v_r_269_ = lean_box(v_res_268_);
return v_r_269_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessStateSet_anySplit___lam__1(lean_object* v_p_270_, uint8_t v_s_271_){
_start:
{
uint8_t v___x_272_; uint8_t v___x_273_; 
v___x_272_ = 0;
lean_inc_ref(v_p_270_);
v___x_273_ = l_Lean_Fmt_FullnessStateSet_anySplit___lam__0(v_s_271_, v_p_270_, v___x_272_, v___x_272_);
if (v___x_273_ == 0)
{
uint8_t v___x_274_; uint8_t v___x_275_; 
v___x_274_ = 1;
lean_inc_ref(v_p_270_);
v___x_275_ = l_Lean_Fmt_FullnessStateSet_anySplit___lam__0(v_s_271_, v_p_270_, v___x_273_, v___x_274_);
if (v___x_275_ == 0)
{
uint8_t v___x_276_; 
lean_inc_ref(v_p_270_);
v___x_276_ = l_Lean_Fmt_FullnessStateSet_anySplit___lam__0(v_s_271_, v_p_270_, v___x_274_, v___x_275_);
if (v___x_276_ == 0)
{
uint8_t v___x_277_; 
v___x_277_ = l_Lean_Fmt_FullnessStateSet_anySplit___lam__0(v_s_271_, v_p_270_, v___x_274_, v___x_274_);
return v___x_277_;
}
else
{
lean_dec_ref(v_p_270_);
return v___x_276_;
}
}
else
{
lean_dec_ref(v_p_270_);
return v___x_275_;
}
}
else
{
lean_dec_ref(v_p_270_);
return v___x_273_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_anySplit___lam__1___boxed(lean_object* v_p_278_, lean_object* v_s_279_){
_start:
{
uint8_t v_s_boxed_280_; uint8_t v_res_281_; lean_object* v_r_282_; 
v_s_boxed_280_ = lean_unbox(v_s_279_);
v_res_281_ = l_Lean_Fmt_FullnessStateSet_anySplit___lam__1(v_p_278_, v_s_boxed_280_);
v_r_282_ = lean_box(v_res_281_);
return v_r_282_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_anySplit(lean_object* v_p_283_){
_start:
{
lean_object* v___f_284_; lean_object* v___x_285_; uint16_t v___x_286_; uint16_t v___x_287_; 
v___f_284_ = lean_alloc_closure((void*)(l_Lean_Fmt_FullnessStateSet_anySplit___lam__1___boxed), 2, 1);
lean_closure_set(v___f_284_, 0, v_p_283_);
v___x_285_ = lean_unsigned_to_nat(16u);
v___x_286_ = 0;
v___x_287_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow(v___f_284_, v___x_285_, v___x_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_anySplit___boxed(lean_object* v_p_288_){
_start:
{
uint16_t v_res_289_; lean_object* v_r_290_; 
v_res_289_ = l_Lean_Fmt_FullnessStateSet_anySplit(v_p_288_);
v_r_290_ = lean_box(v_res_289_);
return v_r_290_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_newlineFailureSet_spec__0(lean_object* v_x_291_, uint16_t v_x_292_){
_start:
{
lean_object* v_zero_293_; uint8_t v_isZero_294_; 
v_zero_293_ = lean_unsigned_to_nat(0u);
v_isZero_294_ = lean_nat_dec_eq(v_x_291_, v_zero_293_);
if (v_isZero_294_ == 1)
{
lean_dec(v_x_291_);
return v_x_292_;
}
else
{
lean_object* v_one_295_; lean_object* v_n_296_; uint8_t v_s_303_; uint8_t v___x_304_; uint8_t v___x_305_; uint8_t v___x_306_; uint8_t v___x_307_; 
v_one_295_ = lean_unsigned_to_nat(1u);
v_n_296_ = lean_nat_sub(v_x_291_, v_one_295_);
lean_dec(v_x_291_);
v_s_303_ = lean_uint8_of_nat(v_n_296_);
v___x_304_ = 1;
v___x_305_ = lean_uint8_land(v_s_303_, v___x_304_);
v___x_306_ = 0;
v___x_307_ = lean_uint8_dec_eq(v___x_305_, v___x_306_);
if (v___x_307_ == 0)
{
goto v___jp_297_;
}
else
{
uint8_t v___x_308_; uint8_t v___x_309_; uint8_t v___x_310_; 
v___x_308_ = 8;
v___x_309_ = lean_uint8_land(v_s_303_, v___x_308_);
v___x_310_ = lean_uint8_dec_eq(v___x_309_, v___x_306_);
if (v___x_310_ == 0)
{
goto v___jp_297_;
}
else
{
v_x_291_ = v_n_296_;
goto _start;
}
}
v___jp_297_:
{
uint16_t v___x_298_; uint16_t v___x_299_; uint16_t v___x_300_; uint16_t v___x_301_; 
v___x_298_ = 1;
v___x_299_ = lean_uint16_of_nat(v_n_296_);
v___x_300_ = lean_uint16_shift_left(v___x_298_, v___x_299_);
v___x_301_ = lean_uint16_lor(v_x_292_, v___x_300_);
v_x_291_ = v_n_296_;
v_x_292_ = v___x_301_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_newlineFailureSet_spec__0___boxed(lean_object* v_x_312_, lean_object* v_x_313_){
_start:
{
uint16_t v_x_141__boxed_314_; uint16_t v_res_315_; lean_object* v_r_316_; 
v_x_141__boxed_314_ = lean_unbox(v_x_313_);
v_res_315_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_newlineFailureSet_spec__0(v_x_312_, v_x_141__boxed_314_);
v_r_316_ = lean_box(v_res_315_);
return v_r_316_;
}
}
static uint16_t _init_l_Lean_Fmt_newlineFailureSet___closed__0(void){
_start:
{
uint16_t v___x_317_; lean_object* v___x_318_; uint16_t v___x_319_; 
v___x_317_ = 0;
v___x_318_ = lean_unsigned_to_nat(16u);
v___x_319_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_newlineFailureSet_spec__0(v___x_318_, v___x_317_);
return v___x_319_;
}
}
static uint16_t _init_l_Lean_Fmt_newlineFailureSet(void){
_start:
{
uint16_t v___x_320_; 
v___x_320_ = lean_uint16_once(&l_Lean_Fmt_newlineFailureSet___closed__0, &l_Lean_Fmt_newlineFailureSet___closed__0_once, _init_l_Lean_Fmt_newlineFailureSet___closed__0);
return v___x_320_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_textFails___lam__0(uint8_t v_isEmpty_321_, uint8_t v_before_322_, uint8_t v_after_323_){
_start:
{
if (v_before_322_ == 0)
{
return v_after_323_;
}
else
{
if (v_after_323_ == 0)
{
return v_before_322_;
}
else
{
if (v_isEmpty_321_ == 0)
{
return v_after_323_;
}
else
{
uint8_t v___x_324_; 
v___x_324_ = 0;
return v___x_324_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_textFails___lam__0___boxed(lean_object* v_isEmpty_325_, lean_object* v_before_326_, lean_object* v_after_327_){
_start:
{
uint8_t v_isEmpty_boxed_328_; uint8_t v_before_boxed_329_; uint8_t v_after_boxed_330_; uint8_t v_res_331_; lean_object* v_r_332_; 
v_isEmpty_boxed_328_ = lean_unbox(v_isEmpty_325_);
v_before_boxed_329_ = lean_unbox(v_before_326_);
v_after_boxed_330_ = lean_unbox(v_after_327_);
v_res_331_ = l_Lean_Fmt_textFails___lam__0(v_isEmpty_boxed_328_, v_before_boxed_329_, v_after_boxed_330_);
v_r_332_ = lean_box(v_res_331_);
return v_r_332_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_textFails(uint8_t v_isEmpty_333_, uint8_t v_state_334_){
_start:
{
uint8_t v___y_336_; uint8_t v___y_337_; uint8_t v___y_346_; uint8_t v___y_347_; uint8_t v___y_355_; uint8_t v___x_362_; uint8_t v___x_363_; uint8_t v___x_364_; uint8_t v___x_365_; 
v___x_362_ = 2;
v___x_363_ = lean_uint8_land(v_state_334_, v___x_362_);
v___x_364_ = 0;
v___x_365_ = lean_uint8_dec_eq(v___x_363_, v___x_364_);
if (v___x_365_ == 0)
{
uint8_t v___x_366_; 
v___x_366_ = 1;
v___y_355_ = v___x_366_;
goto v___jp_354_;
}
else
{
uint8_t v___x_367_; 
v___x_367_ = 0;
v___y_355_ = v___x_367_;
goto v___jp_354_;
}
v___jp_335_:
{
uint8_t v___x_338_; uint8_t v___x_339_; uint8_t v___x_340_; uint8_t v___x_341_; 
v___x_338_ = 4;
v___x_339_ = lean_uint8_land(v_state_334_, v___x_338_);
v___x_340_ = 0;
v___x_341_ = lean_uint8_dec_eq(v___x_339_, v___x_340_);
if (v___x_341_ == 0)
{
uint8_t v___x_342_; uint8_t v___x_343_; 
v___x_342_ = 1;
v___x_343_ = l_Lean_Fmt_textFails___lam__0(v_isEmpty_333_, v___y_337_, v___x_342_);
return v___x_343_;
}
else
{
uint8_t v___x_344_; 
v___x_344_ = l_Lean_Fmt_textFails___lam__0(v_isEmpty_333_, v___y_337_, v___y_336_);
return v___x_344_;
}
}
v___jp_345_:
{
uint8_t v___x_348_; 
v___x_348_ = l_Lean_Fmt_textFails___lam__0(v_isEmpty_333_, v___y_346_, v___y_347_);
if (v___x_348_ == 0)
{
uint8_t v___x_349_; uint8_t v___x_350_; uint8_t v___x_351_; uint8_t v___x_352_; 
v___x_349_ = 8;
v___x_350_ = lean_uint8_land(v_state_334_, v___x_349_);
v___x_351_ = 0;
v___x_352_ = lean_uint8_dec_eq(v___x_350_, v___x_351_);
if (v___x_352_ == 0)
{
uint8_t v___x_353_; 
v___x_353_ = 1;
v___y_336_ = v___x_348_;
v___y_337_ = v___x_353_;
goto v___jp_335_;
}
else
{
v___y_336_ = v___x_348_;
v___y_337_ = v___x_348_;
goto v___jp_335_;
}
}
else
{
return v___x_348_;
}
}
v___jp_354_:
{
uint8_t v___x_356_; uint8_t v___x_357_; uint8_t v___x_358_; uint8_t v___x_359_; 
v___x_356_ = 1;
v___x_357_ = lean_uint8_land(v_state_334_, v___x_356_);
v___x_358_ = 0;
v___x_359_ = lean_uint8_dec_eq(v___x_357_, v___x_358_);
if (v___x_359_ == 0)
{
uint8_t v___x_360_; 
v___x_360_ = 1;
v___y_346_ = v___y_355_;
v___y_347_ = v___x_360_;
goto v___jp_345_;
}
else
{
uint8_t v___x_361_; 
v___x_361_ = 0;
v___y_346_ = v___y_355_;
v___y_347_ = v___x_361_;
goto v___jp_345_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_textFails___boxed(lean_object* v_isEmpty_368_, lean_object* v_state_369_){
_start:
{
uint8_t v_isEmpty_boxed_370_; uint8_t v_state_boxed_371_; uint8_t v_res_372_; lean_object* v_r_373_; 
v_isEmpty_boxed_370_ = lean_unbox(v_isEmpty_368_);
v_state_boxed_371_ = lean_unbox(v_state_369_);
v_res_372_ = l_Lean_Fmt_textFails(v_isEmpty_boxed_370_, v_state_boxed_371_);
v_r_373_ = lean_box(v_res_372_);
return v_r_373_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_emptyTextFailureSet_spec__0(lean_object* v_x_374_, uint16_t v_x_375_){
_start:
{
lean_object* v_zero_376_; uint8_t v_isZero_377_; 
v_zero_376_ = lean_unsigned_to_nat(0u);
v_isZero_377_ = lean_nat_dec_eq(v_x_374_, v_zero_376_);
if (v_isZero_377_ == 1)
{
lean_dec(v_x_374_);
return v_x_375_;
}
else
{
uint8_t v___x_378_; lean_object* v_one_379_; lean_object* v_n_380_; uint8_t v_s_381_; uint8_t v___x_382_; 
v___x_378_ = 1;
v_one_379_ = lean_unsigned_to_nat(1u);
v_n_380_ = lean_nat_sub(v_x_374_, v_one_379_);
lean_dec(v_x_374_);
v_s_381_ = lean_uint8_of_nat(v_n_380_);
v___x_382_ = l_Lean_Fmt_textFails(v___x_378_, v_s_381_);
if (v___x_382_ == 0)
{
v_x_374_ = v_n_380_;
goto _start;
}
else
{
uint16_t v___x_384_; uint16_t v___x_385_; uint16_t v___x_386_; uint16_t v___x_387_; 
v___x_384_ = 1;
v___x_385_ = lean_uint16_of_nat(v_n_380_);
v___x_386_ = lean_uint16_shift_left(v___x_384_, v___x_385_);
v___x_387_ = lean_uint16_lor(v_x_375_, v___x_386_);
v_x_374_ = v_n_380_;
v_x_375_ = v___x_387_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_emptyTextFailureSet_spec__0___boxed(lean_object* v_x_389_, lean_object* v_x_390_){
_start:
{
uint16_t v_x_30__boxed_391_; uint16_t v_res_392_; lean_object* v_r_393_; 
v_x_30__boxed_391_ = lean_unbox(v_x_390_);
v_res_392_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_emptyTextFailureSet_spec__0(v_x_389_, v_x_30__boxed_391_);
v_r_393_ = lean_box(v_res_392_);
return v_r_393_;
}
}
static uint16_t _init_l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_emptyTextFailureSet___closed__0(void){
_start:
{
uint16_t v___x_394_; lean_object* v___x_395_; uint16_t v___x_396_; 
v___x_394_ = 0;
v___x_395_ = lean_unsigned_to_nat(16u);
v___x_396_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_emptyTextFailureSet_spec__0(v___x_395_, v___x_394_);
return v___x_396_;
}
}
static uint16_t _init_l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_emptyTextFailureSet(void){
_start:
{
uint16_t v___x_397_; 
v___x_397_ = lean_uint16_once(&l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_emptyTextFailureSet___closed__0, &l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_emptyTextFailureSet___closed__0_once, _init_l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_emptyTextFailureSet___closed__0);
return v___x_397_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_nonEmptyTextFailureSet_spec__0(lean_object* v_x_398_, uint16_t v_x_399_){
_start:
{
lean_object* v_zero_400_; uint8_t v_isZero_401_; 
v_zero_400_ = lean_unsigned_to_nat(0u);
v_isZero_401_ = lean_nat_dec_eq(v_x_398_, v_zero_400_);
if (v_isZero_401_ == 1)
{
lean_dec(v_x_398_);
return v_x_399_;
}
else
{
lean_object* v_one_402_; lean_object* v_n_403_; uint8_t v_s_404_; uint8_t v___x_405_; 
v_one_402_ = lean_unsigned_to_nat(1u);
v_n_403_ = lean_nat_sub(v_x_398_, v_one_402_);
lean_dec(v_x_398_);
v_s_404_ = lean_uint8_of_nat(v_n_403_);
v___x_405_ = l_Lean_Fmt_textFails(v_isZero_401_, v_s_404_);
if (v___x_405_ == 0)
{
v_x_398_ = v_n_403_;
goto _start;
}
else
{
uint16_t v___x_407_; uint16_t v___x_408_; uint16_t v___x_409_; uint16_t v___x_410_; 
v___x_407_ = 1;
v___x_408_ = lean_uint16_of_nat(v_n_403_);
v___x_409_ = lean_uint16_shift_left(v___x_407_, v___x_408_);
v___x_410_ = lean_uint16_lor(v_x_399_, v___x_409_);
v_x_398_ = v_n_403_;
v_x_399_ = v___x_410_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_nonEmptyTextFailureSet_spec__0___boxed(lean_object* v_x_412_, lean_object* v_x_413_){
_start:
{
uint16_t v_x_30__boxed_414_; uint16_t v_res_415_; lean_object* v_r_416_; 
v_x_30__boxed_414_ = lean_unbox(v_x_413_);
v_res_415_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_nonEmptyTextFailureSet_spec__0(v_x_412_, v_x_30__boxed_414_);
v_r_416_ = lean_box(v_res_415_);
return v_r_416_;
}
}
static uint16_t _init_l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_nonEmptyTextFailureSet___closed__0(void){
_start:
{
uint16_t v___x_417_; lean_object* v___x_418_; uint16_t v___x_419_; 
v___x_417_ = 0;
v___x_418_ = lean_unsigned_to_nat(16u);
v___x_419_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_nonEmptyTextFailureSet_spec__0(v___x_418_, v___x_417_);
return v___x_419_;
}
}
static uint16_t _init_l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_nonEmptyTextFailureSet(void){
_start:
{
uint16_t v___x_420_; 
v___x_420_ = lean_uint16_once(&l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_nonEmptyTextFailureSet___closed__0, &l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_nonEmptyTextFailureSet___closed__0_once, _init_l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_nonEmptyTextFailureSet___closed__0);
return v___x_420_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_textFailureSet(uint8_t v_isEmpty_421_){
_start:
{
if (v_isEmpty_421_ == 0)
{
uint16_t v___x_422_; 
v___x_422_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_nonEmptyTextFailureSet;
return v___x_422_;
}
else
{
uint16_t v___x_423_; 
v___x_423_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_emptyTextFailureSet;
return v___x_423_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_textFailureSet___boxed(lean_object* v_isEmpty_424_){
_start:
{
uint8_t v_isEmpty_boxed_425_; uint16_t v_res_426_; lean_object* v_r_427_; 
v_isEmpty_boxed_425_ = lean_unbox(v_isEmpty_424_);
v_res_426_ = l_Lean_Fmt_textFailureSet(v_isEmpty_boxed_425_);
v_r_427_ = lean_box(v_res_426_);
return v_r_427_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedTagId___aux__1(void){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = lean_unsigned_to_nat(0u);
return v___x_428_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedTagId(void){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = lean_unsigned_to_nat(0u);
return v___x_429_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqTagId___aux__1(lean_object* v_a_430_, lean_object* v_b_431_){
_start:
{
uint8_t v___x_432_; 
v___x_432_ = lean_nat_dec_eq(v_a_430_, v_b_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqTagId___aux__1___boxed(lean_object* v_a_433_, lean_object* v_b_434_){
_start:
{
uint8_t v_res_435_; lean_object* v_r_436_; 
v_res_435_ = l_Lean_Fmt_instBEqTagId___aux__1(v_a_433_, v_b_434_);
lean_dec(v_b_434_);
lean_dec(v_a_433_);
v_r_436_ = lean_box(v_res_435_);
return v_r_436_;
}
}
LEAN_EXPORT uint64_t l_Lean_Fmt_instHashableTagId___aux__1(lean_object* v_n_439_){
_start:
{
uint64_t v___x_440_; 
v___x_440_ = lean_uint64_of_nat(v_n_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableTagId___aux__1___boxed(lean_object* v_n_441_){
_start:
{
uint64_t v_res_442_; lean_object* v_r_443_; 
v_res_442_ = l_Lean_Fmt_instHashableTagId___aux__1(v_n_441_);
lean_dec(v_n_441_);
v_r_443_ = lean_box_uint64(v_res_442_);
return v_r_443_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instOrdTagId___aux__1(lean_object* v_x_446_, lean_object* v_y_447_){
_start:
{
uint8_t v___x_448_; 
v___x_448_ = lean_nat_dec_lt(v_x_446_, v_y_447_);
if (v___x_448_ == 0)
{
uint8_t v___x_449_; 
v___x_449_ = lean_nat_dec_eq(v_x_446_, v_y_447_);
if (v___x_449_ == 0)
{
uint8_t v___x_450_; 
v___x_450_ = 2;
return v___x_450_;
}
else
{
uint8_t v___x_451_; 
v___x_451_ = 1;
return v___x_451_;
}
}
else
{
uint8_t v___x_452_; 
v___x_452_ = 0;
return v___x_452_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instOrdTagId___aux__1___boxed(lean_object* v_x_453_, lean_object* v_y_454_){
_start:
{
uint8_t v_res_455_; lean_object* v_r_456_; 
v_res_455_ = l_Lean_Fmt_instOrdTagId___aux__1(v_x_453_, v_y_454_);
lean_dec(v_y_454_);
lean_dec(v_x_453_);
v_r_456_ = lean_box(v_res_455_);
return v_r_456_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instOrdTagId___lam__0(lean_object* v___y_457_, lean_object* v___y_458_){
_start:
{
uint8_t v___x_459_; 
v___x_459_ = lean_nat_dec_lt(v___y_457_, v___y_458_);
if (v___x_459_ == 0)
{
uint8_t v___x_460_; 
v___x_460_ = lean_nat_dec_eq(v___y_457_, v___y_458_);
if (v___x_460_ == 0)
{
uint8_t v___x_461_; 
v___x_461_ = 2;
return v___x_461_;
}
else
{
uint8_t v___x_462_; 
v___x_462_ = 1;
return v___x_462_;
}
}
else
{
uint8_t v___x_463_; 
v___x_463_ = 0;
return v___x_463_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instOrdTagId___lam__0___boxed(lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
uint8_t v_res_466_; lean_object* v_r_467_; 
v_res_466_ = l_Lean_Fmt_instOrdTagId___lam__0(v___y_464_, v___y_465_);
lean_dec(v___y_465_);
lean_dec(v___y_464_);
v_r_467_ = lean_box(v_res_466_);
return v_r_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprTagId___aux__1___redArg(lean_object* v_n_470_){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = l_Nat_reprFast(v_n_470_);
v___x_472_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprTagId___aux__1(lean_object* v_n_473_, lean_object* v_x_474_){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = l_Nat_reprFast(v_n_473_);
v___x_476_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprTagId___aux__1___boxed(lean_object* v_n_477_, lean_object* v_x_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Lean_Fmt_instReprTagId___aux__1(v_n_477_, v_x_478_);
lean_dec(v_x_478_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprTagId___lam__0(lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = l_Nat_reprFast(v___y_480_);
v___x_483_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprTagId___lam__0___boxed(lean_object* v___y_484_, lean_object* v___y_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Lean_Fmt_instReprTagId___lam__0(v___y_484_, v___y_485_);
lean_dec(v___y_485_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instToStringTagId___aux__1(lean_object* v_n_489_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_Nat_reprFast(v_n_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHAddTagIdNat___aux__1(lean_object* v_a_493_, lean_object* v_b_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = lean_nat_add(v_a_493_, v_b_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHAddTagIdNat___aux__1___boxed(lean_object* v_a_496_, lean_object* v_b_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Lean_Fmt_instHAddTagIdNat___aux__1(v_a_496_, v_b_497_);
lean_dec(v_b_497_);
lean_dec(v_a_496_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_ctorIdx___impl(uint8_t v_x_501_){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = lean_box(v_x_501_);
v___x_503_ = lean_obj_tag_nat(v___x_502_);
lean_dec(v___x_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_ctorIdx___impl___boxed(lean_object* v_x_504_){
_start:
{
uint8_t v_x_4__boxed_505_; lean_object* v_res_506_; 
v_x_4__boxed_505_ = lean_unbox(v_x_504_);
v_res_506_ = l_Lean_Fmt_Doc_AlwaysEmptiness_ctorIdx___impl(v_x_4__boxed_505_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_ctorElim___redArg(lean_object* v_k_507_){
_start:
{
lean_inc(v_k_507_);
return v_k_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_ctorElim___redArg___boxed(lean_object* v_k_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Lean_Fmt_Doc_AlwaysEmptiness_ctorElim___redArg(v_k_508_);
lean_dec(v_k_508_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_ctorElim(lean_object* v_motive_510_, lean_object* v_ctorIdx_511_, uint8_t v_t_512_, lean_object* v_h_513_, lean_object* v_k_514_){
_start:
{
lean_inc(v_k_514_);
return v_k_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_ctorElim___boxed(lean_object* v_motive_515_, lean_object* v_ctorIdx_516_, lean_object* v_t_517_, lean_object* v_h_518_, lean_object* v_k_519_){
_start:
{
uint8_t v_t_boxed_520_; lean_object* v_res_521_; 
v_t_boxed_520_ = lean_unbox(v_t_517_);
v_res_521_ = l_Lean_Fmt_Doc_AlwaysEmptiness_ctorElim(v_motive_515_, v_ctorIdx_516_, v_t_boxed_520_, v_h_518_, v_k_519_);
lean_dec(v_k_519_);
lean_dec(v_ctorIdx_516_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmpty_elim___redArg(lean_object* v_alwaysEmpty_522_){
_start:
{
lean_inc(v_alwaysEmpty_522_);
return v_alwaysEmpty_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmpty_elim___redArg___boxed(lean_object* v_alwaysEmpty_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmpty_elim___redArg(v_alwaysEmpty_523_);
lean_dec(v_alwaysEmpty_523_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmpty_elim(lean_object* v_motive_525_, uint8_t v_t_526_, lean_object* v_h_527_, lean_object* v_alwaysEmpty_528_){
_start:
{
lean_inc(v_alwaysEmpty_528_);
return v_alwaysEmpty_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmpty_elim___boxed(lean_object* v_motive_529_, lean_object* v_t_530_, lean_object* v_h_531_, lean_object* v_alwaysEmpty_532_){
_start:
{
uint8_t v_t_boxed_533_; lean_object* v_res_534_; 
v_t_boxed_533_ = lean_unbox(v_t_530_);
v_res_534_ = l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmpty_elim(v_motive_529_, v_t_boxed_533_, v_h_531_, v_alwaysEmpty_532_);
lean_dec(v_alwaysEmpty_532_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmptyIfFlattened_elim___redArg(lean_object* v_alwaysEmptyIfFlattened_535_){
_start:
{
lean_inc(v_alwaysEmptyIfFlattened_535_);
return v_alwaysEmptyIfFlattened_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmptyIfFlattened_elim___redArg___boxed(lean_object* v_alwaysEmptyIfFlattened_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmptyIfFlattened_elim___redArg(v_alwaysEmptyIfFlattened_536_);
lean_dec(v_alwaysEmptyIfFlattened_536_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmptyIfFlattened_elim(lean_object* v_motive_538_, uint8_t v_t_539_, lean_object* v_h_540_, lean_object* v_alwaysEmptyIfFlattened_541_){
_start:
{
lean_inc(v_alwaysEmptyIfFlattened_541_);
return v_alwaysEmptyIfFlattened_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmptyIfFlattened_elim___boxed(lean_object* v_motive_542_, lean_object* v_t_543_, lean_object* v_h_544_, lean_object* v_alwaysEmptyIfFlattened_545_){
_start:
{
uint8_t v_t_boxed_546_; lean_object* v_res_547_; 
v_t_boxed_546_ = lean_unbox(v_t_543_);
v_res_547_ = l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmptyIfFlattened_elim(v_motive_542_, v_t_boxed_546_, v_h_544_, v_alwaysEmptyIfFlattened_545_);
lean_dec(v_alwaysEmptyIfFlattened_545_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_sometimesNonEmpty_elim___redArg(lean_object* v_sometimesNonEmpty_548_){
_start:
{
lean_inc(v_sometimesNonEmpty_548_);
return v_sometimesNonEmpty_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_sometimesNonEmpty_elim___redArg___boxed(lean_object* v_sometimesNonEmpty_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Lean_Fmt_Doc_AlwaysEmptiness_sometimesNonEmpty_elim___redArg(v_sometimesNonEmpty_549_);
lean_dec(v_sometimesNonEmpty_549_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_sometimesNonEmpty_elim(lean_object* v_motive_551_, uint8_t v_t_552_, lean_object* v_h_553_, lean_object* v_sometimesNonEmpty_554_){
_start:
{
lean_inc(v_sometimesNonEmpty_554_);
return v_sometimesNonEmpty_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_sometimesNonEmpty_elim___boxed(lean_object* v_motive_555_, lean_object* v_t_556_, lean_object* v_h_557_, lean_object* v_sometimesNonEmpty_558_){
_start:
{
uint8_t v_t_boxed_559_; lean_object* v_res_560_; 
v_t_boxed_559_ = lean_unbox(v_t_556_);
v_res_560_ = l_Lean_Fmt_Doc_AlwaysEmptiness_sometimesNonEmpty_elim(v_motive_555_, v_t_boxed_559_, v_h_557_, v_sometimesNonEmpty_558_);
lean_dec(v_sometimesNonEmpty_558_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_max___lam__0(uint8_t v_x_561_){
_start:
{
switch(v_x_561_)
{
case 0:
{
lean_object* v___x_562_; 
v___x_562_ = lean_unsigned_to_nat(0u);
return v___x_562_;
}
case 1:
{
lean_object* v___x_563_; 
v___x_563_ = lean_unsigned_to_nat(1u);
return v___x_563_;
}
default: 
{
lean_object* v___x_564_; 
v___x_564_ = lean_unsigned_to_nat(2u);
return v___x_564_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_max___lam__0___boxed(lean_object* v_x_565_){
_start:
{
uint8_t v_x_68__boxed_566_; lean_object* v_res_567_; 
v_x_68__boxed_566_ = lean_unbox(v_x_565_);
v_res_567_ = l_Lean_Fmt_Doc_AlwaysEmptiness_max___lam__0(v_x_68__boxed_566_);
return v_res_567_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_AlwaysEmptiness_max(uint8_t v_e1_568_, uint8_t v_e2_569_){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; uint8_t v___x_572_; 
v___x_570_ = l_Lean_Fmt_Doc_AlwaysEmptiness_max___lam__0(v_e2_569_);
v___x_571_ = l_Lean_Fmt_Doc_AlwaysEmptiness_max___lam__0(v_e1_568_);
v___x_572_ = lean_nat_dec_le(v___x_570_, v___x_571_);
lean_dec(v___x_571_);
lean_dec(v___x_570_);
if (v___x_572_ == 0)
{
return v_e2_569_;
}
else
{
return v_e1_568_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_max___boxed(lean_object* v_e1_573_, lean_object* v_e2_574_){
_start:
{
uint8_t v_e1_boxed_575_; uint8_t v_e2_boxed_576_; uint8_t v_res_577_; lean_object* v_r_578_; 
v_e1_boxed_575_ = lean_unbox(v_e1_573_);
v_e2_boxed_576_ = lean_unbox(v_e2_574_);
v_res_577_ = l_Lean_Fmt_Doc_AlwaysEmptiness_max(v_e1_boxed_575_, v_e2_boxed_576_);
v_r_578_ = lean_box(v_res_577_);
return v_r_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorIdx___impl(uint8_t v_x_579_){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_580_ = lean_box(v_x_579_);
v___x_581_ = lean_obj_tag_nat(v___x_580_);
lean_dec(v___x_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorIdx___impl___boxed(lean_object* v_x_582_){
_start:
{
uint8_t v_x_4__boxed_583_; lean_object* v_res_584_; 
v_x_4__boxed_583_ = lean_unbox(v_x_582_);
v_res_584_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorIdx___impl(v_x_4__boxed_583_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorElim___redArg(lean_object* v_k_585_){
_start:
{
lean_inc(v_k_585_);
return v_k_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorElim___redArg___boxed(lean_object* v_k_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorElim___redArg(v_k_586_);
lean_dec(v_k_586_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorElim(lean_object* v_motive_588_, lean_object* v_ctorIdx_589_, uint8_t v_t_590_, lean_object* v_h_591_, lean_object* v_k_592_){
_start:
{
lean_inc(v_k_592_);
return v_k_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorElim___boxed(lean_object* v_motive_593_, lean_object* v_ctorIdx_594_, lean_object* v_t_595_, lean_object* v_h_596_, lean_object* v_k_597_){
_start:
{
uint8_t v_t_boxed_598_; lean_object* v_res_599_; 
v_t_boxed_598_ = lean_unbox(v_t_595_);
v_res_599_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorElim(v_motive_593_, v_ctorIdx_594_, v_t_boxed_598_, v_h_596_, v_k_597_);
lean_dec(v_k_597_);
lean_dec(v_ctorIdx_594_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_alwaysNonEmpty_elim___redArg(lean_object* v_alwaysNonEmpty_600_){
_start:
{
lean_inc(v_alwaysNonEmpty_600_);
return v_alwaysNonEmpty_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_alwaysNonEmpty_elim___redArg___boxed(lean_object* v_alwaysNonEmpty_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_alwaysNonEmpty_elim___redArg(v_alwaysNonEmpty_601_);
lean_dec(v_alwaysNonEmpty_601_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_alwaysNonEmpty_elim(lean_object* v_motive_603_, uint8_t v_t_604_, lean_object* v_h_605_, lean_object* v_alwaysNonEmpty_606_){
_start:
{
lean_inc(v_alwaysNonEmpty_606_);
return v_alwaysNonEmpty_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_alwaysNonEmpty_elim___boxed(lean_object* v_motive_607_, lean_object* v_t_608_, lean_object* v_h_609_, lean_object* v_alwaysNonEmpty_610_){
_start:
{
uint8_t v_t_boxed_611_; lean_object* v_res_612_; 
v_t_boxed_611_ = lean_unbox(v_t_608_);
v_res_612_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_alwaysNonEmpty_elim(v_motive_607_, v_t_boxed_611_, v_h_609_, v_alwaysNonEmpty_610_);
lean_dec(v_alwaysNonEmpty_610_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_sometimesEmpty_elim___redArg(lean_object* v_sometimesEmpty_613_){
_start:
{
lean_inc(v_sometimesEmpty_613_);
return v_sometimesEmpty_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_sometimesEmpty_elim___redArg___boxed(lean_object* v_sometimesEmpty_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_sometimesEmpty_elim___redArg(v_sometimesEmpty_614_);
lean_dec(v_sometimesEmpty_614_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_sometimesEmpty_elim(lean_object* v_motive_616_, uint8_t v_t_617_, lean_object* v_h_618_, lean_object* v_sometimesEmpty_619_){
_start:
{
lean_inc(v_sometimesEmpty_619_);
return v_sometimesEmpty_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_sometimesEmpty_elim___boxed(lean_object* v_motive_620_, lean_object* v_t_621_, lean_object* v_h_622_, lean_object* v_sometimesEmpty_623_){
_start:
{
uint8_t v_t_boxed_624_; lean_object* v_res_625_; 
v_t_boxed_624_ = lean_unbox(v_t_621_);
v_res_625_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_sometimesEmpty_elim(v_motive_620_, v_t_boxed_624_, v_h_622_, v_sometimesEmpty_623_);
lean_dec(v_sometimesEmpty_623_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_max___lam__0(uint8_t v_x_626_){
_start:
{
if (v_x_626_ == 0)
{
lean_object* v___x_627_; 
v___x_627_ = lean_unsigned_to_nat(0u);
return v___x_627_;
}
else
{
lean_object* v___x_628_; 
v___x_628_ = lean_unsigned_to_nat(1u);
return v___x_628_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_max___lam__0___boxed(lean_object* v_x_629_){
_start:
{
uint8_t v_x_50__boxed_630_; lean_object* v_res_631_; 
v_x_50__boxed_630_ = lean_unbox(v_x_629_);
v_res_631_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_max___lam__0(v_x_50__boxed_630_);
return v_res_631_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_AlwaysNonEmptiness_max(uint8_t v_e1_632_, uint8_t v_e2_633_){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; uint8_t v___x_636_; 
v___x_634_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_max___lam__0(v_e2_633_);
v___x_635_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_max___lam__0(v_e1_632_);
v___x_636_ = lean_nat_dec_le(v___x_634_, v___x_635_);
lean_dec(v___x_635_);
lean_dec(v___x_634_);
if (v___x_636_ == 0)
{
return v_e2_633_;
}
else
{
return v_e1_632_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_max___boxed(lean_object* v_e1_637_, lean_object* v_e2_638_){
_start:
{
uint8_t v_e1_boxed_639_; uint8_t v_e2_boxed_640_; uint8_t v_res_641_; lean_object* v_r_642_; 
v_e1_boxed_639_ = lean_unbox(v_e1_637_);
v_e2_boxed_640_ = lean_unbox(v_e2_638_);
v_res_641_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_max(v_e1_boxed_639_, v_e2_boxed_640_);
v_r_642_ = lean_box(v_res_641_);
return v_r_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_ctorIdx___impl(uint8_t v_x_643_){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = lean_box(v_x_643_);
v___x_645_ = lean_obj_tag_nat(v___x_644_);
lean_dec(v___x_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_ctorIdx___impl___boxed(lean_object* v_x_646_){
_start:
{
uint8_t v_x_4__boxed_647_; lean_object* v_res_648_; 
v_x_4__boxed_647_ = lean_unbox(v_x_646_);
v_res_648_ = l_Lean_Fmt_Doc_Atomicness_ctorIdx___impl(v_x_4__boxed_647_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_ctorElim___redArg(lean_object* v_k_649_){
_start:
{
lean_inc(v_k_649_);
return v_k_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_ctorElim___redArg___boxed(lean_object* v_k_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Lean_Fmt_Doc_Atomicness_ctorElim___redArg(v_k_650_);
lean_dec(v_k_650_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_ctorElim(lean_object* v_motive_652_, lean_object* v_ctorIdx_653_, uint8_t v_t_654_, lean_object* v_h_655_, lean_object* v_k_656_){
_start:
{
lean_inc(v_k_656_);
return v_k_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_ctorElim___boxed(lean_object* v_motive_657_, lean_object* v_ctorIdx_658_, lean_object* v_t_659_, lean_object* v_h_660_, lean_object* v_k_661_){
_start:
{
uint8_t v_t_boxed_662_; lean_object* v_res_663_; 
v_t_boxed_662_ = lean_unbox(v_t_659_);
v_res_663_ = l_Lean_Fmt_Doc_Atomicness_ctorElim(v_motive_657_, v_ctorIdx_658_, v_t_boxed_662_, v_h_660_, v_k_661_);
lean_dec(v_k_661_);
lean_dec(v_ctorIdx_658_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomic_elim___redArg(lean_object* v_atomic_664_){
_start:
{
lean_inc(v_atomic_664_);
return v_atomic_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomic_elim___redArg___boxed(lean_object* v_atomic_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Lean_Fmt_Doc_Atomicness_atomic_elim___redArg(v_atomic_665_);
lean_dec(v_atomic_665_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomic_elim(lean_object* v_motive_667_, uint8_t v_t_668_, lean_object* v_h_669_, lean_object* v_atomic_670_){
_start:
{
lean_inc(v_atomic_670_);
return v_atomic_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomic_elim___boxed(lean_object* v_motive_671_, lean_object* v_t_672_, lean_object* v_h_673_, lean_object* v_atomic_674_){
_start:
{
uint8_t v_t_boxed_675_; lean_object* v_res_676_; 
v_t_boxed_675_ = lean_unbox(v_t_672_);
v_res_676_ = l_Lean_Fmt_Doc_Atomicness_atomic_elim(v_motive_671_, v_t_boxed_675_, v_h_673_, v_atomic_674_);
lean_dec(v_atomic_674_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomicIfFlattened_elim___redArg(lean_object* v_atomicIfFlattened_677_){
_start:
{
lean_inc(v_atomicIfFlattened_677_);
return v_atomicIfFlattened_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomicIfFlattened_elim___redArg___boxed(lean_object* v_atomicIfFlattened_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Lean_Fmt_Doc_Atomicness_atomicIfFlattened_elim___redArg(v_atomicIfFlattened_678_);
lean_dec(v_atomicIfFlattened_678_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomicIfFlattened_elim(lean_object* v_motive_680_, uint8_t v_t_681_, lean_object* v_h_682_, lean_object* v_atomicIfFlattened_683_){
_start:
{
lean_inc(v_atomicIfFlattened_683_);
return v_atomicIfFlattened_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomicIfFlattened_elim___boxed(lean_object* v_motive_684_, lean_object* v_t_685_, lean_object* v_h_686_, lean_object* v_atomicIfFlattened_687_){
_start:
{
uint8_t v_t_boxed_688_; lean_object* v_res_689_; 
v_t_boxed_688_ = lean_unbox(v_t_685_);
v_res_689_ = l_Lean_Fmt_Doc_Atomicness_atomicIfFlattened_elim(v_motive_684_, v_t_boxed_688_, v_h_686_, v_atomicIfFlattened_687_);
lean_dec(v_atomicIfFlattened_687_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomic_elim___redArg(lean_object* v_compoundAtomic_690_){
_start:
{
lean_inc(v_compoundAtomic_690_);
return v_compoundAtomic_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomic_elim___redArg___boxed(lean_object* v_compoundAtomic_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Lean_Fmt_Doc_Atomicness_compoundAtomic_elim___redArg(v_compoundAtomic_691_);
lean_dec(v_compoundAtomic_691_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomic_elim(lean_object* v_motive_693_, uint8_t v_t_694_, lean_object* v_h_695_, lean_object* v_compoundAtomic_696_){
_start:
{
lean_inc(v_compoundAtomic_696_);
return v_compoundAtomic_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomic_elim___boxed(lean_object* v_motive_697_, lean_object* v_t_698_, lean_object* v_h_699_, lean_object* v_compoundAtomic_700_){
_start:
{
uint8_t v_t_boxed_701_; lean_object* v_res_702_; 
v_t_boxed_701_ = lean_unbox(v_t_698_);
v_res_702_ = l_Lean_Fmt_Doc_Atomicness_compoundAtomic_elim(v_motive_697_, v_t_boxed_701_, v_h_699_, v_compoundAtomic_700_);
lean_dec(v_compoundAtomic_700_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomicIfFlattened_elim___redArg(lean_object* v_compoundAtomicIfFlattened_703_){
_start:
{
lean_inc(v_compoundAtomicIfFlattened_703_);
return v_compoundAtomicIfFlattened_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomicIfFlattened_elim___redArg___boxed(lean_object* v_compoundAtomicIfFlattened_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_Lean_Fmt_Doc_Atomicness_compoundAtomicIfFlattened_elim___redArg(v_compoundAtomicIfFlattened_704_);
lean_dec(v_compoundAtomicIfFlattened_704_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomicIfFlattened_elim(lean_object* v_motive_706_, uint8_t v_t_707_, lean_object* v_h_708_, lean_object* v_compoundAtomicIfFlattened_709_){
_start:
{
lean_inc(v_compoundAtomicIfFlattened_709_);
return v_compoundAtomicIfFlattened_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomicIfFlattened_elim___boxed(lean_object* v_motive_710_, lean_object* v_t_711_, lean_object* v_h_712_, lean_object* v_compoundAtomicIfFlattened_713_){
_start:
{
uint8_t v_t_boxed_714_; lean_object* v_res_715_; 
v_t_boxed_714_ = lean_unbox(v_t_711_);
v_res_715_ = l_Lean_Fmt_Doc_Atomicness_compoundAtomicIfFlattened_elim(v_motive_710_, v_t_boxed_714_, v_h_712_, v_compoundAtomicIfFlattened_713_);
lean_dec(v_compoundAtomicIfFlattened_713_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_nonAtomic_elim___redArg(lean_object* v_nonAtomic_716_){
_start:
{
lean_inc(v_nonAtomic_716_);
return v_nonAtomic_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_nonAtomic_elim___redArg___boxed(lean_object* v_nonAtomic_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_Lean_Fmt_Doc_Atomicness_nonAtomic_elim___redArg(v_nonAtomic_717_);
lean_dec(v_nonAtomic_717_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_nonAtomic_elim(lean_object* v_motive_719_, uint8_t v_t_720_, lean_object* v_h_721_, lean_object* v_nonAtomic_722_){
_start:
{
lean_inc(v_nonAtomic_722_);
return v_nonAtomic_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_nonAtomic_elim___boxed(lean_object* v_motive_723_, lean_object* v_t_724_, lean_object* v_h_725_, lean_object* v_nonAtomic_726_){
_start:
{
uint8_t v_t_boxed_727_; lean_object* v_res_728_; 
v_t_boxed_727_ = lean_unbox(v_t_724_);
v_res_728_ = l_Lean_Fmt_Doc_Atomicness_nonAtomic_elim(v_motive_723_, v_t_boxed_727_, v_h_725_, v_nonAtomic_726_);
lean_dec(v_nonAtomic_726_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_max___lam__0(uint8_t v_x_729_){
_start:
{
switch(v_x_729_)
{
case 0:
{
lean_object* v___x_730_; 
v___x_730_ = lean_unsigned_to_nat(0u);
return v___x_730_;
}
case 1:
{
lean_object* v___x_731_; 
v___x_731_ = lean_unsigned_to_nat(1u);
return v___x_731_;
}
case 2:
{
lean_object* v___x_732_; 
v___x_732_ = lean_unsigned_to_nat(2u);
return v___x_732_;
}
case 3:
{
lean_object* v___x_733_; 
v___x_733_ = lean_unsigned_to_nat(3u);
return v___x_733_;
}
default: 
{
lean_object* v___x_734_; 
v___x_734_ = lean_unsigned_to_nat(4u);
return v___x_734_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_max___lam__0___boxed(lean_object* v_x_735_){
_start:
{
uint8_t v_x_104__boxed_736_; lean_object* v_res_737_; 
v_x_104__boxed_736_ = lean_unbox(v_x_735_);
v_res_737_ = l_Lean_Fmt_Doc_Atomicness_max___lam__0(v_x_104__boxed_736_);
return v_res_737_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_Atomicness_max(uint8_t v_e1_738_, uint8_t v_e2_739_){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; uint8_t v___x_742_; 
v___x_740_ = l_Lean_Fmt_Doc_Atomicness_max___lam__0(v_e2_739_);
v___x_741_ = l_Lean_Fmt_Doc_Atomicness_max___lam__0(v_e1_738_);
v___x_742_ = lean_nat_dec_le(v___x_740_, v___x_741_);
lean_dec(v___x_741_);
lean_dec(v___x_740_);
if (v___x_742_ == 0)
{
return v_e2_739_;
}
else
{
return v_e1_738_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_max___boxed(lean_object* v_e1_743_, lean_object* v_e2_744_){
_start:
{
uint8_t v_e1_boxed_745_; uint8_t v_e2_boxed_746_; uint8_t v_res_747_; lean_object* v_r_748_; 
v_e1_boxed_745_ = lean_unbox(v_e1_743_);
v_e2_boxed_746_ = lean_unbox(v_e2_744_);
v_res_747_ = l_Lean_Fmt_Doc_Atomicness_max(v_e1_boxed_745_, v_e2_boxed_746_);
v_r_748_ = lean_box(v_res_747_);
return v_r_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprAssertion___lam__0(lean_object* v_x_752_, lean_object* v_x_753_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = ((lean_object*)(l_Lean_Fmt_instReprAssertion___lam__0___closed__1));
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprAssertion___lam__0___boxed(lean_object* v_x_755_, lean_object* v_x_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Lean_Fmt_instReprAssertion___lam__0(v_x_755_, v_x_756_);
lean_dec(v_x_756_);
lean_dec_ref(v_x_755_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_ctorIdx___impl___redArg(lean_object* v_x_760_){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = lean_obj_tag_nat(v_x_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_ctorIdx___impl___redArg___boxed(lean_object* v_x_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Lean_Fmt_Doc_ctorIdx___impl___redArg(v_x_762_);
lean_dec(v_x_762_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_ctorIdx___impl(lean_object* v_00_u03c4_764_, lean_object* v_x_765_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = lean_obj_tag_nat(v_x_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_ctorIdx___impl___boxed(lean_object* v_00_u03c4_767_, lean_object* v_x_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Lean_Fmt_Doc_ctorIdx___impl(v_00_u03c4_767_, v_x_768_);
lean_dec(v_x_768_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_ctorElim___redArg(lean_object* v_t_770_, lean_object* v_k_771_){
_start:
{
switch(lean_obj_tag(v_t_770_))
{
case 0:
{
return v_k_771_;
}
case 1:
{
lean_object* v_f_772_; lean_object* v___x_773_; 
v_f_772_ = lean_ctor_get(v_t_770_, 0);
lean_inc_ref(v_f_772_);
lean_dec_ref_known(v_t_770_, 1);
v___x_773_ = lean_apply_1(v_k_771_, v_f_772_);
return v___x_773_;
}
case 2:
{
lean_object* v_s_774_; lean_object* v___x_775_; 
v_s_774_ = lean_ctor_get(v_t_770_, 0);
lean_inc_ref(v_s_774_);
lean_dec_ref_known(v_t_770_, 1);
v___x_775_ = lean_apply_1(v_k_771_, v_s_774_);
return v___x_775_;
}
case 3:
{
lean_object* v_id_776_; lean_object* v_d_777_; lean_object* v___x_778_; 
v_id_776_ = lean_ctor_get(v_t_770_, 0);
lean_inc(v_id_776_);
v_d_777_ = lean_ctor_get(v_t_770_, 1);
lean_inc(v_d_777_);
lean_dec_ref_known(v_t_770_, 2);
v___x_778_ = lean_apply_2(v_k_771_, v_id_776_, v_d_777_);
return v___x_778_;
}
case 6:
{
lean_object* v_n_779_; uint8_t v_isCumulative_780_; lean_object* v_d_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v_n_779_ = lean_ctor_get(v_t_770_, 0);
lean_inc(v_n_779_);
v_isCumulative_780_ = lean_ctor_get_uint8(v_t_770_, sizeof(void*)*2);
v_d_781_ = lean_ctor_get(v_t_770_, 1);
lean_inc(v_d_781_);
lean_dec_ref_known(v_t_770_, 2);
v___x_782_ = lean_box(v_isCumulative_780_);
v___x_783_ = lean_apply_3(v_k_771_, v_n_779_, v___x_782_, v_d_781_);
return v___x_783_;
}
case 8:
{
uint8_t v_onlyNonCumulative_784_; lean_object* v_d_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v_onlyNonCumulative_784_ = lean_ctor_get_uint8(v_t_770_, sizeof(void*)*1);
v_d_785_ = lean_ctor_get(v_t_770_, 0);
lean_inc(v_d_785_);
lean_dec_ref_known(v_t_770_, 1);
v___x_786_ = lean_box(v_onlyNonCumulative_784_);
v___x_787_ = lean_apply_2(v_k_771_, v___x_786_, v_d_785_);
return v___x_787_;
}
case 12:
{
lean_object* v_p_788_; lean_object* v_d_789_; lean_object* v___x_790_; 
v_p_788_ = lean_ctor_get(v_t_770_, 0);
lean_inc_ref(v_p_788_);
v_d_789_ = lean_ctor_get(v_t_770_, 1);
lean_inc(v_d_789_);
lean_dec_ref_known(v_t_770_, 2);
v___x_790_ = lean_apply_2(v_k_771_, v_p_788_, v_d_789_);
return v___x_790_;
}
case 13:
{
lean_object* v_cost_791_; lean_object* v_d_792_; lean_object* v___x_793_; 
v_cost_791_ = lean_ctor_get(v_t_770_, 0);
lean_inc(v_cost_791_);
v_d_792_ = lean_ctor_get(v_t_770_, 1);
lean_inc(v_d_792_);
lean_dec_ref_known(v_t_770_, 2);
v___x_793_ = lean_apply_2(v_k_771_, v_cost_791_, v_d_792_);
return v___x_793_;
}
case 14:
{
lean_object* v_a_794_; lean_object* v_b_795_; lean_object* v___x_796_; 
v_a_794_ = lean_ctor_get(v_t_770_, 0);
lean_inc(v_a_794_);
v_b_795_ = lean_ctor_get(v_t_770_, 1);
lean_inc(v_b_795_);
lean_dec_ref_known(v_t_770_, 2);
v___x_796_ = lean_apply_2(v_k_771_, v_a_794_, v_b_795_);
return v___x_796_;
}
case 15:
{
lean_object* v_a_797_; lean_object* v_b_798_; lean_object* v___x_799_; 
v_a_797_ = lean_ctor_get(v_t_770_, 0);
lean_inc(v_a_797_);
v_b_798_ = lean_ctor_get(v_t_770_, 1);
lean_inc(v_b_798_);
lean_dec_ref_known(v_t_770_, 2);
v___x_799_ = lean_apply_2(v_k_771_, v_a_797_, v_b_798_);
return v___x_799_;
}
default: 
{
lean_object* v_d_800_; lean_object* v___x_801_; 
v_d_800_ = lean_ctor_get(v_t_770_, 0);
lean_inc(v_d_800_);
lean_dec(v_t_770_);
v___x_801_ = lean_apply_1(v_k_771_, v_d_800_);
return v___x_801_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_ctorElim(lean_object* v_00_u03c4_802_, lean_object* v_motive_803_, lean_object* v_ctorIdx_804_, lean_object* v_t_805_, lean_object* v_h_806_, lean_object* v_k_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_805_, v_k_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_ctorElim___boxed(lean_object* v_00_u03c4_809_, lean_object* v_motive_810_, lean_object* v_ctorIdx_811_, lean_object* v_t_812_, lean_object* v_h_813_, lean_object* v_k_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Lean_Fmt_Doc_ctorElim(v_00_u03c4_809_, v_motive_810_, v_ctorIdx_811_, v_t_812_, v_h_813_, v_k_814_);
lean_dec(v_ctorIdx_811_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_failure_elim___redArg(lean_object* v_t_816_, lean_object* v_failure_817_){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_816_, v_failure_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_failure_elim(lean_object* v_00_u03c4_819_, lean_object* v_motive_820_, lean_object* v_t_821_, lean_object* v_h_822_, lean_object* v_failure_823_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_821_, v_failure_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_newline_elim___redArg(lean_object* v_t_825_, lean_object* v_newline_826_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_825_, v_newline_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_newline_elim(lean_object* v_00_u03c4_828_, lean_object* v_motive_829_, lean_object* v_t_830_, lean_object* v_h_831_, lean_object* v_newline_832_){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_830_, v_newline_832_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_text_elim___redArg(lean_object* v_t_834_, lean_object* v_text_835_){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_834_, v_text_835_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_text_elim(lean_object* v_00_u03c4_837_, lean_object* v_motive_838_, lean_object* v_t_839_, lean_object* v_h_840_, lean_object* v_text_841_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_839_, v_text_841_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_tagged_elim___redArg(lean_object* v_t_843_, lean_object* v_tagged_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_843_, v_tagged_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_tagged_elim(lean_object* v_00_u03c4_846_, lean_object* v_motive_847_, lean_object* v_t_848_, lean_object* v_h_849_, lean_object* v_tagged_850_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_848_, v_tagged_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_flattened_elim___redArg(lean_object* v_t_852_, lean_object* v_flattened_853_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_852_, v_flattened_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_flattened_elim(lean_object* v_00_u03c4_855_, lean_object* v_motive_856_, lean_object* v_t_857_, lean_object* v_h_858_, lean_object* v_flattened_859_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_857_, v_flattened_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unflattenable_elim___redArg(lean_object* v_t_861_, lean_object* v_unflattenable_862_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_861_, v_unflattenable_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unflattenable_elim(lean_object* v_00_u03c4_864_, lean_object* v_motive_865_, lean_object* v_t_866_, lean_object* v_h_867_, lean_object* v_unflattenable_868_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_866_, v_unflattenable_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_indented_elim___redArg(lean_object* v_t_870_, lean_object* v_indented_871_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_870_, v_indented_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_indented_elim(lean_object* v_00_u03c4_873_, lean_object* v_motive_874_, lean_object* v_t_875_, lean_object* v_h_876_, lean_object* v_indented_877_){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_875_, v_indented_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_aligned_elim___redArg(lean_object* v_t_879_, lean_object* v_aligned_880_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_879_, v_aligned_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_aligned_elim(lean_object* v_00_u03c4_882_, lean_object* v_motive_883_, lean_object* v_t_884_, lean_object* v_h_885_, lean_object* v_aligned_886_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_884_, v_aligned_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unindented_elim___redArg(lean_object* v_t_888_, lean_object* v_unindented_889_){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_888_, v_unindented_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unindented_elim(lean_object* v_00_u03c4_891_, lean_object* v_motive_892_, lean_object* v_t_893_, lean_object* v_h_894_, lean_object* v_unindented_895_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_893_, v_unindented_895_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_final_elim___redArg(lean_object* v_t_897_, lean_object* v_final_898_){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_897_, v_final_898_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_final_elim(lean_object* v_00_u03c4_900_, lean_object* v_motive_901_, lean_object* v_t_902_, lean_object* v_h_903_, lean_object* v_final_904_){
_start:
{
lean_object* v___x_905_; 
v___x_905_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_902_, v_final_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_initial_elim___redArg(lean_object* v_t_906_, lean_object* v_initial_907_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_906_, v_initial_907_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_initial_elim(lean_object* v_00_u03c4_909_, lean_object* v_motive_910_, lean_object* v_t_911_, lean_object* v_h_912_, lean_object* v_initial_913_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_911_, v_initial_913_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_free_elim___redArg(lean_object* v_t_915_, lean_object* v_free_916_){
_start:
{
lean_object* v___x_917_; 
v___x_917_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_915_, v_free_916_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_free_elim(lean_object* v_00_u03c4_918_, lean_object* v_motive_919_, lean_object* v_t_920_, lean_object* v_h_921_, lean_object* v_free_922_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_920_, v_free_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_guarded_elim___redArg(lean_object* v_t_924_, lean_object* v_guarded_925_){
_start:
{
lean_object* v___x_926_; 
v___x_926_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_924_, v_guarded_925_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_guarded_elim(lean_object* v_00_u03c4_927_, lean_object* v_motive_928_, lean_object* v_t_929_, lean_object* v_h_930_, lean_object* v_guarded_931_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_929_, v_guarded_931_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_costing_elim___redArg(lean_object* v_t_933_, lean_object* v_costing_934_){
_start:
{
lean_object* v___x_935_; 
v___x_935_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_933_, v_costing_934_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_costing_elim(lean_object* v_00_u03c4_936_, lean_object* v_motive_937_, lean_object* v_t_938_, lean_object* v_h_939_, lean_object* v_costing_940_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_938_, v_costing_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_either_elim___redArg(lean_object* v_t_942_, lean_object* v_either_943_){
_start:
{
lean_object* v___x_944_; 
v___x_944_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_942_, v_either_943_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_either_elim(lean_object* v_00_u03c4_945_, lean_object* v_motive_946_, lean_object* v_t_947_, lean_object* v_h_948_, lean_object* v_either_949_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_947_, v_either_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_append_elim___redArg(lean_object* v_t_951_, lean_object* v_append_952_){
_start:
{
lean_object* v___x_953_; 
v___x_953_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_951_, v_append_952_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_append_elim(lean_object* v_00_u03c4_954_, lean_object* v_motive_955_, lean_object* v_t_956_, lean_object* v_h_957_, lean_object* v_append_958_){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_956_, v_append_958_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_failureSet_match__1_splitter___redArg(lean_object* v_x_960_, lean_object* v_h__1_961_, lean_object* v_h__2_962_, lean_object* v_h__3_963_, lean_object* v_h__4_964_, lean_object* v_h__5_965_, lean_object* v_h__6_966_, lean_object* v_h__7_967_, lean_object* v_h__8_968_, lean_object* v_h__9_969_, lean_object* v_h__10_970_, lean_object* v_h__11_971_, lean_object* v_h__12_972_, lean_object* v_h__13_973_, lean_object* v_h__14_974_, lean_object* v_h__15_975_, lean_object* v_h__16_976_){
_start:
{
switch(lean_obj_tag(v_x_960_))
{
case 0:
{
lean_object* v___x_977_; 
lean_dec(v_h__16_976_);
lean_dec(v_h__15_975_);
lean_dec(v_h__14_974_);
lean_dec(v_h__13_973_);
lean_dec(v_h__12_972_);
lean_dec(v_h__11_971_);
lean_dec(v_h__10_970_);
lean_dec(v_h__9_969_);
lean_dec(v_h__8_968_);
lean_dec(v_h__7_967_);
lean_dec(v_h__6_966_);
lean_dec(v_h__5_965_);
lean_dec(v_h__4_964_);
lean_dec(v_h__3_963_);
lean_dec(v_h__2_962_);
v___x_977_ = lean_apply_1(v_h__1_961_, lean_box(0));
return v___x_977_;
}
case 1:
{
lean_object* v_f_978_; lean_object* v___x_979_; 
lean_dec(v_h__16_976_);
lean_dec(v_h__15_975_);
lean_dec(v_h__14_974_);
lean_dec(v_h__13_973_);
lean_dec(v_h__12_972_);
lean_dec(v_h__11_971_);
lean_dec(v_h__10_970_);
lean_dec(v_h__9_969_);
lean_dec(v_h__8_968_);
lean_dec(v_h__7_967_);
lean_dec(v_h__6_966_);
lean_dec(v_h__5_965_);
lean_dec(v_h__4_964_);
lean_dec(v_h__3_963_);
lean_dec(v_h__1_961_);
v_f_978_ = lean_ctor_get(v_x_960_, 0);
lean_inc_ref(v_f_978_);
lean_dec_ref_known(v_x_960_, 1);
v___x_979_ = lean_apply_2(v_h__2_962_, lean_box(0), v_f_978_);
return v___x_979_;
}
case 2:
{
lean_object* v_s_980_; lean_object* v___x_981_; 
lean_dec(v_h__16_976_);
lean_dec(v_h__15_975_);
lean_dec(v_h__14_974_);
lean_dec(v_h__13_973_);
lean_dec(v_h__12_972_);
lean_dec(v_h__11_971_);
lean_dec(v_h__10_970_);
lean_dec(v_h__9_969_);
lean_dec(v_h__8_968_);
lean_dec(v_h__7_967_);
lean_dec(v_h__6_966_);
lean_dec(v_h__5_965_);
lean_dec(v_h__4_964_);
lean_dec(v_h__2_962_);
lean_dec(v_h__1_961_);
v_s_980_ = lean_ctor_get(v_x_960_, 0);
lean_inc_ref(v_s_980_);
lean_dec_ref_known(v_x_960_, 1);
v___x_981_ = lean_apply_2(v_h__3_963_, lean_box(0), v_s_980_);
return v___x_981_;
}
case 3:
{
lean_object* v_id_982_; lean_object* v_d_983_; lean_object* v___x_984_; 
lean_dec(v_h__16_976_);
lean_dec(v_h__15_975_);
lean_dec(v_h__14_974_);
lean_dec(v_h__13_973_);
lean_dec(v_h__12_972_);
lean_dec(v_h__11_971_);
lean_dec(v_h__10_970_);
lean_dec(v_h__9_969_);
lean_dec(v_h__8_968_);
lean_dec(v_h__6_966_);
lean_dec(v_h__5_965_);
lean_dec(v_h__4_964_);
lean_dec(v_h__3_963_);
lean_dec(v_h__2_962_);
lean_dec(v_h__1_961_);
v_id_982_ = lean_ctor_get(v_x_960_, 0);
lean_inc(v_id_982_);
v_d_983_ = lean_ctor_get(v_x_960_, 1);
lean_inc(v_d_983_);
lean_dec_ref_known(v_x_960_, 2);
v___x_984_ = lean_apply_3(v_h__7_967_, lean_box(0), v_id_982_, v_d_983_);
return v___x_984_;
}
case 4:
{
lean_object* v_d_985_; lean_object* v___x_986_; 
lean_dec(v_h__16_976_);
lean_dec(v_h__15_975_);
lean_dec(v_h__14_974_);
lean_dec(v_h__13_973_);
lean_dec(v_h__12_972_);
lean_dec(v_h__11_971_);
lean_dec(v_h__10_970_);
lean_dec(v_h__9_969_);
lean_dec(v_h__8_968_);
lean_dec(v_h__7_967_);
lean_dec(v_h__6_966_);
lean_dec(v_h__5_965_);
lean_dec(v_h__3_963_);
lean_dec(v_h__2_962_);
lean_dec(v_h__1_961_);
v_d_985_ = lean_ctor_get(v_x_960_, 0);
lean_inc(v_d_985_);
lean_dec_ref_known(v_x_960_, 1);
v___x_986_ = lean_apply_2(v_h__4_964_, lean_box(0), v_d_985_);
return v___x_986_;
}
case 5:
{
lean_object* v_d_987_; lean_object* v___x_988_; 
lean_dec(v_h__16_976_);
lean_dec(v_h__15_975_);
lean_dec(v_h__14_974_);
lean_dec(v_h__13_973_);
lean_dec(v_h__12_972_);
lean_dec(v_h__11_971_);
lean_dec(v_h__10_970_);
lean_dec(v_h__9_969_);
lean_dec(v_h__8_968_);
lean_dec(v_h__7_967_);
lean_dec(v_h__6_966_);
lean_dec(v_h__4_964_);
lean_dec(v_h__3_963_);
lean_dec(v_h__2_962_);
lean_dec(v_h__1_961_);
v_d_987_ = lean_ctor_get(v_x_960_, 0);
lean_inc(v_d_987_);
lean_dec_ref_known(v_x_960_, 1);
v___x_988_ = lean_apply_2(v_h__5_965_, lean_box(0), v_d_987_);
return v___x_988_;
}
case 6:
{
lean_object* v_n_989_; uint8_t v_isCumulative_990_; lean_object* v_d_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
lean_dec(v_h__16_976_);
lean_dec(v_h__15_975_);
lean_dec(v_h__14_974_);
lean_dec(v_h__13_973_);
lean_dec(v_h__12_972_);
lean_dec(v_h__11_971_);
lean_dec(v_h__10_970_);
lean_dec(v_h__9_969_);
lean_dec(v_h__7_967_);
lean_dec(v_h__6_966_);
lean_dec(v_h__5_965_);
lean_dec(v_h__4_964_);
lean_dec(v_h__3_963_);
lean_dec(v_h__2_962_);
lean_dec(v_h__1_961_);
v_n_989_ = lean_ctor_get(v_x_960_, 0);
lean_inc(v_n_989_);
v_isCumulative_990_ = lean_ctor_get_uint8(v_x_960_, sizeof(void*)*2);
v_d_991_ = lean_ctor_get(v_x_960_, 1);
lean_inc(v_d_991_);
lean_dec_ref_known(v_x_960_, 2);
v___x_992_ = lean_box(v_isCumulative_990_);
v___x_993_ = lean_apply_4(v_h__8_968_, lean_box(0), v_n_989_, v___x_992_, v_d_991_);
return v___x_993_;
}
case 7:
{
lean_object* v_d_994_; lean_object* v___x_995_; 
lean_dec(v_h__16_976_);
lean_dec(v_h__15_975_);
lean_dec(v_h__14_974_);
lean_dec(v_h__13_973_);
lean_dec(v_h__12_972_);
lean_dec(v_h__11_971_);
lean_dec(v_h__10_970_);
lean_dec(v_h__8_968_);
lean_dec(v_h__7_967_);
lean_dec(v_h__6_966_);
lean_dec(v_h__5_965_);
lean_dec(v_h__4_964_);
lean_dec(v_h__3_963_);
lean_dec(v_h__2_962_);
lean_dec(v_h__1_961_);
v_d_994_ = lean_ctor_get(v_x_960_, 0);
lean_inc(v_d_994_);
lean_dec_ref_known(v_x_960_, 1);
v___x_995_ = lean_apply_2(v_h__9_969_, lean_box(0), v_d_994_);
return v___x_995_;
}
case 8:
{
uint8_t v_onlyNonCumulative_996_; lean_object* v_d_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
lean_dec(v_h__16_976_);
lean_dec(v_h__15_975_);
lean_dec(v_h__14_974_);
lean_dec(v_h__13_973_);
lean_dec(v_h__12_972_);
lean_dec(v_h__11_971_);
lean_dec(v_h__9_969_);
lean_dec(v_h__8_968_);
lean_dec(v_h__7_967_);
lean_dec(v_h__6_966_);
lean_dec(v_h__5_965_);
lean_dec(v_h__4_964_);
lean_dec(v_h__3_963_);
lean_dec(v_h__2_962_);
lean_dec(v_h__1_961_);
v_onlyNonCumulative_996_ = lean_ctor_get_uint8(v_x_960_, sizeof(void*)*1);
v_d_997_ = lean_ctor_get(v_x_960_, 0);
lean_inc(v_d_997_);
lean_dec_ref_known(v_x_960_, 1);
v___x_998_ = lean_box(v_onlyNonCumulative_996_);
v___x_999_ = lean_apply_3(v_h__10_970_, lean_box(0), v___x_998_, v_d_997_);
return v___x_999_;
}
case 9:
{
lean_object* v_d_1000_; lean_object* v___x_1001_; 
lean_dec(v_h__16_976_);
lean_dec(v_h__15_975_);
lean_dec(v_h__14_974_);
lean_dec(v_h__12_972_);
lean_dec(v_h__11_971_);
lean_dec(v_h__10_970_);
lean_dec(v_h__9_969_);
lean_dec(v_h__8_968_);
lean_dec(v_h__7_967_);
lean_dec(v_h__6_966_);
lean_dec(v_h__5_965_);
lean_dec(v_h__4_964_);
lean_dec(v_h__3_963_);
lean_dec(v_h__2_962_);
lean_dec(v_h__1_961_);
v_d_1000_ = lean_ctor_get(v_x_960_, 0);
lean_inc(v_d_1000_);
lean_dec_ref_known(v_x_960_, 1);
v___x_1001_ = lean_apply_2(v_h__13_973_, lean_box(0), v_d_1000_);
return v___x_1001_;
}
case 10:
{
lean_object* v_d_1002_; lean_object* v___x_1003_; 
lean_dec(v_h__16_976_);
lean_dec(v_h__15_975_);
lean_dec(v_h__13_973_);
lean_dec(v_h__12_972_);
lean_dec(v_h__11_971_);
lean_dec(v_h__10_970_);
lean_dec(v_h__9_969_);
lean_dec(v_h__8_968_);
lean_dec(v_h__7_967_);
lean_dec(v_h__6_966_);
lean_dec(v_h__5_965_);
lean_dec(v_h__4_964_);
lean_dec(v_h__3_963_);
lean_dec(v_h__2_962_);
lean_dec(v_h__1_961_);
v_d_1002_ = lean_ctor_get(v_x_960_, 0);
lean_inc(v_d_1002_);
lean_dec_ref_known(v_x_960_, 1);
v___x_1003_ = lean_apply_2(v_h__14_974_, lean_box(0), v_d_1002_);
return v___x_1003_;
}
case 11:
{
lean_object* v_d_1004_; lean_object* v___x_1005_; 
lean_dec(v_h__16_976_);
lean_dec(v_h__15_975_);
lean_dec(v_h__14_974_);
lean_dec(v_h__13_973_);
lean_dec(v_h__12_972_);
lean_dec(v_h__10_970_);
lean_dec(v_h__9_969_);
lean_dec(v_h__8_968_);
lean_dec(v_h__7_967_);
lean_dec(v_h__6_966_);
lean_dec(v_h__5_965_);
lean_dec(v_h__4_964_);
lean_dec(v_h__3_963_);
lean_dec(v_h__2_962_);
lean_dec(v_h__1_961_);
v_d_1004_ = lean_ctor_get(v_x_960_, 0);
lean_inc(v_d_1004_);
lean_dec_ref_known(v_x_960_, 1);
v___x_1005_ = lean_apply_2(v_h__11_971_, lean_box(0), v_d_1004_);
return v___x_1005_;
}
case 12:
{
lean_object* v_p_1006_; lean_object* v_d_1007_; lean_object* v___x_1008_; 
lean_dec(v_h__16_976_);
lean_dec(v_h__15_975_);
lean_dec(v_h__14_974_);
lean_dec(v_h__13_973_);
lean_dec(v_h__12_972_);
lean_dec(v_h__11_971_);
lean_dec(v_h__10_970_);
lean_dec(v_h__9_969_);
lean_dec(v_h__8_968_);
lean_dec(v_h__7_967_);
lean_dec(v_h__5_965_);
lean_dec(v_h__4_964_);
lean_dec(v_h__3_963_);
lean_dec(v_h__2_962_);
lean_dec(v_h__1_961_);
v_p_1006_ = lean_ctor_get(v_x_960_, 0);
lean_inc_ref(v_p_1006_);
v_d_1007_ = lean_ctor_get(v_x_960_, 1);
lean_inc(v_d_1007_);
lean_dec_ref_known(v_x_960_, 2);
v___x_1008_ = lean_apply_3(v_h__6_966_, lean_box(0), v_p_1006_, v_d_1007_);
return v___x_1008_;
}
case 13:
{
lean_object* v_cost_1009_; lean_object* v_d_1010_; lean_object* v___x_1011_; 
lean_dec(v_h__16_976_);
lean_dec(v_h__15_975_);
lean_dec(v_h__14_974_);
lean_dec(v_h__13_973_);
lean_dec(v_h__11_971_);
lean_dec(v_h__10_970_);
lean_dec(v_h__9_969_);
lean_dec(v_h__8_968_);
lean_dec(v_h__7_967_);
lean_dec(v_h__6_966_);
lean_dec(v_h__5_965_);
lean_dec(v_h__4_964_);
lean_dec(v_h__3_963_);
lean_dec(v_h__2_962_);
lean_dec(v_h__1_961_);
v_cost_1009_ = lean_ctor_get(v_x_960_, 0);
lean_inc(v_cost_1009_);
v_d_1010_ = lean_ctor_get(v_x_960_, 1);
lean_inc(v_d_1010_);
lean_dec_ref_known(v_x_960_, 2);
v___x_1011_ = lean_apply_3(v_h__12_972_, lean_box(0), v_cost_1009_, v_d_1010_);
return v___x_1011_;
}
case 14:
{
lean_object* v_a_1012_; lean_object* v_b_1013_; lean_object* v___x_1014_; 
lean_dec(v_h__16_976_);
lean_dec(v_h__14_974_);
lean_dec(v_h__13_973_);
lean_dec(v_h__12_972_);
lean_dec(v_h__11_971_);
lean_dec(v_h__10_970_);
lean_dec(v_h__9_969_);
lean_dec(v_h__8_968_);
lean_dec(v_h__7_967_);
lean_dec(v_h__6_966_);
lean_dec(v_h__5_965_);
lean_dec(v_h__4_964_);
lean_dec(v_h__3_963_);
lean_dec(v_h__2_962_);
lean_dec(v_h__1_961_);
v_a_1012_ = lean_ctor_get(v_x_960_, 0);
lean_inc(v_a_1012_);
v_b_1013_ = lean_ctor_get(v_x_960_, 1);
lean_inc(v_b_1013_);
lean_dec_ref_known(v_x_960_, 2);
v___x_1014_ = lean_apply_3(v_h__15_975_, lean_box(0), v_a_1012_, v_b_1013_);
return v___x_1014_;
}
default: 
{
lean_object* v_a_1015_; lean_object* v_b_1016_; lean_object* v___x_1017_; 
lean_dec(v_h__15_975_);
lean_dec(v_h__14_974_);
lean_dec(v_h__13_973_);
lean_dec(v_h__12_972_);
lean_dec(v_h__11_971_);
lean_dec(v_h__10_970_);
lean_dec(v_h__9_969_);
lean_dec(v_h__8_968_);
lean_dec(v_h__7_967_);
lean_dec(v_h__6_966_);
lean_dec(v_h__5_965_);
lean_dec(v_h__4_964_);
lean_dec(v_h__3_963_);
lean_dec(v_h__2_962_);
lean_dec(v_h__1_961_);
v_a_1015_ = lean_ctor_get(v_x_960_, 0);
lean_inc(v_a_1015_);
v_b_1016_ = lean_ctor_get(v_x_960_, 1);
lean_inc(v_b_1016_);
lean_dec_ref_known(v_x_960_, 2);
v___x_1017_ = lean_apply_3(v_h__16_976_, lean_box(0), v_a_1015_, v_b_1016_);
return v___x_1017_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_failureSet_match__1_splitter___redArg___boxed(lean_object** _args){
lean_object* v_x_1018_ = _args[0];
lean_object* v_h__1_1019_ = _args[1];
lean_object* v_h__2_1020_ = _args[2];
lean_object* v_h__3_1021_ = _args[3];
lean_object* v_h__4_1022_ = _args[4];
lean_object* v_h__5_1023_ = _args[5];
lean_object* v_h__6_1024_ = _args[6];
lean_object* v_h__7_1025_ = _args[7];
lean_object* v_h__8_1026_ = _args[8];
lean_object* v_h__9_1027_ = _args[9];
lean_object* v_h__10_1028_ = _args[10];
lean_object* v_h__11_1029_ = _args[11];
lean_object* v_h__12_1030_ = _args[12];
lean_object* v_h__13_1031_ = _args[13];
lean_object* v_h__14_1032_ = _args[14];
lean_object* v_h__15_1033_ = _args[15];
lean_object* v_h__16_1034_ = _args[16];
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_failureSet_match__1_splitter___redArg(v_x_1018_, v_h__1_1019_, v_h__2_1020_, v_h__3_1021_, v_h__4_1022_, v_h__5_1023_, v_h__6_1024_, v_h__7_1025_, v_h__8_1026_, v_h__9_1027_, v_h__10_1028_, v_h__11_1029_, v_h__12_1030_, v_h__13_1031_, v_h__14_1032_, v_h__15_1033_, v_h__16_1034_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_failureSet_match__1_splitter(lean_object* v_motive_1036_, lean_object* v_x_1037_, lean_object* v_x_1038_, lean_object* v_h__1_1039_, lean_object* v_h__2_1040_, lean_object* v_h__3_1041_, lean_object* v_h__4_1042_, lean_object* v_h__5_1043_, lean_object* v_h__6_1044_, lean_object* v_h__7_1045_, lean_object* v_h__8_1046_, lean_object* v_h__9_1047_, lean_object* v_h__10_1048_, lean_object* v_h__11_1049_, lean_object* v_h__12_1050_, lean_object* v_h__13_1051_, lean_object* v_h__14_1052_, lean_object* v_h__15_1053_, lean_object* v_h__16_1054_){
_start:
{
switch(lean_obj_tag(v_x_1038_))
{
case 0:
{
lean_object* v___x_1055_; 
lean_dec(v_h__16_1054_);
lean_dec(v_h__15_1053_);
lean_dec(v_h__14_1052_);
lean_dec(v_h__13_1051_);
lean_dec(v_h__12_1050_);
lean_dec(v_h__11_1049_);
lean_dec(v_h__10_1048_);
lean_dec(v_h__9_1047_);
lean_dec(v_h__8_1046_);
lean_dec(v_h__7_1045_);
lean_dec(v_h__6_1044_);
lean_dec(v_h__5_1043_);
lean_dec(v_h__4_1042_);
lean_dec(v_h__3_1041_);
lean_dec(v_h__2_1040_);
v___x_1055_ = lean_apply_1(v_h__1_1039_, lean_box(0));
return v___x_1055_;
}
case 1:
{
lean_object* v_f_1056_; lean_object* v___x_1057_; 
lean_dec(v_h__16_1054_);
lean_dec(v_h__15_1053_);
lean_dec(v_h__14_1052_);
lean_dec(v_h__13_1051_);
lean_dec(v_h__12_1050_);
lean_dec(v_h__11_1049_);
lean_dec(v_h__10_1048_);
lean_dec(v_h__9_1047_);
lean_dec(v_h__8_1046_);
lean_dec(v_h__7_1045_);
lean_dec(v_h__6_1044_);
lean_dec(v_h__5_1043_);
lean_dec(v_h__4_1042_);
lean_dec(v_h__3_1041_);
lean_dec(v_h__1_1039_);
v_f_1056_ = lean_ctor_get(v_x_1038_, 0);
lean_inc_ref(v_f_1056_);
lean_dec_ref_known(v_x_1038_, 1);
v___x_1057_ = lean_apply_2(v_h__2_1040_, lean_box(0), v_f_1056_);
return v___x_1057_;
}
case 2:
{
lean_object* v_s_1058_; lean_object* v___x_1059_; 
lean_dec(v_h__16_1054_);
lean_dec(v_h__15_1053_);
lean_dec(v_h__14_1052_);
lean_dec(v_h__13_1051_);
lean_dec(v_h__12_1050_);
lean_dec(v_h__11_1049_);
lean_dec(v_h__10_1048_);
lean_dec(v_h__9_1047_);
lean_dec(v_h__8_1046_);
lean_dec(v_h__7_1045_);
lean_dec(v_h__6_1044_);
lean_dec(v_h__5_1043_);
lean_dec(v_h__4_1042_);
lean_dec(v_h__2_1040_);
lean_dec(v_h__1_1039_);
v_s_1058_ = lean_ctor_get(v_x_1038_, 0);
lean_inc_ref(v_s_1058_);
lean_dec_ref_known(v_x_1038_, 1);
v___x_1059_ = lean_apply_2(v_h__3_1041_, lean_box(0), v_s_1058_);
return v___x_1059_;
}
case 3:
{
lean_object* v_id_1060_; lean_object* v_d_1061_; lean_object* v___x_1062_; 
lean_dec(v_h__16_1054_);
lean_dec(v_h__15_1053_);
lean_dec(v_h__14_1052_);
lean_dec(v_h__13_1051_);
lean_dec(v_h__12_1050_);
lean_dec(v_h__11_1049_);
lean_dec(v_h__10_1048_);
lean_dec(v_h__9_1047_);
lean_dec(v_h__8_1046_);
lean_dec(v_h__6_1044_);
lean_dec(v_h__5_1043_);
lean_dec(v_h__4_1042_);
lean_dec(v_h__3_1041_);
lean_dec(v_h__2_1040_);
lean_dec(v_h__1_1039_);
v_id_1060_ = lean_ctor_get(v_x_1038_, 0);
lean_inc(v_id_1060_);
v_d_1061_ = lean_ctor_get(v_x_1038_, 1);
lean_inc(v_d_1061_);
lean_dec_ref_known(v_x_1038_, 2);
v___x_1062_ = lean_apply_3(v_h__7_1045_, lean_box(0), v_id_1060_, v_d_1061_);
return v___x_1062_;
}
case 4:
{
lean_object* v_d_1063_; lean_object* v___x_1064_; 
lean_dec(v_h__16_1054_);
lean_dec(v_h__15_1053_);
lean_dec(v_h__14_1052_);
lean_dec(v_h__13_1051_);
lean_dec(v_h__12_1050_);
lean_dec(v_h__11_1049_);
lean_dec(v_h__10_1048_);
lean_dec(v_h__9_1047_);
lean_dec(v_h__8_1046_);
lean_dec(v_h__7_1045_);
lean_dec(v_h__6_1044_);
lean_dec(v_h__5_1043_);
lean_dec(v_h__3_1041_);
lean_dec(v_h__2_1040_);
lean_dec(v_h__1_1039_);
v_d_1063_ = lean_ctor_get(v_x_1038_, 0);
lean_inc(v_d_1063_);
lean_dec_ref_known(v_x_1038_, 1);
v___x_1064_ = lean_apply_2(v_h__4_1042_, lean_box(0), v_d_1063_);
return v___x_1064_;
}
case 5:
{
lean_object* v_d_1065_; lean_object* v___x_1066_; 
lean_dec(v_h__16_1054_);
lean_dec(v_h__15_1053_);
lean_dec(v_h__14_1052_);
lean_dec(v_h__13_1051_);
lean_dec(v_h__12_1050_);
lean_dec(v_h__11_1049_);
lean_dec(v_h__10_1048_);
lean_dec(v_h__9_1047_);
lean_dec(v_h__8_1046_);
lean_dec(v_h__7_1045_);
lean_dec(v_h__6_1044_);
lean_dec(v_h__4_1042_);
lean_dec(v_h__3_1041_);
lean_dec(v_h__2_1040_);
lean_dec(v_h__1_1039_);
v_d_1065_ = lean_ctor_get(v_x_1038_, 0);
lean_inc(v_d_1065_);
lean_dec_ref_known(v_x_1038_, 1);
v___x_1066_ = lean_apply_2(v_h__5_1043_, lean_box(0), v_d_1065_);
return v___x_1066_;
}
case 6:
{
lean_object* v_n_1067_; uint8_t v_isCumulative_1068_; lean_object* v_d_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
lean_dec(v_h__16_1054_);
lean_dec(v_h__15_1053_);
lean_dec(v_h__14_1052_);
lean_dec(v_h__13_1051_);
lean_dec(v_h__12_1050_);
lean_dec(v_h__11_1049_);
lean_dec(v_h__10_1048_);
lean_dec(v_h__9_1047_);
lean_dec(v_h__7_1045_);
lean_dec(v_h__6_1044_);
lean_dec(v_h__5_1043_);
lean_dec(v_h__4_1042_);
lean_dec(v_h__3_1041_);
lean_dec(v_h__2_1040_);
lean_dec(v_h__1_1039_);
v_n_1067_ = lean_ctor_get(v_x_1038_, 0);
lean_inc(v_n_1067_);
v_isCumulative_1068_ = lean_ctor_get_uint8(v_x_1038_, sizeof(void*)*2);
v_d_1069_ = lean_ctor_get(v_x_1038_, 1);
lean_inc(v_d_1069_);
lean_dec_ref_known(v_x_1038_, 2);
v___x_1070_ = lean_box(v_isCumulative_1068_);
v___x_1071_ = lean_apply_4(v_h__8_1046_, lean_box(0), v_n_1067_, v___x_1070_, v_d_1069_);
return v___x_1071_;
}
case 7:
{
lean_object* v_d_1072_; lean_object* v___x_1073_; 
lean_dec(v_h__16_1054_);
lean_dec(v_h__15_1053_);
lean_dec(v_h__14_1052_);
lean_dec(v_h__13_1051_);
lean_dec(v_h__12_1050_);
lean_dec(v_h__11_1049_);
lean_dec(v_h__10_1048_);
lean_dec(v_h__8_1046_);
lean_dec(v_h__7_1045_);
lean_dec(v_h__6_1044_);
lean_dec(v_h__5_1043_);
lean_dec(v_h__4_1042_);
lean_dec(v_h__3_1041_);
lean_dec(v_h__2_1040_);
lean_dec(v_h__1_1039_);
v_d_1072_ = lean_ctor_get(v_x_1038_, 0);
lean_inc(v_d_1072_);
lean_dec_ref_known(v_x_1038_, 1);
v___x_1073_ = lean_apply_2(v_h__9_1047_, lean_box(0), v_d_1072_);
return v___x_1073_;
}
case 8:
{
uint8_t v_onlyNonCumulative_1074_; lean_object* v_d_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
lean_dec(v_h__16_1054_);
lean_dec(v_h__15_1053_);
lean_dec(v_h__14_1052_);
lean_dec(v_h__13_1051_);
lean_dec(v_h__12_1050_);
lean_dec(v_h__11_1049_);
lean_dec(v_h__9_1047_);
lean_dec(v_h__8_1046_);
lean_dec(v_h__7_1045_);
lean_dec(v_h__6_1044_);
lean_dec(v_h__5_1043_);
lean_dec(v_h__4_1042_);
lean_dec(v_h__3_1041_);
lean_dec(v_h__2_1040_);
lean_dec(v_h__1_1039_);
v_onlyNonCumulative_1074_ = lean_ctor_get_uint8(v_x_1038_, sizeof(void*)*1);
v_d_1075_ = lean_ctor_get(v_x_1038_, 0);
lean_inc(v_d_1075_);
lean_dec_ref_known(v_x_1038_, 1);
v___x_1076_ = lean_box(v_onlyNonCumulative_1074_);
v___x_1077_ = lean_apply_3(v_h__10_1048_, lean_box(0), v___x_1076_, v_d_1075_);
return v___x_1077_;
}
case 9:
{
lean_object* v_d_1078_; lean_object* v___x_1079_; 
lean_dec(v_h__16_1054_);
lean_dec(v_h__15_1053_);
lean_dec(v_h__14_1052_);
lean_dec(v_h__12_1050_);
lean_dec(v_h__11_1049_);
lean_dec(v_h__10_1048_);
lean_dec(v_h__9_1047_);
lean_dec(v_h__8_1046_);
lean_dec(v_h__7_1045_);
lean_dec(v_h__6_1044_);
lean_dec(v_h__5_1043_);
lean_dec(v_h__4_1042_);
lean_dec(v_h__3_1041_);
lean_dec(v_h__2_1040_);
lean_dec(v_h__1_1039_);
v_d_1078_ = lean_ctor_get(v_x_1038_, 0);
lean_inc(v_d_1078_);
lean_dec_ref_known(v_x_1038_, 1);
v___x_1079_ = lean_apply_2(v_h__13_1051_, lean_box(0), v_d_1078_);
return v___x_1079_;
}
case 10:
{
lean_object* v_d_1080_; lean_object* v___x_1081_; 
lean_dec(v_h__16_1054_);
lean_dec(v_h__15_1053_);
lean_dec(v_h__13_1051_);
lean_dec(v_h__12_1050_);
lean_dec(v_h__11_1049_);
lean_dec(v_h__10_1048_);
lean_dec(v_h__9_1047_);
lean_dec(v_h__8_1046_);
lean_dec(v_h__7_1045_);
lean_dec(v_h__6_1044_);
lean_dec(v_h__5_1043_);
lean_dec(v_h__4_1042_);
lean_dec(v_h__3_1041_);
lean_dec(v_h__2_1040_);
lean_dec(v_h__1_1039_);
v_d_1080_ = lean_ctor_get(v_x_1038_, 0);
lean_inc(v_d_1080_);
lean_dec_ref_known(v_x_1038_, 1);
v___x_1081_ = lean_apply_2(v_h__14_1052_, lean_box(0), v_d_1080_);
return v___x_1081_;
}
case 11:
{
lean_object* v_d_1082_; lean_object* v___x_1083_; 
lean_dec(v_h__16_1054_);
lean_dec(v_h__15_1053_);
lean_dec(v_h__14_1052_);
lean_dec(v_h__13_1051_);
lean_dec(v_h__12_1050_);
lean_dec(v_h__10_1048_);
lean_dec(v_h__9_1047_);
lean_dec(v_h__8_1046_);
lean_dec(v_h__7_1045_);
lean_dec(v_h__6_1044_);
lean_dec(v_h__5_1043_);
lean_dec(v_h__4_1042_);
lean_dec(v_h__3_1041_);
lean_dec(v_h__2_1040_);
lean_dec(v_h__1_1039_);
v_d_1082_ = lean_ctor_get(v_x_1038_, 0);
lean_inc(v_d_1082_);
lean_dec_ref_known(v_x_1038_, 1);
v___x_1083_ = lean_apply_2(v_h__11_1049_, lean_box(0), v_d_1082_);
return v___x_1083_;
}
case 12:
{
lean_object* v_p_1084_; lean_object* v_d_1085_; lean_object* v___x_1086_; 
lean_dec(v_h__16_1054_);
lean_dec(v_h__15_1053_);
lean_dec(v_h__14_1052_);
lean_dec(v_h__13_1051_);
lean_dec(v_h__12_1050_);
lean_dec(v_h__11_1049_);
lean_dec(v_h__10_1048_);
lean_dec(v_h__9_1047_);
lean_dec(v_h__8_1046_);
lean_dec(v_h__7_1045_);
lean_dec(v_h__5_1043_);
lean_dec(v_h__4_1042_);
lean_dec(v_h__3_1041_);
lean_dec(v_h__2_1040_);
lean_dec(v_h__1_1039_);
v_p_1084_ = lean_ctor_get(v_x_1038_, 0);
lean_inc_ref(v_p_1084_);
v_d_1085_ = lean_ctor_get(v_x_1038_, 1);
lean_inc(v_d_1085_);
lean_dec_ref_known(v_x_1038_, 2);
v___x_1086_ = lean_apply_3(v_h__6_1044_, lean_box(0), v_p_1084_, v_d_1085_);
return v___x_1086_;
}
case 13:
{
lean_object* v_cost_1087_; lean_object* v_d_1088_; lean_object* v___x_1089_; 
lean_dec(v_h__16_1054_);
lean_dec(v_h__15_1053_);
lean_dec(v_h__14_1052_);
lean_dec(v_h__13_1051_);
lean_dec(v_h__11_1049_);
lean_dec(v_h__10_1048_);
lean_dec(v_h__9_1047_);
lean_dec(v_h__8_1046_);
lean_dec(v_h__7_1045_);
lean_dec(v_h__6_1044_);
lean_dec(v_h__5_1043_);
lean_dec(v_h__4_1042_);
lean_dec(v_h__3_1041_);
lean_dec(v_h__2_1040_);
lean_dec(v_h__1_1039_);
v_cost_1087_ = lean_ctor_get(v_x_1038_, 0);
lean_inc(v_cost_1087_);
v_d_1088_ = lean_ctor_get(v_x_1038_, 1);
lean_inc(v_d_1088_);
lean_dec_ref_known(v_x_1038_, 2);
v___x_1089_ = lean_apply_3(v_h__12_1050_, lean_box(0), v_cost_1087_, v_d_1088_);
return v___x_1089_;
}
case 14:
{
lean_object* v_a_1090_; lean_object* v_b_1091_; lean_object* v___x_1092_; 
lean_dec(v_h__16_1054_);
lean_dec(v_h__14_1052_);
lean_dec(v_h__13_1051_);
lean_dec(v_h__12_1050_);
lean_dec(v_h__11_1049_);
lean_dec(v_h__10_1048_);
lean_dec(v_h__9_1047_);
lean_dec(v_h__8_1046_);
lean_dec(v_h__7_1045_);
lean_dec(v_h__6_1044_);
lean_dec(v_h__5_1043_);
lean_dec(v_h__4_1042_);
lean_dec(v_h__3_1041_);
lean_dec(v_h__2_1040_);
lean_dec(v_h__1_1039_);
v_a_1090_ = lean_ctor_get(v_x_1038_, 0);
lean_inc(v_a_1090_);
v_b_1091_ = lean_ctor_get(v_x_1038_, 1);
lean_inc(v_b_1091_);
lean_dec_ref_known(v_x_1038_, 2);
v___x_1092_ = lean_apply_3(v_h__15_1053_, lean_box(0), v_a_1090_, v_b_1091_);
return v___x_1092_;
}
default: 
{
lean_object* v_a_1093_; lean_object* v_b_1094_; lean_object* v___x_1095_; 
lean_dec(v_h__15_1053_);
lean_dec(v_h__14_1052_);
lean_dec(v_h__13_1051_);
lean_dec(v_h__12_1050_);
lean_dec(v_h__11_1049_);
lean_dec(v_h__10_1048_);
lean_dec(v_h__9_1047_);
lean_dec(v_h__8_1046_);
lean_dec(v_h__7_1045_);
lean_dec(v_h__6_1044_);
lean_dec(v_h__5_1043_);
lean_dec(v_h__4_1042_);
lean_dec(v_h__3_1041_);
lean_dec(v_h__2_1040_);
lean_dec(v_h__1_1039_);
v_a_1093_ = lean_ctor_get(v_x_1038_, 0);
lean_inc(v_a_1093_);
v_b_1094_ = lean_ctor_get(v_x_1038_, 1);
lean_inc(v_b_1094_);
lean_dec_ref_known(v_x_1038_, 2);
v___x_1095_ = lean_apply_3(v_h__16_1054_, lean_box(0), v_a_1093_, v_b_1094_);
return v___x_1095_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_failureSet_match__1_splitter___boxed(lean_object** _args){
lean_object* v_motive_1096_ = _args[0];
lean_object* v_x_1097_ = _args[1];
lean_object* v_x_1098_ = _args[2];
lean_object* v_h__1_1099_ = _args[3];
lean_object* v_h__2_1100_ = _args[4];
lean_object* v_h__3_1101_ = _args[5];
lean_object* v_h__4_1102_ = _args[6];
lean_object* v_h__5_1103_ = _args[7];
lean_object* v_h__6_1104_ = _args[8];
lean_object* v_h__7_1105_ = _args[9];
lean_object* v_h__8_1106_ = _args[10];
lean_object* v_h__9_1107_ = _args[11];
lean_object* v_h__10_1108_ = _args[12];
lean_object* v_h__11_1109_ = _args[13];
lean_object* v_h__12_1110_ = _args[14];
lean_object* v_h__13_1111_ = _args[15];
lean_object* v_h__14_1112_ = _args[16];
lean_object* v_h__15_1113_ = _args[17];
lean_object* v_h__16_1114_ = _args[18];
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_failureSet_match__1_splitter(v_motive_1096_, v_x_1097_, v_x_1098_, v_h__1_1099_, v_h__2_1100_, v_h__3_1101_, v_h__4_1102_, v_h__5_1103_, v_h__6_1104_, v_h__7_1105_, v_h__8_1106_, v_h__9_1107_, v_h__10_1108_, v_h__11_1109_, v_h__12_1110_, v_h__13_1111_, v_h__14_1112_, v_h__15_1113_, v_h__16_1114_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_maxNewlineCount_x3f_match__1_splitter___redArg(lean_object* v_x_1116_, lean_object* v_h__1_1117_, lean_object* v_h__2_1118_, lean_object* v_h__3_1119_, lean_object* v_h__4_1120_, lean_object* v_h__5_1121_, lean_object* v_h__6_1122_, lean_object* v_h__7_1123_, lean_object* v_h__8_1124_, lean_object* v_h__9_1125_, lean_object* v_h__10_1126_, lean_object* v_h__11_1127_, lean_object* v_h__12_1128_, lean_object* v_h__13_1129_, lean_object* v_h__14_1130_, lean_object* v_h__15_1131_, lean_object* v_h__16_1132_){
_start:
{
switch(lean_obj_tag(v_x_1116_))
{
case 0:
{
lean_object* v___x_1133_; 
lean_dec(v_h__16_1132_);
lean_dec(v_h__15_1131_);
lean_dec(v_h__14_1130_);
lean_dec(v_h__13_1129_);
lean_dec(v_h__12_1128_);
lean_dec(v_h__11_1127_);
lean_dec(v_h__10_1126_);
lean_dec(v_h__9_1125_);
lean_dec(v_h__8_1124_);
lean_dec(v_h__7_1123_);
lean_dec(v_h__6_1122_);
lean_dec(v_h__5_1121_);
lean_dec(v_h__4_1120_);
lean_dec(v_h__3_1119_);
lean_dec(v_h__2_1118_);
v___x_1133_ = lean_apply_1(v_h__1_1117_, lean_box(0));
return v___x_1133_;
}
case 1:
{
lean_object* v_f_1134_; lean_object* v___x_1135_; 
lean_dec(v_h__16_1132_);
lean_dec(v_h__15_1131_);
lean_dec(v_h__14_1130_);
lean_dec(v_h__13_1129_);
lean_dec(v_h__12_1128_);
lean_dec(v_h__11_1127_);
lean_dec(v_h__10_1126_);
lean_dec(v_h__9_1125_);
lean_dec(v_h__8_1124_);
lean_dec(v_h__7_1123_);
lean_dec(v_h__6_1122_);
lean_dec(v_h__5_1121_);
lean_dec(v_h__4_1120_);
lean_dec(v_h__3_1119_);
lean_dec(v_h__1_1117_);
v_f_1134_ = lean_ctor_get(v_x_1116_, 0);
lean_inc_ref(v_f_1134_);
lean_dec_ref_known(v_x_1116_, 1);
v___x_1135_ = lean_apply_2(v_h__2_1118_, lean_box(0), v_f_1134_);
return v___x_1135_;
}
case 2:
{
lean_object* v_s_1136_; lean_object* v___x_1137_; 
lean_dec(v_h__16_1132_);
lean_dec(v_h__15_1131_);
lean_dec(v_h__14_1130_);
lean_dec(v_h__13_1129_);
lean_dec(v_h__12_1128_);
lean_dec(v_h__11_1127_);
lean_dec(v_h__10_1126_);
lean_dec(v_h__9_1125_);
lean_dec(v_h__8_1124_);
lean_dec(v_h__7_1123_);
lean_dec(v_h__6_1122_);
lean_dec(v_h__5_1121_);
lean_dec(v_h__4_1120_);
lean_dec(v_h__2_1118_);
lean_dec(v_h__1_1117_);
v_s_1136_ = lean_ctor_get(v_x_1116_, 0);
lean_inc_ref(v_s_1136_);
lean_dec_ref_known(v_x_1116_, 1);
v___x_1137_ = lean_apply_2(v_h__3_1119_, lean_box(0), v_s_1136_);
return v___x_1137_;
}
case 3:
{
lean_object* v_id_1138_; lean_object* v_d_1139_; lean_object* v___x_1140_; 
lean_dec(v_h__16_1132_);
lean_dec(v_h__15_1131_);
lean_dec(v_h__14_1130_);
lean_dec(v_h__13_1129_);
lean_dec(v_h__12_1128_);
lean_dec(v_h__11_1127_);
lean_dec(v_h__10_1126_);
lean_dec(v_h__9_1125_);
lean_dec(v_h__8_1124_);
lean_dec(v_h__7_1123_);
lean_dec(v_h__6_1122_);
lean_dec(v_h__4_1120_);
lean_dec(v_h__3_1119_);
lean_dec(v_h__2_1118_);
lean_dec(v_h__1_1117_);
v_id_1138_ = lean_ctor_get(v_x_1116_, 0);
lean_inc(v_id_1138_);
v_d_1139_ = lean_ctor_get(v_x_1116_, 1);
lean_inc(v_d_1139_);
lean_dec_ref_known(v_x_1116_, 2);
v___x_1140_ = lean_apply_3(v_h__5_1121_, lean_box(0), v_id_1138_, v_d_1139_);
return v___x_1140_;
}
case 4:
{
lean_object* v_d_1141_; lean_object* v___x_1142_; 
lean_dec(v_h__16_1132_);
lean_dec(v_h__15_1131_);
lean_dec(v_h__14_1130_);
lean_dec(v_h__13_1129_);
lean_dec(v_h__12_1128_);
lean_dec(v_h__11_1127_);
lean_dec(v_h__10_1126_);
lean_dec(v_h__9_1125_);
lean_dec(v_h__8_1124_);
lean_dec(v_h__7_1123_);
lean_dec(v_h__6_1122_);
lean_dec(v_h__5_1121_);
lean_dec(v_h__3_1119_);
lean_dec(v_h__2_1118_);
lean_dec(v_h__1_1117_);
v_d_1141_ = lean_ctor_get(v_x_1116_, 0);
lean_inc(v_d_1141_);
lean_dec_ref_known(v_x_1116_, 1);
v___x_1142_ = lean_apply_2(v_h__4_1120_, lean_box(0), v_d_1141_);
return v___x_1142_;
}
case 5:
{
lean_object* v_d_1143_; lean_object* v___x_1144_; 
lean_dec(v_h__16_1132_);
lean_dec(v_h__15_1131_);
lean_dec(v_h__14_1130_);
lean_dec(v_h__13_1129_);
lean_dec(v_h__11_1127_);
lean_dec(v_h__10_1126_);
lean_dec(v_h__9_1125_);
lean_dec(v_h__8_1124_);
lean_dec(v_h__7_1123_);
lean_dec(v_h__6_1122_);
lean_dec(v_h__5_1121_);
lean_dec(v_h__4_1120_);
lean_dec(v_h__3_1119_);
lean_dec(v_h__2_1118_);
lean_dec(v_h__1_1117_);
v_d_1143_ = lean_ctor_get(v_x_1116_, 0);
lean_inc(v_d_1143_);
lean_dec_ref_known(v_x_1116_, 1);
v___x_1144_ = lean_apply_2(v_h__12_1128_, lean_box(0), v_d_1143_);
return v___x_1144_;
}
case 6:
{
lean_object* v_n_1145_; uint8_t v_isCumulative_1146_; lean_object* v_d_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; 
lean_dec(v_h__16_1132_);
lean_dec(v_h__15_1131_);
lean_dec(v_h__14_1130_);
lean_dec(v_h__13_1129_);
lean_dec(v_h__12_1128_);
lean_dec(v_h__11_1127_);
lean_dec(v_h__10_1126_);
lean_dec(v_h__9_1125_);
lean_dec(v_h__8_1124_);
lean_dec(v_h__7_1123_);
lean_dec(v_h__5_1121_);
lean_dec(v_h__4_1120_);
lean_dec(v_h__3_1119_);
lean_dec(v_h__2_1118_);
lean_dec(v_h__1_1117_);
v_n_1145_ = lean_ctor_get(v_x_1116_, 0);
lean_inc(v_n_1145_);
v_isCumulative_1146_ = lean_ctor_get_uint8(v_x_1116_, sizeof(void*)*2);
v_d_1147_ = lean_ctor_get(v_x_1116_, 1);
lean_inc(v_d_1147_);
lean_dec_ref_known(v_x_1116_, 2);
v___x_1148_ = lean_box(v_isCumulative_1146_);
v___x_1149_ = lean_apply_4(v_h__6_1122_, lean_box(0), v_n_1145_, v___x_1148_, v_d_1147_);
return v___x_1149_;
}
case 7:
{
lean_object* v_d_1150_; lean_object* v___x_1151_; 
lean_dec(v_h__16_1132_);
lean_dec(v_h__15_1131_);
lean_dec(v_h__14_1130_);
lean_dec(v_h__13_1129_);
lean_dec(v_h__12_1128_);
lean_dec(v_h__11_1127_);
lean_dec(v_h__10_1126_);
lean_dec(v_h__9_1125_);
lean_dec(v_h__8_1124_);
lean_dec(v_h__6_1122_);
lean_dec(v_h__5_1121_);
lean_dec(v_h__4_1120_);
lean_dec(v_h__3_1119_);
lean_dec(v_h__2_1118_);
lean_dec(v_h__1_1117_);
v_d_1150_ = lean_ctor_get(v_x_1116_, 0);
lean_inc(v_d_1150_);
lean_dec_ref_known(v_x_1116_, 1);
v___x_1151_ = lean_apply_2(v_h__7_1123_, lean_box(0), v_d_1150_);
return v___x_1151_;
}
case 8:
{
uint8_t v_onlyNonCumulative_1152_; lean_object* v_d_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
lean_dec(v_h__16_1132_);
lean_dec(v_h__15_1131_);
lean_dec(v_h__14_1130_);
lean_dec(v_h__13_1129_);
lean_dec(v_h__12_1128_);
lean_dec(v_h__11_1127_);
lean_dec(v_h__10_1126_);
lean_dec(v_h__9_1125_);
lean_dec(v_h__7_1123_);
lean_dec(v_h__6_1122_);
lean_dec(v_h__5_1121_);
lean_dec(v_h__4_1120_);
lean_dec(v_h__3_1119_);
lean_dec(v_h__2_1118_);
lean_dec(v_h__1_1117_);
v_onlyNonCumulative_1152_ = lean_ctor_get_uint8(v_x_1116_, sizeof(void*)*1);
v_d_1153_ = lean_ctor_get(v_x_1116_, 0);
lean_inc(v_d_1153_);
lean_dec_ref_known(v_x_1116_, 1);
v___x_1154_ = lean_box(v_onlyNonCumulative_1152_);
v___x_1155_ = lean_apply_3(v_h__8_1124_, lean_box(0), v___x_1154_, v_d_1153_);
return v___x_1155_;
}
case 9:
{
lean_object* v_d_1156_; lean_object* v___x_1157_; 
lean_dec(v_h__16_1132_);
lean_dec(v_h__15_1131_);
lean_dec(v_h__14_1130_);
lean_dec(v_h__13_1129_);
lean_dec(v_h__12_1128_);
lean_dec(v_h__11_1127_);
lean_dec(v_h__10_1126_);
lean_dec(v_h__8_1124_);
lean_dec(v_h__7_1123_);
lean_dec(v_h__6_1122_);
lean_dec(v_h__5_1121_);
lean_dec(v_h__4_1120_);
lean_dec(v_h__3_1119_);
lean_dec(v_h__2_1118_);
lean_dec(v_h__1_1117_);
v_d_1156_ = lean_ctor_get(v_x_1116_, 0);
lean_inc(v_d_1156_);
lean_dec_ref_known(v_x_1116_, 1);
v___x_1157_ = lean_apply_2(v_h__9_1125_, lean_box(0), v_d_1156_);
return v___x_1157_;
}
case 10:
{
lean_object* v_d_1158_; lean_object* v___x_1159_; 
lean_dec(v_h__16_1132_);
lean_dec(v_h__15_1131_);
lean_dec(v_h__14_1130_);
lean_dec(v_h__13_1129_);
lean_dec(v_h__12_1128_);
lean_dec(v_h__11_1127_);
lean_dec(v_h__9_1125_);
lean_dec(v_h__8_1124_);
lean_dec(v_h__7_1123_);
lean_dec(v_h__6_1122_);
lean_dec(v_h__5_1121_);
lean_dec(v_h__4_1120_);
lean_dec(v_h__3_1119_);
lean_dec(v_h__2_1118_);
lean_dec(v_h__1_1117_);
v_d_1158_ = lean_ctor_get(v_x_1116_, 0);
lean_inc(v_d_1158_);
lean_dec_ref_known(v_x_1116_, 1);
v___x_1159_ = lean_apply_2(v_h__10_1126_, lean_box(0), v_d_1158_);
return v___x_1159_;
}
case 11:
{
lean_object* v_d_1160_; lean_object* v___x_1161_; 
lean_dec(v_h__16_1132_);
lean_dec(v_h__15_1131_);
lean_dec(v_h__14_1130_);
lean_dec(v_h__13_1129_);
lean_dec(v_h__12_1128_);
lean_dec(v_h__10_1126_);
lean_dec(v_h__9_1125_);
lean_dec(v_h__8_1124_);
lean_dec(v_h__7_1123_);
lean_dec(v_h__6_1122_);
lean_dec(v_h__5_1121_);
lean_dec(v_h__4_1120_);
lean_dec(v_h__3_1119_);
lean_dec(v_h__2_1118_);
lean_dec(v_h__1_1117_);
v_d_1160_ = lean_ctor_get(v_x_1116_, 0);
lean_inc(v_d_1160_);
lean_dec_ref_known(v_x_1116_, 1);
v___x_1161_ = lean_apply_2(v_h__11_1127_, lean_box(0), v_d_1160_);
return v___x_1161_;
}
case 12:
{
lean_object* v_p_1162_; lean_object* v_d_1163_; lean_object* v___x_1164_; 
lean_dec(v_h__16_1132_);
lean_dec(v_h__15_1131_);
lean_dec(v_h__14_1130_);
lean_dec(v_h__12_1128_);
lean_dec(v_h__11_1127_);
lean_dec(v_h__10_1126_);
lean_dec(v_h__9_1125_);
lean_dec(v_h__8_1124_);
lean_dec(v_h__7_1123_);
lean_dec(v_h__6_1122_);
lean_dec(v_h__5_1121_);
lean_dec(v_h__4_1120_);
lean_dec(v_h__3_1119_);
lean_dec(v_h__2_1118_);
lean_dec(v_h__1_1117_);
v_p_1162_ = lean_ctor_get(v_x_1116_, 0);
lean_inc_ref(v_p_1162_);
v_d_1163_ = lean_ctor_get(v_x_1116_, 1);
lean_inc(v_d_1163_);
lean_dec_ref_known(v_x_1116_, 2);
v___x_1164_ = lean_apply_3(v_h__13_1129_, lean_box(0), v_p_1162_, v_d_1163_);
return v___x_1164_;
}
case 13:
{
lean_object* v_cost_1165_; lean_object* v_d_1166_; lean_object* v___x_1167_; 
lean_dec(v_h__16_1132_);
lean_dec(v_h__15_1131_);
lean_dec(v_h__13_1129_);
lean_dec(v_h__12_1128_);
lean_dec(v_h__11_1127_);
lean_dec(v_h__10_1126_);
lean_dec(v_h__9_1125_);
lean_dec(v_h__8_1124_);
lean_dec(v_h__7_1123_);
lean_dec(v_h__6_1122_);
lean_dec(v_h__5_1121_);
lean_dec(v_h__4_1120_);
lean_dec(v_h__3_1119_);
lean_dec(v_h__2_1118_);
lean_dec(v_h__1_1117_);
v_cost_1165_ = lean_ctor_get(v_x_1116_, 0);
lean_inc(v_cost_1165_);
v_d_1166_ = lean_ctor_get(v_x_1116_, 1);
lean_inc(v_d_1166_);
lean_dec_ref_known(v_x_1116_, 2);
v___x_1167_ = lean_apply_3(v_h__14_1130_, lean_box(0), v_cost_1165_, v_d_1166_);
return v___x_1167_;
}
case 14:
{
lean_object* v_a_1168_; lean_object* v_b_1169_; lean_object* v___x_1170_; 
lean_dec(v_h__16_1132_);
lean_dec(v_h__14_1130_);
lean_dec(v_h__13_1129_);
lean_dec(v_h__12_1128_);
lean_dec(v_h__11_1127_);
lean_dec(v_h__10_1126_);
lean_dec(v_h__9_1125_);
lean_dec(v_h__8_1124_);
lean_dec(v_h__7_1123_);
lean_dec(v_h__6_1122_);
lean_dec(v_h__5_1121_);
lean_dec(v_h__4_1120_);
lean_dec(v_h__3_1119_);
lean_dec(v_h__2_1118_);
lean_dec(v_h__1_1117_);
v_a_1168_ = lean_ctor_get(v_x_1116_, 0);
lean_inc(v_a_1168_);
v_b_1169_ = lean_ctor_get(v_x_1116_, 1);
lean_inc(v_b_1169_);
lean_dec_ref_known(v_x_1116_, 2);
v___x_1170_ = lean_apply_3(v_h__15_1131_, lean_box(0), v_a_1168_, v_b_1169_);
return v___x_1170_;
}
default: 
{
lean_object* v_a_1171_; lean_object* v_b_1172_; lean_object* v___x_1173_; 
lean_dec(v_h__15_1131_);
lean_dec(v_h__14_1130_);
lean_dec(v_h__13_1129_);
lean_dec(v_h__12_1128_);
lean_dec(v_h__11_1127_);
lean_dec(v_h__10_1126_);
lean_dec(v_h__9_1125_);
lean_dec(v_h__8_1124_);
lean_dec(v_h__7_1123_);
lean_dec(v_h__6_1122_);
lean_dec(v_h__5_1121_);
lean_dec(v_h__4_1120_);
lean_dec(v_h__3_1119_);
lean_dec(v_h__2_1118_);
lean_dec(v_h__1_1117_);
v_a_1171_ = lean_ctor_get(v_x_1116_, 0);
lean_inc(v_a_1171_);
v_b_1172_ = lean_ctor_get(v_x_1116_, 1);
lean_inc(v_b_1172_);
lean_dec_ref_known(v_x_1116_, 2);
v___x_1173_ = lean_apply_3(v_h__16_1132_, lean_box(0), v_a_1171_, v_b_1172_);
return v___x_1173_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_maxNewlineCount_x3f_match__1_splitter___redArg___boxed(lean_object** _args){
lean_object* v_x_1174_ = _args[0];
lean_object* v_h__1_1175_ = _args[1];
lean_object* v_h__2_1176_ = _args[2];
lean_object* v_h__3_1177_ = _args[3];
lean_object* v_h__4_1178_ = _args[4];
lean_object* v_h__5_1179_ = _args[5];
lean_object* v_h__6_1180_ = _args[6];
lean_object* v_h__7_1181_ = _args[7];
lean_object* v_h__8_1182_ = _args[8];
lean_object* v_h__9_1183_ = _args[9];
lean_object* v_h__10_1184_ = _args[10];
lean_object* v_h__11_1185_ = _args[11];
lean_object* v_h__12_1186_ = _args[12];
lean_object* v_h__13_1187_ = _args[13];
lean_object* v_h__14_1188_ = _args[14];
lean_object* v_h__15_1189_ = _args[15];
lean_object* v_h__16_1190_ = _args[16];
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_maxNewlineCount_x3f_match__1_splitter___redArg(v_x_1174_, v_h__1_1175_, v_h__2_1176_, v_h__3_1177_, v_h__4_1178_, v_h__5_1179_, v_h__6_1180_, v_h__7_1181_, v_h__8_1182_, v_h__9_1183_, v_h__10_1184_, v_h__11_1185_, v_h__12_1186_, v_h__13_1187_, v_h__14_1188_, v_h__15_1189_, v_h__16_1190_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_maxNewlineCount_x3f_match__1_splitter(lean_object* v_motive_1192_, lean_object* v_x_1193_, lean_object* v_x_1194_, lean_object* v_h__1_1195_, lean_object* v_h__2_1196_, lean_object* v_h__3_1197_, lean_object* v_h__4_1198_, lean_object* v_h__5_1199_, lean_object* v_h__6_1200_, lean_object* v_h__7_1201_, lean_object* v_h__8_1202_, lean_object* v_h__9_1203_, lean_object* v_h__10_1204_, lean_object* v_h__11_1205_, lean_object* v_h__12_1206_, lean_object* v_h__13_1207_, lean_object* v_h__14_1208_, lean_object* v_h__15_1209_, lean_object* v_h__16_1210_){
_start:
{
switch(lean_obj_tag(v_x_1194_))
{
case 0:
{
lean_object* v___x_1211_; 
lean_dec(v_h__16_1210_);
lean_dec(v_h__15_1209_);
lean_dec(v_h__14_1208_);
lean_dec(v_h__13_1207_);
lean_dec(v_h__12_1206_);
lean_dec(v_h__11_1205_);
lean_dec(v_h__10_1204_);
lean_dec(v_h__9_1203_);
lean_dec(v_h__8_1202_);
lean_dec(v_h__7_1201_);
lean_dec(v_h__6_1200_);
lean_dec(v_h__5_1199_);
lean_dec(v_h__4_1198_);
lean_dec(v_h__3_1197_);
lean_dec(v_h__2_1196_);
v___x_1211_ = lean_apply_1(v_h__1_1195_, lean_box(0));
return v___x_1211_;
}
case 1:
{
lean_object* v_f_1212_; lean_object* v___x_1213_; 
lean_dec(v_h__16_1210_);
lean_dec(v_h__15_1209_);
lean_dec(v_h__14_1208_);
lean_dec(v_h__13_1207_);
lean_dec(v_h__12_1206_);
lean_dec(v_h__11_1205_);
lean_dec(v_h__10_1204_);
lean_dec(v_h__9_1203_);
lean_dec(v_h__8_1202_);
lean_dec(v_h__7_1201_);
lean_dec(v_h__6_1200_);
lean_dec(v_h__5_1199_);
lean_dec(v_h__4_1198_);
lean_dec(v_h__3_1197_);
lean_dec(v_h__1_1195_);
v_f_1212_ = lean_ctor_get(v_x_1194_, 0);
lean_inc_ref(v_f_1212_);
lean_dec_ref_known(v_x_1194_, 1);
v___x_1213_ = lean_apply_2(v_h__2_1196_, lean_box(0), v_f_1212_);
return v___x_1213_;
}
case 2:
{
lean_object* v_s_1214_; lean_object* v___x_1215_; 
lean_dec(v_h__16_1210_);
lean_dec(v_h__15_1209_);
lean_dec(v_h__14_1208_);
lean_dec(v_h__13_1207_);
lean_dec(v_h__12_1206_);
lean_dec(v_h__11_1205_);
lean_dec(v_h__10_1204_);
lean_dec(v_h__9_1203_);
lean_dec(v_h__8_1202_);
lean_dec(v_h__7_1201_);
lean_dec(v_h__6_1200_);
lean_dec(v_h__5_1199_);
lean_dec(v_h__4_1198_);
lean_dec(v_h__2_1196_);
lean_dec(v_h__1_1195_);
v_s_1214_ = lean_ctor_get(v_x_1194_, 0);
lean_inc_ref(v_s_1214_);
lean_dec_ref_known(v_x_1194_, 1);
v___x_1215_ = lean_apply_2(v_h__3_1197_, lean_box(0), v_s_1214_);
return v___x_1215_;
}
case 3:
{
lean_object* v_id_1216_; lean_object* v_d_1217_; lean_object* v___x_1218_; 
lean_dec(v_h__16_1210_);
lean_dec(v_h__15_1209_);
lean_dec(v_h__14_1208_);
lean_dec(v_h__13_1207_);
lean_dec(v_h__12_1206_);
lean_dec(v_h__11_1205_);
lean_dec(v_h__10_1204_);
lean_dec(v_h__9_1203_);
lean_dec(v_h__8_1202_);
lean_dec(v_h__7_1201_);
lean_dec(v_h__6_1200_);
lean_dec(v_h__4_1198_);
lean_dec(v_h__3_1197_);
lean_dec(v_h__2_1196_);
lean_dec(v_h__1_1195_);
v_id_1216_ = lean_ctor_get(v_x_1194_, 0);
lean_inc(v_id_1216_);
v_d_1217_ = lean_ctor_get(v_x_1194_, 1);
lean_inc(v_d_1217_);
lean_dec_ref_known(v_x_1194_, 2);
v___x_1218_ = lean_apply_3(v_h__5_1199_, lean_box(0), v_id_1216_, v_d_1217_);
return v___x_1218_;
}
case 4:
{
lean_object* v_d_1219_; lean_object* v___x_1220_; 
lean_dec(v_h__16_1210_);
lean_dec(v_h__15_1209_);
lean_dec(v_h__14_1208_);
lean_dec(v_h__13_1207_);
lean_dec(v_h__12_1206_);
lean_dec(v_h__11_1205_);
lean_dec(v_h__10_1204_);
lean_dec(v_h__9_1203_);
lean_dec(v_h__8_1202_);
lean_dec(v_h__7_1201_);
lean_dec(v_h__6_1200_);
lean_dec(v_h__5_1199_);
lean_dec(v_h__3_1197_);
lean_dec(v_h__2_1196_);
lean_dec(v_h__1_1195_);
v_d_1219_ = lean_ctor_get(v_x_1194_, 0);
lean_inc(v_d_1219_);
lean_dec_ref_known(v_x_1194_, 1);
v___x_1220_ = lean_apply_2(v_h__4_1198_, lean_box(0), v_d_1219_);
return v___x_1220_;
}
case 5:
{
lean_object* v_d_1221_; lean_object* v___x_1222_; 
lean_dec(v_h__16_1210_);
lean_dec(v_h__15_1209_);
lean_dec(v_h__14_1208_);
lean_dec(v_h__13_1207_);
lean_dec(v_h__11_1205_);
lean_dec(v_h__10_1204_);
lean_dec(v_h__9_1203_);
lean_dec(v_h__8_1202_);
lean_dec(v_h__7_1201_);
lean_dec(v_h__6_1200_);
lean_dec(v_h__5_1199_);
lean_dec(v_h__4_1198_);
lean_dec(v_h__3_1197_);
lean_dec(v_h__2_1196_);
lean_dec(v_h__1_1195_);
v_d_1221_ = lean_ctor_get(v_x_1194_, 0);
lean_inc(v_d_1221_);
lean_dec_ref_known(v_x_1194_, 1);
v___x_1222_ = lean_apply_2(v_h__12_1206_, lean_box(0), v_d_1221_);
return v___x_1222_;
}
case 6:
{
lean_object* v_n_1223_; uint8_t v_isCumulative_1224_; lean_object* v_d_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
lean_dec(v_h__16_1210_);
lean_dec(v_h__15_1209_);
lean_dec(v_h__14_1208_);
lean_dec(v_h__13_1207_);
lean_dec(v_h__12_1206_);
lean_dec(v_h__11_1205_);
lean_dec(v_h__10_1204_);
lean_dec(v_h__9_1203_);
lean_dec(v_h__8_1202_);
lean_dec(v_h__7_1201_);
lean_dec(v_h__5_1199_);
lean_dec(v_h__4_1198_);
lean_dec(v_h__3_1197_);
lean_dec(v_h__2_1196_);
lean_dec(v_h__1_1195_);
v_n_1223_ = lean_ctor_get(v_x_1194_, 0);
lean_inc(v_n_1223_);
v_isCumulative_1224_ = lean_ctor_get_uint8(v_x_1194_, sizeof(void*)*2);
v_d_1225_ = lean_ctor_get(v_x_1194_, 1);
lean_inc(v_d_1225_);
lean_dec_ref_known(v_x_1194_, 2);
v___x_1226_ = lean_box(v_isCumulative_1224_);
v___x_1227_ = lean_apply_4(v_h__6_1200_, lean_box(0), v_n_1223_, v___x_1226_, v_d_1225_);
return v___x_1227_;
}
case 7:
{
lean_object* v_d_1228_; lean_object* v___x_1229_; 
lean_dec(v_h__16_1210_);
lean_dec(v_h__15_1209_);
lean_dec(v_h__14_1208_);
lean_dec(v_h__13_1207_);
lean_dec(v_h__12_1206_);
lean_dec(v_h__11_1205_);
lean_dec(v_h__10_1204_);
lean_dec(v_h__9_1203_);
lean_dec(v_h__8_1202_);
lean_dec(v_h__6_1200_);
lean_dec(v_h__5_1199_);
lean_dec(v_h__4_1198_);
lean_dec(v_h__3_1197_);
lean_dec(v_h__2_1196_);
lean_dec(v_h__1_1195_);
v_d_1228_ = lean_ctor_get(v_x_1194_, 0);
lean_inc(v_d_1228_);
lean_dec_ref_known(v_x_1194_, 1);
v___x_1229_ = lean_apply_2(v_h__7_1201_, lean_box(0), v_d_1228_);
return v___x_1229_;
}
case 8:
{
uint8_t v_onlyNonCumulative_1230_; lean_object* v_d_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
lean_dec(v_h__16_1210_);
lean_dec(v_h__15_1209_);
lean_dec(v_h__14_1208_);
lean_dec(v_h__13_1207_);
lean_dec(v_h__12_1206_);
lean_dec(v_h__11_1205_);
lean_dec(v_h__10_1204_);
lean_dec(v_h__9_1203_);
lean_dec(v_h__7_1201_);
lean_dec(v_h__6_1200_);
lean_dec(v_h__5_1199_);
lean_dec(v_h__4_1198_);
lean_dec(v_h__3_1197_);
lean_dec(v_h__2_1196_);
lean_dec(v_h__1_1195_);
v_onlyNonCumulative_1230_ = lean_ctor_get_uint8(v_x_1194_, sizeof(void*)*1);
v_d_1231_ = lean_ctor_get(v_x_1194_, 0);
lean_inc(v_d_1231_);
lean_dec_ref_known(v_x_1194_, 1);
v___x_1232_ = lean_box(v_onlyNonCumulative_1230_);
v___x_1233_ = lean_apply_3(v_h__8_1202_, lean_box(0), v___x_1232_, v_d_1231_);
return v___x_1233_;
}
case 9:
{
lean_object* v_d_1234_; lean_object* v___x_1235_; 
lean_dec(v_h__16_1210_);
lean_dec(v_h__15_1209_);
lean_dec(v_h__14_1208_);
lean_dec(v_h__13_1207_);
lean_dec(v_h__12_1206_);
lean_dec(v_h__11_1205_);
lean_dec(v_h__10_1204_);
lean_dec(v_h__8_1202_);
lean_dec(v_h__7_1201_);
lean_dec(v_h__6_1200_);
lean_dec(v_h__5_1199_);
lean_dec(v_h__4_1198_);
lean_dec(v_h__3_1197_);
lean_dec(v_h__2_1196_);
lean_dec(v_h__1_1195_);
v_d_1234_ = lean_ctor_get(v_x_1194_, 0);
lean_inc(v_d_1234_);
lean_dec_ref_known(v_x_1194_, 1);
v___x_1235_ = lean_apply_2(v_h__9_1203_, lean_box(0), v_d_1234_);
return v___x_1235_;
}
case 10:
{
lean_object* v_d_1236_; lean_object* v___x_1237_; 
lean_dec(v_h__16_1210_);
lean_dec(v_h__15_1209_);
lean_dec(v_h__14_1208_);
lean_dec(v_h__13_1207_);
lean_dec(v_h__12_1206_);
lean_dec(v_h__11_1205_);
lean_dec(v_h__9_1203_);
lean_dec(v_h__8_1202_);
lean_dec(v_h__7_1201_);
lean_dec(v_h__6_1200_);
lean_dec(v_h__5_1199_);
lean_dec(v_h__4_1198_);
lean_dec(v_h__3_1197_);
lean_dec(v_h__2_1196_);
lean_dec(v_h__1_1195_);
v_d_1236_ = lean_ctor_get(v_x_1194_, 0);
lean_inc(v_d_1236_);
lean_dec_ref_known(v_x_1194_, 1);
v___x_1237_ = lean_apply_2(v_h__10_1204_, lean_box(0), v_d_1236_);
return v___x_1237_;
}
case 11:
{
lean_object* v_d_1238_; lean_object* v___x_1239_; 
lean_dec(v_h__16_1210_);
lean_dec(v_h__15_1209_);
lean_dec(v_h__14_1208_);
lean_dec(v_h__13_1207_);
lean_dec(v_h__12_1206_);
lean_dec(v_h__10_1204_);
lean_dec(v_h__9_1203_);
lean_dec(v_h__8_1202_);
lean_dec(v_h__7_1201_);
lean_dec(v_h__6_1200_);
lean_dec(v_h__5_1199_);
lean_dec(v_h__4_1198_);
lean_dec(v_h__3_1197_);
lean_dec(v_h__2_1196_);
lean_dec(v_h__1_1195_);
v_d_1238_ = lean_ctor_get(v_x_1194_, 0);
lean_inc(v_d_1238_);
lean_dec_ref_known(v_x_1194_, 1);
v___x_1239_ = lean_apply_2(v_h__11_1205_, lean_box(0), v_d_1238_);
return v___x_1239_;
}
case 12:
{
lean_object* v_p_1240_; lean_object* v_d_1241_; lean_object* v___x_1242_; 
lean_dec(v_h__16_1210_);
lean_dec(v_h__15_1209_);
lean_dec(v_h__14_1208_);
lean_dec(v_h__12_1206_);
lean_dec(v_h__11_1205_);
lean_dec(v_h__10_1204_);
lean_dec(v_h__9_1203_);
lean_dec(v_h__8_1202_);
lean_dec(v_h__7_1201_);
lean_dec(v_h__6_1200_);
lean_dec(v_h__5_1199_);
lean_dec(v_h__4_1198_);
lean_dec(v_h__3_1197_);
lean_dec(v_h__2_1196_);
lean_dec(v_h__1_1195_);
v_p_1240_ = lean_ctor_get(v_x_1194_, 0);
lean_inc_ref(v_p_1240_);
v_d_1241_ = lean_ctor_get(v_x_1194_, 1);
lean_inc(v_d_1241_);
lean_dec_ref_known(v_x_1194_, 2);
v___x_1242_ = lean_apply_3(v_h__13_1207_, lean_box(0), v_p_1240_, v_d_1241_);
return v___x_1242_;
}
case 13:
{
lean_object* v_cost_1243_; lean_object* v_d_1244_; lean_object* v___x_1245_; 
lean_dec(v_h__16_1210_);
lean_dec(v_h__15_1209_);
lean_dec(v_h__13_1207_);
lean_dec(v_h__12_1206_);
lean_dec(v_h__11_1205_);
lean_dec(v_h__10_1204_);
lean_dec(v_h__9_1203_);
lean_dec(v_h__8_1202_);
lean_dec(v_h__7_1201_);
lean_dec(v_h__6_1200_);
lean_dec(v_h__5_1199_);
lean_dec(v_h__4_1198_);
lean_dec(v_h__3_1197_);
lean_dec(v_h__2_1196_);
lean_dec(v_h__1_1195_);
v_cost_1243_ = lean_ctor_get(v_x_1194_, 0);
lean_inc(v_cost_1243_);
v_d_1244_ = lean_ctor_get(v_x_1194_, 1);
lean_inc(v_d_1244_);
lean_dec_ref_known(v_x_1194_, 2);
v___x_1245_ = lean_apply_3(v_h__14_1208_, lean_box(0), v_cost_1243_, v_d_1244_);
return v___x_1245_;
}
case 14:
{
lean_object* v_a_1246_; lean_object* v_b_1247_; lean_object* v___x_1248_; 
lean_dec(v_h__16_1210_);
lean_dec(v_h__14_1208_);
lean_dec(v_h__13_1207_);
lean_dec(v_h__12_1206_);
lean_dec(v_h__11_1205_);
lean_dec(v_h__10_1204_);
lean_dec(v_h__9_1203_);
lean_dec(v_h__8_1202_);
lean_dec(v_h__7_1201_);
lean_dec(v_h__6_1200_);
lean_dec(v_h__5_1199_);
lean_dec(v_h__4_1198_);
lean_dec(v_h__3_1197_);
lean_dec(v_h__2_1196_);
lean_dec(v_h__1_1195_);
v_a_1246_ = lean_ctor_get(v_x_1194_, 0);
lean_inc(v_a_1246_);
v_b_1247_ = lean_ctor_get(v_x_1194_, 1);
lean_inc(v_b_1247_);
lean_dec_ref_known(v_x_1194_, 2);
v___x_1248_ = lean_apply_3(v_h__15_1209_, lean_box(0), v_a_1246_, v_b_1247_);
return v___x_1248_;
}
default: 
{
lean_object* v_a_1249_; lean_object* v_b_1250_; lean_object* v___x_1251_; 
lean_dec(v_h__15_1209_);
lean_dec(v_h__14_1208_);
lean_dec(v_h__13_1207_);
lean_dec(v_h__12_1206_);
lean_dec(v_h__11_1205_);
lean_dec(v_h__10_1204_);
lean_dec(v_h__9_1203_);
lean_dec(v_h__8_1202_);
lean_dec(v_h__7_1201_);
lean_dec(v_h__6_1200_);
lean_dec(v_h__5_1199_);
lean_dec(v_h__4_1198_);
lean_dec(v_h__3_1197_);
lean_dec(v_h__2_1196_);
lean_dec(v_h__1_1195_);
v_a_1249_ = lean_ctor_get(v_x_1194_, 0);
lean_inc(v_a_1249_);
v_b_1250_ = lean_ctor_get(v_x_1194_, 1);
lean_inc(v_b_1250_);
lean_dec_ref_known(v_x_1194_, 2);
v___x_1251_ = lean_apply_3(v_h__16_1210_, lean_box(0), v_a_1249_, v_b_1250_);
return v___x_1251_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_maxNewlineCount_x3f_match__1_splitter___boxed(lean_object** _args){
lean_object* v_motive_1252_ = _args[0];
lean_object* v_x_1253_ = _args[1];
lean_object* v_x_1254_ = _args[2];
lean_object* v_h__1_1255_ = _args[3];
lean_object* v_h__2_1256_ = _args[4];
lean_object* v_h__3_1257_ = _args[5];
lean_object* v_h__4_1258_ = _args[6];
lean_object* v_h__5_1259_ = _args[7];
lean_object* v_h__6_1260_ = _args[8];
lean_object* v_h__7_1261_ = _args[9];
lean_object* v_h__8_1262_ = _args[10];
lean_object* v_h__9_1263_ = _args[11];
lean_object* v_h__10_1264_ = _args[12];
lean_object* v_h__11_1265_ = _args[13];
lean_object* v_h__12_1266_ = _args[14];
lean_object* v_h__13_1267_ = _args[15];
lean_object* v_h__14_1268_ = _args[16];
lean_object* v_h__15_1269_ = _args[17];
lean_object* v_h__16_1270_ = _args[18];
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_maxNewlineCount_x3f_match__1_splitter(v_motive_1252_, v_x_1253_, v_x_1254_, v_h__1_1255_, v_h__2_1256_, v_h__3_1257_, v_h__4_1258_, v_h__5_1259_, v_h__6_1260_, v_h__7_1261_, v_h__8_1262_, v_h__9_1263_, v_h__10_1264_, v_h__11_1265_, v_h__12_1266_, v_h__13_1267_, v_h__14_1268_, v_h__15_1269_, v_h__16_1270_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__2_splitter___redArg(lean_object* v_x_1272_, lean_object* v_h__1_1273_, lean_object* v_h__2_1274_, lean_object* v_h__3_1275_, lean_object* v_h__4_1276_, lean_object* v_h__5_1277_, lean_object* v_h__6_1278_, lean_object* v_h__7_1279_, lean_object* v_h__8_1280_, lean_object* v_h__9_1281_, lean_object* v_h__10_1282_, lean_object* v_h__11_1283_, lean_object* v_h__12_1284_, lean_object* v_h__13_1285_, lean_object* v_h__14_1286_, lean_object* v_h__15_1287_, lean_object* v_h__16_1288_){
_start:
{
switch(lean_obj_tag(v_x_1272_))
{
case 0:
{
lean_object* v___x_1289_; 
lean_dec(v_h__16_1288_);
lean_dec(v_h__15_1287_);
lean_dec(v_h__14_1286_);
lean_dec(v_h__13_1285_);
lean_dec(v_h__12_1284_);
lean_dec(v_h__11_1283_);
lean_dec(v_h__10_1282_);
lean_dec(v_h__9_1281_);
lean_dec(v_h__8_1280_);
lean_dec(v_h__7_1279_);
lean_dec(v_h__6_1278_);
lean_dec(v_h__5_1277_);
lean_dec(v_h__4_1276_);
lean_dec(v_h__3_1275_);
lean_dec(v_h__2_1274_);
v___x_1289_ = lean_apply_1(v_h__1_1273_, lean_box(0));
return v___x_1289_;
}
case 1:
{
lean_object* v_f_1290_; lean_object* v___x_1291_; 
lean_dec(v_h__16_1288_);
lean_dec(v_h__15_1287_);
lean_dec(v_h__14_1286_);
lean_dec(v_h__13_1285_);
lean_dec(v_h__12_1284_);
lean_dec(v_h__11_1283_);
lean_dec(v_h__10_1282_);
lean_dec(v_h__9_1281_);
lean_dec(v_h__8_1280_);
lean_dec(v_h__7_1279_);
lean_dec(v_h__6_1278_);
lean_dec(v_h__5_1277_);
lean_dec(v_h__4_1276_);
lean_dec(v_h__3_1275_);
lean_dec(v_h__1_1273_);
v_f_1290_ = lean_ctor_get(v_x_1272_, 0);
lean_inc_ref(v_f_1290_);
lean_dec_ref_known(v_x_1272_, 1);
v___x_1291_ = lean_apply_2(v_h__2_1274_, lean_box(0), v_f_1290_);
return v___x_1291_;
}
case 2:
{
lean_object* v_s_1292_; lean_object* v___x_1293_; 
lean_dec(v_h__16_1288_);
lean_dec(v_h__15_1287_);
lean_dec(v_h__14_1286_);
lean_dec(v_h__13_1285_);
lean_dec(v_h__12_1284_);
lean_dec(v_h__11_1283_);
lean_dec(v_h__10_1282_);
lean_dec(v_h__9_1281_);
lean_dec(v_h__8_1280_);
lean_dec(v_h__7_1279_);
lean_dec(v_h__6_1278_);
lean_dec(v_h__5_1277_);
lean_dec(v_h__4_1276_);
lean_dec(v_h__2_1274_);
lean_dec(v_h__1_1273_);
v_s_1292_ = lean_ctor_get(v_x_1272_, 0);
lean_inc_ref(v_s_1292_);
lean_dec_ref_known(v_x_1272_, 1);
v___x_1293_ = lean_apply_2(v_h__3_1275_, lean_box(0), v_s_1292_);
return v___x_1293_;
}
case 3:
{
lean_object* v_id_1294_; lean_object* v_d_1295_; lean_object* v___x_1296_; 
lean_dec(v_h__16_1288_);
lean_dec(v_h__15_1287_);
lean_dec(v_h__14_1286_);
lean_dec(v_h__13_1285_);
lean_dec(v_h__12_1284_);
lean_dec(v_h__11_1283_);
lean_dec(v_h__10_1282_);
lean_dec(v_h__9_1281_);
lean_dec(v_h__8_1280_);
lean_dec(v_h__7_1279_);
lean_dec(v_h__5_1277_);
lean_dec(v_h__4_1276_);
lean_dec(v_h__3_1275_);
lean_dec(v_h__2_1274_);
lean_dec(v_h__1_1273_);
v_id_1294_ = lean_ctor_get(v_x_1272_, 0);
lean_inc(v_id_1294_);
v_d_1295_ = lean_ctor_get(v_x_1272_, 1);
lean_inc(v_d_1295_);
lean_dec_ref_known(v_x_1272_, 2);
v___x_1296_ = lean_apply_3(v_h__6_1278_, lean_box(0), v_id_1294_, v_d_1295_);
return v___x_1296_;
}
case 4:
{
lean_object* v_d_1297_; lean_object* v___x_1298_; 
lean_dec(v_h__16_1288_);
lean_dec(v_h__15_1287_);
lean_dec(v_h__14_1286_);
lean_dec(v_h__13_1285_);
lean_dec(v_h__12_1284_);
lean_dec(v_h__11_1283_);
lean_dec(v_h__10_1282_);
lean_dec(v_h__9_1281_);
lean_dec(v_h__8_1280_);
lean_dec(v_h__7_1279_);
lean_dec(v_h__6_1278_);
lean_dec(v_h__5_1277_);
lean_dec(v_h__3_1275_);
lean_dec(v_h__2_1274_);
lean_dec(v_h__1_1273_);
v_d_1297_ = lean_ctor_get(v_x_1272_, 0);
lean_inc(v_d_1297_);
lean_dec_ref_known(v_x_1272_, 1);
v___x_1298_ = lean_apply_2(v_h__4_1276_, lean_box(0), v_d_1297_);
return v___x_1298_;
}
case 5:
{
lean_object* v_d_1299_; lean_object* v___x_1300_; 
lean_dec(v_h__16_1288_);
lean_dec(v_h__15_1287_);
lean_dec(v_h__14_1286_);
lean_dec(v_h__13_1285_);
lean_dec(v_h__12_1284_);
lean_dec(v_h__11_1283_);
lean_dec(v_h__10_1282_);
lean_dec(v_h__9_1281_);
lean_dec(v_h__8_1280_);
lean_dec(v_h__7_1279_);
lean_dec(v_h__6_1278_);
lean_dec(v_h__4_1276_);
lean_dec(v_h__3_1275_);
lean_dec(v_h__2_1274_);
lean_dec(v_h__1_1273_);
v_d_1299_ = lean_ctor_get(v_x_1272_, 0);
lean_inc(v_d_1299_);
lean_dec_ref_known(v_x_1272_, 1);
v___x_1300_ = lean_apply_2(v_h__5_1277_, lean_box(0), v_d_1299_);
return v___x_1300_;
}
case 6:
{
lean_object* v_n_1301_; uint8_t v_isCumulative_1302_; lean_object* v_d_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
lean_dec(v_h__16_1288_);
lean_dec(v_h__15_1287_);
lean_dec(v_h__14_1286_);
lean_dec(v_h__13_1285_);
lean_dec(v_h__12_1284_);
lean_dec(v_h__11_1283_);
lean_dec(v_h__10_1282_);
lean_dec(v_h__9_1281_);
lean_dec(v_h__8_1280_);
lean_dec(v_h__6_1278_);
lean_dec(v_h__5_1277_);
lean_dec(v_h__4_1276_);
lean_dec(v_h__3_1275_);
lean_dec(v_h__2_1274_);
lean_dec(v_h__1_1273_);
v_n_1301_ = lean_ctor_get(v_x_1272_, 0);
lean_inc(v_n_1301_);
v_isCumulative_1302_ = lean_ctor_get_uint8(v_x_1272_, sizeof(void*)*2);
v_d_1303_ = lean_ctor_get(v_x_1272_, 1);
lean_inc(v_d_1303_);
lean_dec_ref_known(v_x_1272_, 2);
v___x_1304_ = lean_box(v_isCumulative_1302_);
v___x_1305_ = lean_apply_4(v_h__7_1279_, lean_box(0), v_n_1301_, v___x_1304_, v_d_1303_);
return v___x_1305_;
}
case 7:
{
lean_object* v_d_1306_; lean_object* v___x_1307_; 
lean_dec(v_h__16_1288_);
lean_dec(v_h__15_1287_);
lean_dec(v_h__14_1286_);
lean_dec(v_h__13_1285_);
lean_dec(v_h__12_1284_);
lean_dec(v_h__11_1283_);
lean_dec(v_h__10_1282_);
lean_dec(v_h__9_1281_);
lean_dec(v_h__7_1279_);
lean_dec(v_h__6_1278_);
lean_dec(v_h__5_1277_);
lean_dec(v_h__4_1276_);
lean_dec(v_h__3_1275_);
lean_dec(v_h__2_1274_);
lean_dec(v_h__1_1273_);
v_d_1306_ = lean_ctor_get(v_x_1272_, 0);
lean_inc(v_d_1306_);
lean_dec_ref_known(v_x_1272_, 1);
v___x_1307_ = lean_apply_2(v_h__8_1280_, lean_box(0), v_d_1306_);
return v___x_1307_;
}
case 8:
{
uint8_t v_onlyNonCumulative_1308_; lean_object* v_d_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
lean_dec(v_h__16_1288_);
lean_dec(v_h__15_1287_);
lean_dec(v_h__14_1286_);
lean_dec(v_h__13_1285_);
lean_dec(v_h__12_1284_);
lean_dec(v_h__11_1283_);
lean_dec(v_h__10_1282_);
lean_dec(v_h__8_1280_);
lean_dec(v_h__7_1279_);
lean_dec(v_h__6_1278_);
lean_dec(v_h__5_1277_);
lean_dec(v_h__4_1276_);
lean_dec(v_h__3_1275_);
lean_dec(v_h__2_1274_);
lean_dec(v_h__1_1273_);
v_onlyNonCumulative_1308_ = lean_ctor_get_uint8(v_x_1272_, sizeof(void*)*1);
v_d_1309_ = lean_ctor_get(v_x_1272_, 0);
lean_inc(v_d_1309_);
lean_dec_ref_known(v_x_1272_, 1);
v___x_1310_ = lean_box(v_onlyNonCumulative_1308_);
v___x_1311_ = lean_apply_3(v_h__9_1281_, lean_box(0), v___x_1310_, v_d_1309_);
return v___x_1311_;
}
case 9:
{
lean_object* v_d_1312_; lean_object* v___x_1313_; 
lean_dec(v_h__16_1288_);
lean_dec(v_h__15_1287_);
lean_dec(v_h__14_1286_);
lean_dec(v_h__13_1285_);
lean_dec(v_h__12_1284_);
lean_dec(v_h__11_1283_);
lean_dec(v_h__9_1281_);
lean_dec(v_h__8_1280_);
lean_dec(v_h__7_1279_);
lean_dec(v_h__6_1278_);
lean_dec(v_h__5_1277_);
lean_dec(v_h__4_1276_);
lean_dec(v_h__3_1275_);
lean_dec(v_h__2_1274_);
lean_dec(v_h__1_1273_);
v_d_1312_ = lean_ctor_get(v_x_1272_, 0);
lean_inc(v_d_1312_);
lean_dec_ref_known(v_x_1272_, 1);
v___x_1313_ = lean_apply_2(v_h__10_1282_, lean_box(0), v_d_1312_);
return v___x_1313_;
}
case 10:
{
lean_object* v_d_1314_; lean_object* v___x_1315_; 
lean_dec(v_h__16_1288_);
lean_dec(v_h__15_1287_);
lean_dec(v_h__14_1286_);
lean_dec(v_h__13_1285_);
lean_dec(v_h__12_1284_);
lean_dec(v_h__10_1282_);
lean_dec(v_h__9_1281_);
lean_dec(v_h__8_1280_);
lean_dec(v_h__7_1279_);
lean_dec(v_h__6_1278_);
lean_dec(v_h__5_1277_);
lean_dec(v_h__4_1276_);
lean_dec(v_h__3_1275_);
lean_dec(v_h__2_1274_);
lean_dec(v_h__1_1273_);
v_d_1314_ = lean_ctor_get(v_x_1272_, 0);
lean_inc(v_d_1314_);
lean_dec_ref_known(v_x_1272_, 1);
v___x_1315_ = lean_apply_2(v_h__11_1283_, lean_box(0), v_d_1314_);
return v___x_1315_;
}
case 11:
{
lean_object* v_d_1316_; lean_object* v___x_1317_; 
lean_dec(v_h__16_1288_);
lean_dec(v_h__15_1287_);
lean_dec(v_h__14_1286_);
lean_dec(v_h__13_1285_);
lean_dec(v_h__11_1283_);
lean_dec(v_h__10_1282_);
lean_dec(v_h__9_1281_);
lean_dec(v_h__8_1280_);
lean_dec(v_h__7_1279_);
lean_dec(v_h__6_1278_);
lean_dec(v_h__5_1277_);
lean_dec(v_h__4_1276_);
lean_dec(v_h__3_1275_);
lean_dec(v_h__2_1274_);
lean_dec(v_h__1_1273_);
v_d_1316_ = lean_ctor_get(v_x_1272_, 0);
lean_inc(v_d_1316_);
lean_dec_ref_known(v_x_1272_, 1);
v___x_1317_ = lean_apply_2(v_h__12_1284_, lean_box(0), v_d_1316_);
return v___x_1317_;
}
case 12:
{
lean_object* v_p_1318_; lean_object* v_d_1319_; lean_object* v___x_1320_; 
lean_dec(v_h__16_1288_);
lean_dec(v_h__15_1287_);
lean_dec(v_h__14_1286_);
lean_dec(v_h__12_1284_);
lean_dec(v_h__11_1283_);
lean_dec(v_h__10_1282_);
lean_dec(v_h__9_1281_);
lean_dec(v_h__8_1280_);
lean_dec(v_h__7_1279_);
lean_dec(v_h__6_1278_);
lean_dec(v_h__5_1277_);
lean_dec(v_h__4_1276_);
lean_dec(v_h__3_1275_);
lean_dec(v_h__2_1274_);
lean_dec(v_h__1_1273_);
v_p_1318_ = lean_ctor_get(v_x_1272_, 0);
lean_inc_ref(v_p_1318_);
v_d_1319_ = lean_ctor_get(v_x_1272_, 1);
lean_inc(v_d_1319_);
lean_dec_ref_known(v_x_1272_, 2);
v___x_1320_ = lean_apply_3(v_h__13_1285_, lean_box(0), v_p_1318_, v_d_1319_);
return v___x_1320_;
}
case 13:
{
lean_object* v_cost_1321_; lean_object* v_d_1322_; lean_object* v___x_1323_; 
lean_dec(v_h__16_1288_);
lean_dec(v_h__15_1287_);
lean_dec(v_h__13_1285_);
lean_dec(v_h__12_1284_);
lean_dec(v_h__11_1283_);
lean_dec(v_h__10_1282_);
lean_dec(v_h__9_1281_);
lean_dec(v_h__8_1280_);
lean_dec(v_h__7_1279_);
lean_dec(v_h__6_1278_);
lean_dec(v_h__5_1277_);
lean_dec(v_h__4_1276_);
lean_dec(v_h__3_1275_);
lean_dec(v_h__2_1274_);
lean_dec(v_h__1_1273_);
v_cost_1321_ = lean_ctor_get(v_x_1272_, 0);
lean_inc(v_cost_1321_);
v_d_1322_ = lean_ctor_get(v_x_1272_, 1);
lean_inc(v_d_1322_);
lean_dec_ref_known(v_x_1272_, 2);
v___x_1323_ = lean_apply_3(v_h__14_1286_, lean_box(0), v_cost_1321_, v_d_1322_);
return v___x_1323_;
}
case 14:
{
lean_object* v_a_1324_; lean_object* v_b_1325_; lean_object* v___x_1326_; 
lean_dec(v_h__16_1288_);
lean_dec(v_h__14_1286_);
lean_dec(v_h__13_1285_);
lean_dec(v_h__12_1284_);
lean_dec(v_h__11_1283_);
lean_dec(v_h__10_1282_);
lean_dec(v_h__9_1281_);
lean_dec(v_h__8_1280_);
lean_dec(v_h__7_1279_);
lean_dec(v_h__6_1278_);
lean_dec(v_h__5_1277_);
lean_dec(v_h__4_1276_);
lean_dec(v_h__3_1275_);
lean_dec(v_h__2_1274_);
lean_dec(v_h__1_1273_);
v_a_1324_ = lean_ctor_get(v_x_1272_, 0);
lean_inc(v_a_1324_);
v_b_1325_ = lean_ctor_get(v_x_1272_, 1);
lean_inc(v_b_1325_);
lean_dec_ref_known(v_x_1272_, 2);
v___x_1326_ = lean_apply_3(v_h__15_1287_, lean_box(0), v_a_1324_, v_b_1325_);
return v___x_1326_;
}
default: 
{
lean_object* v_a_1327_; lean_object* v_b_1328_; lean_object* v___x_1329_; 
lean_dec(v_h__15_1287_);
lean_dec(v_h__14_1286_);
lean_dec(v_h__13_1285_);
lean_dec(v_h__12_1284_);
lean_dec(v_h__11_1283_);
lean_dec(v_h__10_1282_);
lean_dec(v_h__9_1281_);
lean_dec(v_h__8_1280_);
lean_dec(v_h__7_1279_);
lean_dec(v_h__6_1278_);
lean_dec(v_h__5_1277_);
lean_dec(v_h__4_1276_);
lean_dec(v_h__3_1275_);
lean_dec(v_h__2_1274_);
lean_dec(v_h__1_1273_);
v_a_1327_ = lean_ctor_get(v_x_1272_, 0);
lean_inc(v_a_1327_);
v_b_1328_ = lean_ctor_get(v_x_1272_, 1);
lean_inc(v_b_1328_);
lean_dec_ref_known(v_x_1272_, 2);
v___x_1329_ = lean_apply_3(v_h__16_1288_, lean_box(0), v_a_1327_, v_b_1328_);
return v___x_1329_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__2_splitter___redArg___boxed(lean_object** _args){
lean_object* v_x_1330_ = _args[0];
lean_object* v_h__1_1331_ = _args[1];
lean_object* v_h__2_1332_ = _args[2];
lean_object* v_h__3_1333_ = _args[3];
lean_object* v_h__4_1334_ = _args[4];
lean_object* v_h__5_1335_ = _args[5];
lean_object* v_h__6_1336_ = _args[6];
lean_object* v_h__7_1337_ = _args[7];
lean_object* v_h__8_1338_ = _args[8];
lean_object* v_h__9_1339_ = _args[9];
lean_object* v_h__10_1340_ = _args[10];
lean_object* v_h__11_1341_ = _args[11];
lean_object* v_h__12_1342_ = _args[12];
lean_object* v_h__13_1343_ = _args[13];
lean_object* v_h__14_1344_ = _args[14];
lean_object* v_h__15_1345_ = _args[15];
lean_object* v_h__16_1346_ = _args[16];
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__2_splitter___redArg(v_x_1330_, v_h__1_1331_, v_h__2_1332_, v_h__3_1333_, v_h__4_1334_, v_h__5_1335_, v_h__6_1336_, v_h__7_1337_, v_h__8_1338_, v_h__9_1339_, v_h__10_1340_, v_h__11_1341_, v_h__12_1342_, v_h__13_1343_, v_h__14_1344_, v_h__15_1345_, v_h__16_1346_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__2_splitter(lean_object* v_motive_1348_, lean_object* v_x_1349_, lean_object* v_x_1350_, lean_object* v_h__1_1351_, lean_object* v_h__2_1352_, lean_object* v_h__3_1353_, lean_object* v_h__4_1354_, lean_object* v_h__5_1355_, lean_object* v_h__6_1356_, lean_object* v_h__7_1357_, lean_object* v_h__8_1358_, lean_object* v_h__9_1359_, lean_object* v_h__10_1360_, lean_object* v_h__11_1361_, lean_object* v_h__12_1362_, lean_object* v_h__13_1363_, lean_object* v_h__14_1364_, lean_object* v_h__15_1365_, lean_object* v_h__16_1366_){
_start:
{
switch(lean_obj_tag(v_x_1350_))
{
case 0:
{
lean_object* v___x_1367_; 
lean_dec(v_h__16_1366_);
lean_dec(v_h__15_1365_);
lean_dec(v_h__14_1364_);
lean_dec(v_h__13_1363_);
lean_dec(v_h__12_1362_);
lean_dec(v_h__11_1361_);
lean_dec(v_h__10_1360_);
lean_dec(v_h__9_1359_);
lean_dec(v_h__8_1358_);
lean_dec(v_h__7_1357_);
lean_dec(v_h__6_1356_);
lean_dec(v_h__5_1355_);
lean_dec(v_h__4_1354_);
lean_dec(v_h__3_1353_);
lean_dec(v_h__2_1352_);
v___x_1367_ = lean_apply_1(v_h__1_1351_, lean_box(0));
return v___x_1367_;
}
case 1:
{
lean_object* v_f_1368_; lean_object* v___x_1369_; 
lean_dec(v_h__16_1366_);
lean_dec(v_h__15_1365_);
lean_dec(v_h__14_1364_);
lean_dec(v_h__13_1363_);
lean_dec(v_h__12_1362_);
lean_dec(v_h__11_1361_);
lean_dec(v_h__10_1360_);
lean_dec(v_h__9_1359_);
lean_dec(v_h__8_1358_);
lean_dec(v_h__7_1357_);
lean_dec(v_h__6_1356_);
lean_dec(v_h__5_1355_);
lean_dec(v_h__4_1354_);
lean_dec(v_h__3_1353_);
lean_dec(v_h__1_1351_);
v_f_1368_ = lean_ctor_get(v_x_1350_, 0);
lean_inc_ref(v_f_1368_);
lean_dec_ref_known(v_x_1350_, 1);
v___x_1369_ = lean_apply_2(v_h__2_1352_, lean_box(0), v_f_1368_);
return v___x_1369_;
}
case 2:
{
lean_object* v_s_1370_; lean_object* v___x_1371_; 
lean_dec(v_h__16_1366_);
lean_dec(v_h__15_1365_);
lean_dec(v_h__14_1364_);
lean_dec(v_h__13_1363_);
lean_dec(v_h__12_1362_);
lean_dec(v_h__11_1361_);
lean_dec(v_h__10_1360_);
lean_dec(v_h__9_1359_);
lean_dec(v_h__8_1358_);
lean_dec(v_h__7_1357_);
lean_dec(v_h__6_1356_);
lean_dec(v_h__5_1355_);
lean_dec(v_h__4_1354_);
lean_dec(v_h__2_1352_);
lean_dec(v_h__1_1351_);
v_s_1370_ = lean_ctor_get(v_x_1350_, 0);
lean_inc_ref(v_s_1370_);
lean_dec_ref_known(v_x_1350_, 1);
v___x_1371_ = lean_apply_2(v_h__3_1353_, lean_box(0), v_s_1370_);
return v___x_1371_;
}
case 3:
{
lean_object* v_id_1372_; lean_object* v_d_1373_; lean_object* v___x_1374_; 
lean_dec(v_h__16_1366_);
lean_dec(v_h__15_1365_);
lean_dec(v_h__14_1364_);
lean_dec(v_h__13_1363_);
lean_dec(v_h__12_1362_);
lean_dec(v_h__11_1361_);
lean_dec(v_h__10_1360_);
lean_dec(v_h__9_1359_);
lean_dec(v_h__8_1358_);
lean_dec(v_h__7_1357_);
lean_dec(v_h__5_1355_);
lean_dec(v_h__4_1354_);
lean_dec(v_h__3_1353_);
lean_dec(v_h__2_1352_);
lean_dec(v_h__1_1351_);
v_id_1372_ = lean_ctor_get(v_x_1350_, 0);
lean_inc(v_id_1372_);
v_d_1373_ = lean_ctor_get(v_x_1350_, 1);
lean_inc(v_d_1373_);
lean_dec_ref_known(v_x_1350_, 2);
v___x_1374_ = lean_apply_3(v_h__6_1356_, lean_box(0), v_id_1372_, v_d_1373_);
return v___x_1374_;
}
case 4:
{
lean_object* v_d_1375_; lean_object* v___x_1376_; 
lean_dec(v_h__16_1366_);
lean_dec(v_h__15_1365_);
lean_dec(v_h__14_1364_);
lean_dec(v_h__13_1363_);
lean_dec(v_h__12_1362_);
lean_dec(v_h__11_1361_);
lean_dec(v_h__10_1360_);
lean_dec(v_h__9_1359_);
lean_dec(v_h__8_1358_);
lean_dec(v_h__7_1357_);
lean_dec(v_h__6_1356_);
lean_dec(v_h__5_1355_);
lean_dec(v_h__3_1353_);
lean_dec(v_h__2_1352_);
lean_dec(v_h__1_1351_);
v_d_1375_ = lean_ctor_get(v_x_1350_, 0);
lean_inc(v_d_1375_);
lean_dec_ref_known(v_x_1350_, 1);
v___x_1376_ = lean_apply_2(v_h__4_1354_, lean_box(0), v_d_1375_);
return v___x_1376_;
}
case 5:
{
lean_object* v_d_1377_; lean_object* v___x_1378_; 
lean_dec(v_h__16_1366_);
lean_dec(v_h__15_1365_);
lean_dec(v_h__14_1364_);
lean_dec(v_h__13_1363_);
lean_dec(v_h__12_1362_);
lean_dec(v_h__11_1361_);
lean_dec(v_h__10_1360_);
lean_dec(v_h__9_1359_);
lean_dec(v_h__8_1358_);
lean_dec(v_h__7_1357_);
lean_dec(v_h__6_1356_);
lean_dec(v_h__4_1354_);
lean_dec(v_h__3_1353_);
lean_dec(v_h__2_1352_);
lean_dec(v_h__1_1351_);
v_d_1377_ = lean_ctor_get(v_x_1350_, 0);
lean_inc(v_d_1377_);
lean_dec_ref_known(v_x_1350_, 1);
v___x_1378_ = lean_apply_2(v_h__5_1355_, lean_box(0), v_d_1377_);
return v___x_1378_;
}
case 6:
{
lean_object* v_n_1379_; uint8_t v_isCumulative_1380_; lean_object* v_d_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
lean_dec(v_h__16_1366_);
lean_dec(v_h__15_1365_);
lean_dec(v_h__14_1364_);
lean_dec(v_h__13_1363_);
lean_dec(v_h__12_1362_);
lean_dec(v_h__11_1361_);
lean_dec(v_h__10_1360_);
lean_dec(v_h__9_1359_);
lean_dec(v_h__8_1358_);
lean_dec(v_h__6_1356_);
lean_dec(v_h__5_1355_);
lean_dec(v_h__4_1354_);
lean_dec(v_h__3_1353_);
lean_dec(v_h__2_1352_);
lean_dec(v_h__1_1351_);
v_n_1379_ = lean_ctor_get(v_x_1350_, 0);
lean_inc(v_n_1379_);
v_isCumulative_1380_ = lean_ctor_get_uint8(v_x_1350_, sizeof(void*)*2);
v_d_1381_ = lean_ctor_get(v_x_1350_, 1);
lean_inc(v_d_1381_);
lean_dec_ref_known(v_x_1350_, 2);
v___x_1382_ = lean_box(v_isCumulative_1380_);
v___x_1383_ = lean_apply_4(v_h__7_1357_, lean_box(0), v_n_1379_, v___x_1382_, v_d_1381_);
return v___x_1383_;
}
case 7:
{
lean_object* v_d_1384_; lean_object* v___x_1385_; 
lean_dec(v_h__16_1366_);
lean_dec(v_h__15_1365_);
lean_dec(v_h__14_1364_);
lean_dec(v_h__13_1363_);
lean_dec(v_h__12_1362_);
lean_dec(v_h__11_1361_);
lean_dec(v_h__10_1360_);
lean_dec(v_h__9_1359_);
lean_dec(v_h__7_1357_);
lean_dec(v_h__6_1356_);
lean_dec(v_h__5_1355_);
lean_dec(v_h__4_1354_);
lean_dec(v_h__3_1353_);
lean_dec(v_h__2_1352_);
lean_dec(v_h__1_1351_);
v_d_1384_ = lean_ctor_get(v_x_1350_, 0);
lean_inc(v_d_1384_);
lean_dec_ref_known(v_x_1350_, 1);
v___x_1385_ = lean_apply_2(v_h__8_1358_, lean_box(0), v_d_1384_);
return v___x_1385_;
}
case 8:
{
uint8_t v_onlyNonCumulative_1386_; lean_object* v_d_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
lean_dec(v_h__16_1366_);
lean_dec(v_h__15_1365_);
lean_dec(v_h__14_1364_);
lean_dec(v_h__13_1363_);
lean_dec(v_h__12_1362_);
lean_dec(v_h__11_1361_);
lean_dec(v_h__10_1360_);
lean_dec(v_h__8_1358_);
lean_dec(v_h__7_1357_);
lean_dec(v_h__6_1356_);
lean_dec(v_h__5_1355_);
lean_dec(v_h__4_1354_);
lean_dec(v_h__3_1353_);
lean_dec(v_h__2_1352_);
lean_dec(v_h__1_1351_);
v_onlyNonCumulative_1386_ = lean_ctor_get_uint8(v_x_1350_, sizeof(void*)*1);
v_d_1387_ = lean_ctor_get(v_x_1350_, 0);
lean_inc(v_d_1387_);
lean_dec_ref_known(v_x_1350_, 1);
v___x_1388_ = lean_box(v_onlyNonCumulative_1386_);
v___x_1389_ = lean_apply_3(v_h__9_1359_, lean_box(0), v___x_1388_, v_d_1387_);
return v___x_1389_;
}
case 9:
{
lean_object* v_d_1390_; lean_object* v___x_1391_; 
lean_dec(v_h__16_1366_);
lean_dec(v_h__15_1365_);
lean_dec(v_h__14_1364_);
lean_dec(v_h__13_1363_);
lean_dec(v_h__12_1362_);
lean_dec(v_h__11_1361_);
lean_dec(v_h__9_1359_);
lean_dec(v_h__8_1358_);
lean_dec(v_h__7_1357_);
lean_dec(v_h__6_1356_);
lean_dec(v_h__5_1355_);
lean_dec(v_h__4_1354_);
lean_dec(v_h__3_1353_);
lean_dec(v_h__2_1352_);
lean_dec(v_h__1_1351_);
v_d_1390_ = lean_ctor_get(v_x_1350_, 0);
lean_inc(v_d_1390_);
lean_dec_ref_known(v_x_1350_, 1);
v___x_1391_ = lean_apply_2(v_h__10_1360_, lean_box(0), v_d_1390_);
return v___x_1391_;
}
case 10:
{
lean_object* v_d_1392_; lean_object* v___x_1393_; 
lean_dec(v_h__16_1366_);
lean_dec(v_h__15_1365_);
lean_dec(v_h__14_1364_);
lean_dec(v_h__13_1363_);
lean_dec(v_h__12_1362_);
lean_dec(v_h__10_1360_);
lean_dec(v_h__9_1359_);
lean_dec(v_h__8_1358_);
lean_dec(v_h__7_1357_);
lean_dec(v_h__6_1356_);
lean_dec(v_h__5_1355_);
lean_dec(v_h__4_1354_);
lean_dec(v_h__3_1353_);
lean_dec(v_h__2_1352_);
lean_dec(v_h__1_1351_);
v_d_1392_ = lean_ctor_get(v_x_1350_, 0);
lean_inc(v_d_1392_);
lean_dec_ref_known(v_x_1350_, 1);
v___x_1393_ = lean_apply_2(v_h__11_1361_, lean_box(0), v_d_1392_);
return v___x_1393_;
}
case 11:
{
lean_object* v_d_1394_; lean_object* v___x_1395_; 
lean_dec(v_h__16_1366_);
lean_dec(v_h__15_1365_);
lean_dec(v_h__14_1364_);
lean_dec(v_h__13_1363_);
lean_dec(v_h__11_1361_);
lean_dec(v_h__10_1360_);
lean_dec(v_h__9_1359_);
lean_dec(v_h__8_1358_);
lean_dec(v_h__7_1357_);
lean_dec(v_h__6_1356_);
lean_dec(v_h__5_1355_);
lean_dec(v_h__4_1354_);
lean_dec(v_h__3_1353_);
lean_dec(v_h__2_1352_);
lean_dec(v_h__1_1351_);
v_d_1394_ = lean_ctor_get(v_x_1350_, 0);
lean_inc(v_d_1394_);
lean_dec_ref_known(v_x_1350_, 1);
v___x_1395_ = lean_apply_2(v_h__12_1362_, lean_box(0), v_d_1394_);
return v___x_1395_;
}
case 12:
{
lean_object* v_p_1396_; lean_object* v_d_1397_; lean_object* v___x_1398_; 
lean_dec(v_h__16_1366_);
lean_dec(v_h__15_1365_);
lean_dec(v_h__14_1364_);
lean_dec(v_h__12_1362_);
lean_dec(v_h__11_1361_);
lean_dec(v_h__10_1360_);
lean_dec(v_h__9_1359_);
lean_dec(v_h__8_1358_);
lean_dec(v_h__7_1357_);
lean_dec(v_h__6_1356_);
lean_dec(v_h__5_1355_);
lean_dec(v_h__4_1354_);
lean_dec(v_h__3_1353_);
lean_dec(v_h__2_1352_);
lean_dec(v_h__1_1351_);
v_p_1396_ = lean_ctor_get(v_x_1350_, 0);
lean_inc_ref(v_p_1396_);
v_d_1397_ = lean_ctor_get(v_x_1350_, 1);
lean_inc(v_d_1397_);
lean_dec_ref_known(v_x_1350_, 2);
v___x_1398_ = lean_apply_3(v_h__13_1363_, lean_box(0), v_p_1396_, v_d_1397_);
return v___x_1398_;
}
case 13:
{
lean_object* v_cost_1399_; lean_object* v_d_1400_; lean_object* v___x_1401_; 
lean_dec(v_h__16_1366_);
lean_dec(v_h__15_1365_);
lean_dec(v_h__13_1363_);
lean_dec(v_h__12_1362_);
lean_dec(v_h__11_1361_);
lean_dec(v_h__10_1360_);
lean_dec(v_h__9_1359_);
lean_dec(v_h__8_1358_);
lean_dec(v_h__7_1357_);
lean_dec(v_h__6_1356_);
lean_dec(v_h__5_1355_);
lean_dec(v_h__4_1354_);
lean_dec(v_h__3_1353_);
lean_dec(v_h__2_1352_);
lean_dec(v_h__1_1351_);
v_cost_1399_ = lean_ctor_get(v_x_1350_, 0);
lean_inc(v_cost_1399_);
v_d_1400_ = lean_ctor_get(v_x_1350_, 1);
lean_inc(v_d_1400_);
lean_dec_ref_known(v_x_1350_, 2);
v___x_1401_ = lean_apply_3(v_h__14_1364_, lean_box(0), v_cost_1399_, v_d_1400_);
return v___x_1401_;
}
case 14:
{
lean_object* v_a_1402_; lean_object* v_b_1403_; lean_object* v___x_1404_; 
lean_dec(v_h__16_1366_);
lean_dec(v_h__14_1364_);
lean_dec(v_h__13_1363_);
lean_dec(v_h__12_1362_);
lean_dec(v_h__11_1361_);
lean_dec(v_h__10_1360_);
lean_dec(v_h__9_1359_);
lean_dec(v_h__8_1358_);
lean_dec(v_h__7_1357_);
lean_dec(v_h__6_1356_);
lean_dec(v_h__5_1355_);
lean_dec(v_h__4_1354_);
lean_dec(v_h__3_1353_);
lean_dec(v_h__2_1352_);
lean_dec(v_h__1_1351_);
v_a_1402_ = lean_ctor_get(v_x_1350_, 0);
lean_inc(v_a_1402_);
v_b_1403_ = lean_ctor_get(v_x_1350_, 1);
lean_inc(v_b_1403_);
lean_dec_ref_known(v_x_1350_, 2);
v___x_1404_ = lean_apply_3(v_h__15_1365_, lean_box(0), v_a_1402_, v_b_1403_);
return v___x_1404_;
}
default: 
{
lean_object* v_a_1405_; lean_object* v_b_1406_; lean_object* v___x_1407_; 
lean_dec(v_h__15_1365_);
lean_dec(v_h__14_1364_);
lean_dec(v_h__13_1363_);
lean_dec(v_h__12_1362_);
lean_dec(v_h__11_1361_);
lean_dec(v_h__10_1360_);
lean_dec(v_h__9_1359_);
lean_dec(v_h__8_1358_);
lean_dec(v_h__7_1357_);
lean_dec(v_h__6_1356_);
lean_dec(v_h__5_1355_);
lean_dec(v_h__4_1354_);
lean_dec(v_h__3_1353_);
lean_dec(v_h__2_1352_);
lean_dec(v_h__1_1351_);
v_a_1405_ = lean_ctor_get(v_x_1350_, 0);
lean_inc(v_a_1405_);
v_b_1406_ = lean_ctor_get(v_x_1350_, 1);
lean_inc(v_b_1406_);
lean_dec_ref_known(v_x_1350_, 2);
v___x_1407_ = lean_apply_3(v_h__16_1366_, lean_box(0), v_a_1405_, v_b_1406_);
return v___x_1407_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__2_splitter___boxed(lean_object** _args){
lean_object* v_motive_1408_ = _args[0];
lean_object* v_x_1409_ = _args[1];
lean_object* v_x_1410_ = _args[2];
lean_object* v_h__1_1411_ = _args[3];
lean_object* v_h__2_1412_ = _args[4];
lean_object* v_h__3_1413_ = _args[5];
lean_object* v_h__4_1414_ = _args[6];
lean_object* v_h__5_1415_ = _args[7];
lean_object* v_h__6_1416_ = _args[8];
lean_object* v_h__7_1417_ = _args[9];
lean_object* v_h__8_1418_ = _args[10];
lean_object* v_h__9_1419_ = _args[11];
lean_object* v_h__10_1420_ = _args[12];
lean_object* v_h__11_1421_ = _args[13];
lean_object* v_h__12_1422_ = _args[14];
lean_object* v_h__13_1423_ = _args[15];
lean_object* v_h__14_1424_ = _args[16];
lean_object* v_h__15_1425_ = _args[17];
lean_object* v_h__16_1426_ = _args[18];
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__2_splitter(v_motive_1408_, v_x_1409_, v_x_1410_, v_h__1_1411_, v_h__2_1412_, v_h__3_1413_, v_h__4_1414_, v_h__5_1415_, v_h__6_1416_, v_h__7_1417_, v_h__8_1418_, v_h__9_1419_, v_h__10_1420_, v_h__11_1421_, v_h__12_1422_, v_h__13_1423_, v_h__14_1424_, v_h__15_1425_, v_h__16_1426_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__1_splitter___redArg(uint8_t v_x_1428_, lean_object* v_h__1_1429_, lean_object* v_h__2_1430_, lean_object* v_h__3_1431_){
_start:
{
switch(v_x_1428_)
{
case 0:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; 
lean_dec(v_h__3_1431_);
lean_dec(v_h__2_1430_);
v___x_1432_ = lean_box(0);
v___x_1433_ = lean_apply_1(v_h__1_1429_, v___x_1432_);
return v___x_1433_;
}
case 1:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
lean_dec(v_h__3_1431_);
lean_dec(v_h__1_1429_);
v___x_1434_ = lean_box(0);
v___x_1435_ = lean_apply_1(v_h__2_1430_, v___x_1434_);
return v___x_1435_;
}
default: 
{
lean_object* v___x_1436_; lean_object* v___x_1437_; 
lean_dec(v_h__2_1430_);
lean_dec(v_h__1_1429_);
v___x_1436_ = lean_box(0);
v___x_1437_ = lean_apply_1(v_h__3_1431_, v___x_1436_);
return v___x_1437_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__1_splitter___redArg___boxed(lean_object* v_x_1438_, lean_object* v_h__1_1439_, lean_object* v_h__2_1440_, lean_object* v_h__3_1441_){
_start:
{
uint8_t v_x_33__boxed_1442_; lean_object* v_res_1443_; 
v_x_33__boxed_1442_ = lean_unbox(v_x_1438_);
v_res_1443_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__1_splitter___redArg(v_x_33__boxed_1442_, v_h__1_1439_, v_h__2_1440_, v_h__3_1441_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__1_splitter(lean_object* v_motive_1444_, uint8_t v_x_1445_, lean_object* v_h__1_1446_, lean_object* v_h__2_1447_, lean_object* v_h__3_1448_){
_start:
{
switch(v_x_1445_)
{
case 0:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; 
lean_dec(v_h__3_1448_);
lean_dec(v_h__2_1447_);
v___x_1449_ = lean_box(0);
v___x_1450_ = lean_apply_1(v_h__1_1446_, v___x_1449_);
return v___x_1450_;
}
case 1:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; 
lean_dec(v_h__3_1448_);
lean_dec(v_h__1_1446_);
v___x_1451_ = lean_box(0);
v___x_1452_ = lean_apply_1(v_h__2_1447_, v___x_1451_);
return v___x_1452_;
}
default: 
{
lean_object* v___x_1453_; lean_object* v___x_1454_; 
lean_dec(v_h__2_1447_);
lean_dec(v_h__1_1446_);
v___x_1453_ = lean_box(0);
v___x_1454_ = lean_apply_1(v_h__3_1448_, v___x_1453_);
return v___x_1454_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__1_splitter___boxed(lean_object* v_motive_1455_, lean_object* v_x_1456_, lean_object* v_h__1_1457_, lean_object* v_h__2_1458_, lean_object* v_h__3_1459_){
_start:
{
uint8_t v_x_48__boxed_1460_; lean_object* v_res_1461_; 
v_x_48__boxed_1460_ = lean_unbox(v_x_1456_);
v_res_1461_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__1_splitter(v_motive_1455_, v_x_48__boxed_1460_, v_h__1_1457_, v_h__2_1458_, v_h__3_1459_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__4_splitter___redArg(lean_object* v_x_1462_, lean_object* v_h__1_1463_, lean_object* v_h__2_1464_, lean_object* v_h__3_1465_, lean_object* v_h__4_1466_, lean_object* v_h__5_1467_, lean_object* v_h__6_1468_, lean_object* v_h__7_1469_, lean_object* v_h__8_1470_, lean_object* v_h__9_1471_, lean_object* v_h__10_1472_, lean_object* v_h__11_1473_, lean_object* v_h__12_1474_, lean_object* v_h__13_1475_, lean_object* v_h__14_1476_, lean_object* v_h__15_1477_, lean_object* v_h__16_1478_){
_start:
{
switch(lean_obj_tag(v_x_1462_))
{
case 0:
{
lean_object* v___x_1479_; 
lean_dec(v_h__16_1478_);
lean_dec(v_h__15_1477_);
lean_dec(v_h__14_1476_);
lean_dec(v_h__13_1475_);
lean_dec(v_h__12_1474_);
lean_dec(v_h__11_1473_);
lean_dec(v_h__10_1472_);
lean_dec(v_h__9_1471_);
lean_dec(v_h__8_1470_);
lean_dec(v_h__7_1469_);
lean_dec(v_h__6_1468_);
lean_dec(v_h__5_1467_);
lean_dec(v_h__4_1466_);
lean_dec(v_h__3_1465_);
lean_dec(v_h__2_1464_);
v___x_1479_ = lean_apply_1(v_h__1_1463_, lean_box(0));
return v___x_1479_;
}
case 1:
{
lean_object* v_f_1480_; lean_object* v___x_1481_; 
lean_dec(v_h__16_1478_);
lean_dec(v_h__15_1477_);
lean_dec(v_h__14_1476_);
lean_dec(v_h__13_1475_);
lean_dec(v_h__12_1474_);
lean_dec(v_h__11_1473_);
lean_dec(v_h__10_1472_);
lean_dec(v_h__9_1471_);
lean_dec(v_h__8_1470_);
lean_dec(v_h__7_1469_);
lean_dec(v_h__6_1468_);
lean_dec(v_h__5_1467_);
lean_dec(v_h__4_1466_);
lean_dec(v_h__2_1464_);
lean_dec(v_h__1_1463_);
v_f_1480_ = lean_ctor_get(v_x_1462_, 0);
lean_inc_ref(v_f_1480_);
lean_dec_ref_known(v_x_1462_, 1);
v___x_1481_ = lean_apply_2(v_h__3_1465_, lean_box(0), v_f_1480_);
return v___x_1481_;
}
case 2:
{
lean_object* v_s_1482_; lean_object* v___x_1483_; 
lean_dec(v_h__16_1478_);
lean_dec(v_h__15_1477_);
lean_dec(v_h__14_1476_);
lean_dec(v_h__13_1475_);
lean_dec(v_h__12_1474_);
lean_dec(v_h__11_1473_);
lean_dec(v_h__10_1472_);
lean_dec(v_h__9_1471_);
lean_dec(v_h__8_1470_);
lean_dec(v_h__7_1469_);
lean_dec(v_h__6_1468_);
lean_dec(v_h__5_1467_);
lean_dec(v_h__4_1466_);
lean_dec(v_h__3_1465_);
lean_dec(v_h__1_1463_);
v_s_1482_ = lean_ctor_get(v_x_1462_, 0);
lean_inc_ref(v_s_1482_);
lean_dec_ref_known(v_x_1462_, 1);
v___x_1483_ = lean_apply_2(v_h__2_1464_, lean_box(0), v_s_1482_);
return v___x_1483_;
}
case 3:
{
lean_object* v_id_1484_; lean_object* v_d_1485_; lean_object* v___x_1486_; 
lean_dec(v_h__16_1478_);
lean_dec(v_h__15_1477_);
lean_dec(v_h__14_1476_);
lean_dec(v_h__13_1475_);
lean_dec(v_h__12_1474_);
lean_dec(v_h__11_1473_);
lean_dec(v_h__10_1472_);
lean_dec(v_h__9_1471_);
lean_dec(v_h__8_1470_);
lean_dec(v_h__7_1469_);
lean_dec(v_h__5_1467_);
lean_dec(v_h__4_1466_);
lean_dec(v_h__3_1465_);
lean_dec(v_h__2_1464_);
lean_dec(v_h__1_1463_);
v_id_1484_ = lean_ctor_get(v_x_1462_, 0);
lean_inc(v_id_1484_);
v_d_1485_ = lean_ctor_get(v_x_1462_, 1);
lean_inc(v_d_1485_);
lean_dec_ref_known(v_x_1462_, 2);
v___x_1486_ = lean_apply_3(v_h__6_1468_, lean_box(0), v_id_1484_, v_d_1485_);
return v___x_1486_;
}
case 4:
{
lean_object* v_d_1487_; lean_object* v___x_1488_; 
lean_dec(v_h__16_1478_);
lean_dec(v_h__15_1477_);
lean_dec(v_h__14_1476_);
lean_dec(v_h__13_1475_);
lean_dec(v_h__12_1474_);
lean_dec(v_h__11_1473_);
lean_dec(v_h__10_1472_);
lean_dec(v_h__9_1471_);
lean_dec(v_h__8_1470_);
lean_dec(v_h__7_1469_);
lean_dec(v_h__6_1468_);
lean_dec(v_h__5_1467_);
lean_dec(v_h__3_1465_);
lean_dec(v_h__2_1464_);
lean_dec(v_h__1_1463_);
v_d_1487_ = lean_ctor_get(v_x_1462_, 0);
lean_inc(v_d_1487_);
lean_dec_ref_known(v_x_1462_, 1);
v___x_1488_ = lean_apply_2(v_h__4_1466_, lean_box(0), v_d_1487_);
return v___x_1488_;
}
case 5:
{
lean_object* v_d_1489_; lean_object* v___x_1490_; 
lean_dec(v_h__16_1478_);
lean_dec(v_h__15_1477_);
lean_dec(v_h__14_1476_);
lean_dec(v_h__13_1475_);
lean_dec(v_h__12_1474_);
lean_dec(v_h__11_1473_);
lean_dec(v_h__10_1472_);
lean_dec(v_h__9_1471_);
lean_dec(v_h__8_1470_);
lean_dec(v_h__7_1469_);
lean_dec(v_h__6_1468_);
lean_dec(v_h__4_1466_);
lean_dec(v_h__3_1465_);
lean_dec(v_h__2_1464_);
lean_dec(v_h__1_1463_);
v_d_1489_ = lean_ctor_get(v_x_1462_, 0);
lean_inc(v_d_1489_);
lean_dec_ref_known(v_x_1462_, 1);
v___x_1490_ = lean_apply_2(v_h__5_1467_, lean_box(0), v_d_1489_);
return v___x_1490_;
}
case 6:
{
lean_object* v_n_1491_; uint8_t v_isCumulative_1492_; lean_object* v_d_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
lean_dec(v_h__16_1478_);
lean_dec(v_h__15_1477_);
lean_dec(v_h__14_1476_);
lean_dec(v_h__13_1475_);
lean_dec(v_h__12_1474_);
lean_dec(v_h__11_1473_);
lean_dec(v_h__10_1472_);
lean_dec(v_h__9_1471_);
lean_dec(v_h__8_1470_);
lean_dec(v_h__6_1468_);
lean_dec(v_h__5_1467_);
lean_dec(v_h__4_1466_);
lean_dec(v_h__3_1465_);
lean_dec(v_h__2_1464_);
lean_dec(v_h__1_1463_);
v_n_1491_ = lean_ctor_get(v_x_1462_, 0);
lean_inc(v_n_1491_);
v_isCumulative_1492_ = lean_ctor_get_uint8(v_x_1462_, sizeof(void*)*2);
v_d_1493_ = lean_ctor_get(v_x_1462_, 1);
lean_inc(v_d_1493_);
lean_dec_ref_known(v_x_1462_, 2);
v___x_1494_ = lean_box(v_isCumulative_1492_);
v___x_1495_ = lean_apply_4(v_h__7_1469_, lean_box(0), v_n_1491_, v___x_1494_, v_d_1493_);
return v___x_1495_;
}
case 7:
{
lean_object* v_d_1496_; lean_object* v___x_1497_; 
lean_dec(v_h__16_1478_);
lean_dec(v_h__15_1477_);
lean_dec(v_h__14_1476_);
lean_dec(v_h__13_1475_);
lean_dec(v_h__12_1474_);
lean_dec(v_h__11_1473_);
lean_dec(v_h__10_1472_);
lean_dec(v_h__9_1471_);
lean_dec(v_h__7_1469_);
lean_dec(v_h__6_1468_);
lean_dec(v_h__5_1467_);
lean_dec(v_h__4_1466_);
lean_dec(v_h__3_1465_);
lean_dec(v_h__2_1464_);
lean_dec(v_h__1_1463_);
v_d_1496_ = lean_ctor_get(v_x_1462_, 0);
lean_inc(v_d_1496_);
lean_dec_ref_known(v_x_1462_, 1);
v___x_1497_ = lean_apply_2(v_h__8_1470_, lean_box(0), v_d_1496_);
return v___x_1497_;
}
case 8:
{
uint8_t v_onlyNonCumulative_1498_; lean_object* v_d_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; 
lean_dec(v_h__16_1478_);
lean_dec(v_h__15_1477_);
lean_dec(v_h__14_1476_);
lean_dec(v_h__13_1475_);
lean_dec(v_h__12_1474_);
lean_dec(v_h__11_1473_);
lean_dec(v_h__10_1472_);
lean_dec(v_h__8_1470_);
lean_dec(v_h__7_1469_);
lean_dec(v_h__6_1468_);
lean_dec(v_h__5_1467_);
lean_dec(v_h__4_1466_);
lean_dec(v_h__3_1465_);
lean_dec(v_h__2_1464_);
lean_dec(v_h__1_1463_);
v_onlyNonCumulative_1498_ = lean_ctor_get_uint8(v_x_1462_, sizeof(void*)*1);
v_d_1499_ = lean_ctor_get(v_x_1462_, 0);
lean_inc(v_d_1499_);
lean_dec_ref_known(v_x_1462_, 1);
v___x_1500_ = lean_box(v_onlyNonCumulative_1498_);
v___x_1501_ = lean_apply_3(v_h__9_1471_, lean_box(0), v___x_1500_, v_d_1499_);
return v___x_1501_;
}
case 9:
{
lean_object* v_d_1502_; lean_object* v___x_1503_; 
lean_dec(v_h__16_1478_);
lean_dec(v_h__15_1477_);
lean_dec(v_h__14_1476_);
lean_dec(v_h__13_1475_);
lean_dec(v_h__12_1474_);
lean_dec(v_h__11_1473_);
lean_dec(v_h__9_1471_);
lean_dec(v_h__8_1470_);
lean_dec(v_h__7_1469_);
lean_dec(v_h__6_1468_);
lean_dec(v_h__5_1467_);
lean_dec(v_h__4_1466_);
lean_dec(v_h__3_1465_);
lean_dec(v_h__2_1464_);
lean_dec(v_h__1_1463_);
v_d_1502_ = lean_ctor_get(v_x_1462_, 0);
lean_inc(v_d_1502_);
lean_dec_ref_known(v_x_1462_, 1);
v___x_1503_ = lean_apply_2(v_h__10_1472_, lean_box(0), v_d_1502_);
return v___x_1503_;
}
case 10:
{
lean_object* v_d_1504_; lean_object* v___x_1505_; 
lean_dec(v_h__16_1478_);
lean_dec(v_h__15_1477_);
lean_dec(v_h__14_1476_);
lean_dec(v_h__13_1475_);
lean_dec(v_h__12_1474_);
lean_dec(v_h__10_1472_);
lean_dec(v_h__9_1471_);
lean_dec(v_h__8_1470_);
lean_dec(v_h__7_1469_);
lean_dec(v_h__6_1468_);
lean_dec(v_h__5_1467_);
lean_dec(v_h__4_1466_);
lean_dec(v_h__3_1465_);
lean_dec(v_h__2_1464_);
lean_dec(v_h__1_1463_);
v_d_1504_ = lean_ctor_get(v_x_1462_, 0);
lean_inc(v_d_1504_);
lean_dec_ref_known(v_x_1462_, 1);
v___x_1505_ = lean_apply_2(v_h__11_1473_, lean_box(0), v_d_1504_);
return v___x_1505_;
}
case 11:
{
lean_object* v_d_1506_; lean_object* v___x_1507_; 
lean_dec(v_h__16_1478_);
lean_dec(v_h__15_1477_);
lean_dec(v_h__14_1476_);
lean_dec(v_h__13_1475_);
lean_dec(v_h__11_1473_);
lean_dec(v_h__10_1472_);
lean_dec(v_h__9_1471_);
lean_dec(v_h__8_1470_);
lean_dec(v_h__7_1469_);
lean_dec(v_h__6_1468_);
lean_dec(v_h__5_1467_);
lean_dec(v_h__4_1466_);
lean_dec(v_h__3_1465_);
lean_dec(v_h__2_1464_);
lean_dec(v_h__1_1463_);
v_d_1506_ = lean_ctor_get(v_x_1462_, 0);
lean_inc(v_d_1506_);
lean_dec_ref_known(v_x_1462_, 1);
v___x_1507_ = lean_apply_2(v_h__12_1474_, lean_box(0), v_d_1506_);
return v___x_1507_;
}
case 12:
{
lean_object* v_p_1508_; lean_object* v_d_1509_; lean_object* v___x_1510_; 
lean_dec(v_h__16_1478_);
lean_dec(v_h__15_1477_);
lean_dec(v_h__14_1476_);
lean_dec(v_h__12_1474_);
lean_dec(v_h__11_1473_);
lean_dec(v_h__10_1472_);
lean_dec(v_h__9_1471_);
lean_dec(v_h__8_1470_);
lean_dec(v_h__7_1469_);
lean_dec(v_h__6_1468_);
lean_dec(v_h__5_1467_);
lean_dec(v_h__4_1466_);
lean_dec(v_h__3_1465_);
lean_dec(v_h__2_1464_);
lean_dec(v_h__1_1463_);
v_p_1508_ = lean_ctor_get(v_x_1462_, 0);
lean_inc_ref(v_p_1508_);
v_d_1509_ = lean_ctor_get(v_x_1462_, 1);
lean_inc(v_d_1509_);
lean_dec_ref_known(v_x_1462_, 2);
v___x_1510_ = lean_apply_3(v_h__13_1475_, lean_box(0), v_p_1508_, v_d_1509_);
return v___x_1510_;
}
case 13:
{
lean_object* v_cost_1511_; lean_object* v_d_1512_; lean_object* v___x_1513_; 
lean_dec(v_h__16_1478_);
lean_dec(v_h__15_1477_);
lean_dec(v_h__13_1475_);
lean_dec(v_h__12_1474_);
lean_dec(v_h__11_1473_);
lean_dec(v_h__10_1472_);
lean_dec(v_h__9_1471_);
lean_dec(v_h__8_1470_);
lean_dec(v_h__7_1469_);
lean_dec(v_h__6_1468_);
lean_dec(v_h__5_1467_);
lean_dec(v_h__4_1466_);
lean_dec(v_h__3_1465_);
lean_dec(v_h__2_1464_);
lean_dec(v_h__1_1463_);
v_cost_1511_ = lean_ctor_get(v_x_1462_, 0);
lean_inc(v_cost_1511_);
v_d_1512_ = lean_ctor_get(v_x_1462_, 1);
lean_inc(v_d_1512_);
lean_dec_ref_known(v_x_1462_, 2);
v___x_1513_ = lean_apply_3(v_h__14_1476_, lean_box(0), v_cost_1511_, v_d_1512_);
return v___x_1513_;
}
case 14:
{
lean_object* v_a_1514_; lean_object* v_b_1515_; lean_object* v___x_1516_; 
lean_dec(v_h__16_1478_);
lean_dec(v_h__14_1476_);
lean_dec(v_h__13_1475_);
lean_dec(v_h__12_1474_);
lean_dec(v_h__11_1473_);
lean_dec(v_h__10_1472_);
lean_dec(v_h__9_1471_);
lean_dec(v_h__8_1470_);
lean_dec(v_h__7_1469_);
lean_dec(v_h__6_1468_);
lean_dec(v_h__5_1467_);
lean_dec(v_h__4_1466_);
lean_dec(v_h__3_1465_);
lean_dec(v_h__2_1464_);
lean_dec(v_h__1_1463_);
v_a_1514_ = lean_ctor_get(v_x_1462_, 0);
lean_inc(v_a_1514_);
v_b_1515_ = lean_ctor_get(v_x_1462_, 1);
lean_inc(v_b_1515_);
lean_dec_ref_known(v_x_1462_, 2);
v___x_1516_ = lean_apply_3(v_h__15_1477_, lean_box(0), v_a_1514_, v_b_1515_);
return v___x_1516_;
}
default: 
{
lean_object* v_a_1517_; lean_object* v_b_1518_; lean_object* v___x_1519_; 
lean_dec(v_h__15_1477_);
lean_dec(v_h__14_1476_);
lean_dec(v_h__13_1475_);
lean_dec(v_h__12_1474_);
lean_dec(v_h__11_1473_);
lean_dec(v_h__10_1472_);
lean_dec(v_h__9_1471_);
lean_dec(v_h__8_1470_);
lean_dec(v_h__7_1469_);
lean_dec(v_h__6_1468_);
lean_dec(v_h__5_1467_);
lean_dec(v_h__4_1466_);
lean_dec(v_h__3_1465_);
lean_dec(v_h__2_1464_);
lean_dec(v_h__1_1463_);
v_a_1517_ = lean_ctor_get(v_x_1462_, 0);
lean_inc(v_a_1517_);
v_b_1518_ = lean_ctor_get(v_x_1462_, 1);
lean_inc(v_b_1518_);
lean_dec_ref_known(v_x_1462_, 2);
v___x_1519_ = lean_apply_3(v_h__16_1478_, lean_box(0), v_a_1517_, v_b_1518_);
return v___x_1519_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__4_splitter___redArg___boxed(lean_object** _args){
lean_object* v_x_1520_ = _args[0];
lean_object* v_h__1_1521_ = _args[1];
lean_object* v_h__2_1522_ = _args[2];
lean_object* v_h__3_1523_ = _args[3];
lean_object* v_h__4_1524_ = _args[4];
lean_object* v_h__5_1525_ = _args[5];
lean_object* v_h__6_1526_ = _args[6];
lean_object* v_h__7_1527_ = _args[7];
lean_object* v_h__8_1528_ = _args[8];
lean_object* v_h__9_1529_ = _args[9];
lean_object* v_h__10_1530_ = _args[10];
lean_object* v_h__11_1531_ = _args[11];
lean_object* v_h__12_1532_ = _args[12];
lean_object* v_h__13_1533_ = _args[13];
lean_object* v_h__14_1534_ = _args[14];
lean_object* v_h__15_1535_ = _args[15];
lean_object* v_h__16_1536_ = _args[16];
_start:
{
lean_object* v_res_1537_; 
v_res_1537_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__4_splitter___redArg(v_x_1520_, v_h__1_1521_, v_h__2_1522_, v_h__3_1523_, v_h__4_1524_, v_h__5_1525_, v_h__6_1526_, v_h__7_1527_, v_h__8_1528_, v_h__9_1529_, v_h__10_1530_, v_h__11_1531_, v_h__12_1532_, v_h__13_1533_, v_h__14_1534_, v_h__15_1535_, v_h__16_1536_);
return v_res_1537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__4_splitter(lean_object* v_motive_1538_, lean_object* v_x_1539_, lean_object* v_x_1540_, lean_object* v_h__1_1541_, lean_object* v_h__2_1542_, lean_object* v_h__3_1543_, lean_object* v_h__4_1544_, lean_object* v_h__5_1545_, lean_object* v_h__6_1546_, lean_object* v_h__7_1547_, lean_object* v_h__8_1548_, lean_object* v_h__9_1549_, lean_object* v_h__10_1550_, lean_object* v_h__11_1551_, lean_object* v_h__12_1552_, lean_object* v_h__13_1553_, lean_object* v_h__14_1554_, lean_object* v_h__15_1555_, lean_object* v_h__16_1556_){
_start:
{
switch(lean_obj_tag(v_x_1540_))
{
case 0:
{
lean_object* v___x_1557_; 
lean_dec(v_h__16_1556_);
lean_dec(v_h__15_1555_);
lean_dec(v_h__14_1554_);
lean_dec(v_h__13_1553_);
lean_dec(v_h__12_1552_);
lean_dec(v_h__11_1551_);
lean_dec(v_h__10_1550_);
lean_dec(v_h__9_1549_);
lean_dec(v_h__8_1548_);
lean_dec(v_h__7_1547_);
lean_dec(v_h__6_1546_);
lean_dec(v_h__5_1545_);
lean_dec(v_h__4_1544_);
lean_dec(v_h__3_1543_);
lean_dec(v_h__2_1542_);
v___x_1557_ = lean_apply_1(v_h__1_1541_, lean_box(0));
return v___x_1557_;
}
case 1:
{
lean_object* v_f_1558_; lean_object* v___x_1559_; 
lean_dec(v_h__16_1556_);
lean_dec(v_h__15_1555_);
lean_dec(v_h__14_1554_);
lean_dec(v_h__13_1553_);
lean_dec(v_h__12_1552_);
lean_dec(v_h__11_1551_);
lean_dec(v_h__10_1550_);
lean_dec(v_h__9_1549_);
lean_dec(v_h__8_1548_);
lean_dec(v_h__7_1547_);
lean_dec(v_h__6_1546_);
lean_dec(v_h__5_1545_);
lean_dec(v_h__4_1544_);
lean_dec(v_h__2_1542_);
lean_dec(v_h__1_1541_);
v_f_1558_ = lean_ctor_get(v_x_1540_, 0);
lean_inc_ref(v_f_1558_);
lean_dec_ref_known(v_x_1540_, 1);
v___x_1559_ = lean_apply_2(v_h__3_1543_, lean_box(0), v_f_1558_);
return v___x_1559_;
}
case 2:
{
lean_object* v_s_1560_; lean_object* v___x_1561_; 
lean_dec(v_h__16_1556_);
lean_dec(v_h__15_1555_);
lean_dec(v_h__14_1554_);
lean_dec(v_h__13_1553_);
lean_dec(v_h__12_1552_);
lean_dec(v_h__11_1551_);
lean_dec(v_h__10_1550_);
lean_dec(v_h__9_1549_);
lean_dec(v_h__8_1548_);
lean_dec(v_h__7_1547_);
lean_dec(v_h__6_1546_);
lean_dec(v_h__5_1545_);
lean_dec(v_h__4_1544_);
lean_dec(v_h__3_1543_);
lean_dec(v_h__1_1541_);
v_s_1560_ = lean_ctor_get(v_x_1540_, 0);
lean_inc_ref(v_s_1560_);
lean_dec_ref_known(v_x_1540_, 1);
v___x_1561_ = lean_apply_2(v_h__2_1542_, lean_box(0), v_s_1560_);
return v___x_1561_;
}
case 3:
{
lean_object* v_id_1562_; lean_object* v_d_1563_; lean_object* v___x_1564_; 
lean_dec(v_h__16_1556_);
lean_dec(v_h__15_1555_);
lean_dec(v_h__14_1554_);
lean_dec(v_h__13_1553_);
lean_dec(v_h__12_1552_);
lean_dec(v_h__11_1551_);
lean_dec(v_h__10_1550_);
lean_dec(v_h__9_1549_);
lean_dec(v_h__8_1548_);
lean_dec(v_h__7_1547_);
lean_dec(v_h__5_1545_);
lean_dec(v_h__4_1544_);
lean_dec(v_h__3_1543_);
lean_dec(v_h__2_1542_);
lean_dec(v_h__1_1541_);
v_id_1562_ = lean_ctor_get(v_x_1540_, 0);
lean_inc(v_id_1562_);
v_d_1563_ = lean_ctor_get(v_x_1540_, 1);
lean_inc(v_d_1563_);
lean_dec_ref_known(v_x_1540_, 2);
v___x_1564_ = lean_apply_3(v_h__6_1546_, lean_box(0), v_id_1562_, v_d_1563_);
return v___x_1564_;
}
case 4:
{
lean_object* v_d_1565_; lean_object* v___x_1566_; 
lean_dec(v_h__16_1556_);
lean_dec(v_h__15_1555_);
lean_dec(v_h__14_1554_);
lean_dec(v_h__13_1553_);
lean_dec(v_h__12_1552_);
lean_dec(v_h__11_1551_);
lean_dec(v_h__10_1550_);
lean_dec(v_h__9_1549_);
lean_dec(v_h__8_1548_);
lean_dec(v_h__7_1547_);
lean_dec(v_h__6_1546_);
lean_dec(v_h__5_1545_);
lean_dec(v_h__3_1543_);
lean_dec(v_h__2_1542_);
lean_dec(v_h__1_1541_);
v_d_1565_ = lean_ctor_get(v_x_1540_, 0);
lean_inc(v_d_1565_);
lean_dec_ref_known(v_x_1540_, 1);
v___x_1566_ = lean_apply_2(v_h__4_1544_, lean_box(0), v_d_1565_);
return v___x_1566_;
}
case 5:
{
lean_object* v_d_1567_; lean_object* v___x_1568_; 
lean_dec(v_h__16_1556_);
lean_dec(v_h__15_1555_);
lean_dec(v_h__14_1554_);
lean_dec(v_h__13_1553_);
lean_dec(v_h__12_1552_);
lean_dec(v_h__11_1551_);
lean_dec(v_h__10_1550_);
lean_dec(v_h__9_1549_);
lean_dec(v_h__8_1548_);
lean_dec(v_h__7_1547_);
lean_dec(v_h__6_1546_);
lean_dec(v_h__4_1544_);
lean_dec(v_h__3_1543_);
lean_dec(v_h__2_1542_);
lean_dec(v_h__1_1541_);
v_d_1567_ = lean_ctor_get(v_x_1540_, 0);
lean_inc(v_d_1567_);
lean_dec_ref_known(v_x_1540_, 1);
v___x_1568_ = lean_apply_2(v_h__5_1545_, lean_box(0), v_d_1567_);
return v___x_1568_;
}
case 6:
{
lean_object* v_n_1569_; uint8_t v_isCumulative_1570_; lean_object* v_d_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
lean_dec(v_h__16_1556_);
lean_dec(v_h__15_1555_);
lean_dec(v_h__14_1554_);
lean_dec(v_h__13_1553_);
lean_dec(v_h__12_1552_);
lean_dec(v_h__11_1551_);
lean_dec(v_h__10_1550_);
lean_dec(v_h__9_1549_);
lean_dec(v_h__8_1548_);
lean_dec(v_h__6_1546_);
lean_dec(v_h__5_1545_);
lean_dec(v_h__4_1544_);
lean_dec(v_h__3_1543_);
lean_dec(v_h__2_1542_);
lean_dec(v_h__1_1541_);
v_n_1569_ = lean_ctor_get(v_x_1540_, 0);
lean_inc(v_n_1569_);
v_isCumulative_1570_ = lean_ctor_get_uint8(v_x_1540_, sizeof(void*)*2);
v_d_1571_ = lean_ctor_get(v_x_1540_, 1);
lean_inc(v_d_1571_);
lean_dec_ref_known(v_x_1540_, 2);
v___x_1572_ = lean_box(v_isCumulative_1570_);
v___x_1573_ = lean_apply_4(v_h__7_1547_, lean_box(0), v_n_1569_, v___x_1572_, v_d_1571_);
return v___x_1573_;
}
case 7:
{
lean_object* v_d_1574_; lean_object* v___x_1575_; 
lean_dec(v_h__16_1556_);
lean_dec(v_h__15_1555_);
lean_dec(v_h__14_1554_);
lean_dec(v_h__13_1553_);
lean_dec(v_h__12_1552_);
lean_dec(v_h__11_1551_);
lean_dec(v_h__10_1550_);
lean_dec(v_h__9_1549_);
lean_dec(v_h__7_1547_);
lean_dec(v_h__6_1546_);
lean_dec(v_h__5_1545_);
lean_dec(v_h__4_1544_);
lean_dec(v_h__3_1543_);
lean_dec(v_h__2_1542_);
lean_dec(v_h__1_1541_);
v_d_1574_ = lean_ctor_get(v_x_1540_, 0);
lean_inc(v_d_1574_);
lean_dec_ref_known(v_x_1540_, 1);
v___x_1575_ = lean_apply_2(v_h__8_1548_, lean_box(0), v_d_1574_);
return v___x_1575_;
}
case 8:
{
uint8_t v_onlyNonCumulative_1576_; lean_object* v_d_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
lean_dec(v_h__16_1556_);
lean_dec(v_h__15_1555_);
lean_dec(v_h__14_1554_);
lean_dec(v_h__13_1553_);
lean_dec(v_h__12_1552_);
lean_dec(v_h__11_1551_);
lean_dec(v_h__10_1550_);
lean_dec(v_h__8_1548_);
lean_dec(v_h__7_1547_);
lean_dec(v_h__6_1546_);
lean_dec(v_h__5_1545_);
lean_dec(v_h__4_1544_);
lean_dec(v_h__3_1543_);
lean_dec(v_h__2_1542_);
lean_dec(v_h__1_1541_);
v_onlyNonCumulative_1576_ = lean_ctor_get_uint8(v_x_1540_, sizeof(void*)*1);
v_d_1577_ = lean_ctor_get(v_x_1540_, 0);
lean_inc(v_d_1577_);
lean_dec_ref_known(v_x_1540_, 1);
v___x_1578_ = lean_box(v_onlyNonCumulative_1576_);
v___x_1579_ = lean_apply_3(v_h__9_1549_, lean_box(0), v___x_1578_, v_d_1577_);
return v___x_1579_;
}
case 9:
{
lean_object* v_d_1580_; lean_object* v___x_1581_; 
lean_dec(v_h__16_1556_);
lean_dec(v_h__15_1555_);
lean_dec(v_h__14_1554_);
lean_dec(v_h__13_1553_);
lean_dec(v_h__12_1552_);
lean_dec(v_h__11_1551_);
lean_dec(v_h__9_1549_);
lean_dec(v_h__8_1548_);
lean_dec(v_h__7_1547_);
lean_dec(v_h__6_1546_);
lean_dec(v_h__5_1545_);
lean_dec(v_h__4_1544_);
lean_dec(v_h__3_1543_);
lean_dec(v_h__2_1542_);
lean_dec(v_h__1_1541_);
v_d_1580_ = lean_ctor_get(v_x_1540_, 0);
lean_inc(v_d_1580_);
lean_dec_ref_known(v_x_1540_, 1);
v___x_1581_ = lean_apply_2(v_h__10_1550_, lean_box(0), v_d_1580_);
return v___x_1581_;
}
case 10:
{
lean_object* v_d_1582_; lean_object* v___x_1583_; 
lean_dec(v_h__16_1556_);
lean_dec(v_h__15_1555_);
lean_dec(v_h__14_1554_);
lean_dec(v_h__13_1553_);
lean_dec(v_h__12_1552_);
lean_dec(v_h__10_1550_);
lean_dec(v_h__9_1549_);
lean_dec(v_h__8_1548_);
lean_dec(v_h__7_1547_);
lean_dec(v_h__6_1546_);
lean_dec(v_h__5_1545_);
lean_dec(v_h__4_1544_);
lean_dec(v_h__3_1543_);
lean_dec(v_h__2_1542_);
lean_dec(v_h__1_1541_);
v_d_1582_ = lean_ctor_get(v_x_1540_, 0);
lean_inc(v_d_1582_);
lean_dec_ref_known(v_x_1540_, 1);
v___x_1583_ = lean_apply_2(v_h__11_1551_, lean_box(0), v_d_1582_);
return v___x_1583_;
}
case 11:
{
lean_object* v_d_1584_; lean_object* v___x_1585_; 
lean_dec(v_h__16_1556_);
lean_dec(v_h__15_1555_);
lean_dec(v_h__14_1554_);
lean_dec(v_h__13_1553_);
lean_dec(v_h__11_1551_);
lean_dec(v_h__10_1550_);
lean_dec(v_h__9_1549_);
lean_dec(v_h__8_1548_);
lean_dec(v_h__7_1547_);
lean_dec(v_h__6_1546_);
lean_dec(v_h__5_1545_);
lean_dec(v_h__4_1544_);
lean_dec(v_h__3_1543_);
lean_dec(v_h__2_1542_);
lean_dec(v_h__1_1541_);
v_d_1584_ = lean_ctor_get(v_x_1540_, 0);
lean_inc(v_d_1584_);
lean_dec_ref_known(v_x_1540_, 1);
v___x_1585_ = lean_apply_2(v_h__12_1552_, lean_box(0), v_d_1584_);
return v___x_1585_;
}
case 12:
{
lean_object* v_p_1586_; lean_object* v_d_1587_; lean_object* v___x_1588_; 
lean_dec(v_h__16_1556_);
lean_dec(v_h__15_1555_);
lean_dec(v_h__14_1554_);
lean_dec(v_h__12_1552_);
lean_dec(v_h__11_1551_);
lean_dec(v_h__10_1550_);
lean_dec(v_h__9_1549_);
lean_dec(v_h__8_1548_);
lean_dec(v_h__7_1547_);
lean_dec(v_h__6_1546_);
lean_dec(v_h__5_1545_);
lean_dec(v_h__4_1544_);
lean_dec(v_h__3_1543_);
lean_dec(v_h__2_1542_);
lean_dec(v_h__1_1541_);
v_p_1586_ = lean_ctor_get(v_x_1540_, 0);
lean_inc_ref(v_p_1586_);
v_d_1587_ = lean_ctor_get(v_x_1540_, 1);
lean_inc(v_d_1587_);
lean_dec_ref_known(v_x_1540_, 2);
v___x_1588_ = lean_apply_3(v_h__13_1553_, lean_box(0), v_p_1586_, v_d_1587_);
return v___x_1588_;
}
case 13:
{
lean_object* v_cost_1589_; lean_object* v_d_1590_; lean_object* v___x_1591_; 
lean_dec(v_h__16_1556_);
lean_dec(v_h__15_1555_);
lean_dec(v_h__13_1553_);
lean_dec(v_h__12_1552_);
lean_dec(v_h__11_1551_);
lean_dec(v_h__10_1550_);
lean_dec(v_h__9_1549_);
lean_dec(v_h__8_1548_);
lean_dec(v_h__7_1547_);
lean_dec(v_h__6_1546_);
lean_dec(v_h__5_1545_);
lean_dec(v_h__4_1544_);
lean_dec(v_h__3_1543_);
lean_dec(v_h__2_1542_);
lean_dec(v_h__1_1541_);
v_cost_1589_ = lean_ctor_get(v_x_1540_, 0);
lean_inc(v_cost_1589_);
v_d_1590_ = lean_ctor_get(v_x_1540_, 1);
lean_inc(v_d_1590_);
lean_dec_ref_known(v_x_1540_, 2);
v___x_1591_ = lean_apply_3(v_h__14_1554_, lean_box(0), v_cost_1589_, v_d_1590_);
return v___x_1591_;
}
case 14:
{
lean_object* v_a_1592_; lean_object* v_b_1593_; lean_object* v___x_1594_; 
lean_dec(v_h__16_1556_);
lean_dec(v_h__14_1554_);
lean_dec(v_h__13_1553_);
lean_dec(v_h__12_1552_);
lean_dec(v_h__11_1551_);
lean_dec(v_h__10_1550_);
lean_dec(v_h__9_1549_);
lean_dec(v_h__8_1548_);
lean_dec(v_h__7_1547_);
lean_dec(v_h__6_1546_);
lean_dec(v_h__5_1545_);
lean_dec(v_h__4_1544_);
lean_dec(v_h__3_1543_);
lean_dec(v_h__2_1542_);
lean_dec(v_h__1_1541_);
v_a_1592_ = lean_ctor_get(v_x_1540_, 0);
lean_inc(v_a_1592_);
v_b_1593_ = lean_ctor_get(v_x_1540_, 1);
lean_inc(v_b_1593_);
lean_dec_ref_known(v_x_1540_, 2);
v___x_1594_ = lean_apply_3(v_h__15_1555_, lean_box(0), v_a_1592_, v_b_1593_);
return v___x_1594_;
}
default: 
{
lean_object* v_a_1595_; lean_object* v_b_1596_; lean_object* v___x_1597_; 
lean_dec(v_h__15_1555_);
lean_dec(v_h__14_1554_);
lean_dec(v_h__13_1553_);
lean_dec(v_h__12_1552_);
lean_dec(v_h__11_1551_);
lean_dec(v_h__10_1550_);
lean_dec(v_h__9_1549_);
lean_dec(v_h__8_1548_);
lean_dec(v_h__7_1547_);
lean_dec(v_h__6_1546_);
lean_dec(v_h__5_1545_);
lean_dec(v_h__4_1544_);
lean_dec(v_h__3_1543_);
lean_dec(v_h__2_1542_);
lean_dec(v_h__1_1541_);
v_a_1595_ = lean_ctor_get(v_x_1540_, 0);
lean_inc(v_a_1595_);
v_b_1596_ = lean_ctor_get(v_x_1540_, 1);
lean_inc(v_b_1596_);
lean_dec_ref_known(v_x_1540_, 2);
v___x_1597_ = lean_apply_3(v_h__16_1556_, lean_box(0), v_a_1595_, v_b_1596_);
return v___x_1597_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__4_splitter___boxed(lean_object** _args){
lean_object* v_motive_1598_ = _args[0];
lean_object* v_x_1599_ = _args[1];
lean_object* v_x_1600_ = _args[2];
lean_object* v_h__1_1601_ = _args[3];
lean_object* v_h__2_1602_ = _args[4];
lean_object* v_h__3_1603_ = _args[5];
lean_object* v_h__4_1604_ = _args[6];
lean_object* v_h__5_1605_ = _args[7];
lean_object* v_h__6_1606_ = _args[8];
lean_object* v_h__7_1607_ = _args[9];
lean_object* v_h__8_1608_ = _args[10];
lean_object* v_h__9_1609_ = _args[11];
lean_object* v_h__10_1610_ = _args[12];
lean_object* v_h__11_1611_ = _args[13];
lean_object* v_h__12_1612_ = _args[14];
lean_object* v_h__13_1613_ = _args[15];
lean_object* v_h__14_1614_ = _args[16];
lean_object* v_h__15_1615_ = _args[17];
lean_object* v_h__16_1616_ = _args[18];
_start:
{
lean_object* v_res_1617_; 
v_res_1617_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__4_splitter(v_motive_1598_, v_x_1599_, v_x_1600_, v_h__1_1601_, v_h__2_1602_, v_h__3_1603_, v_h__4_1604_, v_h__5_1605_, v_h__6_1606_, v_h__7_1607_, v_h__8_1608_, v_h__9_1609_, v_h__10_1610_, v_h__11_1611_, v_h__12_1612_, v_h__13_1613_, v_h__14_1614_, v_h__15_1615_, v_h__16_1616_);
return v_res_1617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__1_splitter___redArg(uint8_t v_x_1618_, lean_object* v_h__1_1619_, lean_object* v_h__2_1620_, lean_object* v_h__3_1621_, lean_object* v_h__4_1622_, lean_object* v_h__5_1623_){
_start:
{
switch(v_x_1618_)
{
case 0:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; 
lean_dec(v_h__5_1623_);
lean_dec(v_h__4_1622_);
lean_dec(v_h__3_1621_);
lean_dec(v_h__2_1620_);
v___x_1624_ = lean_box(0);
v___x_1625_ = lean_apply_1(v_h__1_1619_, v___x_1624_);
return v___x_1625_;
}
case 1:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; 
lean_dec(v_h__5_1623_);
lean_dec(v_h__4_1622_);
lean_dec(v_h__3_1621_);
lean_dec(v_h__1_1619_);
v___x_1626_ = lean_box(0);
v___x_1627_ = lean_apply_1(v_h__2_1620_, v___x_1626_);
return v___x_1627_;
}
case 2:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
lean_dec(v_h__5_1623_);
lean_dec(v_h__4_1622_);
lean_dec(v_h__2_1620_);
lean_dec(v_h__1_1619_);
v___x_1628_ = lean_box(0);
v___x_1629_ = lean_apply_1(v_h__3_1621_, v___x_1628_);
return v___x_1629_;
}
case 3:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; 
lean_dec(v_h__5_1623_);
lean_dec(v_h__3_1621_);
lean_dec(v_h__2_1620_);
lean_dec(v_h__1_1619_);
v___x_1630_ = lean_box(0);
v___x_1631_ = lean_apply_1(v_h__4_1622_, v___x_1630_);
return v___x_1631_;
}
default: 
{
lean_object* v___x_1632_; lean_object* v___x_1633_; 
lean_dec(v_h__4_1622_);
lean_dec(v_h__3_1621_);
lean_dec(v_h__2_1620_);
lean_dec(v_h__1_1619_);
v___x_1632_ = lean_box(0);
v___x_1633_ = lean_apply_1(v_h__5_1623_, v___x_1632_);
return v___x_1633_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__1_splitter___redArg___boxed(lean_object* v_x_1634_, lean_object* v_h__1_1635_, lean_object* v_h__2_1636_, lean_object* v_h__3_1637_, lean_object* v_h__4_1638_, lean_object* v_h__5_1639_){
_start:
{
uint8_t v_x_51__boxed_1640_; lean_object* v_res_1641_; 
v_x_51__boxed_1640_ = lean_unbox(v_x_1634_);
v_res_1641_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__1_splitter___redArg(v_x_51__boxed_1640_, v_h__1_1635_, v_h__2_1636_, v_h__3_1637_, v_h__4_1638_, v_h__5_1639_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__1_splitter(lean_object* v_motive_1642_, uint8_t v_x_1643_, lean_object* v_h__1_1644_, lean_object* v_h__2_1645_, lean_object* v_h__3_1646_, lean_object* v_h__4_1647_, lean_object* v_h__5_1648_){
_start:
{
switch(v_x_1643_)
{
case 0:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; 
lean_dec(v_h__5_1648_);
lean_dec(v_h__4_1647_);
lean_dec(v_h__3_1646_);
lean_dec(v_h__2_1645_);
v___x_1649_ = lean_box(0);
v___x_1650_ = lean_apply_1(v_h__1_1644_, v___x_1649_);
return v___x_1650_;
}
case 1:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; 
lean_dec(v_h__5_1648_);
lean_dec(v_h__4_1647_);
lean_dec(v_h__3_1646_);
lean_dec(v_h__1_1644_);
v___x_1651_ = lean_box(0);
v___x_1652_ = lean_apply_1(v_h__2_1645_, v___x_1651_);
return v___x_1652_;
}
case 2:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; 
lean_dec(v_h__5_1648_);
lean_dec(v_h__4_1647_);
lean_dec(v_h__2_1645_);
lean_dec(v_h__1_1644_);
v___x_1653_ = lean_box(0);
v___x_1654_ = lean_apply_1(v_h__3_1646_, v___x_1653_);
return v___x_1654_;
}
case 3:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; 
lean_dec(v_h__5_1648_);
lean_dec(v_h__3_1646_);
lean_dec(v_h__2_1645_);
lean_dec(v_h__1_1644_);
v___x_1655_ = lean_box(0);
v___x_1656_ = lean_apply_1(v_h__4_1647_, v___x_1655_);
return v___x_1656_;
}
default: 
{
lean_object* v___x_1657_; lean_object* v___x_1658_; 
lean_dec(v_h__4_1647_);
lean_dec(v_h__3_1646_);
lean_dec(v_h__2_1645_);
lean_dec(v_h__1_1644_);
v___x_1657_ = lean_box(0);
v___x_1658_ = lean_apply_1(v_h__5_1648_, v___x_1657_);
return v___x_1658_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__1_splitter___boxed(lean_object* v_motive_1659_, lean_object* v_x_1660_, lean_object* v_h__1_1661_, lean_object* v_h__2_1662_, lean_object* v_h__3_1663_, lean_object* v_h__4_1664_, lean_object* v_h__5_1665_){
_start:
{
uint8_t v_x_74__boxed_1666_; lean_object* v_res_1667_; 
v_x_74__boxed_1666_ = lean_unbox(v_x_1660_);
v_res_1667_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__1_splitter(v_motive_1659_, v_x_74__boxed_1666_, v_h__1_1661_, v_h__2_1662_, v_h__3_1663_, v_h__4_1664_, v_h__5_1665_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_casesOn___override___redArg(lean_object* v_t_1668_, lean_object* v_failure_1669_, lean_object* v_newline_1670_, lean_object* v_text_1671_, lean_object* v_tagged_1672_, lean_object* v_flattened_1673_, lean_object* v_unflattenable_1674_, lean_object* v_indented_1675_, lean_object* v_aligned_1676_, lean_object* v_unindented_1677_, lean_object* v_final_1678_, lean_object* v_initial_1679_, lean_object* v_free_1680_, lean_object* v_guarded_1681_, lean_object* v_costing_1682_, lean_object* v_either_1683_, lean_object* v_append_1684_){
_start:
{
switch(lean_obj_tag(v_t_1668_))
{
case 0:
{
lean_dec(v_append_1684_);
lean_dec(v_either_1683_);
lean_dec(v_costing_1682_);
lean_dec(v_guarded_1681_);
lean_dec(v_free_1680_);
lean_dec(v_initial_1679_);
lean_dec(v_final_1678_);
lean_dec(v_unindented_1677_);
lean_dec(v_aligned_1676_);
lean_dec(v_indented_1675_);
lean_dec(v_unflattenable_1674_);
lean_dec(v_flattened_1673_);
lean_dec(v_tagged_1672_);
lean_dec(v_text_1671_);
lean_dec(v_newline_1670_);
lean_inc(v_failure_1669_);
return v_failure_1669_;
}
case 1:
{
lean_object* v_f_1685_; lean_object* v___x_1686_; 
lean_dec(v_append_1684_);
lean_dec(v_either_1683_);
lean_dec(v_costing_1682_);
lean_dec(v_guarded_1681_);
lean_dec(v_free_1680_);
lean_dec(v_initial_1679_);
lean_dec(v_final_1678_);
lean_dec(v_unindented_1677_);
lean_dec(v_aligned_1676_);
lean_dec(v_indented_1675_);
lean_dec(v_unflattenable_1674_);
lean_dec(v_flattened_1673_);
lean_dec(v_tagged_1672_);
lean_dec(v_text_1671_);
v_f_1685_ = lean_ctor_get(v_t_1668_, 1);
lean_inc_ref(v_f_1685_);
lean_dec_ref_known(v_t_1668_, 2);
v___x_1686_ = lean_apply_1(v_newline_1670_, v_f_1685_);
return v___x_1686_;
}
case 2:
{
lean_object* v_s_1687_; lean_object* v___x_1688_; 
lean_dec(v_append_1684_);
lean_dec(v_either_1683_);
lean_dec(v_costing_1682_);
lean_dec(v_guarded_1681_);
lean_dec(v_free_1680_);
lean_dec(v_initial_1679_);
lean_dec(v_final_1678_);
lean_dec(v_unindented_1677_);
lean_dec(v_aligned_1676_);
lean_dec(v_indented_1675_);
lean_dec(v_unflattenable_1674_);
lean_dec(v_flattened_1673_);
lean_dec(v_tagged_1672_);
lean_dec(v_newline_1670_);
v_s_1687_ = lean_ctor_get(v_t_1668_, 1);
lean_inc_ref(v_s_1687_);
lean_dec_ref_known(v_t_1668_, 2);
v___x_1688_ = lean_apply_1(v_text_1671_, v_s_1687_);
return v___x_1688_;
}
case 3:
{
lean_object* v_id_1689_; lean_object* v_d_1690_; lean_object* v___x_1691_; 
lean_dec(v_append_1684_);
lean_dec(v_either_1683_);
lean_dec(v_costing_1682_);
lean_dec(v_guarded_1681_);
lean_dec(v_free_1680_);
lean_dec(v_initial_1679_);
lean_dec(v_final_1678_);
lean_dec(v_unindented_1677_);
lean_dec(v_aligned_1676_);
lean_dec(v_indented_1675_);
lean_dec(v_unflattenable_1674_);
lean_dec(v_flattened_1673_);
lean_dec(v_text_1671_);
lean_dec(v_newline_1670_);
v_id_1689_ = lean_ctor_get(v_t_1668_, 1);
lean_inc(v_id_1689_);
v_d_1690_ = lean_ctor_get(v_t_1668_, 2);
lean_inc(v_d_1690_);
lean_dec_ref_known(v_t_1668_, 3);
v___x_1691_ = lean_apply_2(v_tagged_1672_, v_id_1689_, v_d_1690_);
return v___x_1691_;
}
case 4:
{
lean_object* v_d_1692_; lean_object* v___x_1693_; 
lean_dec(v_append_1684_);
lean_dec(v_either_1683_);
lean_dec(v_costing_1682_);
lean_dec(v_guarded_1681_);
lean_dec(v_free_1680_);
lean_dec(v_initial_1679_);
lean_dec(v_final_1678_);
lean_dec(v_unindented_1677_);
lean_dec(v_aligned_1676_);
lean_dec(v_indented_1675_);
lean_dec(v_unflattenable_1674_);
lean_dec(v_tagged_1672_);
lean_dec(v_text_1671_);
lean_dec(v_newline_1670_);
v_d_1692_ = lean_ctor_get(v_t_1668_, 1);
lean_inc(v_d_1692_);
lean_dec_ref_known(v_t_1668_, 2);
v___x_1693_ = lean_apply_1(v_flattened_1673_, v_d_1692_);
return v___x_1693_;
}
case 5:
{
lean_object* v_d_1694_; lean_object* v___x_1695_; 
lean_dec(v_append_1684_);
lean_dec(v_either_1683_);
lean_dec(v_costing_1682_);
lean_dec(v_guarded_1681_);
lean_dec(v_free_1680_);
lean_dec(v_initial_1679_);
lean_dec(v_final_1678_);
lean_dec(v_unindented_1677_);
lean_dec(v_aligned_1676_);
lean_dec(v_indented_1675_);
lean_dec(v_flattened_1673_);
lean_dec(v_tagged_1672_);
lean_dec(v_text_1671_);
lean_dec(v_newline_1670_);
v_d_1694_ = lean_ctor_get(v_t_1668_, 1);
lean_inc(v_d_1694_);
lean_dec_ref_known(v_t_1668_, 2);
v___x_1695_ = lean_apply_1(v_unflattenable_1674_, v_d_1694_);
return v___x_1695_;
}
case 6:
{
lean_object* v_n_1696_; uint8_t v_isCumulative_1697_; lean_object* v_d_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
lean_dec(v_append_1684_);
lean_dec(v_either_1683_);
lean_dec(v_costing_1682_);
lean_dec(v_guarded_1681_);
lean_dec(v_free_1680_);
lean_dec(v_initial_1679_);
lean_dec(v_final_1678_);
lean_dec(v_unindented_1677_);
lean_dec(v_aligned_1676_);
lean_dec(v_unflattenable_1674_);
lean_dec(v_flattened_1673_);
lean_dec(v_tagged_1672_);
lean_dec(v_text_1671_);
lean_dec(v_newline_1670_);
v_n_1696_ = lean_ctor_get(v_t_1668_, 1);
lean_inc(v_n_1696_);
v_isCumulative_1697_ = lean_ctor_get_uint8(v_t_1668_, sizeof(void*)*3 + 7);
v_d_1698_ = lean_ctor_get(v_t_1668_, 2);
lean_inc(v_d_1698_);
lean_dec_ref_known(v_t_1668_, 3);
v___x_1699_ = lean_box(v_isCumulative_1697_);
v___x_1700_ = lean_apply_3(v_indented_1675_, v_n_1696_, v___x_1699_, v_d_1698_);
return v___x_1700_;
}
case 7:
{
lean_object* v_d_1701_; lean_object* v___x_1702_; 
lean_dec(v_append_1684_);
lean_dec(v_either_1683_);
lean_dec(v_costing_1682_);
lean_dec(v_guarded_1681_);
lean_dec(v_free_1680_);
lean_dec(v_initial_1679_);
lean_dec(v_final_1678_);
lean_dec(v_unindented_1677_);
lean_dec(v_indented_1675_);
lean_dec(v_unflattenable_1674_);
lean_dec(v_flattened_1673_);
lean_dec(v_tagged_1672_);
lean_dec(v_text_1671_);
lean_dec(v_newline_1670_);
v_d_1701_ = lean_ctor_get(v_t_1668_, 1);
lean_inc(v_d_1701_);
lean_dec_ref_known(v_t_1668_, 2);
v___x_1702_ = lean_apply_1(v_aligned_1676_, v_d_1701_);
return v___x_1702_;
}
case 8:
{
uint8_t v_onlyNonCumulative_1703_; lean_object* v_d_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
lean_dec(v_append_1684_);
lean_dec(v_either_1683_);
lean_dec(v_costing_1682_);
lean_dec(v_guarded_1681_);
lean_dec(v_free_1680_);
lean_dec(v_initial_1679_);
lean_dec(v_final_1678_);
lean_dec(v_aligned_1676_);
lean_dec(v_indented_1675_);
lean_dec(v_unflattenable_1674_);
lean_dec(v_flattened_1673_);
lean_dec(v_tagged_1672_);
lean_dec(v_text_1671_);
lean_dec(v_newline_1670_);
v_onlyNonCumulative_1703_ = lean_ctor_get_uint8(v_t_1668_, sizeof(void*)*2 + 7);
v_d_1704_ = lean_ctor_get(v_t_1668_, 1);
lean_inc(v_d_1704_);
lean_dec_ref_known(v_t_1668_, 2);
v___x_1705_ = lean_box(v_onlyNonCumulative_1703_);
v___x_1706_ = lean_apply_2(v_unindented_1677_, v___x_1705_, v_d_1704_);
return v___x_1706_;
}
case 9:
{
lean_object* v_d_1707_; lean_object* v___x_1708_; 
lean_dec(v_append_1684_);
lean_dec(v_either_1683_);
lean_dec(v_costing_1682_);
lean_dec(v_guarded_1681_);
lean_dec(v_free_1680_);
lean_dec(v_initial_1679_);
lean_dec(v_unindented_1677_);
lean_dec(v_aligned_1676_);
lean_dec(v_indented_1675_);
lean_dec(v_unflattenable_1674_);
lean_dec(v_flattened_1673_);
lean_dec(v_tagged_1672_);
lean_dec(v_text_1671_);
lean_dec(v_newline_1670_);
v_d_1707_ = lean_ctor_get(v_t_1668_, 1);
lean_inc(v_d_1707_);
lean_dec_ref_known(v_t_1668_, 2);
v___x_1708_ = lean_apply_1(v_final_1678_, v_d_1707_);
return v___x_1708_;
}
case 10:
{
lean_object* v_d_1709_; lean_object* v___x_1710_; 
lean_dec(v_append_1684_);
lean_dec(v_either_1683_);
lean_dec(v_costing_1682_);
lean_dec(v_guarded_1681_);
lean_dec(v_free_1680_);
lean_dec(v_final_1678_);
lean_dec(v_unindented_1677_);
lean_dec(v_aligned_1676_);
lean_dec(v_indented_1675_);
lean_dec(v_unflattenable_1674_);
lean_dec(v_flattened_1673_);
lean_dec(v_tagged_1672_);
lean_dec(v_text_1671_);
lean_dec(v_newline_1670_);
v_d_1709_ = lean_ctor_get(v_t_1668_, 1);
lean_inc(v_d_1709_);
lean_dec_ref_known(v_t_1668_, 2);
v___x_1710_ = lean_apply_1(v_initial_1679_, v_d_1709_);
return v___x_1710_;
}
case 11:
{
lean_object* v_d_1711_; lean_object* v___x_1712_; 
lean_dec(v_append_1684_);
lean_dec(v_either_1683_);
lean_dec(v_costing_1682_);
lean_dec(v_guarded_1681_);
lean_dec(v_initial_1679_);
lean_dec(v_final_1678_);
lean_dec(v_unindented_1677_);
lean_dec(v_aligned_1676_);
lean_dec(v_indented_1675_);
lean_dec(v_unflattenable_1674_);
lean_dec(v_flattened_1673_);
lean_dec(v_tagged_1672_);
lean_dec(v_text_1671_);
lean_dec(v_newline_1670_);
v_d_1711_ = lean_ctor_get(v_t_1668_, 1);
lean_inc(v_d_1711_);
lean_dec_ref_known(v_t_1668_, 2);
v___x_1712_ = lean_apply_1(v_free_1680_, v_d_1711_);
return v___x_1712_;
}
case 12:
{
lean_object* v_p_1713_; lean_object* v_d_1714_; lean_object* v___x_1715_; 
lean_dec(v_append_1684_);
lean_dec(v_either_1683_);
lean_dec(v_costing_1682_);
lean_dec(v_free_1680_);
lean_dec(v_initial_1679_);
lean_dec(v_final_1678_);
lean_dec(v_unindented_1677_);
lean_dec(v_aligned_1676_);
lean_dec(v_indented_1675_);
lean_dec(v_unflattenable_1674_);
lean_dec(v_flattened_1673_);
lean_dec(v_tagged_1672_);
lean_dec(v_text_1671_);
lean_dec(v_newline_1670_);
v_p_1713_ = lean_ctor_get(v_t_1668_, 1);
lean_inc_ref(v_p_1713_);
v_d_1714_ = lean_ctor_get(v_t_1668_, 2);
lean_inc(v_d_1714_);
lean_dec_ref_known(v_t_1668_, 3);
v___x_1715_ = lean_apply_2(v_guarded_1681_, v_p_1713_, v_d_1714_);
return v___x_1715_;
}
case 13:
{
lean_object* v_cost_1716_; lean_object* v_d_1717_; lean_object* v___x_1718_; 
lean_dec(v_append_1684_);
lean_dec(v_either_1683_);
lean_dec(v_guarded_1681_);
lean_dec(v_free_1680_);
lean_dec(v_initial_1679_);
lean_dec(v_final_1678_);
lean_dec(v_unindented_1677_);
lean_dec(v_aligned_1676_);
lean_dec(v_indented_1675_);
lean_dec(v_unflattenable_1674_);
lean_dec(v_flattened_1673_);
lean_dec(v_tagged_1672_);
lean_dec(v_text_1671_);
lean_dec(v_newline_1670_);
v_cost_1716_ = lean_ctor_get(v_t_1668_, 1);
lean_inc(v_cost_1716_);
v_d_1717_ = lean_ctor_get(v_t_1668_, 2);
lean_inc(v_d_1717_);
lean_dec_ref_known(v_t_1668_, 3);
v___x_1718_ = lean_apply_2(v_costing_1682_, v_cost_1716_, v_d_1717_);
return v___x_1718_;
}
case 14:
{
lean_object* v_a_1719_; lean_object* v_b_1720_; lean_object* v___x_1721_; 
lean_dec(v_append_1684_);
lean_dec(v_costing_1682_);
lean_dec(v_guarded_1681_);
lean_dec(v_free_1680_);
lean_dec(v_initial_1679_);
lean_dec(v_final_1678_);
lean_dec(v_unindented_1677_);
lean_dec(v_aligned_1676_);
lean_dec(v_indented_1675_);
lean_dec(v_unflattenable_1674_);
lean_dec(v_flattened_1673_);
lean_dec(v_tagged_1672_);
lean_dec(v_text_1671_);
lean_dec(v_newline_1670_);
v_a_1719_ = lean_ctor_get(v_t_1668_, 1);
lean_inc(v_a_1719_);
v_b_1720_ = lean_ctor_get(v_t_1668_, 2);
lean_inc(v_b_1720_);
lean_dec_ref_known(v_t_1668_, 3);
v___x_1721_ = lean_apply_2(v_either_1683_, v_a_1719_, v_b_1720_);
return v___x_1721_;
}
default: 
{
lean_object* v_a_1722_; lean_object* v_b_1723_; lean_object* v___x_1724_; 
lean_dec(v_either_1683_);
lean_dec(v_costing_1682_);
lean_dec(v_guarded_1681_);
lean_dec(v_free_1680_);
lean_dec(v_initial_1679_);
lean_dec(v_final_1678_);
lean_dec(v_unindented_1677_);
lean_dec(v_aligned_1676_);
lean_dec(v_indented_1675_);
lean_dec(v_unflattenable_1674_);
lean_dec(v_flattened_1673_);
lean_dec(v_tagged_1672_);
lean_dec(v_text_1671_);
lean_dec(v_newline_1670_);
v_a_1722_ = lean_ctor_get(v_t_1668_, 1);
lean_inc(v_a_1722_);
v_b_1723_ = lean_ctor_get(v_t_1668_, 2);
lean_inc(v_b_1723_);
lean_dec_ref_known(v_t_1668_, 3);
v___x_1724_ = lean_apply_2(v_append_1684_, v_a_1722_, v_b_1723_);
return v___x_1724_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_casesOn___override___redArg___boxed(lean_object** _args){
lean_object* v_t_1725_ = _args[0];
lean_object* v_failure_1726_ = _args[1];
lean_object* v_newline_1727_ = _args[2];
lean_object* v_text_1728_ = _args[3];
lean_object* v_tagged_1729_ = _args[4];
lean_object* v_flattened_1730_ = _args[5];
lean_object* v_unflattenable_1731_ = _args[6];
lean_object* v_indented_1732_ = _args[7];
lean_object* v_aligned_1733_ = _args[8];
lean_object* v_unindented_1734_ = _args[9];
lean_object* v_final_1735_ = _args[10];
lean_object* v_initial_1736_ = _args[11];
lean_object* v_free_1737_ = _args[12];
lean_object* v_guarded_1738_ = _args[13];
lean_object* v_costing_1739_ = _args[14];
lean_object* v_either_1740_ = _args[15];
lean_object* v_append_1741_ = _args[16];
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l_Lean_Fmt_Doc_casesOn___override___redArg(v_t_1725_, v_failure_1726_, v_newline_1727_, v_text_1728_, v_tagged_1729_, v_flattened_1730_, v_unflattenable_1731_, v_indented_1732_, v_aligned_1733_, v_unindented_1734_, v_final_1735_, v_initial_1736_, v_free_1737_, v_guarded_1738_, v_costing_1739_, v_either_1740_, v_append_1741_);
lean_dec(v_failure_1726_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_casesOn___override(lean_object* v_00_u03c4_1743_, lean_object* v_motive_1744_, lean_object* v_t_1745_, lean_object* v_failure_1746_, lean_object* v_newline_1747_, lean_object* v_text_1748_, lean_object* v_tagged_1749_, lean_object* v_flattened_1750_, lean_object* v_unflattenable_1751_, lean_object* v_indented_1752_, lean_object* v_aligned_1753_, lean_object* v_unindented_1754_, lean_object* v_final_1755_, lean_object* v_initial_1756_, lean_object* v_free_1757_, lean_object* v_guarded_1758_, lean_object* v_costing_1759_, lean_object* v_either_1760_, lean_object* v_append_1761_){
_start:
{
switch(lean_obj_tag(v_t_1745_))
{
case 0:
{
lean_dec(v_append_1761_);
lean_dec(v_either_1760_);
lean_dec(v_costing_1759_);
lean_dec(v_guarded_1758_);
lean_dec(v_free_1757_);
lean_dec(v_initial_1756_);
lean_dec(v_final_1755_);
lean_dec(v_unindented_1754_);
lean_dec(v_aligned_1753_);
lean_dec(v_indented_1752_);
lean_dec(v_unflattenable_1751_);
lean_dec(v_flattened_1750_);
lean_dec(v_tagged_1749_);
lean_dec(v_text_1748_);
lean_dec(v_newline_1747_);
lean_inc(v_failure_1746_);
return v_failure_1746_;
}
case 1:
{
lean_object* v_f_1762_; lean_object* v___x_1763_; 
lean_dec(v_append_1761_);
lean_dec(v_either_1760_);
lean_dec(v_costing_1759_);
lean_dec(v_guarded_1758_);
lean_dec(v_free_1757_);
lean_dec(v_initial_1756_);
lean_dec(v_final_1755_);
lean_dec(v_unindented_1754_);
lean_dec(v_aligned_1753_);
lean_dec(v_indented_1752_);
lean_dec(v_unflattenable_1751_);
lean_dec(v_flattened_1750_);
lean_dec(v_tagged_1749_);
lean_dec(v_text_1748_);
v_f_1762_ = lean_ctor_get(v_t_1745_, 1);
lean_inc_ref(v_f_1762_);
lean_dec_ref_known(v_t_1745_, 2);
v___x_1763_ = lean_apply_1(v_newline_1747_, v_f_1762_);
return v___x_1763_;
}
case 2:
{
lean_object* v_s_1764_; lean_object* v___x_1765_; 
lean_dec(v_append_1761_);
lean_dec(v_either_1760_);
lean_dec(v_costing_1759_);
lean_dec(v_guarded_1758_);
lean_dec(v_free_1757_);
lean_dec(v_initial_1756_);
lean_dec(v_final_1755_);
lean_dec(v_unindented_1754_);
lean_dec(v_aligned_1753_);
lean_dec(v_indented_1752_);
lean_dec(v_unflattenable_1751_);
lean_dec(v_flattened_1750_);
lean_dec(v_tagged_1749_);
lean_dec(v_newline_1747_);
v_s_1764_ = lean_ctor_get(v_t_1745_, 1);
lean_inc_ref(v_s_1764_);
lean_dec_ref_known(v_t_1745_, 2);
v___x_1765_ = lean_apply_1(v_text_1748_, v_s_1764_);
return v___x_1765_;
}
case 3:
{
lean_object* v_id_1766_; lean_object* v_d_1767_; lean_object* v___x_1768_; 
lean_dec(v_append_1761_);
lean_dec(v_either_1760_);
lean_dec(v_costing_1759_);
lean_dec(v_guarded_1758_);
lean_dec(v_free_1757_);
lean_dec(v_initial_1756_);
lean_dec(v_final_1755_);
lean_dec(v_unindented_1754_);
lean_dec(v_aligned_1753_);
lean_dec(v_indented_1752_);
lean_dec(v_unflattenable_1751_);
lean_dec(v_flattened_1750_);
lean_dec(v_text_1748_);
lean_dec(v_newline_1747_);
v_id_1766_ = lean_ctor_get(v_t_1745_, 1);
lean_inc(v_id_1766_);
v_d_1767_ = lean_ctor_get(v_t_1745_, 2);
lean_inc(v_d_1767_);
lean_dec_ref_known(v_t_1745_, 3);
v___x_1768_ = lean_apply_2(v_tagged_1749_, v_id_1766_, v_d_1767_);
return v___x_1768_;
}
case 4:
{
lean_object* v_d_1769_; lean_object* v___x_1770_; 
lean_dec(v_append_1761_);
lean_dec(v_either_1760_);
lean_dec(v_costing_1759_);
lean_dec(v_guarded_1758_);
lean_dec(v_free_1757_);
lean_dec(v_initial_1756_);
lean_dec(v_final_1755_);
lean_dec(v_unindented_1754_);
lean_dec(v_aligned_1753_);
lean_dec(v_indented_1752_);
lean_dec(v_unflattenable_1751_);
lean_dec(v_tagged_1749_);
lean_dec(v_text_1748_);
lean_dec(v_newline_1747_);
v_d_1769_ = lean_ctor_get(v_t_1745_, 1);
lean_inc(v_d_1769_);
lean_dec_ref_known(v_t_1745_, 2);
v___x_1770_ = lean_apply_1(v_flattened_1750_, v_d_1769_);
return v___x_1770_;
}
case 5:
{
lean_object* v_d_1771_; lean_object* v___x_1772_; 
lean_dec(v_append_1761_);
lean_dec(v_either_1760_);
lean_dec(v_costing_1759_);
lean_dec(v_guarded_1758_);
lean_dec(v_free_1757_);
lean_dec(v_initial_1756_);
lean_dec(v_final_1755_);
lean_dec(v_unindented_1754_);
lean_dec(v_aligned_1753_);
lean_dec(v_indented_1752_);
lean_dec(v_flattened_1750_);
lean_dec(v_tagged_1749_);
lean_dec(v_text_1748_);
lean_dec(v_newline_1747_);
v_d_1771_ = lean_ctor_get(v_t_1745_, 1);
lean_inc(v_d_1771_);
lean_dec_ref_known(v_t_1745_, 2);
v___x_1772_ = lean_apply_1(v_unflattenable_1751_, v_d_1771_);
return v___x_1772_;
}
case 6:
{
lean_object* v_n_1773_; uint8_t v_isCumulative_1774_; lean_object* v_d_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
lean_dec(v_append_1761_);
lean_dec(v_either_1760_);
lean_dec(v_costing_1759_);
lean_dec(v_guarded_1758_);
lean_dec(v_free_1757_);
lean_dec(v_initial_1756_);
lean_dec(v_final_1755_);
lean_dec(v_unindented_1754_);
lean_dec(v_aligned_1753_);
lean_dec(v_unflattenable_1751_);
lean_dec(v_flattened_1750_);
lean_dec(v_tagged_1749_);
lean_dec(v_text_1748_);
lean_dec(v_newline_1747_);
v_n_1773_ = lean_ctor_get(v_t_1745_, 1);
lean_inc(v_n_1773_);
v_isCumulative_1774_ = lean_ctor_get_uint8(v_t_1745_, sizeof(void*)*3 + 7);
v_d_1775_ = lean_ctor_get(v_t_1745_, 2);
lean_inc(v_d_1775_);
lean_dec_ref_known(v_t_1745_, 3);
v___x_1776_ = lean_box(v_isCumulative_1774_);
v___x_1777_ = lean_apply_3(v_indented_1752_, v_n_1773_, v___x_1776_, v_d_1775_);
return v___x_1777_;
}
case 7:
{
lean_object* v_d_1778_; lean_object* v___x_1779_; 
lean_dec(v_append_1761_);
lean_dec(v_either_1760_);
lean_dec(v_costing_1759_);
lean_dec(v_guarded_1758_);
lean_dec(v_free_1757_);
lean_dec(v_initial_1756_);
lean_dec(v_final_1755_);
lean_dec(v_unindented_1754_);
lean_dec(v_indented_1752_);
lean_dec(v_unflattenable_1751_);
lean_dec(v_flattened_1750_);
lean_dec(v_tagged_1749_);
lean_dec(v_text_1748_);
lean_dec(v_newline_1747_);
v_d_1778_ = lean_ctor_get(v_t_1745_, 1);
lean_inc(v_d_1778_);
lean_dec_ref_known(v_t_1745_, 2);
v___x_1779_ = lean_apply_1(v_aligned_1753_, v_d_1778_);
return v___x_1779_;
}
case 8:
{
uint8_t v_onlyNonCumulative_1780_; lean_object* v_d_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
lean_dec(v_append_1761_);
lean_dec(v_either_1760_);
lean_dec(v_costing_1759_);
lean_dec(v_guarded_1758_);
lean_dec(v_free_1757_);
lean_dec(v_initial_1756_);
lean_dec(v_final_1755_);
lean_dec(v_aligned_1753_);
lean_dec(v_indented_1752_);
lean_dec(v_unflattenable_1751_);
lean_dec(v_flattened_1750_);
lean_dec(v_tagged_1749_);
lean_dec(v_text_1748_);
lean_dec(v_newline_1747_);
v_onlyNonCumulative_1780_ = lean_ctor_get_uint8(v_t_1745_, sizeof(void*)*2 + 7);
v_d_1781_ = lean_ctor_get(v_t_1745_, 1);
lean_inc(v_d_1781_);
lean_dec_ref_known(v_t_1745_, 2);
v___x_1782_ = lean_box(v_onlyNonCumulative_1780_);
v___x_1783_ = lean_apply_2(v_unindented_1754_, v___x_1782_, v_d_1781_);
return v___x_1783_;
}
case 9:
{
lean_object* v_d_1784_; lean_object* v___x_1785_; 
lean_dec(v_append_1761_);
lean_dec(v_either_1760_);
lean_dec(v_costing_1759_);
lean_dec(v_guarded_1758_);
lean_dec(v_free_1757_);
lean_dec(v_initial_1756_);
lean_dec(v_unindented_1754_);
lean_dec(v_aligned_1753_);
lean_dec(v_indented_1752_);
lean_dec(v_unflattenable_1751_);
lean_dec(v_flattened_1750_);
lean_dec(v_tagged_1749_);
lean_dec(v_text_1748_);
lean_dec(v_newline_1747_);
v_d_1784_ = lean_ctor_get(v_t_1745_, 1);
lean_inc(v_d_1784_);
lean_dec_ref_known(v_t_1745_, 2);
v___x_1785_ = lean_apply_1(v_final_1755_, v_d_1784_);
return v___x_1785_;
}
case 10:
{
lean_object* v_d_1786_; lean_object* v___x_1787_; 
lean_dec(v_append_1761_);
lean_dec(v_either_1760_);
lean_dec(v_costing_1759_);
lean_dec(v_guarded_1758_);
lean_dec(v_free_1757_);
lean_dec(v_final_1755_);
lean_dec(v_unindented_1754_);
lean_dec(v_aligned_1753_);
lean_dec(v_indented_1752_);
lean_dec(v_unflattenable_1751_);
lean_dec(v_flattened_1750_);
lean_dec(v_tagged_1749_);
lean_dec(v_text_1748_);
lean_dec(v_newline_1747_);
v_d_1786_ = lean_ctor_get(v_t_1745_, 1);
lean_inc(v_d_1786_);
lean_dec_ref_known(v_t_1745_, 2);
v___x_1787_ = lean_apply_1(v_initial_1756_, v_d_1786_);
return v___x_1787_;
}
case 11:
{
lean_object* v_d_1788_; lean_object* v___x_1789_; 
lean_dec(v_append_1761_);
lean_dec(v_either_1760_);
lean_dec(v_costing_1759_);
lean_dec(v_guarded_1758_);
lean_dec(v_initial_1756_);
lean_dec(v_final_1755_);
lean_dec(v_unindented_1754_);
lean_dec(v_aligned_1753_);
lean_dec(v_indented_1752_);
lean_dec(v_unflattenable_1751_);
lean_dec(v_flattened_1750_);
lean_dec(v_tagged_1749_);
lean_dec(v_text_1748_);
lean_dec(v_newline_1747_);
v_d_1788_ = lean_ctor_get(v_t_1745_, 1);
lean_inc(v_d_1788_);
lean_dec_ref_known(v_t_1745_, 2);
v___x_1789_ = lean_apply_1(v_free_1757_, v_d_1788_);
return v___x_1789_;
}
case 12:
{
lean_object* v_p_1790_; lean_object* v_d_1791_; lean_object* v___x_1792_; 
lean_dec(v_append_1761_);
lean_dec(v_either_1760_);
lean_dec(v_costing_1759_);
lean_dec(v_free_1757_);
lean_dec(v_initial_1756_);
lean_dec(v_final_1755_);
lean_dec(v_unindented_1754_);
lean_dec(v_aligned_1753_);
lean_dec(v_indented_1752_);
lean_dec(v_unflattenable_1751_);
lean_dec(v_flattened_1750_);
lean_dec(v_tagged_1749_);
lean_dec(v_text_1748_);
lean_dec(v_newline_1747_);
v_p_1790_ = lean_ctor_get(v_t_1745_, 1);
lean_inc_ref(v_p_1790_);
v_d_1791_ = lean_ctor_get(v_t_1745_, 2);
lean_inc(v_d_1791_);
lean_dec_ref_known(v_t_1745_, 3);
v___x_1792_ = lean_apply_2(v_guarded_1758_, v_p_1790_, v_d_1791_);
return v___x_1792_;
}
case 13:
{
lean_object* v_cost_1793_; lean_object* v_d_1794_; lean_object* v___x_1795_; 
lean_dec(v_append_1761_);
lean_dec(v_either_1760_);
lean_dec(v_guarded_1758_);
lean_dec(v_free_1757_);
lean_dec(v_initial_1756_);
lean_dec(v_final_1755_);
lean_dec(v_unindented_1754_);
lean_dec(v_aligned_1753_);
lean_dec(v_indented_1752_);
lean_dec(v_unflattenable_1751_);
lean_dec(v_flattened_1750_);
lean_dec(v_tagged_1749_);
lean_dec(v_text_1748_);
lean_dec(v_newline_1747_);
v_cost_1793_ = lean_ctor_get(v_t_1745_, 1);
lean_inc(v_cost_1793_);
v_d_1794_ = lean_ctor_get(v_t_1745_, 2);
lean_inc(v_d_1794_);
lean_dec_ref_known(v_t_1745_, 3);
v___x_1795_ = lean_apply_2(v_costing_1759_, v_cost_1793_, v_d_1794_);
return v___x_1795_;
}
case 14:
{
lean_object* v_a_1796_; lean_object* v_b_1797_; lean_object* v___x_1798_; 
lean_dec(v_append_1761_);
lean_dec(v_costing_1759_);
lean_dec(v_guarded_1758_);
lean_dec(v_free_1757_);
lean_dec(v_initial_1756_);
lean_dec(v_final_1755_);
lean_dec(v_unindented_1754_);
lean_dec(v_aligned_1753_);
lean_dec(v_indented_1752_);
lean_dec(v_unflattenable_1751_);
lean_dec(v_flattened_1750_);
lean_dec(v_tagged_1749_);
lean_dec(v_text_1748_);
lean_dec(v_newline_1747_);
v_a_1796_ = lean_ctor_get(v_t_1745_, 1);
lean_inc(v_a_1796_);
v_b_1797_ = lean_ctor_get(v_t_1745_, 2);
lean_inc(v_b_1797_);
lean_dec_ref_known(v_t_1745_, 3);
v___x_1798_ = lean_apply_2(v_either_1760_, v_a_1796_, v_b_1797_);
return v___x_1798_;
}
default: 
{
lean_object* v_a_1799_; lean_object* v_b_1800_; lean_object* v___x_1801_; 
lean_dec(v_either_1760_);
lean_dec(v_costing_1759_);
lean_dec(v_guarded_1758_);
lean_dec(v_free_1757_);
lean_dec(v_initial_1756_);
lean_dec(v_final_1755_);
lean_dec(v_unindented_1754_);
lean_dec(v_aligned_1753_);
lean_dec(v_indented_1752_);
lean_dec(v_unflattenable_1751_);
lean_dec(v_flattened_1750_);
lean_dec(v_tagged_1749_);
lean_dec(v_text_1748_);
lean_dec(v_newline_1747_);
v_a_1799_ = lean_ctor_get(v_t_1745_, 1);
lean_inc(v_a_1799_);
v_b_1800_ = lean_ctor_get(v_t_1745_, 2);
lean_inc(v_b_1800_);
lean_dec_ref_known(v_t_1745_, 3);
v___x_1801_ = lean_apply_2(v_append_1761_, v_a_1799_, v_b_1800_);
return v___x_1801_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_casesOn___override___boxed(lean_object** _args){
lean_object* v_00_u03c4_1802_ = _args[0];
lean_object* v_motive_1803_ = _args[1];
lean_object* v_t_1804_ = _args[2];
lean_object* v_failure_1805_ = _args[3];
lean_object* v_newline_1806_ = _args[4];
lean_object* v_text_1807_ = _args[5];
lean_object* v_tagged_1808_ = _args[6];
lean_object* v_flattened_1809_ = _args[7];
lean_object* v_unflattenable_1810_ = _args[8];
lean_object* v_indented_1811_ = _args[9];
lean_object* v_aligned_1812_ = _args[10];
lean_object* v_unindented_1813_ = _args[11];
lean_object* v_final_1814_ = _args[12];
lean_object* v_initial_1815_ = _args[13];
lean_object* v_free_1816_ = _args[14];
lean_object* v_guarded_1817_ = _args[15];
lean_object* v_costing_1818_ = _args[16];
lean_object* v_either_1819_ = _args[17];
lean_object* v_append_1820_ = _args[18];
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l_Lean_Fmt_Doc_casesOn___override(v_00_u03c4_1802_, v_motive_1803_, v_t_1804_, v_failure_1805_, v_newline_1806_, v_text_1807_, v_tagged_1808_, v_flattened_1809_, v_unflattenable_1810_, v_indented_1811_, v_aligned_1812_, v_unindented_1813_, v_final_1814_, v_initial_1815_, v_free_1816_, v_guarded_1817_, v_costing_1818_, v_either_1819_, v_append_1820_);
lean_dec(v_failure_1805_);
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_failure___override___redArg(){
_start:
{
lean_object* v___x_1823_; 
v___x_1823_ = lean_box(0);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_failure___override___redArg___boxed(lean_object* v___dummy_1824_){
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l_Lean_Fmt_Doc_failure___override___redArg();
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_failure___override(lean_object* v_00_u03c4_1826_){
_start:
{
lean_object* v___x_1827_; 
v___x_1827_ = lean_box(0);
return v___x_1827_;
}
}
static uint16_t _init_l_Lean_Fmt_Doc_newline___override___redArg___closed__1(void){
_start:
{
uint16_t v___x_1830_; uint16_t v___x_1831_; 
v___x_1830_ = l_Lean_Fmt_newlineFailureSet;
v___x_1831_ = lean_uint16_complement(v___x_1830_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_newline___override___redArg(lean_object* v_f_1832_){
_start:
{
uint16_t v___x_1833_; lean_object* v___x_1834_; uint8_t v___y_1836_; uint8_t v___y_1837_; lean_object* v___x_1841_; lean_object* v___x_1842_; uint8_t v___x_1843_; uint8_t v___y_1845_; 
v___x_1833_ = l_Lean_Fmt_newlineFailureSet;
v___x_1834_ = ((lean_object*)(l_Lean_Fmt_Doc_newline___override___redArg___closed__0));
v___x_1841_ = lean_string_utf8_byte_size(v_f_1832_);
v___x_1842_ = lean_unsigned_to_nat(0u);
v___x_1843_ = lean_nat_dec_eq(v___x_1841_, v___x_1842_);
if (v___x_1843_ == 0)
{
uint8_t v___x_1848_; 
v___x_1848_ = 2;
v___y_1845_ = v___x_1848_;
goto v___jp_1844_;
}
else
{
uint8_t v___x_1849_; 
v___x_1849_ = 1;
v___y_1845_ = v___x_1849_;
goto v___jp_1844_;
}
v___jp_1835_:
{
uint8_t v___x_1838_; uint16_t v___x_1839_; lean_object* v___x_1840_; 
v___x_1838_ = 1;
v___x_1839_ = lean_uint16_once(&l_Lean_Fmt_Doc_newline___override___redArg___closed__1, &l_Lean_Fmt_Doc_newline___override___redArg___closed__1_once, _init_l_Lean_Fmt_Doc_newline___override___redArg___closed__1);
v___x_1840_ = lean_alloc_ctor(1, 2, 7);
lean_ctor_set(v___x_1840_, 0, v___x_1834_);
lean_ctor_set(v___x_1840_, 1, v_f_1832_);
lean_ctor_set_uint16(v___x_1840_, sizeof(void*)*2, v___x_1833_);
lean_ctor_set_uint8(v___x_1840_, sizeof(void*)*2 + 4, v___y_1836_);
lean_ctor_set_uint8(v___x_1840_, sizeof(void*)*2 + 5, v___y_1837_);
lean_ctor_set_uint8(v___x_1840_, sizeof(void*)*2 + 6, v___x_1838_);
lean_ctor_set_uint16(v___x_1840_, sizeof(void*)*2 + 2, v___x_1839_);
return v___x_1840_;
}
v___jp_1844_:
{
if (v___x_1843_ == 0)
{
uint8_t v___x_1846_; 
v___x_1846_ = 0;
v___y_1836_ = v___y_1845_;
v___y_1837_ = v___x_1846_;
goto v___jp_1835_;
}
else
{
uint8_t v___x_1847_; 
v___x_1847_ = 1;
v___y_1836_ = v___y_1845_;
v___y_1837_ = v___x_1847_;
goto v___jp_1835_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_newline___override(lean_object* v_00_u03c4_1850_, lean_object* v_f_1851_){
_start:
{
lean_object* v___x_1852_; 
v___x_1852_ = l_Lean_Fmt_Doc_newline___override___redArg(v_f_1851_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_text___override___redArg(lean_object* v_s_1855_){
_start:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; uint8_t v___x_1858_; uint16_t v___x_1859_; lean_object* v___x_1860_; uint8_t v___y_1862_; uint8_t v___y_1863_; uint8_t v___y_1868_; 
v___x_1856_ = lean_string_utf8_byte_size(v_s_1855_);
v___x_1857_ = lean_unsigned_to_nat(0u);
v___x_1858_ = lean_nat_dec_eq(v___x_1856_, v___x_1857_);
v___x_1859_ = l_Lean_Fmt_textFailureSet(v___x_1858_);
v___x_1860_ = ((lean_object*)(l_Lean_Fmt_Doc_text___override___redArg___closed__0));
if (v___x_1858_ == 0)
{
uint8_t v___x_1871_; 
v___x_1871_ = 2;
v___y_1868_ = v___x_1871_;
goto v___jp_1867_;
}
else
{
uint8_t v___x_1872_; 
v___x_1872_ = 0;
v___y_1868_ = v___x_1872_;
goto v___jp_1867_;
}
v___jp_1861_:
{
uint8_t v___x_1864_; uint16_t v___x_1865_; lean_object* v___x_1866_; 
v___x_1864_ = 0;
v___x_1865_ = lean_uint16_complement(v___x_1859_);
v___x_1866_ = lean_alloc_ctor(2, 2, 7);
lean_ctor_set(v___x_1866_, 0, v___x_1860_);
lean_ctor_set(v___x_1866_, 1, v_s_1855_);
lean_ctor_set_uint16(v___x_1866_, sizeof(void*)*2, v___x_1859_);
lean_ctor_set_uint8(v___x_1866_, sizeof(void*)*2 + 4, v___y_1862_);
lean_ctor_set_uint8(v___x_1866_, sizeof(void*)*2 + 5, v___y_1863_);
lean_ctor_set_uint8(v___x_1866_, sizeof(void*)*2 + 6, v___x_1864_);
lean_ctor_set_uint16(v___x_1866_, sizeof(void*)*2 + 2, v___x_1865_);
return v___x_1866_;
}
v___jp_1867_:
{
if (v___x_1858_ == 0)
{
uint8_t v___x_1869_; 
v___x_1869_ = 0;
v___y_1862_ = v___y_1868_;
v___y_1863_ = v___x_1869_;
goto v___jp_1861_;
}
else
{
uint8_t v___x_1870_; 
v___x_1870_ = 1;
v___y_1862_ = v___y_1868_;
v___y_1863_ = v___x_1870_;
goto v___jp_1861_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_text___override(lean_object* v_00_u03c4_1873_, lean_object* v_s_1874_){
_start:
{
lean_object* v___x_1875_; 
v___x_1875_ = l_Lean_Fmt_Doc_text___override___redArg(v_s_1874_);
return v___x_1875_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_atomicness___override___redArg(lean_object* v_x_1876_){
_start:
{
switch(lean_obj_tag(v_x_1876_))
{
case 0:
{
uint8_t v___x_1877_; 
v___x_1877_ = 0;
return v___x_1877_;
}
case 3:
{
uint8_t v_atomicness_1878_; 
v_atomicness_1878_ = lean_ctor_get_uint8(v_x_1876_, sizeof(void*)*3 + 6);
return v_atomicness_1878_;
}
case 6:
{
uint8_t v_atomicness_1879_; 
v_atomicness_1879_ = lean_ctor_get_uint8(v_x_1876_, sizeof(void*)*3 + 6);
return v_atomicness_1879_;
}
case 12:
{
uint8_t v_atomicness_1880_; 
v_atomicness_1880_ = lean_ctor_get_uint8(v_x_1876_, sizeof(void*)*3 + 6);
return v_atomicness_1880_;
}
case 13:
{
uint8_t v_atomicness_1881_; 
v_atomicness_1881_ = lean_ctor_get_uint8(v_x_1876_, sizeof(void*)*3 + 6);
return v_atomicness_1881_;
}
case 14:
{
uint8_t v_atomicness_1882_; 
v_atomicness_1882_ = lean_ctor_get_uint8(v_x_1876_, sizeof(void*)*3 + 6);
return v_atomicness_1882_;
}
case 15:
{
uint8_t v_atomicness_1883_; 
v_atomicness_1883_ = lean_ctor_get_uint8(v_x_1876_, sizeof(void*)*3 + 6);
return v_atomicness_1883_;
}
default: 
{
uint8_t v_atomicness_1884_; 
v_atomicness_1884_ = lean_ctor_get_uint8(v_x_1876_, sizeof(void*)*2 + 6);
return v_atomicness_1884_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_atomicness___override___redArg___boxed(lean_object* v_x_1885_){
_start:
{
uint8_t v_res_1886_; lean_object* v_r_1887_; 
v_res_1886_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_x_1885_);
lean_dec(v_x_1885_);
v_r_1887_ = lean_box(v_res_1886_);
return v_r_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(lean_object* v_x_1888_){
_start:
{
if (lean_obj_tag(v_x_1888_) == 0)
{
lean_object* v___x_1889_; 
v___x_1889_ = lean_box(0);
return v___x_1889_;
}
else
{
lean_object* v_maxNewlineCount_x3f_1890_; 
v_maxNewlineCount_x3f_1890_ = lean_ctor_get(v_x_1888_, 0);
lean_inc(v_maxNewlineCount_x3f_1890_);
return v_maxNewlineCount_x3f_1890_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg___boxed(lean_object* v_x_1891_){
_start:
{
lean_object* v_res_1892_; 
v_res_1892_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_x_1891_);
lean_dec(v_x_1891_);
return v_res_1892_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(lean_object* v_x_1893_){
_start:
{
switch(lean_obj_tag(v_x_1893_))
{
case 0:
{
uint8_t v___x_1894_; 
v___x_1894_ = 1;
return v___x_1894_;
}
case 3:
{
uint8_t v_alwaysNonEmptiness_1895_; 
v_alwaysNonEmptiness_1895_ = lean_ctor_get_uint8(v_x_1893_, sizeof(void*)*3 + 5);
return v_alwaysNonEmptiness_1895_;
}
case 6:
{
uint8_t v_alwaysNonEmptiness_1896_; 
v_alwaysNonEmptiness_1896_ = lean_ctor_get_uint8(v_x_1893_, sizeof(void*)*3 + 5);
return v_alwaysNonEmptiness_1896_;
}
case 12:
{
uint8_t v_alwaysNonEmptiness_1897_; 
v_alwaysNonEmptiness_1897_ = lean_ctor_get_uint8(v_x_1893_, sizeof(void*)*3 + 5);
return v_alwaysNonEmptiness_1897_;
}
case 13:
{
uint8_t v_alwaysNonEmptiness_1898_; 
v_alwaysNonEmptiness_1898_ = lean_ctor_get_uint8(v_x_1893_, sizeof(void*)*3 + 5);
return v_alwaysNonEmptiness_1898_;
}
case 14:
{
uint8_t v_alwaysNonEmptiness_1899_; 
v_alwaysNonEmptiness_1899_ = lean_ctor_get_uint8(v_x_1893_, sizeof(void*)*3 + 5);
return v_alwaysNonEmptiness_1899_;
}
case 15:
{
uint8_t v_alwaysNonEmptiness_1900_; 
v_alwaysNonEmptiness_1900_ = lean_ctor_get_uint8(v_x_1893_, sizeof(void*)*3 + 5);
return v_alwaysNonEmptiness_1900_;
}
default: 
{
uint8_t v_alwaysNonEmptiness_1901_; 
v_alwaysNonEmptiness_1901_ = lean_ctor_get_uint8(v_x_1893_, sizeof(void*)*2 + 5);
return v_alwaysNonEmptiness_1901_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg___boxed(lean_object* v_x_1902_){
_start:
{
uint8_t v_res_1903_; lean_object* v_r_1904_; 
v_res_1903_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_x_1902_);
lean_dec(v_x_1902_);
v_r_1904_ = lean_box(v_res_1903_);
return v_r_1904_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_Doc_neverFailsSet___override___redArg(lean_object* v_x_1905_){
_start:
{
switch(lean_obj_tag(v_x_1905_))
{
case 0:
{
uint16_t v___x_1906_; 
v___x_1906_ = 0;
return v___x_1906_;
}
case 3:
{
uint16_t v_neverFailsSet_1907_; 
v_neverFailsSet_1907_ = lean_ctor_get_uint16(v_x_1905_, sizeof(void*)*3 + 2);
return v_neverFailsSet_1907_;
}
case 6:
{
uint16_t v_neverFailsSet_1908_; 
v_neverFailsSet_1908_ = lean_ctor_get_uint16(v_x_1905_, sizeof(void*)*3 + 2);
return v_neverFailsSet_1908_;
}
case 12:
{
uint16_t v_neverFailsSet_1909_; 
v_neverFailsSet_1909_ = lean_ctor_get_uint16(v_x_1905_, sizeof(void*)*3 + 2);
return v_neverFailsSet_1909_;
}
case 13:
{
uint16_t v_neverFailsSet_1910_; 
v_neverFailsSet_1910_ = lean_ctor_get_uint16(v_x_1905_, sizeof(void*)*3 + 2);
return v_neverFailsSet_1910_;
}
case 14:
{
uint16_t v_neverFailsSet_1911_; 
v_neverFailsSet_1911_ = lean_ctor_get_uint16(v_x_1905_, sizeof(void*)*3 + 2);
return v_neverFailsSet_1911_;
}
case 15:
{
uint16_t v_neverFailsSet_1912_; 
v_neverFailsSet_1912_ = lean_ctor_get_uint16(v_x_1905_, sizeof(void*)*3 + 2);
return v_neverFailsSet_1912_;
}
default: 
{
uint16_t v_neverFailsSet_1913_; 
v_neverFailsSet_1913_ = lean_ctor_get_uint16(v_x_1905_, sizeof(void*)*2 + 2);
return v_neverFailsSet_1913_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_neverFailsSet___override___redArg___boxed(lean_object* v_x_1914_){
_start:
{
uint16_t v_res_1915_; lean_object* v_r_1916_; 
v_res_1915_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_x_1914_);
lean_dec(v_x_1914_);
v_r_1916_ = lean_box(v_res_1915_);
return v_r_1916_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(lean_object* v_x_1917_){
_start:
{
switch(lean_obj_tag(v_x_1917_))
{
case 0:
{
uint8_t v___x_1918_; 
v___x_1918_ = 2;
return v___x_1918_;
}
case 3:
{
uint8_t v_alwaysEmptiness_1919_; 
v_alwaysEmptiness_1919_ = lean_ctor_get_uint8(v_x_1917_, sizeof(void*)*3 + 4);
return v_alwaysEmptiness_1919_;
}
case 6:
{
uint8_t v_alwaysEmptiness_1920_; 
v_alwaysEmptiness_1920_ = lean_ctor_get_uint8(v_x_1917_, sizeof(void*)*3 + 4);
return v_alwaysEmptiness_1920_;
}
case 12:
{
uint8_t v_alwaysEmptiness_1921_; 
v_alwaysEmptiness_1921_ = lean_ctor_get_uint8(v_x_1917_, sizeof(void*)*3 + 4);
return v_alwaysEmptiness_1921_;
}
case 13:
{
uint8_t v_alwaysEmptiness_1922_; 
v_alwaysEmptiness_1922_ = lean_ctor_get_uint8(v_x_1917_, sizeof(void*)*3 + 4);
return v_alwaysEmptiness_1922_;
}
case 14:
{
uint8_t v_alwaysEmptiness_1923_; 
v_alwaysEmptiness_1923_ = lean_ctor_get_uint8(v_x_1917_, sizeof(void*)*3 + 4);
return v_alwaysEmptiness_1923_;
}
case 15:
{
uint8_t v_alwaysEmptiness_1924_; 
v_alwaysEmptiness_1924_ = lean_ctor_get_uint8(v_x_1917_, sizeof(void*)*3 + 4);
return v_alwaysEmptiness_1924_;
}
default: 
{
uint8_t v_alwaysEmptiness_1925_; 
v_alwaysEmptiness_1925_ = lean_ctor_get_uint8(v_x_1917_, sizeof(void*)*2 + 4);
return v_alwaysEmptiness_1925_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg___boxed(lean_object* v_x_1926_){
_start:
{
uint8_t v_res_1927_; lean_object* v_r_1928_; 
v_res_1927_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_x_1926_);
lean_dec(v_x_1926_);
v_r_1928_ = lean_box(v_res_1927_);
return v_r_1928_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_Doc_failureSet___override___redArg(lean_object* v_x_1929_){
_start:
{
switch(lean_obj_tag(v_x_1929_))
{
case 0:
{
uint16_t v___x_1930_; 
v___x_1930_ = 65535;
return v___x_1930_;
}
case 3:
{
uint16_t v_failureSet_1931_; 
v_failureSet_1931_ = lean_ctor_get_uint16(v_x_1929_, sizeof(void*)*3);
return v_failureSet_1931_;
}
case 6:
{
uint16_t v_failureSet_1932_; 
v_failureSet_1932_ = lean_ctor_get_uint16(v_x_1929_, sizeof(void*)*3);
return v_failureSet_1932_;
}
case 12:
{
uint16_t v_failureSet_1933_; 
v_failureSet_1933_ = lean_ctor_get_uint16(v_x_1929_, sizeof(void*)*3);
return v_failureSet_1933_;
}
case 13:
{
uint16_t v_failureSet_1934_; 
v_failureSet_1934_ = lean_ctor_get_uint16(v_x_1929_, sizeof(void*)*3);
return v_failureSet_1934_;
}
case 14:
{
uint16_t v_failureSet_1935_; 
v_failureSet_1935_ = lean_ctor_get_uint16(v_x_1929_, sizeof(void*)*3);
return v_failureSet_1935_;
}
case 15:
{
uint16_t v_failureSet_1936_; 
v_failureSet_1936_ = lean_ctor_get_uint16(v_x_1929_, sizeof(void*)*3);
return v_failureSet_1936_;
}
default: 
{
uint16_t v_failureSet_1937_; 
v_failureSet_1937_ = lean_ctor_get_uint16(v_x_1929_, sizeof(void*)*2);
return v_failureSet_1937_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_failureSet___override___redArg___boxed(lean_object* v_x_1938_){
_start:
{
uint16_t v_res_1939_; lean_object* v_r_1940_; 
v_res_1939_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_x_1938_);
lean_dec(v_x_1938_);
v_r_1940_ = lean_box(v_res_1939_);
return v_r_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_tagged___override___redArg(lean_object* v_id_1941_, lean_object* v_d_1942_){
_start:
{
uint16_t v___x_1943_; lean_object* v___x_1944_; uint8_t v___x_1945_; uint8_t v___x_1946_; uint8_t v___x_1947_; uint16_t v___x_1948_; lean_object* v___x_1949_; 
v___x_1943_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_d_1942_);
v___x_1944_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_1942_);
v___x_1945_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_1942_);
v___x_1946_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_1942_);
v___x_1947_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_1942_);
v___x_1948_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_d_1942_);
v___x_1949_ = lean_alloc_ctor(3, 3, 7);
lean_ctor_set(v___x_1949_, 0, v___x_1944_);
lean_ctor_set(v___x_1949_, 1, v_id_1941_);
lean_ctor_set(v___x_1949_, 2, v_d_1942_);
lean_ctor_set_uint16(v___x_1949_, sizeof(void*)*3, v___x_1943_);
lean_ctor_set_uint8(v___x_1949_, sizeof(void*)*3 + 4, v___x_1945_);
lean_ctor_set_uint8(v___x_1949_, sizeof(void*)*3 + 5, v___x_1946_);
lean_ctor_set_uint8(v___x_1949_, sizeof(void*)*3 + 6, v___x_1947_);
lean_ctor_set_uint16(v___x_1949_, sizeof(void*)*3 + 2, v___x_1948_);
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_tagged___override(lean_object* v_00_u03c4_1950_, lean_object* v_id_1951_, lean_object* v_d_1952_){
_start:
{
lean_object* v___x_1953_; 
v___x_1953_ = l_Lean_Fmt_Doc_tagged___override___redArg(v_id_1951_, v_d_1952_);
return v___x_1953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_flattened___override___redArg(lean_object* v_d_1954_){
_start:
{
uint16_t v___x_1955_; lean_object* v___x_1956_; uint8_t v___y_1958_; uint8_t v___x_1966_; 
v___x_1955_ = 0;
v___x_1956_ = ((lean_object*)(l_Lean_Fmt_Doc_text___override___redArg___closed__0));
v___x_1966_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_1954_);
if (v___x_1966_ == 1)
{
uint8_t v___x_1967_; 
v___x_1967_ = 0;
v___y_1958_ = v___x_1967_;
goto v___jp_1957_;
}
else
{
v___y_1958_ = v___x_1966_;
goto v___jp_1957_;
}
v___jp_1957_:
{
uint8_t v___x_1959_; uint8_t v___x_1960_; 
v___x_1959_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_1954_);
v___x_1960_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_1954_);
switch(v___x_1960_)
{
case 1:
{
uint8_t v___x_1961_; lean_object* v___x_1962_; 
v___x_1961_ = 0;
v___x_1962_ = lean_alloc_ctor(4, 2, 7);
lean_ctor_set(v___x_1962_, 0, v___x_1956_);
lean_ctor_set(v___x_1962_, 1, v_d_1954_);
lean_ctor_set_uint16(v___x_1962_, sizeof(void*)*2, v___x_1955_);
lean_ctor_set_uint8(v___x_1962_, sizeof(void*)*2 + 4, v___y_1958_);
lean_ctor_set_uint8(v___x_1962_, sizeof(void*)*2 + 5, v___x_1959_);
lean_ctor_set_uint8(v___x_1962_, sizeof(void*)*2 + 6, v___x_1961_);
lean_ctor_set_uint16(v___x_1962_, sizeof(void*)*2 + 2, v___x_1955_);
return v___x_1962_;
}
case 3:
{
uint8_t v___x_1963_; lean_object* v___x_1964_; 
v___x_1963_ = 2;
v___x_1964_ = lean_alloc_ctor(4, 2, 7);
lean_ctor_set(v___x_1964_, 0, v___x_1956_);
lean_ctor_set(v___x_1964_, 1, v_d_1954_);
lean_ctor_set_uint16(v___x_1964_, sizeof(void*)*2, v___x_1955_);
lean_ctor_set_uint8(v___x_1964_, sizeof(void*)*2 + 4, v___y_1958_);
lean_ctor_set_uint8(v___x_1964_, sizeof(void*)*2 + 5, v___x_1959_);
lean_ctor_set_uint8(v___x_1964_, sizeof(void*)*2 + 6, v___x_1963_);
lean_ctor_set_uint16(v___x_1964_, sizeof(void*)*2 + 2, v___x_1955_);
return v___x_1964_;
}
default: 
{
lean_object* v___x_1965_; 
v___x_1965_ = lean_alloc_ctor(4, 2, 7);
lean_ctor_set(v___x_1965_, 0, v___x_1956_);
lean_ctor_set(v___x_1965_, 1, v_d_1954_);
lean_ctor_set_uint16(v___x_1965_, sizeof(void*)*2, v___x_1955_);
lean_ctor_set_uint8(v___x_1965_, sizeof(void*)*2 + 4, v___y_1958_);
lean_ctor_set_uint8(v___x_1965_, sizeof(void*)*2 + 5, v___x_1959_);
lean_ctor_set_uint8(v___x_1965_, sizeof(void*)*2 + 6, v___x_1960_);
lean_ctor_set_uint16(v___x_1965_, sizeof(void*)*2 + 2, v___x_1955_);
return v___x_1965_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_flattened___override(lean_object* v_00_u03c4_1968_, lean_object* v_d_1969_){
_start:
{
lean_object* v___x_1970_; 
v___x_1970_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_d_1969_);
return v___x_1970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unflattenable___override___redArg(lean_object* v_d_1971_){
_start:
{
uint16_t v___x_1972_; lean_object* v___x_1973_; uint8_t v___y_1975_; uint8_t v___x_1983_; 
v___x_1972_ = 0;
v___x_1973_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_1971_);
v___x_1983_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_1971_);
if (v___x_1983_ == 1)
{
uint8_t v___x_1984_; 
v___x_1984_ = 2;
v___y_1975_ = v___x_1984_;
goto v___jp_1974_;
}
else
{
v___y_1975_ = v___x_1983_;
goto v___jp_1974_;
}
v___jp_1974_:
{
uint8_t v___x_1976_; uint8_t v___x_1977_; 
v___x_1976_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_1971_);
v___x_1977_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_1971_);
switch(v___x_1977_)
{
case 1:
{
uint8_t v___x_1978_; lean_object* v___x_1979_; 
v___x_1978_ = 4;
v___x_1979_ = lean_alloc_ctor(5, 2, 7);
lean_ctor_set(v___x_1979_, 0, v___x_1973_);
lean_ctor_set(v___x_1979_, 1, v_d_1971_);
lean_ctor_set_uint16(v___x_1979_, sizeof(void*)*2, v___x_1972_);
lean_ctor_set_uint8(v___x_1979_, sizeof(void*)*2 + 4, v___y_1975_);
lean_ctor_set_uint8(v___x_1979_, sizeof(void*)*2 + 5, v___x_1976_);
lean_ctor_set_uint8(v___x_1979_, sizeof(void*)*2 + 6, v___x_1978_);
lean_ctor_set_uint16(v___x_1979_, sizeof(void*)*2 + 2, v___x_1972_);
return v___x_1979_;
}
case 3:
{
uint8_t v___x_1980_; lean_object* v___x_1981_; 
v___x_1980_ = 4;
v___x_1981_ = lean_alloc_ctor(5, 2, 7);
lean_ctor_set(v___x_1981_, 0, v___x_1973_);
lean_ctor_set(v___x_1981_, 1, v_d_1971_);
lean_ctor_set_uint16(v___x_1981_, sizeof(void*)*2, v___x_1972_);
lean_ctor_set_uint8(v___x_1981_, sizeof(void*)*2 + 4, v___y_1975_);
lean_ctor_set_uint8(v___x_1981_, sizeof(void*)*2 + 5, v___x_1976_);
lean_ctor_set_uint8(v___x_1981_, sizeof(void*)*2 + 6, v___x_1980_);
lean_ctor_set_uint16(v___x_1981_, sizeof(void*)*2 + 2, v___x_1972_);
return v___x_1981_;
}
default: 
{
lean_object* v___x_1982_; 
v___x_1982_ = lean_alloc_ctor(5, 2, 7);
lean_ctor_set(v___x_1982_, 0, v___x_1973_);
lean_ctor_set(v___x_1982_, 1, v_d_1971_);
lean_ctor_set_uint16(v___x_1982_, sizeof(void*)*2, v___x_1972_);
lean_ctor_set_uint8(v___x_1982_, sizeof(void*)*2 + 4, v___y_1975_);
lean_ctor_set_uint8(v___x_1982_, sizeof(void*)*2 + 5, v___x_1976_);
lean_ctor_set_uint8(v___x_1982_, sizeof(void*)*2 + 6, v___x_1977_);
lean_ctor_set_uint16(v___x_1982_, sizeof(void*)*2 + 2, v___x_1972_);
return v___x_1982_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unflattenable___override(lean_object* v_00_u03c4_1985_, lean_object* v_d_1986_){
_start:
{
lean_object* v___x_1987_; 
v___x_1987_ = l_Lean_Fmt_Doc_unflattenable___override___redArg(v_d_1986_);
return v___x_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_indented___override___redArg(lean_object* v_n_1988_, uint8_t v_isCumulative_1989_, lean_object* v_d_1990_){
_start:
{
uint16_t v___x_1991_; lean_object* v___x_1992_; uint8_t v___x_1993_; uint8_t v___x_1994_; uint8_t v___x_1995_; uint16_t v___x_1996_; lean_object* v___x_1997_; 
v___x_1991_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_d_1990_);
v___x_1992_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_1990_);
v___x_1993_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_1990_);
v___x_1994_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_1990_);
v___x_1995_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_1990_);
v___x_1996_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_d_1990_);
v___x_1997_ = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(v___x_1997_, 0, v___x_1992_);
lean_ctor_set(v___x_1997_, 1, v_n_1988_);
lean_ctor_set(v___x_1997_, 2, v_d_1990_);
lean_ctor_set_uint16(v___x_1997_, sizeof(void*)*3, v___x_1991_);
lean_ctor_set_uint8(v___x_1997_, sizeof(void*)*3 + 4, v___x_1993_);
lean_ctor_set_uint8(v___x_1997_, sizeof(void*)*3 + 5, v___x_1994_);
lean_ctor_set_uint8(v___x_1997_, sizeof(void*)*3 + 6, v___x_1995_);
lean_ctor_set_uint16(v___x_1997_, sizeof(void*)*3 + 2, v___x_1996_);
lean_ctor_set_uint8(v___x_1997_, sizeof(void*)*3 + 7, v_isCumulative_1989_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_indented___override___redArg___boxed(lean_object* v_n_1998_, lean_object* v_isCumulative_1999_, lean_object* v_d_2000_){
_start:
{
uint8_t v_isCumulative_boxed_2001_; lean_object* v_res_2002_; 
v_isCumulative_boxed_2001_ = lean_unbox(v_isCumulative_1999_);
v_res_2002_ = l_Lean_Fmt_Doc_indented___override___redArg(v_n_1998_, v_isCumulative_boxed_2001_, v_d_2000_);
return v_res_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_indented___override(lean_object* v_00_u03c4_2003_, lean_object* v_n_2004_, uint8_t v_isCumulative_2005_, lean_object* v_d_2006_){
_start:
{
lean_object* v___x_2007_; 
v___x_2007_ = l_Lean_Fmt_Doc_indented___override___redArg(v_n_2004_, v_isCumulative_2005_, v_d_2006_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_indented___override___boxed(lean_object* v_00_u03c4_2008_, lean_object* v_n_2009_, lean_object* v_isCumulative_2010_, lean_object* v_d_2011_){
_start:
{
uint8_t v_isCumulative_boxed_2012_; lean_object* v_res_2013_; 
v_isCumulative_boxed_2012_ = lean_unbox(v_isCumulative_2010_);
v_res_2013_ = l_Lean_Fmt_Doc_indented___override(v_00_u03c4_2008_, v_n_2009_, v_isCumulative_boxed_2012_, v_d_2011_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_aligned___override___redArg(lean_object* v_d_2014_){
_start:
{
uint16_t v___x_2015_; lean_object* v___x_2016_; uint8_t v___x_2017_; uint8_t v___x_2018_; uint8_t v___x_2019_; uint16_t v___x_2020_; lean_object* v___x_2021_; 
v___x_2015_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_d_2014_);
v___x_2016_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_2014_);
v___x_2017_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_2014_);
v___x_2018_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_2014_);
v___x_2019_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_2014_);
v___x_2020_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_d_2014_);
v___x_2021_ = lean_alloc_ctor(7, 2, 7);
lean_ctor_set(v___x_2021_, 0, v___x_2016_);
lean_ctor_set(v___x_2021_, 1, v_d_2014_);
lean_ctor_set_uint16(v___x_2021_, sizeof(void*)*2, v___x_2015_);
lean_ctor_set_uint8(v___x_2021_, sizeof(void*)*2 + 4, v___x_2017_);
lean_ctor_set_uint8(v___x_2021_, sizeof(void*)*2 + 5, v___x_2018_);
lean_ctor_set_uint8(v___x_2021_, sizeof(void*)*2 + 6, v___x_2019_);
lean_ctor_set_uint16(v___x_2021_, sizeof(void*)*2 + 2, v___x_2020_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_aligned___override(lean_object* v_00_u03c4_2022_, lean_object* v_d_2023_){
_start:
{
lean_object* v___x_2024_; 
v___x_2024_ = l_Lean_Fmt_Doc_aligned___override___redArg(v_d_2023_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unindented___override___redArg(uint8_t v_onlyNonCumulative_2025_, lean_object* v_d_2026_){
_start:
{
uint16_t v___x_2027_; lean_object* v___x_2028_; uint8_t v___x_2029_; uint8_t v___x_2030_; uint8_t v___x_2031_; uint16_t v___x_2032_; lean_object* v___x_2033_; 
v___x_2027_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_d_2026_);
v___x_2028_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_2026_);
v___x_2029_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_2026_);
v___x_2030_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_2026_);
v___x_2031_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_2026_);
v___x_2032_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_d_2026_);
v___x_2033_ = lean_alloc_ctor(8, 2, 8);
lean_ctor_set(v___x_2033_, 0, v___x_2028_);
lean_ctor_set(v___x_2033_, 1, v_d_2026_);
lean_ctor_set_uint16(v___x_2033_, sizeof(void*)*2, v___x_2027_);
lean_ctor_set_uint8(v___x_2033_, sizeof(void*)*2 + 4, v___x_2029_);
lean_ctor_set_uint8(v___x_2033_, sizeof(void*)*2 + 5, v___x_2030_);
lean_ctor_set_uint8(v___x_2033_, sizeof(void*)*2 + 6, v___x_2031_);
lean_ctor_set_uint16(v___x_2033_, sizeof(void*)*2 + 2, v___x_2032_);
lean_ctor_set_uint8(v___x_2033_, sizeof(void*)*2 + 7, v_onlyNonCumulative_2025_);
return v___x_2033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unindented___override___redArg___boxed(lean_object* v_onlyNonCumulative_2034_, lean_object* v_d_2035_){
_start:
{
uint8_t v_onlyNonCumulative_boxed_2036_; lean_object* v_res_2037_; 
v_onlyNonCumulative_boxed_2036_ = lean_unbox(v_onlyNonCumulative_2034_);
v_res_2037_ = l_Lean_Fmt_Doc_unindented___override___redArg(v_onlyNonCumulative_boxed_2036_, v_d_2035_);
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unindented___override(lean_object* v_00_u03c4_2038_, uint8_t v_onlyNonCumulative_2039_, lean_object* v_d_2040_){
_start:
{
lean_object* v___x_2041_; 
v___x_2041_ = l_Lean_Fmt_Doc_unindented___override___redArg(v_onlyNonCumulative_2039_, v_d_2040_);
return v___x_2041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unindented___override___boxed(lean_object* v_00_u03c4_2042_, lean_object* v_onlyNonCumulative_2043_, lean_object* v_d_2044_){
_start:
{
uint8_t v_onlyNonCumulative_boxed_2045_; lean_object* v_res_2046_; 
v_onlyNonCumulative_boxed_2045_ = lean_unbox(v_onlyNonCumulative_2043_);
v_res_2046_ = l_Lean_Fmt_Doc_unindented___override(v_00_u03c4_2042_, v_onlyNonCumulative_boxed_2045_, v_d_2044_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_final___override___redArg(lean_object* v_d_2047_){
_start:
{
uint16_t v___x_2048_; uint16_t v___x_2049_; uint16_t v___x_2050_; uint16_t v___x_2051_; uint16_t v___x_2052_; uint16_t v___x_2053_; uint16_t v___x_2054_; uint16_t v___x_2055_; lean_object* v___x_2056_; uint8_t v___x_2057_; uint8_t v___x_2058_; uint8_t v___x_2059_; uint16_t v___x_2060_; uint16_t v___x_2061_; uint16_t v___x_2062_; uint16_t v___x_2063_; lean_object* v___x_2064_; 
v___x_2048_ = 21845;
v___x_2049_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_d_2047_);
v___x_2050_ = 1;
v___x_2051_ = lean_uint16_shift_left(v___x_2049_, v___x_2050_);
v___x_2052_ = lean_uint16_land(v___x_2051_, v___x_2049_);
v___x_2053_ = 43690;
v___x_2054_ = lean_uint16_land(v___x_2052_, v___x_2053_);
v___x_2055_ = lean_uint16_lor(v___x_2048_, v___x_2054_);
v___x_2056_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_2047_);
v___x_2057_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_2047_);
v___x_2058_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_2047_);
v___x_2059_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_2047_);
v___x_2060_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_d_2047_);
v___x_2061_ = lean_uint16_shift_left(v___x_2060_, v___x_2050_);
v___x_2062_ = lean_uint16_lor(v___x_2061_, v___x_2060_);
v___x_2063_ = lean_uint16_land(v___x_2062_, v___x_2053_);
v___x_2064_ = lean_alloc_ctor(9, 2, 7);
lean_ctor_set(v___x_2064_, 0, v___x_2056_);
lean_ctor_set(v___x_2064_, 1, v_d_2047_);
lean_ctor_set_uint16(v___x_2064_, sizeof(void*)*2, v___x_2055_);
lean_ctor_set_uint8(v___x_2064_, sizeof(void*)*2 + 4, v___x_2057_);
lean_ctor_set_uint8(v___x_2064_, sizeof(void*)*2 + 5, v___x_2058_);
lean_ctor_set_uint8(v___x_2064_, sizeof(void*)*2 + 6, v___x_2059_);
lean_ctor_set_uint16(v___x_2064_, sizeof(void*)*2 + 2, v___x_2063_);
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_final___override(lean_object* v_00_u03c4_2065_, lean_object* v_d_2066_){
_start:
{
lean_object* v___x_2067_; 
v___x_2067_ = l_Lean_Fmt_Doc_final___override___redArg(v_d_2066_);
return v___x_2067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_initial___override___redArg(lean_object* v_d_2068_){
_start:
{
uint16_t v___x_2069_; uint16_t v___x_2070_; uint16_t v___x_2071_; uint16_t v___x_2072_; uint16_t v___x_2073_; uint16_t v___x_2074_; uint16_t v___x_2075_; uint16_t v___x_2076_; lean_object* v___x_2077_; uint8_t v___x_2078_; uint8_t v___x_2079_; uint8_t v___x_2080_; uint16_t v___x_2081_; uint16_t v___x_2082_; uint16_t v___x_2083_; uint16_t v___x_2084_; lean_object* v___x_2085_; 
v___x_2069_ = 255;
v___x_2070_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_d_2068_);
v___x_2071_ = 8;
v___x_2072_ = lean_uint16_shift_left(v___x_2070_, v___x_2071_);
v___x_2073_ = lean_uint16_land(v___x_2072_, v___x_2070_);
v___x_2074_ = 65280;
v___x_2075_ = lean_uint16_land(v___x_2073_, v___x_2074_);
v___x_2076_ = lean_uint16_lor(v___x_2069_, v___x_2075_);
v___x_2077_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_2068_);
v___x_2078_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_2068_);
v___x_2079_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_2068_);
v___x_2080_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_2068_);
v___x_2081_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_d_2068_);
v___x_2082_ = lean_uint16_shift_left(v___x_2081_, v___x_2071_);
v___x_2083_ = lean_uint16_lor(v___x_2082_, v___x_2081_);
v___x_2084_ = lean_uint16_land(v___x_2083_, v___x_2074_);
v___x_2085_ = lean_alloc_ctor(10, 2, 7);
lean_ctor_set(v___x_2085_, 0, v___x_2077_);
lean_ctor_set(v___x_2085_, 1, v_d_2068_);
lean_ctor_set_uint16(v___x_2085_, sizeof(void*)*2, v___x_2076_);
lean_ctor_set_uint8(v___x_2085_, sizeof(void*)*2 + 4, v___x_2078_);
lean_ctor_set_uint8(v___x_2085_, sizeof(void*)*2 + 5, v___x_2079_);
lean_ctor_set_uint8(v___x_2085_, sizeof(void*)*2 + 6, v___x_2080_);
lean_ctor_set_uint16(v___x_2085_, sizeof(void*)*2 + 2, v___x_2084_);
return v___x_2085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_initial___override(lean_object* v_00_u03c4_2086_, lean_object* v_d_2087_){
_start:
{
lean_object* v___x_2088_; 
v___x_2088_ = l_Lean_Fmt_Doc_initial___override___redArg(v_d_2087_);
return v___x_2088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_free___override___redArg(lean_object* v_d_2089_){
_start:
{
uint16_t v___x_2090_; lean_object* v___x_2091_; uint8_t v___x_2092_; uint8_t v___x_2093_; uint8_t v___x_2094_; uint16_t v___x_2095_; lean_object* v___x_2096_; 
v___x_2090_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_d_2089_);
v___x_2091_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_2089_);
v___x_2092_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_2089_);
v___x_2093_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_2089_);
v___x_2094_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_2089_);
v___x_2095_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_d_2089_);
v___x_2096_ = lean_alloc_ctor(11, 2, 7);
lean_ctor_set(v___x_2096_, 0, v___x_2091_);
lean_ctor_set(v___x_2096_, 1, v_d_2089_);
lean_ctor_set_uint16(v___x_2096_, sizeof(void*)*2, v___x_2090_);
lean_ctor_set_uint8(v___x_2096_, sizeof(void*)*2 + 4, v___x_2092_);
lean_ctor_set_uint8(v___x_2096_, sizeof(void*)*2 + 5, v___x_2093_);
lean_ctor_set_uint8(v___x_2096_, sizeof(void*)*2 + 6, v___x_2094_);
lean_ctor_set_uint16(v___x_2096_, sizeof(void*)*2 + 2, v___x_2095_);
return v___x_2096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_free___override(lean_object* v_00_u03c4_2097_, lean_object* v_d_2098_){
_start:
{
lean_object* v___x_2099_; 
v___x_2099_ = l_Lean_Fmt_Doc_free___override___redArg(v_d_2098_);
return v___x_2099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_guarded___override___redArg(lean_object* v_p_2100_, lean_object* v_d_2101_){
_start:
{
uint16_t v___x_2102_; lean_object* v___x_2103_; uint8_t v___x_2104_; uint8_t v___x_2105_; uint8_t v___x_2106_; uint16_t v___x_2107_; lean_object* v___x_2108_; 
v___x_2102_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_d_2101_);
v___x_2103_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_2101_);
v___x_2104_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_2101_);
v___x_2105_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_2101_);
v___x_2106_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_2101_);
v___x_2107_ = 0;
v___x_2108_ = lean_alloc_ctor(12, 3, 7);
lean_ctor_set(v___x_2108_, 0, v___x_2103_);
lean_ctor_set(v___x_2108_, 1, v_p_2100_);
lean_ctor_set(v___x_2108_, 2, v_d_2101_);
lean_ctor_set_uint16(v___x_2108_, sizeof(void*)*3, v___x_2102_);
lean_ctor_set_uint8(v___x_2108_, sizeof(void*)*3 + 4, v___x_2104_);
lean_ctor_set_uint8(v___x_2108_, sizeof(void*)*3 + 5, v___x_2105_);
lean_ctor_set_uint8(v___x_2108_, sizeof(void*)*3 + 6, v___x_2106_);
lean_ctor_set_uint16(v___x_2108_, sizeof(void*)*3 + 2, v___x_2107_);
return v___x_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_guarded___override(lean_object* v_00_u03c4_2109_, lean_object* v_p_2110_, lean_object* v_d_2111_){
_start:
{
lean_object* v___x_2112_; 
v___x_2112_ = l_Lean_Fmt_Doc_guarded___override___redArg(v_p_2110_, v_d_2111_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_costing___override___redArg(lean_object* v_cost_2113_, lean_object* v_d_2114_){
_start:
{
uint16_t v___x_2115_; lean_object* v___x_2116_; uint8_t v___x_2117_; uint8_t v___x_2118_; uint8_t v___x_2119_; uint16_t v___x_2120_; lean_object* v___x_2121_; 
v___x_2115_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_d_2114_);
v___x_2116_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_2114_);
v___x_2117_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_2114_);
v___x_2118_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_2114_);
v___x_2119_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_2114_);
v___x_2120_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_d_2114_);
v___x_2121_ = lean_alloc_ctor(13, 3, 7);
lean_ctor_set(v___x_2121_, 0, v___x_2116_);
lean_ctor_set(v___x_2121_, 1, v_cost_2113_);
lean_ctor_set(v___x_2121_, 2, v_d_2114_);
lean_ctor_set_uint16(v___x_2121_, sizeof(void*)*3, v___x_2115_);
lean_ctor_set_uint8(v___x_2121_, sizeof(void*)*3 + 4, v___x_2117_);
lean_ctor_set_uint8(v___x_2121_, sizeof(void*)*3 + 5, v___x_2118_);
lean_ctor_set_uint8(v___x_2121_, sizeof(void*)*3 + 6, v___x_2119_);
lean_ctor_set_uint16(v___x_2121_, sizeof(void*)*3 + 2, v___x_2120_);
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_costing___override(lean_object* v_00_u03c4_2122_, lean_object* v_cost_2123_, lean_object* v_d_2124_){
_start:
{
lean_object* v___x_2125_; 
v___x_2125_ = l_Lean_Fmt_Doc_costing___override___redArg(v_cost_2123_, v_d_2124_);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_either___override___redArg___lam__0(lean_object* v_x1_2126_, lean_object* v_x2_2127_){
_start:
{
uint8_t v___x_2128_; 
v___x_2128_ = lean_nat_dec_le(v_x1_2126_, v_x2_2127_);
if (v___x_2128_ == 0)
{
lean_inc(v_x1_2126_);
return v_x1_2126_;
}
else
{
lean_inc(v_x2_2127_);
return v_x2_2127_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_either___override___redArg___lam__0___boxed(lean_object* v_x1_2129_, lean_object* v_x2_2130_){
_start:
{
lean_object* v_res_2131_; 
v_res_2131_ = l_Lean_Fmt_Doc_either___override___redArg___lam__0(v_x1_2129_, v_x2_2130_);
lean_dec(v_x2_2130_);
lean_dec(v_x1_2129_);
return v_res_2131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_either___override___redArg(lean_object* v_a_2133_, lean_object* v_b_2134_){
_start:
{
lean_object* v___f_2135_; uint16_t v___x_2136_; uint16_t v___x_2137_; uint16_t v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; uint8_t v___x_2142_; uint8_t v___x_2143_; uint8_t v___x_2144_; uint8_t v___x_2145_; uint8_t v___x_2146_; uint8_t v___x_2147_; uint8_t v___x_2148_; uint16_t v___x_2149_; uint16_t v___x_2150_; uint16_t v___x_2151_; lean_object* v___x_2152_; 
v___f_2135_ = ((lean_object*)(l_Lean_Fmt_Doc_either___override___redArg___closed__0));
v___x_2136_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_a_2133_);
v___x_2137_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_b_2134_);
v___x_2138_ = lean_uint16_land(v___x_2136_, v___x_2137_);
v___x_2139_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_a_2133_);
v___x_2140_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_b_2134_);
v___x_2141_ = l_Option_merge___redArg(v___f_2135_, v___x_2139_, v___x_2140_);
v___x_2142_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_a_2133_);
v___x_2143_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_b_2134_);
v___x_2144_ = l_Lean_Fmt_Doc_AlwaysEmptiness_max(v___x_2142_, v___x_2143_);
v___x_2145_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_a_2133_);
v___x_2146_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_b_2134_);
v___x_2147_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_max(v___x_2145_, v___x_2146_);
v___x_2148_ = 4;
v___x_2149_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_a_2133_);
v___x_2150_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_b_2134_);
v___x_2151_ = lean_uint16_lor(v___x_2149_, v___x_2150_);
v___x_2152_ = lean_alloc_ctor(14, 3, 7);
lean_ctor_set(v___x_2152_, 0, v___x_2141_);
lean_ctor_set(v___x_2152_, 1, v_a_2133_);
lean_ctor_set(v___x_2152_, 2, v_b_2134_);
lean_ctor_set_uint16(v___x_2152_, sizeof(void*)*3, v___x_2138_);
lean_ctor_set_uint8(v___x_2152_, sizeof(void*)*3 + 4, v___x_2144_);
lean_ctor_set_uint8(v___x_2152_, sizeof(void*)*3 + 5, v___x_2147_);
lean_ctor_set_uint8(v___x_2152_, sizeof(void*)*3 + 6, v___x_2148_);
lean_ctor_set_uint16(v___x_2152_, sizeof(void*)*3 + 2, v___x_2151_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_either___override(lean_object* v_00_u03c4_2153_, lean_object* v_a_2154_, lean_object* v_b_2155_){
_start:
{
lean_object* v___x_2156_; 
v___x_2156_ = l_Lean_Fmt_Doc_either___override___redArg(v_a_2154_, v_b_2155_);
return v___x_2156_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_Doc_failureSet___override(lean_object* v_00_u03c4_2157_, lean_object* v_x_2158_){
_start:
{
uint16_t v___x_2159_; 
v___x_2159_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_x_2158_);
return v___x_2159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_failureSet___override___boxed(lean_object* v_00_u03c4_2160_, lean_object* v_x_2161_){
_start:
{
uint16_t v_res_2162_; lean_object* v_r_2163_; 
v_res_2162_ = l_Lean_Fmt_Doc_failureSet___override(v_00_u03c4_2160_, v_x_2161_);
lean_dec(v_x_2161_);
v_r_2163_ = lean_box(v_res_2162_);
return v_r_2163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maxNewlineCount_x3f___override(lean_object* v_00_u03c4_2164_, lean_object* v_x_2165_){
_start:
{
lean_object* v___x_2166_; 
v___x_2166_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_x_2165_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___boxed(lean_object* v_00_u03c4_2167_, lean_object* v_x_2168_){
_start:
{
lean_object* v_res_2169_; 
v_res_2169_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override(v_00_u03c4_2167_, v_x_2168_);
lean_dec(v_x_2168_);
return v_res_2169_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_alwaysEmptiness___override(lean_object* v_00_u03c4_2170_, lean_object* v_x_2171_){
_start:
{
uint8_t v___x_2172_; 
v___x_2172_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_x_2171_);
return v___x_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_alwaysEmptiness___override___boxed(lean_object* v_00_u03c4_2173_, lean_object* v_x_2174_){
_start:
{
uint8_t v_res_2175_; lean_object* v_r_2176_; 
v_res_2175_ = l_Lean_Fmt_Doc_alwaysEmptiness___override(v_00_u03c4_2173_, v_x_2174_);
lean_dec(v_x_2174_);
v_r_2176_ = lean_box(v_res_2175_);
return v_r_2176_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_alwaysNonEmptiness___override(lean_object* v_00_u03c4_2177_, lean_object* v_x_2178_){
_start:
{
uint8_t v___x_2179_; 
v___x_2179_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_x_2178_);
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_alwaysNonEmptiness___override___boxed(lean_object* v_00_u03c4_2180_, lean_object* v_x_2181_){
_start:
{
uint8_t v_res_2182_; lean_object* v_r_2183_; 
v_res_2182_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override(v_00_u03c4_2180_, v_x_2181_);
lean_dec(v_x_2181_);
v_r_2183_ = lean_box(v_res_2182_);
return v_r_2183_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_atomicness___override(lean_object* v_00_u03c4_2184_, lean_object* v_x_2185_){
_start:
{
uint8_t v___x_2186_; 
v___x_2186_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_x_2185_);
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_atomicness___override___boxed(lean_object* v_00_u03c4_2187_, lean_object* v_x_2188_){
_start:
{
uint8_t v_res_2189_; lean_object* v_r_2190_; 
v_res_2189_ = l_Lean_Fmt_Doc_atomicness___override(v_00_u03c4_2187_, v_x_2188_);
lean_dec(v_x_2188_);
v_r_2190_ = lean_box(v_res_2189_);
return v_r_2190_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_Doc_neverFailsSet___override(lean_object* v_00_u03c4_2191_, lean_object* v_x_2192_){
_start:
{
uint16_t v___x_2193_; 
v___x_2193_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_x_2192_);
return v___x_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_neverFailsSet___override___boxed(lean_object* v_00_u03c4_2194_, lean_object* v_x_2195_){
_start:
{
uint16_t v_res_2196_; lean_object* v_r_2197_; 
v_res_2196_ = l_Lean_Fmt_Doc_neverFailsSet___override(v_00_u03c4_2194_, v_x_2195_);
lean_dec(v_x_2195_);
v_r_2197_ = lean_box(v_res_2196_);
return v_r_2197_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg___lam__0(uint8_t v_s_2198_, uint16_t v___x_2199_, uint8_t v___y_2200_, lean_object* v_b_2201_, uint8_t v_isMidFull_2202_, uint8_t v_isMidInitial_2203_){
_start:
{
uint8_t v___x_2204_; uint8_t v___x_2205_; uint8_t v___x_2206_; uint8_t v___x_2207_; uint8_t v___x_2208_; uint8_t v___x_2209_; uint8_t v___x_2210_; uint8_t v___x_2211_; uint8_t v___x_2212_; uint8_t v___x_2213_; uint16_t v___x_2214_; uint16_t v___x_2215_; uint16_t v___x_2216_; uint16_t v___x_2217_; uint16_t v___x_2218_; uint8_t v___x_2219_; 
v___x_2204_ = 254;
v___x_2205_ = lean_uint8_land(v_s_2198_, v___x_2204_);
v___x_2206_ = lean_bool_to_uint8(v_isMidFull_2202_);
v___x_2207_ = lean_uint8_lor(v___x_2205_, v___x_2206_);
v___x_2208_ = 251;
v___x_2209_ = lean_uint8_land(v___x_2207_, v___x_2208_);
v___x_2210_ = lean_bool_to_uint8(v_isMidInitial_2203_);
v___x_2211_ = 2;
v___x_2212_ = lean_uint8_shift_left(v___x_2210_, v___x_2211_);
v___x_2213_ = lean_uint8_lor(v___x_2209_, v___x_2212_);
v___x_2214_ = lean_uint8_to_uint16(v___x_2213_);
v___x_2215_ = lean_uint16_shift_right(v___x_2199_, v___x_2214_);
v___x_2216_ = 1;
v___x_2217_ = lean_uint16_land(v___x_2215_, v___x_2216_);
v___x_2218_ = 0;
v___x_2219_ = lean_uint16_dec_eq(v___x_2217_, v___x_2218_);
if (v___x_2219_ == 0)
{
return v___y_2200_;
}
else
{
uint8_t v___x_2220_; uint8_t v___x_2221_; uint8_t v___x_2222_; uint8_t v___x_2223_; uint8_t v___x_2224_; uint8_t v___x_2225_; uint8_t v___x_2226_; uint8_t v___x_2227_; uint8_t v___x_2228_; uint8_t v___x_2229_; uint16_t v___x_2230_; uint16_t v___x_2231_; uint16_t v___x_2232_; uint16_t v___x_2233_; uint8_t v___x_2234_; 
v___x_2220_ = 253;
v___x_2221_ = lean_uint8_land(v_s_2198_, v___x_2220_);
v___x_2222_ = 1;
v___x_2223_ = lean_uint8_shift_left(v___x_2206_, v___x_2222_);
v___x_2224_ = lean_uint8_lor(v___x_2221_, v___x_2223_);
v___x_2225_ = 247;
v___x_2226_ = lean_uint8_land(v___x_2224_, v___x_2225_);
v___x_2227_ = 3;
v___x_2228_ = lean_uint8_shift_left(v___x_2210_, v___x_2227_);
v___x_2229_ = lean_uint8_lor(v___x_2226_, v___x_2228_);
v___x_2230_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_b_2201_);
v___x_2231_ = lean_uint8_to_uint16(v___x_2229_);
v___x_2232_ = lean_uint16_shift_right(v___x_2230_, v___x_2231_);
v___x_2233_ = lean_uint16_land(v___x_2232_, v___x_2216_);
v___x_2234_ = lean_uint16_dec_eq(v___x_2233_, v___x_2218_);
if (v___x_2234_ == 0)
{
return v___y_2200_;
}
else
{
return v___x_2234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg___lam__0___boxed(lean_object* v_s_2235_, lean_object* v___x_2236_, lean_object* v___y_2237_, lean_object* v_b_2238_, lean_object* v_isMidFull_2239_, lean_object* v_isMidInitial_2240_){
_start:
{
uint8_t v_s_boxed_2241_; uint16_t v___x_2199__boxed_2242_; uint8_t v___y_2200__boxed_2243_; uint8_t v_isMidFull_boxed_2244_; uint8_t v_isMidInitial_boxed_2245_; uint8_t v_res_2246_; lean_object* v_r_2247_; 
v_s_boxed_2241_ = lean_unbox(v_s_2235_);
v___x_2199__boxed_2242_ = lean_unbox(v___x_2236_);
v___y_2200__boxed_2243_ = lean_unbox(v___y_2237_);
v_isMidFull_boxed_2244_ = lean_unbox(v_isMidFull_2239_);
v_isMidInitial_boxed_2245_ = lean_unbox(v_isMidInitial_2240_);
v_res_2246_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg___lam__0(v_s_boxed_2241_, v___x_2199__boxed_2242_, v___y_2200__boxed_2243_, v_b_2238_, v_isMidFull_boxed_2244_, v_isMidInitial_boxed_2245_);
lean_dec(v_b_2238_);
v_r_2247_ = lean_box(v_res_2246_);
return v_r_2247_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg(uint16_t v___x_2248_, uint8_t v___y_2249_, lean_object* v_b_2250_, lean_object* v_x_2251_, uint16_t v_x_2252_){
_start:
{
lean_object* v_zero_2253_; uint8_t v_isZero_2254_; 
v_zero_2253_ = lean_unsigned_to_nat(0u);
v_isZero_2254_ = lean_nat_dec_eq(v_x_2251_, v_zero_2253_);
if (v_isZero_2254_ == 1)
{
lean_dec(v_x_2251_);
return v_x_2252_;
}
else
{
lean_object* v_one_2255_; lean_object* v_n_2256_; uint8_t v_s_2263_; uint8_t v___x_2264_; 
v_one_2255_ = lean_unsigned_to_nat(1u);
v_n_2256_ = lean_nat_sub(v_x_2251_, v_one_2255_);
lean_dec(v_x_2251_);
v_s_2263_ = lean_uint8_of_nat(v_n_2256_);
v___x_2264_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg___lam__0(v_s_2263_, v___x_2248_, v___y_2249_, v_b_2250_, v_isZero_2254_, v_isZero_2254_);
if (v___x_2264_ == 0)
{
uint8_t v___x_2265_; uint8_t v___x_2266_; 
v___x_2265_ = 1;
v___x_2266_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg___lam__0(v_s_2263_, v___x_2248_, v___y_2249_, v_b_2250_, v___x_2264_, v___x_2265_);
if (v___x_2266_ == 0)
{
uint8_t v___x_2267_; 
v___x_2267_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg___lam__0(v_s_2263_, v___x_2248_, v___y_2249_, v_b_2250_, v___x_2265_, v___x_2266_);
if (v___x_2267_ == 0)
{
uint8_t v___x_2268_; 
v___x_2268_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg___lam__0(v_s_2263_, v___x_2248_, v___y_2249_, v_b_2250_, v___x_2265_, v___x_2265_);
if (v___x_2268_ == 0)
{
v_x_2251_ = v_n_2256_;
goto _start;
}
else
{
goto v___jp_2257_;
}
}
else
{
goto v___jp_2257_;
}
}
else
{
goto v___jp_2257_;
}
}
else
{
goto v___jp_2257_;
}
v___jp_2257_:
{
uint16_t v___x_2258_; uint16_t v___x_2259_; uint16_t v___x_2260_; uint16_t v___x_2261_; 
v___x_2258_ = 1;
v___x_2259_ = lean_uint16_of_nat(v_n_2256_);
v___x_2260_ = lean_uint16_shift_left(v___x_2258_, v___x_2259_);
v___x_2261_ = lean_uint16_lor(v_x_2252_, v___x_2260_);
v_x_2251_ = v_n_2256_;
v_x_2252_ = v___x_2261_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg___boxed(lean_object* v___x_2270_, lean_object* v___y_2271_, lean_object* v_b_2272_, lean_object* v_x_2273_, lean_object* v_x_2274_){
_start:
{
uint16_t v___x_2267__boxed_2275_; uint8_t v___y_2268__boxed_2276_; uint16_t v_x_2270__boxed_2277_; uint16_t v_res_2278_; lean_object* v_r_2279_; 
v___x_2267__boxed_2275_ = lean_unbox(v___x_2270_);
v___y_2268__boxed_2276_ = lean_unbox(v___y_2271_);
v_x_2270__boxed_2277_ = lean_unbox(v_x_2274_);
v_res_2278_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg(v___x_2267__boxed_2275_, v___y_2268__boxed_2276_, v_b_2272_, v_x_2273_, v_x_2270__boxed_2277_);
lean_dec(v_b_2272_);
v_r_2279_ = lean_box(v_res_2278_);
return v_r_2279_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16___redArg(uint16_t v___x_2280_, uint8_t v___y_2281_, lean_object* v_b_2282_){
_start:
{
lean_object* v___x_2283_; uint16_t v___x_2284_; uint16_t v___x_2285_; 
v___x_2283_ = lean_unsigned_to_nat(16u);
v___x_2284_ = 0;
v___x_2285_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg(v___x_2280_, v___y_2281_, v_b_2282_, v___x_2283_, v___x_2284_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16___redArg___boxed(lean_object* v___x_2286_, lean_object* v___y_2287_, lean_object* v_b_2288_){
_start:
{
uint16_t v___x_2305__boxed_2289_; uint8_t v___y_2306__boxed_2290_; uint16_t v_res_2291_; lean_object* v_r_2292_; 
v___x_2305__boxed_2289_ = lean_unbox(v___x_2286_);
v___y_2306__boxed_2290_ = lean_unbox(v___y_2287_);
v_res_2291_ = l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16___redArg(v___x_2305__boxed_2289_, v___y_2306__boxed_2290_, v_b_2288_);
lean_dec(v_b_2288_);
v_r_2292_ = lean_box(v_res_2291_);
return v_r_2292_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15_spec__21___redArg___lam__0(uint8_t v_s_2293_, uint16_t v___x_2294_, uint16_t v___x_2295_, lean_object* v_b_2296_, uint8_t v___x_2297_, uint8_t v_isMidFull_2298_, uint8_t v_isMidInitial_2299_){
_start:
{
uint8_t v___x_2300_; uint8_t v___x_2301_; uint8_t v___x_2302_; uint8_t v___x_2303_; uint8_t v___x_2304_; uint8_t v___x_2305_; uint8_t v___x_2306_; uint8_t v___x_2307_; uint8_t v___x_2308_; uint8_t v___x_2309_; uint16_t v___x_2310_; uint16_t v___x_2311_; uint16_t v___x_2312_; uint16_t v___x_2313_; uint8_t v___x_2314_; 
v___x_2300_ = 254;
v___x_2301_ = lean_uint8_land(v_s_2293_, v___x_2300_);
v___x_2302_ = lean_bool_to_uint8(v_isMidFull_2298_);
v___x_2303_ = lean_uint8_lor(v___x_2301_, v___x_2302_);
v___x_2304_ = 251;
v___x_2305_ = lean_uint8_land(v___x_2303_, v___x_2304_);
v___x_2306_ = lean_bool_to_uint8(v_isMidInitial_2299_);
v___x_2307_ = 2;
v___x_2308_ = lean_uint8_shift_left(v___x_2306_, v___x_2307_);
v___x_2309_ = lean_uint8_lor(v___x_2305_, v___x_2308_);
v___x_2310_ = lean_uint8_to_uint16(v___x_2309_);
v___x_2311_ = lean_uint16_shift_right(v___x_2294_, v___x_2310_);
v___x_2312_ = 1;
v___x_2313_ = lean_uint16_land(v___x_2311_, v___x_2312_);
v___x_2314_ = lean_uint16_dec_eq(v___x_2313_, v___x_2295_);
if (v___x_2314_ == 0)
{
uint8_t v___x_2315_; uint8_t v___x_2316_; uint8_t v___x_2317_; uint8_t v___x_2318_; uint8_t v___x_2319_; uint8_t v___x_2320_; uint8_t v___x_2321_; uint8_t v___x_2322_; uint8_t v___x_2323_; uint8_t v___x_2324_; uint16_t v___x_2325_; uint16_t v___x_2326_; uint16_t v___x_2327_; uint16_t v___x_2328_; uint8_t v___x_2329_; 
v___x_2315_ = 253;
v___x_2316_ = lean_uint8_land(v_s_2293_, v___x_2315_);
v___x_2317_ = 1;
v___x_2318_ = lean_uint8_shift_left(v___x_2302_, v___x_2317_);
v___x_2319_ = lean_uint8_lor(v___x_2316_, v___x_2318_);
v___x_2320_ = 247;
v___x_2321_ = lean_uint8_land(v___x_2319_, v___x_2320_);
v___x_2322_ = 3;
v___x_2323_ = lean_uint8_shift_left(v___x_2306_, v___x_2322_);
v___x_2324_ = lean_uint8_lor(v___x_2321_, v___x_2323_);
v___x_2325_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_b_2296_);
v___x_2326_ = lean_uint8_to_uint16(v___x_2324_);
v___x_2327_ = lean_uint16_shift_right(v___x_2325_, v___x_2326_);
v___x_2328_ = lean_uint16_land(v___x_2327_, v___x_2312_);
v___x_2329_ = lean_uint16_dec_eq(v___x_2328_, v___x_2295_);
if (v___x_2329_ == 0)
{
uint8_t v___x_2330_; 
v___x_2330_ = 1;
return v___x_2330_;
}
else
{
return v___x_2297_;
}
}
else
{
return v___x_2297_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15_spec__21___redArg___lam__0___boxed(lean_object* v_s_2331_, lean_object* v___x_2332_, lean_object* v___x_2333_, lean_object* v_b_2334_, lean_object* v___x_2335_, lean_object* v_isMidFull_2336_, lean_object* v_isMidInitial_2337_){
_start:
{
uint8_t v_s_boxed_2338_; uint16_t v___x_2317__boxed_2339_; uint16_t v___x_2318__boxed_2340_; uint8_t v___x_2319__boxed_2341_; uint8_t v_isMidFull_boxed_2342_; uint8_t v_isMidInitial_boxed_2343_; uint8_t v_res_2344_; lean_object* v_r_2345_; 
v_s_boxed_2338_ = lean_unbox(v_s_2331_);
v___x_2317__boxed_2339_ = lean_unbox(v___x_2332_);
v___x_2318__boxed_2340_ = lean_unbox(v___x_2333_);
v___x_2319__boxed_2341_ = lean_unbox(v___x_2335_);
v_isMidFull_boxed_2342_ = lean_unbox(v_isMidFull_2336_);
v_isMidInitial_boxed_2343_ = lean_unbox(v_isMidInitial_2337_);
v_res_2344_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15_spec__21___redArg___lam__0(v_s_boxed_2338_, v___x_2317__boxed_2339_, v___x_2318__boxed_2340_, v_b_2334_, v___x_2319__boxed_2341_, v_isMidFull_boxed_2342_, v_isMidInitial_boxed_2343_);
lean_dec(v_b_2334_);
v_r_2345_ = lean_box(v_res_2344_);
return v_r_2345_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15_spec__21___redArg(uint16_t v___x_2346_, lean_object* v_b_2347_, uint16_t v___x_2348_, lean_object* v_x_2349_, uint16_t v_x_2350_){
_start:
{
lean_object* v_zero_2351_; uint8_t v_isZero_2352_; 
v_zero_2351_ = lean_unsigned_to_nat(0u);
v_isZero_2352_ = lean_nat_dec_eq(v_x_2349_, v_zero_2351_);
if (v_isZero_2352_ == 1)
{
lean_dec(v_x_2349_);
return v_x_2350_;
}
else
{
uint16_t v___x_2353_; uint8_t v___x_2354_; lean_object* v_one_2355_; lean_object* v_n_2356_; uint8_t v_s_2363_; uint8_t v___x_2364_; 
v___x_2353_ = 0;
v___x_2354_ = lean_uint16_dec_eq(v___x_2348_, v___x_2353_);
v_one_2355_ = lean_unsigned_to_nat(1u);
v_n_2356_ = lean_nat_sub(v_x_2349_, v_one_2355_);
lean_dec(v_x_2349_);
v_s_2363_ = lean_uint8_of_nat(v_n_2356_);
v___x_2364_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15_spec__21___redArg___lam__0(v_s_2363_, v___x_2346_, v___x_2353_, v_b_2347_, v___x_2354_, v_isZero_2352_, v_isZero_2352_);
if (v___x_2364_ == 0)
{
uint8_t v___x_2365_; uint8_t v___x_2366_; 
v___x_2365_ = 1;
v___x_2366_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15_spec__21___redArg___lam__0(v_s_2363_, v___x_2346_, v___x_2353_, v_b_2347_, v___x_2354_, v___x_2364_, v___x_2365_);
if (v___x_2366_ == 0)
{
uint8_t v___x_2367_; 
v___x_2367_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15_spec__21___redArg___lam__0(v_s_2363_, v___x_2346_, v___x_2353_, v_b_2347_, v___x_2354_, v___x_2365_, v___x_2366_);
if (v___x_2367_ == 0)
{
uint8_t v___x_2368_; 
v___x_2368_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15_spec__21___redArg___lam__0(v_s_2363_, v___x_2346_, v___x_2353_, v_b_2347_, v___x_2354_, v___x_2365_, v___x_2365_);
if (v___x_2368_ == 0)
{
v_x_2349_ = v_n_2356_;
goto _start;
}
else
{
goto v___jp_2357_;
}
}
else
{
goto v___jp_2357_;
}
}
else
{
goto v___jp_2357_;
}
}
else
{
goto v___jp_2357_;
}
v___jp_2357_:
{
uint16_t v___x_2358_; uint16_t v___x_2359_; uint16_t v___x_2360_; uint16_t v___x_2361_; 
v___x_2358_ = 1;
v___x_2359_ = lean_uint16_of_nat(v_n_2356_);
v___x_2360_ = lean_uint16_shift_left(v___x_2358_, v___x_2359_);
v___x_2361_ = lean_uint16_lor(v_x_2350_, v___x_2360_);
v_x_2349_ = v_n_2356_;
v_x_2350_ = v___x_2361_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15_spec__21___redArg___boxed(lean_object* v___x_2370_, lean_object* v_b_2371_, lean_object* v___x_2372_, lean_object* v_x_2373_, lean_object* v_x_2374_){
_start:
{
uint16_t v___x_2388__boxed_2375_; uint16_t v___x_2389__boxed_2376_; uint16_t v_x_2391__boxed_2377_; uint16_t v_res_2378_; lean_object* v_r_2379_; 
v___x_2388__boxed_2375_ = lean_unbox(v___x_2370_);
v___x_2389__boxed_2376_ = lean_unbox(v___x_2372_);
v_x_2391__boxed_2377_ = lean_unbox(v_x_2374_);
v_res_2378_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15_spec__21___redArg(v___x_2388__boxed_2375_, v_b_2371_, v___x_2389__boxed_2376_, v_x_2373_, v_x_2391__boxed_2377_);
lean_dec(v_b_2371_);
v_r_2379_ = lean_box(v_res_2378_);
return v_r_2379_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15___redArg(uint16_t v___x_2380_, lean_object* v_b_2381_, uint16_t v___x_2382_){
_start:
{
lean_object* v___x_2383_; uint16_t v___x_2384_; uint16_t v___x_2385_; 
v___x_2383_ = lean_unsigned_to_nat(16u);
v___x_2384_ = 0;
v___x_2385_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15_spec__21___redArg(v___x_2380_, v_b_2381_, v___x_2382_, v___x_2383_, v___x_2384_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15___redArg___boxed(lean_object* v___x_2386_, lean_object* v_b_2387_, lean_object* v___x_2388_){
_start:
{
uint16_t v___x_2430__boxed_2389_; uint16_t v___x_2431__boxed_2390_; uint16_t v_res_2391_; lean_object* v_r_2392_; 
v___x_2430__boxed_2389_ = lean_unbox(v___x_2386_);
v___x_2431__boxed_2390_ = lean_unbox(v___x_2388_);
v_res_2391_ = l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15___redArg(v___x_2430__boxed_2389_, v_b_2387_, v___x_2431__boxed_2390_);
lean_dec(v_b_2387_);
v_r_2392_ = lean_box(v_res_2391_);
return v_r_2392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_append___override___redArg(lean_object* v_a_2393_, lean_object* v_b_2394_){
_start:
{
lean_object* v___y_2396_; uint8_t v___y_2397_; uint16_t v___y_2398_; uint8_t v___y_2399_; uint8_t v___y_2400_; lean_object* v___f_2410_; uint16_t v___y_2412_; uint16_t v___x_2429_; uint16_t v___x_2430_; uint8_t v___x_2431_; 
v___f_2410_ = ((lean_object*)(l_Lean_Fmt_instHAddTagIdNat___closed__0));
v___x_2429_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_a_2393_);
v___x_2430_ = 65535;
v___x_2431_ = lean_uint16_dec_eq(v___x_2429_, v___x_2430_);
if (v___x_2431_ == 0)
{
uint16_t v___x_2432_; uint8_t v___x_2433_; 
v___x_2432_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_b_2394_);
v___x_2433_ = lean_uint16_dec_eq(v___x_2432_, v___x_2430_);
if (v___x_2433_ == 0)
{
uint16_t v___x_2434_; uint16_t v___x_2435_; 
v___x_2434_ = l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16___redArg(v___x_2429_, v___x_2433_, v_b_2394_);
v___x_2435_ = lean_uint16_complement(v___x_2434_);
v___y_2412_ = v___x_2435_;
goto v___jp_2411_;
}
else
{
v___y_2412_ = v___x_2430_;
goto v___jp_2411_;
}
}
else
{
v___y_2412_ = v___x_2430_;
goto v___jp_2411_;
}
v___jp_2395_:
{
uint16_t v___x_2401_; uint16_t v___x_2402_; uint8_t v___x_2403_; 
v___x_2401_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_a_2393_);
v___x_2402_ = 0;
v___x_2403_ = lean_uint16_dec_eq(v___x_2401_, v___x_2402_);
if (v___x_2403_ == 0)
{
uint16_t v___x_2404_; uint8_t v___x_2405_; 
v___x_2404_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_b_2394_);
v___x_2405_ = lean_uint16_dec_eq(v___x_2404_, v___x_2402_);
if (v___x_2405_ == 0)
{
uint16_t v___x_2406_; lean_object* v___x_2407_; 
v___x_2406_ = l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15___redArg(v___x_2401_, v_b_2394_, v___x_2404_);
v___x_2407_ = lean_alloc_ctor(15, 3, 7);
lean_ctor_set(v___x_2407_, 0, v___y_2396_);
lean_ctor_set(v___x_2407_, 1, v_a_2393_);
lean_ctor_set(v___x_2407_, 2, v_b_2394_);
lean_ctor_set_uint16(v___x_2407_, sizeof(void*)*3, v___y_2398_);
lean_ctor_set_uint8(v___x_2407_, sizeof(void*)*3 + 4, v___y_2397_);
lean_ctor_set_uint8(v___x_2407_, sizeof(void*)*3 + 5, v___y_2399_);
lean_ctor_set_uint8(v___x_2407_, sizeof(void*)*3 + 6, v___y_2400_);
lean_ctor_set_uint16(v___x_2407_, sizeof(void*)*3 + 2, v___x_2406_);
return v___x_2407_;
}
else
{
lean_object* v___x_2408_; 
v___x_2408_ = lean_alloc_ctor(15, 3, 7);
lean_ctor_set(v___x_2408_, 0, v___y_2396_);
lean_ctor_set(v___x_2408_, 1, v_a_2393_);
lean_ctor_set(v___x_2408_, 2, v_b_2394_);
lean_ctor_set_uint16(v___x_2408_, sizeof(void*)*3, v___y_2398_);
lean_ctor_set_uint8(v___x_2408_, sizeof(void*)*3 + 4, v___y_2397_);
lean_ctor_set_uint8(v___x_2408_, sizeof(void*)*3 + 5, v___y_2399_);
lean_ctor_set_uint8(v___x_2408_, sizeof(void*)*3 + 6, v___y_2400_);
lean_ctor_set_uint16(v___x_2408_, sizeof(void*)*3 + 2, v___x_2402_);
return v___x_2408_;
}
}
else
{
lean_object* v___x_2409_; 
v___x_2409_ = lean_alloc_ctor(15, 3, 7);
lean_ctor_set(v___x_2409_, 0, v___y_2396_);
lean_ctor_set(v___x_2409_, 1, v_a_2393_);
lean_ctor_set(v___x_2409_, 2, v_b_2394_);
lean_ctor_set_uint16(v___x_2409_, sizeof(void*)*3, v___y_2398_);
lean_ctor_set_uint8(v___x_2409_, sizeof(void*)*3 + 4, v___y_2397_);
lean_ctor_set_uint8(v___x_2409_, sizeof(void*)*3 + 5, v___y_2399_);
lean_ctor_set_uint8(v___x_2409_, sizeof(void*)*3 + 6, v___y_2400_);
lean_ctor_set_uint16(v___x_2409_, sizeof(void*)*3 + 2, v___x_2402_);
return v___x_2409_;
}
}
v___jp_2411_:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; uint8_t v___x_2416_; uint8_t v___x_2417_; uint8_t v___x_2418_; uint8_t v___x_2419_; uint8_t v___x_2420_; uint8_t v___x_2421_; 
v___x_2413_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_a_2393_);
v___x_2414_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_b_2394_);
v___x_2415_ = l_Option_merge___redArg(v___f_2410_, v___x_2413_, v___x_2414_);
v___x_2416_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_a_2393_);
v___x_2417_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_b_2394_);
v___x_2418_ = l_Lean_Fmt_Doc_AlwaysEmptiness_max(v___x_2416_, v___x_2417_);
v___x_2419_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_a_2393_);
v___x_2420_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_b_2394_);
v___x_2421_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_max(v___x_2419_, v___x_2420_);
if (v___x_2416_ == 0)
{
uint8_t v___x_2422_; 
v___x_2422_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_b_2394_);
v___y_2396_ = v___x_2415_;
v___y_2397_ = v___x_2418_;
v___y_2398_ = v___y_2412_;
v___y_2399_ = v___x_2421_;
v___y_2400_ = v___x_2422_;
goto v___jp_2395_;
}
else
{
if (v___x_2417_ == 0)
{
uint8_t v___x_2423_; 
v___x_2423_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_a_2393_);
v___y_2396_ = v___x_2415_;
v___y_2397_ = v___x_2418_;
v___y_2398_ = v___y_2412_;
v___y_2399_ = v___x_2421_;
v___y_2400_ = v___x_2423_;
goto v___jp_2395_;
}
else
{
uint8_t v___x_2424_; uint8_t v___x_2425_; uint8_t v___x_2426_; uint8_t v___x_2427_; uint8_t v___x_2428_; 
v___x_2424_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_a_2393_);
v___x_2425_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_b_2394_);
v___x_2426_ = l_Lean_Fmt_Doc_Atomicness_max(v___x_2424_, v___x_2425_);
v___x_2427_ = 2;
v___x_2428_ = l_Lean_Fmt_Doc_Atomicness_max(v___x_2426_, v___x_2427_);
v___y_2396_ = v___x_2415_;
v___y_2397_ = v___x_2418_;
v___y_2398_ = v___y_2412_;
v___y_2399_ = v___x_2421_;
v___y_2400_ = v___x_2428_;
goto v___jp_2395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_append___override(lean_object* v_00_u03c4_2436_, lean_object* v_a_2437_, lean_object* v_b_2438_){
_start:
{
lean_object* v___x_2439_; 
v___x_2439_ = l_Lean_Fmt_Doc_append___override___redArg(v_a_2437_, v_b_2438_);
return v___x_2439_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15(uint16_t v___x_2440_, lean_object* v_00_u03c4_2441_, lean_object* v_b_2442_, uint16_t v___x_2443_){
_start:
{
uint16_t v___x_2444_; 
v___x_2444_ = l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15___redArg(v___x_2440_, v_b_2442_, v___x_2443_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15___boxed(lean_object* v___x_2445_, lean_object* v_00_u03c4_2446_, lean_object* v_b_2447_, lean_object* v___x_2448_){
_start:
{
uint16_t v___x_2527__boxed_2449_; uint16_t v___x_2528__boxed_2450_; uint16_t v_res_2451_; lean_object* v_r_2452_; 
v___x_2527__boxed_2449_ = lean_unbox(v___x_2445_);
v___x_2528__boxed_2450_ = lean_unbox(v___x_2448_);
v_res_2451_ = l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15(v___x_2527__boxed_2449_, v_00_u03c4_2446_, v_b_2447_, v___x_2528__boxed_2450_);
lean_dec(v_b_2447_);
v_r_2452_ = lean_box(v_res_2451_);
return v_r_2452_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16(uint16_t v___x_2453_, uint8_t v___y_2454_, lean_object* v_00_u03c4_2455_, lean_object* v_b_2456_){
_start:
{
uint16_t v___x_2457_; 
v___x_2457_ = l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16___redArg(v___x_2453_, v___y_2454_, v_b_2456_);
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16___boxed(lean_object* v___x_2458_, lean_object* v___y_2459_, lean_object* v_00_u03c4_2460_, lean_object* v_b_2461_){
_start:
{
uint16_t v___x_2535__boxed_2462_; uint8_t v___y_2536__boxed_2463_; uint16_t v_res_2464_; lean_object* v_r_2465_; 
v___x_2535__boxed_2462_ = lean_unbox(v___x_2458_);
v___y_2536__boxed_2463_ = lean_unbox(v___y_2459_);
v_res_2464_ = l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16(v___x_2535__boxed_2462_, v___y_2536__boxed_2463_, v_00_u03c4_2460_, v_b_2461_);
lean_dec(v_b_2461_);
v_r_2465_ = lean_box(v_res_2464_);
return v_r_2465_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15_spec__21(uint16_t v___x_2466_, lean_object* v_00_u03c4_2467_, lean_object* v_b_2468_, uint16_t v___x_2469_, lean_object* v_x_2470_, uint16_t v_x_2471_){
_start:
{
uint16_t v___x_2472_; 
v___x_2472_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15_spec__21___redArg(v___x_2466_, v_b_2468_, v___x_2469_, v_x_2470_, v_x_2471_);
return v___x_2472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15_spec__21___boxed(lean_object* v___x_2473_, lean_object* v_00_u03c4_2474_, lean_object* v_b_2475_, lean_object* v___x_2476_, lean_object* v_x_2477_, lean_object* v_x_2478_){
_start:
{
uint16_t v___x_2543__boxed_2479_; uint16_t v___x_2544__boxed_2480_; uint16_t v_x_2546__boxed_2481_; uint16_t v_res_2482_; lean_object* v_r_2483_; 
v___x_2543__boxed_2479_ = lean_unbox(v___x_2473_);
v___x_2544__boxed_2480_ = lean_unbox(v___x_2476_);
v_x_2546__boxed_2481_ = lean_unbox(v_x_2478_);
v_res_2482_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15_spec__21(v___x_2543__boxed_2479_, v_00_u03c4_2474_, v_b_2475_, v___x_2544__boxed_2480_, v_x_2477_, v_x_2546__boxed_2481_);
lean_dec(v_b_2475_);
v_r_2483_ = lean_box(v_res_2482_);
return v_r_2483_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23(uint16_t v___x_2484_, uint8_t v___y_2485_, lean_object* v_00_u03c4_2486_, lean_object* v_b_2487_, lean_object* v_x_2488_, uint16_t v_x_2489_){
_start:
{
uint16_t v___x_2490_; 
v___x_2490_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg(v___x_2484_, v___y_2485_, v_b_2487_, v_x_2488_, v_x_2489_);
return v___x_2490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___boxed(lean_object* v___x_2491_, lean_object* v___y_2492_, lean_object* v_00_u03c4_2493_, lean_object* v_b_2494_, lean_object* v_x_2495_, lean_object* v_x_2496_){
_start:
{
uint16_t v___x_2557__boxed_2497_; uint8_t v___y_2558__boxed_2498_; uint16_t v_x_2560__boxed_2499_; uint16_t v_res_2500_; lean_object* v_r_2501_; 
v___x_2557__boxed_2497_ = lean_unbox(v___x_2491_);
v___y_2558__boxed_2498_ = lean_unbox(v___y_2492_);
v_x_2560__boxed_2499_ = lean_unbox(v_x_2496_);
v_res_2500_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23(v___x_2557__boxed_2497_, v___y_2558__boxed_2498_, v_00_u03c4_2493_, v_b_2494_, v_x_2495_, v_x_2560__boxed_2499_);
lean_dec(v_b_2494_);
v_r_2501_ = lean_box(v_res_2500_);
return v_r_2501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedDoc_default___redArg(){
_start:
{
lean_object* v___x_2503_; 
v___x_2503_ = lean_box(0);
return v___x_2503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedDoc_default___redArg___boxed(lean_object* v___dummy_2504_){
_start:
{
lean_object* v_res_2505_; 
v_res_2505_ = l_Lean_Fmt_instInhabitedDoc_default___redArg();
return v_res_2505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedDoc_default(lean_object* v_00_u03c4_2506_){
_start:
{
lean_object* v___x_2507_; 
v___x_2507_ = lean_box(0);
return v___x_2507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedDoc___redArg(){
_start:
{
lean_object* v___x_2509_; 
v___x_2509_ = lean_box(0);
return v___x_2509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedDoc___redArg___boxed(lean_object* v___dummy_2510_){
_start:
{
lean_object* v_res_2511_; 
v_res_2511_ = l_Lean_Fmt_instInhabitedDoc___redArg();
return v_res_2511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedDoc(lean_object* v_a_2512_){
_start:
{
lean_object* v___x_2513_; 
v___x_2513_ = lean_box(0);
return v___x_2513_;
}
}
static lean_object* _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2(void){
_start:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2517_ = lean_unsigned_to_nat(2u);
v___x_2518_ = lean_nat_to_int(v___x_2517_);
return v___x_2518_;
}
}
static lean_object* _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3(void){
_start:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2519_ = lean_unsigned_to_nat(1u);
v___x_2520_ = lean_nat_to_int(v___x_2519_);
return v___x_2520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprDoc_repr___redArg(lean_object* v_inst_2617_, lean_object* v_x_2618_, lean_object* v_prec_2619_){
_start:
{
lean_object* v___y_2621_; 
switch(lean_obj_tag(v_x_2618_))
{
case 0:
{
lean_object* v___x_2627_; uint8_t v___x_2628_; 
lean_dec_ref(v_inst_2617_);
v___x_2627_ = lean_unsigned_to_nat(1024u);
v___x_2628_ = lean_nat_dec_le(v___x_2627_, v_prec_2619_);
if (v___x_2628_ == 0)
{
lean_object* v___x_2629_; 
v___x_2629_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2621_ = v___x_2629_;
goto v___jp_2620_;
}
else
{
lean_object* v___x_2630_; 
v___x_2630_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2621_ = v___x_2630_;
goto v___jp_2620_;
}
}
case 1:
{
lean_object* v_f_2631_; lean_object* v___y_2633_; lean_object* v___x_2642_; uint8_t v___x_2643_; 
lean_dec_ref(v_inst_2617_);
v_f_2631_ = lean_ctor_get(v_x_2618_, 1);
lean_inc_ref(v_f_2631_);
lean_dec_ref_known(v_x_2618_, 2);
v___x_2642_ = lean_unsigned_to_nat(1024u);
v___x_2643_ = lean_nat_dec_le(v___x_2642_, v_prec_2619_);
if (v___x_2643_ == 0)
{
lean_object* v___x_2644_; 
v___x_2644_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2633_ = v___x_2644_;
goto v___jp_2632_;
}
else
{
lean_object* v___x_2645_; 
v___x_2645_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2633_ = v___x_2645_;
goto v___jp_2632_;
}
v___jp_2632_:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; uint8_t v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2634_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__6));
v___x_2635_ = l_String_quote(v_f_2631_);
v___x_2636_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2636_, 0, v___x_2635_);
v___x_2637_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2637_, 0, v___x_2634_);
lean_ctor_set(v___x_2637_, 1, v___x_2636_);
lean_inc(v___y_2633_);
v___x_2638_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2638_, 0, v___y_2633_);
lean_ctor_set(v___x_2638_, 1, v___x_2637_);
v___x_2639_ = 0;
v___x_2640_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2640_, 0, v___x_2638_);
lean_ctor_set_uint8(v___x_2640_, sizeof(void*)*1, v___x_2639_);
v___x_2641_ = l_Repr_addAppParen(v___x_2640_, v_prec_2619_);
return v___x_2641_;
}
}
case 2:
{
lean_object* v_s_2646_; lean_object* v___y_2648_; lean_object* v___x_2657_; uint8_t v___x_2658_; 
lean_dec_ref(v_inst_2617_);
v_s_2646_ = lean_ctor_get(v_x_2618_, 1);
lean_inc_ref(v_s_2646_);
lean_dec_ref_known(v_x_2618_, 2);
v___x_2657_ = lean_unsigned_to_nat(1024u);
v___x_2658_ = lean_nat_dec_le(v___x_2657_, v_prec_2619_);
if (v___x_2658_ == 0)
{
lean_object* v___x_2659_; 
v___x_2659_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2648_ = v___x_2659_;
goto v___jp_2647_;
}
else
{
lean_object* v___x_2660_; 
v___x_2660_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2648_ = v___x_2660_;
goto v___jp_2647_;
}
v___jp_2647_:
{
lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; uint8_t v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; 
v___x_2649_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__9));
v___x_2650_ = l_String_quote(v_s_2646_);
v___x_2651_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2651_, 0, v___x_2650_);
v___x_2652_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2652_, 0, v___x_2649_);
lean_ctor_set(v___x_2652_, 1, v___x_2651_);
lean_inc(v___y_2648_);
v___x_2653_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2653_, 0, v___y_2648_);
lean_ctor_set(v___x_2653_, 1, v___x_2652_);
v___x_2654_ = 0;
v___x_2655_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2655_, 0, v___x_2653_);
lean_ctor_set_uint8(v___x_2655_, sizeof(void*)*1, v___x_2654_);
v___x_2656_ = l_Repr_addAppParen(v___x_2655_, v_prec_2619_);
return v___x_2656_;
}
}
case 3:
{
lean_object* v_id_2661_; lean_object* v_d_2662_; lean_object* v___x_2663_; lean_object* v___y_2665_; uint8_t v___x_2678_; 
v_id_2661_ = lean_ctor_get(v_x_2618_, 1);
lean_inc(v_id_2661_);
v_d_2662_ = lean_ctor_get(v_x_2618_, 2);
lean_inc(v_d_2662_);
lean_dec_ref_known(v_x_2618_, 3);
v___x_2663_ = lean_unsigned_to_nat(1024u);
v___x_2678_ = lean_nat_dec_le(v___x_2663_, v_prec_2619_);
if (v___x_2678_ == 0)
{
lean_object* v___x_2679_; 
v___x_2679_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2665_ = v___x_2679_;
goto v___jp_2664_;
}
else
{
lean_object* v___x_2680_; 
v___x_2680_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2665_ = v___x_2680_;
goto v___jp_2664_;
}
v___jp_2664_:
{
lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; uint8_t v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; 
v___x_2666_ = lean_box(1);
v___x_2667_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__12));
v___x_2668_ = l_Nat_reprFast(v_id_2661_);
v___x_2669_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2668_);
v___x_2670_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2667_);
lean_ctor_set(v___x_2670_, 1, v___x_2669_);
v___x_2671_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2671_, 0, v___x_2670_);
lean_ctor_set(v___x_2671_, 1, v___x_2666_);
v___x_2672_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2617_, v_d_2662_, v___x_2663_);
v___x_2673_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2673_, 0, v___x_2671_);
lean_ctor_set(v___x_2673_, 1, v___x_2672_);
lean_inc(v___y_2665_);
v___x_2674_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2674_, 0, v___y_2665_);
lean_ctor_set(v___x_2674_, 1, v___x_2673_);
v___x_2675_ = 0;
v___x_2676_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2676_, 0, v___x_2674_);
lean_ctor_set_uint8(v___x_2676_, sizeof(void*)*1, v___x_2675_);
v___x_2677_ = l_Repr_addAppParen(v___x_2676_, v_prec_2619_);
return v___x_2677_;
}
}
case 4:
{
lean_object* v_d_2681_; lean_object* v___x_2682_; lean_object* v___y_2684_; uint8_t v___x_2692_; 
v_d_2681_ = lean_ctor_get(v_x_2618_, 1);
lean_inc(v_d_2681_);
lean_dec_ref_known(v_x_2618_, 2);
v___x_2682_ = lean_unsigned_to_nat(1024u);
v___x_2692_ = lean_nat_dec_le(v___x_2682_, v_prec_2619_);
if (v___x_2692_ == 0)
{
lean_object* v___x_2693_; 
v___x_2693_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2684_ = v___x_2693_;
goto v___jp_2683_;
}
else
{
lean_object* v___x_2694_; 
v___x_2694_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2684_ = v___x_2694_;
goto v___jp_2683_;
}
v___jp_2683_:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; uint8_t v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; 
v___x_2685_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__15));
v___x_2686_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2617_, v_d_2681_, v___x_2682_);
v___x_2687_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2687_, 0, v___x_2685_);
lean_ctor_set(v___x_2687_, 1, v___x_2686_);
lean_inc(v___y_2684_);
v___x_2688_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2688_, 0, v___y_2684_);
lean_ctor_set(v___x_2688_, 1, v___x_2687_);
v___x_2689_ = 0;
v___x_2690_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2690_, 0, v___x_2688_);
lean_ctor_set_uint8(v___x_2690_, sizeof(void*)*1, v___x_2689_);
v___x_2691_ = l_Repr_addAppParen(v___x_2690_, v_prec_2619_);
return v___x_2691_;
}
}
case 5:
{
lean_object* v_d_2695_; lean_object* v___x_2696_; lean_object* v___y_2698_; uint8_t v___x_2706_; 
v_d_2695_ = lean_ctor_get(v_x_2618_, 1);
lean_inc(v_d_2695_);
lean_dec_ref_known(v_x_2618_, 2);
v___x_2696_ = lean_unsigned_to_nat(1024u);
v___x_2706_ = lean_nat_dec_le(v___x_2696_, v_prec_2619_);
if (v___x_2706_ == 0)
{
lean_object* v___x_2707_; 
v___x_2707_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2698_ = v___x_2707_;
goto v___jp_2697_;
}
else
{
lean_object* v___x_2708_; 
v___x_2708_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2698_ = v___x_2708_;
goto v___jp_2697_;
}
v___jp_2697_:
{
lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; uint8_t v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v___x_2699_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__18));
v___x_2700_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2617_, v_d_2695_, v___x_2696_);
v___x_2701_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2699_);
lean_ctor_set(v___x_2701_, 1, v___x_2700_);
lean_inc(v___y_2698_);
v___x_2702_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2702_, 0, v___y_2698_);
lean_ctor_set(v___x_2702_, 1, v___x_2701_);
v___x_2703_ = 0;
v___x_2704_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2704_, 0, v___x_2702_);
lean_ctor_set_uint8(v___x_2704_, sizeof(void*)*1, v___x_2703_);
v___x_2705_ = l_Repr_addAppParen(v___x_2704_, v_prec_2619_);
return v___x_2705_;
}
}
case 6:
{
lean_object* v_n_2709_; uint8_t v_isCumulative_2710_; lean_object* v_d_2711_; lean_object* v___x_2712_; lean_object* v___y_2714_; uint8_t v___x_2730_; 
v_n_2709_ = lean_ctor_get(v_x_2618_, 1);
lean_inc(v_n_2709_);
v_isCumulative_2710_ = lean_ctor_get_uint8(v_x_2618_, sizeof(void*)*3 + 7);
v_d_2711_ = lean_ctor_get(v_x_2618_, 2);
lean_inc(v_d_2711_);
lean_dec_ref_known(v_x_2618_, 3);
v___x_2712_ = lean_unsigned_to_nat(1024u);
v___x_2730_ = lean_nat_dec_le(v___x_2712_, v_prec_2619_);
if (v___x_2730_ == 0)
{
lean_object* v___x_2731_; 
v___x_2731_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2714_ = v___x_2731_;
goto v___jp_2713_;
}
else
{
lean_object* v___x_2732_; 
v___x_2732_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2714_ = v___x_2732_;
goto v___jp_2713_;
}
v___jp_2713_:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; uint8_t v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___x_2715_ = lean_box(1);
v___x_2716_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__21));
v___x_2717_ = l_Nat_reprFast(v_n_2709_);
v___x_2718_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2718_, 0, v___x_2717_);
v___x_2719_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2719_, 0, v___x_2716_);
lean_ctor_set(v___x_2719_, 1, v___x_2718_);
v___x_2720_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2720_, 0, v___x_2719_);
lean_ctor_set(v___x_2720_, 1, v___x_2715_);
v___x_2721_ = l_Bool_repr___redArg(v_isCumulative_2710_);
v___x_2722_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2720_);
lean_ctor_set(v___x_2722_, 1, v___x_2721_);
v___x_2723_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2723_, 0, v___x_2722_);
lean_ctor_set(v___x_2723_, 1, v___x_2715_);
v___x_2724_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2617_, v_d_2711_, v___x_2712_);
v___x_2725_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2725_, 0, v___x_2723_);
lean_ctor_set(v___x_2725_, 1, v___x_2724_);
lean_inc(v___y_2714_);
v___x_2726_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2726_, 0, v___y_2714_);
lean_ctor_set(v___x_2726_, 1, v___x_2725_);
v___x_2727_ = 0;
v___x_2728_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2728_, 0, v___x_2726_);
lean_ctor_set_uint8(v___x_2728_, sizeof(void*)*1, v___x_2727_);
v___x_2729_ = l_Repr_addAppParen(v___x_2728_, v_prec_2619_);
return v___x_2729_;
}
}
case 7:
{
lean_object* v_d_2733_; lean_object* v___x_2734_; lean_object* v___y_2736_; uint8_t v___x_2744_; 
v_d_2733_ = lean_ctor_get(v_x_2618_, 1);
lean_inc(v_d_2733_);
lean_dec_ref_known(v_x_2618_, 2);
v___x_2734_ = lean_unsigned_to_nat(1024u);
v___x_2744_ = lean_nat_dec_le(v___x_2734_, v_prec_2619_);
if (v___x_2744_ == 0)
{
lean_object* v___x_2745_; 
v___x_2745_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2736_ = v___x_2745_;
goto v___jp_2735_;
}
else
{
lean_object* v___x_2746_; 
v___x_2746_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2736_ = v___x_2746_;
goto v___jp_2735_;
}
v___jp_2735_:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; uint8_t v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; 
v___x_2737_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__24));
v___x_2738_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2617_, v_d_2733_, v___x_2734_);
v___x_2739_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2739_, 0, v___x_2737_);
lean_ctor_set(v___x_2739_, 1, v___x_2738_);
lean_inc(v___y_2736_);
v___x_2740_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2740_, 0, v___y_2736_);
lean_ctor_set(v___x_2740_, 1, v___x_2739_);
v___x_2741_ = 0;
v___x_2742_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2742_, 0, v___x_2740_);
lean_ctor_set_uint8(v___x_2742_, sizeof(void*)*1, v___x_2741_);
v___x_2743_ = l_Repr_addAppParen(v___x_2742_, v_prec_2619_);
return v___x_2743_;
}
}
case 8:
{
uint8_t v_onlyNonCumulative_2747_; lean_object* v_d_2748_; lean_object* v___x_2749_; lean_object* v___y_2751_; uint8_t v___x_2763_; 
v_onlyNonCumulative_2747_ = lean_ctor_get_uint8(v_x_2618_, sizeof(void*)*2 + 7);
v_d_2748_ = lean_ctor_get(v_x_2618_, 1);
lean_inc(v_d_2748_);
lean_dec_ref_known(v_x_2618_, 2);
v___x_2749_ = lean_unsigned_to_nat(1024u);
v___x_2763_ = lean_nat_dec_le(v___x_2749_, v_prec_2619_);
if (v___x_2763_ == 0)
{
lean_object* v___x_2764_; 
v___x_2764_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2751_ = v___x_2764_;
goto v___jp_2750_;
}
else
{
lean_object* v___x_2765_; 
v___x_2765_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2751_ = v___x_2765_;
goto v___jp_2750_;
}
v___jp_2750_:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; uint8_t v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; 
v___x_2752_ = lean_box(1);
v___x_2753_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__27));
v___x_2754_ = l_Bool_repr___redArg(v_onlyNonCumulative_2747_);
v___x_2755_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2755_, 0, v___x_2753_);
lean_ctor_set(v___x_2755_, 1, v___x_2754_);
v___x_2756_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2756_, 0, v___x_2755_);
lean_ctor_set(v___x_2756_, 1, v___x_2752_);
v___x_2757_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2617_, v_d_2748_, v___x_2749_);
v___x_2758_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2756_);
lean_ctor_set(v___x_2758_, 1, v___x_2757_);
lean_inc(v___y_2751_);
v___x_2759_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2759_, 0, v___y_2751_);
lean_ctor_set(v___x_2759_, 1, v___x_2758_);
v___x_2760_ = 0;
v___x_2761_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2761_, 0, v___x_2759_);
lean_ctor_set_uint8(v___x_2761_, sizeof(void*)*1, v___x_2760_);
v___x_2762_ = l_Repr_addAppParen(v___x_2761_, v_prec_2619_);
return v___x_2762_;
}
}
case 9:
{
lean_object* v_d_2766_; lean_object* v___x_2767_; lean_object* v___y_2769_; uint8_t v___x_2777_; 
v_d_2766_ = lean_ctor_get(v_x_2618_, 1);
lean_inc(v_d_2766_);
lean_dec_ref_known(v_x_2618_, 2);
v___x_2767_ = lean_unsigned_to_nat(1024u);
v___x_2777_ = lean_nat_dec_le(v___x_2767_, v_prec_2619_);
if (v___x_2777_ == 0)
{
lean_object* v___x_2778_; 
v___x_2778_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2769_ = v___x_2778_;
goto v___jp_2768_;
}
else
{
lean_object* v___x_2779_; 
v___x_2779_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2769_ = v___x_2779_;
goto v___jp_2768_;
}
v___jp_2768_:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; uint8_t v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; 
v___x_2770_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__30));
v___x_2771_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2617_, v_d_2766_, v___x_2767_);
v___x_2772_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2772_, 0, v___x_2770_);
lean_ctor_set(v___x_2772_, 1, v___x_2771_);
lean_inc(v___y_2769_);
v___x_2773_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2773_, 0, v___y_2769_);
lean_ctor_set(v___x_2773_, 1, v___x_2772_);
v___x_2774_ = 0;
v___x_2775_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2775_, 0, v___x_2773_);
lean_ctor_set_uint8(v___x_2775_, sizeof(void*)*1, v___x_2774_);
v___x_2776_ = l_Repr_addAppParen(v___x_2775_, v_prec_2619_);
return v___x_2776_;
}
}
case 10:
{
lean_object* v_d_2780_; lean_object* v___x_2781_; lean_object* v___y_2783_; uint8_t v___x_2791_; 
v_d_2780_ = lean_ctor_get(v_x_2618_, 1);
lean_inc(v_d_2780_);
lean_dec_ref_known(v_x_2618_, 2);
v___x_2781_ = lean_unsigned_to_nat(1024u);
v___x_2791_ = lean_nat_dec_le(v___x_2781_, v_prec_2619_);
if (v___x_2791_ == 0)
{
lean_object* v___x_2792_; 
v___x_2792_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2783_ = v___x_2792_;
goto v___jp_2782_;
}
else
{
lean_object* v___x_2793_; 
v___x_2793_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2783_ = v___x_2793_;
goto v___jp_2782_;
}
v___jp_2782_:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; uint8_t v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; 
v___x_2784_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__33));
v___x_2785_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2617_, v_d_2780_, v___x_2781_);
v___x_2786_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2786_, 0, v___x_2784_);
lean_ctor_set(v___x_2786_, 1, v___x_2785_);
lean_inc(v___y_2783_);
v___x_2787_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2787_, 0, v___y_2783_);
lean_ctor_set(v___x_2787_, 1, v___x_2786_);
v___x_2788_ = 0;
v___x_2789_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2789_, 0, v___x_2787_);
lean_ctor_set_uint8(v___x_2789_, sizeof(void*)*1, v___x_2788_);
v___x_2790_ = l_Repr_addAppParen(v___x_2789_, v_prec_2619_);
return v___x_2790_;
}
}
case 11:
{
lean_object* v_d_2794_; lean_object* v___x_2795_; lean_object* v___y_2797_; uint8_t v___x_2805_; 
v_d_2794_ = lean_ctor_get(v_x_2618_, 1);
lean_inc(v_d_2794_);
lean_dec_ref_known(v_x_2618_, 2);
v___x_2795_ = lean_unsigned_to_nat(1024u);
v___x_2805_ = lean_nat_dec_le(v___x_2795_, v_prec_2619_);
if (v___x_2805_ == 0)
{
lean_object* v___x_2806_; 
v___x_2806_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2797_ = v___x_2806_;
goto v___jp_2796_;
}
else
{
lean_object* v___x_2807_; 
v___x_2807_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2797_ = v___x_2807_;
goto v___jp_2796_;
}
v___jp_2796_:
{
lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; uint8_t v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; 
v___x_2798_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__36));
v___x_2799_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2617_, v_d_2794_, v___x_2795_);
v___x_2800_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2798_);
lean_ctor_set(v___x_2800_, 1, v___x_2799_);
lean_inc(v___y_2797_);
v___x_2801_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2801_, 0, v___y_2797_);
lean_ctor_set(v___x_2801_, 1, v___x_2800_);
v___x_2802_ = 0;
v___x_2803_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2803_, 0, v___x_2801_);
lean_ctor_set_uint8(v___x_2803_, sizeof(void*)*1, v___x_2802_);
v___x_2804_ = l_Repr_addAppParen(v___x_2803_, v_prec_2619_);
return v___x_2804_;
}
}
case 12:
{
lean_object* v_d_2808_; lean_object* v___x_2809_; lean_object* v___y_2811_; uint8_t v___x_2819_; 
v_d_2808_ = lean_ctor_get(v_x_2618_, 2);
lean_inc(v_d_2808_);
lean_dec_ref_known(v_x_2618_, 3);
v___x_2809_ = lean_unsigned_to_nat(1024u);
v___x_2819_ = lean_nat_dec_le(v___x_2809_, v_prec_2619_);
if (v___x_2819_ == 0)
{
lean_object* v___x_2820_; 
v___x_2820_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2811_ = v___x_2820_;
goto v___jp_2810_;
}
else
{
lean_object* v___x_2821_; 
v___x_2821_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2811_ = v___x_2821_;
goto v___jp_2810_;
}
v___jp_2810_:
{
lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; uint8_t v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; 
v___x_2812_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__41));
v___x_2813_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2617_, v_d_2808_, v___x_2809_);
v___x_2814_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2812_);
lean_ctor_set(v___x_2814_, 1, v___x_2813_);
lean_inc(v___y_2811_);
v___x_2815_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2815_, 0, v___y_2811_);
lean_ctor_set(v___x_2815_, 1, v___x_2814_);
v___x_2816_ = 0;
v___x_2817_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2817_, 0, v___x_2815_);
lean_ctor_set_uint8(v___x_2817_, sizeof(void*)*1, v___x_2816_);
v___x_2818_ = l_Repr_addAppParen(v___x_2817_, v_prec_2619_);
return v___x_2818_;
}
}
case 13:
{
lean_object* v_cost_2822_; lean_object* v_d_2823_; lean_object* v___x_2824_; lean_object* v___y_2826_; uint8_t v___x_2838_; 
v_cost_2822_ = lean_ctor_get(v_x_2618_, 1);
lean_inc(v_cost_2822_);
v_d_2823_ = lean_ctor_get(v_x_2618_, 2);
lean_inc(v_d_2823_);
lean_dec_ref_known(v_x_2618_, 3);
v___x_2824_ = lean_unsigned_to_nat(1024u);
v___x_2838_ = lean_nat_dec_le(v___x_2824_, v_prec_2619_);
if (v___x_2838_ == 0)
{
lean_object* v___x_2839_; 
v___x_2839_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2826_ = v___x_2839_;
goto v___jp_2825_;
}
else
{
lean_object* v___x_2840_; 
v___x_2840_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2826_ = v___x_2840_;
goto v___jp_2825_;
}
v___jp_2825_:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; uint8_t v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2827_ = lean_box(1);
v___x_2828_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__44));
lean_inc_ref(v_inst_2617_);
v___x_2829_ = lean_apply_2(v_inst_2617_, v_cost_2822_, v___x_2824_);
v___x_2830_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2830_, 0, v___x_2828_);
lean_ctor_set(v___x_2830_, 1, v___x_2829_);
v___x_2831_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2831_, 0, v___x_2830_);
lean_ctor_set(v___x_2831_, 1, v___x_2827_);
v___x_2832_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2617_, v_d_2823_, v___x_2824_);
v___x_2833_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2831_);
lean_ctor_set(v___x_2833_, 1, v___x_2832_);
lean_inc(v___y_2826_);
v___x_2834_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2834_, 0, v___y_2826_);
lean_ctor_set(v___x_2834_, 1, v___x_2833_);
v___x_2835_ = 0;
v___x_2836_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2836_, 0, v___x_2834_);
lean_ctor_set_uint8(v___x_2836_, sizeof(void*)*1, v___x_2835_);
v___x_2837_ = l_Repr_addAppParen(v___x_2836_, v_prec_2619_);
return v___x_2837_;
}
}
case 14:
{
lean_object* v_a_2841_; lean_object* v_b_2842_; lean_object* v___x_2843_; lean_object* v___y_2845_; uint8_t v___x_2857_; 
v_a_2841_ = lean_ctor_get(v_x_2618_, 1);
lean_inc(v_a_2841_);
v_b_2842_ = lean_ctor_get(v_x_2618_, 2);
lean_inc(v_b_2842_);
lean_dec_ref_known(v_x_2618_, 3);
v___x_2843_ = lean_unsigned_to_nat(1024u);
v___x_2857_ = lean_nat_dec_le(v___x_2843_, v_prec_2619_);
if (v___x_2857_ == 0)
{
lean_object* v___x_2858_; 
v___x_2858_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2845_ = v___x_2858_;
goto v___jp_2844_;
}
else
{
lean_object* v___x_2859_; 
v___x_2859_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2845_ = v___x_2859_;
goto v___jp_2844_;
}
v___jp_2844_:
{
lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; uint8_t v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; 
v___x_2846_ = lean_box(1);
v___x_2847_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__47));
lean_inc_ref(v_inst_2617_);
v___x_2848_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2617_, v_a_2841_, v___x_2843_);
v___x_2849_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2847_);
lean_ctor_set(v___x_2849_, 1, v___x_2848_);
v___x_2850_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2850_, 0, v___x_2849_);
lean_ctor_set(v___x_2850_, 1, v___x_2846_);
v___x_2851_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2617_, v_b_2842_, v___x_2843_);
v___x_2852_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2852_, 0, v___x_2850_);
lean_ctor_set(v___x_2852_, 1, v___x_2851_);
lean_inc(v___y_2845_);
v___x_2853_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2853_, 0, v___y_2845_);
lean_ctor_set(v___x_2853_, 1, v___x_2852_);
v___x_2854_ = 0;
v___x_2855_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2855_, 0, v___x_2853_);
lean_ctor_set_uint8(v___x_2855_, sizeof(void*)*1, v___x_2854_);
v___x_2856_ = l_Repr_addAppParen(v___x_2855_, v_prec_2619_);
return v___x_2856_;
}
}
default: 
{
lean_object* v_a_2860_; lean_object* v_b_2861_; lean_object* v___x_2862_; lean_object* v___y_2864_; uint8_t v___x_2876_; 
v_a_2860_ = lean_ctor_get(v_x_2618_, 1);
lean_inc(v_a_2860_);
v_b_2861_ = lean_ctor_get(v_x_2618_, 2);
lean_inc(v_b_2861_);
lean_dec_ref_known(v_x_2618_, 3);
v___x_2862_ = lean_unsigned_to_nat(1024u);
v___x_2876_ = lean_nat_dec_le(v___x_2862_, v_prec_2619_);
if (v___x_2876_ == 0)
{
lean_object* v___x_2877_; 
v___x_2877_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2864_ = v___x_2877_;
goto v___jp_2863_;
}
else
{
lean_object* v___x_2878_; 
v___x_2878_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2864_ = v___x_2878_;
goto v___jp_2863_;
}
v___jp_2863_:
{
lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; uint8_t v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; 
v___x_2865_ = lean_box(1);
v___x_2866_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__50));
lean_inc_ref(v_inst_2617_);
v___x_2867_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2617_, v_a_2860_, v___x_2862_);
v___x_2868_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2868_, 0, v___x_2866_);
lean_ctor_set(v___x_2868_, 1, v___x_2867_);
v___x_2869_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2869_, 0, v___x_2868_);
lean_ctor_set(v___x_2869_, 1, v___x_2865_);
v___x_2870_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2617_, v_b_2861_, v___x_2862_);
v___x_2871_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2871_, 0, v___x_2869_);
lean_ctor_set(v___x_2871_, 1, v___x_2870_);
lean_inc(v___y_2864_);
v___x_2872_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2872_, 0, v___y_2864_);
lean_ctor_set(v___x_2872_, 1, v___x_2871_);
v___x_2873_ = 0;
v___x_2874_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2874_, 0, v___x_2872_);
lean_ctor_set_uint8(v___x_2874_, sizeof(void*)*1, v___x_2873_);
v___x_2875_ = l_Repr_addAppParen(v___x_2874_, v_prec_2619_);
return v___x_2875_;
}
}
}
v___jp_2620_:
{
lean_object* v___x_2622_; lean_object* v___x_2623_; uint8_t v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2622_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__1));
lean_inc(v___y_2621_);
v___x_2623_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2623_, 0, v___y_2621_);
lean_ctor_set(v___x_2623_, 1, v___x_2622_);
v___x_2624_ = 0;
v___x_2625_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2625_, 0, v___x_2623_);
lean_ctor_set_uint8(v___x_2625_, sizeof(void*)*1, v___x_2624_);
v___x_2626_ = l_Repr_addAppParen(v___x_2625_, v_prec_2619_);
return v___x_2626_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___boxed(lean_object* v_inst_2879_, lean_object* v_x_2880_, lean_object* v_prec_2881_){
_start:
{
lean_object* v_res_2882_; 
v_res_2882_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2879_, v_x_2880_, v_prec_2881_);
lean_dec(v_prec_2881_);
return v_res_2882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprDoc_repr(lean_object* v_00_u03c4_2883_, lean_object* v_inst_2884_, lean_object* v_x_2885_, lean_object* v_prec_2886_){
_start:
{
lean_object* v___x_2887_; 
v___x_2887_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2884_, v_x_2885_, v_prec_2886_);
return v___x_2887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprDoc_repr___boxed(lean_object* v_00_u03c4_2888_, lean_object* v_inst_2889_, lean_object* v_x_2890_, lean_object* v_prec_2891_){
_start:
{
lean_object* v_res_2892_; 
v_res_2892_ = l_Lean_Fmt_instReprDoc_repr(v_00_u03c4_2888_, v_inst_2889_, v_x_2890_, v_prec_2891_);
lean_dec(v_prec_2891_);
return v_res_2892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprDoc___redArg(lean_object* v_inst_2893_){
_start:
{
lean_object* v___x_2894_; 
v___x_2894_ = lean_alloc_closure((void*)(l_Lean_Fmt_instReprDoc_repr___boxed), 4, 2);
lean_closure_set(v___x_2894_, 0, lean_box(0));
lean_closure_set(v___x_2894_, 1, v_inst_2893_);
return v___x_2894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprDoc(lean_object* v_00_u03c4_2895_, lean_object* v_inst_2896_){
_start:
{
lean_object* v___x_2897_; 
v___x_2897_ = lean_alloc_closure((void*)(l_Lean_Fmt_instReprDoc_repr___boxed), 4, 2);
lean_closure_set(v___x_2897_, 0, lean_box(0));
lean_closure_set(v___x_2897_, 1, v_inst_2896_);
return v___x_2897_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isFailure___redArg(lean_object* v_d_2898_, uint8_t v_fullness_2899_){
_start:
{
uint16_t v___x_2900_; uint16_t v___x_2901_; uint16_t v___x_2902_; uint16_t v___x_2903_; uint16_t v___x_2904_; uint16_t v___x_2905_; uint8_t v___x_2906_; 
v___x_2900_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_d_2898_);
v___x_2901_ = lean_uint8_to_uint16(v_fullness_2899_);
v___x_2902_ = lean_uint16_shift_right(v___x_2900_, v___x_2901_);
v___x_2903_ = 1;
v___x_2904_ = lean_uint16_land(v___x_2902_, v___x_2903_);
v___x_2905_ = 0;
v___x_2906_ = lean_uint16_dec_eq(v___x_2904_, v___x_2905_);
if (v___x_2906_ == 0)
{
uint8_t v___x_2907_; 
v___x_2907_ = 1;
return v___x_2907_;
}
else
{
uint8_t v___x_2908_; 
v___x_2908_ = 0;
return v___x_2908_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isFailure___redArg___boxed(lean_object* v_d_2909_, lean_object* v_fullness_2910_){
_start:
{
uint8_t v_fullness_boxed_2911_; uint8_t v_res_2912_; lean_object* v_r_2913_; 
v_fullness_boxed_2911_ = lean_unbox(v_fullness_2910_);
v_res_2912_ = l_Lean_Fmt_Doc_isFailure___redArg(v_d_2909_, v_fullness_boxed_2911_);
lean_dec(v_d_2909_);
v_r_2913_ = lean_box(v_res_2912_);
return v_r_2913_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isFailure(lean_object* v_00_u03c4_2914_, lean_object* v_d_2915_, uint8_t v_fullness_2916_){
_start:
{
uint8_t v___x_2917_; 
v___x_2917_ = l_Lean_Fmt_Doc_isFailure___redArg(v_d_2915_, v_fullness_2916_);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isFailure___boxed(lean_object* v_00_u03c4_2918_, lean_object* v_d_2919_, lean_object* v_fullness_2920_){
_start:
{
uint8_t v_fullness_boxed_2921_; uint8_t v_res_2922_; lean_object* v_r_2923_; 
v_fullness_boxed_2921_ = lean_unbox(v_fullness_2920_);
v_res_2922_ = l_Lean_Fmt_Doc_isFailure(v_00_u03c4_2918_, v_d_2919_, v_fullness_boxed_2921_);
lean_dec(v_d_2919_);
v_r_2923_ = lean_box(v_res_2922_);
return v_r_2923_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_neverFails___redArg(lean_object* v_d_2924_, uint8_t v_fullness_2925_){
_start:
{
uint16_t v___x_2926_; uint16_t v___x_2927_; uint16_t v___x_2928_; uint16_t v___x_2929_; uint16_t v___x_2930_; uint16_t v___x_2931_; uint8_t v___x_2932_; 
v___x_2926_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_d_2924_);
v___x_2927_ = lean_uint8_to_uint16(v_fullness_2925_);
v___x_2928_ = lean_uint16_shift_right(v___x_2926_, v___x_2927_);
v___x_2929_ = 1;
v___x_2930_ = lean_uint16_land(v___x_2928_, v___x_2929_);
v___x_2931_ = 0;
v___x_2932_ = lean_uint16_dec_eq(v___x_2930_, v___x_2931_);
if (v___x_2932_ == 0)
{
uint8_t v___x_2933_; 
v___x_2933_ = 1;
return v___x_2933_;
}
else
{
uint8_t v___x_2934_; 
v___x_2934_ = 0;
return v___x_2934_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_neverFails___redArg___boxed(lean_object* v_d_2935_, lean_object* v_fullness_2936_){
_start:
{
uint8_t v_fullness_boxed_2937_; uint8_t v_res_2938_; lean_object* v_r_2939_; 
v_fullness_boxed_2937_ = lean_unbox(v_fullness_2936_);
v_res_2938_ = l_Lean_Fmt_Doc_neverFails___redArg(v_d_2935_, v_fullness_boxed_2937_);
lean_dec(v_d_2935_);
v_r_2939_ = lean_box(v_res_2938_);
return v_r_2939_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_neverFails(lean_object* v_00_u03c4_2940_, lean_object* v_d_2941_, uint8_t v_fullness_2942_){
_start:
{
uint8_t v___x_2943_; 
v___x_2943_ = l_Lean_Fmt_Doc_neverFails___redArg(v_d_2941_, v_fullness_2942_);
return v___x_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_neverFails___boxed(lean_object* v_00_u03c4_2944_, lean_object* v_d_2945_, lean_object* v_fullness_2946_){
_start:
{
uint8_t v_fullness_boxed_2947_; uint8_t v_res_2948_; lean_object* v_r_2949_; 
v_fullness_boxed_2947_ = lean_unbox(v_fullness_2946_);
v_res_2948_ = l_Lean_Fmt_Doc_neverFails(v_00_u03c4_2944_, v_d_2945_, v_fullness_boxed_2947_);
lean_dec(v_d_2945_);
v_r_2949_ = lean_box(v_res_2948_);
return v_r_2949_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_hasContextDependentFailure___redArg(lean_object* v_d_2950_, uint8_t v_fullness_2951_){
_start:
{
uint16_t v___x_2952_; uint16_t v___x_2953_; uint16_t v___x_2954_; uint16_t v___x_2955_; uint16_t v___x_2956_; uint16_t v___x_2957_; uint16_t v___x_2958_; uint16_t v___x_2959_; uint8_t v___x_2960_; 
v___x_2952_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_d_2950_);
v___x_2953_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_d_2950_);
v___x_2954_ = lean_uint16_lor(v___x_2952_, v___x_2953_);
v___x_2955_ = lean_uint8_to_uint16(v_fullness_2951_);
v___x_2956_ = lean_uint16_shift_right(v___x_2954_, v___x_2955_);
v___x_2957_ = 1;
v___x_2958_ = lean_uint16_land(v___x_2956_, v___x_2957_);
v___x_2959_ = 0;
v___x_2960_ = lean_uint16_dec_eq(v___x_2958_, v___x_2959_);
return v___x_2960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_hasContextDependentFailure___redArg___boxed(lean_object* v_d_2961_, lean_object* v_fullness_2962_){
_start:
{
uint8_t v_fullness_boxed_2963_; uint8_t v_res_2964_; lean_object* v_r_2965_; 
v_fullness_boxed_2963_ = lean_unbox(v_fullness_2962_);
v_res_2964_ = l_Lean_Fmt_Doc_hasContextDependentFailure___redArg(v_d_2961_, v_fullness_boxed_2963_);
lean_dec(v_d_2961_);
v_r_2965_ = lean_box(v_res_2964_);
return v_r_2965_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_hasContextDependentFailure(lean_object* v_00_u03c4_2966_, lean_object* v_d_2967_, uint8_t v_fullness_2968_){
_start:
{
uint8_t v___x_2969_; 
v___x_2969_ = l_Lean_Fmt_Doc_hasContextDependentFailure___redArg(v_d_2967_, v_fullness_2968_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_hasContextDependentFailure___boxed(lean_object* v_00_u03c4_2970_, lean_object* v_d_2971_, lean_object* v_fullness_2972_){
_start:
{
uint8_t v_fullness_boxed_2973_; uint8_t v_res_2974_; lean_object* v_r_2975_; 
v_fullness_boxed_2973_ = lean_unbox(v_fullness_2972_);
v_res_2974_ = l_Lean_Fmt_Doc_hasContextDependentFailure(v_00_u03c4_2970_, v_d_2971_, v_fullness_boxed_2973_);
lean_dec(v_d_2971_);
v_r_2975_ = lean_box(v_res_2974_);
return v_r_2975_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(lean_object* v_d_2976_){
_start:
{
uint8_t v___x_2977_; 
v___x_2977_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_2976_);
if (v___x_2977_ == 0)
{
uint8_t v___x_2978_; 
v___x_2978_ = 1;
return v___x_2978_;
}
else
{
uint8_t v___x_2979_; 
v___x_2979_ = 0;
return v___x_2979_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isAlwaysEmpty___redArg___boxed(lean_object* v_d_2980_){
_start:
{
uint8_t v_res_2981_; lean_object* v_r_2982_; 
v_res_2981_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_d_2980_);
lean_dec(v_d_2980_);
v_r_2982_ = lean_box(v_res_2981_);
return v_r_2982_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isAlwaysEmpty(lean_object* v_00_u03c4_2983_, lean_object* v_d_2984_){
_start:
{
uint8_t v___x_2985_; 
v___x_2985_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_d_2984_);
return v___x_2985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isAlwaysEmpty___boxed(lean_object* v_00_u03c4_2986_, lean_object* v_d_2987_){
_start:
{
uint8_t v_res_2988_; lean_object* v_r_2989_; 
v_res_2988_ = l_Lean_Fmt_Doc_isAlwaysEmpty(v_00_u03c4_2986_, v_d_2987_);
lean_dec(v_d_2987_);
v_r_2989_ = lean_box(v_res_2988_);
return v_r_2989_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isAlwaysNonEmpty___redArg(lean_object* v_d_2990_){
_start:
{
uint8_t v___x_2991_; 
v___x_2991_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_2990_);
if (v___x_2991_ == 0)
{
uint8_t v___x_2992_; 
v___x_2992_ = 1;
return v___x_2992_;
}
else
{
uint8_t v___x_2993_; 
v___x_2993_ = 0;
return v___x_2993_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isAlwaysNonEmpty___redArg___boxed(lean_object* v_d_2994_){
_start:
{
uint8_t v_res_2995_; lean_object* v_r_2996_; 
v_res_2995_ = l_Lean_Fmt_Doc_isAlwaysNonEmpty___redArg(v_d_2994_);
lean_dec(v_d_2994_);
v_r_2996_ = lean_box(v_res_2995_);
return v_r_2996_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isAlwaysNonEmpty(lean_object* v_00_u03c4_2997_, lean_object* v_d_2998_){
_start:
{
uint8_t v___x_2999_; 
v___x_2999_ = l_Lean_Fmt_Doc_isAlwaysNonEmpty___redArg(v_d_2998_);
return v___x_2999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isAlwaysNonEmpty___boxed(lean_object* v_00_u03c4_3000_, lean_object* v_d_3001_){
_start:
{
uint8_t v_res_3002_; lean_object* v_r_3003_; 
v_res_3002_ = l_Lean_Fmt_Doc_isAlwaysNonEmpty(v_00_u03c4_3000_, v_d_3001_);
lean_dec(v_d_3001_);
v_r_3003_ = lean_box(v_res_3002_);
return v_r_3003_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isCompoundAtomic___redArg(lean_object* v_d_3004_){
_start:
{
uint8_t v___x_3005_; 
v___x_3005_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_3004_);
if (v___x_3005_ == 2)
{
uint8_t v___x_3006_; 
v___x_3006_ = 1;
return v___x_3006_;
}
else
{
if (v___x_3005_ == 0)
{
uint8_t v___x_3007_; 
v___x_3007_ = 1;
return v___x_3007_;
}
else
{
uint8_t v___x_3008_; 
v___x_3008_ = 0;
return v___x_3008_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isCompoundAtomic___redArg___boxed(lean_object* v_d_3009_){
_start:
{
uint8_t v_res_3010_; lean_object* v_r_3011_; 
v_res_3010_ = l_Lean_Fmt_Doc_isCompoundAtomic___redArg(v_d_3009_);
lean_dec(v_d_3009_);
v_r_3011_ = lean_box(v_res_3010_);
return v_r_3011_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isCompoundAtomic(lean_object* v_00_u03c4_3012_, lean_object* v_d_3013_){
_start:
{
uint8_t v___x_3014_; 
v___x_3014_ = l_Lean_Fmt_Doc_isCompoundAtomic___redArg(v_d_3013_);
return v___x_3014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isCompoundAtomic___boxed(lean_object* v_00_u03c4_3015_, lean_object* v_d_3016_){
_start:
{
uint8_t v_res_3017_; lean_object* v_r_3018_; 
v_res_3017_ = l_Lean_Fmt_Doc_isCompoundAtomic(v_00_u03c4_3015_, v_d_3016_);
lean_dec(v_d_3016_);
v_r_3018_ = lean_box(v_res_3017_);
return v_r_3018_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isAtomic___redArg(lean_object* v_d_3019_){
_start:
{
uint8_t v___x_3020_; 
v___x_3020_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_3019_);
if (v___x_3020_ == 0)
{
uint8_t v___x_3021_; 
v___x_3021_ = 1;
return v___x_3021_;
}
else
{
uint8_t v___x_3022_; 
v___x_3022_ = 0;
return v___x_3022_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isAtomic___redArg___boxed(lean_object* v_d_3023_){
_start:
{
uint8_t v_res_3024_; lean_object* v_r_3025_; 
v_res_3024_ = l_Lean_Fmt_Doc_isAtomic___redArg(v_d_3023_);
lean_dec(v_d_3023_);
v_r_3025_ = lean_box(v_res_3024_);
return v_r_3025_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isAtomic(lean_object* v_00_u03c4_3026_, lean_object* v_d_3027_){
_start:
{
uint8_t v___x_3028_; 
v___x_3028_ = l_Lean_Fmt_Doc_isAtomic___redArg(v_d_3027_);
return v___x_3028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isAtomic___boxed(lean_object* v_00_u03c4_3029_, lean_object* v_d_3030_){
_start:
{
uint8_t v_res_3031_; lean_object* v_r_3032_; 
v_res_3031_ = l_Lean_Fmt_Doc_isAtomic(v_00_u03c4_3029_, v_d_3030_);
lean_dec(v_d_3030_);
v_r_3032_ = lean_box(v_res_3031_);
return v_r_3032_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_empty___redArg___closed__1(void){
_start:
{
lean_object* v___x_3034_; lean_object* v___x_3035_; 
v___x_3034_ = ((lean_object*)(l_Lean_Fmt_Doc_empty___redArg___closed__0));
v___x_3035_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_3034_);
return v___x_3035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_empty___redArg(){
_start:
{
lean_object* v___x_3037_; 
v___x_3037_ = lean_obj_once(&l_Lean_Fmt_Doc_empty___redArg___closed__1, &l_Lean_Fmt_Doc_empty___redArg___closed__1_once, _init_l_Lean_Fmt_Doc_empty___redArg___closed__1);
return v___x_3037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_empty___redArg___boxed(lean_object* v___dummy_3038_){
_start:
{
lean_object* v_res_3039_; 
v_res_3039_ = l_Lean_Fmt_Doc_empty___redArg();
return v_res_3039_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_empty___closed__0(void){
_start:
{
lean_object* v___x_3040_; 
v___x_3040_ = l_Lean_Fmt_Doc_empty___redArg();
return v___x_3040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_empty(lean_object* v_00_u03c4_3041_){
_start:
{
lean_object* v___x_3042_; 
v___x_3042_ = lean_obj_once(&l_Lean_Fmt_Doc_empty___closed__0, &l_Lean_Fmt_Doc_empty___closed__0_once, _init_l_Lean_Fmt_Doc_empty___closed__0);
return v___x_3042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maybeFlattened___redArg(lean_object* v_d_3043_){
_start:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; 
lean_inc(v_d_3043_);
v___x_3044_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_d_3043_);
v___x_3045_ = l_Lean_Fmt_Doc_either___override___redArg(v_d_3043_, v___x_3044_);
return v___x_3045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maybeFlattened(lean_object* v_00_u03c4_3046_, lean_object* v_d_3047_){
_start:
{
lean_object* v___x_3048_; 
v___x_3048_ = l_Lean_Fmt_Doc_maybeFlattened___redArg(v_d_3047_);
return v___x_3048_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_nl___redArg___closed__1(void){
_start:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3050_ = ((lean_object*)(l_Lean_Fmt_Doc_nl___redArg___closed__0));
v___x_3051_ = l_Lean_Fmt_Doc_newline___override___redArg(v___x_3050_);
return v___x_3051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_nl___redArg(){
_start:
{
lean_object* v___x_3053_; 
v___x_3053_ = lean_obj_once(&l_Lean_Fmt_Doc_nl___redArg___closed__1, &l_Lean_Fmt_Doc_nl___redArg___closed__1_once, _init_l_Lean_Fmt_Doc_nl___redArg___closed__1);
return v___x_3053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_nl___redArg___boxed(lean_object* v___dummy_3054_){
_start:
{
lean_object* v_res_3055_; 
v_res_3055_ = l_Lean_Fmt_Doc_nl___redArg();
return v_res_3055_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_nl___closed__0(void){
_start:
{
lean_object* v___x_3056_; 
v___x_3056_ = l_Lean_Fmt_Doc_nl___redArg();
return v___x_3056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_nl(lean_object* v_00_u03c4_3057_){
_start:
{
lean_object* v___x_3058_; 
v___x_3058_ = lean_obj_once(&l_Lean_Fmt_Doc_nl___closed__0, &l_Lean_Fmt_Doc_nl___closed__0_once, _init_l_Lean_Fmt_Doc_nl___closed__0);
return v___x_3058_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_break___redArg___closed__0(void){
_start:
{
lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3059_ = ((lean_object*)(l_Lean_Fmt_Doc_empty___redArg___closed__0));
v___x_3060_ = l_Lean_Fmt_Doc_newline___override___redArg(v___x_3059_);
return v___x_3060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_break___redArg(){
_start:
{
lean_object* v___x_3062_; 
v___x_3062_ = lean_obj_once(&l_Lean_Fmt_Doc_break___redArg___closed__0, &l_Lean_Fmt_Doc_break___redArg___closed__0_once, _init_l_Lean_Fmt_Doc_break___redArg___closed__0);
return v___x_3062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_break___redArg___boxed(lean_object* v___dummy_3063_){
_start:
{
lean_object* v_res_3064_; 
v_res_3064_ = l_Lean_Fmt_Doc_break___redArg();
return v_res_3064_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_break___closed__0(void){
_start:
{
lean_object* v___x_3065_; 
v___x_3065_ = l_Lean_Fmt_Doc_break___redArg();
return v___x_3065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_break(lean_object* v_00_u03c4_3066_){
_start:
{
lean_object* v___x_3067_; 
v___x_3067_ = lean_obj_once(&l_Lean_Fmt_Doc_break___closed__0, &l_Lean_Fmt_Doc_break___closed__0_once, _init_l_Lean_Fmt_Doc_break___closed__0);
return v___x_3067_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_hardNl___redArg___closed__0(void){
_start:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; 
v___x_3068_ = lean_obj_once(&l_Lean_Fmt_Doc_nl___closed__0, &l_Lean_Fmt_Doc_nl___closed__0_once, _init_l_Lean_Fmt_Doc_nl___closed__0);
v___x_3069_ = l_Lean_Fmt_Doc_unflattenable___override___redArg(v___x_3068_);
return v___x_3069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_hardNl___redArg(){
_start:
{
lean_object* v___x_3071_; 
v___x_3071_ = lean_obj_once(&l_Lean_Fmt_Doc_hardNl___redArg___closed__0, &l_Lean_Fmt_Doc_hardNl___redArg___closed__0_once, _init_l_Lean_Fmt_Doc_hardNl___redArg___closed__0);
return v___x_3071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_hardNl___redArg___boxed(lean_object* v___dummy_3072_){
_start:
{
lean_object* v_res_3073_; 
v_res_3073_ = l_Lean_Fmt_Doc_hardNl___redArg();
return v_res_3073_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_hardNl___closed__0(void){
_start:
{
lean_object* v___x_3074_; 
v___x_3074_ = l_Lean_Fmt_Doc_hardNl___redArg();
return v___x_3074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_hardNl(lean_object* v_00_u03c4_3075_){
_start:
{
lean_object* v___x_3076_; 
v___x_3076_ = lean_obj_once(&l_Lean_Fmt_Doc_hardNl___closed__0, &l_Lean_Fmt_Doc_hardNl___closed__0_once, _init_l_Lean_Fmt_Doc_hardNl___closed__0);
return v___x_3076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_nested___redArg(lean_object* v_d_3077_){
_start:
{
lean_object* v___x_3078_; uint8_t v___x_3079_; lean_object* v___x_3080_; 
v___x_3078_ = lean_unsigned_to_nat(2u);
v___x_3079_ = 0;
v___x_3080_ = l_Lean_Fmt_Doc_indented___override___redArg(v___x_3078_, v___x_3079_, v_d_3077_);
return v___x_3080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_nested(lean_object* v_00_u03c4_3081_, lean_object* v_d_3082_){
_start:
{
lean_object* v___x_3083_; 
v___x_3083_ = l_Lean_Fmt_Doc_nested___redArg(v_d_3082_);
return v___x_3083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_hardNested___redArg(lean_object* v_d_3084_){
_start:
{
lean_object* v___x_3085_; uint8_t v___x_3086_; lean_object* v___x_3087_; 
v___x_3085_ = lean_unsigned_to_nat(2u);
v___x_3086_ = 1;
v___x_3087_ = l_Lean_Fmt_Doc_indented___override___redArg(v___x_3085_, v___x_3086_, v_d_3084_);
return v___x_3087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_hardNested(lean_object* v_00_u03c4_3088_, lean_object* v_d_3089_){
_start:
{
lean_object* v___x_3090_; 
v___x_3090_ = l_Lean_Fmt_Doc_hardNested___redArg(v_d_3089_);
return v___x_3090_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_oneOf_spec__0___redArg(lean_object* v_a_3091_, lean_object* v_b_3092_){
_start:
{
lean_object* v_array_3093_; lean_object* v_start_3094_; lean_object* v_stop_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3108_; 
v_array_3093_ = lean_ctor_get(v_a_3091_, 0);
v_start_3094_ = lean_ctor_get(v_a_3091_, 1);
v_stop_3095_ = lean_ctor_get(v_a_3091_, 2);
v_isSharedCheck_3108_ = !lean_is_exclusive(v_a_3091_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3097_ = v_a_3091_;
v_isShared_3098_ = v_isSharedCheck_3108_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_stop_3095_);
lean_inc(v_start_3094_);
lean_inc(v_array_3093_);
lean_dec(v_a_3091_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3108_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
uint8_t v___x_3099_; 
v___x_3099_ = lean_nat_dec_lt(v_start_3094_, v_stop_3095_);
if (v___x_3099_ == 0)
{
lean_del_object(v___x_3097_);
lean_dec(v_stop_3095_);
lean_dec(v_start_3094_);
lean_dec_ref(v_array_3093_);
return v_b_3092_;
}
else
{
lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3103_; 
v___x_3100_ = lean_unsigned_to_nat(1u);
v___x_3101_ = lean_nat_add(v_start_3094_, v___x_3100_);
lean_inc_ref(v_array_3093_);
if (v_isShared_3098_ == 0)
{
lean_ctor_set(v___x_3097_, 1, v___x_3101_);
v___x_3103_ = v___x_3097_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v_array_3093_);
lean_ctor_set(v_reuseFailAlloc_3107_, 1, v___x_3101_);
lean_ctor_set(v_reuseFailAlloc_3107_, 2, v_stop_3095_);
v___x_3103_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3104_ = lean_array_fget(v_array_3093_, v_start_3094_);
lean_dec(v_start_3094_);
lean_dec_ref(v_array_3093_);
v___x_3105_ = l_Lean_Fmt_Doc_either___override___redArg(v_b_3092_, v___x_3104_);
v_a_3091_ = v___x_3103_;
v_b_3092_ = v___x_3105_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_oneOf___redArg(lean_object* v_ds_3109_){
_start:
{
lean_object* v___x_3110_; lean_object* v___x_3111_; uint8_t v___x_3112_; 
v___x_3110_ = lean_unsigned_to_nat(0u);
v___x_3111_ = lean_array_get_size(v_ds_3109_);
v___x_3112_ = lean_nat_dec_lt(v___x_3110_, v___x_3111_);
if (v___x_3112_ == 0)
{
lean_object* v___x_3113_; 
lean_dec_ref(v_ds_3109_);
v___x_3113_ = lean_box(0);
return v___x_3113_;
}
else
{
lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; 
v___x_3114_ = lean_array_fget(v_ds_3109_, v___x_3110_);
v___x_3115_ = lean_unsigned_to_nat(1u);
v___x_3116_ = l_Array_toSubarray___redArg(v_ds_3109_, v___x_3115_, v___x_3111_);
v___x_3117_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_oneOf_spec__0___redArg(v___x_3116_, v___x_3114_);
return v___x_3117_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_oneOf(lean_object* v_00_u03c4_3118_, lean_object* v_ds_3119_){
_start:
{
lean_object* v___x_3120_; 
v___x_3120_ = l_Lean_Fmt_Doc_oneOf___redArg(v_ds_3119_);
return v___x_3120_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_oneOf_spec__0(lean_object* v_00_u03c4_3121_, lean_object* v_inst_3122_, lean_object* v_R_3123_, lean_object* v_a_3124_, lean_object* v_b_3125_, lean_object* v_c_3126_){
_start:
{
lean_object* v___x_3127_; 
v___x_3127_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_oneOf_spec__0___redArg(v_a_3124_, v_b_3125_);
return v___x_3127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instAppendDoc___redArg___lam__0(lean_object* v_d1_3128_, lean_object* v_d2_3129_){
_start:
{
uint8_t v___x_3130_; 
v___x_3130_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_d1_3128_);
if (v___x_3130_ == 0)
{
uint8_t v___x_3131_; 
v___x_3131_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_d2_3129_);
if (v___x_3131_ == 0)
{
lean_object* v___x_3132_; 
v___x_3132_ = l_Lean_Fmt_Doc_append___override___redArg(v_d1_3128_, v_d2_3129_);
return v___x_3132_;
}
else
{
lean_dec(v_d2_3129_);
return v_d1_3128_;
}
}
else
{
lean_dec(v_d1_3128_);
return v_d2_3129_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instAppendDoc___redArg(){
_start:
{
lean_object* v___f_3135_; 
v___f_3135_ = ((lean_object*)(l_Lean_Fmt_instAppendDoc___redArg___closed__0));
return v___f_3135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instAppendDoc___redArg___boxed(lean_object* v___dummy_3136_){
_start:
{
lean_object* v_res_3137_; 
v_res_3137_ = l_Lean_Fmt_instAppendDoc___redArg();
return v_res_3137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instAppendDoc(lean_object* v_00_u03c4_3138_){
_start:
{
lean_object* v___f_3139_; 
v___f_3139_ = ((lean_object*)(l_Lean_Fmt_instAppendDoc___redArg___closed__0));
return v___f_3139_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_join_spec__0___redArg(lean_object* v_a_3140_, lean_object* v_b_3141_){
_start:
{
lean_object* v_array_3142_; lean_object* v_start_3143_; lean_object* v_stop_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3161_; 
v_array_3142_ = lean_ctor_get(v_a_3140_, 0);
v_start_3143_ = lean_ctor_get(v_a_3140_, 1);
v_stop_3144_ = lean_ctor_get(v_a_3140_, 2);
v_isSharedCheck_3161_ = !lean_is_exclusive(v_a_3140_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3146_ = v_a_3140_;
v_isShared_3147_ = v_isSharedCheck_3161_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_stop_3144_);
lean_inc(v_start_3143_);
lean_inc(v_array_3142_);
lean_dec(v_a_3140_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3161_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
uint8_t v___x_3148_; 
v___x_3148_ = lean_nat_dec_lt(v_start_3143_, v_stop_3144_);
if (v___x_3148_ == 0)
{
lean_del_object(v___x_3146_);
lean_dec(v_stop_3144_);
lean_dec(v_start_3143_);
lean_dec_ref(v_array_3142_);
return v_b_3141_;
}
else
{
lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3152_; 
v___x_3149_ = lean_unsigned_to_nat(1u);
v___x_3150_ = lean_nat_add(v_start_3143_, v___x_3149_);
lean_inc_ref(v_array_3142_);
if (v_isShared_3147_ == 0)
{
lean_ctor_set(v___x_3146_, 1, v___x_3150_);
v___x_3152_ = v___x_3146_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_array_3142_);
lean_ctor_set(v_reuseFailAlloc_3160_, 1, v___x_3150_);
lean_ctor_set(v_reuseFailAlloc_3160_, 2, v_stop_3144_);
v___x_3152_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
lean_object* v___x_3153_; uint8_t v___x_3154_; 
v___x_3153_ = lean_array_fget(v_array_3142_, v_start_3143_);
lean_dec(v_start_3143_);
lean_dec_ref(v_array_3142_);
v___x_3154_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_b_3141_);
if (v___x_3154_ == 0)
{
uint8_t v___x_3155_; 
v___x_3155_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v___x_3153_);
if (v___x_3155_ == 0)
{
lean_object* v___x_3156_; 
v___x_3156_ = l_Lean_Fmt_Doc_append___override___redArg(v_b_3141_, v___x_3153_);
v_a_3140_ = v___x_3152_;
v_b_3141_ = v___x_3156_;
goto _start;
}
else
{
lean_dec(v___x_3153_);
v_a_3140_ = v___x_3152_;
goto _start;
}
}
else
{
lean_dec(v_b_3141_);
v_a_3140_ = v___x_3152_;
v_b_3141_ = v___x_3153_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_join___redArg(lean_object* v_ds_3162_){
_start:
{
lean_object* v___x_3163_; lean_object* v___x_3164_; uint8_t v___x_3165_; 
v___x_3163_ = lean_unsigned_to_nat(0u);
v___x_3164_ = lean_array_get_size(v_ds_3162_);
v___x_3165_ = lean_nat_dec_lt(v___x_3163_, v___x_3164_);
if (v___x_3165_ == 0)
{
lean_object* v___x_3166_; 
lean_dec_ref(v_ds_3162_);
v___x_3166_ = lean_obj_once(&l_Lean_Fmt_Doc_empty___redArg___closed__1, &l_Lean_Fmt_Doc_empty___redArg___closed__1_once, _init_l_Lean_Fmt_Doc_empty___redArg___closed__1);
return v___x_3166_;
}
else
{
lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; 
v___x_3167_ = lean_array_fget(v_ds_3162_, v___x_3163_);
v___x_3168_ = lean_unsigned_to_nat(1u);
v___x_3169_ = l_Array_toSubarray___redArg(v_ds_3162_, v___x_3168_, v___x_3164_);
v___x_3170_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_join_spec__0___redArg(v___x_3169_, v___x_3167_);
return v___x_3170_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_join(lean_object* v_00_u03c4_3171_, lean_object* v_ds_3172_){
_start:
{
lean_object* v___x_3173_; 
v___x_3173_ = l_Lean_Fmt_Doc_join___redArg(v_ds_3172_);
return v___x_3173_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_join_spec__0(lean_object* v_00_u03c4_3174_, lean_object* v_inst_3175_, lean_object* v_R_3176_, lean_object* v_a_3177_, lean_object* v_b_3178_, lean_object* v_c_3179_){
_start:
{
lean_object* v___x_3180_; 
v___x_3180_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_join_spec__0___redArg(v_a_3177_, v_b_3178_);
return v___x_3180_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_joinUsing_spec__0___redArg(lean_object* v_sep_3181_, lean_object* v_a_3182_, lean_object* v_b_3183_){
_start:
{
lean_object* v_array_3184_; lean_object* v_start_3185_; lean_object* v_stop_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3208_; 
v_array_3184_ = lean_ctor_get(v_a_3182_, 0);
v_start_3185_ = lean_ctor_get(v_a_3182_, 1);
v_stop_3186_ = lean_ctor_get(v_a_3182_, 2);
v_isSharedCheck_3208_ = !lean_is_exclusive(v_a_3182_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3188_ = v_a_3182_;
v_isShared_3189_ = v_isSharedCheck_3208_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_stop_3186_);
lean_inc(v_start_3185_);
lean_inc(v_array_3184_);
lean_dec(v_a_3182_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3208_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
uint8_t v___x_3190_; 
v___x_3190_ = lean_nat_dec_lt(v_start_3185_, v_stop_3186_);
if (v___x_3190_ == 0)
{
lean_del_object(v___x_3188_);
lean_dec(v_stop_3186_);
lean_dec(v_start_3185_);
lean_dec_ref(v_array_3184_);
lean_dec(v_sep_3181_);
return v_b_3183_;
}
else
{
lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3194_; 
v___x_3191_ = lean_unsigned_to_nat(1u);
v___x_3192_ = lean_nat_add(v_start_3185_, v___x_3191_);
lean_inc_ref(v_array_3184_);
if (v_isShared_3189_ == 0)
{
lean_ctor_set(v___x_3188_, 1, v___x_3192_);
v___x_3194_ = v___x_3188_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_array_3184_);
lean_ctor_set(v_reuseFailAlloc_3207_, 1, v___x_3192_);
lean_ctor_set(v_reuseFailAlloc_3207_, 2, v_stop_3186_);
v___x_3194_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
lean_object* v___x_3195_; lean_object* v___y_3197_; uint8_t v___x_3204_; 
v___x_3195_ = lean_array_fget(v_array_3184_, v_start_3185_);
lean_dec(v_start_3185_);
lean_dec_ref(v_array_3184_);
v___x_3204_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_b_3183_);
if (v___x_3204_ == 0)
{
uint8_t v___x_3205_; 
v___x_3205_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_sep_3181_);
if (v___x_3205_ == 0)
{
lean_object* v___x_3206_; 
lean_inc(v_sep_3181_);
v___x_3206_ = l_Lean_Fmt_Doc_append___override___redArg(v_b_3183_, v_sep_3181_);
v___y_3197_ = v___x_3206_;
goto v___jp_3196_;
}
else
{
v___y_3197_ = v_b_3183_;
goto v___jp_3196_;
}
}
else
{
lean_dec(v_b_3183_);
lean_inc(v_sep_3181_);
v___y_3197_ = v_sep_3181_;
goto v___jp_3196_;
}
v___jp_3196_:
{
uint8_t v___x_3198_; 
v___x_3198_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v___y_3197_);
if (v___x_3198_ == 0)
{
uint8_t v___x_3199_; 
v___x_3199_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v___x_3195_);
if (v___x_3199_ == 0)
{
lean_object* v___x_3200_; 
v___x_3200_ = l_Lean_Fmt_Doc_append___override___redArg(v___y_3197_, v___x_3195_);
v_a_3182_ = v___x_3194_;
v_b_3183_ = v___x_3200_;
goto _start;
}
else
{
lean_dec(v___x_3195_);
v_a_3182_ = v___x_3194_;
v_b_3183_ = v___y_3197_;
goto _start;
}
}
else
{
lean_dec(v___y_3197_);
v_a_3182_ = v___x_3194_;
v_b_3183_ = v___x_3195_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_joinUsing___redArg(lean_object* v_sep_3209_, lean_object* v_ds_3210_){
_start:
{
lean_object* v___x_3211_; lean_object* v___x_3212_; uint8_t v___x_3213_; 
v___x_3211_ = lean_unsigned_to_nat(0u);
v___x_3212_ = lean_array_get_size(v_ds_3210_);
v___x_3213_ = lean_nat_dec_lt(v___x_3211_, v___x_3212_);
if (v___x_3213_ == 0)
{
lean_object* v___x_3214_; 
lean_dec_ref(v_ds_3210_);
lean_dec(v_sep_3209_);
v___x_3214_ = lean_obj_once(&l_Lean_Fmt_Doc_empty___redArg___closed__1, &l_Lean_Fmt_Doc_empty___redArg___closed__1_once, _init_l_Lean_Fmt_Doc_empty___redArg___closed__1);
return v___x_3214_;
}
else
{
lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; 
v___x_3215_ = lean_array_fget(v_ds_3210_, v___x_3211_);
v___x_3216_ = lean_unsigned_to_nat(1u);
v___x_3217_ = l_Array_toSubarray___redArg(v_ds_3210_, v___x_3216_, v___x_3212_);
v___x_3218_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_joinUsing_spec__0___redArg(v_sep_3209_, v___x_3217_, v___x_3215_);
return v___x_3218_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_joinUsing(lean_object* v_00_u03c4_3219_, lean_object* v_sep_3220_, lean_object* v_ds_3221_){
_start:
{
lean_object* v___x_3222_; 
v___x_3222_ = l_Lean_Fmt_Doc_joinUsing___redArg(v_sep_3220_, v_ds_3221_);
return v___x_3222_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_joinUsing_spec__0(lean_object* v_00_u03c4_3223_, lean_object* v_sep_3224_, lean_object* v_inst_3225_, lean_object* v_R_3226_, lean_object* v_a_3227_, lean_object* v_b_3228_, lean_object* v_c_3229_){
_start:
{
lean_object* v___x_3230_; 
v___x_3230_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_joinUsing_spec__0___redArg(v_sep_3224_, v_a_3227_, v_b_3228_);
return v___x_3230_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillWith_spec__0___redArg(lean_object* v_upperBound_3231_, lean_object* v_sep_3232_, lean_object* v_ds_3233_, lean_object* v_a_3234_, lean_object* v_b_3235_){
_start:
{
uint8_t v___x_3236_; 
v___x_3236_ = lean_nat_dec_lt(v_a_3234_, v_upperBound_3231_);
if (v___x_3236_ == 0)
{
lean_dec(v_a_3234_);
lean_dec_ref(v_sep_3232_);
return v_b_3235_;
}
else
{
lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v_flat_3240_; lean_object* v_broken_3241_; lean_object* v_fst_3242_; lean_object* v_snd_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3278_; 
v___x_3237_ = lean_unsigned_to_nat(1u);
v___x_3238_ = lean_nat_sub(v_a_3234_, v___x_3237_);
lean_inc_ref(v_sep_3232_);
v___x_3239_ = lean_apply_1(v_sep_3232_, v___x_3238_);
v_flat_3240_ = lean_ctor_get(v___x_3239_, 0);
lean_inc(v_flat_3240_);
v_broken_3241_ = lean_ctor_get(v___x_3239_, 1);
lean_inc(v_broken_3241_);
lean_dec_ref(v___x_3239_);
v_fst_3242_ = lean_ctor_get(v_b_3235_, 0);
v_snd_3243_ = lean_ctor_get(v_b_3235_, 1);
v_isSharedCheck_3278_ = !lean_is_exclusive(v_b_3235_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3245_ = v_b_3235_;
v_isShared_3246_ = v_isSharedCheck_3278_;
goto v_resetjp_3244_;
}
else
{
lean_inc(v_snd_3243_);
lean_inc(v_fst_3242_);
lean_dec(v_b_3235_);
v___x_3245_ = lean_box(0);
v_isShared_3246_ = v_isSharedCheck_3278_;
goto v_resetjp_3244_;
}
v_resetjp_3244_:
{
lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3274_; 
v___x_3247_ = lean_array_fget_borrowed(v_ds_3233_, v_a_3234_);
v___x_3248_ = lean_unsigned_to_nat(2u);
v___x_3249_ = lean_mk_empty_array_with_capacity(v___x_3248_);
lean_inc(v_fst_3242_);
lean_inc_ref(v___x_3249_);
v___x_3250_ = lean_array_push(v___x_3249_, v_fst_3242_);
v___x_3251_ = lean_array_push(v___x_3250_, v_snd_3243_);
v___x_3252_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_3251_);
lean_inc_n(v___x_3247_, 2);
v___x_3253_ = l_Lean_Fmt_Doc_flattened___override___redArg(v___x_3247_);
v___x_3254_ = lean_unsigned_to_nat(3u);
v___x_3255_ = lean_mk_empty_array_with_capacity(v___x_3254_);
v___x_3256_ = lean_array_push(v___x_3255_, v_fst_3242_);
v___x_3257_ = lean_array_push(v___x_3256_, v_flat_3240_);
lean_inc(v___x_3253_);
v___x_3258_ = lean_array_push(v___x_3257_, v___x_3253_);
v___x_3259_ = l_Lean_Fmt_Doc_join___redArg(v___x_3258_);
v___x_3260_ = lean_obj_once(&l_Lean_Fmt_Doc_hardNl___closed__0, &l_Lean_Fmt_Doc_hardNl___closed__0_once, _init_l_Lean_Fmt_Doc_hardNl___closed__0);
v___x_3261_ = lean_unsigned_to_nat(4u);
v___x_3262_ = lean_mk_empty_array_with_capacity(v___x_3261_);
v___x_3263_ = lean_array_push(v___x_3262_, v___x_3252_);
v___x_3264_ = lean_array_push(v___x_3263_, v_broken_3241_);
v___x_3265_ = lean_array_push(v___x_3264_, v___x_3260_);
lean_inc_ref(v___x_3265_);
v___x_3266_ = lean_array_push(v___x_3265_, v___x_3253_);
v___x_3267_ = l_Lean_Fmt_Doc_join___redArg(v___x_3266_);
v___x_3268_ = lean_array_push(v___x_3249_, v___x_3259_);
v___x_3269_ = lean_array_push(v___x_3268_, v___x_3267_);
v___x_3270_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_3269_);
v___x_3271_ = lean_array_push(v___x_3265_, v___x_3247_);
v___x_3272_ = l_Lean_Fmt_Doc_join___redArg(v___x_3271_);
if (v_isShared_3246_ == 0)
{
lean_ctor_set(v___x_3245_, 1, v___x_3272_);
lean_ctor_set(v___x_3245_, 0, v___x_3270_);
v___x_3274_ = v___x_3245_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v___x_3270_);
lean_ctor_set(v_reuseFailAlloc_3277_, 1, v___x_3272_);
v___x_3274_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
lean_object* v___x_3275_; 
v___x_3275_ = lean_nat_add(v_a_3234_, v___x_3237_);
lean_dec(v_a_3234_);
v_a_3234_ = v___x_3275_;
v_b_3235_ = v___x_3274_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillWith_spec__0___redArg___boxed(lean_object* v_upperBound_3279_, lean_object* v_sep_3280_, lean_object* v_ds_3281_, lean_object* v_a_3282_, lean_object* v_b_3283_){
_start:
{
lean_object* v_res_3284_; 
v_res_3284_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillWith_spec__0___redArg(v_upperBound_3279_, v_sep_3280_, v_ds_3281_, v_a_3282_, v_b_3283_);
lean_dec_ref(v_ds_3281_);
lean_dec(v_upperBound_3279_);
return v_res_3284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillWith___redArg(lean_object* v_ds_3285_, lean_object* v_sep_3286_){
_start:
{
lean_object* v___x_3287_; lean_object* v___x_3288_; uint8_t v___x_3289_; 
v___x_3287_ = lean_array_get_size(v_ds_3285_);
v___x_3288_ = lean_unsigned_to_nat(0u);
v___x_3289_ = lean_nat_dec_eq(v___x_3287_, v___x_3288_);
if (v___x_3289_ == 0)
{
lean_object* v___x_3290_; lean_object* v_lastNotFlattened_3291_; lean_object* v___x_3292_; uint8_t v___x_3293_; 
v___x_3290_ = lean_box(0);
v_lastNotFlattened_3291_ = lean_array_get_borrowed(v___x_3290_, v_ds_3285_, v___x_3288_);
v___x_3292_ = lean_unsigned_to_nat(1u);
v___x_3293_ = lean_nat_dec_eq(v___x_3287_, v___x_3292_);
if (v___x_3293_ == 0)
{
lean_object* v_lastFlattened_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v_fst_3297_; lean_object* v_snd_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; 
lean_inc_n(v_lastNotFlattened_3291_, 2);
v_lastFlattened_3294_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_lastNotFlattened_3291_);
v___x_3295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3295_, 0, v_lastFlattened_3294_);
lean_ctor_set(v___x_3295_, 1, v_lastNotFlattened_3291_);
v___x_3296_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillWith_spec__0___redArg(v___x_3287_, v_sep_3286_, v_ds_3285_, v___x_3292_, v___x_3295_);
v_fst_3297_ = lean_ctor_get(v___x_3296_, 0);
lean_inc(v_fst_3297_);
v_snd_3298_ = lean_ctor_get(v___x_3296_, 1);
lean_inc(v_snd_3298_);
lean_dec_ref(v___x_3296_);
v___x_3299_ = lean_unsigned_to_nat(2u);
v___x_3300_ = lean_mk_empty_array_with_capacity(v___x_3299_);
v___x_3301_ = lean_array_push(v___x_3300_, v_fst_3297_);
v___x_3302_ = lean_array_push(v___x_3301_, v_snd_3298_);
v___x_3303_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_3302_);
return v___x_3303_;
}
else
{
lean_dec_ref(v_sep_3286_);
lean_inc(v_lastNotFlattened_3291_);
return v_lastNotFlattened_3291_;
}
}
else
{
lean_object* v___x_3304_; 
lean_dec_ref(v_sep_3286_);
v___x_3304_ = lean_obj_once(&l_Lean_Fmt_Doc_empty___closed__0, &l_Lean_Fmt_Doc_empty___closed__0_once, _init_l_Lean_Fmt_Doc_empty___closed__0);
return v___x_3304_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillWith___redArg___boxed(lean_object* v_ds_3305_, lean_object* v_sep_3306_){
_start:
{
lean_object* v_res_3307_; 
v_res_3307_ = l_Lean_Fmt_Doc_fillWith___redArg(v_ds_3305_, v_sep_3306_);
lean_dec_ref(v_ds_3305_);
return v_res_3307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillWith(lean_object* v_00_u03c4_3308_, lean_object* v_ds_3309_, lean_object* v_sep_3310_){
_start:
{
lean_object* v___x_3311_; 
v___x_3311_ = l_Lean_Fmt_Doc_fillWith___redArg(v_ds_3309_, v_sep_3310_);
return v___x_3311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillWith___boxed(lean_object* v_00_u03c4_3312_, lean_object* v_ds_3313_, lean_object* v_sep_3314_){
_start:
{
lean_object* v_res_3315_; 
v_res_3315_ = l_Lean_Fmt_Doc_fillWith(v_00_u03c4_3312_, v_ds_3313_, v_sep_3314_);
lean_dec_ref(v_ds_3313_);
return v_res_3315_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillWith_spec__0(lean_object* v_00_u03c4_3316_, lean_object* v_upperBound_3317_, lean_object* v_sep_3318_, lean_object* v_ds_3319_, lean_object* v_inst_3320_, lean_object* v_R_3321_, lean_object* v_a_3322_, lean_object* v_b_3323_, lean_object* v_c_3324_){
_start:
{
lean_object* v___x_3325_; 
v___x_3325_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillWith_spec__0___redArg(v_upperBound_3317_, v_sep_3318_, v_ds_3319_, v_a_3322_, v_b_3323_);
return v___x_3325_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillWith_spec__0___boxed(lean_object* v_00_u03c4_3326_, lean_object* v_upperBound_3327_, lean_object* v_sep_3328_, lean_object* v_ds_3329_, lean_object* v_inst_3330_, lean_object* v_R_3331_, lean_object* v_a_3332_, lean_object* v_b_3333_, lean_object* v_c_3334_){
_start:
{
lean_object* v_res_3335_; 
v_res_3335_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillWith_spec__0(v_00_u03c4_3326_, v_upperBound_3327_, v_sep_3328_, v_ds_3329_, v_inst_3330_, v_R_3331_, v_a_3332_, v_b_3333_, v_c_3334_);
lean_dec_ref(v_ds_3329_);
lean_dec(v_upperBound_3327_);
return v_res_3335_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_fill___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3336_; lean_object* v___x_3337_; 
v___x_3336_ = lean_obj_once(&l_Lean_Fmt_Doc_empty___closed__0, &l_Lean_Fmt_Doc_empty___closed__0_once, _init_l_Lean_Fmt_Doc_empty___closed__0);
v___x_3337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3337_, 0, v___x_3336_);
lean_ctor_set(v___x_3337_, 1, v___x_3336_);
return v___x_3337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fill___redArg___lam__0(lean_object* v_x_3338_){
_start:
{
lean_object* v___x_3339_; 
v___x_3339_ = lean_obj_once(&l_Lean_Fmt_Doc_fill___redArg___lam__0___closed__0, &l_Lean_Fmt_Doc_fill___redArg___lam__0___closed__0_once, _init_l_Lean_Fmt_Doc_fill___redArg___lam__0___closed__0);
return v___x_3339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fill___redArg___lam__0___boxed(lean_object* v_x_3340_){
_start:
{
lean_object* v_res_3341_; 
v_res_3341_ = l_Lean_Fmt_Doc_fill___redArg___lam__0(v_x_3340_);
lean_dec(v_x_3340_);
return v_res_3341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fill___redArg(lean_object* v_ds_3343_){
_start:
{
lean_object* v___f_3344_; lean_object* v___x_3345_; 
v___f_3344_ = ((lean_object*)(l_Lean_Fmt_Doc_fill___redArg___closed__0));
v___x_3345_ = l_Lean_Fmt_Doc_fillWith___redArg(v_ds_3343_, v___f_3344_);
return v___x_3345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fill___redArg___boxed(lean_object* v_ds_3346_){
_start:
{
lean_object* v_res_3347_; 
v_res_3347_ = l_Lean_Fmt_Doc_fill___redArg(v_ds_3346_);
lean_dec_ref(v_ds_3346_);
return v_res_3347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fill(lean_object* v_00_u03c4_3348_, lean_object* v_ds_3349_){
_start:
{
lean_object* v___x_3350_; 
v___x_3350_ = l_Lean_Fmt_Doc_fill___redArg(v_ds_3349_);
return v___x_3350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fill___boxed(lean_object* v_00_u03c4_3351_, lean_object* v_ds_3352_){
_start:
{
lean_object* v_res_3353_; 
v_res_3353_ = l_Lean_Fmt_Doc_fill(v_00_u03c4_3351_, v_ds_3352_);
lean_dec_ref(v_ds_3352_);
return v_res_3353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsing___redArg___lam__0(lean_object* v_sep_3354_, lean_object* v_x_3355_){
_start:
{
lean_object* v___x_3356_; 
lean_inc(v_sep_3354_);
v___x_3356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3356_, 0, v_sep_3354_);
lean_ctor_set(v___x_3356_, 1, v_sep_3354_);
return v___x_3356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsing___redArg___lam__0___boxed(lean_object* v_sep_3357_, lean_object* v_x_3358_){
_start:
{
lean_object* v_res_3359_; 
v_res_3359_ = l_Lean_Fmt_Doc_fillUsing___redArg___lam__0(v_sep_3357_, v_x_3358_);
lean_dec(v_x_3358_);
return v_res_3359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsing___redArg(lean_object* v_sep_3360_, lean_object* v_ds_3361_){
_start:
{
lean_object* v___f_3362_; lean_object* v___x_3363_; 
v___f_3362_ = lean_alloc_closure((void*)(l_Lean_Fmt_Doc_fillUsing___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3362_, 0, v_sep_3360_);
v___x_3363_ = l_Lean_Fmt_Doc_fillWith___redArg(v_ds_3361_, v___f_3362_);
return v___x_3363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsing___redArg___boxed(lean_object* v_sep_3364_, lean_object* v_ds_3365_){
_start:
{
lean_object* v_res_3366_; 
v_res_3366_ = l_Lean_Fmt_Doc_fillUsing___redArg(v_sep_3364_, v_ds_3365_);
lean_dec_ref(v_ds_3365_);
return v_res_3366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsing(lean_object* v_00_u03c4_3367_, lean_object* v_sep_3368_, lean_object* v_ds_3369_){
_start:
{
lean_object* v___x_3370_; 
v___x_3370_ = l_Lean_Fmt_Doc_fillUsing___redArg(v_sep_3368_, v_ds_3369_);
return v___x_3370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsing___boxed(lean_object* v_00_u03c4_3371_, lean_object* v_sep_3372_, lean_object* v_ds_3373_){
_start:
{
lean_object* v_res_3374_; 
v_res_3374_ = l_Lean_Fmt_Doc_fillUsing(v_00_u03c4_3371_, v_sep_3372_, v_ds_3373_);
lean_dec_ref(v_ds_3373_);
return v_res_3374_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_fillUsingSpace___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3375_; lean_object* v___x_3376_; 
v___x_3375_ = ((lean_object*)(l_Lean_Fmt_Doc_nl___redArg___closed__0));
v___x_3376_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_3375_);
return v___x_3376_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_fillUsingSpace___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; 
v___x_3377_ = lean_obj_once(&l_Lean_Fmt_Doc_empty___closed__0, &l_Lean_Fmt_Doc_empty___closed__0_once, _init_l_Lean_Fmt_Doc_empty___closed__0);
v___x_3378_ = lean_obj_once(&l_Lean_Fmt_Doc_fillUsingSpace___redArg___lam__0___closed__0, &l_Lean_Fmt_Doc_fillUsingSpace___redArg___lam__0___closed__0_once, _init_l_Lean_Fmt_Doc_fillUsingSpace___redArg___lam__0___closed__0);
v___x_3379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3379_, 0, v___x_3378_);
lean_ctor_set(v___x_3379_, 1, v___x_3377_);
return v___x_3379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpace___redArg___lam__0(lean_object* v_x_3380_){
_start:
{
lean_object* v___x_3381_; 
v___x_3381_ = lean_obj_once(&l_Lean_Fmt_Doc_fillUsingSpace___redArg___lam__0___closed__1, &l_Lean_Fmt_Doc_fillUsingSpace___redArg___lam__0___closed__1_once, _init_l_Lean_Fmt_Doc_fillUsingSpace___redArg___lam__0___closed__1);
return v___x_3381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpace___redArg___lam__0___boxed(lean_object* v_x_3382_){
_start:
{
lean_object* v_res_3383_; 
v_res_3383_ = l_Lean_Fmt_Doc_fillUsingSpace___redArg___lam__0(v_x_3382_);
lean_dec(v_x_3382_);
return v_res_3383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpace___redArg(lean_object* v_ds_3385_){
_start:
{
lean_object* v___f_3386_; lean_object* v___x_3387_; 
v___f_3386_ = ((lean_object*)(l_Lean_Fmt_Doc_fillUsingSpace___redArg___closed__0));
v___x_3387_ = l_Lean_Fmt_Doc_fillWith___redArg(v_ds_3385_, v___f_3386_);
return v___x_3387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpace___redArg___boxed(lean_object* v_ds_3388_){
_start:
{
lean_object* v_res_3389_; 
v_res_3389_ = l_Lean_Fmt_Doc_fillUsingSpace___redArg(v_ds_3388_);
lean_dec_ref(v_ds_3388_);
return v_res_3389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpace(lean_object* v_00_u03c4_3390_, lean_object* v_ds_3391_){
_start:
{
lean_object* v___x_3392_; 
v___x_3392_ = l_Lean_Fmt_Doc_fillUsingSpace___redArg(v_ds_3391_);
return v___x_3392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpace___boxed(lean_object* v_00_u03c4_3393_, lean_object* v_ds_3394_){
_start:
{
lean_object* v_res_3395_; 
v_res_3395_ = l_Lean_Fmt_Doc_fillUsingSpace(v_00_u03c4_3393_, v_ds_3394_);
lean_dec_ref(v_ds_3394_);
return v_res_3395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg___lam__0(uint8_t v___x_3396_, lean_object* v___y_3397_, lean_object* v_sep_3398_, lean_object* v_boundarySep_3399_, lean_object* v_i_3400_){
_start:
{
lean_object* v___y_3402_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; uint8_t v___x_3409_; 
v___x_3405_ = lean_unsigned_to_nat(1u);
v___x_3406_ = lean_nat_add(v_i_3400_, v___x_3405_);
v___x_3407_ = lean_box(v___x_3396_);
v___x_3408_ = lean_array_get(v___x_3407_, v___y_3397_, v___x_3406_);
lean_dec(v___x_3406_);
lean_dec(v___x_3407_);
v___x_3409_ = lean_unbox(v___x_3408_);
lean_dec(v___x_3408_);
if (v___x_3409_ == 0)
{
lean_dec(v_boundarySep_3399_);
v___y_3402_ = v_sep_3398_;
goto v___jp_3401_;
}
else
{
lean_dec(v_sep_3398_);
v___y_3402_ = v_boundarySep_3399_;
goto v___jp_3401_;
}
v___jp_3401_:
{
lean_object* v___x_3403_; lean_object* v___x_3404_; 
v___x_3403_ = lean_obj_once(&l_Lean_Fmt_Doc_empty___closed__0, &l_Lean_Fmt_Doc_empty___closed__0_once, _init_l_Lean_Fmt_Doc_empty___closed__0);
v___x_3404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3404_, 0, v___y_3402_);
lean_ctor_set(v___x_3404_, 1, v___x_3403_);
return v___x_3404_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg___lam__0___boxed(lean_object* v___x_3410_, lean_object* v___y_3411_, lean_object* v_sep_3412_, lean_object* v_boundarySep_3413_, lean_object* v_i_3414_){
_start:
{
uint8_t v___x_550__boxed_3415_; lean_object* v_res_3416_; 
v___x_550__boxed_3415_ = lean_unbox(v___x_3410_);
v_res_3416_ = l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg___lam__0(v___x_550__boxed_3415_, v___y_3411_, v_sep_3412_, v_boundarySep_3413_, v_i_3414_);
lean_dec(v_i_3414_);
lean_dec_ref(v___y_3411_);
return v_res_3416_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__0___redArg(size_t v_sz_3417_, size_t v_i_3418_, lean_object* v_bs_3419_){
_start:
{
uint8_t v___x_3420_; 
v___x_3420_ = lean_usize_dec_lt(v_i_3418_, v_sz_3417_);
if (v___x_3420_ == 0)
{
return v_bs_3419_;
}
else
{
lean_object* v___x_3421_; lean_object* v_bs_x27_3422_; lean_object* v___x_3423_; uint8_t v___x_3424_; size_t v___x_3425_; size_t v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3421_ = lean_unsigned_to_nat(0u);
v_bs_x27_3422_ = lean_array_uset(v_bs_3419_, v_i_3418_, v___x_3421_);
v___x_3423_ = lean_usize_to_nat(v_i_3418_);
v___x_3424_ = lean_nat_dec_eq(v___x_3423_, v___x_3421_);
lean_dec(v___x_3423_);
v___x_3425_ = ((size_t)1ULL);
v___x_3426_ = lean_usize_add(v_i_3418_, v___x_3425_);
v___x_3427_ = lean_box(v___x_3424_);
v___x_3428_ = lean_array_uset(v_bs_x27_3422_, v_i_3418_, v___x_3427_);
v_i_3418_ = v___x_3426_;
v_bs_3419_ = v___x_3428_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__0___redArg___boxed(lean_object* v_sz_3430_, lean_object* v_i_3431_, lean_object* v_bs_3432_){
_start:
{
size_t v_sz_boxed_3433_; size_t v_i_boxed_3434_; lean_object* v_res_3435_; 
v_sz_boxed_3433_ = lean_unbox_usize(v_sz_3430_);
lean_dec(v_sz_3430_);
v_i_boxed_3434_ = lean_unbox_usize(v_i_3431_);
lean_dec(v_i_3431_);
v_res_3435_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__0___redArg(v_sz_boxed_3433_, v_i_boxed_3434_, v_bs_3432_);
return v_res_3435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__2___redArg(lean_object* v_as_3436_, size_t v_i_3437_, size_t v_stop_3438_, lean_object* v_b_3439_){
_start:
{
uint8_t v___x_3440_; 
v___x_3440_ = lean_usize_dec_eq(v_i_3437_, v_stop_3438_);
if (v___x_3440_ == 0)
{
lean_object* v___x_3441_; size_t v_sz_3442_; size_t v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; size_t v___x_3446_; size_t v___x_3447_; 
v___x_3441_ = lean_array_uget_borrowed(v_as_3436_, v_i_3437_);
v_sz_3442_ = lean_array_size(v___x_3441_);
v___x_3443_ = ((size_t)0ULL);
lean_inc(v___x_3441_);
v___x_3444_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__0___redArg(v_sz_3442_, v___x_3443_, v___x_3441_);
v___x_3445_ = l_Array_append___redArg(v_b_3439_, v___x_3444_);
lean_dec_ref(v___x_3444_);
v___x_3446_ = ((size_t)1ULL);
v___x_3447_ = lean_usize_add(v_i_3437_, v___x_3446_);
v_i_3437_ = v___x_3447_;
v_b_3439_ = v___x_3445_;
goto _start;
}
else
{
return v_b_3439_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__2___redArg___boxed(lean_object* v_as_3449_, lean_object* v_i_3450_, lean_object* v_stop_3451_, lean_object* v_b_3452_){
_start:
{
size_t v_i_boxed_3453_; size_t v_stop_boxed_3454_; lean_object* v_res_3455_; 
v_i_boxed_3453_ = lean_unbox_usize(v_i_3450_);
lean_dec(v_i_3450_);
v_stop_boxed_3454_ = lean_unbox_usize(v_stop_3451_);
lean_dec(v_stop_3451_);
v_res_3455_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__2___redArg(v_as_3449_, v_i_boxed_3453_, v_stop_boxed_3454_, v_b_3452_);
lean_dec_ref(v_as_3449_);
return v_res_3455_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__1___redArg(lean_object* v_as_3456_, size_t v_i_3457_, size_t v_stop_3458_, lean_object* v_b_3459_){
_start:
{
uint8_t v___x_3460_; 
v___x_3460_ = lean_usize_dec_eq(v_i_3457_, v_stop_3458_);
if (v___x_3460_ == 0)
{
lean_object* v___x_3461_; lean_object* v___x_3462_; size_t v___x_3463_; size_t v___x_3464_; 
v___x_3461_ = lean_array_uget_borrowed(v_as_3456_, v_i_3457_);
v___x_3462_ = l_Array_append___redArg(v_b_3459_, v___x_3461_);
v___x_3463_ = ((size_t)1ULL);
v___x_3464_ = lean_usize_add(v_i_3457_, v___x_3463_);
v_i_3457_ = v___x_3464_;
v_b_3459_ = v___x_3462_;
goto _start;
}
else
{
return v_b_3459_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__1___redArg___boxed(lean_object* v_as_3466_, lean_object* v_i_3467_, lean_object* v_stop_3468_, lean_object* v_b_3469_){
_start:
{
size_t v_i_boxed_3470_; size_t v_stop_boxed_3471_; lean_object* v_res_3472_; 
v_i_boxed_3470_ = lean_unbox_usize(v_i_3467_);
lean_dec(v_i_3467_);
v_stop_boxed_3471_ = lean_unbox_usize(v_stop_3468_);
lean_dec(v_stop_3468_);
v_res_3472_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__1___redArg(v_as_3466_, v_i_boxed_3470_, v_stop_boxed_3471_, v_b_3469_);
lean_dec_ref(v_as_3466_);
return v_res_3472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg(lean_object* v_boundaryPenalty_3477_, lean_object* v_dss_3478_){
_start:
{
uint8_t v___x_3479_; lean_object* v___y_3481_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; uint8_t v___x_3498_; 
v___x_3479_ = 0;
v___x_3495_ = lean_unsigned_to_nat(0u);
v___x_3496_ = ((lean_object*)(l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg___closed__1));
v___x_3497_ = lean_array_get_size(v_dss_3478_);
v___x_3498_ = lean_nat_dec_lt(v___x_3495_, v___x_3497_);
if (v___x_3498_ == 0)
{
v___y_3481_ = v___x_3496_;
goto v___jp_3480_;
}
else
{
size_t v___x_3499_; size_t v___x_3500_; lean_object* v___x_3501_; 
v___x_3499_ = ((size_t)0ULL);
v___x_3500_ = lean_usize_of_nat(v___x_3497_);
v___x_3501_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__2___redArg(v_dss_3478_, v___x_3499_, v___x_3500_, v___x_3496_);
v___y_3481_ = v___x_3501_;
goto v___jp_3480_;
}
v___jp_3480_:
{
lean_object* v_sep_3482_; lean_object* v_boundarySep_3483_; lean_object* v___x_3484_; lean_object* v___f_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; uint8_t v___x_3489_; 
v_sep_3482_ = lean_obj_once(&l_Lean_Fmt_Doc_fillUsingSpace___redArg___lam__0___closed__0, &l_Lean_Fmt_Doc_fillUsingSpace___redArg___lam__0___closed__0_once, _init_l_Lean_Fmt_Doc_fillUsingSpace___redArg___lam__0___closed__0);
v_boundarySep_3483_ = l_Lean_Fmt_Doc_costing___override___redArg(v_boundaryPenalty_3477_, v_sep_3482_);
v___x_3484_ = lean_box(v___x_3479_);
v___f_3485_ = lean_alloc_closure((void*)(l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3485_, 0, v___x_3484_);
lean_closure_set(v___f_3485_, 1, v___y_3481_);
lean_closure_set(v___f_3485_, 2, v_sep_3482_);
lean_closure_set(v___f_3485_, 3, v_boundarySep_3483_);
v___x_3486_ = lean_unsigned_to_nat(0u);
v___x_3487_ = ((lean_object*)(l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg___closed__0));
v___x_3488_ = lean_array_get_size(v_dss_3478_);
v___x_3489_ = lean_nat_dec_lt(v___x_3486_, v___x_3488_);
if (v___x_3489_ == 0)
{
lean_object* v___x_3490_; 
v___x_3490_ = l_Lean_Fmt_Doc_fillWith___redArg(v___x_3487_, v___f_3485_);
return v___x_3490_;
}
else
{
size_t v___x_3491_; size_t v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; 
v___x_3491_ = ((size_t)0ULL);
v___x_3492_ = lean_usize_of_nat(v___x_3488_);
v___x_3493_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__1___redArg(v_dss_3478_, v___x_3491_, v___x_3492_, v___x_3487_);
v___x_3494_ = l_Lean_Fmt_Doc_fillWith___redArg(v___x_3493_, v___f_3485_);
lean_dec_ref(v___x_3493_);
return v___x_3494_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg___boxed(lean_object* v_boundaryPenalty_3502_, lean_object* v_dss_3503_){
_start:
{
lean_object* v_res_3504_; 
v_res_3504_ = l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg(v_boundaryPenalty_3502_, v_dss_3503_);
lean_dec_ref(v_dss_3503_);
return v_res_3504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries(lean_object* v_00_u03c4_3505_, lean_object* v_boundaryPenalty_3506_, lean_object* v_dss_3507_){
_start:
{
lean_object* v___x_3508_; 
v___x_3508_ = l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg(v_boundaryPenalty_3506_, v_dss_3507_);
return v___x_3508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___boxed(lean_object* v_00_u03c4_3509_, lean_object* v_boundaryPenalty_3510_, lean_object* v_dss_3511_){
_start:
{
lean_object* v_res_3512_; 
v_res_3512_ = l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries(v_00_u03c4_3509_, v_boundaryPenalty_3510_, v_dss_3511_);
lean_dec_ref(v_dss_3511_);
return v_res_3512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__0(lean_object* v_00_u03c4_3513_, lean_object* v_as_3514_, size_t v_sz_3515_, size_t v_i_3516_, lean_object* v_bs_3517_){
_start:
{
lean_object* v___x_3518_; 
v___x_3518_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__0___redArg(v_sz_3515_, v_i_3516_, v_bs_3517_);
return v___x_3518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__0___boxed(lean_object* v_00_u03c4_3519_, lean_object* v_as_3520_, lean_object* v_sz_3521_, lean_object* v_i_3522_, lean_object* v_bs_3523_){
_start:
{
size_t v_sz_boxed_3524_; size_t v_i_boxed_3525_; lean_object* v_res_3526_; 
v_sz_boxed_3524_ = lean_unbox_usize(v_sz_3521_);
lean_dec(v_sz_3521_);
v_i_boxed_3525_ = lean_unbox_usize(v_i_3522_);
lean_dec(v_i_3522_);
v_res_3526_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__0(v_00_u03c4_3519_, v_as_3520_, v_sz_boxed_3524_, v_i_boxed_3525_, v_bs_3523_);
lean_dec_ref(v_as_3520_);
return v_res_3526_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__1(lean_object* v_00_u03c4_3527_, lean_object* v_as_3528_, size_t v_i_3529_, size_t v_stop_3530_, lean_object* v_b_3531_){
_start:
{
lean_object* v___x_3532_; 
v___x_3532_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__1___redArg(v_as_3528_, v_i_3529_, v_stop_3530_, v_b_3531_);
return v___x_3532_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__1___boxed(lean_object* v_00_u03c4_3533_, lean_object* v_as_3534_, lean_object* v_i_3535_, lean_object* v_stop_3536_, lean_object* v_b_3537_){
_start:
{
size_t v_i_boxed_3538_; size_t v_stop_boxed_3539_; lean_object* v_res_3540_; 
v_i_boxed_3538_ = lean_unbox_usize(v_i_3535_);
lean_dec(v_i_3535_);
v_stop_boxed_3539_ = lean_unbox_usize(v_stop_3536_);
lean_dec(v_stop_3536_);
v_res_3540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__1(v_00_u03c4_3533_, v_as_3534_, v_i_boxed_3538_, v_stop_boxed_3539_, v_b_3537_);
lean_dec_ref(v_as_3534_);
return v_res_3540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__2(lean_object* v_00_u03c4_3541_, lean_object* v_as_3542_, size_t v_i_3543_, size_t v_stop_3544_, lean_object* v_b_3545_){
_start:
{
lean_object* v___x_3546_; 
v___x_3546_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__2___redArg(v_as_3542_, v_i_3543_, v_stop_3544_, v_b_3545_);
return v___x_3546_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__2___boxed(lean_object* v_00_u03c4_3547_, lean_object* v_as_3548_, lean_object* v_i_3549_, lean_object* v_stop_3550_, lean_object* v_b_3551_){
_start:
{
size_t v_i_boxed_3552_; size_t v_stop_boxed_3553_; lean_object* v_res_3554_; 
v_i_boxed_3552_ = lean_unbox_usize(v_i_3549_);
lean_dec(v_i_3549_);
v_stop_boxed_3553_ = lean_unbox_usize(v_stop_3550_);
lean_dec(v_stop_3550_);
v_res_3554_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__2(v_00_u03c4_3547_, v_as_3548_, v_i_boxed_3552_, v_stop_boxed_3553_, v_b_3551_);
lean_dec_ref(v_as_3548_);
return v_res_3554_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrappingWith_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; 
v___x_3555_ = lean_obj_once(&l_Lean_Fmt_Doc_nl___closed__0, &l_Lean_Fmt_Doc_nl___closed__0_once, _init_l_Lean_Fmt_Doc_nl___closed__0);
v___x_3556_ = lean_unsigned_to_nat(2u);
v___x_3557_ = lean_mk_empty_array_with_capacity(v___x_3556_);
v___x_3558_ = lean_array_push(v___x_3557_, v___x_3555_);
return v___x_3558_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrappingWith_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; 
v___x_3559_ = lean_obj_once(&l_Lean_Fmt_Doc_hardNl___closed__0, &l_Lean_Fmt_Doc_hardNl___closed__0_once, _init_l_Lean_Fmt_Doc_hardNl___closed__0);
v___x_3560_ = lean_unsigned_to_nat(2u);
v___x_3561_ = lean_mk_empty_array_with_capacity(v___x_3560_);
v___x_3562_ = lean_array_push(v___x_3561_, v___x_3559_);
return v___x_3562_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrappingWith_spec__0___redArg(lean_object* v_sep_3563_, lean_object* v_wrap_3564_, lean_object* v_as_3565_, size_t v_sz_3566_, size_t v_i_3567_, lean_object* v_b_3568_){
_start:
{
lean_object* v_a_3570_; uint8_t v___x_3574_; 
v___x_3574_ = lean_usize_dec_lt(v_i_3567_, v_sz_3566_);
if (v___x_3574_ == 0)
{
lean_dec_ref(v_wrap_3564_);
lean_dec_ref(v_sep_3563_);
return v_b_3568_;
}
else
{
lean_object* v_a_3575_; lean_object* v_fst_3576_; lean_object* v_snd_3577_; lean_object* v_fst_3578_; lean_object* v_snd_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3627_; 
v_a_3575_ = lean_array_uget_borrowed(v_as_3565_, v_i_3567_);
v_fst_3576_ = lean_ctor_get(v_a_3575_, 0);
v_snd_3577_ = lean_ctor_get(v_a_3575_, 1);
v_fst_3578_ = lean_ctor_get(v_b_3568_, 0);
v_snd_3579_ = lean_ctor_get(v_b_3568_, 1);
v_isSharedCheck_3627_ = !lean_is_exclusive(v_b_3568_);
if (v_isSharedCheck_3627_ == 0)
{
v___x_3581_ = v_b_3568_;
v_isShared_3582_ = v_isSharedCheck_3627_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_snd_3579_);
lean_inc(v_fst_3578_);
lean_dec(v_b_3568_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3627_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; 
v___x_3583_ = lean_unsigned_to_nat(2u);
v___x_3584_ = lean_mk_empty_array_with_capacity(v___x_3583_);
lean_inc(v_fst_3578_);
lean_inc_ref(v___x_3584_);
v___x_3585_ = lean_array_push(v___x_3584_, v_fst_3578_);
v___x_3586_ = lean_array_push(v___x_3585_, v_snd_3579_);
v___x_3587_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_3586_);
lean_inc_ref(v_sep_3563_);
lean_inc(v_snd_3577_);
v___x_3588_ = lean_apply_1(v_sep_3563_, v_snd_3577_);
if (lean_obj_tag(v___x_3588_) == 0)
{
lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3601_; 
lean_dec(v_fst_3578_);
v___x_3589_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrappingWith_spec__0___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrappingWith_spec__0___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrappingWith_spec__0___redArg___closed__0);
v___x_3590_ = lean_array_push(v___x_3589_, v___x_3587_);
v___x_3591_ = l_Lean_Fmt_Doc_join___redArg(v___x_3590_);
lean_inc_ref(v_wrap_3564_);
v___x_3592_ = lean_apply_1(v_wrap_3564_, v___x_3591_);
lean_inc_n(v_fst_3576_, 2);
v___x_3593_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_fst_3576_);
lean_inc_ref(v___x_3584_);
v___x_3594_ = lean_array_push(v___x_3584_, v___x_3593_);
lean_inc(v___x_3592_);
v___x_3595_ = lean_array_push(v___x_3594_, v___x_3592_);
v___x_3596_ = l_Lean_Fmt_Doc_join___redArg(v___x_3595_);
v___x_3597_ = lean_array_push(v___x_3584_, v_fst_3576_);
v___x_3598_ = lean_array_push(v___x_3597_, v___x_3592_);
v___x_3599_ = l_Lean_Fmt_Doc_join___redArg(v___x_3598_);
if (v_isShared_3582_ == 0)
{
lean_ctor_set(v___x_3581_, 1, v___x_3599_);
lean_ctor_set(v___x_3581_, 0, v___x_3596_);
v___x_3601_ = v___x_3581_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v___x_3596_);
lean_ctor_set(v_reuseFailAlloc_3602_, 1, v___x_3599_);
v___x_3601_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
v_a_3570_ = v___x_3601_;
goto v___jp_3569_;
}
}
else
{
lean_object* v_val_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3625_; 
v_val_3603_ = lean_ctor_get(v___x_3588_, 0);
lean_inc(v_val_3603_);
lean_dec_ref_known(v___x_3588_, 1);
v___x_3604_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrappingWith_spec__0___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrappingWith_spec__0___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrappingWith_spec__0___redArg___closed__1);
v___x_3605_ = lean_array_push(v___x_3604_, v___x_3587_);
v___x_3606_ = l_Lean_Fmt_Doc_join___redArg(v___x_3605_);
lean_inc_ref_n(v_wrap_3564_, 2);
v___x_3607_ = lean_apply_1(v_wrap_3564_, v___x_3606_);
lean_inc_n(v_fst_3576_, 2);
v___x_3608_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_fst_3576_);
lean_inc_ref_n(v___x_3584_, 3);
v___x_3609_ = lean_array_push(v___x_3584_, v_val_3603_);
v___x_3610_ = lean_array_push(v___x_3609_, v_fst_3578_);
v___x_3611_ = l_Lean_Fmt_Doc_join___redArg(v___x_3610_);
v___x_3612_ = lean_apply_1(v_wrap_3564_, v___x_3611_);
v___x_3613_ = lean_array_push(v___x_3584_, v___x_3608_);
lean_inc_ref(v___x_3613_);
v___x_3614_ = lean_array_push(v___x_3613_, v___x_3612_);
v___x_3615_ = l_Lean_Fmt_Doc_join___redArg(v___x_3614_);
lean_inc(v___x_3607_);
v___x_3616_ = lean_array_push(v___x_3613_, v___x_3607_);
v___x_3617_ = l_Lean_Fmt_Doc_join___redArg(v___x_3616_);
v___x_3618_ = lean_array_push(v___x_3584_, v___x_3615_);
v___x_3619_ = lean_array_push(v___x_3618_, v___x_3617_);
v___x_3620_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_3619_);
v___x_3621_ = lean_array_push(v___x_3584_, v_fst_3576_);
v___x_3622_ = lean_array_push(v___x_3621_, v___x_3607_);
v___x_3623_ = l_Lean_Fmt_Doc_join___redArg(v___x_3622_);
if (v_isShared_3582_ == 0)
{
lean_ctor_set(v___x_3581_, 1, v___x_3623_);
lean_ctor_set(v___x_3581_, 0, v___x_3620_);
v___x_3625_ = v___x_3581_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v___x_3620_);
lean_ctor_set(v_reuseFailAlloc_3626_, 1, v___x_3623_);
v___x_3625_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
v_a_3570_ = v___x_3625_;
goto v___jp_3569_;
}
}
}
}
v___jp_3569_:
{
size_t v___x_3571_; size_t v___x_3572_; 
v___x_3571_ = ((size_t)1ULL);
v___x_3572_ = lean_usize_add(v_i_3567_, v___x_3571_);
v_i_3567_ = v___x_3572_;
v_b_3568_ = v_a_3570_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrappingWith_spec__0___redArg___boxed(lean_object* v_sep_3628_, lean_object* v_wrap_3629_, lean_object* v_as_3630_, lean_object* v_sz_3631_, lean_object* v_i_3632_, lean_object* v_b_3633_){
_start:
{
size_t v_sz_boxed_3634_; size_t v_i_boxed_3635_; lean_object* v_res_3636_; 
v_sz_boxed_3634_ = lean_unbox_usize(v_sz_3631_);
lean_dec(v_sz_3631_);
v_i_boxed_3635_ = lean_unbox_usize(v_i_3632_);
lean_dec(v_i_3632_);
v_res_3636_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrappingWith_spec__0___redArg(v_sep_3628_, v_wrap_3629_, v_as_3630_, v_sz_boxed_3634_, v_i_boxed_3635_, v_b_3633_);
lean_dec_ref(v_as_3630_);
return v_res_3636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillWrappingWith___redArg(lean_object* v_ds_3637_, lean_object* v_wrap_3638_, lean_object* v_sep_3639_){
_start:
{
lean_object* v___x_3640_; lean_object* v___x_3641_; uint8_t v___x_3642_; 
v___x_3640_ = lean_array_get_size(v_ds_3637_);
v___x_3641_ = lean_unsigned_to_nat(0u);
v___x_3642_ = lean_nat_dec_eq(v___x_3640_, v___x_3641_);
if (v___x_3642_ == 0)
{
lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v_restNotFlattened_3646_; uint8_t v___x_3647_; 
v___x_3643_ = lean_box(0);
v___x_3644_ = lean_unsigned_to_nat(1u);
v___x_3645_ = lean_nat_sub(v___x_3640_, v___x_3644_);
v_restNotFlattened_3646_ = lean_array_get(v___x_3643_, v_ds_3637_, v___x_3645_);
lean_dec(v___x_3645_);
v___x_3647_ = lean_nat_dec_eq(v___x_3640_, v___x_3644_);
if (v___x_3647_ == 0)
{
lean_object* v_restFlattened_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; size_t v_sz_3653_; size_t v___x_3654_; lean_object* v___x_3655_; lean_object* v_fst_3656_; lean_object* v_snd_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; 
lean_inc(v_restNotFlattened_3646_);
v_restFlattened_3648_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_restNotFlattened_3646_);
v___x_3649_ = lean_array_pop(v_ds_3637_);
v___x_3650_ = l_Array_zipIdx___redArg(v___x_3649_, v___x_3641_);
v___x_3651_ = l_Array_reverse___redArg(v___x_3650_);
v___x_3652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3652_, 0, v_restFlattened_3648_);
lean_ctor_set(v___x_3652_, 1, v_restNotFlattened_3646_);
v_sz_3653_ = lean_array_size(v___x_3651_);
v___x_3654_ = ((size_t)0ULL);
v___x_3655_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrappingWith_spec__0___redArg(v_sep_3639_, v_wrap_3638_, v___x_3651_, v_sz_3653_, v___x_3654_, v___x_3652_);
lean_dec_ref(v___x_3651_);
v_fst_3656_ = lean_ctor_get(v___x_3655_, 0);
lean_inc(v_fst_3656_);
v_snd_3657_ = lean_ctor_get(v___x_3655_, 1);
lean_inc(v_snd_3657_);
lean_dec_ref(v___x_3655_);
v___x_3658_ = lean_unsigned_to_nat(2u);
v___x_3659_ = lean_mk_empty_array_with_capacity(v___x_3658_);
v___x_3660_ = lean_array_push(v___x_3659_, v_fst_3656_);
v___x_3661_ = lean_array_push(v___x_3660_, v_snd_3657_);
v___x_3662_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_3661_);
return v___x_3662_;
}
else
{
lean_dec_ref(v_sep_3639_);
lean_dec_ref(v_wrap_3638_);
lean_dec_ref(v_ds_3637_);
return v_restNotFlattened_3646_;
}
}
else
{
lean_object* v___x_3663_; 
lean_dec_ref(v_sep_3639_);
lean_dec_ref(v_wrap_3638_);
lean_dec_ref(v_ds_3637_);
v___x_3663_ = lean_obj_once(&l_Lean_Fmt_Doc_empty___closed__0, &l_Lean_Fmt_Doc_empty___closed__0_once, _init_l_Lean_Fmt_Doc_empty___closed__0);
return v___x_3663_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillWrappingWith(lean_object* v_00_u03c4_3664_, lean_object* v_ds_3665_, lean_object* v_wrap_3666_, lean_object* v_sep_3667_){
_start:
{
lean_object* v___x_3668_; 
v___x_3668_ = l_Lean_Fmt_Doc_fillWrappingWith___redArg(v_ds_3665_, v_wrap_3666_, v_sep_3667_);
return v___x_3668_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrappingWith_spec__0(lean_object* v_00_u03c4_3669_, lean_object* v_sep_3670_, lean_object* v_wrap_3671_, lean_object* v_as_3672_, size_t v_sz_3673_, size_t v_i_3674_, lean_object* v_b_3675_){
_start:
{
lean_object* v___x_3676_; 
v___x_3676_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrappingWith_spec__0___redArg(v_sep_3670_, v_wrap_3671_, v_as_3672_, v_sz_3673_, v_i_3674_, v_b_3675_);
return v___x_3676_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrappingWith_spec__0___boxed(lean_object* v_00_u03c4_3677_, lean_object* v_sep_3678_, lean_object* v_wrap_3679_, lean_object* v_as_3680_, lean_object* v_sz_3681_, lean_object* v_i_3682_, lean_object* v_b_3683_){
_start:
{
size_t v_sz_boxed_3684_; size_t v_i_boxed_3685_; lean_object* v_res_3686_; 
v_sz_boxed_3684_ = lean_unbox_usize(v_sz_3681_);
lean_dec(v_sz_3681_);
v_i_boxed_3685_ = lean_unbox_usize(v_i_3682_);
lean_dec(v_i_3682_);
v_res_3686_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrappingWith_spec__0(v_00_u03c4_3677_, v_sep_3678_, v_wrap_3679_, v_as_3680_, v_sz_boxed_3684_, v_i_boxed_3685_, v_b_3683_);
lean_dec_ref(v_as_3680_);
return v_res_3686_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_fillWrapping___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3687_; lean_object* v___x_3688_; 
v___x_3687_ = lean_obj_once(&l_Lean_Fmt_Doc_empty___closed__0, &l_Lean_Fmt_Doc_empty___closed__0_once, _init_l_Lean_Fmt_Doc_empty___closed__0);
v___x_3688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3688_, 0, v___x_3687_);
return v___x_3688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillWrapping___redArg___lam__0(lean_object* v_x_3689_){
_start:
{
lean_object* v___x_3690_; 
v___x_3690_ = lean_obj_once(&l_Lean_Fmt_Doc_fillWrapping___redArg___lam__0___closed__0, &l_Lean_Fmt_Doc_fillWrapping___redArg___lam__0___closed__0_once, _init_l_Lean_Fmt_Doc_fillWrapping___redArg___lam__0___closed__0);
return v___x_3690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillWrapping___redArg___lam__0___boxed(lean_object* v_x_3691_){
_start:
{
lean_object* v_res_3692_; 
v_res_3692_ = l_Lean_Fmt_Doc_fillWrapping___redArg___lam__0(v_x_3691_);
lean_dec(v_x_3691_);
return v_res_3692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillWrapping___redArg(lean_object* v_ds_3694_, lean_object* v_wrap_3695_){
_start:
{
lean_object* v___f_3696_; lean_object* v___x_3697_; 
v___f_3696_ = ((lean_object*)(l_Lean_Fmt_Doc_fillWrapping___redArg___closed__0));
v___x_3697_ = l_Lean_Fmt_Doc_fillWrappingWith___redArg(v_ds_3694_, v_wrap_3695_, v___f_3696_);
return v___x_3697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillWrapping(lean_object* v_00_u03c4_3698_, lean_object* v_ds_3699_, lean_object* v_wrap_3700_){
_start:
{
lean_object* v___x_3701_; 
v___x_3701_ = l_Lean_Fmt_Doc_fillWrapping___redArg(v_ds_3699_, v_wrap_3700_);
return v___x_3701_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3702_; lean_object* v___x_3703_; 
v___x_3702_ = lean_obj_once(&l_Lean_Fmt_Doc_fillUsingSpace___redArg___lam__0___closed__0, &l_Lean_Fmt_Doc_fillUsingSpace___redArg___lam__0___closed__0_once, _init_l_Lean_Fmt_Doc_fillUsingSpace___redArg___lam__0___closed__0);
v___x_3703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3703_, 0, v___x_3702_);
return v___x_3703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg___lam__0(lean_object* v_x_3704_){
_start:
{
lean_object* v___x_3705_; 
v___x_3705_ = lean_obj_once(&l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg___lam__0___closed__0, &l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg___lam__0___closed__0_once, _init_l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg___lam__0___closed__0);
return v___x_3705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg___lam__0___boxed(lean_object* v_x_3706_){
_start:
{
lean_object* v_res_3707_; 
v_res_3707_ = l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg___lam__0(v_x_3706_);
lean_dec(v_x_3706_);
return v_res_3707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg(lean_object* v_ds_3709_, lean_object* v_wrap_3710_){
_start:
{
lean_object* v___f_3711_; lean_object* v___x_3712_; 
v___f_3711_ = ((lean_object*)(l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg___closed__0));
v___x_3712_ = l_Lean_Fmt_Doc_fillWrappingWith___redArg(v_ds_3709_, v_wrap_3710_, v___f_3711_);
return v___x_3712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWrapping(lean_object* v_00_u03c4_3713_, lean_object* v_ds_3714_, lean_object* v_wrap_3715_){
_start:
{
lean_object* v___x_3716_; 
v___x_3716_ = l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg(v_ds_3714_, v_wrap_3715_);
return v___x_3716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedFillable_default___redArg(lean_object* v_inst_3717_){
_start:
{
uint8_t v___x_3718_; lean_object* v___x_3719_; 
v___x_3718_ = 0;
v___x_3719_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3719_, 0, v_inst_3717_);
lean_ctor_set_uint8(v___x_3719_, sizeof(void*)*1, v___x_3718_);
return v___x_3719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedFillable_default(lean_object* v_00_u03b1_3720_, lean_object* v_inst_3721_){
_start:
{
lean_object* v___x_3722_; 
v___x_3722_ = l_Lean_Fmt_instInhabitedFillable_default___redArg(v_inst_3721_);
return v___x_3722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedFillable___redArg(lean_object* v_inst_3723_){
_start:
{
lean_object* v___x_3724_; 
v___x_3724_ = l_Lean_Fmt_instInhabitedFillable_default___redArg(v_inst_3723_);
return v___x_3724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedFillable(lean_object* v_a_3725_, lean_object* v_inst_3726_){
_start:
{
lean_object* v___x_3727_; 
v___x_3727_ = l_Lean_Fmt_instInhabitedFillable_default___redArg(v_inst_3726_);
return v___x_3727_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0___redArg(size_t v_sz_3728_, size_t v_i_3729_, lean_object* v_bs_3730_){
_start:
{
uint8_t v___x_3731_; 
v___x_3731_ = lean_usize_dec_lt(v_i_3729_, v_sz_3728_);
if (v___x_3731_ == 0)
{
return v_bs_3730_;
}
else
{
lean_object* v_v_3732_; lean_object* v_v_3733_; lean_object* v___x_3734_; lean_object* v_bs_x27_3735_; size_t v___x_3736_; size_t v___x_3737_; lean_object* v___x_3738_; 
v_v_3732_ = lean_array_uget_borrowed(v_bs_3730_, v_i_3729_);
v_v_3733_ = lean_ctor_get(v_v_3732_, 0);
lean_inc(v_v_3733_);
v___x_3734_ = lean_unsigned_to_nat(0u);
v_bs_x27_3735_ = lean_array_uset(v_bs_3730_, v_i_3729_, v___x_3734_);
v___x_3736_ = ((size_t)1ULL);
v___x_3737_ = lean_usize_add(v_i_3729_, v___x_3736_);
v___x_3738_ = lean_array_uset(v_bs_x27_3735_, v_i_3729_, v_v_3733_);
v_i_3729_ = v___x_3737_;
v_bs_3730_ = v___x_3738_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0___redArg___boxed(lean_object* v_sz_3740_, lean_object* v_i_3741_, lean_object* v_bs_3742_){
_start:
{
size_t v_sz_boxed_3743_; size_t v_i_boxed_3744_; lean_object* v_res_3745_; 
v_sz_boxed_3743_ = lean_unbox_usize(v_sz_3740_);
lean_dec(v_sz_3740_);
v_i_boxed_3744_ = lean_unbox_usize(v_i_3741_);
lean_dec(v_i_3741_);
v_res_3745_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0___redArg(v_sz_boxed_3743_, v_i_boxed_3744_, v_bs_3742_);
return v_res_3745_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3___redArg(size_t v_sz_3746_, size_t v_i_3747_, lean_object* v_bs_3748_){
_start:
{
uint8_t v___x_3749_; 
v___x_3749_ = lean_usize_dec_lt(v_i_3747_, v_sz_3746_);
if (v___x_3749_ == 0)
{
return v_bs_3748_;
}
else
{
lean_object* v_v_3750_; lean_object* v___x_3751_; lean_object* v_bs_x27_3752_; size_t v_sz_3753_; size_t v___x_3754_; lean_object* v___x_3755_; size_t v___x_3756_; size_t v___x_3757_; lean_object* v___x_3758_; 
v_v_3750_ = lean_array_uget(v_bs_3748_, v_i_3747_);
v___x_3751_ = lean_unsigned_to_nat(0u);
v_bs_x27_3752_ = lean_array_uset(v_bs_3748_, v_i_3747_, v___x_3751_);
v_sz_3753_ = lean_array_size(v_v_3750_);
v___x_3754_ = ((size_t)0ULL);
v___x_3755_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0___redArg(v_sz_3753_, v___x_3754_, v_v_3750_);
v___x_3756_ = ((size_t)1ULL);
v___x_3757_ = lean_usize_add(v_i_3747_, v___x_3756_);
v___x_3758_ = lean_array_uset(v_bs_x27_3752_, v_i_3747_, v___x_3755_);
v_i_3747_ = v___x_3757_;
v_bs_3748_ = v___x_3758_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3___redArg___boxed(lean_object* v_sz_3760_, lean_object* v_i_3761_, lean_object* v_bs_3762_){
_start:
{
size_t v_sz_boxed_3763_; size_t v_i_boxed_3764_; lean_object* v_res_3765_; 
v_sz_boxed_3763_ = lean_unbox_usize(v_sz_3760_);
lean_dec(v_sz_3760_);
v_i_boxed_3764_ = lean_unbox_usize(v_i_3761_);
lean_dec(v_i_3761_);
v_res_3765_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3___redArg(v_sz_boxed_3763_, v_i_boxed_3764_, v_bs_3762_);
return v_res_3765_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Fmt_Doc_splitFillGroups_spec__2___redArg(lean_object* v_a_3766_, lean_object* v_a_3767_){
_start:
{
if (lean_obj_tag(v_a_3766_) == 0)
{
lean_object* v___x_3768_; 
v___x_3768_ = l_List_reverse___redArg(v_a_3767_);
return v___x_3768_;
}
else
{
lean_object* v_head_3769_; lean_object* v_tail_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3779_; 
v_head_3769_ = lean_ctor_get(v_a_3766_, 0);
v_tail_3770_ = lean_ctor_get(v_a_3766_, 1);
v_isSharedCheck_3779_ = !lean_is_exclusive(v_a_3766_);
if (v_isSharedCheck_3779_ == 0)
{
v___x_3772_ = v_a_3766_;
v_isShared_3773_ = v_isSharedCheck_3779_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_tail_3770_);
lean_inc(v_head_3769_);
lean_dec(v_a_3766_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3779_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v___x_3774_; lean_object* v___x_3776_; 
v___x_3774_ = lean_array_mk(v_head_3769_);
if (v_isShared_3773_ == 0)
{
lean_ctor_set(v___x_3772_, 1, v_a_3767_);
lean_ctor_set(v___x_3772_, 0, v___x_3774_);
v___x_3776_ = v___x_3772_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v___x_3774_);
lean_ctor_set(v_reuseFailAlloc_3778_, 1, v_a_3767_);
v___x_3776_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3775_;
}
v_reusejp_3775_:
{
v_a_3766_ = v_tail_3770_;
v_a_3767_ = v___x_3776_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_splitBy_loop___at___00List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1_spec__1___redArg(lean_object* v_a_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_, lean_object* v_a_3783_){
_start:
{
if (lean_obj_tag(v_a_3780_) == 0)
{
lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; 
v___x_3784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3784_, 0, v_a_3781_);
lean_ctor_set(v___x_3784_, 1, v_a_3782_);
v___x_3785_ = l_List_reverse___redArg(v___x_3784_);
v___x_3786_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3786_, 0, v___x_3785_);
lean_ctor_set(v___x_3786_, 1, v_a_3783_);
v___x_3787_ = l_List_reverse___redArg(v___x_3786_);
return v___x_3787_;
}
else
{
lean_object* v_head_3788_; lean_object* v_tail_3789_; lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3805_; 
v_head_3788_ = lean_ctor_get(v_a_3780_, 0);
v_tail_3789_ = lean_ctor_get(v_a_3780_, 1);
v_isSharedCheck_3805_ = !lean_is_exclusive(v_a_3780_);
if (v_isSharedCheck_3805_ == 0)
{
v___x_3791_ = v_a_3780_;
v_isShared_3792_ = v_isSharedCheck_3805_;
goto v_resetjp_3790_;
}
else
{
lean_inc(v_tail_3789_);
lean_inc(v_head_3788_);
lean_dec(v_a_3780_);
v___x_3791_ = lean_box(0);
v_isShared_3792_ = v_isSharedCheck_3805_;
goto v_resetjp_3790_;
}
v_resetjp_3790_:
{
uint8_t v_allowFill_3801_; 
v_allowFill_3801_ = lean_ctor_get_uint8(v_a_3781_, sizeof(void*)*1);
if (v_allowFill_3801_ == 0)
{
goto v___jp_3793_;
}
else
{
uint8_t v_allowFill_3802_; 
v_allowFill_3802_ = lean_ctor_get_uint8(v_head_3788_, sizeof(void*)*1);
if (v_allowFill_3802_ == 0)
{
goto v___jp_3793_;
}
else
{
lean_object* v___x_3803_; 
lean_del_object(v___x_3791_);
v___x_3803_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3803_, 0, v_a_3781_);
lean_ctor_set(v___x_3803_, 1, v_a_3782_);
v_a_3780_ = v_tail_3789_;
v_a_3781_ = v_head_3788_;
v_a_3782_ = v___x_3803_;
goto _start;
}
}
v___jp_3793_:
{
lean_object* v___x_3794_; lean_object* v___x_3796_; 
v___x_3794_ = lean_box(0);
if (v_isShared_3792_ == 0)
{
lean_ctor_set(v___x_3791_, 1, v_a_3782_);
lean_ctor_set(v___x_3791_, 0, v_a_3781_);
v___x_3796_ = v___x_3791_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v_a_3781_);
lean_ctor_set(v_reuseFailAlloc_3800_, 1, v_a_3782_);
v___x_3796_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
lean_object* v___x_3797_; lean_object* v___x_3798_; 
v___x_3797_ = l_List_reverse___redArg(v___x_3796_);
v___x_3798_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3798_, 0, v___x_3797_);
lean_ctor_set(v___x_3798_, 1, v_a_3783_);
v_a_3780_ = v_tail_3789_;
v_a_3781_ = v_head_3788_;
v_a_3782_ = v___x_3794_;
v_a_3783_ = v___x_3798_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1___redArg(lean_object* v_x_3806_){
_start:
{
if (lean_obj_tag(v_x_3806_) == 0)
{
lean_object* v___x_3807_; 
v___x_3807_ = lean_box(0);
return v___x_3807_;
}
else
{
lean_object* v_head_3808_; lean_object* v_tail_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; 
v_head_3808_ = lean_ctor_get(v_x_3806_, 0);
lean_inc(v_head_3808_);
v_tail_3809_ = lean_ctor_get(v_x_3806_, 1);
lean_inc(v_tail_3809_);
lean_dec_ref_known(v_x_3806_, 2);
v___x_3810_ = lean_box(0);
v___x_3811_ = l_List_splitBy_loop___at___00List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1_spec__1___redArg(v_tail_3809_, v_head_3808_, v___x_3810_, v___x_3810_);
return v___x_3811_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_splitFillGroups___redArg(lean_object* v_ds_3812_){
_start:
{
lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; size_t v_sz_3818_; size_t v___x_3819_; lean_object* v___x_3820_; 
v___x_3813_ = lean_array_to_list(v_ds_3812_);
v___x_3814_ = l_List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1___redArg(v___x_3813_);
v___x_3815_ = lean_box(0);
v___x_3816_ = l_List_mapTR_loop___at___00Lean_Fmt_Doc_splitFillGroups_spec__2___redArg(v___x_3814_, v___x_3815_);
v___x_3817_ = lean_array_mk(v___x_3816_);
v_sz_3818_ = lean_array_size(v___x_3817_);
v___x_3819_ = ((size_t)0ULL);
v___x_3820_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3___redArg(v_sz_3818_, v___x_3819_, v___x_3817_);
return v___x_3820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_splitFillGroups(lean_object* v_00_u03c4_3821_, lean_object* v_ds_3822_){
_start:
{
lean_object* v___x_3823_; 
v___x_3823_ = l_Lean_Fmt_Doc_splitFillGroups___redArg(v_ds_3822_);
return v___x_3823_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0(lean_object* v_00_u03c4_3824_, size_t v_sz_3825_, size_t v_i_3826_, lean_object* v_bs_3827_){
_start:
{
lean_object* v___x_3828_; 
v___x_3828_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0___redArg(v_sz_3825_, v_i_3826_, v_bs_3827_);
return v___x_3828_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0___boxed(lean_object* v_00_u03c4_3829_, lean_object* v_sz_3830_, lean_object* v_i_3831_, lean_object* v_bs_3832_){
_start:
{
size_t v_sz_boxed_3833_; size_t v_i_boxed_3834_; lean_object* v_res_3835_; 
v_sz_boxed_3833_ = lean_unbox_usize(v_sz_3830_);
lean_dec(v_sz_3830_);
v_i_boxed_3834_ = lean_unbox_usize(v_i_3831_);
lean_dec(v_i_3831_);
v_res_3835_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0(v_00_u03c4_3829_, v_sz_boxed_3833_, v_i_boxed_3834_, v_bs_3832_);
return v_res_3835_;
}
}
LEAN_EXPORT lean_object* l_List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1(lean_object* v_00_u03c4_3836_, lean_object* v_x_3837_){
_start:
{
lean_object* v___x_3838_; 
v___x_3838_ = l_List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1___redArg(v_x_3837_);
return v___x_3838_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Fmt_Doc_splitFillGroups_spec__2(lean_object* v_00_u03c4_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_){
_start:
{
lean_object* v___x_3842_; 
v___x_3842_ = l_List_mapTR_loop___at___00Lean_Fmt_Doc_splitFillGroups_spec__2___redArg(v_a_3840_, v_a_3841_);
return v___x_3842_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3(lean_object* v_00_u03c4_3843_, size_t v_sz_3844_, size_t v_i_3845_, lean_object* v_bs_3846_){
_start:
{
lean_object* v___x_3847_; 
v___x_3847_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3___redArg(v_sz_3844_, v_i_3845_, v_bs_3846_);
return v___x_3847_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3___boxed(lean_object* v_00_u03c4_3848_, lean_object* v_sz_3849_, lean_object* v_i_3850_, lean_object* v_bs_3851_){
_start:
{
size_t v_sz_boxed_3852_; size_t v_i_boxed_3853_; lean_object* v_res_3854_; 
v_sz_boxed_3852_ = lean_unbox_usize(v_sz_3849_);
lean_dec(v_sz_3849_);
v_i_boxed_3853_ = lean_unbox_usize(v_i_3850_);
lean_dec(v_i_3850_);
v_res_3854_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3(v_00_u03c4_3848_, v_sz_boxed_3852_, v_i_boxed_3853_, v_bs_3851_);
return v_res_3854_;
}
}
LEAN_EXPORT lean_object* l_List_splitBy_loop___at___00List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1_spec__1(lean_object* v_00_u03c4_3855_, lean_object* v_a_3856_, lean_object* v_a_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_){
_start:
{
lean_object* v___x_3860_; 
v___x_3860_ = l_List_splitBy_loop___at___00List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1_spec__1___redArg(v_a_3856_, v_a_3857_, v_a_3858_, v_a_3859_);
return v___x_3860_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0___redArg(size_t v_sz_3861_, size_t v_i_3862_, lean_object* v_bs_3863_){
_start:
{
uint8_t v___x_3864_; 
v___x_3864_ = lean_usize_dec_lt(v_i_3862_, v_sz_3861_);
if (v___x_3864_ == 0)
{
return v_bs_3863_;
}
else
{
lean_object* v_v_3865_; lean_object* v___x_3866_; lean_object* v_bs_x27_3867_; lean_object* v___x_3868_; size_t v___x_3869_; size_t v___x_3870_; lean_object* v___x_3871_; 
v_v_3865_ = lean_array_uget(v_bs_3863_, v_i_3862_);
v___x_3866_ = lean_unsigned_to_nat(0u);
v_bs_x27_3867_ = lean_array_uset(v_bs_3863_, v_i_3862_, v___x_3866_);
v___x_3868_ = l_Lean_Fmt_Doc_fillUsingSpace___redArg(v_v_3865_);
lean_dec(v_v_3865_);
v___x_3869_ = ((size_t)1ULL);
v___x_3870_ = lean_usize_add(v_i_3862_, v___x_3869_);
v___x_3871_ = lean_array_uset(v_bs_x27_3867_, v_i_3862_, v___x_3868_);
v_i_3862_ = v___x_3870_;
v_bs_3863_ = v___x_3871_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0___redArg___boxed(lean_object* v_sz_3873_, lean_object* v_i_3874_, lean_object* v_bs_3875_){
_start:
{
size_t v_sz_boxed_3876_; size_t v_i_boxed_3877_; lean_object* v_res_3878_; 
v_sz_boxed_3876_ = lean_unbox_usize(v_sz_3873_);
lean_dec(v_sz_3873_);
v_i_boxed_3877_ = lean_unbox_usize(v_i_3874_);
lean_dec(v_i_3874_);
v_res_3878_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0___redArg(v_sz_boxed_3876_, v_i_boxed_3877_, v_bs_3875_);
return v_res_3878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillSomeUsingSpace___redArg(lean_object* v_ds_3879_){
_start:
{
lean_object* v_fillGroups_3880_; lean_object* v___x_3881_; size_t v_sz_3882_; size_t v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; 
v_fillGroups_3880_ = l_Lean_Fmt_Doc_splitFillGroups___redArg(v_ds_3879_);
v___x_3881_ = lean_obj_once(&l_Lean_Fmt_Doc_nl___closed__0, &l_Lean_Fmt_Doc_nl___closed__0_once, _init_l_Lean_Fmt_Doc_nl___closed__0);
v_sz_3882_ = lean_array_size(v_fillGroups_3880_);
v___x_3883_ = ((size_t)0ULL);
v___x_3884_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0___redArg(v_sz_3882_, v___x_3883_, v_fillGroups_3880_);
v___x_3885_ = l_Lean_Fmt_Doc_joinUsing___redArg(v___x_3881_, v___x_3884_);
return v___x_3885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillSomeUsingSpace(lean_object* v_00_u03c4_3886_, lean_object* v_ds_3887_){
_start:
{
lean_object* v___x_3888_; 
v___x_3888_ = l_Lean_Fmt_Doc_fillSomeUsingSpace___redArg(v_ds_3887_);
return v___x_3888_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0(lean_object* v_00_u03c4_3889_, size_t v_sz_3890_, size_t v_i_3891_, lean_object* v_bs_3892_){
_start:
{
lean_object* v___x_3893_; 
v___x_3893_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0___redArg(v_sz_3890_, v_i_3891_, v_bs_3892_);
return v___x_3893_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0___boxed(lean_object* v_00_u03c4_3894_, lean_object* v_sz_3895_, lean_object* v_i_3896_, lean_object* v_bs_3897_){
_start:
{
size_t v_sz_boxed_3898_; size_t v_i_boxed_3899_; lean_object* v_res_3900_; 
v_sz_boxed_3898_ = lean_unbox_usize(v_sz_3895_);
lean_dec(v_sz_3895_);
v_i_boxed_3899_ = lean_unbox_usize(v_i_3896_);
lean_dec(v_i_3896_);
v_res_3900_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0(v_00_u03c4_3894_, v_sz_boxed_3898_, v_i_boxed_3899_, v_bs_3897_);
return v_res_3900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg___lam__0(lean_object* v___x_3901_, lean_object* v_ds_3902_, lean_object* v_i_3903_){
_start:
{
lean_object* v___x_3904_; uint8_t v_allowFill_3905_; 
v___x_3904_ = lean_array_get_borrowed(v___x_3901_, v_ds_3902_, v_i_3903_);
v_allowFill_3905_ = lean_ctor_get_uint8(v___x_3904_, sizeof(void*)*1);
if (v_allowFill_3905_ == 0)
{
lean_object* v___x_3906_; 
v___x_3906_ = lean_box(0);
return v___x_3906_;
}
else
{
lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; uint8_t v_allowFill_3910_; 
v___x_3907_ = lean_unsigned_to_nat(1u);
v___x_3908_ = lean_nat_add(v_i_3903_, v___x_3907_);
v___x_3909_ = lean_array_get_borrowed(v___x_3901_, v_ds_3902_, v___x_3908_);
lean_dec(v___x_3908_);
v_allowFill_3910_ = lean_ctor_get_uint8(v___x_3909_, sizeof(void*)*1);
if (v_allowFill_3910_ == 0)
{
lean_object* v___x_3911_; 
v___x_3911_ = lean_box(0);
return v___x_3911_;
}
else
{
lean_object* v___x_3912_; 
v___x_3912_ = lean_obj_once(&l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg___lam__0___closed__0, &l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg___lam__0___closed__0_once, _init_l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg___lam__0___closed__0);
return v___x_3912_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg___lam__0___boxed(lean_object* v___x_3913_, lean_object* v_ds_3914_, lean_object* v_i_3915_){
_start:
{
lean_object* v_res_3916_; 
v_res_3916_ = l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg___lam__0(v___x_3913_, v_ds_3914_, v_i_3915_);
lean_dec(v_i_3915_);
lean_dec_ref(v_ds_3914_);
lean_dec_ref(v___x_3913_);
return v_res_3916_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg___closed__0(void){
_start:
{
lean_object* v___x_3917_; lean_object* v___x_3918_; 
v___x_3917_ = lean_box(0);
v___x_3918_ = l_Lean_Fmt_instInhabitedFillable_default___redArg(v___x_3917_);
return v___x_3918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg(lean_object* v_ds_3919_, lean_object* v_wrap_3920_){
_start:
{
lean_object* v___x_3921_; lean_object* v___f_3922_; size_t v_sz_3923_; size_t v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; 
v___x_3921_ = lean_obj_once(&l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg___closed__0, &l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg___closed__0_once, _init_l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg___closed__0);
lean_inc_ref(v_ds_3919_);
v___f_3922_ = lean_alloc_closure((void*)(l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3922_, 0, v___x_3921_);
lean_closure_set(v___f_3922_, 1, v_ds_3919_);
v_sz_3923_ = lean_array_size(v_ds_3919_);
v___x_3924_ = ((size_t)0ULL);
v___x_3925_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0___redArg(v_sz_3923_, v___x_3924_, v_ds_3919_);
v___x_3926_ = l_Lean_Fmt_Doc_fillWrappingWith___redArg(v___x_3925_, v_wrap_3920_, v___f_3922_);
return v___x_3926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping(lean_object* v_00_u03c4_3927_, lean_object* v_ds_3928_, lean_object* v_wrap_3929_){
_start:
{
lean_object* v___x_3930_; 
v___x_3930_ = l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg(v_ds_3928_, v_wrap_3929_);
return v___x_3930_;
}
}
static size_t _init_l_Lean_Fmt_instInhabitedPtrKey_default___redArg___closed__0(void){
_start:
{
lean_object* v___x_3931_; size_t v___x_3932_; 
v___x_3931_ = lean_unsigned_to_nat(0u);
v___x_3932_ = lean_usize_of_nat(v___x_3931_);
return v___x_3932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedPtrKey_default___redArg(lean_object* v_inst_3933_){
_start:
{
size_t v___x_3934_; lean_object* v___x_3935_; 
v___x_3934_ = lean_usize_once(&l_Lean_Fmt_instInhabitedPtrKey_default___redArg___closed__0, &l_Lean_Fmt_instInhabitedPtrKey_default___redArg___closed__0_once, _init_l_Lean_Fmt_instInhabitedPtrKey_default___redArg___closed__0);
v___x_3935_ = lean_alloc_ctor(0, 1, sizeof(size_t)*1);
lean_ctor_set(v___x_3935_, 0, v_inst_3933_);
lean_ctor_set_usize(v___x_3935_, 1, v___x_3934_);
return v___x_3935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedPtrKey_default(lean_object* v_00_u03b1_3936_, lean_object* v_inst_3937_){
_start:
{
lean_object* v___x_3938_; 
v___x_3938_ = l_Lean_Fmt_instInhabitedPtrKey_default___redArg(v_inst_3937_);
return v___x_3938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedPtrKey___redArg(lean_object* v_inst_3939_){
_start:
{
lean_object* v___x_3940_; 
v___x_3940_ = l_Lean_Fmt_instInhabitedPtrKey_default___redArg(v_inst_3939_);
return v___x_3940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedPtrKey(lean_object* v_a_3941_, lean_object* v_inst_3942_){
_start:
{
lean_object* v___x_3943_; 
v___x_3943_ = l_Lean_Fmt_instInhabitedPtrKey_default___redArg(v_inst_3942_);
return v___x_3943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_PtrKey_ofKey___redArg(lean_object* v_v_3944_){
_start:
{
size_t v___x_3945_; lean_object* v___x_3946_; 
v___x_3945_ = lean_ptr_addr(v_v_3944_);
v___x_3946_ = lean_alloc_ctor(0, 1, sizeof(size_t)*1);
lean_ctor_set(v___x_3946_, 0, v_v_3944_);
lean_ctor_set_usize(v___x_3946_, 1, v___x_3945_);
return v___x_3946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_PtrKey_ofKey(lean_object* v_00_u03b1_3947_, lean_object* v_v_3948_){
_start:
{
lean_object* v___x_3949_; 
v___x_3949_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_v_3948_);
return v___x_3949_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqPtrKey___redArg___lam__0(lean_object* v_v1_3950_, lean_object* v_v2_3951_){
_start:
{
size_t v_ptr_3952_; size_t v_ptr_3953_; uint8_t v___x_3954_; 
v_ptr_3952_ = lean_ctor_get_usize(v_v1_3950_, 1);
v_ptr_3953_ = lean_ctor_get_usize(v_v2_3951_, 1);
v___x_3954_ = lean_usize_dec_eq(v_ptr_3952_, v_ptr_3953_);
return v___x_3954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqPtrKey___redArg___lam__0___boxed(lean_object* v_v1_3955_, lean_object* v_v2_3956_){
_start:
{
uint8_t v_res_3957_; lean_object* v_r_3958_; 
v_res_3957_ = l_Lean_Fmt_instBEqPtrKey___redArg___lam__0(v_v1_3955_, v_v2_3956_);
lean_dec_ref(v_v2_3956_);
lean_dec_ref(v_v1_3955_);
v_r_3958_ = lean_box(v_res_3957_);
return v_r_3958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqPtrKey___redArg(){
_start:
{
lean_object* v___f_3961_; 
v___f_3961_ = ((lean_object*)(l_Lean_Fmt_instBEqPtrKey___redArg___closed__0));
return v___f_3961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqPtrKey___redArg___boxed(lean_object* v___dummy_3962_){
_start:
{
lean_object* v_res_3963_; 
v_res_3963_ = l_Lean_Fmt_instBEqPtrKey___redArg();
return v_res_3963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqPtrKey(lean_object* v_00_u03b1_3964_){
_start:
{
lean_object* v___f_3965_; 
v___f_3965_ = ((lean_object*)(l_Lean_Fmt_instBEqPtrKey___redArg___closed__0));
return v___f_3965_;
}
}
LEAN_EXPORT uint64_t l_Lean_Fmt_instHashablePtrKey___redArg___lam__0(lean_object* v_v_3966_){
_start:
{
size_t v_ptr_3967_; uint64_t v___x_3968_; 
v_ptr_3967_ = lean_ctor_get_usize(v_v_3966_, 1);
v___x_3968_ = lean_usize_to_uint64(v_ptr_3967_);
return v___x_3968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashablePtrKey___redArg___lam__0___boxed(lean_object* v_v_3969_){
_start:
{
uint64_t v_res_3970_; lean_object* v_r_3971_; 
v_res_3970_ = l_Lean_Fmt_instHashablePtrKey___redArg___lam__0(v_v_3969_);
lean_dec_ref(v_v_3969_);
v_r_3971_ = lean_box_uint64(v_res_3970_);
return v_r_3971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashablePtrKey___redArg(){
_start:
{
lean_object* v___f_3974_; 
v___f_3974_ = ((lean_object*)(l_Lean_Fmt_instHashablePtrKey___redArg___closed__0));
return v___f_3974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashablePtrKey___redArg___boxed(lean_object* v___dummy_3975_){
_start:
{
lean_object* v_res_3976_; 
v_res_3976_ = l_Lean_Fmt_instHashablePtrKey___redArg();
return v_res_3976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashablePtrKey(lean_object* v_00_u03b1_3977_){
_start:
{
lean_object* v___f_3978_; 
v___f_3978_ = ((lean_object*)(l_Lean_Fmt_instHashablePtrKey___redArg___closed__0));
return v___f_3978_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqBEqCacheKey_beq___redArg(lean_object* v_x_3979_, lean_object* v_x_3980_){
_start:
{
lean_object* v_aPtr_3981_; lean_object* v_aPtr_3982_; lean_object* v_bPtr_3983_; lean_object* v_bPtr_3984_; size_t v_ptr_3985_; size_t v_ptr_3986_; uint8_t v___x_3987_; 
v_aPtr_3981_ = lean_ctor_get(v_x_3979_, 0);
v_aPtr_3982_ = lean_ctor_get(v_x_3980_, 0);
v_bPtr_3983_ = lean_ctor_get(v_x_3979_, 1);
v_bPtr_3984_ = lean_ctor_get(v_x_3980_, 1);
v_ptr_3985_ = lean_ctor_get_usize(v_aPtr_3981_, 1);
v_ptr_3986_ = lean_ctor_get_usize(v_aPtr_3982_, 1);
v___x_3987_ = lean_usize_dec_eq(v_ptr_3985_, v_ptr_3986_);
if (v___x_3987_ == 0)
{
return v___x_3987_;
}
else
{
size_t v_ptr_3988_; size_t v_ptr_3989_; uint8_t v___x_3990_; 
v_ptr_3988_ = lean_ctor_get_usize(v_bPtr_3983_, 1);
v_ptr_3989_ = lean_ctor_get_usize(v_bPtr_3984_, 1);
v___x_3990_ = lean_usize_dec_eq(v_ptr_3988_, v_ptr_3989_);
return v___x_3990_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqBEqCacheKey_beq___redArg___boxed(lean_object* v_x_3991_, lean_object* v_x_3992_){
_start:
{
uint8_t v_res_3993_; lean_object* v_r_3994_; 
v_res_3993_ = l_Lean_Fmt_instBEqBEqCacheKey_beq___redArg(v_x_3991_, v_x_3992_);
lean_dec_ref(v_x_3992_);
lean_dec_ref(v_x_3991_);
v_r_3994_ = lean_box(v_res_3993_);
return v_r_3994_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqBEqCacheKey_beq(lean_object* v_00_u03c4_3995_, lean_object* v_inst_3996_, lean_object* v_x_3997_, lean_object* v_x_3998_){
_start:
{
uint8_t v___x_3999_; 
v___x_3999_ = l_Lean_Fmt_instBEqBEqCacheKey_beq___redArg(v_x_3997_, v_x_3998_);
return v___x_3999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqBEqCacheKey_beq___boxed(lean_object* v_00_u03c4_4000_, lean_object* v_inst_4001_, lean_object* v_x_4002_, lean_object* v_x_4003_){
_start:
{
uint8_t v_res_4004_; lean_object* v_r_4005_; 
v_res_4004_ = l_Lean_Fmt_instBEqBEqCacheKey_beq(v_00_u03c4_4000_, v_inst_4001_, v_x_4002_, v_x_4003_);
lean_dec_ref(v_x_4003_);
lean_dec_ref(v_x_4002_);
lean_dec_ref(v_inst_4001_);
v_r_4005_ = lean_box(v_res_4004_);
return v_r_4005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqBEqCacheKey___redArg(lean_object* v_inst_4006_){
_start:
{
lean_object* v___x_4007_; 
v___x_4007_ = lean_alloc_closure((void*)(l_Lean_Fmt_instBEqBEqCacheKey_beq___boxed), 4, 2);
lean_closure_set(v___x_4007_, 0, lean_box(0));
lean_closure_set(v___x_4007_, 1, v_inst_4006_);
return v___x_4007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqBEqCacheKey(lean_object* v_00_u03c4_4008_, lean_object* v_inst_4009_){
_start:
{
lean_object* v___x_4010_; 
v___x_4010_ = lean_alloc_closure((void*)(l_Lean_Fmt_instBEqBEqCacheKey_beq___boxed), 4, 2);
lean_closure_set(v___x_4010_, 0, lean_box(0));
lean_closure_set(v___x_4010_, 1, v_inst_4009_);
return v___x_4010_;
}
}
LEAN_EXPORT uint64_t l_Lean_Fmt_instHashableBEqCacheKey_hash___redArg(lean_object* v_x_4011_){
_start:
{
lean_object* v_aPtr_4012_; lean_object* v_bPtr_4013_; size_t v_ptr_4014_; size_t v_ptr_4015_; uint64_t v___x_4016_; uint64_t v___x_4017_; uint64_t v___x_4018_; uint64_t v___x_4019_; uint64_t v___x_4020_; 
v_aPtr_4012_ = lean_ctor_get(v_x_4011_, 0);
v_bPtr_4013_ = lean_ctor_get(v_x_4011_, 1);
v_ptr_4014_ = lean_ctor_get_usize(v_aPtr_4012_, 1);
v_ptr_4015_ = lean_ctor_get_usize(v_bPtr_4013_, 1);
v___x_4016_ = 0ULL;
v___x_4017_ = lean_usize_to_uint64(v_ptr_4014_);
v___x_4018_ = lean_uint64_mix_hash(v___x_4016_, v___x_4017_);
v___x_4019_ = lean_usize_to_uint64(v_ptr_4015_);
v___x_4020_ = lean_uint64_mix_hash(v___x_4018_, v___x_4019_);
return v___x_4020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableBEqCacheKey_hash___redArg___boxed(lean_object* v_x_4021_){
_start:
{
uint64_t v_res_4022_; lean_object* v_r_4023_; 
v_res_4022_ = l_Lean_Fmt_instHashableBEqCacheKey_hash___redArg(v_x_4021_);
lean_dec_ref(v_x_4021_);
v_r_4023_ = lean_box_uint64(v_res_4022_);
return v_r_4023_;
}
}
LEAN_EXPORT uint64_t l_Lean_Fmt_instHashableBEqCacheKey_hash(lean_object* v_00_u03c4_4024_, lean_object* v_inst_4025_, lean_object* v_x_4026_){
_start:
{
uint64_t v___x_4027_; 
v___x_4027_ = l_Lean_Fmt_instHashableBEqCacheKey_hash___redArg(v_x_4026_);
return v___x_4027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableBEqCacheKey_hash___boxed(lean_object* v_00_u03c4_4028_, lean_object* v_inst_4029_, lean_object* v_x_4030_){
_start:
{
uint64_t v_res_4031_; lean_object* v_r_4032_; 
v_res_4031_ = l_Lean_Fmt_instHashableBEqCacheKey_hash(v_00_u03c4_4028_, v_inst_4029_, v_x_4030_);
lean_dec_ref(v_x_4030_);
lean_dec_ref(v_inst_4029_);
v_r_4032_ = lean_box_uint64(v_res_4031_);
return v_r_4032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableBEqCacheKey___redArg(lean_object* v_inst_4033_){
_start:
{
lean_object* v___x_4034_; 
v___x_4034_ = lean_alloc_closure((void*)(l_Lean_Fmt_instHashableBEqCacheKey_hash___boxed), 3, 2);
lean_closure_set(v___x_4034_, 0, lean_box(0));
lean_closure_set(v___x_4034_, 1, v_inst_4033_);
return v___x_4034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableBEqCacheKey(lean_object* v_00_u03c4_4035_, lean_object* v_inst_4036_){
_start:
{
lean_object* v___x_4037_; 
v___x_4037_ = lean_alloc_closure((void*)(l_Lean_Fmt_instHashableBEqCacheKey_hash___boxed), 3, 2);
lean_closure_set(v___x_4037_, 0, lean_box(0));
lean_closure_set(v___x_4037_, 1, v_inst_4036_);
return v___x_4037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized_unsafe__1___redArg(lean_object* v_a_4038_){
_start:
{
lean_object* v___x_4039_; 
v___x_4039_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_a_4038_);
return v___x_4039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized_unsafe__1(lean_object* v_00_u03c4_4040_, lean_object* v_a_4041_){
_start:
{
lean_object* v___x_4042_; 
v___x_4042_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_a_4041_);
return v___x_4042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized_unsafe__4___redArg(lean_object* v_b_4043_){
_start:
{
lean_object* v___x_4044_; 
v___x_4044_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_b_4043_);
return v___x_4044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized_unsafe__4(lean_object* v_00_u03c4_4045_, lean_object* v_b_4046_){
_start:
{
lean_object* v___x_4047_; 
v___x_4047_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_b_4046_);
return v___x_4047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_go___redArg(lean_object* v_inst_4048_, lean_object* v_inst_4049_, lean_object* v_a_4050_, lean_object* v_b_4051_, lean_object* v_a_4052_){
_start:
{
lean_object* v___y_4054_; lean_object* v_da1_4059_; lean_object* v_da2_4060_; lean_object* v_db1_4061_; lean_object* v_db2_4062_; lean_object* v___y_4063_; lean_object* v_sa_4070_; lean_object* v_sb_4071_; lean_object* v___y_4072_; 
switch(lean_obj_tag(v_a_4050_))
{
case 0:
{
lean_dec_ref(v_inst_4049_);
lean_dec_ref(v_inst_4048_);
if (lean_obj_tag(v_b_4051_) == 0)
{
uint8_t v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; 
v___x_4080_ = 1;
v___x_4081_ = lean_box(v___x_4080_);
v___x_4082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4082_, 0, v___x_4081_);
lean_ctor_set(v___x_4082_, 1, v_a_4052_);
return v___x_4082_;
}
else
{
lean_dec(v_b_4051_);
v___y_4054_ = v_a_4052_;
goto v___jp_4053_;
}
}
case 1:
{
lean_dec_ref(v_inst_4049_);
lean_dec_ref(v_inst_4048_);
if (lean_obj_tag(v_b_4051_) == 1)
{
lean_object* v_f_4083_; lean_object* v_f_4084_; 
v_f_4083_ = lean_ctor_get(v_a_4050_, 1);
lean_inc_ref(v_f_4083_);
lean_dec_ref_known(v_a_4050_, 2);
v_f_4084_ = lean_ctor_get(v_b_4051_, 1);
lean_inc_ref(v_f_4084_);
lean_dec_ref_known(v_b_4051_, 2);
v_sa_4070_ = v_f_4083_;
v_sb_4071_ = v_f_4084_;
v___y_4072_ = v_a_4052_;
goto v___jp_4069_;
}
else
{
lean_dec_ref_known(v_a_4050_, 2);
lean_dec(v_b_4051_);
v___y_4054_ = v_a_4052_;
goto v___jp_4053_;
}
}
case 2:
{
lean_dec_ref(v_inst_4049_);
lean_dec_ref(v_inst_4048_);
if (lean_obj_tag(v_b_4051_) == 2)
{
lean_object* v_s_4085_; lean_object* v_s_4086_; 
v_s_4085_ = lean_ctor_get(v_a_4050_, 1);
lean_inc_ref(v_s_4085_);
lean_dec_ref_known(v_a_4050_, 2);
v_s_4086_ = lean_ctor_get(v_b_4051_, 1);
lean_inc_ref(v_s_4086_);
lean_dec_ref_known(v_b_4051_, 2);
v_sa_4070_ = v_s_4085_;
v_sb_4071_ = v_s_4086_;
v___y_4072_ = v_a_4052_;
goto v___jp_4069_;
}
else
{
lean_dec_ref_known(v_a_4050_, 2);
lean_dec(v_b_4051_);
v___y_4054_ = v_a_4052_;
goto v___jp_4053_;
}
}
case 3:
{
if (lean_obj_tag(v_b_4051_) == 3)
{
lean_object* v_id_4087_; lean_object* v_d_4088_; lean_object* v_id_4089_; lean_object* v_d_4090_; uint8_t v___x_4091_; 
v_id_4087_ = lean_ctor_get(v_a_4050_, 1);
lean_inc(v_id_4087_);
v_d_4088_ = lean_ctor_get(v_a_4050_, 2);
lean_inc(v_d_4088_);
lean_dec_ref_known(v_a_4050_, 3);
v_id_4089_ = lean_ctor_get(v_b_4051_, 1);
lean_inc(v_id_4089_);
v_d_4090_ = lean_ctor_get(v_b_4051_, 2);
lean_inc(v_d_4090_);
lean_dec_ref_known(v_b_4051_, 3);
v___x_4091_ = lean_nat_dec_eq(v_id_4087_, v_id_4089_);
lean_dec(v_id_4089_);
lean_dec(v_id_4087_);
if (v___x_4091_ == 0)
{
lean_object* v___x_4092_; lean_object* v___x_4093_; 
lean_dec(v_d_4090_);
lean_dec(v_d_4088_);
lean_dec_ref(v_inst_4049_);
lean_dec_ref(v_inst_4048_);
v___x_4092_ = lean_box(v___x_4091_);
v___x_4093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4093_, 0, v___x_4092_);
lean_ctor_set(v___x_4093_, 1, v_a_4052_);
return v___x_4093_;
}
else
{
lean_object* v___x_4094_; 
v___x_4094_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4048_, v_inst_4049_, v_d_4088_, v_d_4090_, v_a_4052_);
return v___x_4094_;
}
}
else
{
lean_dec_ref_known(v_a_4050_, 3);
lean_dec(v_b_4051_);
lean_dec_ref(v_inst_4049_);
lean_dec_ref(v_inst_4048_);
v___y_4054_ = v_a_4052_;
goto v___jp_4053_;
}
}
case 4:
{
if (lean_obj_tag(v_b_4051_) == 4)
{
lean_object* v_d_4095_; lean_object* v_d_4096_; lean_object* v___x_4097_; 
v_d_4095_ = lean_ctor_get(v_a_4050_, 1);
lean_inc(v_d_4095_);
lean_dec_ref_known(v_a_4050_, 2);
v_d_4096_ = lean_ctor_get(v_b_4051_, 1);
lean_inc(v_d_4096_);
lean_dec_ref_known(v_b_4051_, 2);
v___x_4097_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4048_, v_inst_4049_, v_d_4095_, v_d_4096_, v_a_4052_);
return v___x_4097_;
}
else
{
lean_dec_ref_known(v_a_4050_, 2);
lean_dec(v_b_4051_);
lean_dec_ref(v_inst_4049_);
lean_dec_ref(v_inst_4048_);
v___y_4054_ = v_a_4052_;
goto v___jp_4053_;
}
}
case 5:
{
if (lean_obj_tag(v_b_4051_) == 5)
{
lean_object* v_d_4098_; lean_object* v_d_4099_; lean_object* v___x_4100_; 
v_d_4098_ = lean_ctor_get(v_a_4050_, 1);
lean_inc(v_d_4098_);
lean_dec_ref_known(v_a_4050_, 2);
v_d_4099_ = lean_ctor_get(v_b_4051_, 1);
lean_inc(v_d_4099_);
lean_dec_ref_known(v_b_4051_, 2);
v___x_4100_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4048_, v_inst_4049_, v_d_4098_, v_d_4099_, v_a_4052_);
return v___x_4100_;
}
else
{
lean_dec_ref_known(v_a_4050_, 2);
lean_dec(v_b_4051_);
lean_dec_ref(v_inst_4049_);
lean_dec_ref(v_inst_4048_);
v___y_4054_ = v_a_4052_;
goto v___jp_4053_;
}
}
case 6:
{
if (lean_obj_tag(v_b_4051_) == 6)
{
lean_object* v_n_4101_; uint8_t v_isCumulative_4102_; lean_object* v_d_4103_; lean_object* v_n_4104_; uint8_t v_isCumulative_4105_; lean_object* v_d_4106_; uint8_t v___x_4107_; 
v_n_4101_ = lean_ctor_get(v_a_4050_, 1);
lean_inc(v_n_4101_);
v_isCumulative_4102_ = lean_ctor_get_uint8(v_a_4050_, sizeof(void*)*3 + 7);
v_d_4103_ = lean_ctor_get(v_a_4050_, 2);
lean_inc(v_d_4103_);
lean_dec_ref_known(v_a_4050_, 3);
v_n_4104_ = lean_ctor_get(v_b_4051_, 1);
lean_inc(v_n_4104_);
v_isCumulative_4105_ = lean_ctor_get_uint8(v_b_4051_, sizeof(void*)*3 + 7);
v_d_4106_ = lean_ctor_get(v_b_4051_, 2);
lean_inc(v_d_4106_);
lean_dec_ref_known(v_b_4051_, 3);
v___x_4107_ = lean_nat_dec_eq(v_n_4101_, v_n_4104_);
lean_dec(v_n_4104_);
lean_dec(v_n_4101_);
if (v___x_4107_ == 0)
{
lean_dec(v_d_4106_);
lean_dec(v_d_4103_);
lean_dec_ref(v_inst_4049_);
lean_dec_ref(v_inst_4048_);
goto v___jp_4076_;
}
else
{
if (v_isCumulative_4105_ == 0)
{
if (v_isCumulative_4102_ == 0)
{
lean_object* v___x_4108_; 
v___x_4108_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4048_, v_inst_4049_, v_d_4103_, v_d_4106_, v_a_4052_);
return v___x_4108_;
}
else
{
lean_dec(v_d_4106_);
lean_dec(v_d_4103_);
lean_dec_ref(v_inst_4049_);
lean_dec_ref(v_inst_4048_);
goto v___jp_4076_;
}
}
else
{
if (v_isCumulative_4102_ == 0)
{
lean_dec(v_d_4106_);
lean_dec(v_d_4103_);
lean_dec_ref(v_inst_4049_);
lean_dec_ref(v_inst_4048_);
goto v___jp_4076_;
}
else
{
lean_object* v___x_4109_; 
v___x_4109_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4048_, v_inst_4049_, v_d_4103_, v_d_4106_, v_a_4052_);
return v___x_4109_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_4050_, 3);
lean_dec(v_b_4051_);
lean_dec_ref(v_inst_4049_);
lean_dec_ref(v_inst_4048_);
v___y_4054_ = v_a_4052_;
goto v___jp_4053_;
}
}
case 7:
{
if (lean_obj_tag(v_b_4051_) == 7)
{
lean_object* v_d_4110_; lean_object* v_d_4111_; lean_object* v___x_4112_; 
v_d_4110_ = lean_ctor_get(v_a_4050_, 1);
lean_inc(v_d_4110_);
lean_dec_ref_known(v_a_4050_, 2);
v_d_4111_ = lean_ctor_get(v_b_4051_, 1);
lean_inc(v_d_4111_);
lean_dec_ref_known(v_b_4051_, 2);
v___x_4112_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4048_, v_inst_4049_, v_d_4110_, v_d_4111_, v_a_4052_);
return v___x_4112_;
}
else
{
lean_dec_ref_known(v_a_4050_, 2);
lean_dec(v_b_4051_);
lean_dec_ref(v_inst_4049_);
lean_dec_ref(v_inst_4048_);
v___y_4054_ = v_a_4052_;
goto v___jp_4053_;
}
}
case 8:
{
if (lean_obj_tag(v_b_4051_) == 8)
{
uint8_t v_onlyNonCumulative_4113_; 
v_onlyNonCumulative_4113_ = lean_ctor_get_uint8(v_b_4051_, sizeof(void*)*2 + 7);
if (v_onlyNonCumulative_4113_ == 0)
{
uint8_t v_onlyNonCumulative_4114_; 
v_onlyNonCumulative_4114_ = lean_ctor_get_uint8(v_a_4050_, sizeof(void*)*2 + 7);
if (v_onlyNonCumulative_4114_ == 0)
{
lean_object* v_d_4115_; lean_object* v_d_4116_; lean_object* v___x_4117_; 
v_d_4115_ = lean_ctor_get(v_a_4050_, 1);
lean_inc(v_d_4115_);
lean_dec_ref_known(v_a_4050_, 2);
v_d_4116_ = lean_ctor_get(v_b_4051_, 1);
lean_inc(v_d_4116_);
lean_dec_ref_known(v_b_4051_, 2);
v___x_4117_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4048_, v_inst_4049_, v_d_4115_, v_d_4116_, v_a_4052_);
return v___x_4117_;
}
else
{
lean_object* v___x_4118_; lean_object* v___x_4119_; 
lean_dec_ref_known(v_b_4051_, 2);
lean_dec_ref_known(v_a_4050_, 2);
lean_dec_ref(v_inst_4049_);
lean_dec_ref(v_inst_4048_);
v___x_4118_ = lean_box(v_onlyNonCumulative_4113_);
v___x_4119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4119_, 0, v___x_4118_);
lean_ctor_set(v___x_4119_, 1, v_a_4052_);
return v___x_4119_;
}
}
else
{
uint8_t v_onlyNonCumulative_4120_; 
v_onlyNonCumulative_4120_ = lean_ctor_get_uint8(v_a_4050_, sizeof(void*)*2 + 7);
if (v_onlyNonCumulative_4120_ == 0)
{
lean_object* v___x_4121_; lean_object* v___x_4122_; 
lean_dec_ref_known(v_b_4051_, 2);
lean_dec_ref_known(v_a_4050_, 2);
lean_dec_ref(v_inst_4049_);
lean_dec_ref(v_inst_4048_);
v___x_4121_ = lean_box(v_onlyNonCumulative_4120_);
v___x_4122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4122_, 0, v___x_4121_);
lean_ctor_set(v___x_4122_, 1, v_a_4052_);
return v___x_4122_;
}
else
{
lean_object* v_d_4123_; lean_object* v_d_4124_; lean_object* v___x_4125_; 
v_d_4123_ = lean_ctor_get(v_a_4050_, 1);
lean_inc(v_d_4123_);
lean_dec_ref_known(v_a_4050_, 2);
v_d_4124_ = lean_ctor_get(v_b_4051_, 1);
lean_inc(v_d_4124_);
lean_dec_ref_known(v_b_4051_, 2);
v___x_4125_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4048_, v_inst_4049_, v_d_4123_, v_d_4124_, v_a_4052_);
return v___x_4125_;
}
}
}
else
{
lean_dec_ref_known(v_a_4050_, 2);
lean_dec(v_b_4051_);
lean_dec_ref(v_inst_4049_);
lean_dec_ref(v_inst_4048_);
v___y_4054_ = v_a_4052_;
goto v___jp_4053_;
}
}
case 9:
{
if (lean_obj_tag(v_b_4051_) == 9)
{
lean_object* v_d_4126_; lean_object* v_d_4127_; lean_object* v___x_4128_; 
v_d_4126_ = lean_ctor_get(v_a_4050_, 1);
lean_inc(v_d_4126_);
lean_dec_ref_known(v_a_4050_, 2);
v_d_4127_ = lean_ctor_get(v_b_4051_, 1);
lean_inc(v_d_4127_);
lean_dec_ref_known(v_b_4051_, 2);
v___x_4128_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4048_, v_inst_4049_, v_d_4126_, v_d_4127_, v_a_4052_);
return v___x_4128_;
}
else
{
lean_dec_ref_known(v_a_4050_, 2);
lean_dec(v_b_4051_);
lean_dec_ref(v_inst_4049_);
lean_dec_ref(v_inst_4048_);
v___y_4054_ = v_a_4052_;
goto v___jp_4053_;
}
}
case 10:
{
if (lean_obj_tag(v_b_4051_) == 10)
{
lean_object* v_d_4129_; lean_object* v_d_4130_; lean_object* v___x_4131_; 
v_d_4129_ = lean_ctor_get(v_a_4050_, 1);
lean_inc(v_d_4129_);
lean_dec_ref_known(v_a_4050_, 2);
v_d_4130_ = lean_ctor_get(v_b_4051_, 1);
lean_inc(v_d_4130_);
lean_dec_ref_known(v_b_4051_, 2);
v___x_4131_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4048_, v_inst_4049_, v_d_4129_, v_d_4130_, v_a_4052_);
return v___x_4131_;
}
else
{
lean_dec_ref_known(v_a_4050_, 2);
lean_dec(v_b_4051_);
lean_dec_ref(v_inst_4049_);
lean_dec_ref(v_inst_4048_);
v___y_4054_ = v_a_4052_;
goto v___jp_4053_;
}
}
case 11:
{
if (lean_obj_tag(v_b_4051_) == 11)
{
lean_object* v_d_4132_; lean_object* v_d_4133_; lean_object* v___x_4134_; 
v_d_4132_ = lean_ctor_get(v_a_4050_, 1);
lean_inc(v_d_4132_);
lean_dec_ref_known(v_a_4050_, 2);
v_d_4133_ = lean_ctor_get(v_b_4051_, 1);
lean_inc(v_d_4133_);
lean_dec_ref_known(v_b_4051_, 2);
v___x_4134_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4048_, v_inst_4049_, v_d_4132_, v_d_4133_, v_a_4052_);
return v___x_4134_;
}
else
{
lean_dec_ref_known(v_a_4050_, 2);
lean_dec(v_b_4051_);
lean_dec_ref(v_inst_4049_);
lean_dec_ref(v_inst_4048_);
v___y_4054_ = v_a_4052_;
goto v___jp_4053_;
}
}
case 12:
{
if (lean_obj_tag(v_b_4051_) == 12)
{
lean_object* v_p_4135_; lean_object* v_p_4136_; lean_object* v_d_4137_; lean_object* v_d_4138_; lean_object* v_id_4139_; lean_object* v_id_4140_; lean_object* v___x_4142_; uint8_t v_isShared_4143_; uint8_t v_isSharedCheck_4150_; 
v_p_4135_ = lean_ctor_get(v_a_4050_, 1);
lean_inc_ref(v_p_4135_);
v_p_4136_ = lean_ctor_get(v_b_4051_, 1);
lean_inc_ref(v_p_4136_);
v_d_4137_ = lean_ctor_get(v_a_4050_, 2);
lean_inc(v_d_4137_);
lean_dec_ref_known(v_a_4050_, 3);
v_d_4138_ = lean_ctor_get(v_b_4051_, 2);
lean_inc(v_d_4138_);
lean_dec_ref_known(v_b_4051_, 3);
v_id_4139_ = lean_ctor_get(v_p_4135_, 1);
lean_inc(v_id_4139_);
lean_dec_ref(v_p_4135_);
v_id_4140_ = lean_ctor_get(v_p_4136_, 1);
v_isSharedCheck_4150_ = !lean_is_exclusive(v_p_4136_);
if (v_isSharedCheck_4150_ == 0)
{
lean_object* v_unused_4151_; 
v_unused_4151_ = lean_ctor_get(v_p_4136_, 0);
lean_dec(v_unused_4151_);
v___x_4142_ = v_p_4136_;
v_isShared_4143_ = v_isSharedCheck_4150_;
goto v_resetjp_4141_;
}
else
{
lean_inc(v_id_4140_);
lean_dec(v_p_4136_);
v___x_4142_ = lean_box(0);
v_isShared_4143_ = v_isSharedCheck_4150_;
goto v_resetjp_4141_;
}
v_resetjp_4141_:
{
uint8_t v___x_4144_; 
v___x_4144_ = lean_name_eq(v_id_4139_, v_id_4140_);
lean_dec(v_id_4140_);
lean_dec(v_id_4139_);
if (v___x_4144_ == 0)
{
lean_object* v___x_4145_; lean_object* v___x_4147_; 
lean_dec(v_d_4138_);
lean_dec(v_d_4137_);
lean_dec_ref(v_inst_4049_);
lean_dec_ref(v_inst_4048_);
v___x_4145_ = lean_box(v___x_4144_);
if (v_isShared_4143_ == 0)
{
lean_ctor_set(v___x_4142_, 1, v_a_4052_);
lean_ctor_set(v___x_4142_, 0, v___x_4145_);
v___x_4147_ = v___x_4142_;
goto v_reusejp_4146_;
}
else
{
lean_object* v_reuseFailAlloc_4148_; 
v_reuseFailAlloc_4148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4148_, 0, v___x_4145_);
lean_ctor_set(v_reuseFailAlloc_4148_, 1, v_a_4052_);
v___x_4147_ = v_reuseFailAlloc_4148_;
goto v_reusejp_4146_;
}
v_reusejp_4146_:
{
return v___x_4147_;
}
}
else
{
lean_object* v___x_4149_; 
lean_del_object(v___x_4142_);
v___x_4149_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4048_, v_inst_4049_, v_d_4137_, v_d_4138_, v_a_4052_);
return v___x_4149_;
}
}
}
else
{
lean_dec_ref_known(v_a_4050_, 3);
lean_dec(v_b_4051_);
lean_dec_ref(v_inst_4049_);
lean_dec_ref(v_inst_4048_);
v___y_4054_ = v_a_4052_;
goto v___jp_4053_;
}
}
case 13:
{
if (lean_obj_tag(v_b_4051_) == 13)
{
lean_object* v_cost_4152_; lean_object* v_d_4153_; lean_object* v_cost_4154_; lean_object* v_d_4155_; lean_object* v___x_4156_; uint8_t v___x_4157_; 
v_cost_4152_ = lean_ctor_get(v_a_4050_, 1);
lean_inc(v_cost_4152_);
v_d_4153_ = lean_ctor_get(v_a_4050_, 2);
lean_inc(v_d_4153_);
lean_dec_ref_known(v_a_4050_, 3);
v_cost_4154_ = lean_ctor_get(v_b_4051_, 1);
lean_inc(v_cost_4154_);
v_d_4155_ = lean_ctor_get(v_b_4051_, 2);
lean_inc(v_d_4155_);
lean_dec_ref_known(v_b_4051_, 3);
lean_inc_ref(v_inst_4048_);
v___x_4156_ = lean_apply_2(v_inst_4048_, v_cost_4152_, v_cost_4154_);
v___x_4157_ = lean_unbox(v___x_4156_);
if (v___x_4157_ == 0)
{
lean_object* v___x_4158_; 
lean_dec(v_d_4155_);
lean_dec(v_d_4153_);
lean_dec_ref(v_inst_4049_);
lean_dec_ref(v_inst_4048_);
v___x_4158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4158_, 0, v___x_4156_);
lean_ctor_set(v___x_4158_, 1, v_a_4052_);
return v___x_4158_;
}
else
{
lean_object* v___x_4159_; 
v___x_4159_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4048_, v_inst_4049_, v_d_4153_, v_d_4155_, v_a_4052_);
return v___x_4159_;
}
}
else
{
lean_dec_ref_known(v_a_4050_, 3);
lean_dec(v_b_4051_);
lean_dec_ref(v_inst_4049_);
lean_dec_ref(v_inst_4048_);
v___y_4054_ = v_a_4052_;
goto v___jp_4053_;
}
}
case 14:
{
if (lean_obj_tag(v_b_4051_) == 14)
{
lean_object* v_a_4160_; lean_object* v_b_4161_; lean_object* v_a_4162_; lean_object* v_b_4163_; 
v_a_4160_ = lean_ctor_get(v_a_4050_, 1);
lean_inc(v_a_4160_);
v_b_4161_ = lean_ctor_get(v_a_4050_, 2);
lean_inc(v_b_4161_);
lean_dec_ref_known(v_a_4050_, 3);
v_a_4162_ = lean_ctor_get(v_b_4051_, 1);
lean_inc(v_a_4162_);
v_b_4163_ = lean_ctor_get(v_b_4051_, 2);
lean_inc(v_b_4163_);
lean_dec_ref_known(v_b_4051_, 3);
v_da1_4059_ = v_a_4160_;
v_da2_4060_ = v_b_4161_;
v_db1_4061_ = v_a_4162_;
v_db2_4062_ = v_b_4163_;
v___y_4063_ = v_a_4052_;
goto v___jp_4058_;
}
else
{
lean_dec_ref_known(v_a_4050_, 3);
lean_dec(v_b_4051_);
lean_dec_ref(v_inst_4049_);
lean_dec_ref(v_inst_4048_);
v___y_4054_ = v_a_4052_;
goto v___jp_4053_;
}
}
default: 
{
if (lean_obj_tag(v_b_4051_) == 15)
{
lean_object* v_a_4164_; lean_object* v_b_4165_; lean_object* v_a_4166_; lean_object* v_b_4167_; 
v_a_4164_ = lean_ctor_get(v_a_4050_, 1);
lean_inc(v_a_4164_);
v_b_4165_ = lean_ctor_get(v_a_4050_, 2);
lean_inc(v_b_4165_);
lean_dec_ref_known(v_a_4050_, 3);
v_a_4166_ = lean_ctor_get(v_b_4051_, 1);
lean_inc(v_a_4166_);
v_b_4167_ = lean_ctor_get(v_b_4051_, 2);
lean_inc(v_b_4167_);
lean_dec_ref_known(v_b_4051_, 3);
v_da1_4059_ = v_a_4164_;
v_da2_4060_ = v_b_4165_;
v_db1_4061_ = v_a_4166_;
v_db2_4062_ = v_b_4167_;
v___y_4063_ = v_a_4052_;
goto v___jp_4058_;
}
else
{
lean_dec_ref_known(v_a_4050_, 3);
lean_dec(v_b_4051_);
lean_dec_ref(v_inst_4049_);
lean_dec_ref(v_inst_4048_);
v___y_4054_ = v_a_4052_;
goto v___jp_4053_;
}
}
}
v___jp_4053_:
{
uint8_t v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; 
v___x_4055_ = 0;
v___x_4056_ = lean_box(v___x_4055_);
v___x_4057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4057_, 0, v___x_4056_);
lean_ctor_set(v___x_4057_, 1, v___y_4054_);
return v___x_4057_;
}
v___jp_4058_:
{
lean_object* v___x_4064_; lean_object* v_fst_4065_; uint8_t v___x_4066_; 
lean_inc_ref(v_inst_4049_);
lean_inc_ref(v_inst_4048_);
v___x_4064_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4048_, v_inst_4049_, v_da1_4059_, v_db1_4061_, v___y_4063_);
v_fst_4065_ = lean_ctor_get(v___x_4064_, 0);
v___x_4066_ = lean_unbox(v_fst_4065_);
if (v___x_4066_ == 0)
{
lean_dec(v_db2_4062_);
lean_dec(v_da2_4060_);
lean_dec_ref(v_inst_4049_);
lean_dec_ref(v_inst_4048_);
return v___x_4064_;
}
else
{
lean_object* v_snd_4067_; lean_object* v___x_4068_; 
v_snd_4067_ = lean_ctor_get(v___x_4064_, 1);
lean_inc(v_snd_4067_);
lean_dec_ref(v___x_4064_);
v___x_4068_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4048_, v_inst_4049_, v_da2_4060_, v_db2_4062_, v_snd_4067_);
return v___x_4068_;
}
}
v___jp_4069_:
{
uint8_t v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; 
v___x_4073_ = lean_string_dec_eq(v_sa_4070_, v_sb_4071_);
lean_dec_ref(v_sb_4071_);
lean_dec_ref(v_sa_4070_);
v___x_4074_ = lean_box(v___x_4073_);
v___x_4075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4075_, 0, v___x_4074_);
lean_ctor_set(v___x_4075_, 1, v___y_4072_);
return v___x_4075_;
}
v___jp_4076_:
{
uint8_t v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; 
v___x_4077_ = 0;
v___x_4078_ = lean_box(v___x_4077_);
v___x_4079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4079_, 0, v___x_4078_);
lean_ctor_set(v___x_4079_, 1, v_a_4052_);
return v___x_4079_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(lean_object* v_inst_4168_, lean_object* v_inst_4169_, lean_object* v_a_4170_, lean_object* v_b_4171_, lean_object* v_a_4172_){
_start:
{
lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v_cacheKey_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; 
lean_inc(v_a_4170_);
v___x_4173_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_a_4170_);
lean_inc(v_b_4171_);
v___x_4174_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_b_4171_);
v_cacheKey_4175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_cacheKey_4175_, 0, v___x_4173_);
lean_ctor_set(v_cacheKey_4175_, 1, v___x_4174_);
lean_inc_ref(v_inst_4168_);
v___x_4176_ = lean_alloc_closure((void*)(l_Lean_Fmt_instBEqBEqCacheKey_beq___boxed), 4, 2);
lean_closure_set(v___x_4176_, 0, lean_box(0));
lean_closure_set(v___x_4176_, 1, v_inst_4168_);
lean_inc_ref(v_inst_4169_);
v___x_4177_ = lean_alloc_closure((void*)(l_Lean_Fmt_instHashableBEqCacheKey_hash___boxed), 3, 2);
lean_closure_set(v___x_4177_, 0, lean_box(0));
lean_closure_set(v___x_4177_, 1, v_inst_4169_);
lean_inc_ref(v_cacheKey_4175_);
lean_inc_ref(v___x_4177_);
lean_inc_ref(v___x_4176_);
v___x_4178_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_4176_, v___x_4177_, v_a_4172_, v_cacheKey_4175_);
if (lean_obj_tag(v___x_4178_) == 1)
{
lean_object* v_val_4179_; lean_object* v___x_4180_; 
lean_dec_ref(v___x_4177_);
lean_dec_ref(v___x_4176_);
lean_dec_ref_known(v_cacheKey_4175_, 2);
lean_dec(v_b_4171_);
lean_dec(v_a_4170_);
lean_dec_ref(v_inst_4169_);
lean_dec_ref(v_inst_4168_);
v_val_4179_ = lean_ctor_get(v___x_4178_, 0);
lean_inc(v_val_4179_);
lean_dec_ref_known(v___x_4178_, 1);
v___x_4180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4180_, 0, v_val_4179_);
lean_ctor_set(v___x_4180_, 1, v_a_4172_);
return v___x_4180_;
}
else
{
lean_object* v___x_4181_; lean_object* v_fst_4182_; lean_object* v_snd_4183_; lean_object* v___x_4185_; uint8_t v_isShared_4186_; uint8_t v_isSharedCheck_4191_; 
lean_dec(v___x_4178_);
v___x_4181_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_go___redArg(v_inst_4168_, v_inst_4169_, v_a_4170_, v_b_4171_, v_a_4172_);
v_fst_4182_ = lean_ctor_get(v___x_4181_, 0);
v_snd_4183_ = lean_ctor_get(v___x_4181_, 1);
v_isSharedCheck_4191_ = !lean_is_exclusive(v___x_4181_);
if (v_isSharedCheck_4191_ == 0)
{
v___x_4185_ = v___x_4181_;
v_isShared_4186_ = v_isSharedCheck_4191_;
goto v_resetjp_4184_;
}
else
{
lean_inc(v_snd_4183_);
lean_inc(v_fst_4182_);
lean_dec(v___x_4181_);
v___x_4185_ = lean_box(0);
v_isShared_4186_ = v_isSharedCheck_4191_;
goto v_resetjp_4184_;
}
v_resetjp_4184_:
{
lean_object* v___x_4187_; lean_object* v___x_4189_; 
lean_inc(v_fst_4182_);
v___x_4187_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_4176_, v___x_4177_, v_snd_4183_, v_cacheKey_4175_, v_fst_4182_);
if (v_isShared_4186_ == 0)
{
lean_ctor_set(v___x_4185_, 1, v___x_4187_);
v___x_4189_ = v___x_4185_;
goto v_reusejp_4188_;
}
else
{
lean_object* v_reuseFailAlloc_4190_; 
v_reuseFailAlloc_4190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4190_, 0, v_fst_4182_);
lean_ctor_set(v_reuseFailAlloc_4190_, 1, v___x_4187_);
v___x_4189_ = v_reuseFailAlloc_4190_;
goto v_reusejp_4188_;
}
v_reusejp_4188_:
{
return v___x_4189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized(lean_object* v_00_u03c4_4192_, lean_object* v_inst_4193_, lean_object* v_inst_4194_, lean_object* v_a_4195_, lean_object* v_b_4196_, lean_object* v_a_4197_){
_start:
{
lean_object* v___x_4198_; 
v___x_4198_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4193_, v_inst_4194_, v_a_4195_, v_b_4196_, v_a_4197_);
return v___x_4198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_go(lean_object* v_00_u03c4_4199_, lean_object* v_inst_4200_, lean_object* v_inst_4201_, lean_object* v_a_4202_, lean_object* v_b_4203_, lean_object* v_a_4204_){
_start:
{
lean_object* v___x_4205_; 
v___x_4205_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_go___redArg(v_inst_4200_, v_inst_4201_, v_a_4202_, v_b_4203_, v_a_4204_);
return v___x_4205_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_beq___redArg___closed__0(void){
_start:
{
lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; 
v___x_4206_ = lean_box(0);
v___x_4207_ = lean_unsigned_to_nat(16u);
v___x_4208_ = lean_mk_array(v___x_4207_, v___x_4206_);
return v___x_4208_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_beq___redArg___closed__1(void){
_start:
{
lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; 
v___x_4209_ = lean_obj_once(&l_Lean_Fmt_Doc_beq___redArg___closed__0, &l_Lean_Fmt_Doc_beq___redArg___closed__0_once, _init_l_Lean_Fmt_Doc_beq___redArg___closed__0);
v___x_4210_ = lean_unsigned_to_nat(0u);
v___x_4211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4211_, 0, v___x_4210_);
lean_ctor_set(v___x_4211_, 1, v___x_4209_);
return v___x_4211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_beq___redArg(lean_object* v_inst_4212_, lean_object* v_inst_4213_, lean_object* v_a_4214_, lean_object* v_b_4215_){
_start:
{
lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v_fst_4218_; 
v___x_4216_ = lean_obj_once(&l_Lean_Fmt_Doc_beq___redArg___closed__1, &l_Lean_Fmt_Doc_beq___redArg___closed__1_once, _init_l_Lean_Fmt_Doc_beq___redArg___closed__1);
v___x_4217_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4212_, v_inst_4213_, v_a_4214_, v_b_4215_, v___x_4216_);
v_fst_4218_ = lean_ctor_get(v___x_4217_, 0);
lean_inc(v_fst_4218_);
lean_dec_ref(v___x_4217_);
return v_fst_4218_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_beq(lean_object* v_00_u03c4_4219_, lean_object* v_inst_4220_, lean_object* v_inst_4221_, lean_object* v_a_4222_, lean_object* v_b_4223_){
_start:
{
lean_object* v___x_4224_; uint8_t v___x_4225_; 
v___x_4224_ = l_Lean_Fmt_Doc_beq___redArg(v_inst_4220_, v_inst_4221_, v_a_4222_, v_b_4223_);
v___x_4225_ = lean_unbox(v___x_4224_);
lean_dec(v___x_4224_);
return v___x_4225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_beq___boxed(lean_object* v_00_u03c4_4226_, lean_object* v_inst_4227_, lean_object* v_inst_4228_, lean_object* v_a_4229_, lean_object* v_b_4230_){
_start:
{
uint8_t v_res_4231_; lean_object* v_r_4232_; 
v_res_4231_ = l_Lean_Fmt_Doc_beq(v_00_u03c4_4226_, v_inst_4227_, v_inst_4228_, v_a_4229_, v_b_4230_);
v_r_4232_ = lean_box(v_res_4231_);
return v_r_4232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqDocOfHashable___redArg___lam__0(lean_object* v_inst_4233_, lean_object* v_inst_4234_, lean_object* v_a_4235_, lean_object* v_b_4236_){
_start:
{
lean_object* v___x_4237_; 
v___x_4237_ = l_Lean_Fmt_Doc_beq___redArg(v_inst_4233_, v_inst_4234_, v_a_4235_, v_b_4236_);
return v___x_4237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqDocOfHashable___redArg(lean_object* v_inst_4238_, lean_object* v_inst_4239_){
_start:
{
lean_object* v___f_4240_; 
v___f_4240_ = lean_alloc_closure((void*)(l_Lean_Fmt_instBEqDocOfHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_4240_, 0, v_inst_4238_);
lean_closure_set(v___f_4240_, 1, v_inst_4239_);
return v___f_4240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqDocOfHashable(lean_object* v_00_u03c4_4241_, lean_object* v_inst_4242_, lean_object* v_inst_4243_){
_start:
{
lean_object* v___f_4244_; 
v___f_4244_ = lean_alloc_closure((void*)(l_Lean_Fmt_instBEqDocOfHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_4244_, 0, v_inst_4242_);
lean_closure_set(v___f_4244_, 1, v_inst_4243_);
return v___f_4244_;
}
}
lean_object* runtime_initialize_Init_Data_Hashable(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashMap_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Core_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Fmt_instInhabitedFullnessState___aux__1 = _init_l_Lean_Fmt_instInhabitedFullnessState___aux__1();
l_Lean_Fmt_instInhabitedFullnessState = _init_l_Lean_Fmt_instInhabitedFullnessState();
l_Lean_Fmt_newlineFailureSet = _init_l_Lean_Fmt_newlineFailureSet();
l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_emptyTextFailureSet = _init_l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_emptyTextFailureSet();
l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_nonEmptyTextFailureSet = _init_l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_nonEmptyTextFailureSet();
l_Lean_Fmt_instInhabitedTagId___aux__1 = _init_l_Lean_Fmt_instInhabitedTagId___aux__1();
lean_mark_persistent(l_Lean_Fmt_instInhabitedTagId___aux__1);
l_Lean_Fmt_instInhabitedTagId = _init_l_Lean_Fmt_instInhabitedTagId();
lean_mark_persistent(l_Lean_Fmt_instInhabitedTagId);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Core_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Hashable(uint8_t builtin);
lean_object* initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* initialize_Std_Data_HashMap_Basic(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Core_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Core_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Core_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Core_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
