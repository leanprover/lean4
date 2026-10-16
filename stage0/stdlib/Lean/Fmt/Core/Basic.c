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
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_containsGuarded_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_containsGuarded_match__1_splitter___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_containsGuarded_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_containsGuarded_match__1_splitter___boxed(lean_object**);
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
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_atomicness___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_atomicness___override___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg___boxed(lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_Doc_neverFailsSet___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_neverFailsSet___override___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_containsGuarded___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_containsGuarded___override___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg___boxed(lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_Doc_failureSet___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_failureSet___override___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_tagged___override___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_tagged___override(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Fmt_Doc_flattened___override___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_Doc_flattened___override___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_Doc_flattened___override___redArg___closed__0_value;
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
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_containsGuarded___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_containsGuarded___override___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_text___override_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_text___override_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_text___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_text___override(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__17_spec__25___redArg___lam__0(uint8_t, uint16_t, uint8_t, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__17_spec__25___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__17_spec__25___redArg(uint16_t, uint8_t, lean_object*, lean_object*, uint16_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__17_spec__25___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__17___redArg(uint16_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg___lam__0(uint8_t, uint16_t, lean_object*, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg(uint16_t, lean_object*, uint8_t, lean_object*, uint16_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16___redArg(uint16_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_append___override___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_append___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_text___override_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_text___override_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16(uint16_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__17(uint16_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23(uint16_t, lean_object*, lean_object*, uint8_t, lean_object*, uint16_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__17_spec__25(uint16_t, uint8_t, lean_object*, lean_object*, lean_object*, uint16_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__17_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec(v_h__5_1121_);
lean_dec(v_h__4_1120_);
lean_dec(v_h__3_1119_);
lean_dec(v_h__2_1118_);
lean_dec(v_h__1_1117_);
v_id_1138_ = lean_ctor_get(v_x_1116_, 0);
lean_inc(v_id_1138_);
v_d_1139_ = lean_ctor_get(v_x_1116_, 1);
lean_inc(v_d_1139_);
lean_dec_ref_known(v_x_1116_, 2);
v___x_1140_ = lean_apply_3(v_h__6_1122_, lean_box(0), v_id_1138_, v_d_1139_);
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
v_d_1143_ = lean_ctor_get(v_x_1116_, 0);
lean_inc(v_d_1143_);
lean_dec_ref_known(v_x_1116_, 1);
v___x_1144_ = lean_apply_2(v_h__5_1121_, lean_box(0), v_d_1143_);
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
lean_dec(v_h__6_1122_);
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
v___x_1149_ = lean_apply_4(v_h__7_1123_, lean_box(0), v_n_1145_, v___x_1148_, v_d_1147_);
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
lean_dec(v_h__7_1123_);
lean_dec(v_h__6_1122_);
lean_dec(v_h__5_1121_);
lean_dec(v_h__4_1120_);
lean_dec(v_h__3_1119_);
lean_dec(v_h__2_1118_);
lean_dec(v_h__1_1117_);
v_d_1150_ = lean_ctor_get(v_x_1116_, 0);
lean_inc(v_d_1150_);
lean_dec_ref_known(v_x_1116_, 1);
v___x_1151_ = lean_apply_2(v_h__8_1124_, lean_box(0), v_d_1150_);
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
lean_dec(v_h__8_1124_);
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
v___x_1155_ = lean_apply_3(v_h__9_1125_, lean_box(0), v___x_1154_, v_d_1153_);
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
lean_dec(v_h__9_1125_);
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
v___x_1157_ = lean_apply_2(v_h__10_1126_, lean_box(0), v_d_1156_);
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
v_d_1158_ = lean_ctor_get(v_x_1116_, 0);
lean_inc(v_d_1158_);
lean_dec_ref_known(v_x_1116_, 1);
v___x_1159_ = lean_apply_2(v_h__11_1127_, lean_box(0), v_d_1158_);
return v___x_1159_;
}
case 11:
{
lean_object* v_d_1160_; lean_object* v___x_1161_; 
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
v_d_1160_ = lean_ctor_get(v_x_1116_, 0);
lean_inc(v_d_1160_);
lean_dec_ref_known(v_x_1116_, 1);
v___x_1161_ = lean_apply_2(v_h__12_1128_, lean_box(0), v_d_1160_);
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
lean_dec(v_h__5_1199_);
lean_dec(v_h__4_1198_);
lean_dec(v_h__3_1197_);
lean_dec(v_h__2_1196_);
lean_dec(v_h__1_1195_);
v_id_1216_ = lean_ctor_get(v_x_1194_, 0);
lean_inc(v_id_1216_);
v_d_1217_ = lean_ctor_get(v_x_1194_, 1);
lean_inc(v_d_1217_);
lean_dec_ref_known(v_x_1194_, 2);
v___x_1218_ = lean_apply_3(v_h__6_1200_, lean_box(0), v_id_1216_, v_d_1217_);
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
v_d_1221_ = lean_ctor_get(v_x_1194_, 0);
lean_inc(v_d_1221_);
lean_dec_ref_known(v_x_1194_, 1);
v___x_1222_ = lean_apply_2(v_h__5_1199_, lean_box(0), v_d_1221_);
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
lean_dec(v_h__6_1200_);
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
v___x_1227_ = lean_apply_4(v_h__7_1201_, lean_box(0), v_n_1223_, v___x_1226_, v_d_1225_);
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
lean_dec(v_h__7_1201_);
lean_dec(v_h__6_1200_);
lean_dec(v_h__5_1199_);
lean_dec(v_h__4_1198_);
lean_dec(v_h__3_1197_);
lean_dec(v_h__2_1196_);
lean_dec(v_h__1_1195_);
v_d_1228_ = lean_ctor_get(v_x_1194_, 0);
lean_inc(v_d_1228_);
lean_dec_ref_known(v_x_1194_, 1);
v___x_1229_ = lean_apply_2(v_h__8_1202_, lean_box(0), v_d_1228_);
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
lean_dec(v_h__8_1202_);
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
v___x_1233_ = lean_apply_3(v_h__9_1203_, lean_box(0), v___x_1232_, v_d_1231_);
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
lean_dec(v_h__9_1203_);
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
v___x_1235_ = lean_apply_2(v_h__10_1204_, lean_box(0), v_d_1234_);
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
v_d_1236_ = lean_ctor_get(v_x_1194_, 0);
lean_inc(v_d_1236_);
lean_dec_ref_known(v_x_1194_, 1);
v___x_1237_ = lean_apply_2(v_h__11_1205_, lean_box(0), v_d_1236_);
return v___x_1237_;
}
case 11:
{
lean_object* v_d_1238_; lean_object* v___x_1239_; 
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
v_d_1238_ = lean_ctor_get(v_x_1194_, 0);
lean_inc(v_d_1238_);
lean_dec_ref_known(v_x_1194_, 1);
v___x_1239_ = lean_apply_2(v_h__12_1206_, lean_box(0), v_d_1238_);
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
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__1_splitter___redArg(uint8_t v_x_1272_, lean_object* v_h__1_1273_, lean_object* v_h__2_1274_, lean_object* v_h__3_1275_){
_start:
{
switch(v_x_1272_)
{
case 0:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; 
lean_dec(v_h__3_1275_);
lean_dec(v_h__2_1274_);
v___x_1276_ = lean_box(0);
v___x_1277_ = lean_apply_1(v_h__1_1273_, v___x_1276_);
return v___x_1277_;
}
case 1:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
lean_dec(v_h__3_1275_);
lean_dec(v_h__1_1273_);
v___x_1278_ = lean_box(0);
v___x_1279_ = lean_apply_1(v_h__2_1274_, v___x_1278_);
return v___x_1279_;
}
default: 
{
lean_object* v___x_1280_; lean_object* v___x_1281_; 
lean_dec(v_h__2_1274_);
lean_dec(v_h__1_1273_);
v___x_1280_ = lean_box(0);
v___x_1281_ = lean_apply_1(v_h__3_1275_, v___x_1280_);
return v___x_1281_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__1_splitter___redArg___boxed(lean_object* v_x_1282_, lean_object* v_h__1_1283_, lean_object* v_h__2_1284_, lean_object* v_h__3_1285_){
_start:
{
uint8_t v_x_33__boxed_1286_; lean_object* v_res_1287_; 
v_x_33__boxed_1286_ = lean_unbox(v_x_1282_);
v_res_1287_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__1_splitter___redArg(v_x_33__boxed_1286_, v_h__1_1283_, v_h__2_1284_, v_h__3_1285_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__1_splitter(lean_object* v_motive_1288_, uint8_t v_x_1289_, lean_object* v_h__1_1290_, lean_object* v_h__2_1291_, lean_object* v_h__3_1292_){
_start:
{
switch(v_x_1289_)
{
case 0:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
lean_dec(v_h__3_1292_);
lean_dec(v_h__2_1291_);
v___x_1293_ = lean_box(0);
v___x_1294_ = lean_apply_1(v_h__1_1290_, v___x_1293_);
return v___x_1294_;
}
case 1:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
lean_dec(v_h__3_1292_);
lean_dec(v_h__1_1290_);
v___x_1295_ = lean_box(0);
v___x_1296_ = lean_apply_1(v_h__2_1291_, v___x_1295_);
return v___x_1296_;
}
default: 
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
lean_dec(v_h__2_1291_);
lean_dec(v_h__1_1290_);
v___x_1297_ = lean_box(0);
v___x_1298_ = lean_apply_1(v_h__3_1292_, v___x_1297_);
return v___x_1298_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__1_splitter___boxed(lean_object* v_motive_1299_, lean_object* v_x_1300_, lean_object* v_h__1_1301_, lean_object* v_h__2_1302_, lean_object* v_h__3_1303_){
_start:
{
uint8_t v_x_48__boxed_1304_; lean_object* v_res_1305_; 
v_x_48__boxed_1304_ = lean_unbox(v_x_1300_);
v_res_1305_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__1_splitter(v_motive_1299_, v_x_48__boxed_1304_, v_h__1_1301_, v_h__2_1302_, v_h__3_1303_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__4_splitter___redArg(lean_object* v_x_1306_, lean_object* v_h__1_1307_, lean_object* v_h__2_1308_, lean_object* v_h__3_1309_, lean_object* v_h__4_1310_, lean_object* v_h__5_1311_, lean_object* v_h__6_1312_, lean_object* v_h__7_1313_, lean_object* v_h__8_1314_, lean_object* v_h__9_1315_, lean_object* v_h__10_1316_, lean_object* v_h__11_1317_, lean_object* v_h__12_1318_, lean_object* v_h__13_1319_, lean_object* v_h__14_1320_, lean_object* v_h__15_1321_, lean_object* v_h__16_1322_){
_start:
{
switch(lean_obj_tag(v_x_1306_))
{
case 0:
{
lean_object* v___x_1323_; 
lean_dec(v_h__16_1322_);
lean_dec(v_h__15_1321_);
lean_dec(v_h__14_1320_);
lean_dec(v_h__13_1319_);
lean_dec(v_h__12_1318_);
lean_dec(v_h__11_1317_);
lean_dec(v_h__10_1316_);
lean_dec(v_h__9_1315_);
lean_dec(v_h__8_1314_);
lean_dec(v_h__7_1313_);
lean_dec(v_h__6_1312_);
lean_dec(v_h__5_1311_);
lean_dec(v_h__4_1310_);
lean_dec(v_h__3_1309_);
lean_dec(v_h__2_1308_);
v___x_1323_ = lean_apply_1(v_h__1_1307_, lean_box(0));
return v___x_1323_;
}
case 1:
{
lean_object* v_f_1324_; lean_object* v___x_1325_; 
lean_dec(v_h__16_1322_);
lean_dec(v_h__15_1321_);
lean_dec(v_h__14_1320_);
lean_dec(v_h__13_1319_);
lean_dec(v_h__12_1318_);
lean_dec(v_h__11_1317_);
lean_dec(v_h__10_1316_);
lean_dec(v_h__9_1315_);
lean_dec(v_h__8_1314_);
lean_dec(v_h__7_1313_);
lean_dec(v_h__6_1312_);
lean_dec(v_h__5_1311_);
lean_dec(v_h__4_1310_);
lean_dec(v_h__2_1308_);
lean_dec(v_h__1_1307_);
v_f_1324_ = lean_ctor_get(v_x_1306_, 0);
lean_inc_ref(v_f_1324_);
lean_dec_ref_known(v_x_1306_, 1);
v___x_1325_ = lean_apply_2(v_h__3_1309_, lean_box(0), v_f_1324_);
return v___x_1325_;
}
case 2:
{
lean_object* v_s_1326_; lean_object* v___x_1327_; 
lean_dec(v_h__16_1322_);
lean_dec(v_h__15_1321_);
lean_dec(v_h__14_1320_);
lean_dec(v_h__13_1319_);
lean_dec(v_h__12_1318_);
lean_dec(v_h__11_1317_);
lean_dec(v_h__10_1316_);
lean_dec(v_h__9_1315_);
lean_dec(v_h__8_1314_);
lean_dec(v_h__7_1313_);
lean_dec(v_h__6_1312_);
lean_dec(v_h__5_1311_);
lean_dec(v_h__4_1310_);
lean_dec(v_h__3_1309_);
lean_dec(v_h__1_1307_);
v_s_1326_ = lean_ctor_get(v_x_1306_, 0);
lean_inc_ref(v_s_1326_);
lean_dec_ref_known(v_x_1306_, 1);
v___x_1327_ = lean_apply_2(v_h__2_1308_, lean_box(0), v_s_1326_);
return v___x_1327_;
}
case 3:
{
lean_object* v_id_1328_; lean_object* v_d_1329_; lean_object* v___x_1330_; 
lean_dec(v_h__16_1322_);
lean_dec(v_h__15_1321_);
lean_dec(v_h__14_1320_);
lean_dec(v_h__13_1319_);
lean_dec(v_h__12_1318_);
lean_dec(v_h__11_1317_);
lean_dec(v_h__10_1316_);
lean_dec(v_h__9_1315_);
lean_dec(v_h__8_1314_);
lean_dec(v_h__7_1313_);
lean_dec(v_h__5_1311_);
lean_dec(v_h__4_1310_);
lean_dec(v_h__3_1309_);
lean_dec(v_h__2_1308_);
lean_dec(v_h__1_1307_);
v_id_1328_ = lean_ctor_get(v_x_1306_, 0);
lean_inc(v_id_1328_);
v_d_1329_ = lean_ctor_get(v_x_1306_, 1);
lean_inc(v_d_1329_);
lean_dec_ref_known(v_x_1306_, 2);
v___x_1330_ = lean_apply_3(v_h__6_1312_, lean_box(0), v_id_1328_, v_d_1329_);
return v___x_1330_;
}
case 4:
{
lean_object* v_d_1331_; lean_object* v___x_1332_; 
lean_dec(v_h__16_1322_);
lean_dec(v_h__15_1321_);
lean_dec(v_h__14_1320_);
lean_dec(v_h__13_1319_);
lean_dec(v_h__12_1318_);
lean_dec(v_h__11_1317_);
lean_dec(v_h__10_1316_);
lean_dec(v_h__9_1315_);
lean_dec(v_h__8_1314_);
lean_dec(v_h__7_1313_);
lean_dec(v_h__6_1312_);
lean_dec(v_h__5_1311_);
lean_dec(v_h__3_1309_);
lean_dec(v_h__2_1308_);
lean_dec(v_h__1_1307_);
v_d_1331_ = lean_ctor_get(v_x_1306_, 0);
lean_inc(v_d_1331_);
lean_dec_ref_known(v_x_1306_, 1);
v___x_1332_ = lean_apply_2(v_h__4_1310_, lean_box(0), v_d_1331_);
return v___x_1332_;
}
case 5:
{
lean_object* v_d_1333_; lean_object* v___x_1334_; 
lean_dec(v_h__16_1322_);
lean_dec(v_h__15_1321_);
lean_dec(v_h__14_1320_);
lean_dec(v_h__13_1319_);
lean_dec(v_h__12_1318_);
lean_dec(v_h__11_1317_);
lean_dec(v_h__10_1316_);
lean_dec(v_h__9_1315_);
lean_dec(v_h__8_1314_);
lean_dec(v_h__7_1313_);
lean_dec(v_h__6_1312_);
lean_dec(v_h__4_1310_);
lean_dec(v_h__3_1309_);
lean_dec(v_h__2_1308_);
lean_dec(v_h__1_1307_);
v_d_1333_ = lean_ctor_get(v_x_1306_, 0);
lean_inc(v_d_1333_);
lean_dec_ref_known(v_x_1306_, 1);
v___x_1334_ = lean_apply_2(v_h__5_1311_, lean_box(0), v_d_1333_);
return v___x_1334_;
}
case 6:
{
lean_object* v_n_1335_; uint8_t v_isCumulative_1336_; lean_object* v_d_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
lean_dec(v_h__16_1322_);
lean_dec(v_h__15_1321_);
lean_dec(v_h__14_1320_);
lean_dec(v_h__13_1319_);
lean_dec(v_h__12_1318_);
lean_dec(v_h__11_1317_);
lean_dec(v_h__10_1316_);
lean_dec(v_h__9_1315_);
lean_dec(v_h__8_1314_);
lean_dec(v_h__6_1312_);
lean_dec(v_h__5_1311_);
lean_dec(v_h__4_1310_);
lean_dec(v_h__3_1309_);
lean_dec(v_h__2_1308_);
lean_dec(v_h__1_1307_);
v_n_1335_ = lean_ctor_get(v_x_1306_, 0);
lean_inc(v_n_1335_);
v_isCumulative_1336_ = lean_ctor_get_uint8(v_x_1306_, sizeof(void*)*2);
v_d_1337_ = lean_ctor_get(v_x_1306_, 1);
lean_inc(v_d_1337_);
lean_dec_ref_known(v_x_1306_, 2);
v___x_1338_ = lean_box(v_isCumulative_1336_);
v___x_1339_ = lean_apply_4(v_h__7_1313_, lean_box(0), v_n_1335_, v___x_1338_, v_d_1337_);
return v___x_1339_;
}
case 7:
{
lean_object* v_d_1340_; lean_object* v___x_1341_; 
lean_dec(v_h__16_1322_);
lean_dec(v_h__15_1321_);
lean_dec(v_h__14_1320_);
lean_dec(v_h__13_1319_);
lean_dec(v_h__12_1318_);
lean_dec(v_h__11_1317_);
lean_dec(v_h__10_1316_);
lean_dec(v_h__9_1315_);
lean_dec(v_h__7_1313_);
lean_dec(v_h__6_1312_);
lean_dec(v_h__5_1311_);
lean_dec(v_h__4_1310_);
lean_dec(v_h__3_1309_);
lean_dec(v_h__2_1308_);
lean_dec(v_h__1_1307_);
v_d_1340_ = lean_ctor_get(v_x_1306_, 0);
lean_inc(v_d_1340_);
lean_dec_ref_known(v_x_1306_, 1);
v___x_1341_ = lean_apply_2(v_h__8_1314_, lean_box(0), v_d_1340_);
return v___x_1341_;
}
case 8:
{
uint8_t v_onlyNonCumulative_1342_; lean_object* v_d_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
lean_dec(v_h__16_1322_);
lean_dec(v_h__15_1321_);
lean_dec(v_h__14_1320_);
lean_dec(v_h__13_1319_);
lean_dec(v_h__12_1318_);
lean_dec(v_h__11_1317_);
lean_dec(v_h__10_1316_);
lean_dec(v_h__8_1314_);
lean_dec(v_h__7_1313_);
lean_dec(v_h__6_1312_);
lean_dec(v_h__5_1311_);
lean_dec(v_h__4_1310_);
lean_dec(v_h__3_1309_);
lean_dec(v_h__2_1308_);
lean_dec(v_h__1_1307_);
v_onlyNonCumulative_1342_ = lean_ctor_get_uint8(v_x_1306_, sizeof(void*)*1);
v_d_1343_ = lean_ctor_get(v_x_1306_, 0);
lean_inc(v_d_1343_);
lean_dec_ref_known(v_x_1306_, 1);
v___x_1344_ = lean_box(v_onlyNonCumulative_1342_);
v___x_1345_ = lean_apply_3(v_h__9_1315_, lean_box(0), v___x_1344_, v_d_1343_);
return v___x_1345_;
}
case 9:
{
lean_object* v_d_1346_; lean_object* v___x_1347_; 
lean_dec(v_h__16_1322_);
lean_dec(v_h__15_1321_);
lean_dec(v_h__14_1320_);
lean_dec(v_h__13_1319_);
lean_dec(v_h__12_1318_);
lean_dec(v_h__11_1317_);
lean_dec(v_h__9_1315_);
lean_dec(v_h__8_1314_);
lean_dec(v_h__7_1313_);
lean_dec(v_h__6_1312_);
lean_dec(v_h__5_1311_);
lean_dec(v_h__4_1310_);
lean_dec(v_h__3_1309_);
lean_dec(v_h__2_1308_);
lean_dec(v_h__1_1307_);
v_d_1346_ = lean_ctor_get(v_x_1306_, 0);
lean_inc(v_d_1346_);
lean_dec_ref_known(v_x_1306_, 1);
v___x_1347_ = lean_apply_2(v_h__10_1316_, lean_box(0), v_d_1346_);
return v___x_1347_;
}
case 10:
{
lean_object* v_d_1348_; lean_object* v___x_1349_; 
lean_dec(v_h__16_1322_);
lean_dec(v_h__15_1321_);
lean_dec(v_h__14_1320_);
lean_dec(v_h__13_1319_);
lean_dec(v_h__12_1318_);
lean_dec(v_h__10_1316_);
lean_dec(v_h__9_1315_);
lean_dec(v_h__8_1314_);
lean_dec(v_h__7_1313_);
lean_dec(v_h__6_1312_);
lean_dec(v_h__5_1311_);
lean_dec(v_h__4_1310_);
lean_dec(v_h__3_1309_);
lean_dec(v_h__2_1308_);
lean_dec(v_h__1_1307_);
v_d_1348_ = lean_ctor_get(v_x_1306_, 0);
lean_inc(v_d_1348_);
lean_dec_ref_known(v_x_1306_, 1);
v___x_1349_ = lean_apply_2(v_h__11_1317_, lean_box(0), v_d_1348_);
return v___x_1349_;
}
case 11:
{
lean_object* v_d_1350_; lean_object* v___x_1351_; 
lean_dec(v_h__16_1322_);
lean_dec(v_h__15_1321_);
lean_dec(v_h__14_1320_);
lean_dec(v_h__13_1319_);
lean_dec(v_h__11_1317_);
lean_dec(v_h__10_1316_);
lean_dec(v_h__9_1315_);
lean_dec(v_h__8_1314_);
lean_dec(v_h__7_1313_);
lean_dec(v_h__6_1312_);
lean_dec(v_h__5_1311_);
lean_dec(v_h__4_1310_);
lean_dec(v_h__3_1309_);
lean_dec(v_h__2_1308_);
lean_dec(v_h__1_1307_);
v_d_1350_ = lean_ctor_get(v_x_1306_, 0);
lean_inc(v_d_1350_);
lean_dec_ref_known(v_x_1306_, 1);
v___x_1351_ = lean_apply_2(v_h__12_1318_, lean_box(0), v_d_1350_);
return v___x_1351_;
}
case 12:
{
lean_object* v_p_1352_; lean_object* v_d_1353_; lean_object* v___x_1354_; 
lean_dec(v_h__16_1322_);
lean_dec(v_h__15_1321_);
lean_dec(v_h__14_1320_);
lean_dec(v_h__12_1318_);
lean_dec(v_h__11_1317_);
lean_dec(v_h__10_1316_);
lean_dec(v_h__9_1315_);
lean_dec(v_h__8_1314_);
lean_dec(v_h__7_1313_);
lean_dec(v_h__6_1312_);
lean_dec(v_h__5_1311_);
lean_dec(v_h__4_1310_);
lean_dec(v_h__3_1309_);
lean_dec(v_h__2_1308_);
lean_dec(v_h__1_1307_);
v_p_1352_ = lean_ctor_get(v_x_1306_, 0);
lean_inc_ref(v_p_1352_);
v_d_1353_ = lean_ctor_get(v_x_1306_, 1);
lean_inc(v_d_1353_);
lean_dec_ref_known(v_x_1306_, 2);
v___x_1354_ = lean_apply_3(v_h__13_1319_, lean_box(0), v_p_1352_, v_d_1353_);
return v___x_1354_;
}
case 13:
{
lean_object* v_cost_1355_; lean_object* v_d_1356_; lean_object* v___x_1357_; 
lean_dec(v_h__16_1322_);
lean_dec(v_h__15_1321_);
lean_dec(v_h__13_1319_);
lean_dec(v_h__12_1318_);
lean_dec(v_h__11_1317_);
lean_dec(v_h__10_1316_);
lean_dec(v_h__9_1315_);
lean_dec(v_h__8_1314_);
lean_dec(v_h__7_1313_);
lean_dec(v_h__6_1312_);
lean_dec(v_h__5_1311_);
lean_dec(v_h__4_1310_);
lean_dec(v_h__3_1309_);
lean_dec(v_h__2_1308_);
lean_dec(v_h__1_1307_);
v_cost_1355_ = lean_ctor_get(v_x_1306_, 0);
lean_inc(v_cost_1355_);
v_d_1356_ = lean_ctor_get(v_x_1306_, 1);
lean_inc(v_d_1356_);
lean_dec_ref_known(v_x_1306_, 2);
v___x_1357_ = lean_apply_3(v_h__14_1320_, lean_box(0), v_cost_1355_, v_d_1356_);
return v___x_1357_;
}
case 14:
{
lean_object* v_a_1358_; lean_object* v_b_1359_; lean_object* v___x_1360_; 
lean_dec(v_h__16_1322_);
lean_dec(v_h__14_1320_);
lean_dec(v_h__13_1319_);
lean_dec(v_h__12_1318_);
lean_dec(v_h__11_1317_);
lean_dec(v_h__10_1316_);
lean_dec(v_h__9_1315_);
lean_dec(v_h__8_1314_);
lean_dec(v_h__7_1313_);
lean_dec(v_h__6_1312_);
lean_dec(v_h__5_1311_);
lean_dec(v_h__4_1310_);
lean_dec(v_h__3_1309_);
lean_dec(v_h__2_1308_);
lean_dec(v_h__1_1307_);
v_a_1358_ = lean_ctor_get(v_x_1306_, 0);
lean_inc(v_a_1358_);
v_b_1359_ = lean_ctor_get(v_x_1306_, 1);
lean_inc(v_b_1359_);
lean_dec_ref_known(v_x_1306_, 2);
v___x_1360_ = lean_apply_3(v_h__15_1321_, lean_box(0), v_a_1358_, v_b_1359_);
return v___x_1360_;
}
default: 
{
lean_object* v_a_1361_; lean_object* v_b_1362_; lean_object* v___x_1363_; 
lean_dec(v_h__15_1321_);
lean_dec(v_h__14_1320_);
lean_dec(v_h__13_1319_);
lean_dec(v_h__12_1318_);
lean_dec(v_h__11_1317_);
lean_dec(v_h__10_1316_);
lean_dec(v_h__9_1315_);
lean_dec(v_h__8_1314_);
lean_dec(v_h__7_1313_);
lean_dec(v_h__6_1312_);
lean_dec(v_h__5_1311_);
lean_dec(v_h__4_1310_);
lean_dec(v_h__3_1309_);
lean_dec(v_h__2_1308_);
lean_dec(v_h__1_1307_);
v_a_1361_ = lean_ctor_get(v_x_1306_, 0);
lean_inc(v_a_1361_);
v_b_1362_ = lean_ctor_get(v_x_1306_, 1);
lean_inc(v_b_1362_);
lean_dec_ref_known(v_x_1306_, 2);
v___x_1363_ = lean_apply_3(v_h__16_1322_, lean_box(0), v_a_1361_, v_b_1362_);
return v___x_1363_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__4_splitter___redArg___boxed(lean_object** _args){
lean_object* v_x_1364_ = _args[0];
lean_object* v_h__1_1365_ = _args[1];
lean_object* v_h__2_1366_ = _args[2];
lean_object* v_h__3_1367_ = _args[3];
lean_object* v_h__4_1368_ = _args[4];
lean_object* v_h__5_1369_ = _args[5];
lean_object* v_h__6_1370_ = _args[6];
lean_object* v_h__7_1371_ = _args[7];
lean_object* v_h__8_1372_ = _args[8];
lean_object* v_h__9_1373_ = _args[9];
lean_object* v_h__10_1374_ = _args[10];
lean_object* v_h__11_1375_ = _args[11];
lean_object* v_h__12_1376_ = _args[12];
lean_object* v_h__13_1377_ = _args[13];
lean_object* v_h__14_1378_ = _args[14];
lean_object* v_h__15_1379_ = _args[15];
lean_object* v_h__16_1380_ = _args[16];
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__4_splitter___redArg(v_x_1364_, v_h__1_1365_, v_h__2_1366_, v_h__3_1367_, v_h__4_1368_, v_h__5_1369_, v_h__6_1370_, v_h__7_1371_, v_h__8_1372_, v_h__9_1373_, v_h__10_1374_, v_h__11_1375_, v_h__12_1376_, v_h__13_1377_, v_h__14_1378_, v_h__15_1379_, v_h__16_1380_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__4_splitter(lean_object* v_motive_1382_, lean_object* v_x_1383_, lean_object* v_x_1384_, lean_object* v_h__1_1385_, lean_object* v_h__2_1386_, lean_object* v_h__3_1387_, lean_object* v_h__4_1388_, lean_object* v_h__5_1389_, lean_object* v_h__6_1390_, lean_object* v_h__7_1391_, lean_object* v_h__8_1392_, lean_object* v_h__9_1393_, lean_object* v_h__10_1394_, lean_object* v_h__11_1395_, lean_object* v_h__12_1396_, lean_object* v_h__13_1397_, lean_object* v_h__14_1398_, lean_object* v_h__15_1399_, lean_object* v_h__16_1400_){
_start:
{
switch(lean_obj_tag(v_x_1384_))
{
case 0:
{
lean_object* v___x_1401_; 
lean_dec(v_h__16_1400_);
lean_dec(v_h__15_1399_);
lean_dec(v_h__14_1398_);
lean_dec(v_h__13_1397_);
lean_dec(v_h__12_1396_);
lean_dec(v_h__11_1395_);
lean_dec(v_h__10_1394_);
lean_dec(v_h__9_1393_);
lean_dec(v_h__8_1392_);
lean_dec(v_h__7_1391_);
lean_dec(v_h__6_1390_);
lean_dec(v_h__5_1389_);
lean_dec(v_h__4_1388_);
lean_dec(v_h__3_1387_);
lean_dec(v_h__2_1386_);
v___x_1401_ = lean_apply_1(v_h__1_1385_, lean_box(0));
return v___x_1401_;
}
case 1:
{
lean_object* v_f_1402_; lean_object* v___x_1403_; 
lean_dec(v_h__16_1400_);
lean_dec(v_h__15_1399_);
lean_dec(v_h__14_1398_);
lean_dec(v_h__13_1397_);
lean_dec(v_h__12_1396_);
lean_dec(v_h__11_1395_);
lean_dec(v_h__10_1394_);
lean_dec(v_h__9_1393_);
lean_dec(v_h__8_1392_);
lean_dec(v_h__7_1391_);
lean_dec(v_h__6_1390_);
lean_dec(v_h__5_1389_);
lean_dec(v_h__4_1388_);
lean_dec(v_h__2_1386_);
lean_dec(v_h__1_1385_);
v_f_1402_ = lean_ctor_get(v_x_1384_, 0);
lean_inc_ref(v_f_1402_);
lean_dec_ref_known(v_x_1384_, 1);
v___x_1403_ = lean_apply_2(v_h__3_1387_, lean_box(0), v_f_1402_);
return v___x_1403_;
}
case 2:
{
lean_object* v_s_1404_; lean_object* v___x_1405_; 
lean_dec(v_h__16_1400_);
lean_dec(v_h__15_1399_);
lean_dec(v_h__14_1398_);
lean_dec(v_h__13_1397_);
lean_dec(v_h__12_1396_);
lean_dec(v_h__11_1395_);
lean_dec(v_h__10_1394_);
lean_dec(v_h__9_1393_);
lean_dec(v_h__8_1392_);
lean_dec(v_h__7_1391_);
lean_dec(v_h__6_1390_);
lean_dec(v_h__5_1389_);
lean_dec(v_h__4_1388_);
lean_dec(v_h__3_1387_);
lean_dec(v_h__1_1385_);
v_s_1404_ = lean_ctor_get(v_x_1384_, 0);
lean_inc_ref(v_s_1404_);
lean_dec_ref_known(v_x_1384_, 1);
v___x_1405_ = lean_apply_2(v_h__2_1386_, lean_box(0), v_s_1404_);
return v___x_1405_;
}
case 3:
{
lean_object* v_id_1406_; lean_object* v_d_1407_; lean_object* v___x_1408_; 
lean_dec(v_h__16_1400_);
lean_dec(v_h__15_1399_);
lean_dec(v_h__14_1398_);
lean_dec(v_h__13_1397_);
lean_dec(v_h__12_1396_);
lean_dec(v_h__11_1395_);
lean_dec(v_h__10_1394_);
lean_dec(v_h__9_1393_);
lean_dec(v_h__8_1392_);
lean_dec(v_h__7_1391_);
lean_dec(v_h__5_1389_);
lean_dec(v_h__4_1388_);
lean_dec(v_h__3_1387_);
lean_dec(v_h__2_1386_);
lean_dec(v_h__1_1385_);
v_id_1406_ = lean_ctor_get(v_x_1384_, 0);
lean_inc(v_id_1406_);
v_d_1407_ = lean_ctor_get(v_x_1384_, 1);
lean_inc(v_d_1407_);
lean_dec_ref_known(v_x_1384_, 2);
v___x_1408_ = lean_apply_3(v_h__6_1390_, lean_box(0), v_id_1406_, v_d_1407_);
return v___x_1408_;
}
case 4:
{
lean_object* v_d_1409_; lean_object* v___x_1410_; 
lean_dec(v_h__16_1400_);
lean_dec(v_h__15_1399_);
lean_dec(v_h__14_1398_);
lean_dec(v_h__13_1397_);
lean_dec(v_h__12_1396_);
lean_dec(v_h__11_1395_);
lean_dec(v_h__10_1394_);
lean_dec(v_h__9_1393_);
lean_dec(v_h__8_1392_);
lean_dec(v_h__7_1391_);
lean_dec(v_h__6_1390_);
lean_dec(v_h__5_1389_);
lean_dec(v_h__3_1387_);
lean_dec(v_h__2_1386_);
lean_dec(v_h__1_1385_);
v_d_1409_ = lean_ctor_get(v_x_1384_, 0);
lean_inc(v_d_1409_);
lean_dec_ref_known(v_x_1384_, 1);
v___x_1410_ = lean_apply_2(v_h__4_1388_, lean_box(0), v_d_1409_);
return v___x_1410_;
}
case 5:
{
lean_object* v_d_1411_; lean_object* v___x_1412_; 
lean_dec(v_h__16_1400_);
lean_dec(v_h__15_1399_);
lean_dec(v_h__14_1398_);
lean_dec(v_h__13_1397_);
lean_dec(v_h__12_1396_);
lean_dec(v_h__11_1395_);
lean_dec(v_h__10_1394_);
lean_dec(v_h__9_1393_);
lean_dec(v_h__8_1392_);
lean_dec(v_h__7_1391_);
lean_dec(v_h__6_1390_);
lean_dec(v_h__4_1388_);
lean_dec(v_h__3_1387_);
lean_dec(v_h__2_1386_);
lean_dec(v_h__1_1385_);
v_d_1411_ = lean_ctor_get(v_x_1384_, 0);
lean_inc(v_d_1411_);
lean_dec_ref_known(v_x_1384_, 1);
v___x_1412_ = lean_apply_2(v_h__5_1389_, lean_box(0), v_d_1411_);
return v___x_1412_;
}
case 6:
{
lean_object* v_n_1413_; uint8_t v_isCumulative_1414_; lean_object* v_d_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
lean_dec(v_h__16_1400_);
lean_dec(v_h__15_1399_);
lean_dec(v_h__14_1398_);
lean_dec(v_h__13_1397_);
lean_dec(v_h__12_1396_);
lean_dec(v_h__11_1395_);
lean_dec(v_h__10_1394_);
lean_dec(v_h__9_1393_);
lean_dec(v_h__8_1392_);
lean_dec(v_h__6_1390_);
lean_dec(v_h__5_1389_);
lean_dec(v_h__4_1388_);
lean_dec(v_h__3_1387_);
lean_dec(v_h__2_1386_);
lean_dec(v_h__1_1385_);
v_n_1413_ = lean_ctor_get(v_x_1384_, 0);
lean_inc(v_n_1413_);
v_isCumulative_1414_ = lean_ctor_get_uint8(v_x_1384_, sizeof(void*)*2);
v_d_1415_ = lean_ctor_get(v_x_1384_, 1);
lean_inc(v_d_1415_);
lean_dec_ref_known(v_x_1384_, 2);
v___x_1416_ = lean_box(v_isCumulative_1414_);
v___x_1417_ = lean_apply_4(v_h__7_1391_, lean_box(0), v_n_1413_, v___x_1416_, v_d_1415_);
return v___x_1417_;
}
case 7:
{
lean_object* v_d_1418_; lean_object* v___x_1419_; 
lean_dec(v_h__16_1400_);
lean_dec(v_h__15_1399_);
lean_dec(v_h__14_1398_);
lean_dec(v_h__13_1397_);
lean_dec(v_h__12_1396_);
lean_dec(v_h__11_1395_);
lean_dec(v_h__10_1394_);
lean_dec(v_h__9_1393_);
lean_dec(v_h__7_1391_);
lean_dec(v_h__6_1390_);
lean_dec(v_h__5_1389_);
lean_dec(v_h__4_1388_);
lean_dec(v_h__3_1387_);
lean_dec(v_h__2_1386_);
lean_dec(v_h__1_1385_);
v_d_1418_ = lean_ctor_get(v_x_1384_, 0);
lean_inc(v_d_1418_);
lean_dec_ref_known(v_x_1384_, 1);
v___x_1419_ = lean_apply_2(v_h__8_1392_, lean_box(0), v_d_1418_);
return v___x_1419_;
}
case 8:
{
uint8_t v_onlyNonCumulative_1420_; lean_object* v_d_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
lean_dec(v_h__16_1400_);
lean_dec(v_h__15_1399_);
lean_dec(v_h__14_1398_);
lean_dec(v_h__13_1397_);
lean_dec(v_h__12_1396_);
lean_dec(v_h__11_1395_);
lean_dec(v_h__10_1394_);
lean_dec(v_h__8_1392_);
lean_dec(v_h__7_1391_);
lean_dec(v_h__6_1390_);
lean_dec(v_h__5_1389_);
lean_dec(v_h__4_1388_);
lean_dec(v_h__3_1387_);
lean_dec(v_h__2_1386_);
lean_dec(v_h__1_1385_);
v_onlyNonCumulative_1420_ = lean_ctor_get_uint8(v_x_1384_, sizeof(void*)*1);
v_d_1421_ = lean_ctor_get(v_x_1384_, 0);
lean_inc(v_d_1421_);
lean_dec_ref_known(v_x_1384_, 1);
v___x_1422_ = lean_box(v_onlyNonCumulative_1420_);
v___x_1423_ = lean_apply_3(v_h__9_1393_, lean_box(0), v___x_1422_, v_d_1421_);
return v___x_1423_;
}
case 9:
{
lean_object* v_d_1424_; lean_object* v___x_1425_; 
lean_dec(v_h__16_1400_);
lean_dec(v_h__15_1399_);
lean_dec(v_h__14_1398_);
lean_dec(v_h__13_1397_);
lean_dec(v_h__12_1396_);
lean_dec(v_h__11_1395_);
lean_dec(v_h__9_1393_);
lean_dec(v_h__8_1392_);
lean_dec(v_h__7_1391_);
lean_dec(v_h__6_1390_);
lean_dec(v_h__5_1389_);
lean_dec(v_h__4_1388_);
lean_dec(v_h__3_1387_);
lean_dec(v_h__2_1386_);
lean_dec(v_h__1_1385_);
v_d_1424_ = lean_ctor_get(v_x_1384_, 0);
lean_inc(v_d_1424_);
lean_dec_ref_known(v_x_1384_, 1);
v___x_1425_ = lean_apply_2(v_h__10_1394_, lean_box(0), v_d_1424_);
return v___x_1425_;
}
case 10:
{
lean_object* v_d_1426_; lean_object* v___x_1427_; 
lean_dec(v_h__16_1400_);
lean_dec(v_h__15_1399_);
lean_dec(v_h__14_1398_);
lean_dec(v_h__13_1397_);
lean_dec(v_h__12_1396_);
lean_dec(v_h__10_1394_);
lean_dec(v_h__9_1393_);
lean_dec(v_h__8_1392_);
lean_dec(v_h__7_1391_);
lean_dec(v_h__6_1390_);
lean_dec(v_h__5_1389_);
lean_dec(v_h__4_1388_);
lean_dec(v_h__3_1387_);
lean_dec(v_h__2_1386_);
lean_dec(v_h__1_1385_);
v_d_1426_ = lean_ctor_get(v_x_1384_, 0);
lean_inc(v_d_1426_);
lean_dec_ref_known(v_x_1384_, 1);
v___x_1427_ = lean_apply_2(v_h__11_1395_, lean_box(0), v_d_1426_);
return v___x_1427_;
}
case 11:
{
lean_object* v_d_1428_; lean_object* v___x_1429_; 
lean_dec(v_h__16_1400_);
lean_dec(v_h__15_1399_);
lean_dec(v_h__14_1398_);
lean_dec(v_h__13_1397_);
lean_dec(v_h__11_1395_);
lean_dec(v_h__10_1394_);
lean_dec(v_h__9_1393_);
lean_dec(v_h__8_1392_);
lean_dec(v_h__7_1391_);
lean_dec(v_h__6_1390_);
lean_dec(v_h__5_1389_);
lean_dec(v_h__4_1388_);
lean_dec(v_h__3_1387_);
lean_dec(v_h__2_1386_);
lean_dec(v_h__1_1385_);
v_d_1428_ = lean_ctor_get(v_x_1384_, 0);
lean_inc(v_d_1428_);
lean_dec_ref_known(v_x_1384_, 1);
v___x_1429_ = lean_apply_2(v_h__12_1396_, lean_box(0), v_d_1428_);
return v___x_1429_;
}
case 12:
{
lean_object* v_p_1430_; lean_object* v_d_1431_; lean_object* v___x_1432_; 
lean_dec(v_h__16_1400_);
lean_dec(v_h__15_1399_);
lean_dec(v_h__14_1398_);
lean_dec(v_h__12_1396_);
lean_dec(v_h__11_1395_);
lean_dec(v_h__10_1394_);
lean_dec(v_h__9_1393_);
lean_dec(v_h__8_1392_);
lean_dec(v_h__7_1391_);
lean_dec(v_h__6_1390_);
lean_dec(v_h__5_1389_);
lean_dec(v_h__4_1388_);
lean_dec(v_h__3_1387_);
lean_dec(v_h__2_1386_);
lean_dec(v_h__1_1385_);
v_p_1430_ = lean_ctor_get(v_x_1384_, 0);
lean_inc_ref(v_p_1430_);
v_d_1431_ = lean_ctor_get(v_x_1384_, 1);
lean_inc(v_d_1431_);
lean_dec_ref_known(v_x_1384_, 2);
v___x_1432_ = lean_apply_3(v_h__13_1397_, lean_box(0), v_p_1430_, v_d_1431_);
return v___x_1432_;
}
case 13:
{
lean_object* v_cost_1433_; lean_object* v_d_1434_; lean_object* v___x_1435_; 
lean_dec(v_h__16_1400_);
lean_dec(v_h__15_1399_);
lean_dec(v_h__13_1397_);
lean_dec(v_h__12_1396_);
lean_dec(v_h__11_1395_);
lean_dec(v_h__10_1394_);
lean_dec(v_h__9_1393_);
lean_dec(v_h__8_1392_);
lean_dec(v_h__7_1391_);
lean_dec(v_h__6_1390_);
lean_dec(v_h__5_1389_);
lean_dec(v_h__4_1388_);
lean_dec(v_h__3_1387_);
lean_dec(v_h__2_1386_);
lean_dec(v_h__1_1385_);
v_cost_1433_ = lean_ctor_get(v_x_1384_, 0);
lean_inc(v_cost_1433_);
v_d_1434_ = lean_ctor_get(v_x_1384_, 1);
lean_inc(v_d_1434_);
lean_dec_ref_known(v_x_1384_, 2);
v___x_1435_ = lean_apply_3(v_h__14_1398_, lean_box(0), v_cost_1433_, v_d_1434_);
return v___x_1435_;
}
case 14:
{
lean_object* v_a_1436_; lean_object* v_b_1437_; lean_object* v___x_1438_; 
lean_dec(v_h__16_1400_);
lean_dec(v_h__14_1398_);
lean_dec(v_h__13_1397_);
lean_dec(v_h__12_1396_);
lean_dec(v_h__11_1395_);
lean_dec(v_h__10_1394_);
lean_dec(v_h__9_1393_);
lean_dec(v_h__8_1392_);
lean_dec(v_h__7_1391_);
lean_dec(v_h__6_1390_);
lean_dec(v_h__5_1389_);
lean_dec(v_h__4_1388_);
lean_dec(v_h__3_1387_);
lean_dec(v_h__2_1386_);
lean_dec(v_h__1_1385_);
v_a_1436_ = lean_ctor_get(v_x_1384_, 0);
lean_inc(v_a_1436_);
v_b_1437_ = lean_ctor_get(v_x_1384_, 1);
lean_inc(v_b_1437_);
lean_dec_ref_known(v_x_1384_, 2);
v___x_1438_ = lean_apply_3(v_h__15_1399_, lean_box(0), v_a_1436_, v_b_1437_);
return v___x_1438_;
}
default: 
{
lean_object* v_a_1439_; lean_object* v_b_1440_; lean_object* v___x_1441_; 
lean_dec(v_h__15_1399_);
lean_dec(v_h__14_1398_);
lean_dec(v_h__13_1397_);
lean_dec(v_h__12_1396_);
lean_dec(v_h__11_1395_);
lean_dec(v_h__10_1394_);
lean_dec(v_h__9_1393_);
lean_dec(v_h__8_1392_);
lean_dec(v_h__7_1391_);
lean_dec(v_h__6_1390_);
lean_dec(v_h__5_1389_);
lean_dec(v_h__4_1388_);
lean_dec(v_h__3_1387_);
lean_dec(v_h__2_1386_);
lean_dec(v_h__1_1385_);
v_a_1439_ = lean_ctor_get(v_x_1384_, 0);
lean_inc(v_a_1439_);
v_b_1440_ = lean_ctor_get(v_x_1384_, 1);
lean_inc(v_b_1440_);
lean_dec_ref_known(v_x_1384_, 2);
v___x_1441_ = lean_apply_3(v_h__16_1400_, lean_box(0), v_a_1439_, v_b_1440_);
return v___x_1441_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__4_splitter___boxed(lean_object** _args){
lean_object* v_motive_1442_ = _args[0];
lean_object* v_x_1443_ = _args[1];
lean_object* v_x_1444_ = _args[2];
lean_object* v_h__1_1445_ = _args[3];
lean_object* v_h__2_1446_ = _args[4];
lean_object* v_h__3_1447_ = _args[5];
lean_object* v_h__4_1448_ = _args[6];
lean_object* v_h__5_1449_ = _args[7];
lean_object* v_h__6_1450_ = _args[8];
lean_object* v_h__7_1451_ = _args[9];
lean_object* v_h__8_1452_ = _args[10];
lean_object* v_h__9_1453_ = _args[11];
lean_object* v_h__10_1454_ = _args[12];
lean_object* v_h__11_1455_ = _args[13];
lean_object* v_h__12_1456_ = _args[14];
lean_object* v_h__13_1457_ = _args[15];
lean_object* v_h__14_1458_ = _args[16];
lean_object* v_h__15_1459_ = _args[17];
lean_object* v_h__16_1460_ = _args[18];
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__4_splitter(v_motive_1442_, v_x_1443_, v_x_1444_, v_h__1_1445_, v_h__2_1446_, v_h__3_1447_, v_h__4_1448_, v_h__5_1449_, v_h__6_1450_, v_h__7_1451_, v_h__8_1452_, v_h__9_1453_, v_h__10_1454_, v_h__11_1455_, v_h__12_1456_, v_h__13_1457_, v_h__14_1458_, v_h__15_1459_, v_h__16_1460_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__1_splitter___redArg(uint8_t v_x_1462_, lean_object* v_h__1_1463_, lean_object* v_h__2_1464_, lean_object* v_h__3_1465_, lean_object* v_h__4_1466_, lean_object* v_h__5_1467_){
_start:
{
switch(v_x_1462_)
{
case 0:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
lean_dec(v_h__5_1467_);
lean_dec(v_h__4_1466_);
lean_dec(v_h__3_1465_);
lean_dec(v_h__2_1464_);
v___x_1468_ = lean_box(0);
v___x_1469_ = lean_apply_1(v_h__1_1463_, v___x_1468_);
return v___x_1469_;
}
case 1:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
lean_dec(v_h__5_1467_);
lean_dec(v_h__4_1466_);
lean_dec(v_h__3_1465_);
lean_dec(v_h__1_1463_);
v___x_1470_ = lean_box(0);
v___x_1471_ = lean_apply_1(v_h__2_1464_, v___x_1470_);
return v___x_1471_;
}
case 2:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
lean_dec(v_h__5_1467_);
lean_dec(v_h__4_1466_);
lean_dec(v_h__2_1464_);
lean_dec(v_h__1_1463_);
v___x_1472_ = lean_box(0);
v___x_1473_ = lean_apply_1(v_h__3_1465_, v___x_1472_);
return v___x_1473_;
}
case 3:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; 
lean_dec(v_h__5_1467_);
lean_dec(v_h__3_1465_);
lean_dec(v_h__2_1464_);
lean_dec(v_h__1_1463_);
v___x_1474_ = lean_box(0);
v___x_1475_ = lean_apply_1(v_h__4_1466_, v___x_1474_);
return v___x_1475_;
}
default: 
{
lean_object* v___x_1476_; lean_object* v___x_1477_; 
lean_dec(v_h__4_1466_);
lean_dec(v_h__3_1465_);
lean_dec(v_h__2_1464_);
lean_dec(v_h__1_1463_);
v___x_1476_ = lean_box(0);
v___x_1477_ = lean_apply_1(v_h__5_1467_, v___x_1476_);
return v___x_1477_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__1_splitter___redArg___boxed(lean_object* v_x_1478_, lean_object* v_h__1_1479_, lean_object* v_h__2_1480_, lean_object* v_h__3_1481_, lean_object* v_h__4_1482_, lean_object* v_h__5_1483_){
_start:
{
uint8_t v_x_51__boxed_1484_; lean_object* v_res_1485_; 
v_x_51__boxed_1484_ = lean_unbox(v_x_1478_);
v_res_1485_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__1_splitter___redArg(v_x_51__boxed_1484_, v_h__1_1479_, v_h__2_1480_, v_h__3_1481_, v_h__4_1482_, v_h__5_1483_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__1_splitter(lean_object* v_motive_1486_, uint8_t v_x_1487_, lean_object* v_h__1_1488_, lean_object* v_h__2_1489_, lean_object* v_h__3_1490_, lean_object* v_h__4_1491_, lean_object* v_h__5_1492_){
_start:
{
switch(v_x_1487_)
{
case 0:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; 
lean_dec(v_h__5_1492_);
lean_dec(v_h__4_1491_);
lean_dec(v_h__3_1490_);
lean_dec(v_h__2_1489_);
v___x_1493_ = lean_box(0);
v___x_1494_ = lean_apply_1(v_h__1_1488_, v___x_1493_);
return v___x_1494_;
}
case 1:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; 
lean_dec(v_h__5_1492_);
lean_dec(v_h__4_1491_);
lean_dec(v_h__3_1490_);
lean_dec(v_h__1_1488_);
v___x_1495_ = lean_box(0);
v___x_1496_ = lean_apply_1(v_h__2_1489_, v___x_1495_);
return v___x_1496_;
}
case 2:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; 
lean_dec(v_h__5_1492_);
lean_dec(v_h__4_1491_);
lean_dec(v_h__2_1489_);
lean_dec(v_h__1_1488_);
v___x_1497_ = lean_box(0);
v___x_1498_ = lean_apply_1(v_h__3_1490_, v___x_1497_);
return v___x_1498_;
}
case 3:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; 
lean_dec(v_h__5_1492_);
lean_dec(v_h__3_1490_);
lean_dec(v_h__2_1489_);
lean_dec(v_h__1_1488_);
v___x_1499_ = lean_box(0);
v___x_1500_ = lean_apply_1(v_h__4_1491_, v___x_1499_);
return v___x_1500_;
}
default: 
{
lean_object* v___x_1501_; lean_object* v___x_1502_; 
lean_dec(v_h__4_1491_);
lean_dec(v_h__3_1490_);
lean_dec(v_h__2_1489_);
lean_dec(v_h__1_1488_);
v___x_1501_ = lean_box(0);
v___x_1502_ = lean_apply_1(v_h__5_1492_, v___x_1501_);
return v___x_1502_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__1_splitter___boxed(lean_object* v_motive_1503_, lean_object* v_x_1504_, lean_object* v_h__1_1505_, lean_object* v_h__2_1506_, lean_object* v_h__3_1507_, lean_object* v_h__4_1508_, lean_object* v_h__5_1509_){
_start:
{
uint8_t v_x_74__boxed_1510_; lean_object* v_res_1511_; 
v_x_74__boxed_1510_ = lean_unbox(v_x_1504_);
v_res_1511_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__1_splitter(v_motive_1503_, v_x_74__boxed_1510_, v_h__1_1505_, v_h__2_1506_, v_h__3_1507_, v_h__4_1508_, v_h__5_1509_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_containsGuarded_match__1_splitter___redArg(lean_object* v_x_1512_, lean_object* v_h__1_1513_, lean_object* v_h__2_1514_, lean_object* v_h__3_1515_, lean_object* v_h__4_1516_, lean_object* v_h__5_1517_, lean_object* v_h__6_1518_, lean_object* v_h__7_1519_, lean_object* v_h__8_1520_, lean_object* v_h__9_1521_, lean_object* v_h__10_1522_, lean_object* v_h__11_1523_, lean_object* v_h__12_1524_, lean_object* v_h__13_1525_, lean_object* v_h__14_1526_, lean_object* v_h__15_1527_, lean_object* v_h__16_1528_){
_start:
{
switch(lean_obj_tag(v_x_1512_))
{
case 0:
{
lean_object* v___x_1529_; 
lean_dec(v_h__16_1528_);
lean_dec(v_h__15_1527_);
lean_dec(v_h__14_1526_);
lean_dec(v_h__13_1525_);
lean_dec(v_h__12_1524_);
lean_dec(v_h__11_1523_);
lean_dec(v_h__10_1522_);
lean_dec(v_h__9_1521_);
lean_dec(v_h__8_1520_);
lean_dec(v_h__7_1519_);
lean_dec(v_h__6_1518_);
lean_dec(v_h__5_1517_);
lean_dec(v_h__4_1516_);
lean_dec(v_h__3_1515_);
lean_dec(v_h__1_1513_);
v___x_1529_ = lean_apply_1(v_h__2_1514_, lean_box(0));
return v___x_1529_;
}
case 1:
{
lean_object* v_f_1530_; lean_object* v___x_1531_; 
lean_dec(v_h__16_1528_);
lean_dec(v_h__15_1527_);
lean_dec(v_h__14_1526_);
lean_dec(v_h__13_1525_);
lean_dec(v_h__12_1524_);
lean_dec(v_h__11_1523_);
lean_dec(v_h__10_1522_);
lean_dec(v_h__9_1521_);
lean_dec(v_h__8_1520_);
lean_dec(v_h__7_1519_);
lean_dec(v_h__6_1518_);
lean_dec(v_h__5_1517_);
lean_dec(v_h__4_1516_);
lean_dec(v_h__2_1514_);
lean_dec(v_h__1_1513_);
v_f_1530_ = lean_ctor_get(v_x_1512_, 0);
lean_inc_ref(v_f_1530_);
lean_dec_ref_known(v_x_1512_, 1);
v___x_1531_ = lean_apply_2(v_h__3_1515_, lean_box(0), v_f_1530_);
return v___x_1531_;
}
case 2:
{
lean_object* v_s_1532_; lean_object* v___x_1533_; 
lean_dec(v_h__16_1528_);
lean_dec(v_h__15_1527_);
lean_dec(v_h__14_1526_);
lean_dec(v_h__13_1525_);
lean_dec(v_h__12_1524_);
lean_dec(v_h__11_1523_);
lean_dec(v_h__10_1522_);
lean_dec(v_h__9_1521_);
lean_dec(v_h__8_1520_);
lean_dec(v_h__7_1519_);
lean_dec(v_h__6_1518_);
lean_dec(v_h__5_1517_);
lean_dec(v_h__3_1515_);
lean_dec(v_h__2_1514_);
lean_dec(v_h__1_1513_);
v_s_1532_ = lean_ctor_get(v_x_1512_, 0);
lean_inc_ref(v_s_1532_);
lean_dec_ref_known(v_x_1512_, 1);
v___x_1533_ = lean_apply_2(v_h__4_1516_, lean_box(0), v_s_1532_);
return v___x_1533_;
}
case 3:
{
lean_object* v_id_1534_; lean_object* v_d_1535_; lean_object* v___x_1536_; 
lean_dec(v_h__16_1528_);
lean_dec(v_h__15_1527_);
lean_dec(v_h__14_1526_);
lean_dec(v_h__13_1525_);
lean_dec(v_h__12_1524_);
lean_dec(v_h__11_1523_);
lean_dec(v_h__10_1522_);
lean_dec(v_h__9_1521_);
lean_dec(v_h__8_1520_);
lean_dec(v_h__7_1519_);
lean_dec(v_h__6_1518_);
lean_dec(v_h__4_1516_);
lean_dec(v_h__3_1515_);
lean_dec(v_h__2_1514_);
lean_dec(v_h__1_1513_);
v_id_1534_ = lean_ctor_get(v_x_1512_, 0);
lean_inc(v_id_1534_);
v_d_1535_ = lean_ctor_get(v_x_1512_, 1);
lean_inc(v_d_1535_);
lean_dec_ref_known(v_x_1512_, 2);
v___x_1536_ = lean_apply_3(v_h__5_1517_, lean_box(0), v_id_1534_, v_d_1535_);
return v___x_1536_;
}
case 4:
{
lean_object* v_d_1537_; lean_object* v___x_1538_; 
lean_dec(v_h__16_1528_);
lean_dec(v_h__15_1527_);
lean_dec(v_h__14_1526_);
lean_dec(v_h__13_1525_);
lean_dec(v_h__12_1524_);
lean_dec(v_h__11_1523_);
lean_dec(v_h__10_1522_);
lean_dec(v_h__9_1521_);
lean_dec(v_h__8_1520_);
lean_dec(v_h__7_1519_);
lean_dec(v_h__5_1517_);
lean_dec(v_h__4_1516_);
lean_dec(v_h__3_1515_);
lean_dec(v_h__2_1514_);
lean_dec(v_h__1_1513_);
v_d_1537_ = lean_ctor_get(v_x_1512_, 0);
lean_inc(v_d_1537_);
lean_dec_ref_known(v_x_1512_, 1);
v___x_1538_ = lean_apply_2(v_h__6_1518_, lean_box(0), v_d_1537_);
return v___x_1538_;
}
case 5:
{
lean_object* v_d_1539_; lean_object* v___x_1540_; 
lean_dec(v_h__16_1528_);
lean_dec(v_h__15_1527_);
lean_dec(v_h__14_1526_);
lean_dec(v_h__13_1525_);
lean_dec(v_h__12_1524_);
lean_dec(v_h__11_1523_);
lean_dec(v_h__10_1522_);
lean_dec(v_h__9_1521_);
lean_dec(v_h__8_1520_);
lean_dec(v_h__6_1518_);
lean_dec(v_h__5_1517_);
lean_dec(v_h__4_1516_);
lean_dec(v_h__3_1515_);
lean_dec(v_h__2_1514_);
lean_dec(v_h__1_1513_);
v_d_1539_ = lean_ctor_get(v_x_1512_, 0);
lean_inc(v_d_1539_);
lean_dec_ref_known(v_x_1512_, 1);
v___x_1540_ = lean_apply_2(v_h__7_1519_, lean_box(0), v_d_1539_);
return v___x_1540_;
}
case 6:
{
lean_object* v_n_1541_; uint8_t v_isCumulative_1542_; lean_object* v_d_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
lean_dec(v_h__16_1528_);
lean_dec(v_h__15_1527_);
lean_dec(v_h__14_1526_);
lean_dec(v_h__13_1525_);
lean_dec(v_h__12_1524_);
lean_dec(v_h__11_1523_);
lean_dec(v_h__10_1522_);
lean_dec(v_h__9_1521_);
lean_dec(v_h__7_1519_);
lean_dec(v_h__6_1518_);
lean_dec(v_h__5_1517_);
lean_dec(v_h__4_1516_);
lean_dec(v_h__3_1515_);
lean_dec(v_h__2_1514_);
lean_dec(v_h__1_1513_);
v_n_1541_ = lean_ctor_get(v_x_1512_, 0);
lean_inc(v_n_1541_);
v_isCumulative_1542_ = lean_ctor_get_uint8(v_x_1512_, sizeof(void*)*2);
v_d_1543_ = lean_ctor_get(v_x_1512_, 1);
lean_inc(v_d_1543_);
lean_dec_ref_known(v_x_1512_, 2);
v___x_1544_ = lean_box(v_isCumulative_1542_);
v___x_1545_ = lean_apply_4(v_h__8_1520_, lean_box(0), v_n_1541_, v___x_1544_, v_d_1543_);
return v___x_1545_;
}
case 7:
{
lean_object* v_d_1546_; lean_object* v___x_1547_; 
lean_dec(v_h__16_1528_);
lean_dec(v_h__15_1527_);
lean_dec(v_h__14_1526_);
lean_dec(v_h__13_1525_);
lean_dec(v_h__12_1524_);
lean_dec(v_h__11_1523_);
lean_dec(v_h__10_1522_);
lean_dec(v_h__8_1520_);
lean_dec(v_h__7_1519_);
lean_dec(v_h__6_1518_);
lean_dec(v_h__5_1517_);
lean_dec(v_h__4_1516_);
lean_dec(v_h__3_1515_);
lean_dec(v_h__2_1514_);
lean_dec(v_h__1_1513_);
v_d_1546_ = lean_ctor_get(v_x_1512_, 0);
lean_inc(v_d_1546_);
lean_dec_ref_known(v_x_1512_, 1);
v___x_1547_ = lean_apply_2(v_h__9_1521_, lean_box(0), v_d_1546_);
return v___x_1547_;
}
case 8:
{
uint8_t v_onlyNonCumulative_1548_; lean_object* v_d_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
lean_dec(v_h__16_1528_);
lean_dec(v_h__15_1527_);
lean_dec(v_h__14_1526_);
lean_dec(v_h__13_1525_);
lean_dec(v_h__12_1524_);
lean_dec(v_h__11_1523_);
lean_dec(v_h__9_1521_);
lean_dec(v_h__8_1520_);
lean_dec(v_h__7_1519_);
lean_dec(v_h__6_1518_);
lean_dec(v_h__5_1517_);
lean_dec(v_h__4_1516_);
lean_dec(v_h__3_1515_);
lean_dec(v_h__2_1514_);
lean_dec(v_h__1_1513_);
v_onlyNonCumulative_1548_ = lean_ctor_get_uint8(v_x_1512_, sizeof(void*)*1);
v_d_1549_ = lean_ctor_get(v_x_1512_, 0);
lean_inc(v_d_1549_);
lean_dec_ref_known(v_x_1512_, 1);
v___x_1550_ = lean_box(v_onlyNonCumulative_1548_);
v___x_1551_ = lean_apply_3(v_h__10_1522_, lean_box(0), v___x_1550_, v_d_1549_);
return v___x_1551_;
}
case 9:
{
lean_object* v_d_1552_; lean_object* v___x_1553_; 
lean_dec(v_h__16_1528_);
lean_dec(v_h__15_1527_);
lean_dec(v_h__14_1526_);
lean_dec(v_h__13_1525_);
lean_dec(v_h__12_1524_);
lean_dec(v_h__10_1522_);
lean_dec(v_h__9_1521_);
lean_dec(v_h__8_1520_);
lean_dec(v_h__7_1519_);
lean_dec(v_h__6_1518_);
lean_dec(v_h__5_1517_);
lean_dec(v_h__4_1516_);
lean_dec(v_h__3_1515_);
lean_dec(v_h__2_1514_);
lean_dec(v_h__1_1513_);
v_d_1552_ = lean_ctor_get(v_x_1512_, 0);
lean_inc(v_d_1552_);
lean_dec_ref_known(v_x_1512_, 1);
v___x_1553_ = lean_apply_2(v_h__11_1523_, lean_box(0), v_d_1552_);
return v___x_1553_;
}
case 10:
{
lean_object* v_d_1554_; lean_object* v___x_1555_; 
lean_dec(v_h__16_1528_);
lean_dec(v_h__15_1527_);
lean_dec(v_h__14_1526_);
lean_dec(v_h__13_1525_);
lean_dec(v_h__11_1523_);
lean_dec(v_h__10_1522_);
lean_dec(v_h__9_1521_);
lean_dec(v_h__8_1520_);
lean_dec(v_h__7_1519_);
lean_dec(v_h__6_1518_);
lean_dec(v_h__5_1517_);
lean_dec(v_h__4_1516_);
lean_dec(v_h__3_1515_);
lean_dec(v_h__2_1514_);
lean_dec(v_h__1_1513_);
v_d_1554_ = lean_ctor_get(v_x_1512_, 0);
lean_inc(v_d_1554_);
lean_dec_ref_known(v_x_1512_, 1);
v___x_1555_ = lean_apply_2(v_h__12_1524_, lean_box(0), v_d_1554_);
return v___x_1555_;
}
case 11:
{
lean_object* v_d_1556_; lean_object* v___x_1557_; 
lean_dec(v_h__16_1528_);
lean_dec(v_h__15_1527_);
lean_dec(v_h__14_1526_);
lean_dec(v_h__12_1524_);
lean_dec(v_h__11_1523_);
lean_dec(v_h__10_1522_);
lean_dec(v_h__9_1521_);
lean_dec(v_h__8_1520_);
lean_dec(v_h__7_1519_);
lean_dec(v_h__6_1518_);
lean_dec(v_h__5_1517_);
lean_dec(v_h__4_1516_);
lean_dec(v_h__3_1515_);
lean_dec(v_h__2_1514_);
lean_dec(v_h__1_1513_);
v_d_1556_ = lean_ctor_get(v_x_1512_, 0);
lean_inc(v_d_1556_);
lean_dec_ref_known(v_x_1512_, 1);
v___x_1557_ = lean_apply_2(v_h__13_1525_, lean_box(0), v_d_1556_);
return v___x_1557_;
}
case 12:
{
lean_object* v_p_1558_; lean_object* v_d_1559_; lean_object* v___x_1560_; 
lean_dec(v_h__16_1528_);
lean_dec(v_h__15_1527_);
lean_dec(v_h__14_1526_);
lean_dec(v_h__13_1525_);
lean_dec(v_h__12_1524_);
lean_dec(v_h__11_1523_);
lean_dec(v_h__10_1522_);
lean_dec(v_h__9_1521_);
lean_dec(v_h__8_1520_);
lean_dec(v_h__7_1519_);
lean_dec(v_h__6_1518_);
lean_dec(v_h__5_1517_);
lean_dec(v_h__4_1516_);
lean_dec(v_h__3_1515_);
lean_dec(v_h__2_1514_);
v_p_1558_ = lean_ctor_get(v_x_1512_, 0);
lean_inc_ref(v_p_1558_);
v_d_1559_ = lean_ctor_get(v_x_1512_, 1);
lean_inc(v_d_1559_);
lean_dec_ref_known(v_x_1512_, 2);
v___x_1560_ = lean_apply_3(v_h__1_1513_, lean_box(0), v_p_1558_, v_d_1559_);
return v___x_1560_;
}
case 13:
{
lean_object* v_cost_1561_; lean_object* v_d_1562_; lean_object* v___x_1563_; 
lean_dec(v_h__16_1528_);
lean_dec(v_h__15_1527_);
lean_dec(v_h__13_1525_);
lean_dec(v_h__12_1524_);
lean_dec(v_h__11_1523_);
lean_dec(v_h__10_1522_);
lean_dec(v_h__9_1521_);
lean_dec(v_h__8_1520_);
lean_dec(v_h__7_1519_);
lean_dec(v_h__6_1518_);
lean_dec(v_h__5_1517_);
lean_dec(v_h__4_1516_);
lean_dec(v_h__3_1515_);
lean_dec(v_h__2_1514_);
lean_dec(v_h__1_1513_);
v_cost_1561_ = lean_ctor_get(v_x_1512_, 0);
lean_inc(v_cost_1561_);
v_d_1562_ = lean_ctor_get(v_x_1512_, 1);
lean_inc(v_d_1562_);
lean_dec_ref_known(v_x_1512_, 2);
v___x_1563_ = lean_apply_3(v_h__14_1526_, lean_box(0), v_cost_1561_, v_d_1562_);
return v___x_1563_;
}
case 14:
{
lean_object* v_a_1564_; lean_object* v_b_1565_; lean_object* v___x_1566_; 
lean_dec(v_h__16_1528_);
lean_dec(v_h__14_1526_);
lean_dec(v_h__13_1525_);
lean_dec(v_h__12_1524_);
lean_dec(v_h__11_1523_);
lean_dec(v_h__10_1522_);
lean_dec(v_h__9_1521_);
lean_dec(v_h__8_1520_);
lean_dec(v_h__7_1519_);
lean_dec(v_h__6_1518_);
lean_dec(v_h__5_1517_);
lean_dec(v_h__4_1516_);
lean_dec(v_h__3_1515_);
lean_dec(v_h__2_1514_);
lean_dec(v_h__1_1513_);
v_a_1564_ = lean_ctor_get(v_x_1512_, 0);
lean_inc(v_a_1564_);
v_b_1565_ = lean_ctor_get(v_x_1512_, 1);
lean_inc(v_b_1565_);
lean_dec_ref_known(v_x_1512_, 2);
v___x_1566_ = lean_apply_3(v_h__15_1527_, lean_box(0), v_a_1564_, v_b_1565_);
return v___x_1566_;
}
default: 
{
lean_object* v_a_1567_; lean_object* v_b_1568_; lean_object* v___x_1569_; 
lean_dec(v_h__15_1527_);
lean_dec(v_h__14_1526_);
lean_dec(v_h__13_1525_);
lean_dec(v_h__12_1524_);
lean_dec(v_h__11_1523_);
lean_dec(v_h__10_1522_);
lean_dec(v_h__9_1521_);
lean_dec(v_h__8_1520_);
lean_dec(v_h__7_1519_);
lean_dec(v_h__6_1518_);
lean_dec(v_h__5_1517_);
lean_dec(v_h__4_1516_);
lean_dec(v_h__3_1515_);
lean_dec(v_h__2_1514_);
lean_dec(v_h__1_1513_);
v_a_1567_ = lean_ctor_get(v_x_1512_, 0);
lean_inc(v_a_1567_);
v_b_1568_ = lean_ctor_get(v_x_1512_, 1);
lean_inc(v_b_1568_);
lean_dec_ref_known(v_x_1512_, 2);
v___x_1569_ = lean_apply_3(v_h__16_1528_, lean_box(0), v_a_1567_, v_b_1568_);
return v___x_1569_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_containsGuarded_match__1_splitter___redArg___boxed(lean_object** _args){
lean_object* v_x_1570_ = _args[0];
lean_object* v_h__1_1571_ = _args[1];
lean_object* v_h__2_1572_ = _args[2];
lean_object* v_h__3_1573_ = _args[3];
lean_object* v_h__4_1574_ = _args[4];
lean_object* v_h__5_1575_ = _args[5];
lean_object* v_h__6_1576_ = _args[6];
lean_object* v_h__7_1577_ = _args[7];
lean_object* v_h__8_1578_ = _args[8];
lean_object* v_h__9_1579_ = _args[9];
lean_object* v_h__10_1580_ = _args[10];
lean_object* v_h__11_1581_ = _args[11];
lean_object* v_h__12_1582_ = _args[12];
lean_object* v_h__13_1583_ = _args[13];
lean_object* v_h__14_1584_ = _args[14];
lean_object* v_h__15_1585_ = _args[15];
lean_object* v_h__16_1586_ = _args[16];
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_containsGuarded_match__1_splitter___redArg(v_x_1570_, v_h__1_1571_, v_h__2_1572_, v_h__3_1573_, v_h__4_1574_, v_h__5_1575_, v_h__6_1576_, v_h__7_1577_, v_h__8_1578_, v_h__9_1579_, v_h__10_1580_, v_h__11_1581_, v_h__12_1582_, v_h__13_1583_, v_h__14_1584_, v_h__15_1585_, v_h__16_1586_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_containsGuarded_match__1_splitter(lean_object* v_motive_1588_, lean_object* v_x_1589_, lean_object* v_x_1590_, lean_object* v_h__1_1591_, lean_object* v_h__2_1592_, lean_object* v_h__3_1593_, lean_object* v_h__4_1594_, lean_object* v_h__5_1595_, lean_object* v_h__6_1596_, lean_object* v_h__7_1597_, lean_object* v_h__8_1598_, lean_object* v_h__9_1599_, lean_object* v_h__10_1600_, lean_object* v_h__11_1601_, lean_object* v_h__12_1602_, lean_object* v_h__13_1603_, lean_object* v_h__14_1604_, lean_object* v_h__15_1605_, lean_object* v_h__16_1606_){
_start:
{
switch(lean_obj_tag(v_x_1590_))
{
case 0:
{
lean_object* v___x_1607_; 
lean_dec(v_h__16_1606_);
lean_dec(v_h__15_1605_);
lean_dec(v_h__14_1604_);
lean_dec(v_h__13_1603_);
lean_dec(v_h__12_1602_);
lean_dec(v_h__11_1601_);
lean_dec(v_h__10_1600_);
lean_dec(v_h__9_1599_);
lean_dec(v_h__8_1598_);
lean_dec(v_h__7_1597_);
lean_dec(v_h__6_1596_);
lean_dec(v_h__5_1595_);
lean_dec(v_h__4_1594_);
lean_dec(v_h__3_1593_);
lean_dec(v_h__1_1591_);
v___x_1607_ = lean_apply_1(v_h__2_1592_, lean_box(0));
return v___x_1607_;
}
case 1:
{
lean_object* v_f_1608_; lean_object* v___x_1609_; 
lean_dec(v_h__16_1606_);
lean_dec(v_h__15_1605_);
lean_dec(v_h__14_1604_);
lean_dec(v_h__13_1603_);
lean_dec(v_h__12_1602_);
lean_dec(v_h__11_1601_);
lean_dec(v_h__10_1600_);
lean_dec(v_h__9_1599_);
lean_dec(v_h__8_1598_);
lean_dec(v_h__7_1597_);
lean_dec(v_h__6_1596_);
lean_dec(v_h__5_1595_);
lean_dec(v_h__4_1594_);
lean_dec(v_h__2_1592_);
lean_dec(v_h__1_1591_);
v_f_1608_ = lean_ctor_get(v_x_1590_, 0);
lean_inc_ref(v_f_1608_);
lean_dec_ref_known(v_x_1590_, 1);
v___x_1609_ = lean_apply_2(v_h__3_1593_, lean_box(0), v_f_1608_);
return v___x_1609_;
}
case 2:
{
lean_object* v_s_1610_; lean_object* v___x_1611_; 
lean_dec(v_h__16_1606_);
lean_dec(v_h__15_1605_);
lean_dec(v_h__14_1604_);
lean_dec(v_h__13_1603_);
lean_dec(v_h__12_1602_);
lean_dec(v_h__11_1601_);
lean_dec(v_h__10_1600_);
lean_dec(v_h__9_1599_);
lean_dec(v_h__8_1598_);
lean_dec(v_h__7_1597_);
lean_dec(v_h__6_1596_);
lean_dec(v_h__5_1595_);
lean_dec(v_h__3_1593_);
lean_dec(v_h__2_1592_);
lean_dec(v_h__1_1591_);
v_s_1610_ = lean_ctor_get(v_x_1590_, 0);
lean_inc_ref(v_s_1610_);
lean_dec_ref_known(v_x_1590_, 1);
v___x_1611_ = lean_apply_2(v_h__4_1594_, lean_box(0), v_s_1610_);
return v___x_1611_;
}
case 3:
{
lean_object* v_id_1612_; lean_object* v_d_1613_; lean_object* v___x_1614_; 
lean_dec(v_h__16_1606_);
lean_dec(v_h__15_1605_);
lean_dec(v_h__14_1604_);
lean_dec(v_h__13_1603_);
lean_dec(v_h__12_1602_);
lean_dec(v_h__11_1601_);
lean_dec(v_h__10_1600_);
lean_dec(v_h__9_1599_);
lean_dec(v_h__8_1598_);
lean_dec(v_h__7_1597_);
lean_dec(v_h__6_1596_);
lean_dec(v_h__4_1594_);
lean_dec(v_h__3_1593_);
lean_dec(v_h__2_1592_);
lean_dec(v_h__1_1591_);
v_id_1612_ = lean_ctor_get(v_x_1590_, 0);
lean_inc(v_id_1612_);
v_d_1613_ = lean_ctor_get(v_x_1590_, 1);
lean_inc(v_d_1613_);
lean_dec_ref_known(v_x_1590_, 2);
v___x_1614_ = lean_apply_3(v_h__5_1595_, lean_box(0), v_id_1612_, v_d_1613_);
return v___x_1614_;
}
case 4:
{
lean_object* v_d_1615_; lean_object* v___x_1616_; 
lean_dec(v_h__16_1606_);
lean_dec(v_h__15_1605_);
lean_dec(v_h__14_1604_);
lean_dec(v_h__13_1603_);
lean_dec(v_h__12_1602_);
lean_dec(v_h__11_1601_);
lean_dec(v_h__10_1600_);
lean_dec(v_h__9_1599_);
lean_dec(v_h__8_1598_);
lean_dec(v_h__7_1597_);
lean_dec(v_h__5_1595_);
lean_dec(v_h__4_1594_);
lean_dec(v_h__3_1593_);
lean_dec(v_h__2_1592_);
lean_dec(v_h__1_1591_);
v_d_1615_ = lean_ctor_get(v_x_1590_, 0);
lean_inc(v_d_1615_);
lean_dec_ref_known(v_x_1590_, 1);
v___x_1616_ = lean_apply_2(v_h__6_1596_, lean_box(0), v_d_1615_);
return v___x_1616_;
}
case 5:
{
lean_object* v_d_1617_; lean_object* v___x_1618_; 
lean_dec(v_h__16_1606_);
lean_dec(v_h__15_1605_);
lean_dec(v_h__14_1604_);
lean_dec(v_h__13_1603_);
lean_dec(v_h__12_1602_);
lean_dec(v_h__11_1601_);
lean_dec(v_h__10_1600_);
lean_dec(v_h__9_1599_);
lean_dec(v_h__8_1598_);
lean_dec(v_h__6_1596_);
lean_dec(v_h__5_1595_);
lean_dec(v_h__4_1594_);
lean_dec(v_h__3_1593_);
lean_dec(v_h__2_1592_);
lean_dec(v_h__1_1591_);
v_d_1617_ = lean_ctor_get(v_x_1590_, 0);
lean_inc(v_d_1617_);
lean_dec_ref_known(v_x_1590_, 1);
v___x_1618_ = lean_apply_2(v_h__7_1597_, lean_box(0), v_d_1617_);
return v___x_1618_;
}
case 6:
{
lean_object* v_n_1619_; uint8_t v_isCumulative_1620_; lean_object* v_d_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
lean_dec(v_h__16_1606_);
lean_dec(v_h__15_1605_);
lean_dec(v_h__14_1604_);
lean_dec(v_h__13_1603_);
lean_dec(v_h__12_1602_);
lean_dec(v_h__11_1601_);
lean_dec(v_h__10_1600_);
lean_dec(v_h__9_1599_);
lean_dec(v_h__7_1597_);
lean_dec(v_h__6_1596_);
lean_dec(v_h__5_1595_);
lean_dec(v_h__4_1594_);
lean_dec(v_h__3_1593_);
lean_dec(v_h__2_1592_);
lean_dec(v_h__1_1591_);
v_n_1619_ = lean_ctor_get(v_x_1590_, 0);
lean_inc(v_n_1619_);
v_isCumulative_1620_ = lean_ctor_get_uint8(v_x_1590_, sizeof(void*)*2);
v_d_1621_ = lean_ctor_get(v_x_1590_, 1);
lean_inc(v_d_1621_);
lean_dec_ref_known(v_x_1590_, 2);
v___x_1622_ = lean_box(v_isCumulative_1620_);
v___x_1623_ = lean_apply_4(v_h__8_1598_, lean_box(0), v_n_1619_, v___x_1622_, v_d_1621_);
return v___x_1623_;
}
case 7:
{
lean_object* v_d_1624_; lean_object* v___x_1625_; 
lean_dec(v_h__16_1606_);
lean_dec(v_h__15_1605_);
lean_dec(v_h__14_1604_);
lean_dec(v_h__13_1603_);
lean_dec(v_h__12_1602_);
lean_dec(v_h__11_1601_);
lean_dec(v_h__10_1600_);
lean_dec(v_h__8_1598_);
lean_dec(v_h__7_1597_);
lean_dec(v_h__6_1596_);
lean_dec(v_h__5_1595_);
lean_dec(v_h__4_1594_);
lean_dec(v_h__3_1593_);
lean_dec(v_h__2_1592_);
lean_dec(v_h__1_1591_);
v_d_1624_ = lean_ctor_get(v_x_1590_, 0);
lean_inc(v_d_1624_);
lean_dec_ref_known(v_x_1590_, 1);
v___x_1625_ = lean_apply_2(v_h__9_1599_, lean_box(0), v_d_1624_);
return v___x_1625_;
}
case 8:
{
uint8_t v_onlyNonCumulative_1626_; lean_object* v_d_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
lean_dec(v_h__16_1606_);
lean_dec(v_h__15_1605_);
lean_dec(v_h__14_1604_);
lean_dec(v_h__13_1603_);
lean_dec(v_h__12_1602_);
lean_dec(v_h__11_1601_);
lean_dec(v_h__9_1599_);
lean_dec(v_h__8_1598_);
lean_dec(v_h__7_1597_);
lean_dec(v_h__6_1596_);
lean_dec(v_h__5_1595_);
lean_dec(v_h__4_1594_);
lean_dec(v_h__3_1593_);
lean_dec(v_h__2_1592_);
lean_dec(v_h__1_1591_);
v_onlyNonCumulative_1626_ = lean_ctor_get_uint8(v_x_1590_, sizeof(void*)*1);
v_d_1627_ = lean_ctor_get(v_x_1590_, 0);
lean_inc(v_d_1627_);
lean_dec_ref_known(v_x_1590_, 1);
v___x_1628_ = lean_box(v_onlyNonCumulative_1626_);
v___x_1629_ = lean_apply_3(v_h__10_1600_, lean_box(0), v___x_1628_, v_d_1627_);
return v___x_1629_;
}
case 9:
{
lean_object* v_d_1630_; lean_object* v___x_1631_; 
lean_dec(v_h__16_1606_);
lean_dec(v_h__15_1605_);
lean_dec(v_h__14_1604_);
lean_dec(v_h__13_1603_);
lean_dec(v_h__12_1602_);
lean_dec(v_h__10_1600_);
lean_dec(v_h__9_1599_);
lean_dec(v_h__8_1598_);
lean_dec(v_h__7_1597_);
lean_dec(v_h__6_1596_);
lean_dec(v_h__5_1595_);
lean_dec(v_h__4_1594_);
lean_dec(v_h__3_1593_);
lean_dec(v_h__2_1592_);
lean_dec(v_h__1_1591_);
v_d_1630_ = lean_ctor_get(v_x_1590_, 0);
lean_inc(v_d_1630_);
lean_dec_ref_known(v_x_1590_, 1);
v___x_1631_ = lean_apply_2(v_h__11_1601_, lean_box(0), v_d_1630_);
return v___x_1631_;
}
case 10:
{
lean_object* v_d_1632_; lean_object* v___x_1633_; 
lean_dec(v_h__16_1606_);
lean_dec(v_h__15_1605_);
lean_dec(v_h__14_1604_);
lean_dec(v_h__13_1603_);
lean_dec(v_h__11_1601_);
lean_dec(v_h__10_1600_);
lean_dec(v_h__9_1599_);
lean_dec(v_h__8_1598_);
lean_dec(v_h__7_1597_);
lean_dec(v_h__6_1596_);
lean_dec(v_h__5_1595_);
lean_dec(v_h__4_1594_);
lean_dec(v_h__3_1593_);
lean_dec(v_h__2_1592_);
lean_dec(v_h__1_1591_);
v_d_1632_ = lean_ctor_get(v_x_1590_, 0);
lean_inc(v_d_1632_);
lean_dec_ref_known(v_x_1590_, 1);
v___x_1633_ = lean_apply_2(v_h__12_1602_, lean_box(0), v_d_1632_);
return v___x_1633_;
}
case 11:
{
lean_object* v_d_1634_; lean_object* v___x_1635_; 
lean_dec(v_h__16_1606_);
lean_dec(v_h__15_1605_);
lean_dec(v_h__14_1604_);
lean_dec(v_h__12_1602_);
lean_dec(v_h__11_1601_);
lean_dec(v_h__10_1600_);
lean_dec(v_h__9_1599_);
lean_dec(v_h__8_1598_);
lean_dec(v_h__7_1597_);
lean_dec(v_h__6_1596_);
lean_dec(v_h__5_1595_);
lean_dec(v_h__4_1594_);
lean_dec(v_h__3_1593_);
lean_dec(v_h__2_1592_);
lean_dec(v_h__1_1591_);
v_d_1634_ = lean_ctor_get(v_x_1590_, 0);
lean_inc(v_d_1634_);
lean_dec_ref_known(v_x_1590_, 1);
v___x_1635_ = lean_apply_2(v_h__13_1603_, lean_box(0), v_d_1634_);
return v___x_1635_;
}
case 12:
{
lean_object* v_p_1636_; lean_object* v_d_1637_; lean_object* v___x_1638_; 
lean_dec(v_h__16_1606_);
lean_dec(v_h__15_1605_);
lean_dec(v_h__14_1604_);
lean_dec(v_h__13_1603_);
lean_dec(v_h__12_1602_);
lean_dec(v_h__11_1601_);
lean_dec(v_h__10_1600_);
lean_dec(v_h__9_1599_);
lean_dec(v_h__8_1598_);
lean_dec(v_h__7_1597_);
lean_dec(v_h__6_1596_);
lean_dec(v_h__5_1595_);
lean_dec(v_h__4_1594_);
lean_dec(v_h__3_1593_);
lean_dec(v_h__2_1592_);
v_p_1636_ = lean_ctor_get(v_x_1590_, 0);
lean_inc_ref(v_p_1636_);
v_d_1637_ = lean_ctor_get(v_x_1590_, 1);
lean_inc(v_d_1637_);
lean_dec_ref_known(v_x_1590_, 2);
v___x_1638_ = lean_apply_3(v_h__1_1591_, lean_box(0), v_p_1636_, v_d_1637_);
return v___x_1638_;
}
case 13:
{
lean_object* v_cost_1639_; lean_object* v_d_1640_; lean_object* v___x_1641_; 
lean_dec(v_h__16_1606_);
lean_dec(v_h__15_1605_);
lean_dec(v_h__13_1603_);
lean_dec(v_h__12_1602_);
lean_dec(v_h__11_1601_);
lean_dec(v_h__10_1600_);
lean_dec(v_h__9_1599_);
lean_dec(v_h__8_1598_);
lean_dec(v_h__7_1597_);
lean_dec(v_h__6_1596_);
lean_dec(v_h__5_1595_);
lean_dec(v_h__4_1594_);
lean_dec(v_h__3_1593_);
lean_dec(v_h__2_1592_);
lean_dec(v_h__1_1591_);
v_cost_1639_ = lean_ctor_get(v_x_1590_, 0);
lean_inc(v_cost_1639_);
v_d_1640_ = lean_ctor_get(v_x_1590_, 1);
lean_inc(v_d_1640_);
lean_dec_ref_known(v_x_1590_, 2);
v___x_1641_ = lean_apply_3(v_h__14_1604_, lean_box(0), v_cost_1639_, v_d_1640_);
return v___x_1641_;
}
case 14:
{
lean_object* v_a_1642_; lean_object* v_b_1643_; lean_object* v___x_1644_; 
lean_dec(v_h__16_1606_);
lean_dec(v_h__14_1604_);
lean_dec(v_h__13_1603_);
lean_dec(v_h__12_1602_);
lean_dec(v_h__11_1601_);
lean_dec(v_h__10_1600_);
lean_dec(v_h__9_1599_);
lean_dec(v_h__8_1598_);
lean_dec(v_h__7_1597_);
lean_dec(v_h__6_1596_);
lean_dec(v_h__5_1595_);
lean_dec(v_h__4_1594_);
lean_dec(v_h__3_1593_);
lean_dec(v_h__2_1592_);
lean_dec(v_h__1_1591_);
v_a_1642_ = lean_ctor_get(v_x_1590_, 0);
lean_inc(v_a_1642_);
v_b_1643_ = lean_ctor_get(v_x_1590_, 1);
lean_inc(v_b_1643_);
lean_dec_ref_known(v_x_1590_, 2);
v___x_1644_ = lean_apply_3(v_h__15_1605_, lean_box(0), v_a_1642_, v_b_1643_);
return v___x_1644_;
}
default: 
{
lean_object* v_a_1645_; lean_object* v_b_1646_; lean_object* v___x_1647_; 
lean_dec(v_h__15_1605_);
lean_dec(v_h__14_1604_);
lean_dec(v_h__13_1603_);
lean_dec(v_h__12_1602_);
lean_dec(v_h__11_1601_);
lean_dec(v_h__10_1600_);
lean_dec(v_h__9_1599_);
lean_dec(v_h__8_1598_);
lean_dec(v_h__7_1597_);
lean_dec(v_h__6_1596_);
lean_dec(v_h__5_1595_);
lean_dec(v_h__4_1594_);
lean_dec(v_h__3_1593_);
lean_dec(v_h__2_1592_);
lean_dec(v_h__1_1591_);
v_a_1645_ = lean_ctor_get(v_x_1590_, 0);
lean_inc(v_a_1645_);
v_b_1646_ = lean_ctor_get(v_x_1590_, 1);
lean_inc(v_b_1646_);
lean_dec_ref_known(v_x_1590_, 2);
v___x_1647_ = lean_apply_3(v_h__16_1606_, lean_box(0), v_a_1645_, v_b_1646_);
return v___x_1647_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_containsGuarded_match__1_splitter___boxed(lean_object** _args){
lean_object* v_motive_1648_ = _args[0];
lean_object* v_x_1649_ = _args[1];
lean_object* v_x_1650_ = _args[2];
lean_object* v_h__1_1651_ = _args[3];
lean_object* v_h__2_1652_ = _args[4];
lean_object* v_h__3_1653_ = _args[5];
lean_object* v_h__4_1654_ = _args[6];
lean_object* v_h__5_1655_ = _args[7];
lean_object* v_h__6_1656_ = _args[8];
lean_object* v_h__7_1657_ = _args[9];
lean_object* v_h__8_1658_ = _args[10];
lean_object* v_h__9_1659_ = _args[11];
lean_object* v_h__10_1660_ = _args[12];
lean_object* v_h__11_1661_ = _args[13];
lean_object* v_h__12_1662_ = _args[14];
lean_object* v_h__13_1663_ = _args[15];
lean_object* v_h__14_1664_ = _args[16];
lean_object* v_h__15_1665_ = _args[17];
lean_object* v_h__16_1666_ = _args[18];
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_containsGuarded_match__1_splitter(v_motive_1648_, v_x_1649_, v_x_1650_, v_h__1_1651_, v_h__2_1652_, v_h__3_1653_, v_h__4_1654_, v_h__5_1655_, v_h__6_1656_, v_h__7_1657_, v_h__8_1658_, v_h__9_1659_, v_h__10_1660_, v_h__11_1661_, v_h__12_1662_, v_h__13_1663_, v_h__14_1664_, v_h__15_1665_, v_h__16_1666_);
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
v_isCumulative_1697_ = lean_ctor_get_uint8(v_t_1668_, sizeof(void*)*3 + 8);
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
v_onlyNonCumulative_1703_ = lean_ctor_get_uint8(v_t_1668_, sizeof(void*)*2 + 8);
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
v_isCumulative_1774_ = lean_ctor_get_uint8(v_t_1745_, sizeof(void*)*3 + 8);
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
v_onlyNonCumulative_1780_ = lean_ctor_get_uint8(v_t_1745_, sizeof(void*)*2 + 8);
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
uint16_t v___x_1833_; lean_object* v___x_1834_; uint8_t v___y_1836_; uint8_t v___y_1837_; lean_object* v___x_1842_; lean_object* v___x_1843_; uint8_t v___x_1844_; uint8_t v___y_1846_; 
v___x_1833_ = l_Lean_Fmt_newlineFailureSet;
v___x_1834_ = ((lean_object*)(l_Lean_Fmt_Doc_newline___override___redArg___closed__0));
v___x_1842_ = lean_string_utf8_byte_size(v_f_1832_);
v___x_1843_ = lean_unsigned_to_nat(0u);
v___x_1844_ = lean_nat_dec_eq(v___x_1842_, v___x_1843_);
if (v___x_1844_ == 0)
{
uint8_t v___x_1849_; 
v___x_1849_ = 2;
v___y_1846_ = v___x_1849_;
goto v___jp_1845_;
}
else
{
uint8_t v___x_1850_; 
v___x_1850_ = 1;
v___y_1846_ = v___x_1850_;
goto v___jp_1845_;
}
v___jp_1835_:
{
uint8_t v___x_1838_; uint16_t v___x_1839_; uint8_t v___x_1840_; lean_object* v___x_1841_; 
v___x_1838_ = 1;
v___x_1839_ = lean_uint16_once(&l_Lean_Fmt_Doc_newline___override___redArg___closed__1, &l_Lean_Fmt_Doc_newline___override___redArg___closed__1_once, _init_l_Lean_Fmt_Doc_newline___override___redArg___closed__1);
v___x_1840_ = 0;
v___x_1841_ = lean_alloc_ctor(1, 2, 8);
lean_ctor_set(v___x_1841_, 0, v___x_1834_);
lean_ctor_set(v___x_1841_, 1, v_f_1832_);
lean_ctor_set_uint16(v___x_1841_, sizeof(void*)*2, v___x_1833_);
lean_ctor_set_uint8(v___x_1841_, sizeof(void*)*2 + 4, v___y_1836_);
lean_ctor_set_uint8(v___x_1841_, sizeof(void*)*2 + 5, v___y_1837_);
lean_ctor_set_uint8(v___x_1841_, sizeof(void*)*2 + 6, v___x_1838_);
lean_ctor_set_uint16(v___x_1841_, sizeof(void*)*2 + 2, v___x_1839_);
lean_ctor_set_uint8(v___x_1841_, sizeof(void*)*2 + 7, v___x_1840_);
return v___x_1841_;
}
v___jp_1845_:
{
if (v___x_1844_ == 0)
{
uint8_t v___x_1847_; 
v___x_1847_ = 0;
v___y_1836_ = v___y_1846_;
v___y_1837_ = v___x_1847_;
goto v___jp_1835_;
}
else
{
uint8_t v___x_1848_; 
v___x_1848_ = 1;
v___y_1836_ = v___y_1846_;
v___y_1837_ = v___x_1848_;
goto v___jp_1835_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_newline___override(lean_object* v_00_u03c4_1851_, lean_object* v_f_1852_){
_start:
{
lean_object* v___x_1853_; 
v___x_1853_ = l_Lean_Fmt_Doc_newline___override___redArg(v_f_1852_);
return v___x_1853_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_atomicness___override___redArg(lean_object* v_x_1854_){
_start:
{
switch(lean_obj_tag(v_x_1854_))
{
case 0:
{
uint8_t v___x_1855_; 
v___x_1855_ = 0;
return v___x_1855_;
}
case 3:
{
uint8_t v_atomicness_1856_; 
v_atomicness_1856_ = lean_ctor_get_uint8(v_x_1854_, sizeof(void*)*3 + 6);
return v_atomicness_1856_;
}
case 6:
{
uint8_t v_atomicness_1857_; 
v_atomicness_1857_ = lean_ctor_get_uint8(v_x_1854_, sizeof(void*)*3 + 6);
return v_atomicness_1857_;
}
case 12:
{
uint8_t v_atomicness_1858_; 
v_atomicness_1858_ = lean_ctor_get_uint8(v_x_1854_, sizeof(void*)*3 + 6);
return v_atomicness_1858_;
}
case 13:
{
uint8_t v_atomicness_1859_; 
v_atomicness_1859_ = lean_ctor_get_uint8(v_x_1854_, sizeof(void*)*3 + 6);
return v_atomicness_1859_;
}
case 14:
{
uint8_t v_atomicness_1860_; 
v_atomicness_1860_ = lean_ctor_get_uint8(v_x_1854_, sizeof(void*)*3 + 6);
return v_atomicness_1860_;
}
case 15:
{
uint8_t v_atomicness_1861_; 
v_atomicness_1861_ = lean_ctor_get_uint8(v_x_1854_, sizeof(void*)*3 + 6);
return v_atomicness_1861_;
}
default: 
{
uint8_t v_atomicness_1862_; 
v_atomicness_1862_ = lean_ctor_get_uint8(v_x_1854_, sizeof(void*)*2 + 6);
return v_atomicness_1862_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_atomicness___override___redArg___boxed(lean_object* v_x_1863_){
_start:
{
uint8_t v_res_1864_; lean_object* v_r_1865_; 
v_res_1864_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_x_1863_);
lean_dec(v_x_1863_);
v_r_1865_ = lean_box(v_res_1864_);
return v_r_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(lean_object* v_x_1866_){
_start:
{
if (lean_obj_tag(v_x_1866_) == 0)
{
lean_object* v___x_1867_; 
v___x_1867_ = lean_box(0);
return v___x_1867_;
}
else
{
lean_object* v_maxNewlineCount_x3f_1868_; 
v_maxNewlineCount_x3f_1868_ = lean_ctor_get(v_x_1866_, 0);
lean_inc(v_maxNewlineCount_x3f_1868_);
return v_maxNewlineCount_x3f_1868_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg___boxed(lean_object* v_x_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_x_1869_);
lean_dec(v_x_1869_);
return v_res_1870_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(lean_object* v_x_1871_){
_start:
{
switch(lean_obj_tag(v_x_1871_))
{
case 0:
{
uint8_t v___x_1872_; 
v___x_1872_ = 1;
return v___x_1872_;
}
case 3:
{
uint8_t v_alwaysNonEmptiness_1873_; 
v_alwaysNonEmptiness_1873_ = lean_ctor_get_uint8(v_x_1871_, sizeof(void*)*3 + 5);
return v_alwaysNonEmptiness_1873_;
}
case 6:
{
uint8_t v_alwaysNonEmptiness_1874_; 
v_alwaysNonEmptiness_1874_ = lean_ctor_get_uint8(v_x_1871_, sizeof(void*)*3 + 5);
return v_alwaysNonEmptiness_1874_;
}
case 12:
{
uint8_t v_alwaysNonEmptiness_1875_; 
v_alwaysNonEmptiness_1875_ = lean_ctor_get_uint8(v_x_1871_, sizeof(void*)*3 + 5);
return v_alwaysNonEmptiness_1875_;
}
case 13:
{
uint8_t v_alwaysNonEmptiness_1876_; 
v_alwaysNonEmptiness_1876_ = lean_ctor_get_uint8(v_x_1871_, sizeof(void*)*3 + 5);
return v_alwaysNonEmptiness_1876_;
}
case 14:
{
uint8_t v_alwaysNonEmptiness_1877_; 
v_alwaysNonEmptiness_1877_ = lean_ctor_get_uint8(v_x_1871_, sizeof(void*)*3 + 5);
return v_alwaysNonEmptiness_1877_;
}
case 15:
{
uint8_t v_alwaysNonEmptiness_1878_; 
v_alwaysNonEmptiness_1878_ = lean_ctor_get_uint8(v_x_1871_, sizeof(void*)*3 + 5);
return v_alwaysNonEmptiness_1878_;
}
default: 
{
uint8_t v_alwaysNonEmptiness_1879_; 
v_alwaysNonEmptiness_1879_ = lean_ctor_get_uint8(v_x_1871_, sizeof(void*)*2 + 5);
return v_alwaysNonEmptiness_1879_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg___boxed(lean_object* v_x_1880_){
_start:
{
uint8_t v_res_1881_; lean_object* v_r_1882_; 
v_res_1881_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_x_1880_);
lean_dec(v_x_1880_);
v_r_1882_ = lean_box(v_res_1881_);
return v_r_1882_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_Doc_neverFailsSet___override___redArg(lean_object* v_x_1883_){
_start:
{
switch(lean_obj_tag(v_x_1883_))
{
case 0:
{
uint16_t v___x_1884_; 
v___x_1884_ = 0;
return v___x_1884_;
}
case 3:
{
uint16_t v_neverFailsSet_1885_; 
v_neverFailsSet_1885_ = lean_ctor_get_uint16(v_x_1883_, sizeof(void*)*3 + 2);
return v_neverFailsSet_1885_;
}
case 6:
{
uint16_t v_neverFailsSet_1886_; 
v_neverFailsSet_1886_ = lean_ctor_get_uint16(v_x_1883_, sizeof(void*)*3 + 2);
return v_neverFailsSet_1886_;
}
case 12:
{
uint16_t v_neverFailsSet_1887_; 
v_neverFailsSet_1887_ = lean_ctor_get_uint16(v_x_1883_, sizeof(void*)*3 + 2);
return v_neverFailsSet_1887_;
}
case 13:
{
uint16_t v_neverFailsSet_1888_; 
v_neverFailsSet_1888_ = lean_ctor_get_uint16(v_x_1883_, sizeof(void*)*3 + 2);
return v_neverFailsSet_1888_;
}
case 14:
{
uint16_t v_neverFailsSet_1889_; 
v_neverFailsSet_1889_ = lean_ctor_get_uint16(v_x_1883_, sizeof(void*)*3 + 2);
return v_neverFailsSet_1889_;
}
case 15:
{
uint16_t v_neverFailsSet_1890_; 
v_neverFailsSet_1890_ = lean_ctor_get_uint16(v_x_1883_, sizeof(void*)*3 + 2);
return v_neverFailsSet_1890_;
}
default: 
{
uint16_t v_neverFailsSet_1891_; 
v_neverFailsSet_1891_ = lean_ctor_get_uint16(v_x_1883_, sizeof(void*)*2 + 2);
return v_neverFailsSet_1891_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_neverFailsSet___override___redArg___boxed(lean_object* v_x_1892_){
_start:
{
uint16_t v_res_1893_; lean_object* v_r_1894_; 
v_res_1893_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_x_1892_);
lean_dec(v_x_1892_);
v_r_1894_ = lean_box(v_res_1893_);
return v_r_1894_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_containsGuarded___override___redArg(lean_object* v_x_1895_){
_start:
{
switch(lean_obj_tag(v_x_1895_))
{
case 0:
{
uint8_t v___x_1896_; 
v___x_1896_ = 0;
return v___x_1896_;
}
case 3:
{
uint8_t v_containsGuarded_1897_; 
v_containsGuarded_1897_ = lean_ctor_get_uint8(v_x_1895_, sizeof(void*)*3 + 7);
return v_containsGuarded_1897_;
}
case 6:
{
uint8_t v_containsGuarded_1898_; 
v_containsGuarded_1898_ = lean_ctor_get_uint8(v_x_1895_, sizeof(void*)*3 + 7);
return v_containsGuarded_1898_;
}
case 12:
{
uint8_t v_containsGuarded_1899_; 
v_containsGuarded_1899_ = lean_ctor_get_uint8(v_x_1895_, sizeof(void*)*3 + 7);
return v_containsGuarded_1899_;
}
case 13:
{
uint8_t v_containsGuarded_1900_; 
v_containsGuarded_1900_ = lean_ctor_get_uint8(v_x_1895_, sizeof(void*)*3 + 7);
return v_containsGuarded_1900_;
}
case 14:
{
uint8_t v_containsGuarded_1901_; 
v_containsGuarded_1901_ = lean_ctor_get_uint8(v_x_1895_, sizeof(void*)*3 + 7);
return v_containsGuarded_1901_;
}
case 15:
{
uint8_t v_containsGuarded_1902_; 
v_containsGuarded_1902_ = lean_ctor_get_uint8(v_x_1895_, sizeof(void*)*3 + 7);
return v_containsGuarded_1902_;
}
default: 
{
uint8_t v_containsGuarded_1903_; 
v_containsGuarded_1903_ = lean_ctor_get_uint8(v_x_1895_, sizeof(void*)*2 + 7);
return v_containsGuarded_1903_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_containsGuarded___override___redArg___boxed(lean_object* v_x_1904_){
_start:
{
uint8_t v_res_1905_; lean_object* v_r_1906_; 
v_res_1905_ = l_Lean_Fmt_Doc_containsGuarded___override___redArg(v_x_1904_);
lean_dec(v_x_1904_);
v_r_1906_ = lean_box(v_res_1905_);
return v_r_1906_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(lean_object* v_x_1907_){
_start:
{
switch(lean_obj_tag(v_x_1907_))
{
case 0:
{
uint8_t v___x_1908_; 
v___x_1908_ = 2;
return v___x_1908_;
}
case 3:
{
uint8_t v_alwaysEmptiness_1909_; 
v_alwaysEmptiness_1909_ = lean_ctor_get_uint8(v_x_1907_, sizeof(void*)*3 + 4);
return v_alwaysEmptiness_1909_;
}
case 6:
{
uint8_t v_alwaysEmptiness_1910_; 
v_alwaysEmptiness_1910_ = lean_ctor_get_uint8(v_x_1907_, sizeof(void*)*3 + 4);
return v_alwaysEmptiness_1910_;
}
case 12:
{
uint8_t v_alwaysEmptiness_1911_; 
v_alwaysEmptiness_1911_ = lean_ctor_get_uint8(v_x_1907_, sizeof(void*)*3 + 4);
return v_alwaysEmptiness_1911_;
}
case 13:
{
uint8_t v_alwaysEmptiness_1912_; 
v_alwaysEmptiness_1912_ = lean_ctor_get_uint8(v_x_1907_, sizeof(void*)*3 + 4);
return v_alwaysEmptiness_1912_;
}
case 14:
{
uint8_t v_alwaysEmptiness_1913_; 
v_alwaysEmptiness_1913_ = lean_ctor_get_uint8(v_x_1907_, sizeof(void*)*3 + 4);
return v_alwaysEmptiness_1913_;
}
case 15:
{
uint8_t v_alwaysEmptiness_1914_; 
v_alwaysEmptiness_1914_ = lean_ctor_get_uint8(v_x_1907_, sizeof(void*)*3 + 4);
return v_alwaysEmptiness_1914_;
}
default: 
{
uint8_t v_alwaysEmptiness_1915_; 
v_alwaysEmptiness_1915_ = lean_ctor_get_uint8(v_x_1907_, sizeof(void*)*2 + 4);
return v_alwaysEmptiness_1915_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg___boxed(lean_object* v_x_1916_){
_start:
{
uint8_t v_res_1917_; lean_object* v_r_1918_; 
v_res_1917_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_x_1916_);
lean_dec(v_x_1916_);
v_r_1918_ = lean_box(v_res_1917_);
return v_r_1918_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_Doc_failureSet___override___redArg(lean_object* v_x_1919_){
_start:
{
switch(lean_obj_tag(v_x_1919_))
{
case 0:
{
uint16_t v___x_1920_; 
v___x_1920_ = 65535;
return v___x_1920_;
}
case 3:
{
uint16_t v_failureSet_1921_; 
v_failureSet_1921_ = lean_ctor_get_uint16(v_x_1919_, sizeof(void*)*3);
return v_failureSet_1921_;
}
case 6:
{
uint16_t v_failureSet_1922_; 
v_failureSet_1922_ = lean_ctor_get_uint16(v_x_1919_, sizeof(void*)*3);
return v_failureSet_1922_;
}
case 12:
{
uint16_t v_failureSet_1923_; 
v_failureSet_1923_ = lean_ctor_get_uint16(v_x_1919_, sizeof(void*)*3);
return v_failureSet_1923_;
}
case 13:
{
uint16_t v_failureSet_1924_; 
v_failureSet_1924_ = lean_ctor_get_uint16(v_x_1919_, sizeof(void*)*3);
return v_failureSet_1924_;
}
case 14:
{
uint16_t v_failureSet_1925_; 
v_failureSet_1925_ = lean_ctor_get_uint16(v_x_1919_, sizeof(void*)*3);
return v_failureSet_1925_;
}
case 15:
{
uint16_t v_failureSet_1926_; 
v_failureSet_1926_ = lean_ctor_get_uint16(v_x_1919_, sizeof(void*)*3);
return v_failureSet_1926_;
}
default: 
{
uint16_t v_failureSet_1927_; 
v_failureSet_1927_ = lean_ctor_get_uint16(v_x_1919_, sizeof(void*)*2);
return v_failureSet_1927_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_failureSet___override___redArg___boxed(lean_object* v_x_1928_){
_start:
{
uint16_t v_res_1929_; lean_object* v_r_1930_; 
v_res_1929_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_x_1928_);
lean_dec(v_x_1928_);
v_r_1930_ = lean_box(v_res_1929_);
return v_r_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_tagged___override___redArg(lean_object* v_id_1931_, lean_object* v_d_1932_){
_start:
{
uint16_t v___x_1933_; lean_object* v___x_1934_; uint8_t v___x_1935_; uint8_t v___x_1936_; uint8_t v___x_1937_; uint16_t v___x_1938_; uint8_t v___x_1939_; lean_object* v___x_1940_; 
v___x_1933_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_d_1932_);
v___x_1934_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_1932_);
v___x_1935_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_1932_);
v___x_1936_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_1932_);
v___x_1937_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_1932_);
v___x_1938_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_d_1932_);
v___x_1939_ = l_Lean_Fmt_Doc_containsGuarded___override___redArg(v_d_1932_);
v___x_1940_ = lean_alloc_ctor(3, 3, 8);
lean_ctor_set(v___x_1940_, 0, v___x_1934_);
lean_ctor_set(v___x_1940_, 1, v_id_1931_);
lean_ctor_set(v___x_1940_, 2, v_d_1932_);
lean_ctor_set_uint16(v___x_1940_, sizeof(void*)*3, v___x_1933_);
lean_ctor_set_uint8(v___x_1940_, sizeof(void*)*3 + 4, v___x_1935_);
lean_ctor_set_uint8(v___x_1940_, sizeof(void*)*3 + 5, v___x_1936_);
lean_ctor_set_uint8(v___x_1940_, sizeof(void*)*3 + 6, v___x_1937_);
lean_ctor_set_uint16(v___x_1940_, sizeof(void*)*3 + 2, v___x_1938_);
lean_ctor_set_uint8(v___x_1940_, sizeof(void*)*3 + 7, v___x_1939_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_tagged___override(lean_object* v_00_u03c4_1941_, lean_object* v_id_1942_, lean_object* v_d_1943_){
_start:
{
lean_object* v___x_1944_; 
v___x_1944_ = l_Lean_Fmt_Doc_tagged___override___redArg(v_id_1942_, v_d_1943_);
return v___x_1944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_flattened___override___redArg(lean_object* v_d_1947_){
_start:
{
uint16_t v___x_1948_; lean_object* v___x_1949_; uint8_t v___y_1951_; uint8_t v___y_1952_; uint8_t v___y_1953_; uint8_t v___y_1957_; uint8_t v___x_1962_; 
v___x_1948_ = 0;
v___x_1949_ = ((lean_object*)(l_Lean_Fmt_Doc_flattened___override___redArg___closed__0));
v___x_1962_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_1947_);
if (v___x_1962_ == 1)
{
uint8_t v___x_1963_; 
v___x_1963_ = 0;
v___y_1957_ = v___x_1963_;
goto v___jp_1956_;
}
else
{
v___y_1957_ = v___x_1962_;
goto v___jp_1956_;
}
v___jp_1950_:
{
uint8_t v___x_1954_; lean_object* v___x_1955_; 
v___x_1954_ = l_Lean_Fmt_Doc_containsGuarded___override___redArg(v_d_1947_);
v___x_1955_ = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(v___x_1955_, 0, v___x_1949_);
lean_ctor_set(v___x_1955_, 1, v_d_1947_);
lean_ctor_set_uint16(v___x_1955_, sizeof(void*)*2, v___x_1948_);
lean_ctor_set_uint8(v___x_1955_, sizeof(void*)*2 + 4, v___y_1951_);
lean_ctor_set_uint8(v___x_1955_, sizeof(void*)*2 + 5, v___y_1952_);
lean_ctor_set_uint8(v___x_1955_, sizeof(void*)*2 + 6, v___y_1953_);
lean_ctor_set_uint16(v___x_1955_, sizeof(void*)*2 + 2, v___x_1948_);
lean_ctor_set_uint8(v___x_1955_, sizeof(void*)*2 + 7, v___x_1954_);
return v___x_1955_;
}
v___jp_1956_:
{
uint8_t v___x_1958_; uint8_t v___x_1959_; 
v___x_1958_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_1947_);
v___x_1959_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_1947_);
switch(v___x_1959_)
{
case 1:
{
uint8_t v___x_1960_; 
v___x_1960_ = 0;
v___y_1951_ = v___y_1957_;
v___y_1952_ = v___x_1958_;
v___y_1953_ = v___x_1960_;
goto v___jp_1950_;
}
case 3:
{
uint8_t v___x_1961_; 
v___x_1961_ = 2;
v___y_1951_ = v___y_1957_;
v___y_1952_ = v___x_1958_;
v___y_1953_ = v___x_1961_;
goto v___jp_1950_;
}
default: 
{
v___y_1951_ = v___y_1957_;
v___y_1952_ = v___x_1958_;
v___y_1953_ = v___x_1959_;
goto v___jp_1950_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_flattened___override(lean_object* v_00_u03c4_1964_, lean_object* v_d_1965_){
_start:
{
lean_object* v___x_1966_; 
v___x_1966_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_d_1965_);
return v___x_1966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unflattenable___override___redArg(lean_object* v_d_1967_){
_start:
{
uint16_t v___x_1968_; uint8_t v___y_1970_; uint8_t v___y_1971_; lean_object* v___y_1972_; uint8_t v___y_1973_; lean_object* v___y_1977_; uint8_t v___y_1978_; lean_object* v___y_1984_; lean_object* v___y_1988_; lean_object* v___x_1990_; 
v___x_1968_ = 0;
v___x_1990_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_1967_);
if (lean_obj_tag(v___x_1990_) == 0)
{
v___y_1984_ = v___x_1990_;
goto v___jp_1983_;
}
else
{
lean_object* v_val_1991_; lean_object* v___x_1992_; uint8_t v___x_1993_; 
v_val_1991_ = lean_ctor_get(v___x_1990_, 0);
lean_inc(v_val_1991_);
lean_dec_ref_known(v___x_1990_, 1);
v___x_1992_ = lean_unsigned_to_nat(1u);
v___x_1993_ = lean_nat_dec_le(v___x_1992_, v_val_1991_);
if (v___x_1993_ == 0)
{
lean_dec(v_val_1991_);
v___y_1988_ = v___x_1992_;
goto v___jp_1987_;
}
else
{
v___y_1988_ = v_val_1991_;
goto v___jp_1987_;
}
}
v___jp_1969_:
{
uint8_t v___x_1974_; lean_object* v___x_1975_; 
v___x_1974_ = l_Lean_Fmt_Doc_containsGuarded___override___redArg(v_d_1967_);
v___x_1975_ = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(v___x_1975_, 0, v___y_1972_);
lean_ctor_set(v___x_1975_, 1, v_d_1967_);
lean_ctor_set_uint16(v___x_1975_, sizeof(void*)*2, v___x_1968_);
lean_ctor_set_uint8(v___x_1975_, sizeof(void*)*2 + 4, v___y_1971_);
lean_ctor_set_uint8(v___x_1975_, sizeof(void*)*2 + 5, v___y_1970_);
lean_ctor_set_uint8(v___x_1975_, sizeof(void*)*2 + 6, v___y_1973_);
lean_ctor_set_uint16(v___x_1975_, sizeof(void*)*2 + 2, v___x_1968_);
lean_ctor_set_uint8(v___x_1975_, sizeof(void*)*2 + 7, v___x_1974_);
return v___x_1975_;
}
v___jp_1976_:
{
uint8_t v___x_1979_; uint8_t v___x_1980_; 
v___x_1979_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_1967_);
v___x_1980_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_1967_);
switch(v___x_1980_)
{
case 1:
{
uint8_t v___x_1981_; 
v___x_1981_ = 4;
v___y_1970_ = v___x_1979_;
v___y_1971_ = v___y_1978_;
v___y_1972_ = v___y_1977_;
v___y_1973_ = v___x_1981_;
goto v___jp_1969_;
}
case 3:
{
uint8_t v___x_1982_; 
v___x_1982_ = 4;
v___y_1970_ = v___x_1979_;
v___y_1971_ = v___y_1978_;
v___y_1972_ = v___y_1977_;
v___y_1973_ = v___x_1982_;
goto v___jp_1969_;
}
default: 
{
v___y_1970_ = v___x_1979_;
v___y_1971_ = v___y_1978_;
v___y_1972_ = v___y_1977_;
v___y_1973_ = v___x_1980_;
goto v___jp_1969_;
}
}
}
v___jp_1983_:
{
uint8_t v___x_1985_; 
v___x_1985_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_1967_);
if (v___x_1985_ == 1)
{
uint8_t v___x_1986_; 
v___x_1986_ = 2;
v___y_1977_ = v___y_1984_;
v___y_1978_ = v___x_1986_;
goto v___jp_1976_;
}
else
{
v___y_1977_ = v___y_1984_;
v___y_1978_ = v___x_1985_;
goto v___jp_1976_;
}
}
v___jp_1987_:
{
lean_object* v___x_1989_; 
v___x_1989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1989_, 0, v___y_1988_);
v___y_1984_ = v___x_1989_;
goto v___jp_1983_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unflattenable___override(lean_object* v_00_u03c4_1994_, lean_object* v_d_1995_){
_start:
{
lean_object* v___x_1996_; 
v___x_1996_ = l_Lean_Fmt_Doc_unflattenable___override___redArg(v_d_1995_);
return v___x_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_indented___override___redArg(lean_object* v_n_1997_, uint8_t v_isCumulative_1998_, lean_object* v_d_1999_){
_start:
{
uint16_t v___x_2000_; lean_object* v___x_2001_; uint8_t v___x_2002_; uint8_t v___x_2003_; uint8_t v___x_2004_; uint16_t v___x_2005_; uint8_t v___x_2006_; lean_object* v___x_2007_; 
v___x_2000_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_d_1999_);
v___x_2001_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_1999_);
v___x_2002_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_1999_);
v___x_2003_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_1999_);
v___x_2004_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_1999_);
v___x_2005_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_d_1999_);
v___x_2006_ = l_Lean_Fmt_Doc_containsGuarded___override___redArg(v_d_1999_);
v___x_2007_ = lean_alloc_ctor(6, 3, 9);
lean_ctor_set(v___x_2007_, 0, v___x_2001_);
lean_ctor_set(v___x_2007_, 1, v_n_1997_);
lean_ctor_set(v___x_2007_, 2, v_d_1999_);
lean_ctor_set_uint16(v___x_2007_, sizeof(void*)*3, v___x_2000_);
lean_ctor_set_uint8(v___x_2007_, sizeof(void*)*3 + 4, v___x_2002_);
lean_ctor_set_uint8(v___x_2007_, sizeof(void*)*3 + 5, v___x_2003_);
lean_ctor_set_uint8(v___x_2007_, sizeof(void*)*3 + 6, v___x_2004_);
lean_ctor_set_uint16(v___x_2007_, sizeof(void*)*3 + 2, v___x_2005_);
lean_ctor_set_uint8(v___x_2007_, sizeof(void*)*3 + 7, v___x_2006_);
lean_ctor_set_uint8(v___x_2007_, sizeof(void*)*3 + 8, v_isCumulative_1998_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_indented___override___redArg___boxed(lean_object* v_n_2008_, lean_object* v_isCumulative_2009_, lean_object* v_d_2010_){
_start:
{
uint8_t v_isCumulative_boxed_2011_; lean_object* v_res_2012_; 
v_isCumulative_boxed_2011_ = lean_unbox(v_isCumulative_2009_);
v_res_2012_ = l_Lean_Fmt_Doc_indented___override___redArg(v_n_2008_, v_isCumulative_boxed_2011_, v_d_2010_);
return v_res_2012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_indented___override(lean_object* v_00_u03c4_2013_, lean_object* v_n_2014_, uint8_t v_isCumulative_2015_, lean_object* v_d_2016_){
_start:
{
lean_object* v___x_2017_; 
v___x_2017_ = l_Lean_Fmt_Doc_indented___override___redArg(v_n_2014_, v_isCumulative_2015_, v_d_2016_);
return v___x_2017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_indented___override___boxed(lean_object* v_00_u03c4_2018_, lean_object* v_n_2019_, lean_object* v_isCumulative_2020_, lean_object* v_d_2021_){
_start:
{
uint8_t v_isCumulative_boxed_2022_; lean_object* v_res_2023_; 
v_isCumulative_boxed_2022_ = lean_unbox(v_isCumulative_2020_);
v_res_2023_ = l_Lean_Fmt_Doc_indented___override(v_00_u03c4_2018_, v_n_2019_, v_isCumulative_boxed_2022_, v_d_2021_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_aligned___override___redArg(lean_object* v_d_2024_){
_start:
{
uint16_t v___x_2025_; lean_object* v___x_2026_; uint8_t v___x_2027_; uint8_t v___x_2028_; uint8_t v___x_2029_; uint16_t v___x_2030_; uint8_t v___x_2031_; lean_object* v___x_2032_; 
v___x_2025_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_d_2024_);
v___x_2026_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_2024_);
v___x_2027_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_2024_);
v___x_2028_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_2024_);
v___x_2029_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_2024_);
v___x_2030_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_d_2024_);
v___x_2031_ = l_Lean_Fmt_Doc_containsGuarded___override___redArg(v_d_2024_);
v___x_2032_ = lean_alloc_ctor(7, 2, 8);
lean_ctor_set(v___x_2032_, 0, v___x_2026_);
lean_ctor_set(v___x_2032_, 1, v_d_2024_);
lean_ctor_set_uint16(v___x_2032_, sizeof(void*)*2, v___x_2025_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*2 + 4, v___x_2027_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*2 + 5, v___x_2028_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*2 + 6, v___x_2029_);
lean_ctor_set_uint16(v___x_2032_, sizeof(void*)*2 + 2, v___x_2030_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*2 + 7, v___x_2031_);
return v___x_2032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_aligned___override(lean_object* v_00_u03c4_2033_, lean_object* v_d_2034_){
_start:
{
lean_object* v___x_2035_; 
v___x_2035_ = l_Lean_Fmt_Doc_aligned___override___redArg(v_d_2034_);
return v___x_2035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unindented___override___redArg(uint8_t v_onlyNonCumulative_2036_, lean_object* v_d_2037_){
_start:
{
uint16_t v___x_2038_; lean_object* v___x_2039_; uint8_t v___x_2040_; uint8_t v___x_2041_; uint8_t v___x_2042_; uint16_t v___x_2043_; uint8_t v___x_2044_; lean_object* v___x_2045_; 
v___x_2038_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_d_2037_);
v___x_2039_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_2037_);
v___x_2040_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_2037_);
v___x_2041_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_2037_);
v___x_2042_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_2037_);
v___x_2043_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_d_2037_);
v___x_2044_ = l_Lean_Fmt_Doc_containsGuarded___override___redArg(v_d_2037_);
v___x_2045_ = lean_alloc_ctor(8, 2, 9);
lean_ctor_set(v___x_2045_, 0, v___x_2039_);
lean_ctor_set(v___x_2045_, 1, v_d_2037_);
lean_ctor_set_uint16(v___x_2045_, sizeof(void*)*2, v___x_2038_);
lean_ctor_set_uint8(v___x_2045_, sizeof(void*)*2 + 4, v___x_2040_);
lean_ctor_set_uint8(v___x_2045_, sizeof(void*)*2 + 5, v___x_2041_);
lean_ctor_set_uint8(v___x_2045_, sizeof(void*)*2 + 6, v___x_2042_);
lean_ctor_set_uint16(v___x_2045_, sizeof(void*)*2 + 2, v___x_2043_);
lean_ctor_set_uint8(v___x_2045_, sizeof(void*)*2 + 7, v___x_2044_);
lean_ctor_set_uint8(v___x_2045_, sizeof(void*)*2 + 8, v_onlyNonCumulative_2036_);
return v___x_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unindented___override___redArg___boxed(lean_object* v_onlyNonCumulative_2046_, lean_object* v_d_2047_){
_start:
{
uint8_t v_onlyNonCumulative_boxed_2048_; lean_object* v_res_2049_; 
v_onlyNonCumulative_boxed_2048_ = lean_unbox(v_onlyNonCumulative_2046_);
v_res_2049_ = l_Lean_Fmt_Doc_unindented___override___redArg(v_onlyNonCumulative_boxed_2048_, v_d_2047_);
return v_res_2049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unindented___override(lean_object* v_00_u03c4_2050_, uint8_t v_onlyNonCumulative_2051_, lean_object* v_d_2052_){
_start:
{
lean_object* v___x_2053_; 
v___x_2053_ = l_Lean_Fmt_Doc_unindented___override___redArg(v_onlyNonCumulative_2051_, v_d_2052_);
return v___x_2053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unindented___override___boxed(lean_object* v_00_u03c4_2054_, lean_object* v_onlyNonCumulative_2055_, lean_object* v_d_2056_){
_start:
{
uint8_t v_onlyNonCumulative_boxed_2057_; lean_object* v_res_2058_; 
v_onlyNonCumulative_boxed_2057_ = lean_unbox(v_onlyNonCumulative_2055_);
v_res_2058_ = l_Lean_Fmt_Doc_unindented___override(v_00_u03c4_2054_, v_onlyNonCumulative_boxed_2057_, v_d_2056_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_final___override___redArg(lean_object* v_d_2059_){
_start:
{
uint16_t v___x_2060_; uint16_t v___x_2061_; uint16_t v___x_2062_; uint16_t v___x_2063_; uint16_t v___x_2064_; uint16_t v___x_2065_; uint16_t v___x_2066_; uint16_t v___x_2067_; lean_object* v___x_2068_; uint8_t v___x_2069_; uint8_t v___x_2070_; uint8_t v___x_2071_; uint16_t v___x_2072_; uint16_t v___x_2073_; uint16_t v___x_2074_; uint16_t v___x_2075_; uint8_t v___x_2076_; lean_object* v___x_2077_; 
v___x_2060_ = 21845;
v___x_2061_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_d_2059_);
v___x_2062_ = 1;
v___x_2063_ = lean_uint16_shift_left(v___x_2061_, v___x_2062_);
v___x_2064_ = lean_uint16_land(v___x_2063_, v___x_2061_);
v___x_2065_ = 43690;
v___x_2066_ = lean_uint16_land(v___x_2064_, v___x_2065_);
v___x_2067_ = lean_uint16_lor(v___x_2060_, v___x_2066_);
v___x_2068_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_2059_);
v___x_2069_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_2059_);
v___x_2070_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_2059_);
v___x_2071_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_2059_);
v___x_2072_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_d_2059_);
v___x_2073_ = lean_uint16_shift_left(v___x_2072_, v___x_2062_);
v___x_2074_ = lean_uint16_lor(v___x_2073_, v___x_2072_);
v___x_2075_ = lean_uint16_land(v___x_2074_, v___x_2065_);
v___x_2076_ = l_Lean_Fmt_Doc_containsGuarded___override___redArg(v_d_2059_);
v___x_2077_ = lean_alloc_ctor(9, 2, 8);
lean_ctor_set(v___x_2077_, 0, v___x_2068_);
lean_ctor_set(v___x_2077_, 1, v_d_2059_);
lean_ctor_set_uint16(v___x_2077_, sizeof(void*)*2, v___x_2067_);
lean_ctor_set_uint8(v___x_2077_, sizeof(void*)*2 + 4, v___x_2069_);
lean_ctor_set_uint8(v___x_2077_, sizeof(void*)*2 + 5, v___x_2070_);
lean_ctor_set_uint8(v___x_2077_, sizeof(void*)*2 + 6, v___x_2071_);
lean_ctor_set_uint16(v___x_2077_, sizeof(void*)*2 + 2, v___x_2075_);
lean_ctor_set_uint8(v___x_2077_, sizeof(void*)*2 + 7, v___x_2076_);
return v___x_2077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_final___override(lean_object* v_00_u03c4_2078_, lean_object* v_d_2079_){
_start:
{
lean_object* v___x_2080_; 
v___x_2080_ = l_Lean_Fmt_Doc_final___override___redArg(v_d_2079_);
return v___x_2080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_initial___override___redArg(lean_object* v_d_2081_){
_start:
{
uint16_t v___x_2082_; uint16_t v___x_2083_; uint16_t v___x_2084_; uint16_t v___x_2085_; uint16_t v___x_2086_; uint16_t v___x_2087_; uint16_t v___x_2088_; uint16_t v___x_2089_; lean_object* v___x_2090_; uint8_t v___x_2091_; uint8_t v___x_2092_; uint8_t v___x_2093_; uint16_t v___x_2094_; uint16_t v___x_2095_; uint16_t v___x_2096_; uint16_t v___x_2097_; uint8_t v___x_2098_; lean_object* v___x_2099_; 
v___x_2082_ = 255;
v___x_2083_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_d_2081_);
v___x_2084_ = 8;
v___x_2085_ = lean_uint16_shift_left(v___x_2083_, v___x_2084_);
v___x_2086_ = lean_uint16_land(v___x_2085_, v___x_2083_);
v___x_2087_ = 65280;
v___x_2088_ = lean_uint16_land(v___x_2086_, v___x_2087_);
v___x_2089_ = lean_uint16_lor(v___x_2082_, v___x_2088_);
v___x_2090_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_2081_);
v___x_2091_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_2081_);
v___x_2092_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_2081_);
v___x_2093_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_2081_);
v___x_2094_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_d_2081_);
v___x_2095_ = lean_uint16_shift_left(v___x_2094_, v___x_2084_);
v___x_2096_ = lean_uint16_lor(v___x_2095_, v___x_2094_);
v___x_2097_ = lean_uint16_land(v___x_2096_, v___x_2087_);
v___x_2098_ = l_Lean_Fmt_Doc_containsGuarded___override___redArg(v_d_2081_);
v___x_2099_ = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(v___x_2099_, 0, v___x_2090_);
lean_ctor_set(v___x_2099_, 1, v_d_2081_);
lean_ctor_set_uint16(v___x_2099_, sizeof(void*)*2, v___x_2089_);
lean_ctor_set_uint8(v___x_2099_, sizeof(void*)*2 + 4, v___x_2091_);
lean_ctor_set_uint8(v___x_2099_, sizeof(void*)*2 + 5, v___x_2092_);
lean_ctor_set_uint8(v___x_2099_, sizeof(void*)*2 + 6, v___x_2093_);
lean_ctor_set_uint16(v___x_2099_, sizeof(void*)*2 + 2, v___x_2097_);
lean_ctor_set_uint8(v___x_2099_, sizeof(void*)*2 + 7, v___x_2098_);
return v___x_2099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_initial___override(lean_object* v_00_u03c4_2100_, lean_object* v_d_2101_){
_start:
{
lean_object* v___x_2102_; 
v___x_2102_ = l_Lean_Fmt_Doc_initial___override___redArg(v_d_2101_);
return v___x_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_free___override___redArg(lean_object* v_d_2103_){
_start:
{
uint16_t v___x_2104_; lean_object* v___x_2105_; uint8_t v___x_2106_; uint8_t v___x_2107_; uint8_t v___x_2108_; uint16_t v___x_2109_; uint8_t v___x_2110_; lean_object* v___x_2111_; 
v___x_2104_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_d_2103_);
v___x_2105_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_2103_);
v___x_2106_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_2103_);
v___x_2107_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_2103_);
v___x_2108_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_2103_);
v___x_2109_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_d_2103_);
v___x_2110_ = l_Lean_Fmt_Doc_containsGuarded___override___redArg(v_d_2103_);
v___x_2111_ = lean_alloc_ctor(11, 2, 8);
lean_ctor_set(v___x_2111_, 0, v___x_2105_);
lean_ctor_set(v___x_2111_, 1, v_d_2103_);
lean_ctor_set_uint16(v___x_2111_, sizeof(void*)*2, v___x_2104_);
lean_ctor_set_uint8(v___x_2111_, sizeof(void*)*2 + 4, v___x_2106_);
lean_ctor_set_uint8(v___x_2111_, sizeof(void*)*2 + 5, v___x_2107_);
lean_ctor_set_uint8(v___x_2111_, sizeof(void*)*2 + 6, v___x_2108_);
lean_ctor_set_uint16(v___x_2111_, sizeof(void*)*2 + 2, v___x_2109_);
lean_ctor_set_uint8(v___x_2111_, sizeof(void*)*2 + 7, v___x_2110_);
return v___x_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_free___override(lean_object* v_00_u03c4_2112_, lean_object* v_d_2113_){
_start:
{
lean_object* v___x_2114_; 
v___x_2114_ = l_Lean_Fmt_Doc_free___override___redArg(v_d_2113_);
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_guarded___override___redArg(lean_object* v_p_2115_, lean_object* v_d_2116_){
_start:
{
uint16_t v___x_2117_; lean_object* v___x_2118_; uint8_t v___x_2119_; uint8_t v___x_2120_; uint8_t v___x_2121_; uint16_t v___x_2122_; uint8_t v___x_2123_; lean_object* v___x_2124_; 
v___x_2117_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_d_2116_);
v___x_2118_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_2116_);
v___x_2119_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_2116_);
v___x_2120_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_2116_);
v___x_2121_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_2116_);
v___x_2122_ = 0;
v___x_2123_ = 1;
v___x_2124_ = lean_alloc_ctor(12, 3, 8);
lean_ctor_set(v___x_2124_, 0, v___x_2118_);
lean_ctor_set(v___x_2124_, 1, v_p_2115_);
lean_ctor_set(v___x_2124_, 2, v_d_2116_);
lean_ctor_set_uint16(v___x_2124_, sizeof(void*)*3, v___x_2117_);
lean_ctor_set_uint8(v___x_2124_, sizeof(void*)*3 + 4, v___x_2119_);
lean_ctor_set_uint8(v___x_2124_, sizeof(void*)*3 + 5, v___x_2120_);
lean_ctor_set_uint8(v___x_2124_, sizeof(void*)*3 + 6, v___x_2121_);
lean_ctor_set_uint16(v___x_2124_, sizeof(void*)*3 + 2, v___x_2122_);
lean_ctor_set_uint8(v___x_2124_, sizeof(void*)*3 + 7, v___x_2123_);
return v___x_2124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_guarded___override(lean_object* v_00_u03c4_2125_, lean_object* v_p_2126_, lean_object* v_d_2127_){
_start:
{
lean_object* v___x_2128_; 
v___x_2128_ = l_Lean_Fmt_Doc_guarded___override___redArg(v_p_2126_, v_d_2127_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_costing___override___redArg(lean_object* v_cost_2129_, lean_object* v_d_2130_){
_start:
{
uint16_t v___x_2131_; lean_object* v___x_2132_; uint8_t v___x_2133_; uint8_t v___x_2134_; uint8_t v___x_2135_; uint16_t v___x_2136_; uint8_t v___x_2137_; lean_object* v___x_2138_; 
v___x_2131_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_d_2130_);
v___x_2132_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_2130_);
v___x_2133_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_2130_);
v___x_2134_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_2130_);
v___x_2135_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_2130_);
v___x_2136_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_d_2130_);
v___x_2137_ = l_Lean_Fmt_Doc_containsGuarded___override___redArg(v_d_2130_);
v___x_2138_ = lean_alloc_ctor(13, 3, 8);
lean_ctor_set(v___x_2138_, 0, v___x_2132_);
lean_ctor_set(v___x_2138_, 1, v_cost_2129_);
lean_ctor_set(v___x_2138_, 2, v_d_2130_);
lean_ctor_set_uint16(v___x_2138_, sizeof(void*)*3, v___x_2131_);
lean_ctor_set_uint8(v___x_2138_, sizeof(void*)*3 + 4, v___x_2133_);
lean_ctor_set_uint8(v___x_2138_, sizeof(void*)*3 + 5, v___x_2134_);
lean_ctor_set_uint8(v___x_2138_, sizeof(void*)*3 + 6, v___x_2135_);
lean_ctor_set_uint16(v___x_2138_, sizeof(void*)*3 + 2, v___x_2136_);
lean_ctor_set_uint8(v___x_2138_, sizeof(void*)*3 + 7, v___x_2137_);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_costing___override(lean_object* v_00_u03c4_2139_, lean_object* v_cost_2140_, lean_object* v_d_2141_){
_start:
{
lean_object* v___x_2142_; 
v___x_2142_ = l_Lean_Fmt_Doc_costing___override___redArg(v_cost_2140_, v_d_2141_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_either___override___redArg___lam__0(lean_object* v_x1_2143_, lean_object* v_x2_2144_){
_start:
{
uint8_t v___x_2145_; 
v___x_2145_ = lean_nat_dec_le(v_x1_2143_, v_x2_2144_);
if (v___x_2145_ == 0)
{
lean_inc(v_x1_2143_);
return v_x1_2143_;
}
else
{
lean_inc(v_x2_2144_);
return v_x2_2144_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_either___override___redArg___lam__0___boxed(lean_object* v_x1_2146_, lean_object* v_x2_2147_){
_start:
{
lean_object* v_res_2148_; 
v_res_2148_ = l_Lean_Fmt_Doc_either___override___redArg___lam__0(v_x1_2146_, v_x2_2147_);
lean_dec(v_x2_2147_);
lean_dec(v_x1_2146_);
return v_res_2148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_either___override___redArg(lean_object* v_a_2150_, lean_object* v_b_2151_){
_start:
{
lean_object* v___f_2152_; uint16_t v___x_2153_; uint16_t v___x_2154_; uint16_t v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; uint8_t v___x_2159_; uint8_t v___x_2160_; uint8_t v___x_2161_; uint8_t v___x_2162_; uint8_t v___x_2163_; uint8_t v___x_2164_; uint8_t v___x_2165_; uint16_t v___x_2166_; uint16_t v___x_2167_; uint16_t v___x_2168_; uint8_t v___x_2169_; 
v___f_2152_ = ((lean_object*)(l_Lean_Fmt_Doc_either___override___redArg___closed__0));
v___x_2153_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_a_2150_);
v___x_2154_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_b_2151_);
v___x_2155_ = lean_uint16_land(v___x_2153_, v___x_2154_);
v___x_2156_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_a_2150_);
v___x_2157_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_b_2151_);
v___x_2158_ = l_Option_merge___redArg(v___f_2152_, v___x_2156_, v___x_2157_);
v___x_2159_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_a_2150_);
v___x_2160_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_b_2151_);
v___x_2161_ = l_Lean_Fmt_Doc_AlwaysEmptiness_max(v___x_2159_, v___x_2160_);
v___x_2162_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_a_2150_);
v___x_2163_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_b_2151_);
v___x_2164_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_max(v___x_2162_, v___x_2163_);
v___x_2165_ = 4;
v___x_2166_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_a_2150_);
v___x_2167_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_b_2151_);
v___x_2168_ = lean_uint16_lor(v___x_2166_, v___x_2167_);
v___x_2169_ = l_Lean_Fmt_Doc_containsGuarded___override___redArg(v_a_2150_);
if (v___x_2169_ == 0)
{
uint8_t v___x_2170_; lean_object* v___x_2171_; 
v___x_2170_ = l_Lean_Fmt_Doc_containsGuarded___override___redArg(v_b_2151_);
v___x_2171_ = lean_alloc_ctor(14, 3, 8);
lean_ctor_set(v___x_2171_, 0, v___x_2158_);
lean_ctor_set(v___x_2171_, 1, v_a_2150_);
lean_ctor_set(v___x_2171_, 2, v_b_2151_);
lean_ctor_set_uint16(v___x_2171_, sizeof(void*)*3, v___x_2155_);
lean_ctor_set_uint8(v___x_2171_, sizeof(void*)*3 + 4, v___x_2161_);
lean_ctor_set_uint8(v___x_2171_, sizeof(void*)*3 + 5, v___x_2164_);
lean_ctor_set_uint8(v___x_2171_, sizeof(void*)*3 + 6, v___x_2165_);
lean_ctor_set_uint16(v___x_2171_, sizeof(void*)*3 + 2, v___x_2168_);
lean_ctor_set_uint8(v___x_2171_, sizeof(void*)*3 + 7, v___x_2170_);
return v___x_2171_;
}
else
{
lean_object* v___x_2172_; 
v___x_2172_ = lean_alloc_ctor(14, 3, 8);
lean_ctor_set(v___x_2172_, 0, v___x_2158_);
lean_ctor_set(v___x_2172_, 1, v_a_2150_);
lean_ctor_set(v___x_2172_, 2, v_b_2151_);
lean_ctor_set_uint16(v___x_2172_, sizeof(void*)*3, v___x_2155_);
lean_ctor_set_uint8(v___x_2172_, sizeof(void*)*3 + 4, v___x_2161_);
lean_ctor_set_uint8(v___x_2172_, sizeof(void*)*3 + 5, v___x_2164_);
lean_ctor_set_uint8(v___x_2172_, sizeof(void*)*3 + 6, v___x_2165_);
lean_ctor_set_uint16(v___x_2172_, sizeof(void*)*3 + 2, v___x_2168_);
lean_ctor_set_uint8(v___x_2172_, sizeof(void*)*3 + 7, v___x_2169_);
return v___x_2172_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_either___override(lean_object* v_00_u03c4_2173_, lean_object* v_a_2174_, lean_object* v_b_2175_){
_start:
{
lean_object* v___x_2176_; 
v___x_2176_ = l_Lean_Fmt_Doc_either___override___redArg(v_a_2174_, v_b_2175_);
return v___x_2176_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_Doc_failureSet___override(lean_object* v_00_u03c4_2177_, lean_object* v_x_2178_){
_start:
{
uint16_t v___x_2179_; 
v___x_2179_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_x_2178_);
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_failureSet___override___boxed(lean_object* v_00_u03c4_2180_, lean_object* v_x_2181_){
_start:
{
uint16_t v_res_2182_; lean_object* v_r_2183_; 
v_res_2182_ = l_Lean_Fmt_Doc_failureSet___override(v_00_u03c4_2180_, v_x_2181_);
lean_dec(v_x_2181_);
v_r_2183_ = lean_box(v_res_2182_);
return v_r_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maxNewlineCount_x3f___override(lean_object* v_00_u03c4_2184_, lean_object* v_x_2185_){
_start:
{
lean_object* v___x_2186_; 
v___x_2186_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_x_2185_);
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___boxed(lean_object* v_00_u03c4_2187_, lean_object* v_x_2188_){
_start:
{
lean_object* v_res_2189_; 
v_res_2189_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override(v_00_u03c4_2187_, v_x_2188_);
lean_dec(v_x_2188_);
return v_res_2189_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_alwaysEmptiness___override(lean_object* v_00_u03c4_2190_, lean_object* v_x_2191_){
_start:
{
uint8_t v___x_2192_; 
v___x_2192_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_x_2191_);
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_alwaysEmptiness___override___boxed(lean_object* v_00_u03c4_2193_, lean_object* v_x_2194_){
_start:
{
uint8_t v_res_2195_; lean_object* v_r_2196_; 
v_res_2195_ = l_Lean_Fmt_Doc_alwaysEmptiness___override(v_00_u03c4_2193_, v_x_2194_);
lean_dec(v_x_2194_);
v_r_2196_ = lean_box(v_res_2195_);
return v_r_2196_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_alwaysNonEmptiness___override(lean_object* v_00_u03c4_2197_, lean_object* v_x_2198_){
_start:
{
uint8_t v___x_2199_; 
v___x_2199_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_x_2198_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_alwaysNonEmptiness___override___boxed(lean_object* v_00_u03c4_2200_, lean_object* v_x_2201_){
_start:
{
uint8_t v_res_2202_; lean_object* v_r_2203_; 
v_res_2202_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override(v_00_u03c4_2200_, v_x_2201_);
lean_dec(v_x_2201_);
v_r_2203_ = lean_box(v_res_2202_);
return v_r_2203_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_atomicness___override(lean_object* v_00_u03c4_2204_, lean_object* v_x_2205_){
_start:
{
uint8_t v___x_2206_; 
v___x_2206_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_x_2205_);
return v___x_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_atomicness___override___boxed(lean_object* v_00_u03c4_2207_, lean_object* v_x_2208_){
_start:
{
uint8_t v_res_2209_; lean_object* v_r_2210_; 
v_res_2209_ = l_Lean_Fmt_Doc_atomicness___override(v_00_u03c4_2207_, v_x_2208_);
lean_dec(v_x_2208_);
v_r_2210_ = lean_box(v_res_2209_);
return v_r_2210_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_Doc_neverFailsSet___override(lean_object* v_00_u03c4_2211_, lean_object* v_x_2212_){
_start:
{
uint16_t v___x_2213_; 
v___x_2213_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_x_2212_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_neverFailsSet___override___boxed(lean_object* v_00_u03c4_2214_, lean_object* v_x_2215_){
_start:
{
uint16_t v_res_2216_; lean_object* v_r_2217_; 
v_res_2216_ = l_Lean_Fmt_Doc_neverFailsSet___override(v_00_u03c4_2214_, v_x_2215_);
lean_dec(v_x_2215_);
v_r_2217_ = lean_box(v_res_2216_);
return v_r_2217_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_containsGuarded___override(lean_object* v_00_u03c4_2218_, lean_object* v_x_2219_){
_start:
{
uint8_t v___x_2220_; 
v___x_2220_ = l_Lean_Fmt_Doc_containsGuarded___override___redArg(v_x_2219_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_containsGuarded___override___boxed(lean_object* v_00_u03c4_2221_, lean_object* v_x_2222_){
_start:
{
uint8_t v_res_2223_; lean_object* v_r_2224_; 
v_res_2223_ = l_Lean_Fmt_Doc_containsGuarded___override(v_00_u03c4_2221_, v_x_2222_);
lean_dec(v_x_2222_);
v_r_2224_ = lean_box(v_res_2223_);
return v_r_2224_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_text___override_spec__2___redArg(lean_object* v___x_2225_, lean_object* v_s_2226_, lean_object* v_a_2227_, lean_object* v_b_2228_){
_start:
{
uint8_t v_decide_2229_; 
v_decide_2229_ = lean_nat_dec_eq(v_a_2227_, v___x_2225_);
if (v_decide_2229_ == 0)
{
uint32_t v___x_2230_; lean_object* v___x_2231_; uint32_t v___x_2232_; uint8_t v___x_2233_; 
v___x_2230_ = lean_string_utf8_get_fast(v_s_2226_, v_a_2227_);
v___x_2231_ = lean_string_utf8_next_fast(v_s_2226_, v_a_2227_);
lean_dec(v_a_2227_);
v___x_2232_ = 10;
v___x_2233_ = lean_uint32_dec_eq(v___x_2230_, v___x_2232_);
if (v___x_2233_ == 0)
{
v_a_2227_ = v___x_2231_;
goto _start;
}
else
{
lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2235_ = lean_unsigned_to_nat(1u);
v___x_2236_ = lean_nat_add(v_b_2228_, v___x_2235_);
lean_dec(v_b_2228_);
v_a_2227_ = v___x_2231_;
v_b_2228_ = v___x_2236_;
goto _start;
}
}
else
{
lean_dec(v_a_2227_);
return v_b_2228_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_text___override_spec__2___redArg___boxed(lean_object* v___x_2238_, lean_object* v_s_2239_, lean_object* v_a_2240_, lean_object* v_b_2241_){
_start:
{
lean_object* v_res_2242_; 
v_res_2242_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_text___override_spec__2___redArg(v___x_2238_, v_s_2239_, v_a_2240_, v_b_2241_);
lean_dec_ref(v_s_2239_);
lean_dec(v___x_2238_);
return v_res_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_text___override___redArg(lean_object* v_s_2243_){
_start:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; uint8_t v___x_2246_; uint16_t v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; uint8_t v___y_2251_; uint8_t v___y_2252_; uint8_t v___y_2258_; 
v___x_2244_ = lean_string_utf8_byte_size(v_s_2243_);
v___x_2245_ = lean_unsigned_to_nat(0u);
v___x_2246_ = lean_nat_dec_eq(v___x_2244_, v___x_2245_);
v___x_2247_ = l_Lean_Fmt_textFailureSet(v___x_2246_);
v___x_2248_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_text___override_spec__2___redArg(v___x_2244_, v_s_2243_, v___x_2245_, v___x_2245_);
v___x_2249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2248_);
if (v___x_2246_ == 0)
{
uint8_t v___x_2261_; 
v___x_2261_ = 2;
v___y_2258_ = v___x_2261_;
goto v___jp_2257_;
}
else
{
uint8_t v___x_2262_; 
v___x_2262_ = 0;
v___y_2258_ = v___x_2262_;
goto v___jp_2257_;
}
v___jp_2250_:
{
uint8_t v___x_2253_; uint16_t v___x_2254_; uint8_t v___x_2255_; lean_object* v___x_2256_; 
v___x_2253_ = 0;
v___x_2254_ = lean_uint16_complement(v___x_2247_);
v___x_2255_ = 0;
v___x_2256_ = lean_alloc_ctor(2, 2, 8);
lean_ctor_set(v___x_2256_, 0, v___x_2249_);
lean_ctor_set(v___x_2256_, 1, v_s_2243_);
lean_ctor_set_uint16(v___x_2256_, sizeof(void*)*2, v___x_2247_);
lean_ctor_set_uint8(v___x_2256_, sizeof(void*)*2 + 4, v___y_2251_);
lean_ctor_set_uint8(v___x_2256_, sizeof(void*)*2 + 5, v___y_2252_);
lean_ctor_set_uint8(v___x_2256_, sizeof(void*)*2 + 6, v___x_2253_);
lean_ctor_set_uint16(v___x_2256_, sizeof(void*)*2 + 2, v___x_2254_);
lean_ctor_set_uint8(v___x_2256_, sizeof(void*)*2 + 7, v___x_2255_);
return v___x_2256_;
}
v___jp_2257_:
{
if (v___x_2246_ == 0)
{
uint8_t v___x_2259_; 
v___x_2259_ = 0;
v___y_2251_ = v___y_2258_;
v___y_2252_ = v___x_2259_;
goto v___jp_2250_;
}
else
{
uint8_t v___x_2260_; 
v___x_2260_ = 1;
v___y_2251_ = v___y_2258_;
v___y_2252_ = v___x_2260_;
goto v___jp_2250_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_text___override(lean_object* v_00_u03c4_2263_, lean_object* v_s_2264_){
_start:
{
lean_object* v___x_2265_; 
v___x_2265_ = l_Lean_Fmt_Doc_text___override___redArg(v_s_2264_);
return v___x_2265_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__17_spec__25___redArg___lam__0(uint8_t v_s_2266_, uint16_t v___x_2267_, uint8_t v___y_2268_, lean_object* v_b_2269_, uint8_t v_isMidFull_2270_, uint8_t v_isMidInitial_2271_){
_start:
{
uint8_t v___x_2272_; uint8_t v___x_2273_; uint8_t v___x_2274_; uint8_t v___x_2275_; uint8_t v___x_2276_; uint8_t v___x_2277_; uint8_t v___x_2278_; uint8_t v___x_2279_; uint8_t v___x_2280_; uint8_t v___x_2281_; uint16_t v___x_2282_; uint16_t v___x_2283_; uint16_t v___x_2284_; uint16_t v___x_2285_; uint16_t v___x_2286_; uint8_t v___x_2287_; 
v___x_2272_ = 254;
v___x_2273_ = lean_uint8_land(v_s_2266_, v___x_2272_);
v___x_2274_ = lean_bool_to_uint8(v_isMidFull_2270_);
v___x_2275_ = lean_uint8_lor(v___x_2273_, v___x_2274_);
v___x_2276_ = 251;
v___x_2277_ = lean_uint8_land(v___x_2275_, v___x_2276_);
v___x_2278_ = lean_bool_to_uint8(v_isMidInitial_2271_);
v___x_2279_ = 2;
v___x_2280_ = lean_uint8_shift_left(v___x_2278_, v___x_2279_);
v___x_2281_ = lean_uint8_lor(v___x_2277_, v___x_2280_);
v___x_2282_ = lean_uint8_to_uint16(v___x_2281_);
v___x_2283_ = lean_uint16_shift_right(v___x_2267_, v___x_2282_);
v___x_2284_ = 1;
v___x_2285_ = lean_uint16_land(v___x_2283_, v___x_2284_);
v___x_2286_ = 0;
v___x_2287_ = lean_uint16_dec_eq(v___x_2285_, v___x_2286_);
if (v___x_2287_ == 0)
{
return v___y_2268_;
}
else
{
uint8_t v___x_2288_; uint8_t v___x_2289_; uint8_t v___x_2290_; uint8_t v___x_2291_; uint8_t v___x_2292_; uint8_t v___x_2293_; uint8_t v___x_2294_; uint8_t v___x_2295_; uint8_t v___x_2296_; uint8_t v___x_2297_; uint16_t v___x_2298_; uint16_t v___x_2299_; uint16_t v___x_2300_; uint16_t v___x_2301_; uint8_t v___x_2302_; 
v___x_2288_ = 253;
v___x_2289_ = lean_uint8_land(v_s_2266_, v___x_2288_);
v___x_2290_ = 1;
v___x_2291_ = lean_uint8_shift_left(v___x_2274_, v___x_2290_);
v___x_2292_ = lean_uint8_lor(v___x_2289_, v___x_2291_);
v___x_2293_ = 247;
v___x_2294_ = lean_uint8_land(v___x_2292_, v___x_2293_);
v___x_2295_ = 3;
v___x_2296_ = lean_uint8_shift_left(v___x_2278_, v___x_2295_);
v___x_2297_ = lean_uint8_lor(v___x_2294_, v___x_2296_);
v___x_2298_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_b_2269_);
v___x_2299_ = lean_uint8_to_uint16(v___x_2297_);
v___x_2300_ = lean_uint16_shift_right(v___x_2298_, v___x_2299_);
v___x_2301_ = lean_uint16_land(v___x_2300_, v___x_2284_);
v___x_2302_ = lean_uint16_dec_eq(v___x_2301_, v___x_2286_);
if (v___x_2302_ == 0)
{
return v___y_2268_;
}
else
{
return v___x_2302_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__17_spec__25___redArg___lam__0___boxed(lean_object* v_s_2303_, lean_object* v___x_2304_, lean_object* v___y_2305_, lean_object* v_b_2306_, lean_object* v_isMidFull_2307_, lean_object* v_isMidInitial_2308_){
_start:
{
uint8_t v_s_boxed_2309_; uint16_t v___x_2687__boxed_2310_; uint8_t v___y_2688__boxed_2311_; uint8_t v_isMidFull_boxed_2312_; uint8_t v_isMidInitial_boxed_2313_; uint8_t v_res_2314_; lean_object* v_r_2315_; 
v_s_boxed_2309_ = lean_unbox(v_s_2303_);
v___x_2687__boxed_2310_ = lean_unbox(v___x_2304_);
v___y_2688__boxed_2311_ = lean_unbox(v___y_2305_);
v_isMidFull_boxed_2312_ = lean_unbox(v_isMidFull_2307_);
v_isMidInitial_boxed_2313_ = lean_unbox(v_isMidInitial_2308_);
v_res_2314_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__17_spec__25___redArg___lam__0(v_s_boxed_2309_, v___x_2687__boxed_2310_, v___y_2688__boxed_2311_, v_b_2306_, v_isMidFull_boxed_2312_, v_isMidInitial_boxed_2313_);
lean_dec(v_b_2306_);
v_r_2315_ = lean_box(v_res_2314_);
return v_r_2315_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__17_spec__25___redArg(uint16_t v___x_2316_, uint8_t v___y_2317_, lean_object* v_b_2318_, lean_object* v_x_2319_, uint16_t v_x_2320_){
_start:
{
lean_object* v_zero_2321_; uint8_t v_isZero_2322_; 
v_zero_2321_ = lean_unsigned_to_nat(0u);
v_isZero_2322_ = lean_nat_dec_eq(v_x_2319_, v_zero_2321_);
if (v_isZero_2322_ == 1)
{
lean_dec(v_x_2319_);
return v_x_2320_;
}
else
{
lean_object* v_one_2323_; lean_object* v_n_2324_; uint8_t v_s_2331_; uint8_t v___x_2332_; 
v_one_2323_ = lean_unsigned_to_nat(1u);
v_n_2324_ = lean_nat_sub(v_x_2319_, v_one_2323_);
lean_dec(v_x_2319_);
v_s_2331_ = lean_uint8_of_nat(v_n_2324_);
v___x_2332_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__17_spec__25___redArg___lam__0(v_s_2331_, v___x_2316_, v___y_2317_, v_b_2318_, v_isZero_2322_, v_isZero_2322_);
if (v___x_2332_ == 0)
{
uint8_t v___x_2333_; uint8_t v___x_2334_; 
v___x_2333_ = 1;
v___x_2334_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__17_spec__25___redArg___lam__0(v_s_2331_, v___x_2316_, v___y_2317_, v_b_2318_, v___x_2332_, v___x_2333_);
if (v___x_2334_ == 0)
{
uint8_t v___x_2335_; 
v___x_2335_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__17_spec__25___redArg___lam__0(v_s_2331_, v___x_2316_, v___y_2317_, v_b_2318_, v___x_2333_, v___x_2334_);
if (v___x_2335_ == 0)
{
uint8_t v___x_2336_; 
v___x_2336_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__17_spec__25___redArg___lam__0(v_s_2331_, v___x_2316_, v___y_2317_, v_b_2318_, v___x_2333_, v___x_2333_);
if (v___x_2336_ == 0)
{
v_x_2319_ = v_n_2324_;
goto _start;
}
else
{
goto v___jp_2325_;
}
}
else
{
goto v___jp_2325_;
}
}
else
{
goto v___jp_2325_;
}
}
else
{
goto v___jp_2325_;
}
v___jp_2325_:
{
uint16_t v___x_2326_; uint16_t v___x_2327_; uint16_t v___x_2328_; uint16_t v___x_2329_; 
v___x_2326_ = 1;
v___x_2327_ = lean_uint16_of_nat(v_n_2324_);
v___x_2328_ = lean_uint16_shift_left(v___x_2326_, v___x_2327_);
v___x_2329_ = lean_uint16_lor(v_x_2320_, v___x_2328_);
v_x_2319_ = v_n_2324_;
v_x_2320_ = v___x_2329_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__17_spec__25___redArg___boxed(lean_object* v___x_2338_, lean_object* v___y_2339_, lean_object* v_b_2340_, lean_object* v_x_2341_, lean_object* v_x_2342_){
_start:
{
uint16_t v___x_2755__boxed_2343_; uint8_t v___y_2756__boxed_2344_; uint16_t v_x_2758__boxed_2345_; uint16_t v_res_2346_; lean_object* v_r_2347_; 
v___x_2755__boxed_2343_ = lean_unbox(v___x_2338_);
v___y_2756__boxed_2344_ = lean_unbox(v___y_2339_);
v_x_2758__boxed_2345_ = lean_unbox(v_x_2342_);
v_res_2346_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__17_spec__25___redArg(v___x_2755__boxed_2343_, v___y_2756__boxed_2344_, v_b_2340_, v_x_2341_, v_x_2758__boxed_2345_);
lean_dec(v_b_2340_);
v_r_2347_ = lean_box(v_res_2346_);
return v_r_2347_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__17___redArg(uint16_t v___x_2348_, uint8_t v___y_2349_, lean_object* v_b_2350_){
_start:
{
lean_object* v___x_2351_; uint16_t v___x_2352_; uint16_t v___x_2353_; 
v___x_2351_ = lean_unsigned_to_nat(16u);
v___x_2352_ = 0;
v___x_2353_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__17_spec__25___redArg(v___x_2348_, v___y_2349_, v_b_2350_, v___x_2351_, v___x_2352_);
return v___x_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__17___redArg___boxed(lean_object* v___x_2354_, lean_object* v___y_2355_, lean_object* v_b_2356_){
_start:
{
uint16_t v___x_2793__boxed_2357_; uint8_t v___y_2794__boxed_2358_; uint16_t v_res_2359_; lean_object* v_r_2360_; 
v___x_2793__boxed_2357_ = lean_unbox(v___x_2354_);
v___y_2794__boxed_2358_ = lean_unbox(v___y_2355_);
v_res_2359_ = l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__17___redArg(v___x_2793__boxed_2357_, v___y_2794__boxed_2358_, v_b_2356_);
lean_dec(v_b_2356_);
v_r_2360_ = lean_box(v_res_2359_);
return v_r_2360_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg___lam__0(uint8_t v_s_2361_, uint16_t v___x_2362_, lean_object* v_b_2363_, uint8_t v___y_2364_, uint8_t v_isMidFull_2365_, uint8_t v_isMidInitial_2366_){
_start:
{
uint8_t v___x_2367_; uint8_t v___x_2368_; uint8_t v___x_2369_; uint8_t v___x_2370_; uint8_t v___x_2371_; uint8_t v___x_2372_; uint8_t v___x_2373_; uint8_t v___x_2374_; uint8_t v___x_2375_; uint8_t v___x_2376_; uint16_t v___x_2377_; uint16_t v___x_2378_; uint16_t v___x_2379_; uint16_t v___x_2380_; uint16_t v___x_2381_; uint8_t v___x_2382_; 
v___x_2367_ = 254;
v___x_2368_ = lean_uint8_land(v_s_2361_, v___x_2367_);
v___x_2369_ = lean_bool_to_uint8(v_isMidFull_2365_);
v___x_2370_ = lean_uint8_lor(v___x_2368_, v___x_2369_);
v___x_2371_ = 251;
v___x_2372_ = lean_uint8_land(v___x_2370_, v___x_2371_);
v___x_2373_ = lean_bool_to_uint8(v_isMidInitial_2366_);
v___x_2374_ = 2;
v___x_2375_ = lean_uint8_shift_left(v___x_2373_, v___x_2374_);
v___x_2376_ = lean_uint8_lor(v___x_2372_, v___x_2375_);
v___x_2377_ = lean_uint8_to_uint16(v___x_2376_);
v___x_2378_ = lean_uint16_shift_right(v___x_2362_, v___x_2377_);
v___x_2379_ = 1;
v___x_2380_ = lean_uint16_land(v___x_2378_, v___x_2379_);
v___x_2381_ = 0;
v___x_2382_ = lean_uint16_dec_eq(v___x_2380_, v___x_2381_);
if (v___x_2382_ == 0)
{
uint8_t v___x_2383_; uint8_t v___x_2384_; uint8_t v___x_2385_; uint8_t v___x_2386_; uint8_t v___x_2387_; uint8_t v___x_2388_; uint8_t v___x_2389_; uint8_t v___x_2390_; uint8_t v___x_2391_; uint8_t v___x_2392_; uint16_t v___x_2393_; uint16_t v___x_2394_; uint16_t v___x_2395_; uint16_t v___x_2396_; uint8_t v___x_2397_; 
v___x_2383_ = 253;
v___x_2384_ = lean_uint8_land(v_s_2361_, v___x_2383_);
v___x_2385_ = 1;
v___x_2386_ = lean_uint8_shift_left(v___x_2369_, v___x_2385_);
v___x_2387_ = lean_uint8_lor(v___x_2384_, v___x_2386_);
v___x_2388_ = 247;
v___x_2389_ = lean_uint8_land(v___x_2387_, v___x_2388_);
v___x_2390_ = 3;
v___x_2391_ = lean_uint8_shift_left(v___x_2373_, v___x_2390_);
v___x_2392_ = lean_uint8_lor(v___x_2389_, v___x_2391_);
v___x_2393_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_b_2363_);
v___x_2394_ = lean_uint8_to_uint16(v___x_2392_);
v___x_2395_ = lean_uint16_shift_right(v___x_2393_, v___x_2394_);
v___x_2396_ = lean_uint16_land(v___x_2395_, v___x_2379_);
v___x_2397_ = lean_uint16_dec_eq(v___x_2396_, v___x_2381_);
if (v___x_2397_ == 0)
{
uint8_t v___x_2398_; 
v___x_2398_ = 1;
return v___x_2398_;
}
else
{
return v___y_2364_;
}
}
else
{
return v___y_2364_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg___lam__0___boxed(lean_object* v_s_2399_, lean_object* v___x_2400_, lean_object* v_b_2401_, lean_object* v___y_2402_, lean_object* v_isMidFull_2403_, lean_object* v_isMidInitial_2404_){
_start:
{
uint8_t v_s_boxed_2405_; uint16_t v___x_2805__boxed_2406_; uint8_t v___y_2806__boxed_2407_; uint8_t v_isMidFull_boxed_2408_; uint8_t v_isMidInitial_boxed_2409_; uint8_t v_res_2410_; lean_object* v_r_2411_; 
v_s_boxed_2405_ = lean_unbox(v_s_2399_);
v___x_2805__boxed_2406_ = lean_unbox(v___x_2400_);
v___y_2806__boxed_2407_ = lean_unbox(v___y_2402_);
v_isMidFull_boxed_2408_ = lean_unbox(v_isMidFull_2403_);
v_isMidInitial_boxed_2409_ = lean_unbox(v_isMidInitial_2404_);
v_res_2410_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg___lam__0(v_s_boxed_2405_, v___x_2805__boxed_2406_, v_b_2401_, v___y_2806__boxed_2407_, v_isMidFull_boxed_2408_, v_isMidInitial_boxed_2409_);
lean_dec(v_b_2401_);
v_r_2411_ = lean_box(v_res_2410_);
return v_r_2411_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg(uint16_t v___x_2412_, lean_object* v_b_2413_, uint8_t v___y_2414_, lean_object* v_x_2415_, uint16_t v_x_2416_){
_start:
{
lean_object* v_zero_2417_; uint8_t v_isZero_2418_; 
v_zero_2417_ = lean_unsigned_to_nat(0u);
v_isZero_2418_ = lean_nat_dec_eq(v_x_2415_, v_zero_2417_);
if (v_isZero_2418_ == 1)
{
lean_dec(v_x_2415_);
return v_x_2416_;
}
else
{
lean_object* v_one_2419_; lean_object* v_n_2420_; uint8_t v_s_2427_; uint8_t v___x_2428_; 
v_one_2419_ = lean_unsigned_to_nat(1u);
v_n_2420_ = lean_nat_sub(v_x_2415_, v_one_2419_);
lean_dec(v_x_2415_);
v_s_2427_ = lean_uint8_of_nat(v_n_2420_);
v___x_2428_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg___lam__0(v_s_2427_, v___x_2412_, v_b_2413_, v___y_2414_, v_isZero_2418_, v_isZero_2418_);
if (v___x_2428_ == 0)
{
uint8_t v___x_2429_; uint8_t v___x_2430_; 
v___x_2429_ = 1;
v___x_2430_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg___lam__0(v_s_2427_, v___x_2412_, v_b_2413_, v___y_2414_, v___x_2428_, v___x_2429_);
if (v___x_2430_ == 0)
{
uint8_t v___x_2431_; 
v___x_2431_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg___lam__0(v_s_2427_, v___x_2412_, v_b_2413_, v___y_2414_, v___x_2429_, v___x_2430_);
if (v___x_2431_ == 0)
{
uint8_t v___x_2432_; 
v___x_2432_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg___lam__0(v_s_2427_, v___x_2412_, v_b_2413_, v___y_2414_, v___x_2429_, v___x_2429_);
if (v___x_2432_ == 0)
{
v_x_2415_ = v_n_2420_;
goto _start;
}
else
{
goto v___jp_2421_;
}
}
else
{
goto v___jp_2421_;
}
}
else
{
goto v___jp_2421_;
}
}
else
{
goto v___jp_2421_;
}
v___jp_2421_:
{
uint16_t v___x_2422_; uint16_t v___x_2423_; uint16_t v___x_2424_; uint16_t v___x_2425_; 
v___x_2422_ = 1;
v___x_2423_ = lean_uint16_of_nat(v_n_2420_);
v___x_2424_ = lean_uint16_shift_left(v___x_2422_, v___x_2423_);
v___x_2425_ = lean_uint16_lor(v_x_2416_, v___x_2424_);
v_x_2415_ = v_n_2420_;
v_x_2416_ = v___x_2425_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg___boxed(lean_object* v___x_2434_, lean_object* v_b_2435_, lean_object* v___y_2436_, lean_object* v_x_2437_, lean_object* v_x_2438_){
_start:
{
uint16_t v___x_2875__boxed_2439_; uint8_t v___y_2876__boxed_2440_; uint16_t v_x_2878__boxed_2441_; uint16_t v_res_2442_; lean_object* v_r_2443_; 
v___x_2875__boxed_2439_ = lean_unbox(v___x_2434_);
v___y_2876__boxed_2440_ = lean_unbox(v___y_2436_);
v_x_2878__boxed_2441_ = lean_unbox(v_x_2438_);
v_res_2442_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg(v___x_2875__boxed_2439_, v_b_2435_, v___y_2876__boxed_2440_, v_x_2437_, v_x_2878__boxed_2441_);
lean_dec(v_b_2435_);
v_r_2443_ = lean_box(v_res_2442_);
return v_r_2443_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16___redArg(uint16_t v___x_2444_, lean_object* v_b_2445_, uint8_t v___y_2446_){
_start:
{
lean_object* v___x_2447_; uint16_t v___x_2448_; uint16_t v___x_2449_; 
v___x_2447_ = lean_unsigned_to_nat(16u);
v___x_2448_ = 0;
v___x_2449_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg(v___x_2444_, v_b_2445_, v___y_2446_, v___x_2447_, v___x_2448_);
return v___x_2449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16___redArg___boxed(lean_object* v___x_2450_, lean_object* v_b_2451_, lean_object* v___y_2452_){
_start:
{
uint16_t v___x_2913__boxed_2453_; uint8_t v___y_2914__boxed_2454_; uint16_t v_res_2455_; lean_object* v_r_2456_; 
v___x_2913__boxed_2453_ = lean_unbox(v___x_2450_);
v___y_2914__boxed_2454_ = lean_unbox(v___y_2452_);
v_res_2455_ = l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16___redArg(v___x_2913__boxed_2453_, v_b_2451_, v___y_2914__boxed_2454_);
lean_dec(v_b_2451_);
v_r_2456_ = lean_box(v_res_2455_);
return v_r_2456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_append___override___redArg(lean_object* v_a_2457_, lean_object* v_b_2458_){
_start:
{
lean_object* v___y_2460_; uint8_t v___y_2461_; uint8_t v___y_2462_; uint16_t v___y_2463_; uint8_t v___y_2464_; uint16_t v___y_2465_; lean_object* v___y_2471_; uint8_t v___y_2472_; uint16_t v___y_2473_; uint8_t v___y_2474_; uint8_t v___y_2475_; lean_object* v___f_2482_; uint16_t v___y_2484_; uint16_t v___x_2501_; uint16_t v___x_2502_; uint8_t v___x_2503_; 
v___f_2482_ = ((lean_object*)(l_Lean_Fmt_instHAddTagIdNat___closed__0));
v___x_2501_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_a_2457_);
v___x_2502_ = 65535;
v___x_2503_ = lean_uint16_dec_eq(v___x_2501_, v___x_2502_);
if (v___x_2503_ == 0)
{
uint16_t v___x_2504_; uint8_t v___x_2505_; 
v___x_2504_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_b_2458_);
v___x_2505_ = lean_uint16_dec_eq(v___x_2504_, v___x_2502_);
if (v___x_2505_ == 0)
{
uint16_t v___x_2506_; uint16_t v___x_2507_; 
v___x_2506_ = l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__17___redArg(v___x_2501_, v___x_2505_, v_b_2458_);
v___x_2507_ = lean_uint16_complement(v___x_2506_);
v___y_2484_ = v___x_2507_;
goto v___jp_2483_;
}
else
{
v___y_2484_ = v___x_2502_;
goto v___jp_2483_;
}
}
else
{
v___y_2484_ = v___x_2502_;
goto v___jp_2483_;
}
v___jp_2459_:
{
uint8_t v___x_2466_; 
v___x_2466_ = l_Lean_Fmt_Doc_containsGuarded___override___redArg(v_a_2457_);
if (v___x_2466_ == 0)
{
uint8_t v___x_2467_; lean_object* v___x_2468_; 
v___x_2467_ = l_Lean_Fmt_Doc_containsGuarded___override___redArg(v_b_2458_);
v___x_2468_ = lean_alloc_ctor(15, 3, 8);
lean_ctor_set(v___x_2468_, 0, v___y_2460_);
lean_ctor_set(v___x_2468_, 1, v_a_2457_);
lean_ctor_set(v___x_2468_, 2, v_b_2458_);
lean_ctor_set_uint16(v___x_2468_, sizeof(void*)*3, v___y_2463_);
lean_ctor_set_uint8(v___x_2468_, sizeof(void*)*3 + 4, v___y_2462_);
lean_ctor_set_uint8(v___x_2468_, sizeof(void*)*3 + 5, v___y_2464_);
lean_ctor_set_uint8(v___x_2468_, sizeof(void*)*3 + 6, v___y_2461_);
lean_ctor_set_uint16(v___x_2468_, sizeof(void*)*3 + 2, v___y_2465_);
lean_ctor_set_uint8(v___x_2468_, sizeof(void*)*3 + 7, v___x_2467_);
return v___x_2468_;
}
else
{
lean_object* v___x_2469_; 
v___x_2469_ = lean_alloc_ctor(15, 3, 8);
lean_ctor_set(v___x_2469_, 0, v___y_2460_);
lean_ctor_set(v___x_2469_, 1, v_a_2457_);
lean_ctor_set(v___x_2469_, 2, v_b_2458_);
lean_ctor_set_uint16(v___x_2469_, sizeof(void*)*3, v___y_2463_);
lean_ctor_set_uint8(v___x_2469_, sizeof(void*)*3 + 4, v___y_2462_);
lean_ctor_set_uint8(v___x_2469_, sizeof(void*)*3 + 5, v___y_2464_);
lean_ctor_set_uint8(v___x_2469_, sizeof(void*)*3 + 6, v___y_2461_);
lean_ctor_set_uint16(v___x_2469_, sizeof(void*)*3 + 2, v___y_2465_);
lean_ctor_set_uint8(v___x_2469_, sizeof(void*)*3 + 7, v___x_2466_);
return v___x_2469_;
}
}
v___jp_2470_:
{
uint16_t v___x_2476_; uint16_t v___x_2477_; uint8_t v___x_2478_; 
v___x_2476_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_a_2457_);
v___x_2477_ = 0;
v___x_2478_ = lean_uint16_dec_eq(v___x_2476_, v___x_2477_);
if (v___x_2478_ == 0)
{
uint16_t v___x_2479_; uint8_t v___x_2480_; 
v___x_2479_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_b_2458_);
v___x_2480_ = lean_uint16_dec_eq(v___x_2479_, v___x_2477_);
if (v___x_2480_ == 0)
{
uint16_t v___x_2481_; 
v___x_2481_ = l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16___redArg(v___x_2476_, v_b_2458_, v___x_2480_);
v___y_2460_ = v___y_2471_;
v___y_2461_ = v___y_2475_;
v___y_2462_ = v___y_2472_;
v___y_2463_ = v___y_2473_;
v___y_2464_ = v___y_2474_;
v___y_2465_ = v___x_2481_;
goto v___jp_2459_;
}
else
{
v___y_2460_ = v___y_2471_;
v___y_2461_ = v___y_2475_;
v___y_2462_ = v___y_2472_;
v___y_2463_ = v___y_2473_;
v___y_2464_ = v___y_2474_;
v___y_2465_ = v___x_2477_;
goto v___jp_2459_;
}
}
else
{
v___y_2460_ = v___y_2471_;
v___y_2461_ = v___y_2475_;
v___y_2462_ = v___y_2472_;
v___y_2463_ = v___y_2473_;
v___y_2464_ = v___y_2474_;
v___y_2465_ = v___x_2477_;
goto v___jp_2459_;
}
}
v___jp_2483_:
{
lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; uint8_t v___x_2488_; uint8_t v___x_2489_; uint8_t v___x_2490_; uint8_t v___x_2491_; uint8_t v___x_2492_; uint8_t v___x_2493_; 
v___x_2485_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_a_2457_);
v___x_2486_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_b_2458_);
v___x_2487_ = l_Option_merge___redArg(v___f_2482_, v___x_2485_, v___x_2486_);
v___x_2488_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_a_2457_);
v___x_2489_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_b_2458_);
v___x_2490_ = l_Lean_Fmt_Doc_AlwaysEmptiness_max(v___x_2488_, v___x_2489_);
v___x_2491_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_a_2457_);
v___x_2492_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_b_2458_);
v___x_2493_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_max(v___x_2491_, v___x_2492_);
if (v___x_2488_ == 0)
{
uint8_t v___x_2494_; 
v___x_2494_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_b_2458_);
v___y_2471_ = v___x_2487_;
v___y_2472_ = v___x_2490_;
v___y_2473_ = v___y_2484_;
v___y_2474_ = v___x_2493_;
v___y_2475_ = v___x_2494_;
goto v___jp_2470_;
}
else
{
if (v___x_2489_ == 0)
{
uint8_t v___x_2495_; 
v___x_2495_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_a_2457_);
v___y_2471_ = v___x_2487_;
v___y_2472_ = v___x_2490_;
v___y_2473_ = v___y_2484_;
v___y_2474_ = v___x_2493_;
v___y_2475_ = v___x_2495_;
goto v___jp_2470_;
}
else
{
uint8_t v___x_2496_; uint8_t v___x_2497_; uint8_t v___x_2498_; uint8_t v___x_2499_; uint8_t v___x_2500_; 
v___x_2496_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_a_2457_);
v___x_2497_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_b_2458_);
v___x_2498_ = l_Lean_Fmt_Doc_Atomicness_max(v___x_2496_, v___x_2497_);
v___x_2499_ = 2;
v___x_2500_ = l_Lean_Fmt_Doc_Atomicness_max(v___x_2498_, v___x_2499_);
v___y_2471_ = v___x_2487_;
v___y_2472_ = v___x_2490_;
v___y_2473_ = v___y_2484_;
v___y_2474_ = v___x_2493_;
v___y_2475_ = v___x_2500_;
goto v___jp_2470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_append___override(lean_object* v_00_u03c4_2508_, lean_object* v_a_2509_, lean_object* v_b_2510_){
_start:
{
lean_object* v___x_2511_; 
v___x_2511_ = l_Lean_Fmt_Doc_append___override___redArg(v_a_2509_, v_b_2510_);
return v___x_2511_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_text___override_spec__2(lean_object* v___x_2512_, lean_object* v___x_2513_, lean_object* v_s_2514_, lean_object* v_inst_2515_, lean_object* v_R_2516_, lean_object* v_a_2517_, lean_object* v_b_2518_, lean_object* v_c_2519_){
_start:
{
lean_object* v___x_2520_; 
v___x_2520_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_text___override_spec__2___redArg(v___x_2513_, v_s_2514_, v_a_2517_, v_b_2518_);
return v___x_2520_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_text___override_spec__2___boxed(lean_object* v___x_2521_, lean_object* v___x_2522_, lean_object* v_s_2523_, lean_object* v_inst_2524_, lean_object* v_R_2525_, lean_object* v_a_2526_, lean_object* v_b_2527_, lean_object* v_c_2528_){
_start:
{
lean_object* v_res_2529_; 
v_res_2529_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_text___override_spec__2(v___x_2521_, v___x_2522_, v_s_2523_, v_inst_2524_, v_R_2525_, v_a_2526_, v_b_2527_, v_c_2528_);
lean_dec_ref(v_s_2523_);
lean_dec(v___x_2522_);
lean_dec_ref(v___x_2521_);
return v_res_2529_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16(uint16_t v___x_2530_, lean_object* v_00_u03c4_2531_, lean_object* v_b_2532_, uint8_t v___y_2533_){
_start:
{
uint16_t v___x_2534_; 
v___x_2534_ = l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16___redArg(v___x_2530_, v_b_2532_, v___y_2533_);
return v___x_2534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16___boxed(lean_object* v___x_2535_, lean_object* v_00_u03c4_2536_, lean_object* v_b_2537_, lean_object* v___y_2538_){
_start:
{
uint16_t v___x_3037__boxed_2539_; uint8_t v___y_3038__boxed_2540_; uint16_t v_res_2541_; lean_object* v_r_2542_; 
v___x_3037__boxed_2539_ = lean_unbox(v___x_2535_);
v___y_3038__boxed_2540_ = lean_unbox(v___y_2538_);
v_res_2541_ = l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16(v___x_3037__boxed_2539_, v_00_u03c4_2536_, v_b_2537_, v___y_3038__boxed_2540_);
lean_dec(v_b_2537_);
v_r_2542_ = lean_box(v_res_2541_);
return v_r_2542_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__17(uint16_t v___x_2543_, uint8_t v___y_2544_, lean_object* v_00_u03c4_2545_, lean_object* v_b_2546_){
_start:
{
uint16_t v___x_2547_; 
v___x_2547_ = l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__17___redArg(v___x_2543_, v___y_2544_, v_b_2546_);
return v___x_2547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__17___boxed(lean_object* v___x_2548_, lean_object* v___y_2549_, lean_object* v_00_u03c4_2550_, lean_object* v_b_2551_){
_start:
{
uint16_t v___x_3045__boxed_2552_; uint8_t v___y_3046__boxed_2553_; uint16_t v_res_2554_; lean_object* v_r_2555_; 
v___x_3045__boxed_2552_ = lean_unbox(v___x_2548_);
v___y_3046__boxed_2553_ = lean_unbox(v___y_2549_);
v_res_2554_ = l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__17(v___x_3045__boxed_2552_, v___y_3046__boxed_2553_, v_00_u03c4_2550_, v_b_2551_);
lean_dec(v_b_2551_);
v_r_2555_ = lean_box(v_res_2554_);
return v_r_2555_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23(uint16_t v___x_2556_, lean_object* v_00_u03c4_2557_, lean_object* v_b_2558_, uint8_t v___y_2559_, lean_object* v_x_2560_, uint16_t v_x_2561_){
_start:
{
uint16_t v___x_2562_; 
v___x_2562_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg(v___x_2556_, v_b_2558_, v___y_2559_, v_x_2560_, v_x_2561_);
return v___x_2562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___boxed(lean_object* v___x_2563_, lean_object* v_00_u03c4_2564_, lean_object* v_b_2565_, lean_object* v___y_2566_, lean_object* v_x_2567_, lean_object* v_x_2568_){
_start:
{
uint16_t v___x_3053__boxed_2569_; uint8_t v___y_3054__boxed_2570_; uint16_t v_x_3056__boxed_2571_; uint16_t v_res_2572_; lean_object* v_r_2573_; 
v___x_3053__boxed_2569_ = lean_unbox(v___x_2563_);
v___y_3054__boxed_2570_ = lean_unbox(v___y_2566_);
v_x_3056__boxed_2571_ = lean_unbox(v_x_2568_);
v_res_2572_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23(v___x_3053__boxed_2569_, v_00_u03c4_2564_, v_b_2565_, v___y_3054__boxed_2570_, v_x_2567_, v_x_3056__boxed_2571_);
lean_dec(v_b_2565_);
v_r_2573_ = lean_box(v_res_2572_);
return v_r_2573_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__17_spec__25(uint16_t v___x_2574_, uint8_t v___y_2575_, lean_object* v_00_u03c4_2576_, lean_object* v_b_2577_, lean_object* v_x_2578_, uint16_t v_x_2579_){
_start:
{
uint16_t v___x_2580_; 
v___x_2580_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__17_spec__25___redArg(v___x_2574_, v___y_2575_, v_b_2577_, v_x_2578_, v_x_2579_);
return v___x_2580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__17_spec__25___boxed(lean_object* v___x_2581_, lean_object* v___y_2582_, lean_object* v_00_u03c4_2583_, lean_object* v_b_2584_, lean_object* v_x_2585_, lean_object* v_x_2586_){
_start:
{
uint16_t v___x_3067__boxed_2587_; uint8_t v___y_3068__boxed_2588_; uint16_t v_x_3070__boxed_2589_; uint16_t v_res_2590_; lean_object* v_r_2591_; 
v___x_3067__boxed_2587_ = lean_unbox(v___x_2581_);
v___y_3068__boxed_2588_ = lean_unbox(v___y_2582_);
v_x_3070__boxed_2589_ = lean_unbox(v_x_2586_);
v_res_2590_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__17_spec__25(v___x_3067__boxed_2587_, v___y_3068__boxed_2588_, v_00_u03c4_2583_, v_b_2584_, v_x_2585_, v_x_3070__boxed_2589_);
lean_dec(v_b_2584_);
v_r_2591_ = lean_box(v_res_2590_);
return v_r_2591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedDoc_default___redArg(){
_start:
{
lean_object* v___x_2593_; 
v___x_2593_ = lean_box(0);
return v___x_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedDoc_default___redArg___boxed(lean_object* v___dummy_2594_){
_start:
{
lean_object* v_res_2595_; 
v_res_2595_ = l_Lean_Fmt_instInhabitedDoc_default___redArg();
return v_res_2595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedDoc_default(lean_object* v_00_u03c4_2596_){
_start:
{
lean_object* v___x_2597_; 
v___x_2597_ = lean_box(0);
return v___x_2597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedDoc___redArg(){
_start:
{
lean_object* v___x_2599_; 
v___x_2599_ = lean_box(0);
return v___x_2599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedDoc___redArg___boxed(lean_object* v___dummy_2600_){
_start:
{
lean_object* v_res_2601_; 
v_res_2601_ = l_Lean_Fmt_instInhabitedDoc___redArg();
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedDoc(lean_object* v_a_2602_){
_start:
{
lean_object* v___x_2603_; 
v___x_2603_ = lean_box(0);
return v___x_2603_;
}
}
static lean_object* _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2(void){
_start:
{
lean_object* v___x_2607_; lean_object* v___x_2608_; 
v___x_2607_ = lean_unsigned_to_nat(2u);
v___x_2608_ = lean_nat_to_int(v___x_2607_);
return v___x_2608_;
}
}
static lean_object* _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3(void){
_start:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2609_ = lean_unsigned_to_nat(1u);
v___x_2610_ = lean_nat_to_int(v___x_2609_);
return v___x_2610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprDoc_repr___redArg(lean_object* v_inst_2707_, lean_object* v_x_2708_, lean_object* v_prec_2709_){
_start:
{
lean_object* v___y_2711_; 
switch(lean_obj_tag(v_x_2708_))
{
case 0:
{
lean_object* v___x_2717_; uint8_t v___x_2718_; 
lean_dec_ref(v_inst_2707_);
v___x_2717_ = lean_unsigned_to_nat(1024u);
v___x_2718_ = lean_nat_dec_le(v___x_2717_, v_prec_2709_);
if (v___x_2718_ == 0)
{
lean_object* v___x_2719_; 
v___x_2719_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2711_ = v___x_2719_;
goto v___jp_2710_;
}
else
{
lean_object* v___x_2720_; 
v___x_2720_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2711_ = v___x_2720_;
goto v___jp_2710_;
}
}
case 1:
{
lean_object* v_f_2721_; lean_object* v___y_2723_; lean_object* v___x_2732_; uint8_t v___x_2733_; 
lean_dec_ref(v_inst_2707_);
v_f_2721_ = lean_ctor_get(v_x_2708_, 1);
lean_inc_ref(v_f_2721_);
lean_dec_ref_known(v_x_2708_, 2);
v___x_2732_ = lean_unsigned_to_nat(1024u);
v___x_2733_ = lean_nat_dec_le(v___x_2732_, v_prec_2709_);
if (v___x_2733_ == 0)
{
lean_object* v___x_2734_; 
v___x_2734_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2723_ = v___x_2734_;
goto v___jp_2722_;
}
else
{
lean_object* v___x_2735_; 
v___x_2735_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2723_ = v___x_2735_;
goto v___jp_2722_;
}
v___jp_2722_:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; uint8_t v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; 
v___x_2724_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__6));
v___x_2725_ = l_String_quote(v_f_2721_);
v___x_2726_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2725_);
v___x_2727_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2727_, 0, v___x_2724_);
lean_ctor_set(v___x_2727_, 1, v___x_2726_);
lean_inc(v___y_2723_);
v___x_2728_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2728_, 0, v___y_2723_);
lean_ctor_set(v___x_2728_, 1, v___x_2727_);
v___x_2729_ = 0;
v___x_2730_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2730_, 0, v___x_2728_);
lean_ctor_set_uint8(v___x_2730_, sizeof(void*)*1, v___x_2729_);
v___x_2731_ = l_Repr_addAppParen(v___x_2730_, v_prec_2709_);
return v___x_2731_;
}
}
case 2:
{
lean_object* v_s_2736_; lean_object* v___y_2738_; lean_object* v___x_2747_; uint8_t v___x_2748_; 
lean_dec_ref(v_inst_2707_);
v_s_2736_ = lean_ctor_get(v_x_2708_, 1);
lean_inc_ref(v_s_2736_);
lean_dec_ref_known(v_x_2708_, 2);
v___x_2747_ = lean_unsigned_to_nat(1024u);
v___x_2748_ = lean_nat_dec_le(v___x_2747_, v_prec_2709_);
if (v___x_2748_ == 0)
{
lean_object* v___x_2749_; 
v___x_2749_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2738_ = v___x_2749_;
goto v___jp_2737_;
}
else
{
lean_object* v___x_2750_; 
v___x_2750_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2738_ = v___x_2750_;
goto v___jp_2737_;
}
v___jp_2737_:
{
lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; uint8_t v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; 
v___x_2739_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__9));
v___x_2740_ = l_String_quote(v_s_2736_);
v___x_2741_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2741_, 0, v___x_2740_);
v___x_2742_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2742_, 0, v___x_2739_);
lean_ctor_set(v___x_2742_, 1, v___x_2741_);
lean_inc(v___y_2738_);
v___x_2743_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2743_, 0, v___y_2738_);
lean_ctor_set(v___x_2743_, 1, v___x_2742_);
v___x_2744_ = 0;
v___x_2745_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2745_, 0, v___x_2743_);
lean_ctor_set_uint8(v___x_2745_, sizeof(void*)*1, v___x_2744_);
v___x_2746_ = l_Repr_addAppParen(v___x_2745_, v_prec_2709_);
return v___x_2746_;
}
}
case 3:
{
lean_object* v_id_2751_; lean_object* v_d_2752_; lean_object* v___x_2753_; lean_object* v___y_2755_; uint8_t v___x_2768_; 
v_id_2751_ = lean_ctor_get(v_x_2708_, 1);
lean_inc(v_id_2751_);
v_d_2752_ = lean_ctor_get(v_x_2708_, 2);
lean_inc(v_d_2752_);
lean_dec_ref_known(v_x_2708_, 3);
v___x_2753_ = lean_unsigned_to_nat(1024u);
v___x_2768_ = lean_nat_dec_le(v___x_2753_, v_prec_2709_);
if (v___x_2768_ == 0)
{
lean_object* v___x_2769_; 
v___x_2769_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2755_ = v___x_2769_;
goto v___jp_2754_;
}
else
{
lean_object* v___x_2770_; 
v___x_2770_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2755_ = v___x_2770_;
goto v___jp_2754_;
}
v___jp_2754_:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; uint8_t v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; 
v___x_2756_ = lean_box(1);
v___x_2757_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__12));
v___x_2758_ = l_Nat_reprFast(v_id_2751_);
v___x_2759_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2759_, 0, v___x_2758_);
v___x_2760_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2760_, 0, v___x_2757_);
lean_ctor_set(v___x_2760_, 1, v___x_2759_);
v___x_2761_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2761_, 0, v___x_2760_);
lean_ctor_set(v___x_2761_, 1, v___x_2756_);
v___x_2762_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2707_, v_d_2752_, v___x_2753_);
v___x_2763_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2761_);
lean_ctor_set(v___x_2763_, 1, v___x_2762_);
lean_inc(v___y_2755_);
v___x_2764_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2764_, 0, v___y_2755_);
lean_ctor_set(v___x_2764_, 1, v___x_2763_);
v___x_2765_ = 0;
v___x_2766_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2766_, 0, v___x_2764_);
lean_ctor_set_uint8(v___x_2766_, sizeof(void*)*1, v___x_2765_);
v___x_2767_ = l_Repr_addAppParen(v___x_2766_, v_prec_2709_);
return v___x_2767_;
}
}
case 4:
{
lean_object* v_d_2771_; lean_object* v___x_2772_; lean_object* v___y_2774_; uint8_t v___x_2782_; 
v_d_2771_ = lean_ctor_get(v_x_2708_, 1);
lean_inc(v_d_2771_);
lean_dec_ref_known(v_x_2708_, 2);
v___x_2772_ = lean_unsigned_to_nat(1024u);
v___x_2782_ = lean_nat_dec_le(v___x_2772_, v_prec_2709_);
if (v___x_2782_ == 0)
{
lean_object* v___x_2783_; 
v___x_2783_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2774_ = v___x_2783_;
goto v___jp_2773_;
}
else
{
lean_object* v___x_2784_; 
v___x_2784_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2774_ = v___x_2784_;
goto v___jp_2773_;
}
v___jp_2773_:
{
lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; uint8_t v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; 
v___x_2775_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__15));
v___x_2776_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2707_, v_d_2771_, v___x_2772_);
v___x_2777_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2777_, 0, v___x_2775_);
lean_ctor_set(v___x_2777_, 1, v___x_2776_);
lean_inc(v___y_2774_);
v___x_2778_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2778_, 0, v___y_2774_);
lean_ctor_set(v___x_2778_, 1, v___x_2777_);
v___x_2779_ = 0;
v___x_2780_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2780_, 0, v___x_2778_);
lean_ctor_set_uint8(v___x_2780_, sizeof(void*)*1, v___x_2779_);
v___x_2781_ = l_Repr_addAppParen(v___x_2780_, v_prec_2709_);
return v___x_2781_;
}
}
case 5:
{
lean_object* v_d_2785_; lean_object* v___x_2786_; lean_object* v___y_2788_; uint8_t v___x_2796_; 
v_d_2785_ = lean_ctor_get(v_x_2708_, 1);
lean_inc(v_d_2785_);
lean_dec_ref_known(v_x_2708_, 2);
v___x_2786_ = lean_unsigned_to_nat(1024u);
v___x_2796_ = lean_nat_dec_le(v___x_2786_, v_prec_2709_);
if (v___x_2796_ == 0)
{
lean_object* v___x_2797_; 
v___x_2797_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2788_ = v___x_2797_;
goto v___jp_2787_;
}
else
{
lean_object* v___x_2798_; 
v___x_2798_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2788_ = v___x_2798_;
goto v___jp_2787_;
}
v___jp_2787_:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; uint8_t v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2789_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__18));
v___x_2790_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2707_, v_d_2785_, v___x_2786_);
v___x_2791_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2791_, 0, v___x_2789_);
lean_ctor_set(v___x_2791_, 1, v___x_2790_);
lean_inc(v___y_2788_);
v___x_2792_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2792_, 0, v___y_2788_);
lean_ctor_set(v___x_2792_, 1, v___x_2791_);
v___x_2793_ = 0;
v___x_2794_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2794_, 0, v___x_2792_);
lean_ctor_set_uint8(v___x_2794_, sizeof(void*)*1, v___x_2793_);
v___x_2795_ = l_Repr_addAppParen(v___x_2794_, v_prec_2709_);
return v___x_2795_;
}
}
case 6:
{
lean_object* v_n_2799_; uint8_t v_isCumulative_2800_; lean_object* v_d_2801_; lean_object* v___x_2802_; lean_object* v___y_2804_; uint8_t v___x_2820_; 
v_n_2799_ = lean_ctor_get(v_x_2708_, 1);
lean_inc(v_n_2799_);
v_isCumulative_2800_ = lean_ctor_get_uint8(v_x_2708_, sizeof(void*)*3 + 8);
v_d_2801_ = lean_ctor_get(v_x_2708_, 2);
lean_inc(v_d_2801_);
lean_dec_ref_known(v_x_2708_, 3);
v___x_2802_ = lean_unsigned_to_nat(1024u);
v___x_2820_ = lean_nat_dec_le(v___x_2802_, v_prec_2709_);
if (v___x_2820_ == 0)
{
lean_object* v___x_2821_; 
v___x_2821_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2804_ = v___x_2821_;
goto v___jp_2803_;
}
else
{
lean_object* v___x_2822_; 
v___x_2822_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2804_ = v___x_2822_;
goto v___jp_2803_;
}
v___jp_2803_:
{
lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; uint8_t v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; 
v___x_2805_ = lean_box(1);
v___x_2806_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__21));
v___x_2807_ = l_Nat_reprFast(v_n_2799_);
v___x_2808_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2807_);
v___x_2809_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2809_, 0, v___x_2806_);
lean_ctor_set(v___x_2809_, 1, v___x_2808_);
v___x_2810_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2810_, 0, v___x_2809_);
lean_ctor_set(v___x_2810_, 1, v___x_2805_);
v___x_2811_ = l_Bool_repr___redArg(v_isCumulative_2800_);
v___x_2812_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2812_, 0, v___x_2810_);
lean_ctor_set(v___x_2812_, 1, v___x_2811_);
v___x_2813_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2813_, 0, v___x_2812_);
lean_ctor_set(v___x_2813_, 1, v___x_2805_);
v___x_2814_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2707_, v_d_2801_, v___x_2802_);
v___x_2815_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2815_, 0, v___x_2813_);
lean_ctor_set(v___x_2815_, 1, v___x_2814_);
lean_inc(v___y_2804_);
v___x_2816_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2816_, 0, v___y_2804_);
lean_ctor_set(v___x_2816_, 1, v___x_2815_);
v___x_2817_ = 0;
v___x_2818_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2818_, 0, v___x_2816_);
lean_ctor_set_uint8(v___x_2818_, sizeof(void*)*1, v___x_2817_);
v___x_2819_ = l_Repr_addAppParen(v___x_2818_, v_prec_2709_);
return v___x_2819_;
}
}
case 7:
{
lean_object* v_d_2823_; lean_object* v___x_2824_; lean_object* v___y_2826_; uint8_t v___x_2834_; 
v_d_2823_ = lean_ctor_get(v_x_2708_, 1);
lean_inc(v_d_2823_);
lean_dec_ref_known(v_x_2708_, 2);
v___x_2824_ = lean_unsigned_to_nat(1024u);
v___x_2834_ = lean_nat_dec_le(v___x_2824_, v_prec_2709_);
if (v___x_2834_ == 0)
{
lean_object* v___x_2835_; 
v___x_2835_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2826_ = v___x_2835_;
goto v___jp_2825_;
}
else
{
lean_object* v___x_2836_; 
v___x_2836_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2826_ = v___x_2836_;
goto v___jp_2825_;
}
v___jp_2825_:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; uint8_t v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2827_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__24));
v___x_2828_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2707_, v_d_2823_, v___x_2824_);
v___x_2829_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2827_);
lean_ctor_set(v___x_2829_, 1, v___x_2828_);
lean_inc(v___y_2826_);
v___x_2830_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2830_, 0, v___y_2826_);
lean_ctor_set(v___x_2830_, 1, v___x_2829_);
v___x_2831_ = 0;
v___x_2832_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2832_, 0, v___x_2830_);
lean_ctor_set_uint8(v___x_2832_, sizeof(void*)*1, v___x_2831_);
v___x_2833_ = l_Repr_addAppParen(v___x_2832_, v_prec_2709_);
return v___x_2833_;
}
}
case 8:
{
uint8_t v_onlyNonCumulative_2837_; lean_object* v_d_2838_; lean_object* v___x_2839_; lean_object* v___y_2841_; uint8_t v___x_2853_; 
v_onlyNonCumulative_2837_ = lean_ctor_get_uint8(v_x_2708_, sizeof(void*)*2 + 8);
v_d_2838_ = lean_ctor_get(v_x_2708_, 1);
lean_inc(v_d_2838_);
lean_dec_ref_known(v_x_2708_, 2);
v___x_2839_ = lean_unsigned_to_nat(1024u);
v___x_2853_ = lean_nat_dec_le(v___x_2839_, v_prec_2709_);
if (v___x_2853_ == 0)
{
lean_object* v___x_2854_; 
v___x_2854_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2841_ = v___x_2854_;
goto v___jp_2840_;
}
else
{
lean_object* v___x_2855_; 
v___x_2855_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2841_ = v___x_2855_;
goto v___jp_2840_;
}
v___jp_2840_:
{
lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; uint8_t v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___x_2842_ = lean_box(1);
v___x_2843_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__27));
v___x_2844_ = l_Bool_repr___redArg(v_onlyNonCumulative_2837_);
v___x_2845_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2845_, 0, v___x_2843_);
lean_ctor_set(v___x_2845_, 1, v___x_2844_);
v___x_2846_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2846_, 0, v___x_2845_);
lean_ctor_set(v___x_2846_, 1, v___x_2842_);
v___x_2847_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2707_, v_d_2838_, v___x_2839_);
v___x_2848_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2846_);
lean_ctor_set(v___x_2848_, 1, v___x_2847_);
lean_inc(v___y_2841_);
v___x_2849_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2849_, 0, v___y_2841_);
lean_ctor_set(v___x_2849_, 1, v___x_2848_);
v___x_2850_ = 0;
v___x_2851_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2851_, 0, v___x_2849_);
lean_ctor_set_uint8(v___x_2851_, sizeof(void*)*1, v___x_2850_);
v___x_2852_ = l_Repr_addAppParen(v___x_2851_, v_prec_2709_);
return v___x_2852_;
}
}
case 9:
{
lean_object* v_d_2856_; lean_object* v___x_2857_; lean_object* v___y_2859_; uint8_t v___x_2867_; 
v_d_2856_ = lean_ctor_get(v_x_2708_, 1);
lean_inc(v_d_2856_);
lean_dec_ref_known(v_x_2708_, 2);
v___x_2857_ = lean_unsigned_to_nat(1024u);
v___x_2867_ = lean_nat_dec_le(v___x_2857_, v_prec_2709_);
if (v___x_2867_ == 0)
{
lean_object* v___x_2868_; 
v___x_2868_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2859_ = v___x_2868_;
goto v___jp_2858_;
}
else
{
lean_object* v___x_2869_; 
v___x_2869_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2859_ = v___x_2869_;
goto v___jp_2858_;
}
v___jp_2858_:
{
lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; uint8_t v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; 
v___x_2860_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__30));
v___x_2861_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2707_, v_d_2856_, v___x_2857_);
v___x_2862_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2862_, 0, v___x_2860_);
lean_ctor_set(v___x_2862_, 1, v___x_2861_);
lean_inc(v___y_2859_);
v___x_2863_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2863_, 0, v___y_2859_);
lean_ctor_set(v___x_2863_, 1, v___x_2862_);
v___x_2864_ = 0;
v___x_2865_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2865_, 0, v___x_2863_);
lean_ctor_set_uint8(v___x_2865_, sizeof(void*)*1, v___x_2864_);
v___x_2866_ = l_Repr_addAppParen(v___x_2865_, v_prec_2709_);
return v___x_2866_;
}
}
case 10:
{
lean_object* v_d_2870_; lean_object* v___x_2871_; lean_object* v___y_2873_; uint8_t v___x_2881_; 
v_d_2870_ = lean_ctor_get(v_x_2708_, 1);
lean_inc(v_d_2870_);
lean_dec_ref_known(v_x_2708_, 2);
v___x_2871_ = lean_unsigned_to_nat(1024u);
v___x_2881_ = lean_nat_dec_le(v___x_2871_, v_prec_2709_);
if (v___x_2881_ == 0)
{
lean_object* v___x_2882_; 
v___x_2882_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2873_ = v___x_2882_;
goto v___jp_2872_;
}
else
{
lean_object* v___x_2883_; 
v___x_2883_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2873_ = v___x_2883_;
goto v___jp_2872_;
}
v___jp_2872_:
{
lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; uint8_t v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; 
v___x_2874_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__33));
v___x_2875_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2707_, v_d_2870_, v___x_2871_);
v___x_2876_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2874_);
lean_ctor_set(v___x_2876_, 1, v___x_2875_);
lean_inc(v___y_2873_);
v___x_2877_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2877_, 0, v___y_2873_);
lean_ctor_set(v___x_2877_, 1, v___x_2876_);
v___x_2878_ = 0;
v___x_2879_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2879_, 0, v___x_2877_);
lean_ctor_set_uint8(v___x_2879_, sizeof(void*)*1, v___x_2878_);
v___x_2880_ = l_Repr_addAppParen(v___x_2879_, v_prec_2709_);
return v___x_2880_;
}
}
case 11:
{
lean_object* v_d_2884_; lean_object* v___x_2885_; lean_object* v___y_2887_; uint8_t v___x_2895_; 
v_d_2884_ = lean_ctor_get(v_x_2708_, 1);
lean_inc(v_d_2884_);
lean_dec_ref_known(v_x_2708_, 2);
v___x_2885_ = lean_unsigned_to_nat(1024u);
v___x_2895_ = lean_nat_dec_le(v___x_2885_, v_prec_2709_);
if (v___x_2895_ == 0)
{
lean_object* v___x_2896_; 
v___x_2896_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2887_ = v___x_2896_;
goto v___jp_2886_;
}
else
{
lean_object* v___x_2897_; 
v___x_2897_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2887_ = v___x_2897_;
goto v___jp_2886_;
}
v___jp_2886_:
{
lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; uint8_t v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; 
v___x_2888_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__36));
v___x_2889_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2707_, v_d_2884_, v___x_2885_);
v___x_2890_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2888_);
lean_ctor_set(v___x_2890_, 1, v___x_2889_);
lean_inc(v___y_2887_);
v___x_2891_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2891_, 0, v___y_2887_);
lean_ctor_set(v___x_2891_, 1, v___x_2890_);
v___x_2892_ = 0;
v___x_2893_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2893_, 0, v___x_2891_);
lean_ctor_set_uint8(v___x_2893_, sizeof(void*)*1, v___x_2892_);
v___x_2894_ = l_Repr_addAppParen(v___x_2893_, v_prec_2709_);
return v___x_2894_;
}
}
case 12:
{
lean_object* v_d_2898_; lean_object* v___x_2899_; lean_object* v___y_2901_; uint8_t v___x_2909_; 
v_d_2898_ = lean_ctor_get(v_x_2708_, 2);
lean_inc(v_d_2898_);
lean_dec_ref_known(v_x_2708_, 3);
v___x_2899_ = lean_unsigned_to_nat(1024u);
v___x_2909_ = lean_nat_dec_le(v___x_2899_, v_prec_2709_);
if (v___x_2909_ == 0)
{
lean_object* v___x_2910_; 
v___x_2910_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2901_ = v___x_2910_;
goto v___jp_2900_;
}
else
{
lean_object* v___x_2911_; 
v___x_2911_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2901_ = v___x_2911_;
goto v___jp_2900_;
}
v___jp_2900_:
{
lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; uint8_t v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; 
v___x_2902_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__41));
v___x_2903_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2707_, v_d_2898_, v___x_2899_);
v___x_2904_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2904_, 0, v___x_2902_);
lean_ctor_set(v___x_2904_, 1, v___x_2903_);
lean_inc(v___y_2901_);
v___x_2905_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2905_, 0, v___y_2901_);
lean_ctor_set(v___x_2905_, 1, v___x_2904_);
v___x_2906_ = 0;
v___x_2907_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2907_, 0, v___x_2905_);
lean_ctor_set_uint8(v___x_2907_, sizeof(void*)*1, v___x_2906_);
v___x_2908_ = l_Repr_addAppParen(v___x_2907_, v_prec_2709_);
return v___x_2908_;
}
}
case 13:
{
lean_object* v_cost_2912_; lean_object* v_d_2913_; lean_object* v___x_2914_; lean_object* v___y_2916_; uint8_t v___x_2928_; 
v_cost_2912_ = lean_ctor_get(v_x_2708_, 1);
lean_inc(v_cost_2912_);
v_d_2913_ = lean_ctor_get(v_x_2708_, 2);
lean_inc(v_d_2913_);
lean_dec_ref_known(v_x_2708_, 3);
v___x_2914_ = lean_unsigned_to_nat(1024u);
v___x_2928_ = lean_nat_dec_le(v___x_2914_, v_prec_2709_);
if (v___x_2928_ == 0)
{
lean_object* v___x_2929_; 
v___x_2929_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2916_ = v___x_2929_;
goto v___jp_2915_;
}
else
{
lean_object* v___x_2930_; 
v___x_2930_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2916_ = v___x_2930_;
goto v___jp_2915_;
}
v___jp_2915_:
{
lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; uint8_t v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___x_2917_ = lean_box(1);
v___x_2918_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__44));
lean_inc_ref(v_inst_2707_);
v___x_2919_ = lean_apply_2(v_inst_2707_, v_cost_2912_, v___x_2914_);
v___x_2920_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2920_, 0, v___x_2918_);
lean_ctor_set(v___x_2920_, 1, v___x_2919_);
v___x_2921_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2921_, 0, v___x_2920_);
lean_ctor_set(v___x_2921_, 1, v___x_2917_);
v___x_2922_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2707_, v_d_2913_, v___x_2914_);
v___x_2923_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2923_, 0, v___x_2921_);
lean_ctor_set(v___x_2923_, 1, v___x_2922_);
lean_inc(v___y_2916_);
v___x_2924_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2924_, 0, v___y_2916_);
lean_ctor_set(v___x_2924_, 1, v___x_2923_);
v___x_2925_ = 0;
v___x_2926_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2926_, 0, v___x_2924_);
lean_ctor_set_uint8(v___x_2926_, sizeof(void*)*1, v___x_2925_);
v___x_2927_ = l_Repr_addAppParen(v___x_2926_, v_prec_2709_);
return v___x_2927_;
}
}
case 14:
{
lean_object* v_a_2931_; lean_object* v_b_2932_; lean_object* v___x_2933_; lean_object* v___y_2935_; uint8_t v___x_2947_; 
v_a_2931_ = lean_ctor_get(v_x_2708_, 1);
lean_inc(v_a_2931_);
v_b_2932_ = lean_ctor_get(v_x_2708_, 2);
lean_inc(v_b_2932_);
lean_dec_ref_known(v_x_2708_, 3);
v___x_2933_ = lean_unsigned_to_nat(1024u);
v___x_2947_ = lean_nat_dec_le(v___x_2933_, v_prec_2709_);
if (v___x_2947_ == 0)
{
lean_object* v___x_2948_; 
v___x_2948_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2935_ = v___x_2948_;
goto v___jp_2934_;
}
else
{
lean_object* v___x_2949_; 
v___x_2949_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2935_ = v___x_2949_;
goto v___jp_2934_;
}
v___jp_2934_:
{
lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; uint8_t v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2936_ = lean_box(1);
v___x_2937_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__47));
lean_inc_ref(v_inst_2707_);
v___x_2938_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2707_, v_a_2931_, v___x_2933_);
v___x_2939_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2939_, 0, v___x_2937_);
lean_ctor_set(v___x_2939_, 1, v___x_2938_);
v___x_2940_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2940_, 0, v___x_2939_);
lean_ctor_set(v___x_2940_, 1, v___x_2936_);
v___x_2941_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2707_, v_b_2932_, v___x_2933_);
v___x_2942_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2940_);
lean_ctor_set(v___x_2942_, 1, v___x_2941_);
lean_inc(v___y_2935_);
v___x_2943_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2943_, 0, v___y_2935_);
lean_ctor_set(v___x_2943_, 1, v___x_2942_);
v___x_2944_ = 0;
v___x_2945_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2945_, 0, v___x_2943_);
lean_ctor_set_uint8(v___x_2945_, sizeof(void*)*1, v___x_2944_);
v___x_2946_ = l_Repr_addAppParen(v___x_2945_, v_prec_2709_);
return v___x_2946_;
}
}
default: 
{
lean_object* v_a_2950_; lean_object* v_b_2951_; lean_object* v___x_2952_; lean_object* v___y_2954_; uint8_t v___x_2966_; 
v_a_2950_ = lean_ctor_get(v_x_2708_, 1);
lean_inc(v_a_2950_);
v_b_2951_ = lean_ctor_get(v_x_2708_, 2);
lean_inc(v_b_2951_);
lean_dec_ref_known(v_x_2708_, 3);
v___x_2952_ = lean_unsigned_to_nat(1024u);
v___x_2966_ = lean_nat_dec_le(v___x_2952_, v_prec_2709_);
if (v___x_2966_ == 0)
{
lean_object* v___x_2967_; 
v___x_2967_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2954_ = v___x_2967_;
goto v___jp_2953_;
}
else
{
lean_object* v___x_2968_; 
v___x_2968_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2954_ = v___x_2968_;
goto v___jp_2953_;
}
v___jp_2953_:
{
lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; uint8_t v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
v___x_2955_ = lean_box(1);
v___x_2956_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__50));
lean_inc_ref(v_inst_2707_);
v___x_2957_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2707_, v_a_2950_, v___x_2952_);
v___x_2958_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2958_, 0, v___x_2956_);
lean_ctor_set(v___x_2958_, 1, v___x_2957_);
v___x_2959_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2958_);
lean_ctor_set(v___x_2959_, 1, v___x_2955_);
v___x_2960_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2707_, v_b_2951_, v___x_2952_);
v___x_2961_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2961_, 0, v___x_2959_);
lean_ctor_set(v___x_2961_, 1, v___x_2960_);
lean_inc(v___y_2954_);
v___x_2962_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2962_, 0, v___y_2954_);
lean_ctor_set(v___x_2962_, 1, v___x_2961_);
v___x_2963_ = 0;
v___x_2964_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2964_, 0, v___x_2962_);
lean_ctor_set_uint8(v___x_2964_, sizeof(void*)*1, v___x_2963_);
v___x_2965_ = l_Repr_addAppParen(v___x_2964_, v_prec_2709_);
return v___x_2965_;
}
}
}
v___jp_2710_:
{
lean_object* v___x_2712_; lean_object* v___x_2713_; uint8_t v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; 
v___x_2712_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__1));
lean_inc(v___y_2711_);
v___x_2713_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2713_, 0, v___y_2711_);
lean_ctor_set(v___x_2713_, 1, v___x_2712_);
v___x_2714_ = 0;
v___x_2715_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2715_, 0, v___x_2713_);
lean_ctor_set_uint8(v___x_2715_, sizeof(void*)*1, v___x_2714_);
v___x_2716_ = l_Repr_addAppParen(v___x_2715_, v_prec_2709_);
return v___x_2716_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___boxed(lean_object* v_inst_2969_, lean_object* v_x_2970_, lean_object* v_prec_2971_){
_start:
{
lean_object* v_res_2972_; 
v_res_2972_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2969_, v_x_2970_, v_prec_2971_);
lean_dec(v_prec_2971_);
return v_res_2972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprDoc_repr(lean_object* v_00_u03c4_2973_, lean_object* v_inst_2974_, lean_object* v_x_2975_, lean_object* v_prec_2976_){
_start:
{
lean_object* v___x_2977_; 
v___x_2977_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2974_, v_x_2975_, v_prec_2976_);
return v___x_2977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprDoc_repr___boxed(lean_object* v_00_u03c4_2978_, lean_object* v_inst_2979_, lean_object* v_x_2980_, lean_object* v_prec_2981_){
_start:
{
lean_object* v_res_2982_; 
v_res_2982_ = l_Lean_Fmt_instReprDoc_repr(v_00_u03c4_2978_, v_inst_2979_, v_x_2980_, v_prec_2981_);
lean_dec(v_prec_2981_);
return v_res_2982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprDoc___redArg(lean_object* v_inst_2983_){
_start:
{
lean_object* v___x_2984_; 
v___x_2984_ = lean_alloc_closure((void*)(l_Lean_Fmt_instReprDoc_repr___boxed), 4, 2);
lean_closure_set(v___x_2984_, 0, lean_box(0));
lean_closure_set(v___x_2984_, 1, v_inst_2983_);
return v___x_2984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprDoc(lean_object* v_00_u03c4_2985_, lean_object* v_inst_2986_){
_start:
{
lean_object* v___x_2987_; 
v___x_2987_ = lean_alloc_closure((void*)(l_Lean_Fmt_instReprDoc_repr___boxed), 4, 2);
lean_closure_set(v___x_2987_, 0, lean_box(0));
lean_closure_set(v___x_2987_, 1, v_inst_2986_);
return v___x_2987_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isFailure___redArg(lean_object* v_d_2988_, uint8_t v_fullness_2989_){
_start:
{
uint16_t v___x_2990_; uint16_t v___x_2991_; uint16_t v___x_2992_; uint16_t v___x_2993_; uint16_t v___x_2994_; uint16_t v___x_2995_; uint8_t v___x_2996_; 
v___x_2990_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_d_2988_);
v___x_2991_ = lean_uint8_to_uint16(v_fullness_2989_);
v___x_2992_ = lean_uint16_shift_right(v___x_2990_, v___x_2991_);
v___x_2993_ = 1;
v___x_2994_ = lean_uint16_land(v___x_2992_, v___x_2993_);
v___x_2995_ = 0;
v___x_2996_ = lean_uint16_dec_eq(v___x_2994_, v___x_2995_);
if (v___x_2996_ == 0)
{
uint8_t v___x_2997_; 
v___x_2997_ = 1;
return v___x_2997_;
}
else
{
uint8_t v___x_2998_; 
v___x_2998_ = 0;
return v___x_2998_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isFailure___redArg___boxed(lean_object* v_d_2999_, lean_object* v_fullness_3000_){
_start:
{
uint8_t v_fullness_boxed_3001_; uint8_t v_res_3002_; lean_object* v_r_3003_; 
v_fullness_boxed_3001_ = lean_unbox(v_fullness_3000_);
v_res_3002_ = l_Lean_Fmt_Doc_isFailure___redArg(v_d_2999_, v_fullness_boxed_3001_);
lean_dec(v_d_2999_);
v_r_3003_ = lean_box(v_res_3002_);
return v_r_3003_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isFailure(lean_object* v_00_u03c4_3004_, lean_object* v_d_3005_, uint8_t v_fullness_3006_){
_start:
{
uint8_t v___x_3007_; 
v___x_3007_ = l_Lean_Fmt_Doc_isFailure___redArg(v_d_3005_, v_fullness_3006_);
return v___x_3007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isFailure___boxed(lean_object* v_00_u03c4_3008_, lean_object* v_d_3009_, lean_object* v_fullness_3010_){
_start:
{
uint8_t v_fullness_boxed_3011_; uint8_t v_res_3012_; lean_object* v_r_3013_; 
v_fullness_boxed_3011_ = lean_unbox(v_fullness_3010_);
v_res_3012_ = l_Lean_Fmt_Doc_isFailure(v_00_u03c4_3008_, v_d_3009_, v_fullness_boxed_3011_);
lean_dec(v_d_3009_);
v_r_3013_ = lean_box(v_res_3012_);
return v_r_3013_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_neverFails___redArg(lean_object* v_d_3014_, uint8_t v_fullness_3015_){
_start:
{
uint16_t v___x_3016_; uint16_t v___x_3017_; uint16_t v___x_3018_; uint16_t v___x_3019_; uint16_t v___x_3020_; uint16_t v___x_3021_; uint8_t v___x_3022_; 
v___x_3016_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_d_3014_);
v___x_3017_ = lean_uint8_to_uint16(v_fullness_3015_);
v___x_3018_ = lean_uint16_shift_right(v___x_3016_, v___x_3017_);
v___x_3019_ = 1;
v___x_3020_ = lean_uint16_land(v___x_3018_, v___x_3019_);
v___x_3021_ = 0;
v___x_3022_ = lean_uint16_dec_eq(v___x_3020_, v___x_3021_);
if (v___x_3022_ == 0)
{
uint8_t v___x_3023_; 
v___x_3023_ = 1;
return v___x_3023_;
}
else
{
uint8_t v___x_3024_; 
v___x_3024_ = 0;
return v___x_3024_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_neverFails___redArg___boxed(lean_object* v_d_3025_, lean_object* v_fullness_3026_){
_start:
{
uint8_t v_fullness_boxed_3027_; uint8_t v_res_3028_; lean_object* v_r_3029_; 
v_fullness_boxed_3027_ = lean_unbox(v_fullness_3026_);
v_res_3028_ = l_Lean_Fmt_Doc_neverFails___redArg(v_d_3025_, v_fullness_boxed_3027_);
lean_dec(v_d_3025_);
v_r_3029_ = lean_box(v_res_3028_);
return v_r_3029_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_neverFails(lean_object* v_00_u03c4_3030_, lean_object* v_d_3031_, uint8_t v_fullness_3032_){
_start:
{
uint8_t v___x_3033_; 
v___x_3033_ = l_Lean_Fmt_Doc_neverFails___redArg(v_d_3031_, v_fullness_3032_);
return v___x_3033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_neverFails___boxed(lean_object* v_00_u03c4_3034_, lean_object* v_d_3035_, lean_object* v_fullness_3036_){
_start:
{
uint8_t v_fullness_boxed_3037_; uint8_t v_res_3038_; lean_object* v_r_3039_; 
v_fullness_boxed_3037_ = lean_unbox(v_fullness_3036_);
v_res_3038_ = l_Lean_Fmt_Doc_neverFails(v_00_u03c4_3034_, v_d_3035_, v_fullness_boxed_3037_);
lean_dec(v_d_3035_);
v_r_3039_ = lean_box(v_res_3038_);
return v_r_3039_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_hasContextDependentFailure___redArg(lean_object* v_d_3040_, uint8_t v_fullness_3041_){
_start:
{
uint16_t v___x_3042_; uint16_t v___x_3043_; uint16_t v___x_3044_; uint16_t v___x_3045_; uint16_t v___x_3046_; uint16_t v___x_3047_; uint16_t v___x_3048_; uint16_t v___x_3049_; uint8_t v___x_3050_; 
v___x_3042_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_d_3040_);
v___x_3043_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_d_3040_);
v___x_3044_ = lean_uint16_lor(v___x_3042_, v___x_3043_);
v___x_3045_ = lean_uint8_to_uint16(v_fullness_3041_);
v___x_3046_ = lean_uint16_shift_right(v___x_3044_, v___x_3045_);
v___x_3047_ = 1;
v___x_3048_ = lean_uint16_land(v___x_3046_, v___x_3047_);
v___x_3049_ = 0;
v___x_3050_ = lean_uint16_dec_eq(v___x_3048_, v___x_3049_);
return v___x_3050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_hasContextDependentFailure___redArg___boxed(lean_object* v_d_3051_, lean_object* v_fullness_3052_){
_start:
{
uint8_t v_fullness_boxed_3053_; uint8_t v_res_3054_; lean_object* v_r_3055_; 
v_fullness_boxed_3053_ = lean_unbox(v_fullness_3052_);
v_res_3054_ = l_Lean_Fmt_Doc_hasContextDependentFailure___redArg(v_d_3051_, v_fullness_boxed_3053_);
lean_dec(v_d_3051_);
v_r_3055_ = lean_box(v_res_3054_);
return v_r_3055_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_hasContextDependentFailure(lean_object* v_00_u03c4_3056_, lean_object* v_d_3057_, uint8_t v_fullness_3058_){
_start:
{
uint8_t v___x_3059_; 
v___x_3059_ = l_Lean_Fmt_Doc_hasContextDependentFailure___redArg(v_d_3057_, v_fullness_3058_);
return v___x_3059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_hasContextDependentFailure___boxed(lean_object* v_00_u03c4_3060_, lean_object* v_d_3061_, lean_object* v_fullness_3062_){
_start:
{
uint8_t v_fullness_boxed_3063_; uint8_t v_res_3064_; lean_object* v_r_3065_; 
v_fullness_boxed_3063_ = lean_unbox(v_fullness_3062_);
v_res_3064_ = l_Lean_Fmt_Doc_hasContextDependentFailure(v_00_u03c4_3060_, v_d_3061_, v_fullness_boxed_3063_);
lean_dec(v_d_3061_);
v_r_3065_ = lean_box(v_res_3064_);
return v_r_3065_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(lean_object* v_d_3066_){
_start:
{
uint8_t v___x_3067_; 
v___x_3067_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_3066_);
if (v___x_3067_ == 0)
{
uint8_t v___x_3068_; 
v___x_3068_ = 1;
return v___x_3068_;
}
else
{
uint8_t v___x_3069_; 
v___x_3069_ = 0;
return v___x_3069_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isAlwaysEmpty___redArg___boxed(lean_object* v_d_3070_){
_start:
{
uint8_t v_res_3071_; lean_object* v_r_3072_; 
v_res_3071_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_d_3070_);
lean_dec(v_d_3070_);
v_r_3072_ = lean_box(v_res_3071_);
return v_r_3072_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isAlwaysEmpty(lean_object* v_00_u03c4_3073_, lean_object* v_d_3074_){
_start:
{
uint8_t v___x_3075_; 
v___x_3075_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_d_3074_);
return v___x_3075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isAlwaysEmpty___boxed(lean_object* v_00_u03c4_3076_, lean_object* v_d_3077_){
_start:
{
uint8_t v_res_3078_; lean_object* v_r_3079_; 
v_res_3078_ = l_Lean_Fmt_Doc_isAlwaysEmpty(v_00_u03c4_3076_, v_d_3077_);
lean_dec(v_d_3077_);
v_r_3079_ = lean_box(v_res_3078_);
return v_r_3079_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isAlwaysNonEmpty___redArg(lean_object* v_d_3080_){
_start:
{
uint8_t v___x_3081_; 
v___x_3081_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_3080_);
if (v___x_3081_ == 0)
{
uint8_t v___x_3082_; 
v___x_3082_ = 1;
return v___x_3082_;
}
else
{
uint8_t v___x_3083_; 
v___x_3083_ = 0;
return v___x_3083_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isAlwaysNonEmpty___redArg___boxed(lean_object* v_d_3084_){
_start:
{
uint8_t v_res_3085_; lean_object* v_r_3086_; 
v_res_3085_ = l_Lean_Fmt_Doc_isAlwaysNonEmpty___redArg(v_d_3084_);
lean_dec(v_d_3084_);
v_r_3086_ = lean_box(v_res_3085_);
return v_r_3086_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isAlwaysNonEmpty(lean_object* v_00_u03c4_3087_, lean_object* v_d_3088_){
_start:
{
uint8_t v___x_3089_; 
v___x_3089_ = l_Lean_Fmt_Doc_isAlwaysNonEmpty___redArg(v_d_3088_);
return v___x_3089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isAlwaysNonEmpty___boxed(lean_object* v_00_u03c4_3090_, lean_object* v_d_3091_){
_start:
{
uint8_t v_res_3092_; lean_object* v_r_3093_; 
v_res_3092_ = l_Lean_Fmt_Doc_isAlwaysNonEmpty(v_00_u03c4_3090_, v_d_3091_);
lean_dec(v_d_3091_);
v_r_3093_ = lean_box(v_res_3092_);
return v_r_3093_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isCompoundAtomic___redArg(lean_object* v_d_3094_){
_start:
{
uint8_t v___x_3095_; 
v___x_3095_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_3094_);
if (v___x_3095_ == 2)
{
uint8_t v___x_3096_; 
v___x_3096_ = 1;
return v___x_3096_;
}
else
{
if (v___x_3095_ == 0)
{
uint8_t v___x_3097_; 
v___x_3097_ = 1;
return v___x_3097_;
}
else
{
uint8_t v___x_3098_; 
v___x_3098_ = 0;
return v___x_3098_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isCompoundAtomic___redArg___boxed(lean_object* v_d_3099_){
_start:
{
uint8_t v_res_3100_; lean_object* v_r_3101_; 
v_res_3100_ = l_Lean_Fmt_Doc_isCompoundAtomic___redArg(v_d_3099_);
lean_dec(v_d_3099_);
v_r_3101_ = lean_box(v_res_3100_);
return v_r_3101_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isCompoundAtomic(lean_object* v_00_u03c4_3102_, lean_object* v_d_3103_){
_start:
{
uint8_t v___x_3104_; 
v___x_3104_ = l_Lean_Fmt_Doc_isCompoundAtomic___redArg(v_d_3103_);
return v___x_3104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isCompoundAtomic___boxed(lean_object* v_00_u03c4_3105_, lean_object* v_d_3106_){
_start:
{
uint8_t v_res_3107_; lean_object* v_r_3108_; 
v_res_3107_ = l_Lean_Fmt_Doc_isCompoundAtomic(v_00_u03c4_3105_, v_d_3106_);
lean_dec(v_d_3106_);
v_r_3108_ = lean_box(v_res_3107_);
return v_r_3108_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isAtomic___redArg(lean_object* v_d_3109_){
_start:
{
uint8_t v___x_3110_; 
v___x_3110_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_3109_);
if (v___x_3110_ == 0)
{
uint8_t v___x_3111_; 
v___x_3111_ = 1;
return v___x_3111_;
}
else
{
uint8_t v___x_3112_; 
v___x_3112_ = 0;
return v___x_3112_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isAtomic___redArg___boxed(lean_object* v_d_3113_){
_start:
{
uint8_t v_res_3114_; lean_object* v_r_3115_; 
v_res_3114_ = l_Lean_Fmt_Doc_isAtomic___redArg(v_d_3113_);
lean_dec(v_d_3113_);
v_r_3115_ = lean_box(v_res_3114_);
return v_r_3115_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isAtomic(lean_object* v_00_u03c4_3116_, lean_object* v_d_3117_){
_start:
{
uint8_t v___x_3118_; 
v___x_3118_ = l_Lean_Fmt_Doc_isAtomic___redArg(v_d_3117_);
return v___x_3118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isAtomic___boxed(lean_object* v_00_u03c4_3119_, lean_object* v_d_3120_){
_start:
{
uint8_t v_res_3121_; lean_object* v_r_3122_; 
v_res_3121_ = l_Lean_Fmt_Doc_isAtomic(v_00_u03c4_3119_, v_d_3120_);
lean_dec(v_d_3120_);
v_r_3122_ = lean_box(v_res_3121_);
return v_r_3122_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_empty___redArg___closed__1(void){
_start:
{
lean_object* v___x_3124_; lean_object* v___x_3125_; 
v___x_3124_ = ((lean_object*)(l_Lean_Fmt_Doc_empty___redArg___closed__0));
v___x_3125_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_3124_);
return v___x_3125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_empty___redArg(){
_start:
{
lean_object* v___x_3127_; 
v___x_3127_ = lean_obj_once(&l_Lean_Fmt_Doc_empty___redArg___closed__1, &l_Lean_Fmt_Doc_empty___redArg___closed__1_once, _init_l_Lean_Fmt_Doc_empty___redArg___closed__1);
return v___x_3127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_empty___redArg___boxed(lean_object* v___dummy_3128_){
_start:
{
lean_object* v_res_3129_; 
v_res_3129_ = l_Lean_Fmt_Doc_empty___redArg();
return v_res_3129_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_empty___closed__0(void){
_start:
{
lean_object* v___x_3130_; 
v___x_3130_ = l_Lean_Fmt_Doc_empty___redArg();
return v___x_3130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_empty(lean_object* v_00_u03c4_3131_){
_start:
{
lean_object* v___x_3132_; 
v___x_3132_ = lean_obj_once(&l_Lean_Fmt_Doc_empty___closed__0, &l_Lean_Fmt_Doc_empty___closed__0_once, _init_l_Lean_Fmt_Doc_empty___closed__0);
return v___x_3132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maybeFlattened___redArg(lean_object* v_d_3133_){
_start:
{
lean_object* v___x_3134_; lean_object* v___x_3135_; 
lean_inc(v_d_3133_);
v___x_3134_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_d_3133_);
v___x_3135_ = l_Lean_Fmt_Doc_either___override___redArg(v_d_3133_, v___x_3134_);
return v___x_3135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maybeFlattened(lean_object* v_00_u03c4_3136_, lean_object* v_d_3137_){
_start:
{
lean_object* v___x_3138_; 
v___x_3138_ = l_Lean_Fmt_Doc_maybeFlattened___redArg(v_d_3137_);
return v___x_3138_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_nl___redArg___closed__1(void){
_start:
{
lean_object* v___x_3140_; lean_object* v___x_3141_; 
v___x_3140_ = ((lean_object*)(l_Lean_Fmt_Doc_nl___redArg___closed__0));
v___x_3141_ = l_Lean_Fmt_Doc_newline___override___redArg(v___x_3140_);
return v___x_3141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_nl___redArg(){
_start:
{
lean_object* v___x_3143_; 
v___x_3143_ = lean_obj_once(&l_Lean_Fmt_Doc_nl___redArg___closed__1, &l_Lean_Fmt_Doc_nl___redArg___closed__1_once, _init_l_Lean_Fmt_Doc_nl___redArg___closed__1);
return v___x_3143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_nl___redArg___boxed(lean_object* v___dummy_3144_){
_start:
{
lean_object* v_res_3145_; 
v_res_3145_ = l_Lean_Fmt_Doc_nl___redArg();
return v_res_3145_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_nl___closed__0(void){
_start:
{
lean_object* v___x_3146_; 
v___x_3146_ = l_Lean_Fmt_Doc_nl___redArg();
return v___x_3146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_nl(lean_object* v_00_u03c4_3147_){
_start:
{
lean_object* v___x_3148_; 
v___x_3148_ = lean_obj_once(&l_Lean_Fmt_Doc_nl___closed__0, &l_Lean_Fmt_Doc_nl___closed__0_once, _init_l_Lean_Fmt_Doc_nl___closed__0);
return v___x_3148_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_break___redArg___closed__0(void){
_start:
{
lean_object* v___x_3149_; lean_object* v___x_3150_; 
v___x_3149_ = ((lean_object*)(l_Lean_Fmt_Doc_empty___redArg___closed__0));
v___x_3150_ = l_Lean_Fmt_Doc_newline___override___redArg(v___x_3149_);
return v___x_3150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_break___redArg(){
_start:
{
lean_object* v___x_3152_; 
v___x_3152_ = lean_obj_once(&l_Lean_Fmt_Doc_break___redArg___closed__0, &l_Lean_Fmt_Doc_break___redArg___closed__0_once, _init_l_Lean_Fmt_Doc_break___redArg___closed__0);
return v___x_3152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_break___redArg___boxed(lean_object* v___dummy_3153_){
_start:
{
lean_object* v_res_3154_; 
v_res_3154_ = l_Lean_Fmt_Doc_break___redArg();
return v_res_3154_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_break___closed__0(void){
_start:
{
lean_object* v___x_3155_; 
v___x_3155_ = l_Lean_Fmt_Doc_break___redArg();
return v___x_3155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_break(lean_object* v_00_u03c4_3156_){
_start:
{
lean_object* v___x_3157_; 
v___x_3157_ = lean_obj_once(&l_Lean_Fmt_Doc_break___closed__0, &l_Lean_Fmt_Doc_break___closed__0_once, _init_l_Lean_Fmt_Doc_break___closed__0);
return v___x_3157_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_hardNl___redArg___closed__0(void){
_start:
{
lean_object* v___x_3158_; lean_object* v___x_3159_; 
v___x_3158_ = lean_obj_once(&l_Lean_Fmt_Doc_nl___closed__0, &l_Lean_Fmt_Doc_nl___closed__0_once, _init_l_Lean_Fmt_Doc_nl___closed__0);
v___x_3159_ = l_Lean_Fmt_Doc_unflattenable___override___redArg(v___x_3158_);
return v___x_3159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_hardNl___redArg(){
_start:
{
lean_object* v___x_3161_; 
v___x_3161_ = lean_obj_once(&l_Lean_Fmt_Doc_hardNl___redArg___closed__0, &l_Lean_Fmt_Doc_hardNl___redArg___closed__0_once, _init_l_Lean_Fmt_Doc_hardNl___redArg___closed__0);
return v___x_3161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_hardNl___redArg___boxed(lean_object* v___dummy_3162_){
_start:
{
lean_object* v_res_3163_; 
v_res_3163_ = l_Lean_Fmt_Doc_hardNl___redArg();
return v_res_3163_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_hardNl___closed__0(void){
_start:
{
lean_object* v___x_3164_; 
v___x_3164_ = l_Lean_Fmt_Doc_hardNl___redArg();
return v___x_3164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_hardNl(lean_object* v_00_u03c4_3165_){
_start:
{
lean_object* v___x_3166_; 
v___x_3166_ = lean_obj_once(&l_Lean_Fmt_Doc_hardNl___closed__0, &l_Lean_Fmt_Doc_hardNl___closed__0_once, _init_l_Lean_Fmt_Doc_hardNl___closed__0);
return v___x_3166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_nested___redArg(lean_object* v_d_3167_){
_start:
{
lean_object* v___x_3168_; uint8_t v___x_3169_; lean_object* v___x_3170_; 
v___x_3168_ = lean_unsigned_to_nat(2u);
v___x_3169_ = 0;
v___x_3170_ = l_Lean_Fmt_Doc_indented___override___redArg(v___x_3168_, v___x_3169_, v_d_3167_);
return v___x_3170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_nested(lean_object* v_00_u03c4_3171_, lean_object* v_d_3172_){
_start:
{
lean_object* v___x_3173_; 
v___x_3173_ = l_Lean_Fmt_Doc_nested___redArg(v_d_3172_);
return v___x_3173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_hardNested___redArg(lean_object* v_d_3174_){
_start:
{
lean_object* v___x_3175_; uint8_t v___x_3176_; lean_object* v___x_3177_; 
v___x_3175_ = lean_unsigned_to_nat(2u);
v___x_3176_ = 1;
v___x_3177_ = l_Lean_Fmt_Doc_indented___override___redArg(v___x_3175_, v___x_3176_, v_d_3174_);
return v___x_3177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_hardNested(lean_object* v_00_u03c4_3178_, lean_object* v_d_3179_){
_start:
{
lean_object* v___x_3180_; 
v___x_3180_ = l_Lean_Fmt_Doc_hardNested___redArg(v_d_3179_);
return v___x_3180_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_oneOf_spec__0___redArg(lean_object* v_a_3181_, lean_object* v_b_3182_){
_start:
{
lean_object* v_array_3183_; lean_object* v_start_3184_; lean_object* v_stop_3185_; lean_object* v___x_3187_; uint8_t v_isShared_3188_; uint8_t v_isSharedCheck_3198_; 
v_array_3183_ = lean_ctor_get(v_a_3181_, 0);
v_start_3184_ = lean_ctor_get(v_a_3181_, 1);
v_stop_3185_ = lean_ctor_get(v_a_3181_, 2);
v_isSharedCheck_3198_ = !lean_is_exclusive(v_a_3181_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3187_ = v_a_3181_;
v_isShared_3188_ = v_isSharedCheck_3198_;
goto v_resetjp_3186_;
}
else
{
lean_inc(v_stop_3185_);
lean_inc(v_start_3184_);
lean_inc(v_array_3183_);
lean_dec(v_a_3181_);
v___x_3187_ = lean_box(0);
v_isShared_3188_ = v_isSharedCheck_3198_;
goto v_resetjp_3186_;
}
v_resetjp_3186_:
{
uint8_t v___x_3189_; 
v___x_3189_ = lean_nat_dec_lt(v_start_3184_, v_stop_3185_);
if (v___x_3189_ == 0)
{
lean_del_object(v___x_3187_);
lean_dec(v_stop_3185_);
lean_dec(v_start_3184_);
lean_dec_ref(v_array_3183_);
return v_b_3182_;
}
else
{
lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3193_; 
v___x_3190_ = lean_unsigned_to_nat(1u);
v___x_3191_ = lean_nat_add(v_start_3184_, v___x_3190_);
lean_inc_ref(v_array_3183_);
if (v_isShared_3188_ == 0)
{
lean_ctor_set(v___x_3187_, 1, v___x_3191_);
v___x_3193_ = v___x_3187_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v_array_3183_);
lean_ctor_set(v_reuseFailAlloc_3197_, 1, v___x_3191_);
lean_ctor_set(v_reuseFailAlloc_3197_, 2, v_stop_3185_);
v___x_3193_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
lean_object* v___x_3194_; lean_object* v___x_3195_; 
v___x_3194_ = lean_array_fget(v_array_3183_, v_start_3184_);
lean_dec(v_start_3184_);
lean_dec_ref(v_array_3183_);
v___x_3195_ = l_Lean_Fmt_Doc_either___override___redArg(v_b_3182_, v___x_3194_);
v_a_3181_ = v___x_3193_;
v_b_3182_ = v___x_3195_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_oneOf___redArg(lean_object* v_ds_3199_){
_start:
{
lean_object* v___x_3200_; lean_object* v___x_3201_; uint8_t v___x_3202_; 
v___x_3200_ = lean_unsigned_to_nat(0u);
v___x_3201_ = lean_array_get_size(v_ds_3199_);
v___x_3202_ = lean_nat_dec_lt(v___x_3200_, v___x_3201_);
if (v___x_3202_ == 0)
{
lean_object* v___x_3203_; 
lean_dec_ref(v_ds_3199_);
v___x_3203_ = lean_box(0);
return v___x_3203_;
}
else
{
lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3204_ = lean_array_fget(v_ds_3199_, v___x_3200_);
v___x_3205_ = lean_unsigned_to_nat(1u);
v___x_3206_ = l_Array_toSubarray___redArg(v_ds_3199_, v___x_3205_, v___x_3201_);
v___x_3207_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_oneOf_spec__0___redArg(v___x_3206_, v___x_3204_);
return v___x_3207_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_oneOf(lean_object* v_00_u03c4_3208_, lean_object* v_ds_3209_){
_start:
{
lean_object* v___x_3210_; 
v___x_3210_ = l_Lean_Fmt_Doc_oneOf___redArg(v_ds_3209_);
return v___x_3210_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_oneOf_spec__0(lean_object* v_00_u03c4_3211_, lean_object* v_inst_3212_, lean_object* v_R_3213_, lean_object* v_a_3214_, lean_object* v_b_3215_, lean_object* v_c_3216_){
_start:
{
lean_object* v___x_3217_; 
v___x_3217_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_oneOf_spec__0___redArg(v_a_3214_, v_b_3215_);
return v___x_3217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instAppendDoc___redArg___lam__0(lean_object* v_d1_3218_, lean_object* v_d2_3219_){
_start:
{
uint8_t v___x_3220_; 
v___x_3220_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_d1_3218_);
if (v___x_3220_ == 0)
{
uint8_t v___x_3221_; 
v___x_3221_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_d2_3219_);
if (v___x_3221_ == 0)
{
lean_object* v___x_3222_; 
v___x_3222_ = l_Lean_Fmt_Doc_append___override___redArg(v_d1_3218_, v_d2_3219_);
return v___x_3222_;
}
else
{
lean_dec(v_d2_3219_);
return v_d1_3218_;
}
}
else
{
lean_dec(v_d1_3218_);
return v_d2_3219_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instAppendDoc___redArg(){
_start:
{
lean_object* v___f_3225_; 
v___f_3225_ = ((lean_object*)(l_Lean_Fmt_instAppendDoc___redArg___closed__0));
return v___f_3225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instAppendDoc___redArg___boxed(lean_object* v___dummy_3226_){
_start:
{
lean_object* v_res_3227_; 
v_res_3227_ = l_Lean_Fmt_instAppendDoc___redArg();
return v_res_3227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instAppendDoc(lean_object* v_00_u03c4_3228_){
_start:
{
lean_object* v___f_3229_; 
v___f_3229_ = ((lean_object*)(l_Lean_Fmt_instAppendDoc___redArg___closed__0));
return v___f_3229_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_join_spec__0___redArg(lean_object* v_a_3230_, lean_object* v_b_3231_){
_start:
{
lean_object* v_array_3232_; lean_object* v_start_3233_; lean_object* v_stop_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3251_; 
v_array_3232_ = lean_ctor_get(v_a_3230_, 0);
v_start_3233_ = lean_ctor_get(v_a_3230_, 1);
v_stop_3234_ = lean_ctor_get(v_a_3230_, 2);
v_isSharedCheck_3251_ = !lean_is_exclusive(v_a_3230_);
if (v_isSharedCheck_3251_ == 0)
{
v___x_3236_ = v_a_3230_;
v_isShared_3237_ = v_isSharedCheck_3251_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_stop_3234_);
lean_inc(v_start_3233_);
lean_inc(v_array_3232_);
lean_dec(v_a_3230_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3251_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
uint8_t v___x_3238_; 
v___x_3238_ = lean_nat_dec_lt(v_start_3233_, v_stop_3234_);
if (v___x_3238_ == 0)
{
lean_del_object(v___x_3236_);
lean_dec(v_stop_3234_);
lean_dec(v_start_3233_);
lean_dec_ref(v_array_3232_);
return v_b_3231_;
}
else
{
lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3242_; 
v___x_3239_ = lean_unsigned_to_nat(1u);
v___x_3240_ = lean_nat_add(v_start_3233_, v___x_3239_);
lean_inc_ref(v_array_3232_);
if (v_isShared_3237_ == 0)
{
lean_ctor_set(v___x_3236_, 1, v___x_3240_);
v___x_3242_ = v___x_3236_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v_array_3232_);
lean_ctor_set(v_reuseFailAlloc_3250_, 1, v___x_3240_);
lean_ctor_set(v_reuseFailAlloc_3250_, 2, v_stop_3234_);
v___x_3242_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
lean_object* v___x_3243_; uint8_t v___x_3244_; 
v___x_3243_ = lean_array_fget(v_array_3232_, v_start_3233_);
lean_dec(v_start_3233_);
lean_dec_ref(v_array_3232_);
v___x_3244_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_b_3231_);
if (v___x_3244_ == 0)
{
uint8_t v___x_3245_; 
v___x_3245_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v___x_3243_);
if (v___x_3245_ == 0)
{
lean_object* v___x_3246_; 
v___x_3246_ = l_Lean_Fmt_Doc_append___override___redArg(v_b_3231_, v___x_3243_);
v_a_3230_ = v___x_3242_;
v_b_3231_ = v___x_3246_;
goto _start;
}
else
{
lean_dec(v___x_3243_);
v_a_3230_ = v___x_3242_;
goto _start;
}
}
else
{
lean_dec(v_b_3231_);
v_a_3230_ = v___x_3242_;
v_b_3231_ = v___x_3243_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_join___redArg(lean_object* v_ds_3252_){
_start:
{
lean_object* v___x_3253_; lean_object* v___x_3254_; uint8_t v___x_3255_; 
v___x_3253_ = lean_unsigned_to_nat(0u);
v___x_3254_ = lean_array_get_size(v_ds_3252_);
v___x_3255_ = lean_nat_dec_lt(v___x_3253_, v___x_3254_);
if (v___x_3255_ == 0)
{
lean_object* v___x_3256_; 
lean_dec_ref(v_ds_3252_);
v___x_3256_ = lean_obj_once(&l_Lean_Fmt_Doc_empty___redArg___closed__1, &l_Lean_Fmt_Doc_empty___redArg___closed__1_once, _init_l_Lean_Fmt_Doc_empty___redArg___closed__1);
return v___x_3256_;
}
else
{
lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; 
v___x_3257_ = lean_array_fget(v_ds_3252_, v___x_3253_);
v___x_3258_ = lean_unsigned_to_nat(1u);
v___x_3259_ = l_Array_toSubarray___redArg(v_ds_3252_, v___x_3258_, v___x_3254_);
v___x_3260_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_join_spec__0___redArg(v___x_3259_, v___x_3257_);
return v___x_3260_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_join(lean_object* v_00_u03c4_3261_, lean_object* v_ds_3262_){
_start:
{
lean_object* v___x_3263_; 
v___x_3263_ = l_Lean_Fmt_Doc_join___redArg(v_ds_3262_);
return v___x_3263_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_join_spec__0(lean_object* v_00_u03c4_3264_, lean_object* v_inst_3265_, lean_object* v_R_3266_, lean_object* v_a_3267_, lean_object* v_b_3268_, lean_object* v_c_3269_){
_start:
{
lean_object* v___x_3270_; 
v___x_3270_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_join_spec__0___redArg(v_a_3267_, v_b_3268_);
return v___x_3270_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_joinUsing_spec__0___redArg(lean_object* v_sep_3271_, lean_object* v_a_3272_, lean_object* v_b_3273_){
_start:
{
lean_object* v_array_3274_; lean_object* v_start_3275_; lean_object* v_stop_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3298_; 
v_array_3274_ = lean_ctor_get(v_a_3272_, 0);
v_start_3275_ = lean_ctor_get(v_a_3272_, 1);
v_stop_3276_ = lean_ctor_get(v_a_3272_, 2);
v_isSharedCheck_3298_ = !lean_is_exclusive(v_a_3272_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3278_ = v_a_3272_;
v_isShared_3279_ = v_isSharedCheck_3298_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_stop_3276_);
lean_inc(v_start_3275_);
lean_inc(v_array_3274_);
lean_dec(v_a_3272_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3298_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
uint8_t v___x_3280_; 
v___x_3280_ = lean_nat_dec_lt(v_start_3275_, v_stop_3276_);
if (v___x_3280_ == 0)
{
lean_del_object(v___x_3278_);
lean_dec(v_stop_3276_);
lean_dec(v_start_3275_);
lean_dec_ref(v_array_3274_);
lean_dec(v_sep_3271_);
return v_b_3273_;
}
else
{
lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3284_; 
v___x_3281_ = lean_unsigned_to_nat(1u);
v___x_3282_ = lean_nat_add(v_start_3275_, v___x_3281_);
lean_inc_ref(v_array_3274_);
if (v_isShared_3279_ == 0)
{
lean_ctor_set(v___x_3278_, 1, v___x_3282_);
v___x_3284_ = v___x_3278_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v_array_3274_);
lean_ctor_set(v_reuseFailAlloc_3297_, 1, v___x_3282_);
lean_ctor_set(v_reuseFailAlloc_3297_, 2, v_stop_3276_);
v___x_3284_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
lean_object* v___x_3285_; lean_object* v___y_3287_; uint8_t v___x_3294_; 
v___x_3285_ = lean_array_fget(v_array_3274_, v_start_3275_);
lean_dec(v_start_3275_);
lean_dec_ref(v_array_3274_);
v___x_3294_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_b_3273_);
if (v___x_3294_ == 0)
{
uint8_t v___x_3295_; 
v___x_3295_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_sep_3271_);
if (v___x_3295_ == 0)
{
lean_object* v___x_3296_; 
lean_inc(v_sep_3271_);
v___x_3296_ = l_Lean_Fmt_Doc_append___override___redArg(v_b_3273_, v_sep_3271_);
v___y_3287_ = v___x_3296_;
goto v___jp_3286_;
}
else
{
v___y_3287_ = v_b_3273_;
goto v___jp_3286_;
}
}
else
{
lean_dec(v_b_3273_);
lean_inc(v_sep_3271_);
v___y_3287_ = v_sep_3271_;
goto v___jp_3286_;
}
v___jp_3286_:
{
uint8_t v___x_3288_; 
v___x_3288_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v___y_3287_);
if (v___x_3288_ == 0)
{
uint8_t v___x_3289_; 
v___x_3289_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v___x_3285_);
if (v___x_3289_ == 0)
{
lean_object* v___x_3290_; 
v___x_3290_ = l_Lean_Fmt_Doc_append___override___redArg(v___y_3287_, v___x_3285_);
v_a_3272_ = v___x_3284_;
v_b_3273_ = v___x_3290_;
goto _start;
}
else
{
lean_dec(v___x_3285_);
v_a_3272_ = v___x_3284_;
v_b_3273_ = v___y_3287_;
goto _start;
}
}
else
{
lean_dec(v___y_3287_);
v_a_3272_ = v___x_3284_;
v_b_3273_ = v___x_3285_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_joinUsing___redArg(lean_object* v_sep_3299_, lean_object* v_ds_3300_){
_start:
{
lean_object* v___x_3301_; lean_object* v___x_3302_; uint8_t v___x_3303_; 
v___x_3301_ = lean_unsigned_to_nat(0u);
v___x_3302_ = lean_array_get_size(v_ds_3300_);
v___x_3303_ = lean_nat_dec_lt(v___x_3301_, v___x_3302_);
if (v___x_3303_ == 0)
{
lean_object* v___x_3304_; 
lean_dec_ref(v_ds_3300_);
lean_dec(v_sep_3299_);
v___x_3304_ = lean_obj_once(&l_Lean_Fmt_Doc_empty___redArg___closed__1, &l_Lean_Fmt_Doc_empty___redArg___closed__1_once, _init_l_Lean_Fmt_Doc_empty___redArg___closed__1);
return v___x_3304_;
}
else
{
lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; 
v___x_3305_ = lean_array_fget(v_ds_3300_, v___x_3301_);
v___x_3306_ = lean_unsigned_to_nat(1u);
v___x_3307_ = l_Array_toSubarray___redArg(v_ds_3300_, v___x_3306_, v___x_3302_);
v___x_3308_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_joinUsing_spec__0___redArg(v_sep_3299_, v___x_3307_, v___x_3305_);
return v___x_3308_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_joinUsing(lean_object* v_00_u03c4_3309_, lean_object* v_sep_3310_, lean_object* v_ds_3311_){
_start:
{
lean_object* v___x_3312_; 
v___x_3312_ = l_Lean_Fmt_Doc_joinUsing___redArg(v_sep_3310_, v_ds_3311_);
return v___x_3312_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_joinUsing_spec__0(lean_object* v_00_u03c4_3313_, lean_object* v_sep_3314_, lean_object* v_inst_3315_, lean_object* v_R_3316_, lean_object* v_a_3317_, lean_object* v_b_3318_, lean_object* v_c_3319_){
_start:
{
lean_object* v___x_3320_; 
v___x_3320_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_joinUsing_spec__0___redArg(v_sep_3314_, v_a_3317_, v_b_3318_);
return v___x_3320_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillWith_spec__0___redArg(lean_object* v_upperBound_3321_, lean_object* v_sep_3322_, lean_object* v_ds_3323_, lean_object* v_a_3324_, lean_object* v_b_3325_){
_start:
{
uint8_t v___x_3326_; 
v___x_3326_ = lean_nat_dec_lt(v_a_3324_, v_upperBound_3321_);
if (v___x_3326_ == 0)
{
lean_dec(v_a_3324_);
lean_dec_ref(v_sep_3322_);
return v_b_3325_;
}
else
{
lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v_flat_3330_; lean_object* v_broken_3331_; lean_object* v_fst_3332_; lean_object* v_snd_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3368_; 
v___x_3327_ = lean_unsigned_to_nat(1u);
v___x_3328_ = lean_nat_sub(v_a_3324_, v___x_3327_);
lean_inc_ref(v_sep_3322_);
v___x_3329_ = lean_apply_1(v_sep_3322_, v___x_3328_);
v_flat_3330_ = lean_ctor_get(v___x_3329_, 0);
lean_inc(v_flat_3330_);
v_broken_3331_ = lean_ctor_get(v___x_3329_, 1);
lean_inc(v_broken_3331_);
lean_dec_ref(v___x_3329_);
v_fst_3332_ = lean_ctor_get(v_b_3325_, 0);
v_snd_3333_ = lean_ctor_get(v_b_3325_, 1);
v_isSharedCheck_3368_ = !lean_is_exclusive(v_b_3325_);
if (v_isSharedCheck_3368_ == 0)
{
v___x_3335_ = v_b_3325_;
v_isShared_3336_ = v_isSharedCheck_3368_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_snd_3333_);
lean_inc(v_fst_3332_);
lean_dec(v_b_3325_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3368_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3364_; 
v___x_3337_ = lean_array_fget_borrowed(v_ds_3323_, v_a_3324_);
v___x_3338_ = lean_unsigned_to_nat(2u);
v___x_3339_ = lean_mk_empty_array_with_capacity(v___x_3338_);
lean_inc(v_fst_3332_);
lean_inc_ref(v___x_3339_);
v___x_3340_ = lean_array_push(v___x_3339_, v_fst_3332_);
v___x_3341_ = lean_array_push(v___x_3340_, v_snd_3333_);
v___x_3342_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_3341_);
lean_inc_n(v___x_3337_, 2);
v___x_3343_ = l_Lean_Fmt_Doc_flattened___override___redArg(v___x_3337_);
v___x_3344_ = lean_unsigned_to_nat(3u);
v___x_3345_ = lean_mk_empty_array_with_capacity(v___x_3344_);
v___x_3346_ = lean_array_push(v___x_3345_, v_fst_3332_);
v___x_3347_ = lean_array_push(v___x_3346_, v_flat_3330_);
lean_inc(v___x_3343_);
v___x_3348_ = lean_array_push(v___x_3347_, v___x_3343_);
v___x_3349_ = l_Lean_Fmt_Doc_join___redArg(v___x_3348_);
v___x_3350_ = lean_obj_once(&l_Lean_Fmt_Doc_hardNl___closed__0, &l_Lean_Fmt_Doc_hardNl___closed__0_once, _init_l_Lean_Fmt_Doc_hardNl___closed__0);
v___x_3351_ = lean_unsigned_to_nat(4u);
v___x_3352_ = lean_mk_empty_array_with_capacity(v___x_3351_);
v___x_3353_ = lean_array_push(v___x_3352_, v___x_3342_);
v___x_3354_ = lean_array_push(v___x_3353_, v_broken_3331_);
v___x_3355_ = lean_array_push(v___x_3354_, v___x_3350_);
lean_inc_ref(v___x_3355_);
v___x_3356_ = lean_array_push(v___x_3355_, v___x_3343_);
v___x_3357_ = l_Lean_Fmt_Doc_join___redArg(v___x_3356_);
v___x_3358_ = lean_array_push(v___x_3339_, v___x_3349_);
v___x_3359_ = lean_array_push(v___x_3358_, v___x_3357_);
v___x_3360_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_3359_);
v___x_3361_ = lean_array_push(v___x_3355_, v___x_3337_);
v___x_3362_ = l_Lean_Fmt_Doc_join___redArg(v___x_3361_);
if (v_isShared_3336_ == 0)
{
lean_ctor_set(v___x_3335_, 1, v___x_3362_);
lean_ctor_set(v___x_3335_, 0, v___x_3360_);
v___x_3364_ = v___x_3335_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v___x_3360_);
lean_ctor_set(v_reuseFailAlloc_3367_, 1, v___x_3362_);
v___x_3364_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
lean_object* v___x_3365_; 
v___x_3365_ = lean_nat_add(v_a_3324_, v___x_3327_);
lean_dec(v_a_3324_);
v_a_3324_ = v___x_3365_;
v_b_3325_ = v___x_3364_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillWith_spec__0___redArg___boxed(lean_object* v_upperBound_3369_, lean_object* v_sep_3370_, lean_object* v_ds_3371_, lean_object* v_a_3372_, lean_object* v_b_3373_){
_start:
{
lean_object* v_res_3374_; 
v_res_3374_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillWith_spec__0___redArg(v_upperBound_3369_, v_sep_3370_, v_ds_3371_, v_a_3372_, v_b_3373_);
lean_dec_ref(v_ds_3371_);
lean_dec(v_upperBound_3369_);
return v_res_3374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillWith___redArg(lean_object* v_ds_3375_, lean_object* v_sep_3376_){
_start:
{
lean_object* v___x_3377_; lean_object* v___x_3378_; uint8_t v___x_3379_; 
v___x_3377_ = lean_array_get_size(v_ds_3375_);
v___x_3378_ = lean_unsigned_to_nat(0u);
v___x_3379_ = lean_nat_dec_eq(v___x_3377_, v___x_3378_);
if (v___x_3379_ == 0)
{
lean_object* v___x_3380_; lean_object* v_lastNotFlattened_3381_; lean_object* v___x_3382_; uint8_t v___x_3383_; 
v___x_3380_ = lean_box(0);
v_lastNotFlattened_3381_ = lean_array_get_borrowed(v___x_3380_, v_ds_3375_, v___x_3378_);
v___x_3382_ = lean_unsigned_to_nat(1u);
v___x_3383_ = lean_nat_dec_eq(v___x_3377_, v___x_3382_);
if (v___x_3383_ == 0)
{
lean_object* v_lastFlattened_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v_fst_3387_; lean_object* v_snd_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; 
lean_inc_n(v_lastNotFlattened_3381_, 2);
v_lastFlattened_3384_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_lastNotFlattened_3381_);
v___x_3385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3385_, 0, v_lastFlattened_3384_);
lean_ctor_set(v___x_3385_, 1, v_lastNotFlattened_3381_);
v___x_3386_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillWith_spec__0___redArg(v___x_3377_, v_sep_3376_, v_ds_3375_, v___x_3382_, v___x_3385_);
v_fst_3387_ = lean_ctor_get(v___x_3386_, 0);
lean_inc(v_fst_3387_);
v_snd_3388_ = lean_ctor_get(v___x_3386_, 1);
lean_inc(v_snd_3388_);
lean_dec_ref(v___x_3386_);
v___x_3389_ = lean_unsigned_to_nat(2u);
v___x_3390_ = lean_mk_empty_array_with_capacity(v___x_3389_);
v___x_3391_ = lean_array_push(v___x_3390_, v_fst_3387_);
v___x_3392_ = lean_array_push(v___x_3391_, v_snd_3388_);
v___x_3393_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_3392_);
return v___x_3393_;
}
else
{
lean_dec_ref(v_sep_3376_);
lean_inc(v_lastNotFlattened_3381_);
return v_lastNotFlattened_3381_;
}
}
else
{
lean_object* v___x_3394_; 
lean_dec_ref(v_sep_3376_);
v___x_3394_ = lean_obj_once(&l_Lean_Fmt_Doc_empty___closed__0, &l_Lean_Fmt_Doc_empty___closed__0_once, _init_l_Lean_Fmt_Doc_empty___closed__0);
return v___x_3394_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillWith___redArg___boxed(lean_object* v_ds_3395_, lean_object* v_sep_3396_){
_start:
{
lean_object* v_res_3397_; 
v_res_3397_ = l_Lean_Fmt_Doc_fillWith___redArg(v_ds_3395_, v_sep_3396_);
lean_dec_ref(v_ds_3395_);
return v_res_3397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillWith(lean_object* v_00_u03c4_3398_, lean_object* v_ds_3399_, lean_object* v_sep_3400_){
_start:
{
lean_object* v___x_3401_; 
v___x_3401_ = l_Lean_Fmt_Doc_fillWith___redArg(v_ds_3399_, v_sep_3400_);
return v___x_3401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillWith___boxed(lean_object* v_00_u03c4_3402_, lean_object* v_ds_3403_, lean_object* v_sep_3404_){
_start:
{
lean_object* v_res_3405_; 
v_res_3405_ = l_Lean_Fmt_Doc_fillWith(v_00_u03c4_3402_, v_ds_3403_, v_sep_3404_);
lean_dec_ref(v_ds_3403_);
return v_res_3405_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillWith_spec__0(lean_object* v_00_u03c4_3406_, lean_object* v_upperBound_3407_, lean_object* v_sep_3408_, lean_object* v_ds_3409_, lean_object* v_inst_3410_, lean_object* v_R_3411_, lean_object* v_a_3412_, lean_object* v_b_3413_, lean_object* v_c_3414_){
_start:
{
lean_object* v___x_3415_; 
v___x_3415_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillWith_spec__0___redArg(v_upperBound_3407_, v_sep_3408_, v_ds_3409_, v_a_3412_, v_b_3413_);
return v___x_3415_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillWith_spec__0___boxed(lean_object* v_00_u03c4_3416_, lean_object* v_upperBound_3417_, lean_object* v_sep_3418_, lean_object* v_ds_3419_, lean_object* v_inst_3420_, lean_object* v_R_3421_, lean_object* v_a_3422_, lean_object* v_b_3423_, lean_object* v_c_3424_){
_start:
{
lean_object* v_res_3425_; 
v_res_3425_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillWith_spec__0(v_00_u03c4_3416_, v_upperBound_3417_, v_sep_3418_, v_ds_3419_, v_inst_3420_, v_R_3421_, v_a_3422_, v_b_3423_, v_c_3424_);
lean_dec_ref(v_ds_3419_);
lean_dec(v_upperBound_3417_);
return v_res_3425_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_fill___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3426_; lean_object* v___x_3427_; 
v___x_3426_ = lean_obj_once(&l_Lean_Fmt_Doc_empty___closed__0, &l_Lean_Fmt_Doc_empty___closed__0_once, _init_l_Lean_Fmt_Doc_empty___closed__0);
v___x_3427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3426_);
lean_ctor_set(v___x_3427_, 1, v___x_3426_);
return v___x_3427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fill___redArg___lam__0(lean_object* v_x_3428_){
_start:
{
lean_object* v___x_3429_; 
v___x_3429_ = lean_obj_once(&l_Lean_Fmt_Doc_fill___redArg___lam__0___closed__0, &l_Lean_Fmt_Doc_fill___redArg___lam__0___closed__0_once, _init_l_Lean_Fmt_Doc_fill___redArg___lam__0___closed__0);
return v___x_3429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fill___redArg___lam__0___boxed(lean_object* v_x_3430_){
_start:
{
lean_object* v_res_3431_; 
v_res_3431_ = l_Lean_Fmt_Doc_fill___redArg___lam__0(v_x_3430_);
lean_dec(v_x_3430_);
return v_res_3431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fill___redArg(lean_object* v_ds_3433_){
_start:
{
lean_object* v___f_3434_; lean_object* v___x_3435_; 
v___f_3434_ = ((lean_object*)(l_Lean_Fmt_Doc_fill___redArg___closed__0));
v___x_3435_ = l_Lean_Fmt_Doc_fillWith___redArg(v_ds_3433_, v___f_3434_);
return v___x_3435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fill___redArg___boxed(lean_object* v_ds_3436_){
_start:
{
lean_object* v_res_3437_; 
v_res_3437_ = l_Lean_Fmt_Doc_fill___redArg(v_ds_3436_);
lean_dec_ref(v_ds_3436_);
return v_res_3437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fill(lean_object* v_00_u03c4_3438_, lean_object* v_ds_3439_){
_start:
{
lean_object* v___x_3440_; 
v___x_3440_ = l_Lean_Fmt_Doc_fill___redArg(v_ds_3439_);
return v___x_3440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fill___boxed(lean_object* v_00_u03c4_3441_, lean_object* v_ds_3442_){
_start:
{
lean_object* v_res_3443_; 
v_res_3443_ = l_Lean_Fmt_Doc_fill(v_00_u03c4_3441_, v_ds_3442_);
lean_dec_ref(v_ds_3442_);
return v_res_3443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsing___redArg___lam__0(lean_object* v_sep_3444_, lean_object* v_x_3445_){
_start:
{
lean_object* v___x_3446_; 
lean_inc(v_sep_3444_);
v___x_3446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3446_, 0, v_sep_3444_);
lean_ctor_set(v___x_3446_, 1, v_sep_3444_);
return v___x_3446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsing___redArg___lam__0___boxed(lean_object* v_sep_3447_, lean_object* v_x_3448_){
_start:
{
lean_object* v_res_3449_; 
v_res_3449_ = l_Lean_Fmt_Doc_fillUsing___redArg___lam__0(v_sep_3447_, v_x_3448_);
lean_dec(v_x_3448_);
return v_res_3449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsing___redArg(lean_object* v_sep_3450_, lean_object* v_ds_3451_){
_start:
{
lean_object* v___f_3452_; lean_object* v___x_3453_; 
v___f_3452_ = lean_alloc_closure((void*)(l_Lean_Fmt_Doc_fillUsing___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3452_, 0, v_sep_3450_);
v___x_3453_ = l_Lean_Fmt_Doc_fillWith___redArg(v_ds_3451_, v___f_3452_);
return v___x_3453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsing___redArg___boxed(lean_object* v_sep_3454_, lean_object* v_ds_3455_){
_start:
{
lean_object* v_res_3456_; 
v_res_3456_ = l_Lean_Fmt_Doc_fillUsing___redArg(v_sep_3454_, v_ds_3455_);
lean_dec_ref(v_ds_3455_);
return v_res_3456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsing(lean_object* v_00_u03c4_3457_, lean_object* v_sep_3458_, lean_object* v_ds_3459_){
_start:
{
lean_object* v___x_3460_; 
v___x_3460_ = l_Lean_Fmt_Doc_fillUsing___redArg(v_sep_3458_, v_ds_3459_);
return v___x_3460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsing___boxed(lean_object* v_00_u03c4_3461_, lean_object* v_sep_3462_, lean_object* v_ds_3463_){
_start:
{
lean_object* v_res_3464_; 
v_res_3464_ = l_Lean_Fmt_Doc_fillUsing(v_00_u03c4_3461_, v_sep_3462_, v_ds_3463_);
lean_dec_ref(v_ds_3463_);
return v_res_3464_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_fillUsingSpace___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3465_; lean_object* v___x_3466_; 
v___x_3465_ = ((lean_object*)(l_Lean_Fmt_Doc_nl___redArg___closed__0));
v___x_3466_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_3465_);
return v___x_3466_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_fillUsingSpace___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; 
v___x_3467_ = lean_obj_once(&l_Lean_Fmt_Doc_empty___closed__0, &l_Lean_Fmt_Doc_empty___closed__0_once, _init_l_Lean_Fmt_Doc_empty___closed__0);
v___x_3468_ = lean_obj_once(&l_Lean_Fmt_Doc_fillUsingSpace___redArg___lam__0___closed__0, &l_Lean_Fmt_Doc_fillUsingSpace___redArg___lam__0___closed__0_once, _init_l_Lean_Fmt_Doc_fillUsingSpace___redArg___lam__0___closed__0);
v___x_3469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3468_);
lean_ctor_set(v___x_3469_, 1, v___x_3467_);
return v___x_3469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpace___redArg___lam__0(lean_object* v_x_3470_){
_start:
{
lean_object* v___x_3471_; 
v___x_3471_ = lean_obj_once(&l_Lean_Fmt_Doc_fillUsingSpace___redArg___lam__0___closed__1, &l_Lean_Fmt_Doc_fillUsingSpace___redArg___lam__0___closed__1_once, _init_l_Lean_Fmt_Doc_fillUsingSpace___redArg___lam__0___closed__1);
return v___x_3471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpace___redArg___lam__0___boxed(lean_object* v_x_3472_){
_start:
{
lean_object* v_res_3473_; 
v_res_3473_ = l_Lean_Fmt_Doc_fillUsingSpace___redArg___lam__0(v_x_3472_);
lean_dec(v_x_3472_);
return v_res_3473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpace___redArg(lean_object* v_ds_3475_){
_start:
{
lean_object* v___f_3476_; lean_object* v___x_3477_; 
v___f_3476_ = ((lean_object*)(l_Lean_Fmt_Doc_fillUsingSpace___redArg___closed__0));
v___x_3477_ = l_Lean_Fmt_Doc_fillWith___redArg(v_ds_3475_, v___f_3476_);
return v___x_3477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpace___redArg___boxed(lean_object* v_ds_3478_){
_start:
{
lean_object* v_res_3479_; 
v_res_3479_ = l_Lean_Fmt_Doc_fillUsingSpace___redArg(v_ds_3478_);
lean_dec_ref(v_ds_3478_);
return v_res_3479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpace(lean_object* v_00_u03c4_3480_, lean_object* v_ds_3481_){
_start:
{
lean_object* v___x_3482_; 
v___x_3482_ = l_Lean_Fmt_Doc_fillUsingSpace___redArg(v_ds_3481_);
return v___x_3482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpace___boxed(lean_object* v_00_u03c4_3483_, lean_object* v_ds_3484_){
_start:
{
lean_object* v_res_3485_; 
v_res_3485_ = l_Lean_Fmt_Doc_fillUsingSpace(v_00_u03c4_3483_, v_ds_3484_);
lean_dec_ref(v_ds_3484_);
return v_res_3485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg___lam__0(uint8_t v___x_3486_, lean_object* v___y_3487_, lean_object* v_sep_3488_, lean_object* v_boundarySep_3489_, lean_object* v_i_3490_){
_start:
{
lean_object* v___y_3492_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; uint8_t v___x_3499_; 
v___x_3495_ = lean_unsigned_to_nat(1u);
v___x_3496_ = lean_nat_add(v_i_3490_, v___x_3495_);
v___x_3497_ = lean_box(v___x_3486_);
v___x_3498_ = lean_array_get(v___x_3497_, v___y_3487_, v___x_3496_);
lean_dec(v___x_3496_);
lean_dec(v___x_3497_);
v___x_3499_ = lean_unbox(v___x_3498_);
lean_dec(v___x_3498_);
if (v___x_3499_ == 0)
{
lean_dec(v_boundarySep_3489_);
v___y_3492_ = v_sep_3488_;
goto v___jp_3491_;
}
else
{
lean_dec(v_sep_3488_);
v___y_3492_ = v_boundarySep_3489_;
goto v___jp_3491_;
}
v___jp_3491_:
{
lean_object* v___x_3493_; lean_object* v___x_3494_; 
v___x_3493_ = lean_obj_once(&l_Lean_Fmt_Doc_empty___closed__0, &l_Lean_Fmt_Doc_empty___closed__0_once, _init_l_Lean_Fmt_Doc_empty___closed__0);
v___x_3494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3494_, 0, v___y_3492_);
lean_ctor_set(v___x_3494_, 1, v___x_3493_);
return v___x_3494_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg___lam__0___boxed(lean_object* v___x_3500_, lean_object* v___y_3501_, lean_object* v_sep_3502_, lean_object* v_boundarySep_3503_, lean_object* v_i_3504_){
_start:
{
uint8_t v___x_550__boxed_3505_; lean_object* v_res_3506_; 
v___x_550__boxed_3505_ = lean_unbox(v___x_3500_);
v_res_3506_ = l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg___lam__0(v___x_550__boxed_3505_, v___y_3501_, v_sep_3502_, v_boundarySep_3503_, v_i_3504_);
lean_dec(v_i_3504_);
lean_dec_ref(v___y_3501_);
return v_res_3506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__0___redArg(size_t v_sz_3507_, size_t v_i_3508_, lean_object* v_bs_3509_){
_start:
{
uint8_t v___x_3510_; 
v___x_3510_ = lean_usize_dec_lt(v_i_3508_, v_sz_3507_);
if (v___x_3510_ == 0)
{
return v_bs_3509_;
}
else
{
lean_object* v___x_3511_; lean_object* v_bs_x27_3512_; lean_object* v___x_3513_; uint8_t v___x_3514_; size_t v___x_3515_; size_t v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; 
v___x_3511_ = lean_unsigned_to_nat(0u);
v_bs_x27_3512_ = lean_array_uset(v_bs_3509_, v_i_3508_, v___x_3511_);
v___x_3513_ = lean_usize_to_nat(v_i_3508_);
v___x_3514_ = lean_nat_dec_eq(v___x_3513_, v___x_3511_);
lean_dec(v___x_3513_);
v___x_3515_ = ((size_t)1ULL);
v___x_3516_ = lean_usize_add(v_i_3508_, v___x_3515_);
v___x_3517_ = lean_box(v___x_3514_);
v___x_3518_ = lean_array_uset(v_bs_x27_3512_, v_i_3508_, v___x_3517_);
v_i_3508_ = v___x_3516_;
v_bs_3509_ = v___x_3518_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__0___redArg___boxed(lean_object* v_sz_3520_, lean_object* v_i_3521_, lean_object* v_bs_3522_){
_start:
{
size_t v_sz_boxed_3523_; size_t v_i_boxed_3524_; lean_object* v_res_3525_; 
v_sz_boxed_3523_ = lean_unbox_usize(v_sz_3520_);
lean_dec(v_sz_3520_);
v_i_boxed_3524_ = lean_unbox_usize(v_i_3521_);
lean_dec(v_i_3521_);
v_res_3525_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__0___redArg(v_sz_boxed_3523_, v_i_boxed_3524_, v_bs_3522_);
return v_res_3525_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__2___redArg(lean_object* v_as_3526_, size_t v_i_3527_, size_t v_stop_3528_, lean_object* v_b_3529_){
_start:
{
uint8_t v___x_3530_; 
v___x_3530_ = lean_usize_dec_eq(v_i_3527_, v_stop_3528_);
if (v___x_3530_ == 0)
{
lean_object* v___x_3531_; size_t v_sz_3532_; size_t v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; size_t v___x_3536_; size_t v___x_3537_; 
v___x_3531_ = lean_array_uget_borrowed(v_as_3526_, v_i_3527_);
v_sz_3532_ = lean_array_size(v___x_3531_);
v___x_3533_ = ((size_t)0ULL);
lean_inc(v___x_3531_);
v___x_3534_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__0___redArg(v_sz_3532_, v___x_3533_, v___x_3531_);
v___x_3535_ = l_Array_append___redArg(v_b_3529_, v___x_3534_);
lean_dec_ref(v___x_3534_);
v___x_3536_ = ((size_t)1ULL);
v___x_3537_ = lean_usize_add(v_i_3527_, v___x_3536_);
v_i_3527_ = v___x_3537_;
v_b_3529_ = v___x_3535_;
goto _start;
}
else
{
return v_b_3529_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__2___redArg___boxed(lean_object* v_as_3539_, lean_object* v_i_3540_, lean_object* v_stop_3541_, lean_object* v_b_3542_){
_start:
{
size_t v_i_boxed_3543_; size_t v_stop_boxed_3544_; lean_object* v_res_3545_; 
v_i_boxed_3543_ = lean_unbox_usize(v_i_3540_);
lean_dec(v_i_3540_);
v_stop_boxed_3544_ = lean_unbox_usize(v_stop_3541_);
lean_dec(v_stop_3541_);
v_res_3545_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__2___redArg(v_as_3539_, v_i_boxed_3543_, v_stop_boxed_3544_, v_b_3542_);
lean_dec_ref(v_as_3539_);
return v_res_3545_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__1___redArg(lean_object* v_as_3546_, size_t v_i_3547_, size_t v_stop_3548_, lean_object* v_b_3549_){
_start:
{
uint8_t v___x_3550_; 
v___x_3550_ = lean_usize_dec_eq(v_i_3547_, v_stop_3548_);
if (v___x_3550_ == 0)
{
lean_object* v___x_3551_; lean_object* v___x_3552_; size_t v___x_3553_; size_t v___x_3554_; 
v___x_3551_ = lean_array_uget_borrowed(v_as_3546_, v_i_3547_);
v___x_3552_ = l_Array_append___redArg(v_b_3549_, v___x_3551_);
v___x_3553_ = ((size_t)1ULL);
v___x_3554_ = lean_usize_add(v_i_3547_, v___x_3553_);
v_i_3547_ = v___x_3554_;
v_b_3549_ = v___x_3552_;
goto _start;
}
else
{
return v_b_3549_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__1___redArg___boxed(lean_object* v_as_3556_, lean_object* v_i_3557_, lean_object* v_stop_3558_, lean_object* v_b_3559_){
_start:
{
size_t v_i_boxed_3560_; size_t v_stop_boxed_3561_; lean_object* v_res_3562_; 
v_i_boxed_3560_ = lean_unbox_usize(v_i_3557_);
lean_dec(v_i_3557_);
v_stop_boxed_3561_ = lean_unbox_usize(v_stop_3558_);
lean_dec(v_stop_3558_);
v_res_3562_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__1___redArg(v_as_3556_, v_i_boxed_3560_, v_stop_boxed_3561_, v_b_3559_);
lean_dec_ref(v_as_3556_);
return v_res_3562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg(lean_object* v_boundaryPenalty_3567_, lean_object* v_dss_3568_){
_start:
{
uint8_t v___x_3569_; lean_object* v___y_3571_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; uint8_t v___x_3588_; 
v___x_3569_ = 0;
v___x_3585_ = lean_unsigned_to_nat(0u);
v___x_3586_ = ((lean_object*)(l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg___closed__1));
v___x_3587_ = lean_array_get_size(v_dss_3568_);
v___x_3588_ = lean_nat_dec_lt(v___x_3585_, v___x_3587_);
if (v___x_3588_ == 0)
{
v___y_3571_ = v___x_3586_;
goto v___jp_3570_;
}
else
{
size_t v___x_3589_; size_t v___x_3590_; lean_object* v___x_3591_; 
v___x_3589_ = ((size_t)0ULL);
v___x_3590_ = lean_usize_of_nat(v___x_3587_);
v___x_3591_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__2___redArg(v_dss_3568_, v___x_3589_, v___x_3590_, v___x_3586_);
v___y_3571_ = v___x_3591_;
goto v___jp_3570_;
}
v___jp_3570_:
{
lean_object* v_sep_3572_; lean_object* v_boundarySep_3573_; lean_object* v___x_3574_; lean_object* v___f_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; uint8_t v___x_3579_; 
v_sep_3572_ = lean_obj_once(&l_Lean_Fmt_Doc_fillUsingSpace___redArg___lam__0___closed__0, &l_Lean_Fmt_Doc_fillUsingSpace___redArg___lam__0___closed__0_once, _init_l_Lean_Fmt_Doc_fillUsingSpace___redArg___lam__0___closed__0);
v_boundarySep_3573_ = l_Lean_Fmt_Doc_costing___override___redArg(v_boundaryPenalty_3567_, v_sep_3572_);
v___x_3574_ = lean_box(v___x_3569_);
v___f_3575_ = lean_alloc_closure((void*)(l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_3575_, 0, v___x_3574_);
lean_closure_set(v___f_3575_, 1, v___y_3571_);
lean_closure_set(v___f_3575_, 2, v_sep_3572_);
lean_closure_set(v___f_3575_, 3, v_boundarySep_3573_);
v___x_3576_ = lean_unsigned_to_nat(0u);
v___x_3577_ = ((lean_object*)(l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg___closed__0));
v___x_3578_ = lean_array_get_size(v_dss_3568_);
v___x_3579_ = lean_nat_dec_lt(v___x_3576_, v___x_3578_);
if (v___x_3579_ == 0)
{
lean_object* v___x_3580_; 
v___x_3580_ = l_Lean_Fmt_Doc_fillWith___redArg(v___x_3577_, v___f_3575_);
return v___x_3580_;
}
else
{
size_t v___x_3581_; size_t v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; 
v___x_3581_ = ((size_t)0ULL);
v___x_3582_ = lean_usize_of_nat(v___x_3578_);
v___x_3583_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__1___redArg(v_dss_3568_, v___x_3581_, v___x_3582_, v___x_3577_);
v___x_3584_ = l_Lean_Fmt_Doc_fillWith___redArg(v___x_3583_, v___f_3575_);
lean_dec_ref(v___x_3583_);
return v___x_3584_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg___boxed(lean_object* v_boundaryPenalty_3592_, lean_object* v_dss_3593_){
_start:
{
lean_object* v_res_3594_; 
v_res_3594_ = l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg(v_boundaryPenalty_3592_, v_dss_3593_);
lean_dec_ref(v_dss_3593_);
return v_res_3594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries(lean_object* v_00_u03c4_3595_, lean_object* v_boundaryPenalty_3596_, lean_object* v_dss_3597_){
_start:
{
lean_object* v___x_3598_; 
v___x_3598_ = l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg(v_boundaryPenalty_3596_, v_dss_3597_);
return v___x_3598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___boxed(lean_object* v_00_u03c4_3599_, lean_object* v_boundaryPenalty_3600_, lean_object* v_dss_3601_){
_start:
{
lean_object* v_res_3602_; 
v_res_3602_ = l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries(v_00_u03c4_3599_, v_boundaryPenalty_3600_, v_dss_3601_);
lean_dec_ref(v_dss_3601_);
return v_res_3602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__0(lean_object* v_00_u03c4_3603_, lean_object* v_as_3604_, size_t v_sz_3605_, size_t v_i_3606_, lean_object* v_bs_3607_){
_start:
{
lean_object* v___x_3608_; 
v___x_3608_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__0___redArg(v_sz_3605_, v_i_3606_, v_bs_3607_);
return v___x_3608_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__0___boxed(lean_object* v_00_u03c4_3609_, lean_object* v_as_3610_, lean_object* v_sz_3611_, lean_object* v_i_3612_, lean_object* v_bs_3613_){
_start:
{
size_t v_sz_boxed_3614_; size_t v_i_boxed_3615_; lean_object* v_res_3616_; 
v_sz_boxed_3614_ = lean_unbox_usize(v_sz_3611_);
lean_dec(v_sz_3611_);
v_i_boxed_3615_ = lean_unbox_usize(v_i_3612_);
lean_dec(v_i_3612_);
v_res_3616_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__0(v_00_u03c4_3609_, v_as_3610_, v_sz_boxed_3614_, v_i_boxed_3615_, v_bs_3613_);
lean_dec_ref(v_as_3610_);
return v_res_3616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__1(lean_object* v_00_u03c4_3617_, lean_object* v_as_3618_, size_t v_i_3619_, size_t v_stop_3620_, lean_object* v_b_3621_){
_start:
{
lean_object* v___x_3622_; 
v___x_3622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__1___redArg(v_as_3618_, v_i_3619_, v_stop_3620_, v_b_3621_);
return v___x_3622_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__1___boxed(lean_object* v_00_u03c4_3623_, lean_object* v_as_3624_, lean_object* v_i_3625_, lean_object* v_stop_3626_, lean_object* v_b_3627_){
_start:
{
size_t v_i_boxed_3628_; size_t v_stop_boxed_3629_; lean_object* v_res_3630_; 
v_i_boxed_3628_ = lean_unbox_usize(v_i_3625_);
lean_dec(v_i_3625_);
v_stop_boxed_3629_ = lean_unbox_usize(v_stop_3626_);
lean_dec(v_stop_3626_);
v_res_3630_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__1(v_00_u03c4_3623_, v_as_3624_, v_i_boxed_3628_, v_stop_boxed_3629_, v_b_3627_);
lean_dec_ref(v_as_3624_);
return v_res_3630_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__2(lean_object* v_00_u03c4_3631_, lean_object* v_as_3632_, size_t v_i_3633_, size_t v_stop_3634_, lean_object* v_b_3635_){
_start:
{
lean_object* v___x_3636_; 
v___x_3636_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__2___redArg(v_as_3632_, v_i_3633_, v_stop_3634_, v_b_3635_);
return v___x_3636_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__2___boxed(lean_object* v_00_u03c4_3637_, lean_object* v_as_3638_, lean_object* v_i_3639_, lean_object* v_stop_3640_, lean_object* v_b_3641_){
_start:
{
size_t v_i_boxed_3642_; size_t v_stop_boxed_3643_; lean_object* v_res_3644_; 
v_i_boxed_3642_ = lean_unbox_usize(v_i_3639_);
lean_dec(v_i_3639_);
v_stop_boxed_3643_ = lean_unbox_usize(v_stop_3640_);
lean_dec(v_stop_3640_);
v_res_3644_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__2(v_00_u03c4_3637_, v_as_3638_, v_i_boxed_3642_, v_stop_boxed_3643_, v_b_3641_);
lean_dec_ref(v_as_3638_);
return v_res_3644_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrappingWith_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; 
v___x_3645_ = lean_obj_once(&l_Lean_Fmt_Doc_nl___closed__0, &l_Lean_Fmt_Doc_nl___closed__0_once, _init_l_Lean_Fmt_Doc_nl___closed__0);
v___x_3646_ = lean_unsigned_to_nat(2u);
v___x_3647_ = lean_mk_empty_array_with_capacity(v___x_3646_);
v___x_3648_ = lean_array_push(v___x_3647_, v___x_3645_);
return v___x_3648_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrappingWith_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; 
v___x_3649_ = lean_obj_once(&l_Lean_Fmt_Doc_hardNl___closed__0, &l_Lean_Fmt_Doc_hardNl___closed__0_once, _init_l_Lean_Fmt_Doc_hardNl___closed__0);
v___x_3650_ = lean_unsigned_to_nat(2u);
v___x_3651_ = lean_mk_empty_array_with_capacity(v___x_3650_);
v___x_3652_ = lean_array_push(v___x_3651_, v___x_3649_);
return v___x_3652_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrappingWith_spec__0___redArg(lean_object* v_sep_3653_, lean_object* v_wrap_3654_, lean_object* v_as_3655_, size_t v_sz_3656_, size_t v_i_3657_, lean_object* v_b_3658_){
_start:
{
lean_object* v_a_3660_; uint8_t v___x_3664_; 
v___x_3664_ = lean_usize_dec_lt(v_i_3657_, v_sz_3656_);
if (v___x_3664_ == 0)
{
lean_dec_ref(v_wrap_3654_);
lean_dec_ref(v_sep_3653_);
return v_b_3658_;
}
else
{
lean_object* v_a_3665_; lean_object* v_fst_3666_; lean_object* v_snd_3667_; lean_object* v_fst_3668_; lean_object* v_snd_3669_; lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3717_; 
v_a_3665_ = lean_array_uget_borrowed(v_as_3655_, v_i_3657_);
v_fst_3666_ = lean_ctor_get(v_a_3665_, 0);
v_snd_3667_ = lean_ctor_get(v_a_3665_, 1);
v_fst_3668_ = lean_ctor_get(v_b_3658_, 0);
v_snd_3669_ = lean_ctor_get(v_b_3658_, 1);
v_isSharedCheck_3717_ = !lean_is_exclusive(v_b_3658_);
if (v_isSharedCheck_3717_ == 0)
{
v___x_3671_ = v_b_3658_;
v_isShared_3672_ = v_isSharedCheck_3717_;
goto v_resetjp_3670_;
}
else
{
lean_inc(v_snd_3669_);
lean_inc(v_fst_3668_);
lean_dec(v_b_3658_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3717_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; 
v___x_3673_ = lean_unsigned_to_nat(2u);
v___x_3674_ = lean_mk_empty_array_with_capacity(v___x_3673_);
lean_inc(v_fst_3668_);
lean_inc_ref(v___x_3674_);
v___x_3675_ = lean_array_push(v___x_3674_, v_fst_3668_);
v___x_3676_ = lean_array_push(v___x_3675_, v_snd_3669_);
v___x_3677_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_3676_);
lean_inc_ref(v_sep_3653_);
lean_inc(v_snd_3667_);
v___x_3678_ = lean_apply_1(v_sep_3653_, v_snd_3667_);
if (lean_obj_tag(v___x_3678_) == 0)
{
lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3691_; 
lean_dec(v_fst_3668_);
v___x_3679_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrappingWith_spec__0___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrappingWith_spec__0___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrappingWith_spec__0___redArg___closed__0);
v___x_3680_ = lean_array_push(v___x_3679_, v___x_3677_);
v___x_3681_ = l_Lean_Fmt_Doc_join___redArg(v___x_3680_);
lean_inc_ref(v_wrap_3654_);
v___x_3682_ = lean_apply_1(v_wrap_3654_, v___x_3681_);
lean_inc_n(v_fst_3666_, 2);
v___x_3683_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_fst_3666_);
lean_inc_ref(v___x_3674_);
v___x_3684_ = lean_array_push(v___x_3674_, v___x_3683_);
lean_inc(v___x_3682_);
v___x_3685_ = lean_array_push(v___x_3684_, v___x_3682_);
v___x_3686_ = l_Lean_Fmt_Doc_join___redArg(v___x_3685_);
v___x_3687_ = lean_array_push(v___x_3674_, v_fst_3666_);
v___x_3688_ = lean_array_push(v___x_3687_, v___x_3682_);
v___x_3689_ = l_Lean_Fmt_Doc_join___redArg(v___x_3688_);
if (v_isShared_3672_ == 0)
{
lean_ctor_set(v___x_3671_, 1, v___x_3689_);
lean_ctor_set(v___x_3671_, 0, v___x_3686_);
v___x_3691_ = v___x_3671_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v___x_3686_);
lean_ctor_set(v_reuseFailAlloc_3692_, 1, v___x_3689_);
v___x_3691_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
v_a_3660_ = v___x_3691_;
goto v___jp_3659_;
}
}
else
{
lean_object* v_val_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3715_; 
v_val_3693_ = lean_ctor_get(v___x_3678_, 0);
lean_inc(v_val_3693_);
lean_dec_ref_known(v___x_3678_, 1);
v___x_3694_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrappingWith_spec__0___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrappingWith_spec__0___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrappingWith_spec__0___redArg___closed__1);
v___x_3695_ = lean_array_push(v___x_3694_, v___x_3677_);
v___x_3696_ = l_Lean_Fmt_Doc_join___redArg(v___x_3695_);
lean_inc_ref_n(v_wrap_3654_, 2);
v___x_3697_ = lean_apply_1(v_wrap_3654_, v___x_3696_);
lean_inc_n(v_fst_3666_, 2);
v___x_3698_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_fst_3666_);
lean_inc_ref_n(v___x_3674_, 3);
v___x_3699_ = lean_array_push(v___x_3674_, v_val_3693_);
v___x_3700_ = lean_array_push(v___x_3699_, v_fst_3668_);
v___x_3701_ = l_Lean_Fmt_Doc_join___redArg(v___x_3700_);
v___x_3702_ = lean_apply_1(v_wrap_3654_, v___x_3701_);
v___x_3703_ = lean_array_push(v___x_3674_, v___x_3698_);
lean_inc_ref(v___x_3703_);
v___x_3704_ = lean_array_push(v___x_3703_, v___x_3702_);
v___x_3705_ = l_Lean_Fmt_Doc_join___redArg(v___x_3704_);
lean_inc(v___x_3697_);
v___x_3706_ = lean_array_push(v___x_3703_, v___x_3697_);
v___x_3707_ = l_Lean_Fmt_Doc_join___redArg(v___x_3706_);
v___x_3708_ = lean_array_push(v___x_3674_, v___x_3705_);
v___x_3709_ = lean_array_push(v___x_3708_, v___x_3707_);
v___x_3710_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_3709_);
v___x_3711_ = lean_array_push(v___x_3674_, v_fst_3666_);
v___x_3712_ = lean_array_push(v___x_3711_, v___x_3697_);
v___x_3713_ = l_Lean_Fmt_Doc_join___redArg(v___x_3712_);
if (v_isShared_3672_ == 0)
{
lean_ctor_set(v___x_3671_, 1, v___x_3713_);
lean_ctor_set(v___x_3671_, 0, v___x_3710_);
v___x_3715_ = v___x_3671_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3716_; 
v_reuseFailAlloc_3716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3716_, 0, v___x_3710_);
lean_ctor_set(v_reuseFailAlloc_3716_, 1, v___x_3713_);
v___x_3715_ = v_reuseFailAlloc_3716_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
v_a_3660_ = v___x_3715_;
goto v___jp_3659_;
}
}
}
}
v___jp_3659_:
{
size_t v___x_3661_; size_t v___x_3662_; 
v___x_3661_ = ((size_t)1ULL);
v___x_3662_ = lean_usize_add(v_i_3657_, v___x_3661_);
v_i_3657_ = v___x_3662_;
v_b_3658_ = v_a_3660_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrappingWith_spec__0___redArg___boxed(lean_object* v_sep_3718_, lean_object* v_wrap_3719_, lean_object* v_as_3720_, lean_object* v_sz_3721_, lean_object* v_i_3722_, lean_object* v_b_3723_){
_start:
{
size_t v_sz_boxed_3724_; size_t v_i_boxed_3725_; lean_object* v_res_3726_; 
v_sz_boxed_3724_ = lean_unbox_usize(v_sz_3721_);
lean_dec(v_sz_3721_);
v_i_boxed_3725_ = lean_unbox_usize(v_i_3722_);
lean_dec(v_i_3722_);
v_res_3726_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrappingWith_spec__0___redArg(v_sep_3718_, v_wrap_3719_, v_as_3720_, v_sz_boxed_3724_, v_i_boxed_3725_, v_b_3723_);
lean_dec_ref(v_as_3720_);
return v_res_3726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillWrappingWith___redArg(lean_object* v_ds_3727_, lean_object* v_wrap_3728_, lean_object* v_sep_3729_){
_start:
{
lean_object* v___x_3730_; lean_object* v___x_3731_; uint8_t v___x_3732_; 
v___x_3730_ = lean_array_get_size(v_ds_3727_);
v___x_3731_ = lean_unsigned_to_nat(0u);
v___x_3732_ = lean_nat_dec_eq(v___x_3730_, v___x_3731_);
if (v___x_3732_ == 0)
{
lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v_restNotFlattened_3736_; uint8_t v___x_3737_; 
v___x_3733_ = lean_box(0);
v___x_3734_ = lean_unsigned_to_nat(1u);
v___x_3735_ = lean_nat_sub(v___x_3730_, v___x_3734_);
v_restNotFlattened_3736_ = lean_array_get(v___x_3733_, v_ds_3727_, v___x_3735_);
lean_dec(v___x_3735_);
v___x_3737_ = lean_nat_dec_eq(v___x_3730_, v___x_3734_);
if (v___x_3737_ == 0)
{
lean_object* v_restFlattened_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; size_t v_sz_3743_; size_t v___x_3744_; lean_object* v___x_3745_; lean_object* v_fst_3746_; lean_object* v_snd_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; 
lean_inc(v_restNotFlattened_3736_);
v_restFlattened_3738_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_restNotFlattened_3736_);
v___x_3739_ = lean_array_pop(v_ds_3727_);
v___x_3740_ = l_Array_zipIdx___redArg(v___x_3739_, v___x_3731_);
v___x_3741_ = l_Array_reverse___redArg(v___x_3740_);
v___x_3742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3742_, 0, v_restFlattened_3738_);
lean_ctor_set(v___x_3742_, 1, v_restNotFlattened_3736_);
v_sz_3743_ = lean_array_size(v___x_3741_);
v___x_3744_ = ((size_t)0ULL);
v___x_3745_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrappingWith_spec__0___redArg(v_sep_3729_, v_wrap_3728_, v___x_3741_, v_sz_3743_, v___x_3744_, v___x_3742_);
lean_dec_ref(v___x_3741_);
v_fst_3746_ = lean_ctor_get(v___x_3745_, 0);
lean_inc(v_fst_3746_);
v_snd_3747_ = lean_ctor_get(v___x_3745_, 1);
lean_inc(v_snd_3747_);
lean_dec_ref(v___x_3745_);
v___x_3748_ = lean_unsigned_to_nat(2u);
v___x_3749_ = lean_mk_empty_array_with_capacity(v___x_3748_);
v___x_3750_ = lean_array_push(v___x_3749_, v_fst_3746_);
v___x_3751_ = lean_array_push(v___x_3750_, v_snd_3747_);
v___x_3752_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_3751_);
return v___x_3752_;
}
else
{
lean_dec_ref(v_sep_3729_);
lean_dec_ref(v_wrap_3728_);
lean_dec_ref(v_ds_3727_);
return v_restNotFlattened_3736_;
}
}
else
{
lean_object* v___x_3753_; 
lean_dec_ref(v_sep_3729_);
lean_dec_ref(v_wrap_3728_);
lean_dec_ref(v_ds_3727_);
v___x_3753_ = lean_obj_once(&l_Lean_Fmt_Doc_empty___closed__0, &l_Lean_Fmt_Doc_empty___closed__0_once, _init_l_Lean_Fmt_Doc_empty___closed__0);
return v___x_3753_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillWrappingWith(lean_object* v_00_u03c4_3754_, lean_object* v_ds_3755_, lean_object* v_wrap_3756_, lean_object* v_sep_3757_){
_start:
{
lean_object* v___x_3758_; 
v___x_3758_ = l_Lean_Fmt_Doc_fillWrappingWith___redArg(v_ds_3755_, v_wrap_3756_, v_sep_3757_);
return v___x_3758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrappingWith_spec__0(lean_object* v_00_u03c4_3759_, lean_object* v_sep_3760_, lean_object* v_wrap_3761_, lean_object* v_as_3762_, size_t v_sz_3763_, size_t v_i_3764_, lean_object* v_b_3765_){
_start:
{
lean_object* v___x_3766_; 
v___x_3766_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrappingWith_spec__0___redArg(v_sep_3760_, v_wrap_3761_, v_as_3762_, v_sz_3763_, v_i_3764_, v_b_3765_);
return v___x_3766_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrappingWith_spec__0___boxed(lean_object* v_00_u03c4_3767_, lean_object* v_sep_3768_, lean_object* v_wrap_3769_, lean_object* v_as_3770_, lean_object* v_sz_3771_, lean_object* v_i_3772_, lean_object* v_b_3773_){
_start:
{
size_t v_sz_boxed_3774_; size_t v_i_boxed_3775_; lean_object* v_res_3776_; 
v_sz_boxed_3774_ = lean_unbox_usize(v_sz_3771_);
lean_dec(v_sz_3771_);
v_i_boxed_3775_ = lean_unbox_usize(v_i_3772_);
lean_dec(v_i_3772_);
v_res_3776_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrappingWith_spec__0(v_00_u03c4_3767_, v_sep_3768_, v_wrap_3769_, v_as_3770_, v_sz_boxed_3774_, v_i_boxed_3775_, v_b_3773_);
lean_dec_ref(v_as_3770_);
return v_res_3776_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_fillWrapping___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3777_; lean_object* v___x_3778_; 
v___x_3777_ = lean_obj_once(&l_Lean_Fmt_Doc_empty___closed__0, &l_Lean_Fmt_Doc_empty___closed__0_once, _init_l_Lean_Fmt_Doc_empty___closed__0);
v___x_3778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3778_, 0, v___x_3777_);
return v___x_3778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillWrapping___redArg___lam__0(lean_object* v_x_3779_){
_start:
{
lean_object* v___x_3780_; 
v___x_3780_ = lean_obj_once(&l_Lean_Fmt_Doc_fillWrapping___redArg___lam__0___closed__0, &l_Lean_Fmt_Doc_fillWrapping___redArg___lam__0___closed__0_once, _init_l_Lean_Fmt_Doc_fillWrapping___redArg___lam__0___closed__0);
return v___x_3780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillWrapping___redArg___lam__0___boxed(lean_object* v_x_3781_){
_start:
{
lean_object* v_res_3782_; 
v_res_3782_ = l_Lean_Fmt_Doc_fillWrapping___redArg___lam__0(v_x_3781_);
lean_dec(v_x_3781_);
return v_res_3782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillWrapping___redArg(lean_object* v_ds_3784_, lean_object* v_wrap_3785_){
_start:
{
lean_object* v___f_3786_; lean_object* v___x_3787_; 
v___f_3786_ = ((lean_object*)(l_Lean_Fmt_Doc_fillWrapping___redArg___closed__0));
v___x_3787_ = l_Lean_Fmt_Doc_fillWrappingWith___redArg(v_ds_3784_, v_wrap_3785_, v___f_3786_);
return v___x_3787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillWrapping(lean_object* v_00_u03c4_3788_, lean_object* v_ds_3789_, lean_object* v_wrap_3790_){
_start:
{
lean_object* v___x_3791_; 
v___x_3791_ = l_Lean_Fmt_Doc_fillWrapping___redArg(v_ds_3789_, v_wrap_3790_);
return v___x_3791_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3792_; lean_object* v___x_3793_; 
v___x_3792_ = lean_obj_once(&l_Lean_Fmt_Doc_fillUsingSpace___redArg___lam__0___closed__0, &l_Lean_Fmt_Doc_fillUsingSpace___redArg___lam__0___closed__0_once, _init_l_Lean_Fmt_Doc_fillUsingSpace___redArg___lam__0___closed__0);
v___x_3793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3793_, 0, v___x_3792_);
return v___x_3793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg___lam__0(lean_object* v_x_3794_){
_start:
{
lean_object* v___x_3795_; 
v___x_3795_ = lean_obj_once(&l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg___lam__0___closed__0, &l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg___lam__0___closed__0_once, _init_l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg___lam__0___closed__0);
return v___x_3795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg___lam__0___boxed(lean_object* v_x_3796_){
_start:
{
lean_object* v_res_3797_; 
v_res_3797_ = l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg___lam__0(v_x_3796_);
lean_dec(v_x_3796_);
return v_res_3797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg(lean_object* v_ds_3799_, lean_object* v_wrap_3800_){
_start:
{
lean_object* v___f_3801_; lean_object* v___x_3802_; 
v___f_3801_ = ((lean_object*)(l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg___closed__0));
v___x_3802_ = l_Lean_Fmt_Doc_fillWrappingWith___redArg(v_ds_3799_, v_wrap_3800_, v___f_3801_);
return v___x_3802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWrapping(lean_object* v_00_u03c4_3803_, lean_object* v_ds_3804_, lean_object* v_wrap_3805_){
_start:
{
lean_object* v___x_3806_; 
v___x_3806_ = l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg(v_ds_3804_, v_wrap_3805_);
return v___x_3806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedFillable_default___redArg(lean_object* v_inst_3807_){
_start:
{
uint8_t v___x_3808_; lean_object* v___x_3809_; 
v___x_3808_ = 0;
v___x_3809_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3809_, 0, v_inst_3807_);
lean_ctor_set_uint8(v___x_3809_, sizeof(void*)*1, v___x_3808_);
return v___x_3809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedFillable_default(lean_object* v_00_u03b1_3810_, lean_object* v_inst_3811_){
_start:
{
lean_object* v___x_3812_; 
v___x_3812_ = l_Lean_Fmt_instInhabitedFillable_default___redArg(v_inst_3811_);
return v___x_3812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedFillable___redArg(lean_object* v_inst_3813_){
_start:
{
lean_object* v___x_3814_; 
v___x_3814_ = l_Lean_Fmt_instInhabitedFillable_default___redArg(v_inst_3813_);
return v___x_3814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedFillable(lean_object* v_a_3815_, lean_object* v_inst_3816_){
_start:
{
lean_object* v___x_3817_; 
v___x_3817_ = l_Lean_Fmt_instInhabitedFillable_default___redArg(v_inst_3816_);
return v___x_3817_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0___redArg(size_t v_sz_3818_, size_t v_i_3819_, lean_object* v_bs_3820_){
_start:
{
uint8_t v___x_3821_; 
v___x_3821_ = lean_usize_dec_lt(v_i_3819_, v_sz_3818_);
if (v___x_3821_ == 0)
{
return v_bs_3820_;
}
else
{
lean_object* v_v_3822_; lean_object* v_v_3823_; lean_object* v___x_3824_; lean_object* v_bs_x27_3825_; size_t v___x_3826_; size_t v___x_3827_; lean_object* v___x_3828_; 
v_v_3822_ = lean_array_uget_borrowed(v_bs_3820_, v_i_3819_);
v_v_3823_ = lean_ctor_get(v_v_3822_, 0);
lean_inc(v_v_3823_);
v___x_3824_ = lean_unsigned_to_nat(0u);
v_bs_x27_3825_ = lean_array_uset(v_bs_3820_, v_i_3819_, v___x_3824_);
v___x_3826_ = ((size_t)1ULL);
v___x_3827_ = lean_usize_add(v_i_3819_, v___x_3826_);
v___x_3828_ = lean_array_uset(v_bs_x27_3825_, v_i_3819_, v_v_3823_);
v_i_3819_ = v___x_3827_;
v_bs_3820_ = v___x_3828_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0___redArg___boxed(lean_object* v_sz_3830_, lean_object* v_i_3831_, lean_object* v_bs_3832_){
_start:
{
size_t v_sz_boxed_3833_; size_t v_i_boxed_3834_; lean_object* v_res_3835_; 
v_sz_boxed_3833_ = lean_unbox_usize(v_sz_3830_);
lean_dec(v_sz_3830_);
v_i_boxed_3834_ = lean_unbox_usize(v_i_3831_);
lean_dec(v_i_3831_);
v_res_3835_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0___redArg(v_sz_boxed_3833_, v_i_boxed_3834_, v_bs_3832_);
return v_res_3835_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3___redArg(size_t v_sz_3836_, size_t v_i_3837_, lean_object* v_bs_3838_){
_start:
{
uint8_t v___x_3839_; 
v___x_3839_ = lean_usize_dec_lt(v_i_3837_, v_sz_3836_);
if (v___x_3839_ == 0)
{
return v_bs_3838_;
}
else
{
lean_object* v_v_3840_; lean_object* v___x_3841_; lean_object* v_bs_x27_3842_; size_t v_sz_3843_; size_t v___x_3844_; lean_object* v___x_3845_; size_t v___x_3846_; size_t v___x_3847_; lean_object* v___x_3848_; 
v_v_3840_ = lean_array_uget(v_bs_3838_, v_i_3837_);
v___x_3841_ = lean_unsigned_to_nat(0u);
v_bs_x27_3842_ = lean_array_uset(v_bs_3838_, v_i_3837_, v___x_3841_);
v_sz_3843_ = lean_array_size(v_v_3840_);
v___x_3844_ = ((size_t)0ULL);
v___x_3845_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0___redArg(v_sz_3843_, v___x_3844_, v_v_3840_);
v___x_3846_ = ((size_t)1ULL);
v___x_3847_ = lean_usize_add(v_i_3837_, v___x_3846_);
v___x_3848_ = lean_array_uset(v_bs_x27_3842_, v_i_3837_, v___x_3845_);
v_i_3837_ = v___x_3847_;
v_bs_3838_ = v___x_3848_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3___redArg___boxed(lean_object* v_sz_3850_, lean_object* v_i_3851_, lean_object* v_bs_3852_){
_start:
{
size_t v_sz_boxed_3853_; size_t v_i_boxed_3854_; lean_object* v_res_3855_; 
v_sz_boxed_3853_ = lean_unbox_usize(v_sz_3850_);
lean_dec(v_sz_3850_);
v_i_boxed_3854_ = lean_unbox_usize(v_i_3851_);
lean_dec(v_i_3851_);
v_res_3855_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3___redArg(v_sz_boxed_3853_, v_i_boxed_3854_, v_bs_3852_);
return v_res_3855_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Fmt_Doc_splitFillGroups_spec__2___redArg(lean_object* v_a_3856_, lean_object* v_a_3857_){
_start:
{
if (lean_obj_tag(v_a_3856_) == 0)
{
lean_object* v___x_3858_; 
v___x_3858_ = l_List_reverse___redArg(v_a_3857_);
return v___x_3858_;
}
else
{
lean_object* v_head_3859_; lean_object* v_tail_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3869_; 
v_head_3859_ = lean_ctor_get(v_a_3856_, 0);
v_tail_3860_ = lean_ctor_get(v_a_3856_, 1);
v_isSharedCheck_3869_ = !lean_is_exclusive(v_a_3856_);
if (v_isSharedCheck_3869_ == 0)
{
v___x_3862_ = v_a_3856_;
v_isShared_3863_ = v_isSharedCheck_3869_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_tail_3860_);
lean_inc(v_head_3859_);
lean_dec(v_a_3856_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3869_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v___x_3864_; lean_object* v___x_3866_; 
v___x_3864_ = lean_array_mk(v_head_3859_);
if (v_isShared_3863_ == 0)
{
lean_ctor_set(v___x_3862_, 1, v_a_3857_);
lean_ctor_set(v___x_3862_, 0, v___x_3864_);
v___x_3866_ = v___x_3862_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v___x_3864_);
lean_ctor_set(v_reuseFailAlloc_3868_, 1, v_a_3857_);
v___x_3866_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
v_a_3856_ = v_tail_3860_;
v_a_3857_ = v___x_3866_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_splitBy_loop___at___00List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1_spec__1___redArg(lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_){
_start:
{
if (lean_obj_tag(v_a_3870_) == 0)
{
lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; 
v___x_3874_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3874_, 0, v_a_3871_);
lean_ctor_set(v___x_3874_, 1, v_a_3872_);
v___x_3875_ = l_List_reverse___redArg(v___x_3874_);
v___x_3876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3876_, 0, v___x_3875_);
lean_ctor_set(v___x_3876_, 1, v_a_3873_);
v___x_3877_ = l_List_reverse___redArg(v___x_3876_);
return v___x_3877_;
}
else
{
lean_object* v_head_3878_; lean_object* v_tail_3879_; lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3895_; 
v_head_3878_ = lean_ctor_get(v_a_3870_, 0);
v_tail_3879_ = lean_ctor_get(v_a_3870_, 1);
v_isSharedCheck_3895_ = !lean_is_exclusive(v_a_3870_);
if (v_isSharedCheck_3895_ == 0)
{
v___x_3881_ = v_a_3870_;
v_isShared_3882_ = v_isSharedCheck_3895_;
goto v_resetjp_3880_;
}
else
{
lean_inc(v_tail_3879_);
lean_inc(v_head_3878_);
lean_dec(v_a_3870_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3895_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
uint8_t v_allowFill_3891_; 
v_allowFill_3891_ = lean_ctor_get_uint8(v_a_3871_, sizeof(void*)*1);
if (v_allowFill_3891_ == 0)
{
goto v___jp_3883_;
}
else
{
uint8_t v_allowFill_3892_; 
v_allowFill_3892_ = lean_ctor_get_uint8(v_head_3878_, sizeof(void*)*1);
if (v_allowFill_3892_ == 0)
{
goto v___jp_3883_;
}
else
{
lean_object* v___x_3893_; 
lean_del_object(v___x_3881_);
v___x_3893_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3893_, 0, v_a_3871_);
lean_ctor_set(v___x_3893_, 1, v_a_3872_);
v_a_3870_ = v_tail_3879_;
v_a_3871_ = v_head_3878_;
v_a_3872_ = v___x_3893_;
goto _start;
}
}
v___jp_3883_:
{
lean_object* v___x_3884_; lean_object* v___x_3886_; 
v___x_3884_ = lean_box(0);
if (v_isShared_3882_ == 0)
{
lean_ctor_set(v___x_3881_, 1, v_a_3872_);
lean_ctor_set(v___x_3881_, 0, v_a_3871_);
v___x_3886_ = v___x_3881_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v_a_3871_);
lean_ctor_set(v_reuseFailAlloc_3890_, 1, v_a_3872_);
v___x_3886_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
lean_object* v___x_3887_; lean_object* v___x_3888_; 
v___x_3887_ = l_List_reverse___redArg(v___x_3886_);
v___x_3888_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3888_, 0, v___x_3887_);
lean_ctor_set(v___x_3888_, 1, v_a_3873_);
v_a_3870_ = v_tail_3879_;
v_a_3871_ = v_head_3878_;
v_a_3872_ = v___x_3884_;
v_a_3873_ = v___x_3888_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1___redArg(lean_object* v_x_3896_){
_start:
{
if (lean_obj_tag(v_x_3896_) == 0)
{
lean_object* v___x_3897_; 
v___x_3897_ = lean_box(0);
return v___x_3897_;
}
else
{
lean_object* v_head_3898_; lean_object* v_tail_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; 
v_head_3898_ = lean_ctor_get(v_x_3896_, 0);
lean_inc(v_head_3898_);
v_tail_3899_ = lean_ctor_get(v_x_3896_, 1);
lean_inc(v_tail_3899_);
lean_dec_ref_known(v_x_3896_, 2);
v___x_3900_ = lean_box(0);
v___x_3901_ = l_List_splitBy_loop___at___00List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1_spec__1___redArg(v_tail_3899_, v_head_3898_, v___x_3900_, v___x_3900_);
return v___x_3901_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_splitFillGroups___redArg(lean_object* v_ds_3902_){
_start:
{
lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; size_t v_sz_3908_; size_t v___x_3909_; lean_object* v___x_3910_; 
v___x_3903_ = lean_array_to_list(v_ds_3902_);
v___x_3904_ = l_List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1___redArg(v___x_3903_);
v___x_3905_ = lean_box(0);
v___x_3906_ = l_List_mapTR_loop___at___00Lean_Fmt_Doc_splitFillGroups_spec__2___redArg(v___x_3904_, v___x_3905_);
v___x_3907_ = lean_array_mk(v___x_3906_);
v_sz_3908_ = lean_array_size(v___x_3907_);
v___x_3909_ = ((size_t)0ULL);
v___x_3910_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3___redArg(v_sz_3908_, v___x_3909_, v___x_3907_);
return v___x_3910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_splitFillGroups(lean_object* v_00_u03c4_3911_, lean_object* v_ds_3912_){
_start:
{
lean_object* v___x_3913_; 
v___x_3913_ = l_Lean_Fmt_Doc_splitFillGroups___redArg(v_ds_3912_);
return v___x_3913_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0(lean_object* v_00_u03c4_3914_, size_t v_sz_3915_, size_t v_i_3916_, lean_object* v_bs_3917_){
_start:
{
lean_object* v___x_3918_; 
v___x_3918_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0___redArg(v_sz_3915_, v_i_3916_, v_bs_3917_);
return v___x_3918_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0___boxed(lean_object* v_00_u03c4_3919_, lean_object* v_sz_3920_, lean_object* v_i_3921_, lean_object* v_bs_3922_){
_start:
{
size_t v_sz_boxed_3923_; size_t v_i_boxed_3924_; lean_object* v_res_3925_; 
v_sz_boxed_3923_ = lean_unbox_usize(v_sz_3920_);
lean_dec(v_sz_3920_);
v_i_boxed_3924_ = lean_unbox_usize(v_i_3921_);
lean_dec(v_i_3921_);
v_res_3925_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0(v_00_u03c4_3919_, v_sz_boxed_3923_, v_i_boxed_3924_, v_bs_3922_);
return v_res_3925_;
}
}
LEAN_EXPORT lean_object* l_List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1(lean_object* v_00_u03c4_3926_, lean_object* v_x_3927_){
_start:
{
lean_object* v___x_3928_; 
v___x_3928_ = l_List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1___redArg(v_x_3927_);
return v___x_3928_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Fmt_Doc_splitFillGroups_spec__2(lean_object* v_00_u03c4_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_){
_start:
{
lean_object* v___x_3932_; 
v___x_3932_ = l_List_mapTR_loop___at___00Lean_Fmt_Doc_splitFillGroups_spec__2___redArg(v_a_3930_, v_a_3931_);
return v___x_3932_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3(lean_object* v_00_u03c4_3933_, size_t v_sz_3934_, size_t v_i_3935_, lean_object* v_bs_3936_){
_start:
{
lean_object* v___x_3937_; 
v___x_3937_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3___redArg(v_sz_3934_, v_i_3935_, v_bs_3936_);
return v___x_3937_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3___boxed(lean_object* v_00_u03c4_3938_, lean_object* v_sz_3939_, lean_object* v_i_3940_, lean_object* v_bs_3941_){
_start:
{
size_t v_sz_boxed_3942_; size_t v_i_boxed_3943_; lean_object* v_res_3944_; 
v_sz_boxed_3942_ = lean_unbox_usize(v_sz_3939_);
lean_dec(v_sz_3939_);
v_i_boxed_3943_ = lean_unbox_usize(v_i_3940_);
lean_dec(v_i_3940_);
v_res_3944_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3(v_00_u03c4_3938_, v_sz_boxed_3942_, v_i_boxed_3943_, v_bs_3941_);
return v_res_3944_;
}
}
LEAN_EXPORT lean_object* l_List_splitBy_loop___at___00List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1_spec__1(lean_object* v_00_u03c4_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_){
_start:
{
lean_object* v___x_3950_; 
v___x_3950_ = l_List_splitBy_loop___at___00List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1_spec__1___redArg(v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_);
return v___x_3950_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0___redArg(size_t v_sz_3951_, size_t v_i_3952_, lean_object* v_bs_3953_){
_start:
{
uint8_t v___x_3954_; 
v___x_3954_ = lean_usize_dec_lt(v_i_3952_, v_sz_3951_);
if (v___x_3954_ == 0)
{
return v_bs_3953_;
}
else
{
lean_object* v_v_3955_; lean_object* v___x_3956_; lean_object* v_bs_x27_3957_; lean_object* v___x_3958_; size_t v___x_3959_; size_t v___x_3960_; lean_object* v___x_3961_; 
v_v_3955_ = lean_array_uget(v_bs_3953_, v_i_3952_);
v___x_3956_ = lean_unsigned_to_nat(0u);
v_bs_x27_3957_ = lean_array_uset(v_bs_3953_, v_i_3952_, v___x_3956_);
v___x_3958_ = l_Lean_Fmt_Doc_fillUsingSpace___redArg(v_v_3955_);
lean_dec(v_v_3955_);
v___x_3959_ = ((size_t)1ULL);
v___x_3960_ = lean_usize_add(v_i_3952_, v___x_3959_);
v___x_3961_ = lean_array_uset(v_bs_x27_3957_, v_i_3952_, v___x_3958_);
v_i_3952_ = v___x_3960_;
v_bs_3953_ = v___x_3961_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0___redArg___boxed(lean_object* v_sz_3963_, lean_object* v_i_3964_, lean_object* v_bs_3965_){
_start:
{
size_t v_sz_boxed_3966_; size_t v_i_boxed_3967_; lean_object* v_res_3968_; 
v_sz_boxed_3966_ = lean_unbox_usize(v_sz_3963_);
lean_dec(v_sz_3963_);
v_i_boxed_3967_ = lean_unbox_usize(v_i_3964_);
lean_dec(v_i_3964_);
v_res_3968_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0___redArg(v_sz_boxed_3966_, v_i_boxed_3967_, v_bs_3965_);
return v_res_3968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillSomeUsingSpace___redArg(lean_object* v_ds_3969_){
_start:
{
lean_object* v_fillGroups_3970_; lean_object* v___x_3971_; size_t v_sz_3972_; size_t v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; 
v_fillGroups_3970_ = l_Lean_Fmt_Doc_splitFillGroups___redArg(v_ds_3969_);
v___x_3971_ = lean_obj_once(&l_Lean_Fmt_Doc_nl___closed__0, &l_Lean_Fmt_Doc_nl___closed__0_once, _init_l_Lean_Fmt_Doc_nl___closed__0);
v_sz_3972_ = lean_array_size(v_fillGroups_3970_);
v___x_3973_ = ((size_t)0ULL);
v___x_3974_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0___redArg(v_sz_3972_, v___x_3973_, v_fillGroups_3970_);
v___x_3975_ = l_Lean_Fmt_Doc_joinUsing___redArg(v___x_3971_, v___x_3974_);
return v___x_3975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillSomeUsingSpace(lean_object* v_00_u03c4_3976_, lean_object* v_ds_3977_){
_start:
{
lean_object* v___x_3978_; 
v___x_3978_ = l_Lean_Fmt_Doc_fillSomeUsingSpace___redArg(v_ds_3977_);
return v___x_3978_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0(lean_object* v_00_u03c4_3979_, size_t v_sz_3980_, size_t v_i_3981_, lean_object* v_bs_3982_){
_start:
{
lean_object* v___x_3983_; 
v___x_3983_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0___redArg(v_sz_3980_, v_i_3981_, v_bs_3982_);
return v___x_3983_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0___boxed(lean_object* v_00_u03c4_3984_, lean_object* v_sz_3985_, lean_object* v_i_3986_, lean_object* v_bs_3987_){
_start:
{
size_t v_sz_boxed_3988_; size_t v_i_boxed_3989_; lean_object* v_res_3990_; 
v_sz_boxed_3988_ = lean_unbox_usize(v_sz_3985_);
lean_dec(v_sz_3985_);
v_i_boxed_3989_ = lean_unbox_usize(v_i_3986_);
lean_dec(v_i_3986_);
v_res_3990_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0(v_00_u03c4_3984_, v_sz_boxed_3988_, v_i_boxed_3989_, v_bs_3987_);
return v_res_3990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg___lam__0(lean_object* v___x_3991_, lean_object* v_ds_3992_, lean_object* v_i_3993_){
_start:
{
lean_object* v___x_3994_; uint8_t v_allowFill_3995_; 
v___x_3994_ = lean_array_get_borrowed(v___x_3991_, v_ds_3992_, v_i_3993_);
v_allowFill_3995_ = lean_ctor_get_uint8(v___x_3994_, sizeof(void*)*1);
if (v_allowFill_3995_ == 0)
{
lean_object* v___x_3996_; 
v___x_3996_ = lean_box(0);
return v___x_3996_;
}
else
{
lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; uint8_t v_allowFill_4000_; 
v___x_3997_ = lean_unsigned_to_nat(1u);
v___x_3998_ = lean_nat_add(v_i_3993_, v___x_3997_);
v___x_3999_ = lean_array_get_borrowed(v___x_3991_, v_ds_3992_, v___x_3998_);
lean_dec(v___x_3998_);
v_allowFill_4000_ = lean_ctor_get_uint8(v___x_3999_, sizeof(void*)*1);
if (v_allowFill_4000_ == 0)
{
lean_object* v___x_4001_; 
v___x_4001_ = lean_box(0);
return v___x_4001_;
}
else
{
lean_object* v___x_4002_; 
v___x_4002_ = lean_obj_once(&l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg___lam__0___closed__0, &l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg___lam__0___closed__0_once, _init_l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg___lam__0___closed__0);
return v___x_4002_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg___lam__0___boxed(lean_object* v___x_4003_, lean_object* v_ds_4004_, lean_object* v_i_4005_){
_start:
{
lean_object* v_res_4006_; 
v_res_4006_ = l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg___lam__0(v___x_4003_, v_ds_4004_, v_i_4005_);
lean_dec(v_i_4005_);
lean_dec_ref(v_ds_4004_);
lean_dec_ref(v___x_4003_);
return v_res_4006_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg___closed__0(void){
_start:
{
lean_object* v___x_4007_; lean_object* v___x_4008_; 
v___x_4007_ = lean_box(0);
v___x_4008_ = l_Lean_Fmt_instInhabitedFillable_default___redArg(v___x_4007_);
return v___x_4008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg(lean_object* v_ds_4009_, lean_object* v_wrap_4010_){
_start:
{
lean_object* v___x_4011_; lean_object* v___f_4012_; size_t v_sz_4013_; size_t v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; 
v___x_4011_ = lean_obj_once(&l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg___closed__0, &l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg___closed__0_once, _init_l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg___closed__0);
lean_inc_ref(v_ds_4009_);
v___f_4012_ = lean_alloc_closure((void*)(l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4012_, 0, v___x_4011_);
lean_closure_set(v___f_4012_, 1, v_ds_4009_);
v_sz_4013_ = lean_array_size(v_ds_4009_);
v___x_4014_ = ((size_t)0ULL);
v___x_4015_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0___redArg(v_sz_4013_, v___x_4014_, v_ds_4009_);
v___x_4016_ = l_Lean_Fmt_Doc_fillWrappingWith___redArg(v___x_4015_, v_wrap_4010_, v___f_4012_);
return v___x_4016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping(lean_object* v_00_u03c4_4017_, lean_object* v_ds_4018_, lean_object* v_wrap_4019_){
_start:
{
lean_object* v___x_4020_; 
v___x_4020_ = l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg(v_ds_4018_, v_wrap_4019_);
return v___x_4020_;
}
}
static size_t _init_l_Lean_Fmt_instInhabitedPtrKey_default___redArg___closed__0(void){
_start:
{
lean_object* v___x_4021_; size_t v___x_4022_; 
v___x_4021_ = lean_unsigned_to_nat(0u);
v___x_4022_ = lean_usize_of_nat(v___x_4021_);
return v___x_4022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedPtrKey_default___redArg(lean_object* v_inst_4023_){
_start:
{
size_t v___x_4024_; lean_object* v___x_4025_; 
v___x_4024_ = lean_usize_once(&l_Lean_Fmt_instInhabitedPtrKey_default___redArg___closed__0, &l_Lean_Fmt_instInhabitedPtrKey_default___redArg___closed__0_once, _init_l_Lean_Fmt_instInhabitedPtrKey_default___redArg___closed__0);
v___x_4025_ = lean_alloc_ctor(0, 1, sizeof(size_t)*1);
lean_ctor_set(v___x_4025_, 0, v_inst_4023_);
lean_ctor_set_usize(v___x_4025_, 1, v___x_4024_);
return v___x_4025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedPtrKey_default(lean_object* v_00_u03b1_4026_, lean_object* v_inst_4027_){
_start:
{
lean_object* v___x_4028_; 
v___x_4028_ = l_Lean_Fmt_instInhabitedPtrKey_default___redArg(v_inst_4027_);
return v___x_4028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedPtrKey___redArg(lean_object* v_inst_4029_){
_start:
{
lean_object* v___x_4030_; 
v___x_4030_ = l_Lean_Fmt_instInhabitedPtrKey_default___redArg(v_inst_4029_);
return v___x_4030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedPtrKey(lean_object* v_a_4031_, lean_object* v_inst_4032_){
_start:
{
lean_object* v___x_4033_; 
v___x_4033_ = l_Lean_Fmt_instInhabitedPtrKey_default___redArg(v_inst_4032_);
return v___x_4033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_PtrKey_ofKey___redArg(lean_object* v_v_4034_){
_start:
{
size_t v___x_4035_; lean_object* v___x_4036_; 
v___x_4035_ = lean_ptr_addr(v_v_4034_);
v___x_4036_ = lean_alloc_ctor(0, 1, sizeof(size_t)*1);
lean_ctor_set(v___x_4036_, 0, v_v_4034_);
lean_ctor_set_usize(v___x_4036_, 1, v___x_4035_);
return v___x_4036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_PtrKey_ofKey(lean_object* v_00_u03b1_4037_, lean_object* v_v_4038_){
_start:
{
lean_object* v___x_4039_; 
v___x_4039_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_v_4038_);
return v___x_4039_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqPtrKey___redArg___lam__0(lean_object* v_v1_4040_, lean_object* v_v2_4041_){
_start:
{
size_t v_ptr_4042_; size_t v_ptr_4043_; uint8_t v___x_4044_; 
v_ptr_4042_ = lean_ctor_get_usize(v_v1_4040_, 1);
v_ptr_4043_ = lean_ctor_get_usize(v_v2_4041_, 1);
v___x_4044_ = lean_usize_dec_eq(v_ptr_4042_, v_ptr_4043_);
return v___x_4044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqPtrKey___redArg___lam__0___boxed(lean_object* v_v1_4045_, lean_object* v_v2_4046_){
_start:
{
uint8_t v_res_4047_; lean_object* v_r_4048_; 
v_res_4047_ = l_Lean_Fmt_instBEqPtrKey___redArg___lam__0(v_v1_4045_, v_v2_4046_);
lean_dec_ref(v_v2_4046_);
lean_dec_ref(v_v1_4045_);
v_r_4048_ = lean_box(v_res_4047_);
return v_r_4048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqPtrKey___redArg(){
_start:
{
lean_object* v___f_4051_; 
v___f_4051_ = ((lean_object*)(l_Lean_Fmt_instBEqPtrKey___redArg___closed__0));
return v___f_4051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqPtrKey___redArg___boxed(lean_object* v___dummy_4052_){
_start:
{
lean_object* v_res_4053_; 
v_res_4053_ = l_Lean_Fmt_instBEqPtrKey___redArg();
return v_res_4053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqPtrKey(lean_object* v_00_u03b1_4054_){
_start:
{
lean_object* v___f_4055_; 
v___f_4055_ = ((lean_object*)(l_Lean_Fmt_instBEqPtrKey___redArg___closed__0));
return v___f_4055_;
}
}
LEAN_EXPORT uint64_t l_Lean_Fmt_instHashablePtrKey___redArg___lam__0(lean_object* v_v_4056_){
_start:
{
size_t v_ptr_4057_; uint64_t v___x_4058_; 
v_ptr_4057_ = lean_ctor_get_usize(v_v_4056_, 1);
v___x_4058_ = lean_usize_to_uint64(v_ptr_4057_);
return v___x_4058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashablePtrKey___redArg___lam__0___boxed(lean_object* v_v_4059_){
_start:
{
uint64_t v_res_4060_; lean_object* v_r_4061_; 
v_res_4060_ = l_Lean_Fmt_instHashablePtrKey___redArg___lam__0(v_v_4059_);
lean_dec_ref(v_v_4059_);
v_r_4061_ = lean_box_uint64(v_res_4060_);
return v_r_4061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashablePtrKey___redArg(){
_start:
{
lean_object* v___f_4064_; 
v___f_4064_ = ((lean_object*)(l_Lean_Fmt_instHashablePtrKey___redArg___closed__0));
return v___f_4064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashablePtrKey___redArg___boxed(lean_object* v___dummy_4065_){
_start:
{
lean_object* v_res_4066_; 
v_res_4066_ = l_Lean_Fmt_instHashablePtrKey___redArg();
return v_res_4066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashablePtrKey(lean_object* v_00_u03b1_4067_){
_start:
{
lean_object* v___f_4068_; 
v___f_4068_ = ((lean_object*)(l_Lean_Fmt_instHashablePtrKey___redArg___closed__0));
return v___f_4068_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqBEqCacheKey_beq___redArg(lean_object* v_x_4069_, lean_object* v_x_4070_){
_start:
{
lean_object* v_aPtr_4071_; lean_object* v_aPtr_4072_; lean_object* v_bPtr_4073_; lean_object* v_bPtr_4074_; size_t v_ptr_4075_; size_t v_ptr_4076_; uint8_t v___x_4077_; 
v_aPtr_4071_ = lean_ctor_get(v_x_4069_, 0);
v_aPtr_4072_ = lean_ctor_get(v_x_4070_, 0);
v_bPtr_4073_ = lean_ctor_get(v_x_4069_, 1);
v_bPtr_4074_ = lean_ctor_get(v_x_4070_, 1);
v_ptr_4075_ = lean_ctor_get_usize(v_aPtr_4071_, 1);
v_ptr_4076_ = lean_ctor_get_usize(v_aPtr_4072_, 1);
v___x_4077_ = lean_usize_dec_eq(v_ptr_4075_, v_ptr_4076_);
if (v___x_4077_ == 0)
{
return v___x_4077_;
}
else
{
size_t v_ptr_4078_; size_t v_ptr_4079_; uint8_t v___x_4080_; 
v_ptr_4078_ = lean_ctor_get_usize(v_bPtr_4073_, 1);
v_ptr_4079_ = lean_ctor_get_usize(v_bPtr_4074_, 1);
v___x_4080_ = lean_usize_dec_eq(v_ptr_4078_, v_ptr_4079_);
return v___x_4080_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqBEqCacheKey_beq___redArg___boxed(lean_object* v_x_4081_, lean_object* v_x_4082_){
_start:
{
uint8_t v_res_4083_; lean_object* v_r_4084_; 
v_res_4083_ = l_Lean_Fmt_instBEqBEqCacheKey_beq___redArg(v_x_4081_, v_x_4082_);
lean_dec_ref(v_x_4082_);
lean_dec_ref(v_x_4081_);
v_r_4084_ = lean_box(v_res_4083_);
return v_r_4084_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqBEqCacheKey_beq(lean_object* v_00_u03c4_4085_, lean_object* v_inst_4086_, lean_object* v_x_4087_, lean_object* v_x_4088_){
_start:
{
uint8_t v___x_4089_; 
v___x_4089_ = l_Lean_Fmt_instBEqBEqCacheKey_beq___redArg(v_x_4087_, v_x_4088_);
return v___x_4089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqBEqCacheKey_beq___boxed(lean_object* v_00_u03c4_4090_, lean_object* v_inst_4091_, lean_object* v_x_4092_, lean_object* v_x_4093_){
_start:
{
uint8_t v_res_4094_; lean_object* v_r_4095_; 
v_res_4094_ = l_Lean_Fmt_instBEqBEqCacheKey_beq(v_00_u03c4_4090_, v_inst_4091_, v_x_4092_, v_x_4093_);
lean_dec_ref(v_x_4093_);
lean_dec_ref(v_x_4092_);
lean_dec_ref(v_inst_4091_);
v_r_4095_ = lean_box(v_res_4094_);
return v_r_4095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqBEqCacheKey___redArg(lean_object* v_inst_4096_){
_start:
{
lean_object* v___x_4097_; 
v___x_4097_ = lean_alloc_closure((void*)(l_Lean_Fmt_instBEqBEqCacheKey_beq___boxed), 4, 2);
lean_closure_set(v___x_4097_, 0, lean_box(0));
lean_closure_set(v___x_4097_, 1, v_inst_4096_);
return v___x_4097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqBEqCacheKey(lean_object* v_00_u03c4_4098_, lean_object* v_inst_4099_){
_start:
{
lean_object* v___x_4100_; 
v___x_4100_ = lean_alloc_closure((void*)(l_Lean_Fmt_instBEqBEqCacheKey_beq___boxed), 4, 2);
lean_closure_set(v___x_4100_, 0, lean_box(0));
lean_closure_set(v___x_4100_, 1, v_inst_4099_);
return v___x_4100_;
}
}
LEAN_EXPORT uint64_t l_Lean_Fmt_instHashableBEqCacheKey_hash___redArg(lean_object* v_x_4101_){
_start:
{
lean_object* v_aPtr_4102_; lean_object* v_bPtr_4103_; size_t v_ptr_4104_; size_t v_ptr_4105_; uint64_t v___x_4106_; uint64_t v___x_4107_; uint64_t v___x_4108_; uint64_t v___x_4109_; uint64_t v___x_4110_; 
v_aPtr_4102_ = lean_ctor_get(v_x_4101_, 0);
v_bPtr_4103_ = lean_ctor_get(v_x_4101_, 1);
v_ptr_4104_ = lean_ctor_get_usize(v_aPtr_4102_, 1);
v_ptr_4105_ = lean_ctor_get_usize(v_bPtr_4103_, 1);
v___x_4106_ = 0ULL;
v___x_4107_ = lean_usize_to_uint64(v_ptr_4104_);
v___x_4108_ = lean_uint64_mix_hash(v___x_4106_, v___x_4107_);
v___x_4109_ = lean_usize_to_uint64(v_ptr_4105_);
v___x_4110_ = lean_uint64_mix_hash(v___x_4108_, v___x_4109_);
return v___x_4110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableBEqCacheKey_hash___redArg___boxed(lean_object* v_x_4111_){
_start:
{
uint64_t v_res_4112_; lean_object* v_r_4113_; 
v_res_4112_ = l_Lean_Fmt_instHashableBEqCacheKey_hash___redArg(v_x_4111_);
lean_dec_ref(v_x_4111_);
v_r_4113_ = lean_box_uint64(v_res_4112_);
return v_r_4113_;
}
}
LEAN_EXPORT uint64_t l_Lean_Fmt_instHashableBEqCacheKey_hash(lean_object* v_00_u03c4_4114_, lean_object* v_inst_4115_, lean_object* v_x_4116_){
_start:
{
uint64_t v___x_4117_; 
v___x_4117_ = l_Lean_Fmt_instHashableBEqCacheKey_hash___redArg(v_x_4116_);
return v___x_4117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableBEqCacheKey_hash___boxed(lean_object* v_00_u03c4_4118_, lean_object* v_inst_4119_, lean_object* v_x_4120_){
_start:
{
uint64_t v_res_4121_; lean_object* v_r_4122_; 
v_res_4121_ = l_Lean_Fmt_instHashableBEqCacheKey_hash(v_00_u03c4_4118_, v_inst_4119_, v_x_4120_);
lean_dec_ref(v_x_4120_);
lean_dec_ref(v_inst_4119_);
v_r_4122_ = lean_box_uint64(v_res_4121_);
return v_r_4122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableBEqCacheKey___redArg(lean_object* v_inst_4123_){
_start:
{
lean_object* v___x_4124_; 
v___x_4124_ = lean_alloc_closure((void*)(l_Lean_Fmt_instHashableBEqCacheKey_hash___boxed), 3, 2);
lean_closure_set(v___x_4124_, 0, lean_box(0));
lean_closure_set(v___x_4124_, 1, v_inst_4123_);
return v___x_4124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableBEqCacheKey(lean_object* v_00_u03c4_4125_, lean_object* v_inst_4126_){
_start:
{
lean_object* v___x_4127_; 
v___x_4127_ = lean_alloc_closure((void*)(l_Lean_Fmt_instHashableBEqCacheKey_hash___boxed), 3, 2);
lean_closure_set(v___x_4127_, 0, lean_box(0));
lean_closure_set(v___x_4127_, 1, v_inst_4126_);
return v___x_4127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized_unsafe__1___redArg(lean_object* v_a_4128_){
_start:
{
lean_object* v___x_4129_; 
v___x_4129_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_a_4128_);
return v___x_4129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized_unsafe__1(lean_object* v_00_u03c4_4130_, lean_object* v_a_4131_){
_start:
{
lean_object* v___x_4132_; 
v___x_4132_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_a_4131_);
return v___x_4132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized_unsafe__4___redArg(lean_object* v_b_4133_){
_start:
{
lean_object* v___x_4134_; 
v___x_4134_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_b_4133_);
return v___x_4134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized_unsafe__4(lean_object* v_00_u03c4_4135_, lean_object* v_b_4136_){
_start:
{
lean_object* v___x_4137_; 
v___x_4137_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_b_4136_);
return v___x_4137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_go___redArg(lean_object* v_inst_4138_, lean_object* v_inst_4139_, lean_object* v_a_4140_, lean_object* v_b_4141_, lean_object* v_a_4142_){
_start:
{
lean_object* v___y_4144_; lean_object* v_da1_4149_; lean_object* v_da2_4150_; lean_object* v_db1_4151_; lean_object* v_db2_4152_; lean_object* v___y_4153_; lean_object* v_sa_4160_; lean_object* v_sb_4161_; lean_object* v___y_4162_; 
switch(lean_obj_tag(v_a_4140_))
{
case 0:
{
lean_dec_ref(v_inst_4139_);
lean_dec_ref(v_inst_4138_);
if (lean_obj_tag(v_b_4141_) == 0)
{
uint8_t v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; 
v___x_4170_ = 1;
v___x_4171_ = lean_box(v___x_4170_);
v___x_4172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4172_, 0, v___x_4171_);
lean_ctor_set(v___x_4172_, 1, v_a_4142_);
return v___x_4172_;
}
else
{
lean_dec(v_b_4141_);
v___y_4144_ = v_a_4142_;
goto v___jp_4143_;
}
}
case 1:
{
lean_dec_ref(v_inst_4139_);
lean_dec_ref(v_inst_4138_);
if (lean_obj_tag(v_b_4141_) == 1)
{
lean_object* v_f_4173_; lean_object* v_f_4174_; 
v_f_4173_ = lean_ctor_get(v_a_4140_, 1);
lean_inc_ref(v_f_4173_);
lean_dec_ref_known(v_a_4140_, 2);
v_f_4174_ = lean_ctor_get(v_b_4141_, 1);
lean_inc_ref(v_f_4174_);
lean_dec_ref_known(v_b_4141_, 2);
v_sa_4160_ = v_f_4173_;
v_sb_4161_ = v_f_4174_;
v___y_4162_ = v_a_4142_;
goto v___jp_4159_;
}
else
{
lean_dec_ref_known(v_a_4140_, 2);
lean_dec(v_b_4141_);
v___y_4144_ = v_a_4142_;
goto v___jp_4143_;
}
}
case 2:
{
lean_dec_ref(v_inst_4139_);
lean_dec_ref(v_inst_4138_);
if (lean_obj_tag(v_b_4141_) == 2)
{
lean_object* v_s_4175_; lean_object* v_s_4176_; 
v_s_4175_ = lean_ctor_get(v_a_4140_, 1);
lean_inc_ref(v_s_4175_);
lean_dec_ref_known(v_a_4140_, 2);
v_s_4176_ = lean_ctor_get(v_b_4141_, 1);
lean_inc_ref(v_s_4176_);
lean_dec_ref_known(v_b_4141_, 2);
v_sa_4160_ = v_s_4175_;
v_sb_4161_ = v_s_4176_;
v___y_4162_ = v_a_4142_;
goto v___jp_4159_;
}
else
{
lean_dec_ref_known(v_a_4140_, 2);
lean_dec(v_b_4141_);
v___y_4144_ = v_a_4142_;
goto v___jp_4143_;
}
}
case 3:
{
if (lean_obj_tag(v_b_4141_) == 3)
{
lean_object* v_id_4177_; lean_object* v_d_4178_; lean_object* v_id_4179_; lean_object* v_d_4180_; uint8_t v___x_4181_; 
v_id_4177_ = lean_ctor_get(v_a_4140_, 1);
lean_inc(v_id_4177_);
v_d_4178_ = lean_ctor_get(v_a_4140_, 2);
lean_inc(v_d_4178_);
lean_dec_ref_known(v_a_4140_, 3);
v_id_4179_ = lean_ctor_get(v_b_4141_, 1);
lean_inc(v_id_4179_);
v_d_4180_ = lean_ctor_get(v_b_4141_, 2);
lean_inc(v_d_4180_);
lean_dec_ref_known(v_b_4141_, 3);
v___x_4181_ = lean_nat_dec_eq(v_id_4177_, v_id_4179_);
lean_dec(v_id_4179_);
lean_dec(v_id_4177_);
if (v___x_4181_ == 0)
{
lean_object* v___x_4182_; lean_object* v___x_4183_; 
lean_dec(v_d_4180_);
lean_dec(v_d_4178_);
lean_dec_ref(v_inst_4139_);
lean_dec_ref(v_inst_4138_);
v___x_4182_ = lean_box(v___x_4181_);
v___x_4183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4183_, 0, v___x_4182_);
lean_ctor_set(v___x_4183_, 1, v_a_4142_);
return v___x_4183_;
}
else
{
lean_object* v___x_4184_; 
v___x_4184_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4138_, v_inst_4139_, v_d_4178_, v_d_4180_, v_a_4142_);
return v___x_4184_;
}
}
else
{
lean_dec_ref_known(v_a_4140_, 3);
lean_dec(v_b_4141_);
lean_dec_ref(v_inst_4139_);
lean_dec_ref(v_inst_4138_);
v___y_4144_ = v_a_4142_;
goto v___jp_4143_;
}
}
case 4:
{
if (lean_obj_tag(v_b_4141_) == 4)
{
lean_object* v_d_4185_; lean_object* v_d_4186_; lean_object* v___x_4187_; 
v_d_4185_ = lean_ctor_get(v_a_4140_, 1);
lean_inc(v_d_4185_);
lean_dec_ref_known(v_a_4140_, 2);
v_d_4186_ = lean_ctor_get(v_b_4141_, 1);
lean_inc(v_d_4186_);
lean_dec_ref_known(v_b_4141_, 2);
v___x_4187_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4138_, v_inst_4139_, v_d_4185_, v_d_4186_, v_a_4142_);
return v___x_4187_;
}
else
{
lean_dec_ref_known(v_a_4140_, 2);
lean_dec(v_b_4141_);
lean_dec_ref(v_inst_4139_);
lean_dec_ref(v_inst_4138_);
v___y_4144_ = v_a_4142_;
goto v___jp_4143_;
}
}
case 5:
{
if (lean_obj_tag(v_b_4141_) == 5)
{
lean_object* v_d_4188_; lean_object* v_d_4189_; lean_object* v___x_4190_; 
v_d_4188_ = lean_ctor_get(v_a_4140_, 1);
lean_inc(v_d_4188_);
lean_dec_ref_known(v_a_4140_, 2);
v_d_4189_ = lean_ctor_get(v_b_4141_, 1);
lean_inc(v_d_4189_);
lean_dec_ref_known(v_b_4141_, 2);
v___x_4190_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4138_, v_inst_4139_, v_d_4188_, v_d_4189_, v_a_4142_);
return v___x_4190_;
}
else
{
lean_dec_ref_known(v_a_4140_, 2);
lean_dec(v_b_4141_);
lean_dec_ref(v_inst_4139_);
lean_dec_ref(v_inst_4138_);
v___y_4144_ = v_a_4142_;
goto v___jp_4143_;
}
}
case 6:
{
if (lean_obj_tag(v_b_4141_) == 6)
{
lean_object* v_n_4191_; uint8_t v_isCumulative_4192_; lean_object* v_d_4193_; lean_object* v_n_4194_; uint8_t v_isCumulative_4195_; lean_object* v_d_4196_; uint8_t v___x_4197_; 
v_n_4191_ = lean_ctor_get(v_a_4140_, 1);
lean_inc(v_n_4191_);
v_isCumulative_4192_ = lean_ctor_get_uint8(v_a_4140_, sizeof(void*)*3 + 8);
v_d_4193_ = lean_ctor_get(v_a_4140_, 2);
lean_inc(v_d_4193_);
lean_dec_ref_known(v_a_4140_, 3);
v_n_4194_ = lean_ctor_get(v_b_4141_, 1);
lean_inc(v_n_4194_);
v_isCumulative_4195_ = lean_ctor_get_uint8(v_b_4141_, sizeof(void*)*3 + 8);
v_d_4196_ = lean_ctor_get(v_b_4141_, 2);
lean_inc(v_d_4196_);
lean_dec_ref_known(v_b_4141_, 3);
v___x_4197_ = lean_nat_dec_eq(v_n_4191_, v_n_4194_);
lean_dec(v_n_4194_);
lean_dec(v_n_4191_);
if (v___x_4197_ == 0)
{
lean_dec(v_d_4196_);
lean_dec(v_d_4193_);
lean_dec_ref(v_inst_4139_);
lean_dec_ref(v_inst_4138_);
goto v___jp_4166_;
}
else
{
if (v_isCumulative_4195_ == 0)
{
if (v_isCumulative_4192_ == 0)
{
lean_object* v___x_4198_; 
v___x_4198_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4138_, v_inst_4139_, v_d_4193_, v_d_4196_, v_a_4142_);
return v___x_4198_;
}
else
{
lean_dec(v_d_4196_);
lean_dec(v_d_4193_);
lean_dec_ref(v_inst_4139_);
lean_dec_ref(v_inst_4138_);
goto v___jp_4166_;
}
}
else
{
if (v_isCumulative_4192_ == 0)
{
lean_dec(v_d_4196_);
lean_dec(v_d_4193_);
lean_dec_ref(v_inst_4139_);
lean_dec_ref(v_inst_4138_);
goto v___jp_4166_;
}
else
{
lean_object* v___x_4199_; 
v___x_4199_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4138_, v_inst_4139_, v_d_4193_, v_d_4196_, v_a_4142_);
return v___x_4199_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_4140_, 3);
lean_dec(v_b_4141_);
lean_dec_ref(v_inst_4139_);
lean_dec_ref(v_inst_4138_);
v___y_4144_ = v_a_4142_;
goto v___jp_4143_;
}
}
case 7:
{
if (lean_obj_tag(v_b_4141_) == 7)
{
lean_object* v_d_4200_; lean_object* v_d_4201_; lean_object* v___x_4202_; 
v_d_4200_ = lean_ctor_get(v_a_4140_, 1);
lean_inc(v_d_4200_);
lean_dec_ref_known(v_a_4140_, 2);
v_d_4201_ = lean_ctor_get(v_b_4141_, 1);
lean_inc(v_d_4201_);
lean_dec_ref_known(v_b_4141_, 2);
v___x_4202_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4138_, v_inst_4139_, v_d_4200_, v_d_4201_, v_a_4142_);
return v___x_4202_;
}
else
{
lean_dec_ref_known(v_a_4140_, 2);
lean_dec(v_b_4141_);
lean_dec_ref(v_inst_4139_);
lean_dec_ref(v_inst_4138_);
v___y_4144_ = v_a_4142_;
goto v___jp_4143_;
}
}
case 8:
{
if (lean_obj_tag(v_b_4141_) == 8)
{
uint8_t v_onlyNonCumulative_4203_; 
v_onlyNonCumulative_4203_ = lean_ctor_get_uint8(v_b_4141_, sizeof(void*)*2 + 8);
if (v_onlyNonCumulative_4203_ == 0)
{
uint8_t v_onlyNonCumulative_4204_; 
v_onlyNonCumulative_4204_ = lean_ctor_get_uint8(v_a_4140_, sizeof(void*)*2 + 8);
if (v_onlyNonCumulative_4204_ == 0)
{
lean_object* v_d_4205_; lean_object* v_d_4206_; lean_object* v___x_4207_; 
v_d_4205_ = lean_ctor_get(v_a_4140_, 1);
lean_inc(v_d_4205_);
lean_dec_ref_known(v_a_4140_, 2);
v_d_4206_ = lean_ctor_get(v_b_4141_, 1);
lean_inc(v_d_4206_);
lean_dec_ref_known(v_b_4141_, 2);
v___x_4207_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4138_, v_inst_4139_, v_d_4205_, v_d_4206_, v_a_4142_);
return v___x_4207_;
}
else
{
lean_object* v___x_4208_; lean_object* v___x_4209_; 
lean_dec_ref_known(v_b_4141_, 2);
lean_dec_ref_known(v_a_4140_, 2);
lean_dec_ref(v_inst_4139_);
lean_dec_ref(v_inst_4138_);
v___x_4208_ = lean_box(v_onlyNonCumulative_4203_);
v___x_4209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4209_, 0, v___x_4208_);
lean_ctor_set(v___x_4209_, 1, v_a_4142_);
return v___x_4209_;
}
}
else
{
uint8_t v_onlyNonCumulative_4210_; 
v_onlyNonCumulative_4210_ = lean_ctor_get_uint8(v_a_4140_, sizeof(void*)*2 + 8);
if (v_onlyNonCumulative_4210_ == 0)
{
lean_object* v___x_4211_; lean_object* v___x_4212_; 
lean_dec_ref_known(v_b_4141_, 2);
lean_dec_ref_known(v_a_4140_, 2);
lean_dec_ref(v_inst_4139_);
lean_dec_ref(v_inst_4138_);
v___x_4211_ = lean_box(v_onlyNonCumulative_4210_);
v___x_4212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4212_, 0, v___x_4211_);
lean_ctor_set(v___x_4212_, 1, v_a_4142_);
return v___x_4212_;
}
else
{
lean_object* v_d_4213_; lean_object* v_d_4214_; lean_object* v___x_4215_; 
v_d_4213_ = lean_ctor_get(v_a_4140_, 1);
lean_inc(v_d_4213_);
lean_dec_ref_known(v_a_4140_, 2);
v_d_4214_ = lean_ctor_get(v_b_4141_, 1);
lean_inc(v_d_4214_);
lean_dec_ref_known(v_b_4141_, 2);
v___x_4215_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4138_, v_inst_4139_, v_d_4213_, v_d_4214_, v_a_4142_);
return v___x_4215_;
}
}
}
else
{
lean_dec_ref_known(v_a_4140_, 2);
lean_dec(v_b_4141_);
lean_dec_ref(v_inst_4139_);
lean_dec_ref(v_inst_4138_);
v___y_4144_ = v_a_4142_;
goto v___jp_4143_;
}
}
case 9:
{
if (lean_obj_tag(v_b_4141_) == 9)
{
lean_object* v_d_4216_; lean_object* v_d_4217_; lean_object* v___x_4218_; 
v_d_4216_ = lean_ctor_get(v_a_4140_, 1);
lean_inc(v_d_4216_);
lean_dec_ref_known(v_a_4140_, 2);
v_d_4217_ = lean_ctor_get(v_b_4141_, 1);
lean_inc(v_d_4217_);
lean_dec_ref_known(v_b_4141_, 2);
v___x_4218_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4138_, v_inst_4139_, v_d_4216_, v_d_4217_, v_a_4142_);
return v___x_4218_;
}
else
{
lean_dec_ref_known(v_a_4140_, 2);
lean_dec(v_b_4141_);
lean_dec_ref(v_inst_4139_);
lean_dec_ref(v_inst_4138_);
v___y_4144_ = v_a_4142_;
goto v___jp_4143_;
}
}
case 10:
{
if (lean_obj_tag(v_b_4141_) == 10)
{
lean_object* v_d_4219_; lean_object* v_d_4220_; lean_object* v___x_4221_; 
v_d_4219_ = lean_ctor_get(v_a_4140_, 1);
lean_inc(v_d_4219_);
lean_dec_ref_known(v_a_4140_, 2);
v_d_4220_ = lean_ctor_get(v_b_4141_, 1);
lean_inc(v_d_4220_);
lean_dec_ref_known(v_b_4141_, 2);
v___x_4221_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4138_, v_inst_4139_, v_d_4219_, v_d_4220_, v_a_4142_);
return v___x_4221_;
}
else
{
lean_dec_ref_known(v_a_4140_, 2);
lean_dec(v_b_4141_);
lean_dec_ref(v_inst_4139_);
lean_dec_ref(v_inst_4138_);
v___y_4144_ = v_a_4142_;
goto v___jp_4143_;
}
}
case 11:
{
if (lean_obj_tag(v_b_4141_) == 11)
{
lean_object* v_d_4222_; lean_object* v_d_4223_; lean_object* v___x_4224_; 
v_d_4222_ = lean_ctor_get(v_a_4140_, 1);
lean_inc(v_d_4222_);
lean_dec_ref_known(v_a_4140_, 2);
v_d_4223_ = lean_ctor_get(v_b_4141_, 1);
lean_inc(v_d_4223_);
lean_dec_ref_known(v_b_4141_, 2);
v___x_4224_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4138_, v_inst_4139_, v_d_4222_, v_d_4223_, v_a_4142_);
return v___x_4224_;
}
else
{
lean_dec_ref_known(v_a_4140_, 2);
lean_dec(v_b_4141_);
lean_dec_ref(v_inst_4139_);
lean_dec_ref(v_inst_4138_);
v___y_4144_ = v_a_4142_;
goto v___jp_4143_;
}
}
case 12:
{
if (lean_obj_tag(v_b_4141_) == 12)
{
lean_object* v_p_4225_; lean_object* v_p_4226_; lean_object* v_d_4227_; lean_object* v_d_4228_; lean_object* v_id_4229_; lean_object* v_id_4230_; lean_object* v___x_4232_; uint8_t v_isShared_4233_; uint8_t v_isSharedCheck_4240_; 
v_p_4225_ = lean_ctor_get(v_a_4140_, 1);
lean_inc_ref(v_p_4225_);
v_p_4226_ = lean_ctor_get(v_b_4141_, 1);
lean_inc_ref(v_p_4226_);
v_d_4227_ = lean_ctor_get(v_a_4140_, 2);
lean_inc(v_d_4227_);
lean_dec_ref_known(v_a_4140_, 3);
v_d_4228_ = lean_ctor_get(v_b_4141_, 2);
lean_inc(v_d_4228_);
lean_dec_ref_known(v_b_4141_, 3);
v_id_4229_ = lean_ctor_get(v_p_4225_, 1);
lean_inc(v_id_4229_);
lean_dec_ref(v_p_4225_);
v_id_4230_ = lean_ctor_get(v_p_4226_, 1);
v_isSharedCheck_4240_ = !lean_is_exclusive(v_p_4226_);
if (v_isSharedCheck_4240_ == 0)
{
lean_object* v_unused_4241_; 
v_unused_4241_ = lean_ctor_get(v_p_4226_, 0);
lean_dec(v_unused_4241_);
v___x_4232_ = v_p_4226_;
v_isShared_4233_ = v_isSharedCheck_4240_;
goto v_resetjp_4231_;
}
else
{
lean_inc(v_id_4230_);
lean_dec(v_p_4226_);
v___x_4232_ = lean_box(0);
v_isShared_4233_ = v_isSharedCheck_4240_;
goto v_resetjp_4231_;
}
v_resetjp_4231_:
{
uint8_t v___x_4234_; 
v___x_4234_ = lean_name_eq(v_id_4229_, v_id_4230_);
lean_dec(v_id_4230_);
lean_dec(v_id_4229_);
if (v___x_4234_ == 0)
{
lean_object* v___x_4235_; lean_object* v___x_4237_; 
lean_dec(v_d_4228_);
lean_dec(v_d_4227_);
lean_dec_ref(v_inst_4139_);
lean_dec_ref(v_inst_4138_);
v___x_4235_ = lean_box(v___x_4234_);
if (v_isShared_4233_ == 0)
{
lean_ctor_set(v___x_4232_, 1, v_a_4142_);
lean_ctor_set(v___x_4232_, 0, v___x_4235_);
v___x_4237_ = v___x_4232_;
goto v_reusejp_4236_;
}
else
{
lean_object* v_reuseFailAlloc_4238_; 
v_reuseFailAlloc_4238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4238_, 0, v___x_4235_);
lean_ctor_set(v_reuseFailAlloc_4238_, 1, v_a_4142_);
v___x_4237_ = v_reuseFailAlloc_4238_;
goto v_reusejp_4236_;
}
v_reusejp_4236_:
{
return v___x_4237_;
}
}
else
{
lean_object* v___x_4239_; 
lean_del_object(v___x_4232_);
v___x_4239_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4138_, v_inst_4139_, v_d_4227_, v_d_4228_, v_a_4142_);
return v___x_4239_;
}
}
}
else
{
lean_dec_ref_known(v_a_4140_, 3);
lean_dec(v_b_4141_);
lean_dec_ref(v_inst_4139_);
lean_dec_ref(v_inst_4138_);
v___y_4144_ = v_a_4142_;
goto v___jp_4143_;
}
}
case 13:
{
if (lean_obj_tag(v_b_4141_) == 13)
{
lean_object* v_cost_4242_; lean_object* v_d_4243_; lean_object* v_cost_4244_; lean_object* v_d_4245_; lean_object* v___x_4246_; uint8_t v___x_4247_; 
v_cost_4242_ = lean_ctor_get(v_a_4140_, 1);
lean_inc(v_cost_4242_);
v_d_4243_ = lean_ctor_get(v_a_4140_, 2);
lean_inc(v_d_4243_);
lean_dec_ref_known(v_a_4140_, 3);
v_cost_4244_ = lean_ctor_get(v_b_4141_, 1);
lean_inc(v_cost_4244_);
v_d_4245_ = lean_ctor_get(v_b_4141_, 2);
lean_inc(v_d_4245_);
lean_dec_ref_known(v_b_4141_, 3);
lean_inc_ref(v_inst_4138_);
v___x_4246_ = lean_apply_2(v_inst_4138_, v_cost_4242_, v_cost_4244_);
v___x_4247_ = lean_unbox(v___x_4246_);
if (v___x_4247_ == 0)
{
lean_object* v___x_4248_; 
lean_dec(v_d_4245_);
lean_dec(v_d_4243_);
lean_dec_ref(v_inst_4139_);
lean_dec_ref(v_inst_4138_);
v___x_4248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4248_, 0, v___x_4246_);
lean_ctor_set(v___x_4248_, 1, v_a_4142_);
return v___x_4248_;
}
else
{
lean_object* v___x_4249_; 
v___x_4249_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4138_, v_inst_4139_, v_d_4243_, v_d_4245_, v_a_4142_);
return v___x_4249_;
}
}
else
{
lean_dec_ref_known(v_a_4140_, 3);
lean_dec(v_b_4141_);
lean_dec_ref(v_inst_4139_);
lean_dec_ref(v_inst_4138_);
v___y_4144_ = v_a_4142_;
goto v___jp_4143_;
}
}
case 14:
{
if (lean_obj_tag(v_b_4141_) == 14)
{
lean_object* v_a_4250_; lean_object* v_b_4251_; lean_object* v_a_4252_; lean_object* v_b_4253_; 
v_a_4250_ = lean_ctor_get(v_a_4140_, 1);
lean_inc(v_a_4250_);
v_b_4251_ = lean_ctor_get(v_a_4140_, 2);
lean_inc(v_b_4251_);
lean_dec_ref_known(v_a_4140_, 3);
v_a_4252_ = lean_ctor_get(v_b_4141_, 1);
lean_inc(v_a_4252_);
v_b_4253_ = lean_ctor_get(v_b_4141_, 2);
lean_inc(v_b_4253_);
lean_dec_ref_known(v_b_4141_, 3);
v_da1_4149_ = v_a_4250_;
v_da2_4150_ = v_b_4251_;
v_db1_4151_ = v_a_4252_;
v_db2_4152_ = v_b_4253_;
v___y_4153_ = v_a_4142_;
goto v___jp_4148_;
}
else
{
lean_dec_ref_known(v_a_4140_, 3);
lean_dec(v_b_4141_);
lean_dec_ref(v_inst_4139_);
lean_dec_ref(v_inst_4138_);
v___y_4144_ = v_a_4142_;
goto v___jp_4143_;
}
}
default: 
{
if (lean_obj_tag(v_b_4141_) == 15)
{
lean_object* v_a_4254_; lean_object* v_b_4255_; lean_object* v_a_4256_; lean_object* v_b_4257_; 
v_a_4254_ = lean_ctor_get(v_a_4140_, 1);
lean_inc(v_a_4254_);
v_b_4255_ = lean_ctor_get(v_a_4140_, 2);
lean_inc(v_b_4255_);
lean_dec_ref_known(v_a_4140_, 3);
v_a_4256_ = lean_ctor_get(v_b_4141_, 1);
lean_inc(v_a_4256_);
v_b_4257_ = lean_ctor_get(v_b_4141_, 2);
lean_inc(v_b_4257_);
lean_dec_ref_known(v_b_4141_, 3);
v_da1_4149_ = v_a_4254_;
v_da2_4150_ = v_b_4255_;
v_db1_4151_ = v_a_4256_;
v_db2_4152_ = v_b_4257_;
v___y_4153_ = v_a_4142_;
goto v___jp_4148_;
}
else
{
lean_dec_ref_known(v_a_4140_, 3);
lean_dec(v_b_4141_);
lean_dec_ref(v_inst_4139_);
lean_dec_ref(v_inst_4138_);
v___y_4144_ = v_a_4142_;
goto v___jp_4143_;
}
}
}
v___jp_4143_:
{
uint8_t v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; 
v___x_4145_ = 0;
v___x_4146_ = lean_box(v___x_4145_);
v___x_4147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4147_, 0, v___x_4146_);
lean_ctor_set(v___x_4147_, 1, v___y_4144_);
return v___x_4147_;
}
v___jp_4148_:
{
lean_object* v___x_4154_; lean_object* v_fst_4155_; uint8_t v___x_4156_; 
lean_inc_ref(v_inst_4139_);
lean_inc_ref(v_inst_4138_);
v___x_4154_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4138_, v_inst_4139_, v_da1_4149_, v_db1_4151_, v___y_4153_);
v_fst_4155_ = lean_ctor_get(v___x_4154_, 0);
v___x_4156_ = lean_unbox(v_fst_4155_);
if (v___x_4156_ == 0)
{
lean_dec(v_db2_4152_);
lean_dec(v_da2_4150_);
lean_dec_ref(v_inst_4139_);
lean_dec_ref(v_inst_4138_);
return v___x_4154_;
}
else
{
lean_object* v_snd_4157_; lean_object* v___x_4158_; 
v_snd_4157_ = lean_ctor_get(v___x_4154_, 1);
lean_inc(v_snd_4157_);
lean_dec_ref(v___x_4154_);
v___x_4158_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4138_, v_inst_4139_, v_da2_4150_, v_db2_4152_, v_snd_4157_);
return v___x_4158_;
}
}
v___jp_4159_:
{
uint8_t v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; 
v___x_4163_ = lean_string_dec_eq(v_sa_4160_, v_sb_4161_);
lean_dec_ref(v_sb_4161_);
lean_dec_ref(v_sa_4160_);
v___x_4164_ = lean_box(v___x_4163_);
v___x_4165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4165_, 0, v___x_4164_);
lean_ctor_set(v___x_4165_, 1, v___y_4162_);
return v___x_4165_;
}
v___jp_4166_:
{
uint8_t v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; 
v___x_4167_ = 0;
v___x_4168_ = lean_box(v___x_4167_);
v___x_4169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4169_, 0, v___x_4168_);
lean_ctor_set(v___x_4169_, 1, v_a_4142_);
return v___x_4169_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(lean_object* v_inst_4258_, lean_object* v_inst_4259_, lean_object* v_a_4260_, lean_object* v_b_4261_, lean_object* v_a_4262_){
_start:
{
lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v_cacheKey_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; 
lean_inc(v_a_4260_);
v___x_4263_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_a_4260_);
lean_inc(v_b_4261_);
v___x_4264_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_b_4261_);
v_cacheKey_4265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_cacheKey_4265_, 0, v___x_4263_);
lean_ctor_set(v_cacheKey_4265_, 1, v___x_4264_);
lean_inc_ref(v_inst_4258_);
v___x_4266_ = lean_alloc_closure((void*)(l_Lean_Fmt_instBEqBEqCacheKey_beq___boxed), 4, 2);
lean_closure_set(v___x_4266_, 0, lean_box(0));
lean_closure_set(v___x_4266_, 1, v_inst_4258_);
lean_inc_ref(v_inst_4259_);
v___x_4267_ = lean_alloc_closure((void*)(l_Lean_Fmt_instHashableBEqCacheKey_hash___boxed), 3, 2);
lean_closure_set(v___x_4267_, 0, lean_box(0));
lean_closure_set(v___x_4267_, 1, v_inst_4259_);
lean_inc_ref(v_cacheKey_4265_);
lean_inc_ref(v___x_4267_);
lean_inc_ref(v___x_4266_);
v___x_4268_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_4266_, v___x_4267_, v_a_4262_, v_cacheKey_4265_);
if (lean_obj_tag(v___x_4268_) == 1)
{
lean_object* v_val_4269_; lean_object* v___x_4270_; 
lean_dec_ref(v___x_4267_);
lean_dec_ref(v___x_4266_);
lean_dec_ref_known(v_cacheKey_4265_, 2);
lean_dec(v_b_4261_);
lean_dec(v_a_4260_);
lean_dec_ref(v_inst_4259_);
lean_dec_ref(v_inst_4258_);
v_val_4269_ = lean_ctor_get(v___x_4268_, 0);
lean_inc(v_val_4269_);
lean_dec_ref_known(v___x_4268_, 1);
v___x_4270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4270_, 0, v_val_4269_);
lean_ctor_set(v___x_4270_, 1, v_a_4262_);
return v___x_4270_;
}
else
{
lean_object* v___x_4271_; lean_object* v_fst_4272_; lean_object* v_snd_4273_; lean_object* v___x_4275_; uint8_t v_isShared_4276_; uint8_t v_isSharedCheck_4281_; 
lean_dec(v___x_4268_);
v___x_4271_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_go___redArg(v_inst_4258_, v_inst_4259_, v_a_4260_, v_b_4261_, v_a_4262_);
v_fst_4272_ = lean_ctor_get(v___x_4271_, 0);
v_snd_4273_ = lean_ctor_get(v___x_4271_, 1);
v_isSharedCheck_4281_ = !lean_is_exclusive(v___x_4271_);
if (v_isSharedCheck_4281_ == 0)
{
v___x_4275_ = v___x_4271_;
v_isShared_4276_ = v_isSharedCheck_4281_;
goto v_resetjp_4274_;
}
else
{
lean_inc(v_snd_4273_);
lean_inc(v_fst_4272_);
lean_dec(v___x_4271_);
v___x_4275_ = lean_box(0);
v_isShared_4276_ = v_isSharedCheck_4281_;
goto v_resetjp_4274_;
}
v_resetjp_4274_:
{
lean_object* v___x_4277_; lean_object* v___x_4279_; 
lean_inc(v_fst_4272_);
v___x_4277_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_4266_, v___x_4267_, v_snd_4273_, v_cacheKey_4265_, v_fst_4272_);
if (v_isShared_4276_ == 0)
{
lean_ctor_set(v___x_4275_, 1, v___x_4277_);
v___x_4279_ = v___x_4275_;
goto v_reusejp_4278_;
}
else
{
lean_object* v_reuseFailAlloc_4280_; 
v_reuseFailAlloc_4280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4280_, 0, v_fst_4272_);
lean_ctor_set(v_reuseFailAlloc_4280_, 1, v___x_4277_);
v___x_4279_ = v_reuseFailAlloc_4280_;
goto v_reusejp_4278_;
}
v_reusejp_4278_:
{
return v___x_4279_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized(lean_object* v_00_u03c4_4282_, lean_object* v_inst_4283_, lean_object* v_inst_4284_, lean_object* v_a_4285_, lean_object* v_b_4286_, lean_object* v_a_4287_){
_start:
{
lean_object* v___x_4288_; 
v___x_4288_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4283_, v_inst_4284_, v_a_4285_, v_b_4286_, v_a_4287_);
return v___x_4288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_go(lean_object* v_00_u03c4_4289_, lean_object* v_inst_4290_, lean_object* v_inst_4291_, lean_object* v_a_4292_, lean_object* v_b_4293_, lean_object* v_a_4294_){
_start:
{
lean_object* v___x_4295_; 
v___x_4295_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_go___redArg(v_inst_4290_, v_inst_4291_, v_a_4292_, v_b_4293_, v_a_4294_);
return v___x_4295_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_beq___redArg___closed__0(void){
_start:
{
lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; 
v___x_4296_ = lean_box(0);
v___x_4297_ = lean_unsigned_to_nat(16u);
v___x_4298_ = lean_mk_array(v___x_4297_, v___x_4296_);
return v___x_4298_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_beq___redArg___closed__1(void){
_start:
{
lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; 
v___x_4299_ = lean_obj_once(&l_Lean_Fmt_Doc_beq___redArg___closed__0, &l_Lean_Fmt_Doc_beq___redArg___closed__0_once, _init_l_Lean_Fmt_Doc_beq___redArg___closed__0);
v___x_4300_ = lean_unsigned_to_nat(0u);
v___x_4301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4301_, 0, v___x_4300_);
lean_ctor_set(v___x_4301_, 1, v___x_4299_);
return v___x_4301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_beq___redArg(lean_object* v_inst_4302_, lean_object* v_inst_4303_, lean_object* v_a_4304_, lean_object* v_b_4305_){
_start:
{
lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v_fst_4308_; 
v___x_4306_ = lean_obj_once(&l_Lean_Fmt_Doc_beq___redArg___closed__1, &l_Lean_Fmt_Doc_beq___redArg___closed__1_once, _init_l_Lean_Fmt_Doc_beq___redArg___closed__1);
v___x_4307_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4302_, v_inst_4303_, v_a_4304_, v_b_4305_, v___x_4306_);
v_fst_4308_ = lean_ctor_get(v___x_4307_, 0);
lean_inc(v_fst_4308_);
lean_dec_ref(v___x_4307_);
return v_fst_4308_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_beq(lean_object* v_00_u03c4_4309_, lean_object* v_inst_4310_, lean_object* v_inst_4311_, lean_object* v_a_4312_, lean_object* v_b_4313_){
_start:
{
lean_object* v___x_4314_; uint8_t v___x_4315_; 
v___x_4314_ = l_Lean_Fmt_Doc_beq___redArg(v_inst_4310_, v_inst_4311_, v_a_4312_, v_b_4313_);
v___x_4315_ = lean_unbox(v___x_4314_);
lean_dec(v___x_4314_);
return v___x_4315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_beq___boxed(lean_object* v_00_u03c4_4316_, lean_object* v_inst_4317_, lean_object* v_inst_4318_, lean_object* v_a_4319_, lean_object* v_b_4320_){
_start:
{
uint8_t v_res_4321_; lean_object* v_r_4322_; 
v_res_4321_ = l_Lean_Fmt_Doc_beq(v_00_u03c4_4316_, v_inst_4317_, v_inst_4318_, v_a_4319_, v_b_4320_);
v_r_4322_ = lean_box(v_res_4321_);
return v_r_4322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqDocOfHashable___redArg___lam__0(lean_object* v_inst_4323_, lean_object* v_inst_4324_, lean_object* v_a_4325_, lean_object* v_b_4326_){
_start:
{
lean_object* v___x_4327_; 
v___x_4327_ = l_Lean_Fmt_Doc_beq___redArg(v_inst_4323_, v_inst_4324_, v_a_4325_, v_b_4326_);
return v___x_4327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqDocOfHashable___redArg(lean_object* v_inst_4328_, lean_object* v_inst_4329_){
_start:
{
lean_object* v___f_4330_; 
v___f_4330_ = lean_alloc_closure((void*)(l_Lean_Fmt_instBEqDocOfHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_4330_, 0, v_inst_4328_);
lean_closure_set(v___f_4330_, 1, v_inst_4329_);
return v___f_4330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqDocOfHashable(lean_object* v_00_u03c4_4331_, lean_object* v_inst_4332_, lean_object* v_inst_4333_){
_start:
{
lean_object* v___f_4334_; 
v___f_4334_ = lean_alloc_closure((void*)(l_Lean_Fmt_instBEqDocOfHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_4334_, 0, v_inst_4332_);
lean_closure_set(v___f_4334_, 1, v_inst_4333_);
return v___f_4334_;
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
