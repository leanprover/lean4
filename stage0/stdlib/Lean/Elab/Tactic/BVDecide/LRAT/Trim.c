// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide.LRAT.Trim
// Imports: public import Init.Data.Nat.Fold public import Std.Tactic.BVDecide.LRAT.Actions public import Std.Data.HashMap import Init.Data.Range.Polymorphic import Init.Omega
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
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findInitialId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "LRAT proof doesn't contain a proper first proof step."};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findInitialId___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findInitialId___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findInitialId___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findInitialId___closed__0_value)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findInitialId___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findInitialId___closed__1_value;
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findInitialId(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findInitialId___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findEmptyId_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findEmptyId_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findEmptyId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "LRAT proof doesn't contain the empty clause."};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findEmptyId___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findEmptyId___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findEmptyId___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findEmptyId___closed__0_value)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findEmptyId___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findEmptyId___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findEmptyId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findEmptyId___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findEmptyId_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findEmptyId_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1___redArg(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__2(lean_object*, size_t, size_t, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_byte_array_push(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__1___redArg(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__0;
lean_object* lean_int_neg(lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__3;
lean_object* lean_mk_empty_byte_array(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_getInitialId(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_getInitialId___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_getEmptyId(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_getEmptyId___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_M_idIndex(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_M_idIndex___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_UInt64_ofNat___boxed(lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_getProofStep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_ofNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_getProofStep___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_getProofStep___closed__0_value;
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_getProofStep___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_getProofStep___closed__1;
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_getProofStep(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_getProofStep___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_byte_array_size(lean_object*);
extern uint8_t l_instInhabitedUInt8;
lean_object* l_outOfBounds___redArg(lean_object*);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_isUsed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_isUsed___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_byte_array_set(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_markUsed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_markUsed___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_registerIdMap(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_registerIdMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Int_instInhabited;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_updateLastUse___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_updateLastUse___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_updateLastUse(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_updateLastUse___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapIdent(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapIdent___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__0 = (const lean_object*)&l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__0_value;
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__1 = (const lean_object*)&l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__1_value;
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__2 = (const lean_object*)&l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__2_value;
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__3 = (const lean_object*)&l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__3_value;
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__4 = (const lean_object*)&l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__4_value;
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__5 = (const lean_object*)&l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__5_value;
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__6 = (const lean_object*)&l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__6_value;
lean_object* l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__7;
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Elab.Tactic.BVDecide.LRAT.Trim"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "Lean.Elab.Tactic.BVDecide.LRAT.trim.M.mapStep"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__2_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__3___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Array_back___redArg(lean_object*);
lean_object* lean_array_pop(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__0_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__0;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__2_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__3_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__4;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findInitialId(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findInitialId___closed__1));
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_array_fget_borrowed(x_1, x_2);
if (lean_obj_tag(x_6) == 3)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_2, x_7);
lean_dec(x_2);
x_2 = x_8;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findInitialId___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findInitialId(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findEmptyId_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 1)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
lean_dec(x_2);
x_8 = lean_array_fget_borrowed(x_1, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
else
{
x_2 = x_7;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findEmptyId_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findEmptyId_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findEmptyId(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_array_get_size(x_1);
x_3 = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findEmptyId_spec__0___redArg(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findEmptyId___closed__1));
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findEmptyId___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findEmptyId(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findEmptyId_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findEmptyId_spec__0___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findEmptyId_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findEmptyId_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_nat_dec_eq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_nat_dec_eq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__2___redArg(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = lean_nat_dec_eq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__2___redArg(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = lean_uint64_of_nat(x_4);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget_borrowed(x_1, x_18);
lean_inc(x_19);
lean_ctor_set(x_2, 2, x_19);
x_20 = lean_array_uset(x_1, x_18, x_2);
x_1 = x_20;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_25 = lean_array_get_size(x_1);
x_26 = lean_uint64_of_nat(x_22);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_25);
x_35 = 1;
x_36 = lean_usize_sub(x_34, x_35);
x_37 = lean_usize_land(x_33, x_36);
x_38 = lean_array_uget_borrowed(x_1, x_37);
lean_inc(x_38);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_23);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_array_uset(x_1, x_37, x_39);
x_1 = x_40;
x_2 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1_spec__2_spec__5___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1_spec__2___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; uint8_t x_21; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_uint64_of_nat(x_2);
x_9 = 32;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = 16;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = lean_uint64_to_usize(x_14);
x_16 = lean_usize_of_nat(x_7);
x_17 = 1;
x_18 = lean_usize_sub(x_16, x_17);
x_19 = lean_usize_land(x_15, x_18);
x_20 = lean_array_uget_borrowed(x_6, x_19);
x_21 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__0___redArg(x_2, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_5, x_22);
lean_dec(x_5);
lean_inc(x_20);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 2, x_20);
x_25 = lean_array_uset(x_6, x_19, x_24);
x_26 = lean_unsigned_to_nat(4u);
x_27 = lean_nat_mul(x_23, x_26);
x_28 = lean_unsigned_to_nat(3u);
x_29 = lean_nat_div(x_27, x_28);
lean_dec(x_27);
x_30 = lean_array_get_size(x_25);
x_31 = lean_nat_dec_le(x_29, x_30);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1___redArg(x_25);
lean_ctor_set(x_1, 1, x_32);
lean_ctor_set(x_1, 0, x_23);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_25);
lean_ctor_set(x_1, 0, x_23);
return x_1;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_inc(x_20);
x_33 = lean_box(0);
x_34 = lean_array_uset(x_6, x_19, x_33);
x_35 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__2___redArg(x_2, x_3, x_20);
x_36 = lean_array_uset(x_34, x_19, x_35);
lean_ctor_set(x_1, 1, x_36);
return x_1;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; size_t x_47; size_t x_48; size_t x_49; size_t x_50; size_t x_51; lean_object* x_52; uint8_t x_53; 
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_1);
x_39 = lean_array_get_size(x_38);
x_40 = lean_uint64_of_nat(x_2);
x_41 = 32;
x_42 = lean_uint64_shift_right(x_40, x_41);
x_43 = lean_uint64_xor(x_40, x_42);
x_44 = 16;
x_45 = lean_uint64_shift_right(x_43, x_44);
x_46 = lean_uint64_xor(x_43, x_45);
x_47 = lean_uint64_to_usize(x_46);
x_48 = lean_usize_of_nat(x_39);
x_49 = 1;
x_50 = lean_usize_sub(x_48, x_49);
x_51 = lean_usize_land(x_47, x_50);
x_52 = lean_array_uget_borrowed(x_38, x_51);
x_53 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__0___redArg(x_2, x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_add(x_37, x_54);
lean_dec(x_37);
lean_inc(x_52);
x_56 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_56, 0, x_2);
lean_ctor_set(x_56, 1, x_3);
lean_ctor_set(x_56, 2, x_52);
x_57 = lean_array_uset(x_38, x_51, x_56);
x_58 = lean_unsigned_to_nat(4u);
x_59 = lean_nat_mul(x_55, x_58);
x_60 = lean_unsigned_to_nat(3u);
x_61 = lean_nat_div(x_59, x_60);
lean_dec(x_59);
x_62 = lean_array_get_size(x_57);
x_63 = lean_nat_dec_le(x_61, x_62);
lean_dec(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1___redArg(x_57);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_55);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_55);
lean_ctor_set(x_66, 1, x_57);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_inc(x_52);
x_67 = lean_box(0);
x_68 = lean_array_uset(x_38, x_51, x_67);
x_69 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__2___redArg(x_2, x_3, x_52);
x_70 = lean_array_uset(x_68, x_51, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_37);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_array_uget_borrowed(x_1, x_2);
if (lean_obj_tag(x_11) == 3)
{
x_5 = x_4;
goto block_9;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_11);
lean_inc(x_12);
x_13 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0___redArg(x_4, x_12, x_11);
x_5 = x_13;
goto block_9;
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__2(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 1)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_1, x_5);
lean_dec(x_1);
x_7 = 0;
x_8 = lean_byte_array_push(x_2, x_7);
x_1 = x_6;
x_2 = x_8;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__0, &l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__0);
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__2, &l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__2);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findInitialId(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec_ref(x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec_ref(x_4);
x_9 = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findEmptyId(x_1);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_8);
lean_dec_ref(x_2);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_29; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_14 = x_9;
} else {
 lean_dec_ref(x_9);
 x_14 = lean_box(0);
}
x_32 = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__3, &l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__3);
x_33 = lean_array_get_size(x_1);
x_34 = lean_nat_dec_lt(x_3, x_33);
if (x_34 == 0)
{
x_15 = x_32;
x_16 = x_3;
goto block_28;
}
else
{
uint8_t x_35; 
x_35 = lean_nat_dec_le(x_33, x_33);
if (x_35 == 0)
{
if (x_34 == 0)
{
x_15 = x_32;
x_16 = x_3;
goto block_28;
}
else
{
size_t x_36; size_t x_37; lean_object* x_38; 
x_36 = 0;
x_37 = lean_usize_of_nat(x_33);
x_38 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__2(x_1, x_36, x_37, x_32);
x_29 = x_38;
goto block_31;
}
}
else
{
size_t x_39; size_t x_40; lean_object* x_41; 
x_39 = 0;
x_40 = lean_usize_of_nat(x_33);
x_41 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__2(x_1, x_39, x_40, x_32);
x_29 = x_41;
goto block_31;
}
}
block_28:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_17 = lean_mk_empty_byte_array(x_16);
lean_inc(x_16);
x_18 = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__1___redArg(x_16, x_17);
x_19 = lean_nat_add(x_8, x_16);
x_20 = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__1, &l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__1);
x_21 = lean_mk_array(x_19, x_20);
x_22 = lean_mk_array(x_16, x_3);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_8);
lean_ctor_set(x_23, 2, x_13);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_21);
x_25 = lean_apply_2(x_2, x_23, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
if (lean_is_scalar(x_14)) {
 x_27 = lean_alloc_ctor(1, 1, 0);
} else {
 x_27 = x_14;
}
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
block_31:
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_15 = x_29;
x_16 = x_30;
goto block_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__1___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1_spec__2_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1_spec__2_spec__5___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_getInitialId(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_getInitialId___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_getInitialId(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_getEmptyId(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_getEmptyId___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_getEmptyId(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_M_idIndex(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_nat_sub(x_1, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_M_idIndex___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_M_idIndex(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_getProofStep___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_getProofStep(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_getProofStep___closed__0));
x_6 = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_getProofStep___closed__1, &l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_getProofStep___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_getProofStep___closed__1);
x_7 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(x_6, x_5, x_4, x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_getProofStep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_getProofStep(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_isUsed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_nat_sub(x_1, x_10);
x_13 = lean_byte_array_size(x_11);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_12);
x_15 = l_instInhabitedUInt8;
x_16 = lean_box(x_15);
x_17 = l_outOfBounds___redArg(x_16);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
x_4 = x_18;
goto block_9;
}
else
{
uint8_t x_19; 
x_19 = lean_byte_array_fget(x_11, x_12);
lean_dec(x_12);
x_4 = x_19;
goto block_9;
}
block_9:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_5 = 1;
x_6 = lean_uint8_dec_eq(x_4, x_5);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_isUsed___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_isUsed(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_markUsed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_nat_dec_le(x_4, x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_nat_sub(x_1, x_4);
x_11 = lean_box(0);
x_12 = 1;
x_13 = lean_byte_array_set(x_9, x_10, x_12);
lean_dec(x_10);
lean_ctor_set(x_3, 0, x_13);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_3, 1);
x_17 = lean_ctor_get(x_3, 2);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_3);
x_18 = lean_nat_sub(x_1, x_4);
x_19 = lean_box(0);
x_20 = 1;
x_21 = lean_byte_array_set(x_15, x_18, x_20);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_16);
lean_ctor_set(x_22, 2, x_17);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_markUsed___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_markUsed(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_registerIdMap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_nat_sub(x_1, x_6);
x_9 = lean_box(0);
x_10 = lean_array_set(x_7, x_8, x_2);
lean_dec(x_8);
lean_ctor_set(x_4, 1, x_10);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_ctor_get(x_4, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_16 = lean_nat_sub(x_1, x_12);
x_17 = lean_box(0);
x_18 = lean_array_set(x_14, x_16, x_2);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_15);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_registerIdMap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_registerIdMap(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_updateLastUse___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_6);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_7 = x_3;
} else {
 lean_dec_ref(x_3);
 x_7 = lean_box(0);
}
x_8 = l_Int_instInhabited;
x_9 = lean_box(0);
x_15 = lean_array_get_borrowed(x_8, x_6, x_1);
x_16 = lean_nat_to_int(x_2);
x_17 = lean_int_dec_le(x_15, x_16);
if (x_17 == 0)
{
lean_dec(x_16);
lean_inc(x_15);
x_10 = x_15;
goto block_14;
}
else
{
x_10 = x_16;
goto block_14;
}
block_14:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_array_set(x_6, x_1, x_10);
if (lean_is_scalar(x_7)) {
 x_12 = lean_alloc_ctor(0, 3, 0);
} else {
 x_12 = x_7;
}
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_5);
lean_ctor_set(x_12, 2, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_updateLastUse___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_updateLastUse___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_updateLastUse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_7);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 x_8 = x_4;
} else {
 lean_dec_ref(x_4);
 x_8 = lean_box(0);
}
x_9 = l_Int_instInhabited;
x_10 = lean_box(0);
x_16 = lean_array_get_borrowed(x_9, x_7, x_1);
x_17 = lean_nat_to_int(x_2);
x_18 = lean_int_dec_le(x_16, x_17);
if (x_18 == 0)
{
lean_dec(x_17);
lean_inc(x_16);
x_11 = x_16;
goto block_15;
}
else
{
x_11 = x_17;
goto block_15;
}
block_15:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_array_set(x_7, x_1, x_11);
if (lean_is_scalar(x_8)) {
 x_13 = lean_alloc_ctor(0, 3, 0);
} else {
 x_13 = x_8;
}
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_6);
lean_ctor_set(x_13, 2, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_updateLastUse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_updateLastUse(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapIdent(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_nat_sub(x_1, x_4);
lean_dec(x_1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_get(x_8, x_6, x_7);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapIdent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapIdent(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__7(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_4 = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__0));
x_5 = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__1));
x_6 = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__2));
x_7 = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__3));
x_8 = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__4));
x_9 = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__5));
x_10 = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__6));
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_5);
x_12 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
lean_ctor_set(x_12, 2, x_7);
lean_ctor_set(x_12, 3, x_8);
lean_ctor_set(x_12, 4, x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
lean_inc_ref(x_13);
x_14 = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_14, 0, x_13);
lean_inc_ref(x_13);
x_15 = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_15, 0, x_13);
lean_inc_ref(x_13);
x_16 = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(x_16, 0, x_13);
lean_inc_ref(x_13);
x_17 = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(x_17, 0, x_13);
lean_inc_ref(x_13);
x_18 = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(x_18, 0, lean_box(0));
lean_closure_set(x_18, 1, lean_box(0));
lean_closure_set(x_18, 2, x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_14);
lean_inc_ref(x_13);
x_20 = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(x_20, 0, lean_box(0));
lean_closure_set(x_20, 1, lean_box(0));
lean_closure_set(x_20, 2, x_13);
x_21 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_15);
lean_ctor_set(x_21, 3, x_16);
lean_ctor_set(x_21, 4, x_17);
x_22 = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(x_22, 0, lean_box(0));
lean_closure_set(x_22, 1, lean_box(0));
lean_closure_set(x_22, 2, x_13);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_obj_once(&l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__7, &l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__7_once, _init_l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__7);
x_25 = l_instInhabitedOfMonad___redArg(x_23, x_24);
x_26 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_26, 0, x_25);
x_27 = lean_panic_fn(x_26, x_1);
x_28 = lean_apply_2(x_27, x_2, x_3);
return x_28;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_2, x_1);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_19; 
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_array_uget(x_3, x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_uset(x_3, x_2, x_10);
x_19 = lean_nat_dec_lt(x_9, x_8);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_5, 1);
x_21 = lean_nat_sub(x_9, x_8);
lean_dec(x_9);
x_22 = lean_array_get(x_10, x_20, x_21);
lean_dec(x_21);
x_12 = x_22;
x_13 = x_5;
goto block_18;
}
else
{
x_12 = x_9;
x_13 = x_5;
goto block_18;
}
block_18:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_16 = lean_array_uset(x_11, x_2, x_12);
x_2 = x_15;
x_3 = x_16;
x_5 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__0(x_6, x_7, x_3, x_4, x_5);
lean_dec_ref(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_2, x_1);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_34; 
x_8 = lean_array_uget(x_3, x_2);
x_9 = lean_ctor_get(x_8, 0);
x_10 = lean_ctor_get(x_4, 1);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_uset(x_3, x_2, x_11);
x_34 = lean_nat_dec_lt(x_9, x_10);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_5, 1);
x_36 = lean_nat_sub(x_9, x_10);
x_37 = lean_array_get(x_11, x_35, x_36);
lean_dec(x_36);
x_13 = x_37;
x_14 = x_5;
goto block_33;
}
else
{
lean_inc(x_9);
x_13 = x_9;
x_14 = x_5;
goto block_33;
}
block_33:
{
lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_array_size(x_15);
x_17 = 0;
x_18 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__0(x_16, x_17, x_15, x_4, x_14);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_ctor_set(x_18, 1, x_20);
lean_ctor_set(x_18, 0, x_13);
x_22 = 1;
x_23 = lean_usize_add(x_2, x_22);
x_24 = lean_array_uset(x_12, x_2, x_18);
x_2 = x_23;
x_3 = x_24;
x_5 = x_21;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_18);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_13);
lean_ctor_set(x_28, 1, x_26);
x_29 = 1;
x_30 = lean_usize_add(x_2, x_29);
x_31 = lean_array_uset(x_12, x_2, x_28);
x_2 = x_30;
x_3 = x_31;
x_5 = x_27;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__1(x_6, x_7, x_3, x_4, x_5);
lean_dec_ref(x_4);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__2));
x_2 = lean_unsigned_to_nat(15u);
x_3 = lean_unsigned_to_nat(166u);
x_4 = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__1));
x_5 = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_20; uint8_t x_21; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_5);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_6 = x_1;
} else {
 lean_dec_ref(x_1);
 x_6 = lean_box(0);
}
x_20 = lean_ctor_get(x_2, 1);
x_21 = lean_nat_dec_lt(x_4, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_3, 1);
x_23 = lean_nat_sub(x_4, x_20);
lean_dec(x_4);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_array_get(x_24, x_22, x_23);
lean_dec(x_23);
x_7 = x_25;
x_8 = x_3;
goto block_19;
}
else
{
x_7 = x_4;
x_8 = x_3;
goto block_19;
}
block_19:
{
size_t x_9; size_t x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_array_size(x_5);
x_10 = 0;
x_11 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__0(x_9, x_10, x_5, x_2, x_8);
lean_dec_ref(x_2);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
if (lean_is_scalar(x_6)) {
 x_14 = lean_alloc_ctor(0, 2, 0);
} else {
 x_14 = x_6;
}
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
if (lean_is_scalar(x_6)) {
 x_17 = lean_alloc_ctor(0, 2, 0);
} else {
 x_17 = x_6;
}
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
case 1:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_43; uint8_t x_44; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_28);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 x_29 = x_1;
} else {
 lean_dec_ref(x_1);
 x_29 = lean_box(0);
}
x_43 = lean_ctor_get(x_2, 1);
x_44 = lean_nat_dec_lt(x_26, x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_3, 1);
x_46 = lean_nat_sub(x_26, x_43);
lean_dec(x_26);
x_47 = lean_unsigned_to_nat(0u);
x_48 = lean_array_get(x_47, x_45, x_46);
lean_dec(x_46);
x_30 = x_48;
x_31 = x_3;
goto block_42;
}
else
{
x_30 = x_26;
x_31 = x_3;
goto block_42;
}
block_42:
{
size_t x_32; size_t x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_array_size(x_28);
x_33 = 0;
x_34 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__0(x_32, x_33, x_28, x_2, x_31);
lean_dec_ref(x_2);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
if (lean_is_scalar(x_29)) {
 x_37 = lean_alloc_ctor(1, 3, 0);
} else {
 x_37 = x_29;
}
lean_ctor_set(x_37, 0, x_30);
lean_ctor_set(x_37, 1, x_27);
lean_ctor_set(x_37, 2, x_36);
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_34);
if (lean_is_scalar(x_29)) {
 x_40 = lean_alloc_ctor(1, 3, 0);
} else {
 x_40 = x_29;
}
lean_ctor_set(x_40, 0, x_30);
lean_ctor_set(x_40, 1, x_27);
lean_ctor_set(x_40, 2, x_38);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
case 2:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_72; uint8_t x_73; 
x_49 = lean_ctor_get(x_1, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_1, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_51);
x_52 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_52);
x_53 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_53);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 x_54 = x_1;
} else {
 lean_dec_ref(x_1);
 x_54 = lean_box(0);
}
x_72 = lean_ctor_get(x_2, 1);
x_73 = lean_nat_dec_lt(x_49, x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_3, 1);
x_75 = lean_nat_sub(x_49, x_72);
lean_dec(x_49);
x_76 = lean_unsigned_to_nat(0u);
x_77 = lean_array_get(x_76, x_74, x_75);
lean_dec(x_75);
x_55 = x_77;
x_56 = x_3;
goto block_71;
}
else
{
x_55 = x_49;
x_56 = x_3;
goto block_71;
}
block_71:
{
size_t x_57; size_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; size_t x_62; lean_object* x_63; uint8_t x_64; 
x_57 = lean_array_size(x_52);
x_58 = 0;
x_59 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__0(x_57, x_58, x_52, x_2, x_56);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec_ref(x_59);
x_62 = lean_array_size(x_53);
x_63 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__1(x_62, x_58, x_53, x_2, x_61);
lean_dec_ref(x_2);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_63, 0);
if (lean_is_scalar(x_54)) {
 x_66 = lean_alloc_ctor(2, 5, 0);
} else {
 x_66 = x_54;
}
lean_ctor_set(x_66, 0, x_55);
lean_ctor_set(x_66, 1, x_50);
lean_ctor_set(x_66, 2, x_51);
lean_ctor_set(x_66, 3, x_60);
lean_ctor_set(x_66, 4, x_65);
lean_ctor_set(x_63, 0, x_66);
return x_63;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_63, 0);
x_68 = lean_ctor_get(x_63, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_63);
if (lean_is_scalar(x_54)) {
 x_69 = lean_alloc_ctor(2, 5, 0);
} else {
 x_69 = x_54;
}
lean_ctor_set(x_69, 0, x_55);
lean_ctor_set(x_69, 1, x_50);
lean_ctor_set(x_69, 2, x_51);
lean_ctor_set(x_69, 3, x_60);
lean_ctor_set(x_69, 4, x_67);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
}
default: 
{
lean_object* x_78; lean_object* x_79; 
lean_dec_ref(x_1);
x_78 = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__3, &l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__3);
x_79 = l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2(x_78, x_2, x_3);
return x_79;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__3___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_4, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_6, 2);
lean_inc_ref(x_11);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 x_12 = x_6;
} else {
 lean_dec_ref(x_6);
 x_12 = lean_box(0);
}
x_13 = lean_box(0);
x_14 = lean_array_uget_borrowed(x_2, x_4);
x_22 = l_Int_instInhabited;
x_23 = lean_array_get_borrowed(x_22, x_11, x_14);
lean_inc(x_1);
x_24 = lean_nat_to_int(x_1);
x_25 = lean_int_dec_le(x_23, x_24);
if (x_25 == 0)
{
lean_dec(x_24);
lean_inc(x_23);
x_15 = x_23;
goto block_21;
}
else
{
x_15 = x_24;
goto block_21;
}
block_21:
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_16 = lean_array_set(x_11, x_14, x_15);
if (lean_is_scalar(x_12)) {
 x_17 = lean_alloc_ctor(0, 3, 0);
} else {
 x_17 = x_12;
}
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_10);
lean_ctor_set(x_17, 2, x_16);
x_18 = 1;
x_19 = lean_usize_add(x_4, x_18);
x_4 = x_19;
x_5 = x_13;
x_6 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__3___redArg(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_6 = lean_array_uget_borrowed(x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
x_9 = lean_array_push(x_4, x_7);
x_10 = l_Array_append___redArg(x_9, x_8);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_10;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__5(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_3, x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_6, 2);
lean_inc_ref(x_10);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 x_11 = x_6;
} else {
 lean_dec_ref(x_6);
 x_11 = lean_box(0);
}
x_12 = lean_array_uget_borrowed(x_2, x_3);
x_13 = l_Int_instInhabited;
x_14 = lean_box(0);
x_22 = lean_array_get_borrowed(x_13, x_10, x_12);
lean_inc(x_1);
x_23 = lean_nat_to_int(x_1);
x_24 = lean_int_dec_le(x_22, x_23);
if (x_24 == 0)
{
lean_dec(x_23);
lean_inc(x_22);
x_15 = x_22;
goto block_21;
}
else
{
x_15 = x_23;
goto block_21;
}
block_21:
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_16 = lean_array_set(x_10, x_12, x_15);
if (lean_is_scalar(x_11)) {
 x_17 = lean_alloc_ctor(0, 3, 0);
} else {
 x_17 = x_11;
}
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_9);
lean_ctor_set(x_17, 2, x_16);
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_3 = x_19;
x_5 = x_14;
x_6 = x_17;
goto _start;
}
}
else
{
lean_object* x_25; 
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_6);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2___redArg(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_3, x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_7, 2);
lean_inc_ref(x_11);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 x_12 = x_7;
} else {
 lean_dec_ref(x_7);
 x_12 = lean_box(0);
}
x_13 = lean_array_uget_borrowed(x_2, x_3);
x_14 = l_Int_instInhabited;
x_15 = lean_box(0);
x_23 = lean_array_get_borrowed(x_14, x_11, x_13);
lean_inc(x_1);
x_24 = lean_nat_to_int(x_1);
x_25 = lean_int_dec_le(x_23, x_24);
if (x_25 == 0)
{
lean_dec(x_24);
lean_inc(x_23);
x_16 = x_23;
goto block_22;
}
else
{
x_16 = x_24;
goto block_22;
}
block_22:
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_17 = lean_array_set(x_11, x_13, x_16);
if (lean_is_scalar(x_12)) {
 x_18 = lean_alloc_ctor(0, 3, 0);
} else {
 x_18 = x_12;
}
lean_ctor_set(x_18, 0, x_9);
lean_ctor_set(x_18, 1, x_10);
lean_ctor_set(x_18, 2, x_17);
x_19 = 1;
x_20 = lean_usize_add(x_3, x_19);
x_21 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2___redArg(x_1, x_2, x_20, x_4, x_15, x_18);
return x_21;
}
}
else
{
lean_object* x_26; 
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_7);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__4(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_nat_dec_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_uint64_of_nat(x_2);
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget_borrowed(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1_spec__1___redArg(x_2, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_19; lean_object* x_20; lean_object* x_23; lean_object* x_24; lean_object* x_28; lean_object* x_29; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_44; lean_object* x_45; lean_object* x_46; size_t x_47; lean_object* x_48; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_79; uint8_t x_119; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_3, 2);
x_12 = l_Array_back___redArg(x_1);
x_13 = lean_array_pop(x_1);
x_134 = lean_nat_sub(x_12, x_8);
x_135 = lean_byte_array_size(x_9);
x_136 = lean_nat_dec_lt(x_134, x_135);
if (x_136 == 0)
{
uint8_t x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
lean_dec(x_134);
x_137 = l_instInhabitedUInt8;
x_138 = lean_box(x_137);
x_139 = l_outOfBounds___redArg(x_138);
x_140 = lean_unbox(x_139);
lean_dec(x_139);
x_119 = x_140;
goto block_133;
}
else
{
uint8_t x_141; 
x_141 = lean_byte_array_fget(x_9, x_134);
lean_dec(x_134);
x_119 = x_141;
goto block_133;
}
block_18:
{
lean_object* x_16; 
x_16 = l_Array_append___redArg(x_13, x_14);
lean_dec_ref(x_14);
x_1 = x_16;
x_3 = x_15;
goto _start;
}
block_22:
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec_ref(x_20);
x_14 = x_19;
x_15 = x_21;
goto block_18;
}
block_27:
{
lean_object* x_25; 
x_25 = l_Array_append___redArg(x_13, x_23);
lean_dec_ref(x_23);
x_1 = x_25;
x_3 = x_24;
goto _start;
}
block_31:
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec_ref(x_29);
x_23 = x_28;
x_24 = x_30;
goto block_27;
}
block_38:
{
lean_object* x_35; lean_object* x_36; 
x_35 = l_Array_append___redArg(x_13, x_33);
lean_dec_ref(x_33);
x_36 = l_Array_append___redArg(x_35, x_32);
lean_dec_ref(x_32);
x_1 = x_36;
x_3 = x_34;
goto _start;
}
block_43:
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec_ref(x_41);
x_32 = x_39;
x_33 = x_40;
x_34 = x_42;
goto block_38;
}
block_56:
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_array_get_size(x_48);
x_50 = lean_nat_dec_lt(x_5, x_49);
if (x_50 == 0)
{
lean_dec(x_12);
x_32 = x_45;
x_33 = x_48;
x_34 = x_46;
goto block_38;
}
else
{
uint8_t x_51; 
x_51 = lean_nat_dec_le(x_49, x_49);
if (x_51 == 0)
{
if (x_50 == 0)
{
lean_dec(x_12);
x_32 = x_45;
x_33 = x_48;
x_34 = x_46;
goto block_38;
}
else
{
size_t x_52; lean_object* x_53; 
x_52 = lean_usize_of_nat(x_49);
x_53 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__4(x_12, x_48, x_47, x_52, x_44, x_2, x_46);
x_39 = x_45;
x_40 = x_48;
x_41 = x_53;
goto block_43;
}
}
else
{
size_t x_54; lean_object* x_55; 
x_54 = lean_usize_of_nat(x_49);
x_55 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__4(x_12, x_48, x_47, x_54, x_44, x_2, x_46);
x_39 = x_45;
x_40 = x_48;
x_41 = x_55;
goto block_43;
}
}
}
block_73:
{
lean_object* x_60; size_t x_61; size_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_60 = lean_box(0);
x_61 = lean_array_size(x_57);
x_62 = 0;
lean_inc(x_12);
x_63 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__3___redArg(x_12, x_57, x_61, x_62, x_60, x_59);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec_ref(x_63);
x_65 = lean_array_get_size(x_58);
x_66 = lean_mk_empty_array_with_capacity(x_65);
x_67 = lean_nat_dec_lt(x_5, x_65);
if (x_67 == 0)
{
lean_dec_ref(x_58);
x_44 = x_60;
x_45 = x_57;
x_46 = x_64;
x_47 = x_62;
x_48 = x_66;
goto block_56;
}
else
{
uint8_t x_68; 
x_68 = lean_nat_dec_le(x_65, x_65);
if (x_68 == 0)
{
if (x_67 == 0)
{
lean_dec_ref(x_58);
x_44 = x_60;
x_45 = x_57;
x_46 = x_64;
x_47 = x_62;
x_48 = x_66;
goto block_56;
}
else
{
size_t x_69; lean_object* x_70; 
x_69 = lean_usize_of_nat(x_65);
x_70 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__5(x_58, x_62, x_69, x_66);
lean_dec_ref(x_58);
x_44 = x_60;
x_45 = x_57;
x_46 = x_64;
x_47 = x_62;
x_48 = x_70;
goto block_56;
}
}
else
{
size_t x_71; lean_object* x_72; 
x_71 = lean_usize_of_nat(x_65);
x_72 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__5(x_58, x_62, x_71, x_66);
lean_dec_ref(x_58);
x_44 = x_60;
x_45 = x_57;
x_46 = x_64;
x_47 = x_62;
x_48 = x_72;
goto block_56;
}
}
}
block_78:
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec_ref(x_76);
x_57 = x_74;
x_58 = x_75;
x_59 = x_77;
goto block_73;
}
block_118:
{
lean_object* x_80; 
x_80 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1___redArg(x_7, x_12);
if (lean_obj_tag(x_80) == 0)
{
lean_dec(x_12);
x_1 = x_13;
x_3 = x_79;
goto _start;
}
else
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_80, 0);
lean_inc(x_82);
lean_dec_ref(x_80);
switch (lean_obj_tag(x_82)) {
case 0:
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_83 = lean_ctor_get(x_82, 1);
lean_inc_ref(x_83);
lean_dec_ref(x_82);
x_84 = lean_array_get_size(x_83);
x_85 = lean_nat_dec_lt(x_5, x_84);
if (x_85 == 0)
{
lean_dec(x_12);
x_14 = x_83;
x_15 = x_79;
goto block_18;
}
else
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_box(0);
x_87 = lean_nat_dec_le(x_84, x_84);
if (x_87 == 0)
{
if (x_85 == 0)
{
lean_dec(x_12);
x_14 = x_83;
x_15 = x_79;
goto block_18;
}
else
{
size_t x_88; size_t x_89; lean_object* x_90; 
x_88 = 0;
x_89 = lean_usize_of_nat(x_84);
x_90 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2___redArg(x_12, x_83, x_88, x_89, x_86, x_79);
x_19 = x_83;
x_20 = x_90;
goto block_22;
}
}
else
{
size_t x_91; size_t x_92; lean_object* x_93; 
x_91 = 0;
x_92 = lean_usize_of_nat(x_84);
x_93 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2___redArg(x_12, x_83, x_91, x_92, x_86, x_79);
x_19 = x_83;
x_20 = x_93;
goto block_22;
}
}
}
case 1:
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_94 = lean_ctor_get(x_82, 2);
lean_inc_ref(x_94);
lean_dec_ref(x_82);
x_95 = lean_array_get_size(x_94);
x_96 = lean_nat_dec_lt(x_5, x_95);
if (x_96 == 0)
{
lean_dec(x_12);
x_23 = x_94;
x_24 = x_79;
goto block_27;
}
else
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_box(0);
x_98 = lean_nat_dec_le(x_95, x_95);
if (x_98 == 0)
{
if (x_96 == 0)
{
lean_dec(x_12);
x_23 = x_94;
x_24 = x_79;
goto block_27;
}
else
{
size_t x_99; size_t x_100; lean_object* x_101; 
x_99 = 0;
x_100 = lean_usize_of_nat(x_95);
x_101 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2___redArg(x_12, x_94, x_99, x_100, x_97, x_79);
x_28 = x_94;
x_29 = x_101;
goto block_31;
}
}
else
{
size_t x_102; size_t x_103; lean_object* x_104; 
x_102 = 0;
x_103 = lean_usize_of_nat(x_95);
x_104 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2___redArg(x_12, x_94, x_102, x_103, x_97, x_79);
x_28 = x_94;
x_29 = x_104;
goto block_31;
}
}
}
case 2:
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_105 = lean_ctor_get(x_82, 3);
lean_inc_ref(x_105);
x_106 = lean_ctor_get(x_82, 4);
lean_inc_ref(x_106);
lean_dec_ref(x_82);
x_107 = lean_array_get_size(x_105);
x_108 = lean_nat_dec_lt(x_5, x_107);
if (x_108 == 0)
{
x_57 = x_105;
x_58 = x_106;
x_59 = x_79;
goto block_73;
}
else
{
lean_object* x_109; uint8_t x_110; 
x_109 = lean_box(0);
x_110 = lean_nat_dec_le(x_107, x_107);
if (x_110 == 0)
{
if (x_108 == 0)
{
x_57 = x_105;
x_58 = x_106;
x_59 = x_79;
goto block_73;
}
else
{
size_t x_111; size_t x_112; lean_object* x_113; 
x_111 = 0;
x_112 = lean_usize_of_nat(x_107);
lean_inc(x_12);
x_113 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__4(x_12, x_105, x_111, x_112, x_109, x_2, x_79);
x_74 = x_105;
x_75 = x_106;
x_76 = x_113;
goto block_78;
}
}
else
{
size_t x_114; size_t x_115; lean_object* x_116; 
x_114 = 0;
x_115 = lean_usize_of_nat(x_107);
lean_inc(x_12);
x_116 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__4(x_12, x_105, x_114, x_115, x_109, x_2, x_79);
x_74 = x_105;
x_75 = x_106;
x_76 = x_116;
goto block_78;
}
}
}
default: 
{
lean_dec_ref(x_82);
lean_dec(x_12);
x_1 = x_13;
x_3 = x_79;
goto _start;
}
}
}
}
block_133:
{
uint8_t x_120; uint8_t x_121; 
x_120 = 1;
x_121 = lean_uint8_dec_eq(x_119, x_120);
if (x_121 == 0)
{
uint8_t x_122; 
x_122 = lean_nat_dec_le(x_8, x_12);
if (x_122 == 0)
{
x_79 = x_3;
goto block_118;
}
else
{
uint8_t x_123; 
lean_inc_ref(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
x_123 = !lean_is_exclusive(x_3);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_124 = lean_ctor_get(x_3, 2);
lean_dec(x_124);
x_125 = lean_ctor_get(x_3, 1);
lean_dec(x_125);
x_126 = lean_ctor_get(x_3, 0);
lean_dec(x_126);
x_127 = lean_nat_sub(x_12, x_8);
x_128 = lean_byte_array_set(x_9, x_127, x_120);
lean_dec(x_127);
lean_ctor_set(x_3, 0, x_128);
x_79 = x_3;
goto block_118;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_3);
x_129 = lean_nat_sub(x_12, x_8);
x_130 = lean_byte_array_set(x_9, x_129, x_120);
lean_dec(x_129);
x_131 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_10);
lean_ctor_set(x_131, 2, x_11);
x_79 = x_131;
goto block_118;
}
}
}
else
{
lean_dec(x_12);
x_1 = x_13;
goto _start;
}
}
}
else
{
lean_object* x_142; lean_object* x_143; 
lean_dec_ref(x_1);
x_142 = lean_box(0);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_3);
return x_143;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__3(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis___closed__0, &l_Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis___closed__0_once, _init_l_Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis___closed__0);
lean_inc(x_3);
x_5 = lean_array_push(x_4, x_3);
x_6 = l___private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go(x_5, x_1, x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__0_spec__0___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis___closed__0, &l_Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis___closed__0_once, _init_l_Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis___closed__0);
x_4 = lean_array_push(x_3, x_1);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_array_push(x_7, x_1);
lean_ctor_set(x_2, 0, x_8);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_array_push(x_9, x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_box(0);
x_5 = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__0_spec__0___lam__0(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 2, x_3);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_3, 2);
x_12 = lean_nat_dec_eq(x_9, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__0_spec__0(x_1, x_2, x_11);
lean_ctor_set(x_3, 2, x_13);
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_9);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_10);
x_15 = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__0_spec__0___lam__0(x_1, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
lean_ctor_set(x_3, 1, x_16);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_3, 0);
x_18 = lean_ctor_get(x_3, 1);
x_19 = lean_ctor_get(x_3, 2);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_3);
x_20 = lean_nat_dec_eq(x_17, x_2);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__0_spec__0(x_1, x_2, x_19);
x_22 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_17);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_18);
x_24 = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__0_spec__0___lam__0(x_1, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_19);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; uint8_t x_21; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_5);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_6 = x_2;
} else {
 lean_dec_ref(x_2);
 x_6 = lean_box(0);
}
x_7 = lean_array_get_size(x_5);
x_8 = lean_uint64_of_nat(x_3);
x_9 = 32;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = 16;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = lean_uint64_to_usize(x_14);
x_16 = lean_usize_of_nat(x_7);
x_17 = 1;
x_18 = lean_usize_sub(x_16, x_17);
x_19 = lean_usize_land(x_15, x_18);
x_20 = lean_array_uget_borrowed(x_5, x_19);
x_21 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__0___redArg(x_3, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis___closed__0, &l_Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis___closed__0_once, _init_l_Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis___closed__0);
x_24 = lean_array_push(x_23, x_1);
x_25 = lean_nat_add(x_4, x_22);
lean_dec(x_4);
lean_inc(x_20);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_3);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_20);
x_27 = lean_array_uset(x_5, x_19, x_26);
x_28 = lean_unsigned_to_nat(4u);
x_29 = lean_nat_mul(x_25, x_28);
x_30 = lean_unsigned_to_nat(3u);
x_31 = lean_nat_div(x_29, x_30);
lean_dec(x_29);
x_32 = lean_array_get_size(x_27);
x_33 = lean_nat_dec_le(x_31, x_32);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1___redArg(x_27);
if (lean_is_scalar(x_6)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_6;
}
lean_ctor_set(x_35, 0, x_25);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
else
{
lean_object* x_36; 
if (lean_is_scalar(x_6)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_6;
}
lean_ctor_set(x_36, 0, x_25);
lean_ctor_set(x_36, 1, x_27);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_44; 
lean_inc(x_20);
x_37 = lean_box(0);
x_38 = lean_array_uset(x_5, x_19, x_37);
lean_inc(x_3);
x_39 = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__0_spec__0(x_1, x_3, x_20);
x_44 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__0___redArg(x_3, x_39);
lean_dec(x_3);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_sub(x_4, x_45);
lean_dec(x_4);
x_40 = x_46;
goto block_43;
}
else
{
x_40 = x_4;
goto block_43;
}
block_43:
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_array_uset(x_38, x_19, x_39);
if (lean_is_scalar(x_6)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_6;
}
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_12; 
x_12 = lean_nat_dec_lt(x_3, x_1);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_3);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_5);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_array_fget_borrowed(x_2, x_3);
x_15 = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__1, &l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__1);
x_16 = lean_int_dec_eq(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_nat_abs(x_14);
lean_inc(x_3);
x_18 = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__0(x_3, x_4, x_17);
x_6 = x_18;
x_7 = x_5;
goto block_11;
}
else
{
x_6 = x_4;
x_7 = x_5;
goto block_11;
}
}
block_11:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_3, x_8);
lean_dec(x_3);
x_3 = x_9;
x_4 = x_6;
x_5 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__1___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_3);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__3, &l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__3);
x_6 = lean_array_get_size(x_3);
x_7 = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__1___redArg(x_6, x_3, x_4, x_5, x_2);
lean_dec_ref(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__1___redArg(x_1, x_2, x_5, x_6, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__7, &l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__7_once, _init_l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__7);
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_4, x_3);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_6, 2);
x_16 = lean_array_uget_borrowed(x_2, x_4);
x_17 = l_Int_instInhabited;
x_18 = lean_array_get_borrowed(x_17, x_15, x_16);
lean_inc(x_1);
x_19 = lean_nat_to_int(x_1);
x_20 = lean_int_dec_eq(x_18, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
x_7 = x_5;
x_8 = x_6;
goto block_12;
}
else
{
lean_object* x_21; 
lean_inc(x_16);
x_21 = lean_array_push(x_5, x_16);
x_7 = x_21;
x_8 = x_6;
goto block_12;
}
}
block_12:
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_4, x_9);
x_4 = x_10;
x_5 = x_7;
x_6 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0_spec__0___redArg(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_4, x_3);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_7);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_array_uget_borrowed(x_2, x_4);
x_18 = l_Int_instInhabited;
x_19 = lean_array_get_borrowed(x_18, x_16, x_17);
lean_inc(x_1);
x_20 = lean_nat_to_int(x_1);
x_21 = lean_int_dec_eq(x_19, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
x_8 = x_5;
x_9 = x_7;
goto block_13;
}
else
{
lean_object* x_22; 
lean_inc(x_17);
x_22 = lean_array_push(x_5, x_17);
x_8 = x_22;
x_9 = x_7;
goto block_13;
}
}
block_13:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = 1;
x_11 = lean_usize_add(x_4, x_10);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0_spec__0___redArg(x_1, x_2, x_3, x_11, x_8, x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__1_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_4, x_3);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_10 = lean_array_uget_borrowed(x_2, x_4);
x_11 = lean_ctor_get(x_10, 0);
x_12 = lean_ctor_get(x_10, 1);
x_25 = lean_ctor_get(x_7, 2);
x_26 = l_Int_instInhabited;
x_27 = lean_array_get_borrowed(x_26, x_25, x_11);
lean_inc(x_1);
x_28 = lean_nat_to_int(x_1);
x_29 = lean_int_dec_eq(x_27, x_28);
lean_dec(x_28);
if (x_29 == 0)
{
x_13 = x_5;
x_14 = x_6;
x_15 = x_7;
goto block_24;
}
else
{
lean_object* x_30; 
lean_inc(x_11);
x_30 = lean_array_push(x_5, x_11);
x_13 = x_30;
x_14 = x_6;
x_15 = x_7;
goto block_24;
}
block_24:
{
size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
x_16 = lean_array_size(x_12);
x_17 = 0;
lean_inc(x_1);
x_18 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0(x_1, x_12, x_16, x_17, x_13, x_14, x_15);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = 1;
x_22 = lean_usize_add(x_4, x_21);
x_4 = x_22;
x_5 = x_19;
x_7 = x_20;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__1_spec__2(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_4, x_3);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_10 = lean_array_uget_borrowed(x_2, x_4);
x_11 = lean_ctor_get(x_10, 0);
x_12 = lean_ctor_get(x_10, 1);
x_25 = lean_ctor_get(x_7, 2);
x_26 = l_Int_instInhabited;
x_27 = lean_array_get_borrowed(x_26, x_25, x_11);
lean_inc(x_1);
x_28 = lean_nat_to_int(x_1);
x_29 = lean_int_dec_eq(x_27, x_28);
lean_dec(x_28);
if (x_29 == 0)
{
x_13 = x_5;
x_14 = x_6;
x_15 = x_7;
goto block_24;
}
else
{
lean_object* x_30; 
lean_inc(x_11);
x_30 = lean_array_push(x_5, x_11);
x_13 = x_30;
x_14 = x_6;
x_15 = x_7;
goto block_24;
}
block_24:
{
size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_16 = lean_array_size(x_12);
x_17 = 0;
lean_inc(x_1);
x_18 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0(x_1, x_12, x_16, x_17, x_13, x_14, x_15);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = 1;
x_22 = lean_usize_add(x_4, x_21);
x_23 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__1_spec__2(x_1, x_2, x_3, x_22, x_19, x_6, x_20);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__1(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_27; uint8_t x_28; 
lean_inc_ref(x_7);
x_9 = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep(x_1, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_12 = x_9;
} else {
 lean_dec_ref(x_9);
 x_12 = lean_box(0);
}
x_13 = lean_array_size(x_3);
x_14 = 0;
x_15 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__0(x_13, x_14, x_3, x_7, x_11);
lean_dec_ref(x_7);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_18 = x_15;
} else {
 lean_dec_ref(x_15);
 x_18 = lean_box(0);
}
x_27 = lean_array_push(x_4, x_10);
x_28 = l_Array_isEmpty___redArg(x_16);
if (x_28 == 0)
{
if (x_2 == 0)
{
lean_dec(x_16);
x_19 = x_27;
x_20 = x_5;
goto block_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_29, 0, x_16);
x_30 = lean_array_push(x_27, x_29);
x_19 = x_30;
x_20 = x_5;
goto block_26;
}
}
else
{
lean_dec(x_16);
x_19 = x_27;
x_20 = x_5;
goto block_26;
}
block_26:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_20, x_21);
if (lean_is_scalar(x_12)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_12;
}
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
if (lean_is_scalar(x_18)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_18;
}
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_17);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___lam__0(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
return x_10;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__3));
x_2 = lean_unsigned_to_nat(14u);
x_3 = lean_unsigned_to_nat(22u);
x_4 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__2));
x_5 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__1));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_13; uint8_t x_24; 
x_24 = lean_nat_dec_le(x_3, x_1);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec_ref(x_5);
lean_dec(x_3);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_4);
lean_ctor_set(x_25, 1, x_6);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_26 = lean_ctor_get(x_4, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_4, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_28 = x_4;
} else {
 lean_dec_ref(x_4);
 x_28 = lean_box(0);
}
x_67 = lean_ctor_get(x_5, 0);
x_68 = lean_ctor_get(x_5, 1);
x_69 = lean_ctor_get(x_6, 0);
x_70 = lean_ctor_get(x_6, 1);
x_71 = lean_ctor_get(x_6, 2);
x_94 = lean_nat_sub(x_3, x_68);
x_95 = lean_byte_array_size(x_69);
x_96 = lean_nat_dec_lt(x_94, x_95);
if (x_96 == 0)
{
uint8_t x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
lean_dec(x_94);
x_97 = l_instInhabitedUInt8;
x_98 = lean_box(x_97);
x_99 = l_outOfBounds___redArg(x_98);
x_100 = lean_unbox(x_99);
lean_dec(x_99);
x_72 = x_100;
goto block_93;
}
else
{
uint8_t x_101; 
x_101 = lean_byte_array_fget(x_69, x_94);
lean_dec(x_94);
x_72 = x_101;
goto block_93;
}
block_34:
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_box(0);
lean_inc_ref(x_5);
x_33 = lean_apply_6(x_29, x_31, x_26, x_27, x_32, x_5, x_30);
x_13 = x_33;
goto block_23;
}
block_66:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_box(x_35);
lean_inc_ref(x_38);
x_40 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___lam__0___boxed), 8, 2);
lean_closure_set(x_40, 0, x_38);
lean_closure_set(x_40, 1, x_39);
x_41 = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__0);
x_42 = lean_nat_dec_eq(x_3, x_2);
if (x_42 == 0)
{
if (x_36 == 0)
{
lean_dec_ref(x_38);
x_29 = x_40;
x_30 = x_37;
x_31 = x_41;
goto block_34;
}
else
{
lean_dec_ref(x_40);
switch (lean_obj_tag(x_38)) {
case 1:
{
lean_object* x_43; size_t x_44; size_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_43 = lean_ctor_get(x_38, 2);
x_44 = lean_array_size(x_43);
x_45 = 0;
lean_inc(x_3);
x_46 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0(x_3, x_43, x_44, x_45, x_41, x_5, x_37);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec_ref(x_46);
x_49 = lean_box(0);
lean_inc_ref(x_5);
x_50 = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___lam__0(x_38, x_35, x_47, x_26, x_27, x_49, x_5, x_48);
lean_dec(x_27);
x_13 = x_50;
goto block_23;
}
case 2:
{
lean_object* x_51; lean_object* x_52; size_t x_53; size_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; size_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_51 = lean_ctor_get(x_38, 3);
x_52 = lean_ctor_get(x_38, 4);
x_53 = lean_array_size(x_51);
x_54 = 0;
lean_inc(x_3);
x_55 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0(x_3, x_51, x_53, x_54, x_41, x_5, x_37);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec_ref(x_55);
x_58 = lean_array_size(x_52);
lean_inc(x_3);
x_59 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__1(x_3, x_52, x_58, x_54, x_56, x_5, x_57);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec_ref(x_59);
x_62 = lean_box(0);
lean_inc_ref(x_5);
x_63 = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___lam__0(x_38, x_35, x_60, x_26, x_27, x_62, x_5, x_61);
lean_dec(x_27);
x_13 = x_63;
goto block_23;
}
default: 
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_box(0);
lean_inc_ref(x_5);
x_65 = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___lam__0(x_38, x_35, x_41, x_26, x_27, x_64, x_5, x_37);
lean_dec(x_27);
x_13 = x_65;
goto block_23;
}
}
}
}
else
{
lean_dec_ref(x_38);
x_29 = x_40;
x_30 = x_37;
x_31 = x_41;
goto block_34;
}
}
block_93:
{
uint8_t x_73; uint8_t x_74; 
x_73 = 1;
x_74 = lean_uint8_dec_eq(x_72, x_73);
if (x_74 == 0)
{
lean_object* x_75; 
if (lean_is_scalar(x_28)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_28;
}
lean_ctor_set(x_75, 0, x_26);
lean_ctor_set(x_75, 1, x_27);
x_7 = x_75;
x_8 = x_6;
goto block_12;
}
else
{
uint8_t x_76; 
lean_inc_ref(x_71);
lean_inc_ref(x_70);
lean_inc_ref(x_69);
lean_dec(x_28);
x_76 = !lean_is_exclusive(x_6);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_77 = lean_ctor_get(x_6, 2);
lean_dec(x_77);
x_78 = lean_ctor_get(x_6, 1);
lean_dec(x_78);
x_79 = lean_ctor_get(x_6, 0);
lean_dec(x_79);
x_80 = lean_nat_sub(x_3, x_68);
lean_inc(x_27);
x_81 = lean_array_set(x_70, x_80, x_27);
lean_dec(x_80);
lean_ctor_set(x_6, 1, x_81);
x_82 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1___redArg(x_67, x_3);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__4);
x_84 = l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__2(x_83);
x_35 = x_74;
x_36 = x_74;
x_37 = x_6;
x_38 = x_84;
goto block_66;
}
else
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_82, 0);
lean_inc(x_85);
lean_dec_ref(x_82);
x_35 = x_74;
x_36 = x_74;
x_37 = x_6;
x_38 = x_85;
goto block_66;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_6);
x_86 = lean_nat_sub(x_3, x_68);
lean_inc(x_27);
x_87 = lean_array_set(x_70, x_86, x_27);
lean_dec(x_86);
x_88 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_88, 0, x_69);
lean_ctor_set(x_88, 1, x_87);
lean_ctor_set(x_88, 2, x_71);
x_89 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1___redArg(x_67, x_3);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__4);
x_91 = l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__2(x_90);
x_35 = x_74;
x_36 = x_74;
x_37 = x_88;
x_38 = x_91;
goto block_66;
}
else
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_89, 0);
lean_inc(x_92);
lean_dec_ref(x_89);
x_35 = x_74;
x_36 = x_74;
x_37 = x_88;
x_38 = x_92;
goto block_66;
}
}
}
}
}
block_12:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
x_4 = x_7;
x_6 = x_8;
goto _start;
}
block_23:
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec_ref(x_5);
lean_dec(x_3);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec_ref(x_14);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec_ref(x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec_ref(x_13);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec_ref(x_14);
x_7 = x_22;
x_8 = x_21;
goto block_12;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping___closed__0, &l_Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping___closed__0_once, _init_l_Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping___closed__0);
lean_inc(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
x_7 = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg(x_4, x_4, x_3, x_6, x_1, x_2);
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg(x_1, x_2, x_5, x_6, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0_spec__0(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_go(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_inc_ref(x_1);
x_3 = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis(x_1, x_2);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_LRAT_trim_go), 2, 0);
x_3 = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_BVDecide_LRAT_trim(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
lean_object* initialize_Init_Data_Nat_Fold(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Actions(uint8_t builtin);
lean_object* initialize_Std_Data_HashMap(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_BVDecide_LRAT_Trim(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Fold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_LRAT_Actions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
