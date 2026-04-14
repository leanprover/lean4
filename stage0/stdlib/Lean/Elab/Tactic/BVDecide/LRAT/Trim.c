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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Int_instInhabited;
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_byte_array_set(lean_object*, lean_object*, uint8_t);
lean_object* lean_byte_array_size(lean_object*);
extern uint8_t l_instInhabitedUInt8;
lean_object* l_outOfBounds___redArg(lean_object*);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default(lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_mk_empty_byte_array(lean_object*);
lean_object* lean_byte_array_push(lean_object*, uint8_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_UInt64_ofNat___boxed(lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findInitialId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "LRAT proof doesn't contain a proper first proof step."};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findInitialId___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findInitialId___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findInitialId___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findInitialId___closed__0_value)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findInitialId___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findInitialId___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findInitialId(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findInitialId___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__1___redArg(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__3;
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
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_getProofStep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_ofNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_getProofStep___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_getProofStep___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_getProofStep___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_getProofStep___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_getProofStep(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_getProofStep___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_isUsed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_isUsed___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_markUsed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_markUsed___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_registerIdMap(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_registerIdMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_updateLastUse___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_updateLastUse___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_updateLastUse(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_updateLastUse___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapIdent(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapIdent___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__0 = (const lean_object*)&l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__0_value;
static const lean_closure_object l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__1 = (const lean_object*)&l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__2 = (const lean_object*)&l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__3 = (const lean_object*)&l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__4 = (const lean_object*)&l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__4_value;
static const lean_closure_object l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__5 = (const lean_object*)&l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__5_value;
static const lean_closure_object l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__6 = (const lean_object*)&l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__6_value;
static lean_once_cell_t l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__7;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Elab.Tactic.BVDecide.LRAT.Trim"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "Lean.Elab.Tactic.BVDecide.LRAT.trim.M.mapStep"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__3___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__0_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__0_value;
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
static const lean_array_object l_Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findInitialId(lean_object* v_proof_4_, lean_object* v_curr_5_){
_start:
{
lean_object* v___x_6_; uint8_t v___x_7_; 
v___x_6_ = lean_array_get_size(v_proof_4_);
v___x_7_ = lean_nat_dec_lt(v_curr_5_, v___x_6_);
if (v___x_7_ == 0)
{
lean_object* v___x_8_; 
lean_dec(v_curr_5_);
v___x_8_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findInitialId___closed__1));
return v___x_8_;
}
else
{
lean_object* v___x_9_; 
v___x_9_ = lean_array_fget_borrowed(v_proof_4_, v_curr_5_);
if (lean_obj_tag(v___x_9_) == 3)
{
lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_10_ = lean_unsigned_to_nat(1u);
v___x_11_ = lean_nat_add(v_curr_5_, v___x_10_);
lean_dec(v_curr_5_);
v_curr_5_ = v___x_11_;
goto _start;
}
else
{
lean_object* v_id_13_; lean_object* v___x_14_; 
lean_dec(v_curr_5_);
v_id_13_ = lean_ctor_get(v___x_9_, 0);
lean_inc(v_id_13_);
v___x_14_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_14_, 0, v_id_13_);
return v___x_14_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findInitialId___boxed(lean_object* v_proof_15_, lean_object* v_curr_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findInitialId(v_proof_15_, v_curr_16_);
lean_dec_ref(v_proof_15_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findEmptyId_spec__0___redArg(lean_object* v_as_18_, lean_object* v_i_19_){
_start:
{
lean_object* v_zero_20_; uint8_t v_isZero_21_; 
v_zero_20_ = lean_unsigned_to_nat(0u);
v_isZero_21_ = lean_nat_dec_eq(v_i_19_, v_zero_20_);
if (v_isZero_21_ == 1)
{
lean_object* v___x_22_; 
lean_dec(v_i_19_);
v___x_22_ = lean_box(0);
return v___x_22_;
}
else
{
lean_object* v_one_23_; lean_object* v_n_24_; lean_object* v___x_25_; 
v_one_23_ = lean_unsigned_to_nat(1u);
v_n_24_ = lean_nat_sub(v_i_19_, v_one_23_);
lean_dec(v_i_19_);
v___x_25_ = lean_array_fget_borrowed(v_as_18_, v_n_24_);
if (lean_obj_tag(v___x_25_) == 0)
{
lean_object* v_id_26_; lean_object* v___x_27_; 
lean_dec(v_n_24_);
v_id_26_ = lean_ctor_get(v___x_25_, 0);
lean_inc(v_id_26_);
v___x_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_27_, 0, v_id_26_);
return v___x_27_;
}
else
{
v_i_19_ = v_n_24_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findEmptyId_spec__0___redArg___boxed(lean_object* v_as_29_, lean_object* v_i_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findEmptyId_spec__0___redArg(v_as_29_, v_i_30_);
lean_dec_ref(v_as_29_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findEmptyId(lean_object* v_proof_35_){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = lean_array_get_size(v_proof_35_);
v___x_37_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findEmptyId_spec__0___redArg(v_proof_35_, v___x_36_);
if (lean_obj_tag(v___x_37_) == 0)
{
lean_object* v___x_38_; 
v___x_38_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findEmptyId___closed__1));
return v___x_38_;
}
else
{
lean_object* v_val_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_46_; 
v_val_39_ = lean_ctor_get(v___x_37_, 0);
v_isSharedCheck_46_ = !lean_is_exclusive(v___x_37_);
if (v_isSharedCheck_46_ == 0)
{
v___x_41_ = v___x_37_;
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_val_39_);
lean_dec(v___x_37_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v___x_44_; 
if (v_isShared_42_ == 0)
{
v___x_44_ = v___x_41_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_val_39_);
v___x_44_ = v_reuseFailAlloc_45_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
return v___x_44_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findEmptyId___boxed(lean_object* v_proof_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findEmptyId(v_proof_47_);
lean_dec_ref(v_proof_47_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findEmptyId_spec__0(lean_object* v_as_49_, lean_object* v_i_50_, lean_object* v_a_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findEmptyId_spec__0___redArg(v_as_49_, v_i_50_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findEmptyId_spec__0___boxed(lean_object* v_as_53_, lean_object* v_i_54_, lean_object* v_a_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findEmptyId_spec__0(v_as_53_, v_i_54_, v_a_55_);
lean_dec_ref(v_as_53_);
return v_res_56_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__0___redArg(lean_object* v_a_57_, lean_object* v_x_58_){
_start:
{
if (lean_obj_tag(v_x_58_) == 0)
{
uint8_t v___x_59_; 
v___x_59_ = 0;
return v___x_59_;
}
else
{
lean_object* v_key_60_; lean_object* v_tail_61_; uint8_t v___x_62_; 
v_key_60_ = lean_ctor_get(v_x_58_, 0);
v_tail_61_ = lean_ctor_get(v_x_58_, 2);
v___x_62_ = lean_nat_dec_eq(v_key_60_, v_a_57_);
if (v___x_62_ == 0)
{
v_x_58_ = v_tail_61_;
goto _start;
}
else
{
return v___x_62_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__0___redArg___boxed(lean_object* v_a_64_, lean_object* v_x_65_){
_start:
{
uint8_t v_res_66_; lean_object* v_r_67_; 
v_res_66_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__0___redArg(v_a_64_, v_x_65_);
lean_dec(v_x_65_);
lean_dec(v_a_64_);
v_r_67_ = lean_box(v_res_66_);
return v_r_67_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__2___redArg(lean_object* v_a_68_, lean_object* v_b_69_, lean_object* v_x_70_){
_start:
{
if (lean_obj_tag(v_x_70_) == 0)
{
lean_dec(v_b_69_);
lean_dec(v_a_68_);
return v_x_70_;
}
else
{
lean_object* v_key_71_; lean_object* v_value_72_; lean_object* v_tail_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_85_; 
v_key_71_ = lean_ctor_get(v_x_70_, 0);
v_value_72_ = lean_ctor_get(v_x_70_, 1);
v_tail_73_ = lean_ctor_get(v_x_70_, 2);
v_isSharedCheck_85_ = !lean_is_exclusive(v_x_70_);
if (v_isSharedCheck_85_ == 0)
{
v___x_75_ = v_x_70_;
v_isShared_76_ = v_isSharedCheck_85_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_tail_73_);
lean_inc(v_value_72_);
lean_inc(v_key_71_);
lean_dec(v_x_70_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_85_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
uint8_t v___x_77_; 
v___x_77_ = lean_nat_dec_eq(v_key_71_, v_a_68_);
if (v___x_77_ == 0)
{
lean_object* v___x_78_; lean_object* v___x_80_; 
v___x_78_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__2___redArg(v_a_68_, v_b_69_, v_tail_73_);
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 2, v___x_78_);
v___x_80_ = v___x_75_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_key_71_);
lean_ctor_set(v_reuseFailAlloc_81_, 1, v_value_72_);
lean_ctor_set(v_reuseFailAlloc_81_, 2, v___x_78_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
else
{
lean_object* v___x_83_; 
lean_dec(v_value_72_);
lean_dec(v_key_71_);
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 1, v_b_69_);
lean_ctor_set(v___x_75_, 0, v_a_68_);
v___x_83_ = v___x_75_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v_a_68_);
lean_ctor_set(v_reuseFailAlloc_84_, 1, v_b_69_);
lean_ctor_set(v_reuseFailAlloc_84_, 2, v_tail_73_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
return v___x_83_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_x_86_, lean_object* v_x_87_){
_start:
{
if (lean_obj_tag(v_x_87_) == 0)
{
return v_x_86_;
}
else
{
lean_object* v_key_88_; lean_object* v_value_89_; lean_object* v_tail_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_113_; 
v_key_88_ = lean_ctor_get(v_x_87_, 0);
v_value_89_ = lean_ctor_get(v_x_87_, 1);
v_tail_90_ = lean_ctor_get(v_x_87_, 2);
v_isSharedCheck_113_ = !lean_is_exclusive(v_x_87_);
if (v_isSharedCheck_113_ == 0)
{
v___x_92_ = v_x_87_;
v_isShared_93_ = v_isSharedCheck_113_;
goto v_resetjp_91_;
}
else
{
lean_inc(v_tail_90_);
lean_inc(v_value_89_);
lean_inc(v_key_88_);
lean_dec(v_x_87_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_113_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
lean_object* v___x_94_; uint64_t v___x_95_; uint64_t v___x_96_; uint64_t v___x_97_; uint64_t v_fold_98_; uint64_t v___x_99_; uint64_t v___x_100_; uint64_t v___x_101_; size_t v___x_102_; size_t v___x_103_; size_t v___x_104_; size_t v___x_105_; size_t v___x_106_; lean_object* v___x_107_; lean_object* v___x_109_; 
v___x_94_ = lean_array_get_size(v_x_86_);
v___x_95_ = lean_uint64_of_nat(v_key_88_);
v___x_96_ = 32ULL;
v___x_97_ = lean_uint64_shift_right(v___x_95_, v___x_96_);
v_fold_98_ = lean_uint64_xor(v___x_95_, v___x_97_);
v___x_99_ = 16ULL;
v___x_100_ = lean_uint64_shift_right(v_fold_98_, v___x_99_);
v___x_101_ = lean_uint64_xor(v_fold_98_, v___x_100_);
v___x_102_ = lean_uint64_to_usize(v___x_101_);
v___x_103_ = lean_usize_of_nat(v___x_94_);
v___x_104_ = ((size_t)1ULL);
v___x_105_ = lean_usize_sub(v___x_103_, v___x_104_);
v___x_106_ = lean_usize_land(v___x_102_, v___x_105_);
v___x_107_ = lean_array_uget_borrowed(v_x_86_, v___x_106_);
lean_inc(v___x_107_);
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 2, v___x_107_);
v___x_109_ = v___x_92_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_key_88_);
lean_ctor_set(v_reuseFailAlloc_112_, 1, v_value_89_);
lean_ctor_set(v_reuseFailAlloc_112_, 2, v___x_107_);
v___x_109_ = v_reuseFailAlloc_112_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v___x_110_; 
v___x_110_ = lean_array_uset(v_x_86_, v___x_106_, v___x_109_);
v_x_86_ = v___x_110_;
v_x_87_ = v_tail_90_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1_spec__2___redArg(lean_object* v_i_114_, lean_object* v_source_115_, lean_object* v_target_116_){
_start:
{
lean_object* v___x_117_; uint8_t v___x_118_; 
v___x_117_ = lean_array_get_size(v_source_115_);
v___x_118_ = lean_nat_dec_lt(v_i_114_, v___x_117_);
if (v___x_118_ == 0)
{
lean_dec_ref(v_source_115_);
lean_dec(v_i_114_);
return v_target_116_;
}
else
{
lean_object* v_es_119_; lean_object* v___x_120_; lean_object* v_source_121_; lean_object* v_target_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v_es_119_ = lean_array_fget(v_source_115_, v_i_114_);
v___x_120_ = lean_box(0);
v_source_121_ = lean_array_fset(v_source_115_, v_i_114_, v___x_120_);
v_target_122_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1_spec__2_spec__5___redArg(v_target_116_, v_es_119_);
v___x_123_ = lean_unsigned_to_nat(1u);
v___x_124_ = lean_nat_add(v_i_114_, v___x_123_);
lean_dec(v_i_114_);
v_i_114_ = v___x_124_;
v_source_115_ = v_source_121_;
v_target_116_ = v_target_122_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1___redArg(lean_object* v_data_126_){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v_nbuckets_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_127_ = lean_array_get_size(v_data_126_);
v___x_128_ = lean_unsigned_to_nat(2u);
v_nbuckets_129_ = lean_nat_mul(v___x_127_, v___x_128_);
v___x_130_ = lean_unsigned_to_nat(0u);
v___x_131_ = lean_box(0);
v___x_132_ = lean_mk_array(v_nbuckets_129_, v___x_131_);
v___x_133_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1_spec__2___redArg(v___x_130_, v_data_126_, v___x_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0___redArg(lean_object* v_m_134_, lean_object* v_a_135_, lean_object* v_b_136_){
_start:
{
lean_object* v_size_137_; lean_object* v_buckets_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_181_; 
v_size_137_ = lean_ctor_get(v_m_134_, 0);
v_buckets_138_ = lean_ctor_get(v_m_134_, 1);
v_isSharedCheck_181_ = !lean_is_exclusive(v_m_134_);
if (v_isSharedCheck_181_ == 0)
{
v___x_140_ = v_m_134_;
v_isShared_141_ = v_isSharedCheck_181_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_buckets_138_);
lean_inc(v_size_137_);
lean_dec(v_m_134_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_181_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_142_; uint64_t v___x_143_; uint64_t v___x_144_; uint64_t v___x_145_; uint64_t v_fold_146_; uint64_t v___x_147_; uint64_t v___x_148_; uint64_t v___x_149_; size_t v___x_150_; size_t v___x_151_; size_t v___x_152_; size_t v___x_153_; size_t v___x_154_; lean_object* v_bkt_155_; uint8_t v___x_156_; 
v___x_142_ = lean_array_get_size(v_buckets_138_);
v___x_143_ = lean_uint64_of_nat(v_a_135_);
v___x_144_ = 32ULL;
v___x_145_ = lean_uint64_shift_right(v___x_143_, v___x_144_);
v_fold_146_ = lean_uint64_xor(v___x_143_, v___x_145_);
v___x_147_ = 16ULL;
v___x_148_ = lean_uint64_shift_right(v_fold_146_, v___x_147_);
v___x_149_ = lean_uint64_xor(v_fold_146_, v___x_148_);
v___x_150_ = lean_uint64_to_usize(v___x_149_);
v___x_151_ = lean_usize_of_nat(v___x_142_);
v___x_152_ = ((size_t)1ULL);
v___x_153_ = lean_usize_sub(v___x_151_, v___x_152_);
v___x_154_ = lean_usize_land(v___x_150_, v___x_153_);
v_bkt_155_ = lean_array_uget_borrowed(v_buckets_138_, v___x_154_);
v___x_156_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__0___redArg(v_a_135_, v_bkt_155_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; lean_object* v_size_x27_158_; lean_object* v___x_159_; lean_object* v_buckets_x27_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; uint8_t v___x_166_; 
v___x_157_ = lean_unsigned_to_nat(1u);
v_size_x27_158_ = lean_nat_add(v_size_137_, v___x_157_);
lean_dec(v_size_137_);
lean_inc(v_bkt_155_);
v___x_159_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_159_, 0, v_a_135_);
lean_ctor_set(v___x_159_, 1, v_b_136_);
lean_ctor_set(v___x_159_, 2, v_bkt_155_);
v_buckets_x27_160_ = lean_array_uset(v_buckets_138_, v___x_154_, v___x_159_);
v___x_161_ = lean_unsigned_to_nat(4u);
v___x_162_ = lean_nat_mul(v_size_x27_158_, v___x_161_);
v___x_163_ = lean_unsigned_to_nat(3u);
v___x_164_ = lean_nat_div(v___x_162_, v___x_163_);
lean_dec(v___x_162_);
v___x_165_ = lean_array_get_size(v_buckets_x27_160_);
v___x_166_ = lean_nat_dec_le(v___x_164_, v___x_165_);
lean_dec(v___x_164_);
if (v___x_166_ == 0)
{
lean_object* v_val_167_; lean_object* v___x_169_; 
v_val_167_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1___redArg(v_buckets_x27_160_);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 1, v_val_167_);
lean_ctor_set(v___x_140_, 0, v_size_x27_158_);
v___x_169_ = v___x_140_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_size_x27_158_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v_val_167_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
else
{
lean_object* v___x_172_; 
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 1, v_buckets_x27_160_);
lean_ctor_set(v___x_140_, 0, v_size_x27_158_);
v___x_172_ = v___x_140_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_size_x27_158_);
lean_ctor_set(v_reuseFailAlloc_173_, 1, v_buckets_x27_160_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
else
{
lean_object* v___x_174_; lean_object* v_buckets_x27_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_179_; 
lean_inc(v_bkt_155_);
v___x_174_ = lean_box(0);
v_buckets_x27_175_ = lean_array_uset(v_buckets_138_, v___x_154_, v___x_174_);
v___x_176_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__2___redArg(v_a_135_, v_b_136_, v_bkt_155_);
v___x_177_ = lean_array_uset(v_buckets_x27_175_, v___x_154_, v___x_176_);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 1, v___x_177_);
v___x_179_ = v___x_140_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_size_137_);
lean_ctor_set(v_reuseFailAlloc_180_, 1, v___x_177_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__2(lean_object* v_as_182_, size_t v_i_183_, size_t v_stop_184_, lean_object* v_b_185_){
_start:
{
lean_object* v___y_187_; uint8_t v___x_191_; 
v___x_191_ = lean_usize_dec_eq(v_i_183_, v_stop_184_);
if (v___x_191_ == 0)
{
lean_object* v___x_192_; 
v___x_192_ = lean_array_uget_borrowed(v_as_182_, v_i_183_);
if (lean_obj_tag(v___x_192_) == 3)
{
v___y_187_ = v_b_185_;
goto v___jp_186_;
}
else
{
lean_object* v_id_193_; lean_object* v___x_194_; 
v_id_193_ = lean_ctor_get(v___x_192_, 0);
lean_inc(v___x_192_);
lean_inc(v_id_193_);
v___x_194_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0___redArg(v_b_185_, v_id_193_, v___x_192_);
v___y_187_ = v___x_194_;
goto v___jp_186_;
}
}
else
{
return v_b_185_;
}
v___jp_186_:
{
size_t v___x_188_; size_t v___x_189_; 
v___x_188_ = ((size_t)1ULL);
v___x_189_ = lean_usize_add(v_i_183_, v___x_188_);
v_i_183_ = v___x_189_;
v_b_185_ = v___y_187_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__2___boxed(lean_object* v_as_195_, lean_object* v_i_196_, lean_object* v_stop_197_, lean_object* v_b_198_){
_start:
{
size_t v_i_boxed_199_; size_t v_stop_boxed_200_; lean_object* v_res_201_; 
v_i_boxed_199_ = lean_unbox_usize(v_i_196_);
lean_dec(v_i_196_);
v_stop_boxed_200_ = lean_unbox_usize(v_stop_197_);
lean_dec(v_stop_197_);
v_res_201_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__2(v_as_195_, v_i_boxed_199_, v_stop_boxed_200_, v_b_198_);
lean_dec_ref(v_as_195_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__1___redArg(lean_object* v_j_202_, lean_object* v_a_203_){
_start:
{
lean_object* v_zero_204_; uint8_t v_isZero_205_; 
v_zero_204_ = lean_unsigned_to_nat(0u);
v_isZero_205_ = lean_nat_dec_eq(v_j_202_, v_zero_204_);
if (v_isZero_205_ == 1)
{
lean_dec(v_j_202_);
return v_a_203_;
}
else
{
lean_object* v_one_206_; lean_object* v_n_207_; uint8_t v___x_208_; lean_object* v___x_209_; 
v_one_206_ = lean_unsigned_to_nat(1u);
v_n_207_ = lean_nat_sub(v_j_202_, v_one_206_);
lean_dec(v_j_202_);
v___x_208_ = 0;
v___x_209_ = lean_byte_array_push(v_a_203_, v___x_208_);
v_j_202_ = v_n_207_;
v_a_203_ = v___x_209_;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = lean_unsigned_to_nat(1u);
v___x_212_ = lean_nat_to_int(v___x_211_);
return v___x_212_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__0, &l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__0);
v___x_214_ = lean_int_neg(v___x_213_);
return v___x_214_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__2(void){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_215_ = lean_box(0);
v___x_216_ = lean_unsigned_to_nat(16u);
v___x_217_ = lean_mk_array(v___x_216_, v___x_215_);
return v___x_217_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__3(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_218_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__2, &l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__2);
v___x_219_ = lean_unsigned_to_nat(0u);
v___x_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
lean_ctor_set(v___x_220_, 1, v___x_218_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg(lean_object* v_proof_221_, lean_object* v_x_222_){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = lean_unsigned_to_nat(0u);
v___x_224_ = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findInitialId(v_proof_221_, v___x_223_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_object* v_a_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_232_; 
lean_dec_ref(v_x_222_);
v_a_225_ = lean_ctor_get(v___x_224_, 0);
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_232_ == 0)
{
v___x_227_ = v___x_224_;
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_a_225_);
lean_dec(v___x_224_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_230_; 
if (v_isShared_228_ == 0)
{
v___x_230_ = v___x_227_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_a_225_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
else
{
lean_object* v_a_233_; lean_object* v___x_234_; 
v_a_233_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_a_233_);
lean_dec_ref(v___x_224_);
v___x_234_ = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_findEmptyId(v_proof_221_);
if (lean_obj_tag(v___x_234_) == 0)
{
lean_object* v_a_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_242_; 
lean_dec(v_a_233_);
lean_dec_ref(v_x_222_);
v_a_235_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_242_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_242_ == 0)
{
v___x_237_ = v___x_234_;
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_a_235_);
lean_dec(v___x_234_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_240_; 
if (v_isShared_238_ == 0)
{
v___x_240_ = v___x_237_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_a_235_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
}
else
{
lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_276_; 
v_a_243_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_276_ == 0)
{
v___x_245_ = v___x_234_;
v_isShared_246_ = v_isSharedCheck_276_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_234_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_276_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___y_248_; lean_object* v_size_249_; lean_object* v___y_264_; lean_object* v___x_266_; lean_object* v___x_267_; uint8_t v___x_268_; 
v___x_266_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__3, &l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__3);
v___x_267_ = lean_array_get_size(v_proof_221_);
v___x_268_ = lean_nat_dec_lt(v___x_223_, v___x_267_);
if (v___x_268_ == 0)
{
v___y_248_ = v___x_266_;
v_size_249_ = v___x_223_;
goto v___jp_247_;
}
else
{
uint8_t v___x_269_; 
v___x_269_ = lean_nat_dec_le(v___x_267_, v___x_267_);
if (v___x_269_ == 0)
{
if (v___x_268_ == 0)
{
v___y_248_ = v___x_266_;
v_size_249_ = v___x_223_;
goto v___jp_247_;
}
else
{
size_t v___x_270_; size_t v___x_271_; lean_object* v___x_272_; 
v___x_270_ = ((size_t)0ULL);
v___x_271_ = lean_usize_of_nat(v___x_267_);
v___x_272_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__2(v_proof_221_, v___x_270_, v___x_271_, v___x_266_);
v___y_264_ = v___x_272_;
goto v___jp_263_;
}
}
else
{
size_t v___x_273_; size_t v___x_274_; lean_object* v___x_275_; 
v___x_273_ = ((size_t)0ULL);
v___x_274_ = lean_usize_of_nat(v___x_267_);
v___x_275_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__2(v_proof_221_, v___x_273_, v___x_274_, v___x_266_);
v___y_264_ = v___x_275_;
goto v___jp_263_;
}
}
v___jp_247_:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v_fst_259_; lean_object* v___x_261_; 
v___x_250_ = lean_mk_empty_byte_array(v_size_249_);
lean_inc(v_size_249_);
v___x_251_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__1___redArg(v_size_249_, v___x_250_);
v___x_252_ = lean_nat_add(v_a_233_, v_size_249_);
v___x_253_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__1, &l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__1);
v___x_254_ = lean_mk_array(v___x_252_, v___x_253_);
v___x_255_ = lean_mk_array(v_size_249_, v___x_223_);
v___x_256_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_256_, 0, v___y_248_);
lean_ctor_set(v___x_256_, 1, v_a_233_);
lean_ctor_set(v___x_256_, 2, v_a_243_);
v___x_257_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_257_, 0, v___x_251_);
lean_ctor_set(v___x_257_, 1, v___x_255_);
lean_ctor_set(v___x_257_, 2, v___x_254_);
v___x_258_ = lean_apply_2(v_x_222_, v___x_256_, v___x_257_);
v_fst_259_ = lean_ctor_get(v___x_258_, 0);
lean_inc(v_fst_259_);
lean_dec_ref(v___x_258_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 0, v_fst_259_);
v___x_261_ = v___x_245_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_fst_259_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
v___jp_263_:
{
lean_object* v_size_265_; 
v_size_265_ = lean_ctor_get(v___y_264_, 0);
lean_inc(v_size_265_);
v___y_248_ = v___y_264_;
v_size_249_ = v_size_265_;
goto v___jp_247_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___boxed(lean_object* v_proof_277_, lean_object* v_x_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg(v_proof_277_, v_x_278_);
lean_dec_ref(v_proof_277_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run(lean_object* v_00_u03b1_280_, lean_object* v_proof_281_, lean_object* v_x_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg(v_proof_281_, v_x_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___boxed(lean_object* v_00_u03b1_284_, lean_object* v_proof_285_, lean_object* v_x_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run(v_00_u03b1_284_, v_proof_285_, v_x_286_);
lean_dec_ref(v_proof_285_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0(lean_object* v_00_u03b2_288_, lean_object* v_m_289_, lean_object* v_a_290_, lean_object* v_b_291_){
_start:
{
lean_object* v___x_292_; 
v___x_292_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0___redArg(v_m_289_, v_a_290_, v_b_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__1(lean_object* v_n_293_, lean_object* v_j_294_, lean_object* v_a_295_, lean_object* v_a_296_){
_start:
{
lean_object* v___x_297_; 
v___x_297_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__1___redArg(v_j_294_, v_a_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__1___boxed(lean_object* v_n_298_, lean_object* v_j_299_, lean_object* v_a_300_, lean_object* v_a_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__1(v_n_298_, v_j_299_, v_a_300_, v_a_301_);
lean_dec(v_n_298_);
return v_res_302_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__0(lean_object* v_00_u03b2_303_, lean_object* v_a_304_, lean_object* v_x_305_){
_start:
{
uint8_t v___x_306_; 
v___x_306_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__0___redArg(v_a_304_, v_x_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__0___boxed(lean_object* v_00_u03b2_307_, lean_object* v_a_308_, lean_object* v_x_309_){
_start:
{
uint8_t v_res_310_; lean_object* v_r_311_; 
v_res_310_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__0(v_00_u03b2_307_, v_a_308_, v_x_309_);
lean_dec(v_x_309_);
lean_dec(v_a_308_);
v_r_311_ = lean_box(v_res_310_);
return v_r_311_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1(lean_object* v_00_u03b2_312_, lean_object* v_data_313_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1___redArg(v_data_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__2(lean_object* v_00_u03b2_315_, lean_object* v_a_316_, lean_object* v_b_317_, lean_object* v_x_318_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__2___redArg(v_a_316_, v_b_317_, v_x_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_320_, lean_object* v_i_321_, lean_object* v_source_322_, lean_object* v_target_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1_spec__2___redArg(v_i_321_, v_source_322_, v_target_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_325_, lean_object* v_x_326_, lean_object* v_x_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1_spec__2_spec__5___redArg(v_x_326_, v_x_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_getInitialId(lean_object* v_a_329_, lean_object* v_a_330_){
_start:
{
lean_object* v_initialId_331_; lean_object* v___x_332_; 
v_initialId_331_ = lean_ctor_get(v_a_329_, 1);
lean_inc(v_initialId_331_);
v___x_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_332_, 0, v_initialId_331_);
lean_ctor_set(v___x_332_, 1, v_a_330_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_getInitialId___boxed(lean_object* v_a_333_, lean_object* v_a_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_getInitialId(v_a_333_, v_a_334_);
lean_dec_ref(v_a_333_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_getEmptyId(lean_object* v_a_336_, lean_object* v_a_337_){
_start:
{
lean_object* v_addEmptyId_338_; lean_object* v___x_339_; 
v_addEmptyId_338_ = lean_ctor_get(v_a_336_, 2);
lean_inc(v_addEmptyId_338_);
v___x_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_339_, 0, v_addEmptyId_338_);
lean_ctor_set(v___x_339_, 1, v_a_337_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_getEmptyId___boxed(lean_object* v_a_340_, lean_object* v_a_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_getEmptyId(v_a_340_, v_a_341_);
lean_dec_ref(v_a_340_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_M_idIndex(lean_object* v_id_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
lean_object* v_initialId_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v_initialId_346_ = lean_ctor_get(v_a_344_, 1);
v___x_347_ = lean_nat_sub(v_id_343_, v_initialId_346_);
v___x_348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
lean_ctor_set(v___x_348_, 1, v_a_345_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_M_idIndex___boxed(lean_object* v_id_349_, lean_object* v_a_350_, lean_object* v_a_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l___private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_M_idIndex(v_id_349_, v_a_350_, v_a_351_);
lean_dec_ref(v_a_350_);
lean_dec(v_id_349_);
return v_res_352_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_getProofStep___closed__1(void){
_start:
{
lean_object* v___x_354_; lean_object* v___f_355_; 
v___x_354_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_355_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_355_, 0, v___x_354_);
return v___f_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_getProofStep(lean_object* v_id_356_, lean_object* v_a_357_, lean_object* v_a_358_){
_start:
{
lean_object* v_proof_359_; lean_object* v___f_360_; lean_object* v___f_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v_proof_359_ = lean_ctor_get(v_a_357_, 0);
v___f_360_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_getProofStep___closed__0));
v___f_361_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_getProofStep___closed__1, &l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_getProofStep___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_getProofStep___closed__1);
v___x_362_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_361_, v___f_360_, v_proof_359_, v_id_356_);
v___x_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
lean_ctor_set(v___x_363_, 1, v_a_358_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_getProofStep___boxed(lean_object* v_id_364_, lean_object* v_a_365_, lean_object* v_a_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_getProofStep(v_id_364_, v_a_365_, v_a_366_);
lean_dec_ref(v_a_365_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_isUsed(lean_object* v_id_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
uint8_t v___y_372_; lean_object* v_initialId_377_; lean_object* v_used_378_; lean_object* v___x_379_; lean_object* v___x_380_; uint8_t v___x_381_; 
v_initialId_377_ = lean_ctor_get(v_a_369_, 1);
v_used_378_ = lean_ctor_get(v_a_370_, 0);
v___x_379_ = lean_nat_sub(v_id_368_, v_initialId_377_);
v___x_380_ = lean_byte_array_size(v_used_378_);
v___x_381_ = lean_nat_dec_lt(v___x_379_, v___x_380_);
if (v___x_381_ == 0)
{
uint8_t v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; uint8_t v___x_385_; 
lean_dec(v___x_379_);
v___x_382_ = l_instInhabitedUInt8;
v___x_383_ = lean_box(v___x_382_);
v___x_384_ = l_outOfBounds___redArg(v___x_383_);
lean_dec(v___x_383_);
v___x_385_ = lean_unbox(v___x_384_);
lean_dec(v___x_384_);
v___y_372_ = v___x_385_;
goto v___jp_371_;
}
else
{
uint8_t v___x_386_; 
v___x_386_ = lean_byte_array_fget(v_used_378_, v___x_379_);
lean_dec(v___x_379_);
v___y_372_ = v___x_386_;
goto v___jp_371_;
}
v___jp_371_:
{
uint8_t v___x_373_; uint8_t v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_373_ = 1;
v___x_374_ = lean_uint8_dec_eq(v___y_372_, v___x_373_);
v___x_375_ = lean_box(v___x_374_);
v___x_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
lean_ctor_set(v___x_376_, 1, v_a_370_);
return v___x_376_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_isUsed___boxed(lean_object* v_id_387_, lean_object* v_a_388_, lean_object* v_a_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_isUsed(v_id_387_, v_a_388_, v_a_389_);
lean_dec_ref(v_a_388_);
lean_dec(v_id_387_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_markUsed(lean_object* v_id_391_, lean_object* v_a_392_, lean_object* v_a_393_){
_start:
{
lean_object* v_initialId_394_; uint8_t v___x_395_; 
v_initialId_394_ = lean_ctor_get(v_a_392_, 1);
v___x_395_ = lean_nat_dec_le(v_initialId_394_, v_id_391_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = lean_box(0);
v___x_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
lean_ctor_set(v___x_397_, 1, v_a_393_);
return v___x_397_;
}
else
{
lean_object* v_used_398_; lean_object* v_mapped_399_; lean_object* v_lastUse_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_412_; 
v_used_398_ = lean_ctor_get(v_a_393_, 0);
v_mapped_399_ = lean_ctor_get(v_a_393_, 1);
v_lastUse_400_ = lean_ctor_get(v_a_393_, 2);
v_isSharedCheck_412_ = !lean_is_exclusive(v_a_393_);
if (v_isSharedCheck_412_ == 0)
{
v___x_402_ = v_a_393_;
v_isShared_403_ = v_isSharedCheck_412_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_lastUse_400_);
lean_inc(v_mapped_399_);
lean_inc(v_used_398_);
lean_dec(v_a_393_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_412_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_404_; lean_object* v___x_405_; uint8_t v___x_406_; lean_object* v___x_407_; lean_object* v___x_409_; 
v___x_404_ = lean_nat_sub(v_id_391_, v_initialId_394_);
v___x_405_ = lean_box(0);
v___x_406_ = 1;
v___x_407_ = lean_byte_array_set(v_used_398_, v___x_404_, v___x_406_);
lean_dec(v___x_404_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 0, v___x_407_);
v___x_409_ = v___x_402_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_407_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v_mapped_399_);
lean_ctor_set(v_reuseFailAlloc_411_, 2, v_lastUse_400_);
v___x_409_ = v_reuseFailAlloc_411_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
lean_object* v___x_410_; 
v___x_410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_410_, 0, v___x_405_);
lean_ctor_set(v___x_410_, 1, v___x_409_);
return v___x_410_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_markUsed___boxed(lean_object* v_id_413_, lean_object* v_a_414_, lean_object* v_a_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_markUsed(v_id_413_, v_a_414_, v_a_415_);
lean_dec_ref(v_a_414_);
lean_dec(v_id_413_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_registerIdMap(lean_object* v_oldId_417_, lean_object* v_newId_418_, lean_object* v_a_419_, lean_object* v_a_420_){
_start:
{
lean_object* v_initialId_421_; lean_object* v_used_422_; lean_object* v_mapped_423_; lean_object* v_lastUse_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_435_; 
v_initialId_421_ = lean_ctor_get(v_a_419_, 1);
v_used_422_ = lean_ctor_get(v_a_420_, 0);
v_mapped_423_ = lean_ctor_get(v_a_420_, 1);
v_lastUse_424_ = lean_ctor_get(v_a_420_, 2);
v_isSharedCheck_435_ = !lean_is_exclusive(v_a_420_);
if (v_isSharedCheck_435_ == 0)
{
v___x_426_ = v_a_420_;
v_isShared_427_ = v_isSharedCheck_435_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_lastUse_424_);
lean_inc(v_mapped_423_);
lean_inc(v_used_422_);
lean_dec(v_a_420_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_435_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_432_; 
v___x_428_ = lean_nat_sub(v_oldId_417_, v_initialId_421_);
v___x_429_ = lean_box(0);
v___x_430_ = lean_array_set(v_mapped_423_, v___x_428_, v_newId_418_);
lean_dec(v___x_428_);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 1, v___x_430_);
v___x_432_ = v___x_426_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_used_422_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v___x_430_);
lean_ctor_set(v_reuseFailAlloc_434_, 2, v_lastUse_424_);
v___x_432_ = v_reuseFailAlloc_434_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
lean_object* v___x_433_; 
v___x_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_433_, 0, v___x_429_);
lean_ctor_set(v___x_433_, 1, v___x_432_);
return v___x_433_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_registerIdMap___boxed(lean_object* v_oldId_436_, lean_object* v_newId_437_, lean_object* v_a_438_, lean_object* v_a_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_registerIdMap(v_oldId_436_, v_newId_437_, v_a_438_, v_a_439_);
lean_dec_ref(v_a_438_);
lean_dec(v_oldId_436_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_updateLastUse___redArg(lean_object* v_hint_441_, lean_object* v_user_442_, lean_object* v_a_443_){
_start:
{
lean_object* v_used_444_; lean_object* v_mapped_445_; lean_object* v_lastUse_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_462_; 
v_used_444_ = lean_ctor_get(v_a_443_, 0);
v_mapped_445_ = lean_ctor_get(v_a_443_, 1);
v_lastUse_446_ = lean_ctor_get(v_a_443_, 2);
v_isSharedCheck_462_ = !lean_is_exclusive(v_a_443_);
if (v_isSharedCheck_462_ == 0)
{
v___x_448_ = v_a_443_;
v_isShared_449_ = v_isSharedCheck_462_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_lastUse_446_);
lean_inc(v_mapped_445_);
lean_inc(v_used_444_);
lean_dec(v_a_443_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_462_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___y_453_; lean_object* v_prev_459_; lean_object* v___x_460_; uint8_t v___x_461_; 
v___x_450_ = l_Int_instInhabited;
v___x_451_ = lean_box(0);
v_prev_459_ = lean_array_get_borrowed(v___x_450_, v_lastUse_446_, v_hint_441_);
v___x_460_ = lean_nat_to_int(v_user_442_);
v___x_461_ = lean_int_dec_le(v_prev_459_, v___x_460_);
if (v___x_461_ == 0)
{
lean_dec(v___x_460_);
lean_inc(v_prev_459_);
v___y_453_ = v_prev_459_;
goto v___jp_452_;
}
else
{
v___y_453_ = v___x_460_;
goto v___jp_452_;
}
v___jp_452_:
{
lean_object* v___x_454_; lean_object* v___x_456_; 
v___x_454_ = lean_array_set(v_lastUse_446_, v_hint_441_, v___y_453_);
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 2, v___x_454_);
v___x_456_ = v___x_448_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_used_444_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v_mapped_445_);
lean_ctor_set(v_reuseFailAlloc_458_, 2, v___x_454_);
v___x_456_ = v_reuseFailAlloc_458_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
lean_object* v___x_457_; 
v___x_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_457_, 0, v___x_451_);
lean_ctor_set(v___x_457_, 1, v___x_456_);
return v___x_457_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_updateLastUse___redArg___boxed(lean_object* v_hint_463_, lean_object* v_user_464_, lean_object* v_a_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_updateLastUse___redArg(v_hint_463_, v_user_464_, v_a_465_);
lean_dec(v_hint_463_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_updateLastUse(lean_object* v_hint_467_, lean_object* v_user_468_, lean_object* v_a_469_, lean_object* v_a_470_){
_start:
{
lean_object* v_used_471_; lean_object* v_mapped_472_; lean_object* v_lastUse_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_489_; 
v_used_471_ = lean_ctor_get(v_a_470_, 0);
v_mapped_472_ = lean_ctor_get(v_a_470_, 1);
v_lastUse_473_ = lean_ctor_get(v_a_470_, 2);
v_isSharedCheck_489_ = !lean_is_exclusive(v_a_470_);
if (v_isSharedCheck_489_ == 0)
{
v___x_475_ = v_a_470_;
v_isShared_476_ = v_isSharedCheck_489_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_lastUse_473_);
lean_inc(v_mapped_472_);
lean_inc(v_used_471_);
lean_dec(v_a_470_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_489_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___y_480_; lean_object* v_prev_486_; lean_object* v___x_487_; uint8_t v___x_488_; 
v___x_477_ = l_Int_instInhabited;
v___x_478_ = lean_box(0);
v_prev_486_ = lean_array_get_borrowed(v___x_477_, v_lastUse_473_, v_hint_467_);
v___x_487_ = lean_nat_to_int(v_user_468_);
v___x_488_ = lean_int_dec_le(v_prev_486_, v___x_487_);
if (v___x_488_ == 0)
{
lean_dec(v___x_487_);
lean_inc(v_prev_486_);
v___y_480_ = v_prev_486_;
goto v___jp_479_;
}
else
{
v___y_480_ = v___x_487_;
goto v___jp_479_;
}
v___jp_479_:
{
lean_object* v___x_481_; lean_object* v___x_483_; 
v___x_481_ = lean_array_set(v_lastUse_473_, v_hint_467_, v___y_480_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 2, v___x_481_);
v___x_483_ = v___x_475_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_used_471_);
lean_ctor_set(v_reuseFailAlloc_485_, 1, v_mapped_472_);
lean_ctor_set(v_reuseFailAlloc_485_, 2, v___x_481_);
v___x_483_ = v_reuseFailAlloc_485_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
lean_object* v___x_484_; 
v___x_484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_484_, 0, v___x_478_);
lean_ctor_set(v___x_484_, 1, v___x_483_);
return v___x_484_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_updateLastUse___boxed(lean_object* v_hint_490_, lean_object* v_user_491_, lean_object* v_a_492_, lean_object* v_a_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_updateLastUse(v_hint_490_, v_user_491_, v_a_492_, v_a_493_);
lean_dec_ref(v_a_492_);
lean_dec(v_hint_490_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapIdent(lean_object* v_ident_495_, lean_object* v_a_496_, lean_object* v_a_497_){
_start:
{
lean_object* v_initialId_498_; uint8_t v___x_499_; 
v_initialId_498_ = lean_ctor_get(v_a_496_, 1);
v___x_499_ = lean_nat_dec_lt(v_ident_495_, v_initialId_498_);
if (v___x_499_ == 0)
{
lean_object* v_mapped_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v_mapped_500_ = lean_ctor_get(v_a_497_, 1);
v___x_501_ = lean_nat_sub(v_ident_495_, v_initialId_498_);
lean_dec(v_ident_495_);
v___x_502_ = lean_unsigned_to_nat(0u);
v___x_503_ = lean_array_get(v___x_502_, v_mapped_500_, v___x_501_);
lean_dec(v___x_501_);
v___x_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
lean_ctor_set(v___x_504_, 1, v_a_497_);
return v___x_504_;
}
else
{
lean_object* v___x_505_; 
v___x_505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_505_, 0, v_ident_495_);
lean_ctor_set(v___x_505_, 1, v_a_497_);
return v___x_505_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapIdent___boxed(lean_object* v_ident_506_, lean_object* v_a_507_, lean_object* v_a_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapIdent(v_ident_506_, v_a_507_, v_a_508_);
lean_dec_ref(v_a_507_);
return v_res_509_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__7(void){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default(lean_box(0), lean_box(0));
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2(lean_object* v_msg_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
lean_object* v___f_521_; lean_object* v___f_522_; lean_object* v___f_523_; lean_object* v___f_524_; lean_object* v___f_525_; lean_object* v___f_526_; lean_object* v___f_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___f_531_; lean_object* v___f_532_; lean_object* v___f_533_; lean_object* v___f_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___f_543_; lean_object* v___x_4260__overap_544_; lean_object* v___x_545_; 
v___f_521_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__0));
v___f_522_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__1));
v___f_523_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__2));
v___f_524_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__3));
v___f_525_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__4));
v___f_526_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__5));
v___f_527_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__6));
v___x_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_528_, 0, v___f_521_);
lean_ctor_set(v___x_528_, 1, v___f_522_);
v___x_529_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
lean_ctor_set(v___x_529_, 1, v___f_523_);
lean_ctor_set(v___x_529_, 2, v___f_524_);
lean_ctor_set(v___x_529_, 3, v___f_525_);
lean_ctor_set(v___x_529_, 4, v___f_526_);
v___x_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
lean_ctor_set(v___x_530_, 1, v___f_527_);
lean_inc_ref_n(v___x_530_, 6);
v___f_531_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_531_, 0, v___x_530_);
v___f_532_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_532_, 0, v___x_530_);
v___f_533_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_533_, 0, v___x_530_);
v___f_534_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_534_, 0, v___x_530_);
v___x_535_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_535_, 0, lean_box(0));
lean_closure_set(v___x_535_, 1, lean_box(0));
lean_closure_set(v___x_535_, 2, v___x_530_);
v___x_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_535_);
lean_ctor_set(v___x_536_, 1, v___f_531_);
v___x_537_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_537_, 0, lean_box(0));
lean_closure_set(v___x_537_, 1, lean_box(0));
lean_closure_set(v___x_537_, 2, v___x_530_);
v___x_538_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_538_, 0, v___x_536_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
lean_ctor_set(v___x_538_, 2, v___f_532_);
lean_ctor_set(v___x_538_, 3, v___f_533_);
lean_ctor_set(v___x_538_, 4, v___f_534_);
v___x_539_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_539_, 0, lean_box(0));
lean_closure_set(v___x_539_, 1, lean_box(0));
lean_closure_set(v___x_539_, 2, v___x_530_);
v___x_540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_540_, 0, v___x_538_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
v___x_541_ = lean_obj_once(&l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__7, &l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__7_once, _init_l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__7);
v___x_542_ = l_instInhabitedOfMonad___redArg(v___x_540_, v___x_541_);
v___f_543_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_543_, 0, v___x_542_);
v___x_4260__overap_544_ = lean_panic_fn_borrowed(v___f_543_, v_msg_518_);
lean_dec_ref(v___f_543_);
lean_inc_ref(v___y_519_);
v___x_545_ = lean_apply_2(v___x_4260__overap_544_, v___y_519_, v___y_520_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___boxed(lean_object* v_msg_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2(v_msg_546_, v___y_547_, v___y_548_);
lean_dec_ref(v___y_547_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__0(size_t v_sz_550_, size_t v_i_551_, lean_object* v_bs_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
uint8_t v___x_555_; 
v___x_555_ = lean_usize_dec_lt(v_i_551_, v_sz_550_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; 
v___x_556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_556_, 0, v_bs_552_);
lean_ctor_set(v___x_556_, 1, v___y_554_);
return v___x_556_;
}
else
{
lean_object* v_initialId_557_; lean_object* v_v_558_; lean_object* v___x_559_; lean_object* v_bs_x27_560_; lean_object* v_fst_562_; lean_object* v_snd_563_; uint8_t v___x_568_; 
v_initialId_557_ = lean_ctor_get(v___y_553_, 1);
v_v_558_ = lean_array_uget(v_bs_552_, v_i_551_);
v___x_559_ = lean_unsigned_to_nat(0u);
v_bs_x27_560_ = lean_array_uset(v_bs_552_, v_i_551_, v___x_559_);
v___x_568_ = lean_nat_dec_lt(v_v_558_, v_initialId_557_);
if (v___x_568_ == 0)
{
lean_object* v_mapped_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v_mapped_569_ = lean_ctor_get(v___y_554_, 1);
v___x_570_ = lean_nat_sub(v_v_558_, v_initialId_557_);
lean_dec(v_v_558_);
v___x_571_ = lean_array_get(v___x_559_, v_mapped_569_, v___x_570_);
lean_dec(v___x_570_);
v_fst_562_ = v___x_571_;
v_snd_563_ = v___y_554_;
goto v___jp_561_;
}
else
{
v_fst_562_ = v_v_558_;
v_snd_563_ = v___y_554_;
goto v___jp_561_;
}
v___jp_561_:
{
size_t v___x_564_; size_t v___x_565_; lean_object* v___x_566_; 
v___x_564_ = ((size_t)1ULL);
v___x_565_ = lean_usize_add(v_i_551_, v___x_564_);
v___x_566_ = lean_array_uset(v_bs_x27_560_, v_i_551_, v_fst_562_);
v_i_551_ = v___x_565_;
v_bs_552_ = v___x_566_;
v___y_554_ = v_snd_563_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__0___boxed(lean_object* v_sz_572_, lean_object* v_i_573_, lean_object* v_bs_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
size_t v_sz_boxed_577_; size_t v_i_boxed_578_; lean_object* v_res_579_; 
v_sz_boxed_577_ = lean_unbox_usize(v_sz_572_);
lean_dec(v_sz_572_);
v_i_boxed_578_ = lean_unbox_usize(v_i_573_);
lean_dec(v_i_573_);
v_res_579_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__0(v_sz_boxed_577_, v_i_boxed_578_, v_bs_574_, v___y_575_, v___y_576_);
lean_dec_ref(v___y_575_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__1(size_t v_sz_580_, size_t v_i_581_, lean_object* v_bs_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
uint8_t v___x_585_; 
v___x_585_ = lean_usize_dec_lt(v_i_581_, v_sz_580_);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; 
v___x_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_586_, 0, v_bs_582_);
lean_ctor_set(v___x_586_, 1, v___y_584_);
return v___x_586_;
}
else
{
lean_object* v_v_587_; lean_object* v_fst_588_; lean_object* v_initialId_589_; lean_object* v___x_590_; lean_object* v_bs_x27_591_; lean_object* v_fst_593_; lean_object* v_snd_594_; uint8_t v___x_612_; 
v_v_587_ = lean_array_uget(v_bs_582_, v_i_581_);
v_fst_588_ = lean_ctor_get(v_v_587_, 0);
v_initialId_589_ = lean_ctor_get(v___y_583_, 1);
v___x_590_ = lean_unsigned_to_nat(0u);
v_bs_x27_591_ = lean_array_uset(v_bs_582_, v_i_581_, v___x_590_);
v___x_612_ = lean_nat_dec_lt(v_fst_588_, v_initialId_589_);
if (v___x_612_ == 0)
{
lean_object* v_mapped_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v_mapped_613_ = lean_ctor_get(v___y_584_, 1);
v___x_614_ = lean_nat_sub(v_fst_588_, v_initialId_589_);
v___x_615_ = lean_array_get(v___x_590_, v_mapped_613_, v___x_614_);
lean_dec(v___x_614_);
v_fst_593_ = v___x_615_;
v_snd_594_ = v___y_584_;
goto v___jp_592_;
}
else
{
lean_inc(v_fst_588_);
v_fst_593_ = v_fst_588_;
v_snd_594_ = v___y_584_;
goto v___jp_592_;
}
v___jp_592_:
{
lean_object* v_snd_595_; size_t v_sz_596_; size_t v___x_597_; lean_object* v___x_598_; lean_object* v_fst_599_; lean_object* v_snd_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_611_; 
v_snd_595_ = lean_ctor_get(v_v_587_, 1);
lean_inc(v_snd_595_);
lean_dec(v_v_587_);
v_sz_596_ = lean_array_size(v_snd_595_);
v___x_597_ = ((size_t)0ULL);
v___x_598_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__0(v_sz_596_, v___x_597_, v_snd_595_, v___y_583_, v_snd_594_);
v_fst_599_ = lean_ctor_get(v___x_598_, 0);
v_snd_600_ = lean_ctor_get(v___x_598_, 1);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_611_ == 0)
{
v___x_602_ = v___x_598_;
v_isShared_603_ = v_isSharedCheck_611_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_snd_600_);
lean_inc(v_fst_599_);
lean_dec(v___x_598_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_611_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_605_; 
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 1, v_fst_599_);
lean_ctor_set(v___x_602_, 0, v_fst_593_);
v___x_605_ = v___x_602_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_fst_593_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_fst_599_);
v___x_605_ = v_reuseFailAlloc_610_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
size_t v___x_606_; size_t v___x_607_; lean_object* v___x_608_; 
v___x_606_ = ((size_t)1ULL);
v___x_607_ = lean_usize_add(v_i_581_, v___x_606_);
v___x_608_ = lean_array_uset(v_bs_x27_591_, v_i_581_, v___x_605_);
v_i_581_ = v___x_607_;
v_bs_582_ = v___x_608_;
v___y_584_ = v_snd_600_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__1___boxed(lean_object* v_sz_616_, lean_object* v_i_617_, lean_object* v_bs_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
size_t v_sz_boxed_621_; size_t v_i_boxed_622_; lean_object* v_res_623_; 
v_sz_boxed_621_ = lean_unbox_usize(v_sz_616_);
lean_dec(v_sz_616_);
v_i_boxed_622_ = lean_unbox_usize(v_i_617_);
lean_dec(v_i_617_);
v_res_623_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__1(v_sz_boxed_621_, v_i_boxed_622_, v_bs_618_, v___y_619_, v___y_620_);
lean_dec_ref(v___y_619_);
return v_res_623_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__3(void){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_627_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__2));
v___x_628_ = lean_unsigned_to_nat(15u);
v___x_629_ = lean_unsigned_to_nat(166u);
v___x_630_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__1));
v___x_631_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__0));
v___x_632_ = l_mkPanicMessageWithDecl(v___x_631_, v___x_630_, v___x_629_, v___x_628_, v___x_627_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep(lean_object* v_step_633_, lean_object* v_a_634_, lean_object* v_a_635_){
_start:
{
switch(lean_obj_tag(v_step_633_))
{
case 0:
{
lean_object* v_id_636_; lean_object* v_rupHints_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_665_; 
v_id_636_ = lean_ctor_get(v_step_633_, 0);
v_rupHints_637_ = lean_ctor_get(v_step_633_, 1);
v_isSharedCheck_665_ = !lean_is_exclusive(v_step_633_);
if (v_isSharedCheck_665_ == 0)
{
v___x_639_ = v_step_633_;
v_isShared_640_ = v_isSharedCheck_665_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_rupHints_637_);
lean_inc(v_id_636_);
lean_dec(v_step_633_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_665_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v_fst_642_; lean_object* v_snd_643_; lean_object* v_initialId_659_; uint8_t v___x_660_; 
v_initialId_659_ = lean_ctor_get(v_a_634_, 1);
v___x_660_ = lean_nat_dec_lt(v_id_636_, v_initialId_659_);
if (v___x_660_ == 0)
{
lean_object* v_mapped_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v_mapped_661_ = lean_ctor_get(v_a_635_, 1);
v___x_662_ = lean_nat_sub(v_id_636_, v_initialId_659_);
lean_dec(v_id_636_);
v___x_663_ = lean_unsigned_to_nat(0u);
v___x_664_ = lean_array_get(v___x_663_, v_mapped_661_, v___x_662_);
lean_dec(v___x_662_);
v_fst_642_ = v___x_664_;
v_snd_643_ = v_a_635_;
goto v___jp_641_;
}
else
{
v_fst_642_ = v_id_636_;
v_snd_643_ = v_a_635_;
goto v___jp_641_;
}
v___jp_641_:
{
size_t v_sz_644_; size_t v___x_645_; lean_object* v___x_646_; lean_object* v_fst_647_; lean_object* v_snd_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_658_; 
v_sz_644_ = lean_array_size(v_rupHints_637_);
v___x_645_ = ((size_t)0ULL);
v___x_646_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__0(v_sz_644_, v___x_645_, v_rupHints_637_, v_a_634_, v_snd_643_);
v_fst_647_ = lean_ctor_get(v___x_646_, 0);
v_snd_648_ = lean_ctor_get(v___x_646_, 1);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_658_ == 0)
{
v___x_650_ = v___x_646_;
v_isShared_651_ = v_isSharedCheck_658_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_snd_648_);
lean_inc(v_fst_647_);
lean_dec(v___x_646_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_658_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_653_; 
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 1, v_fst_647_);
lean_ctor_set(v___x_639_, 0, v_fst_642_);
v___x_653_ = v___x_639_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_fst_642_);
lean_ctor_set(v_reuseFailAlloc_657_, 1, v_fst_647_);
v___x_653_ = v_reuseFailAlloc_657_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
lean_object* v___x_655_; 
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 0, v___x_653_);
v___x_655_ = v___x_650_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v___x_653_);
lean_ctor_set(v_reuseFailAlloc_656_, 1, v_snd_648_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
}
}
}
case 1:
{
lean_object* v_id_666_; lean_object* v_c_667_; lean_object* v_rupHints_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_696_; 
v_id_666_ = lean_ctor_get(v_step_633_, 0);
v_c_667_ = lean_ctor_get(v_step_633_, 1);
v_rupHints_668_ = lean_ctor_get(v_step_633_, 2);
v_isSharedCheck_696_ = !lean_is_exclusive(v_step_633_);
if (v_isSharedCheck_696_ == 0)
{
v___x_670_ = v_step_633_;
v_isShared_671_ = v_isSharedCheck_696_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_rupHints_668_);
lean_inc(v_c_667_);
lean_inc(v_id_666_);
lean_dec(v_step_633_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_696_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v_fst_673_; lean_object* v_snd_674_; lean_object* v_initialId_690_; uint8_t v___x_691_; 
v_initialId_690_ = lean_ctor_get(v_a_634_, 1);
v___x_691_ = lean_nat_dec_lt(v_id_666_, v_initialId_690_);
if (v___x_691_ == 0)
{
lean_object* v_mapped_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v_mapped_692_ = lean_ctor_get(v_a_635_, 1);
v___x_693_ = lean_nat_sub(v_id_666_, v_initialId_690_);
lean_dec(v_id_666_);
v___x_694_ = lean_unsigned_to_nat(0u);
v___x_695_ = lean_array_get(v___x_694_, v_mapped_692_, v___x_693_);
lean_dec(v___x_693_);
v_fst_673_ = v___x_695_;
v_snd_674_ = v_a_635_;
goto v___jp_672_;
}
else
{
v_fst_673_ = v_id_666_;
v_snd_674_ = v_a_635_;
goto v___jp_672_;
}
v___jp_672_:
{
size_t v_sz_675_; size_t v___x_676_; lean_object* v___x_677_; lean_object* v_fst_678_; lean_object* v_snd_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_689_; 
v_sz_675_ = lean_array_size(v_rupHints_668_);
v___x_676_ = ((size_t)0ULL);
v___x_677_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__0(v_sz_675_, v___x_676_, v_rupHints_668_, v_a_634_, v_snd_674_);
v_fst_678_ = lean_ctor_get(v___x_677_, 0);
v_snd_679_ = lean_ctor_get(v___x_677_, 1);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_689_ == 0)
{
v___x_681_ = v___x_677_;
v_isShared_682_ = v_isSharedCheck_689_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_snd_679_);
lean_inc(v_fst_678_);
lean_dec(v___x_677_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_689_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 2, v_fst_678_);
lean_ctor_set(v___x_670_, 0, v_fst_673_);
v___x_684_ = v___x_670_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_fst_673_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v_c_667_);
lean_ctor_set(v_reuseFailAlloc_688_, 2, v_fst_678_);
v___x_684_ = v_reuseFailAlloc_688_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
lean_object* v___x_686_; 
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 0, v___x_684_);
v___x_686_ = v___x_681_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_684_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v_snd_679_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
}
}
case 2:
{
lean_object* v_id_697_; lean_object* v_c_698_; lean_object* v_pivot_699_; lean_object* v_rupHints_700_; lean_object* v_ratHints_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_733_; 
v_id_697_ = lean_ctor_get(v_step_633_, 0);
v_c_698_ = lean_ctor_get(v_step_633_, 1);
v_pivot_699_ = lean_ctor_get(v_step_633_, 2);
v_rupHints_700_ = lean_ctor_get(v_step_633_, 3);
v_ratHints_701_ = lean_ctor_get(v_step_633_, 4);
v_isSharedCheck_733_ = !lean_is_exclusive(v_step_633_);
if (v_isSharedCheck_733_ == 0)
{
v___x_703_ = v_step_633_;
v_isShared_704_ = v_isSharedCheck_733_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_ratHints_701_);
lean_inc(v_rupHints_700_);
lean_inc(v_pivot_699_);
lean_inc(v_c_698_);
lean_inc(v_id_697_);
lean_dec(v_step_633_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_733_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v_fst_706_; lean_object* v_snd_707_; lean_object* v_initialId_727_; uint8_t v___x_728_; 
v_initialId_727_ = lean_ctor_get(v_a_634_, 1);
v___x_728_ = lean_nat_dec_lt(v_id_697_, v_initialId_727_);
if (v___x_728_ == 0)
{
lean_object* v_mapped_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v_mapped_729_ = lean_ctor_get(v_a_635_, 1);
v___x_730_ = lean_nat_sub(v_id_697_, v_initialId_727_);
lean_dec(v_id_697_);
v___x_731_ = lean_unsigned_to_nat(0u);
v___x_732_ = lean_array_get(v___x_731_, v_mapped_729_, v___x_730_);
lean_dec(v___x_730_);
v_fst_706_ = v___x_732_;
v_snd_707_ = v_a_635_;
goto v___jp_705_;
}
else
{
v_fst_706_ = v_id_697_;
v_snd_707_ = v_a_635_;
goto v___jp_705_;
}
v___jp_705_:
{
size_t v_sz_708_; size_t v___x_709_; lean_object* v___x_710_; lean_object* v_fst_711_; lean_object* v_snd_712_; size_t v_sz_713_; lean_object* v___x_714_; lean_object* v_fst_715_; lean_object* v_snd_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_726_; 
v_sz_708_ = lean_array_size(v_rupHints_700_);
v___x_709_ = ((size_t)0ULL);
v___x_710_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__0(v_sz_708_, v___x_709_, v_rupHints_700_, v_a_634_, v_snd_707_);
v_fst_711_ = lean_ctor_get(v___x_710_, 0);
lean_inc(v_fst_711_);
v_snd_712_ = lean_ctor_get(v___x_710_, 1);
lean_inc(v_snd_712_);
lean_dec_ref(v___x_710_);
v_sz_713_ = lean_array_size(v_ratHints_701_);
v___x_714_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__1(v_sz_713_, v___x_709_, v_ratHints_701_, v_a_634_, v_snd_712_);
v_fst_715_ = lean_ctor_get(v___x_714_, 0);
v_snd_716_ = lean_ctor_get(v___x_714_, 1);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_726_ == 0)
{
v___x_718_ = v___x_714_;
v_isShared_719_ = v_isSharedCheck_726_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_snd_716_);
lean_inc(v_fst_715_);
lean_dec(v___x_714_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_726_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_721_; 
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 4, v_fst_715_);
lean_ctor_set(v___x_703_, 3, v_fst_711_);
lean_ctor_set(v___x_703_, 0, v_fst_706_);
v___x_721_ = v___x_703_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_fst_706_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v_c_698_);
lean_ctor_set(v_reuseFailAlloc_725_, 2, v_pivot_699_);
lean_ctor_set(v_reuseFailAlloc_725_, 3, v_fst_711_);
lean_ctor_set(v_reuseFailAlloc_725_, 4, v_fst_715_);
v___x_721_ = v_reuseFailAlloc_725_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
lean_object* v___x_723_; 
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 0, v___x_721_);
v___x_723_ = v___x_718_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_721_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v_snd_716_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_734_; lean_object* v___x_735_; 
lean_dec_ref(v_step_633_);
v___x_734_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__3, &l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__3);
v___x_735_ = l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2(v___x_734_, v_a_634_, v_a_635_);
return v___x_735_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep___boxed(lean_object* v_step_736_, lean_object* v_a_737_, lean_object* v_a_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep(v_step_736_, v_a_737_, v_a_738_);
lean_dec_ref(v_a_737_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__0(lean_object* v_a_740_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = lean_nat_to_int(v_a_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__3___redArg(lean_object* v_id_742_, lean_object* v_as_743_, size_t v_sz_744_, size_t v_i_745_, lean_object* v_b_746_, lean_object* v___y_747_){
_start:
{
uint8_t v___x_748_; 
v___x_748_ = lean_usize_dec_lt(v_i_745_, v_sz_744_);
if (v___x_748_ == 0)
{
lean_object* v___x_749_; 
lean_dec(v_id_742_);
v___x_749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_749_, 0, v_b_746_);
lean_ctor_set(v___x_749_, 1, v___y_747_);
return v___x_749_;
}
else
{
lean_object* v_used_750_; lean_object* v_mapped_751_; lean_object* v_lastUse_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_771_; 
v_used_750_ = lean_ctor_get(v___y_747_, 0);
v_mapped_751_ = lean_ctor_get(v___y_747_, 1);
v_lastUse_752_ = lean_ctor_get(v___y_747_, 2);
v_isSharedCheck_771_ = !lean_is_exclusive(v___y_747_);
if (v_isSharedCheck_771_ == 0)
{
v___x_754_ = v___y_747_;
v_isShared_755_ = v_isSharedCheck_771_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_lastUse_752_);
lean_inc(v_mapped_751_);
lean_inc(v_used_750_);
lean_dec(v___y_747_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_771_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_756_; lean_object* v_a_757_; lean_object* v___y_759_; lean_object* v___x_767_; lean_object* v_prev_768_; lean_object* v___x_769_; uint8_t v___x_770_; 
v___x_756_ = lean_box(0);
v_a_757_ = lean_array_uget_borrowed(v_as_743_, v_i_745_);
v___x_767_ = l_Int_instInhabited;
v_prev_768_ = lean_array_get_borrowed(v___x_767_, v_lastUse_752_, v_a_757_);
lean_inc(v_id_742_);
v___x_769_ = lean_nat_to_int(v_id_742_);
v___x_770_ = lean_int_dec_le(v_prev_768_, v___x_769_);
if (v___x_770_ == 0)
{
lean_dec(v___x_769_);
lean_inc(v_prev_768_);
v___y_759_ = v_prev_768_;
goto v___jp_758_;
}
else
{
v___y_759_ = v___x_769_;
goto v___jp_758_;
}
v___jp_758_:
{
lean_object* v___x_760_; lean_object* v___x_762_; 
v___x_760_ = lean_array_set(v_lastUse_752_, v_a_757_, v___y_759_);
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 2, v___x_760_);
v___x_762_ = v___x_754_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_used_750_);
lean_ctor_set(v_reuseFailAlloc_766_, 1, v_mapped_751_);
lean_ctor_set(v_reuseFailAlloc_766_, 2, v___x_760_);
v___x_762_ = v_reuseFailAlloc_766_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
size_t v___x_763_; size_t v___x_764_; 
v___x_763_ = ((size_t)1ULL);
v___x_764_ = lean_usize_add(v_i_745_, v___x_763_);
v_i_745_ = v___x_764_;
v_b_746_ = v___x_756_;
v___y_747_ = v___x_762_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__3___redArg___boxed(lean_object* v_id_772_, lean_object* v_as_773_, lean_object* v_sz_774_, lean_object* v_i_775_, lean_object* v_b_776_, lean_object* v___y_777_){
_start:
{
size_t v_sz_boxed_778_; size_t v_i_boxed_779_; lean_object* v_res_780_; 
v_sz_boxed_778_ = lean_unbox_usize(v_sz_774_);
lean_dec(v_sz_774_);
v_i_boxed_779_ = lean_unbox_usize(v_i_775_);
lean_dec(v_i_775_);
v_res_780_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__3___redArg(v_id_772_, v_as_773_, v_sz_boxed_778_, v_i_boxed_779_, v_b_776_, v___y_777_);
lean_dec_ref(v_as_773_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__5(lean_object* v_as_781_, size_t v_i_782_, size_t v_stop_783_, lean_object* v_b_784_){
_start:
{
uint8_t v___x_785_; 
v___x_785_ = lean_usize_dec_eq(v_i_782_, v_stop_783_);
if (v___x_785_ == 0)
{
lean_object* v___x_786_; lean_object* v_fst_787_; lean_object* v_snd_788_; lean_object* v___x_789_; lean_object* v___x_790_; size_t v___x_791_; size_t v___x_792_; 
v___x_786_ = lean_array_uget_borrowed(v_as_781_, v_i_782_);
v_fst_787_ = lean_ctor_get(v___x_786_, 0);
v_snd_788_ = lean_ctor_get(v___x_786_, 1);
lean_inc(v_fst_787_);
v___x_789_ = lean_array_push(v_b_784_, v_fst_787_);
v___x_790_ = l_Array_append___redArg(v___x_789_, v_snd_788_);
v___x_791_ = ((size_t)1ULL);
v___x_792_ = lean_usize_add(v_i_782_, v___x_791_);
v_i_782_ = v___x_792_;
v_b_784_ = v___x_790_;
goto _start;
}
else
{
return v_b_784_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__5___boxed(lean_object* v_as_794_, lean_object* v_i_795_, lean_object* v_stop_796_, lean_object* v_b_797_){
_start:
{
size_t v_i_boxed_798_; size_t v_stop_boxed_799_; lean_object* v_res_800_; 
v_i_boxed_798_ = lean_unbox_usize(v_i_795_);
lean_dec(v_i_795_);
v_stop_boxed_799_ = lean_unbox_usize(v_stop_796_);
lean_dec(v_stop_796_);
v_res_800_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__5(v_as_794_, v_i_boxed_798_, v_stop_boxed_799_, v_b_797_);
lean_dec_ref(v_as_794_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2___redArg(lean_object* v_id_801_, lean_object* v_as_802_, size_t v_i_803_, size_t v_stop_804_, lean_object* v_b_805_, lean_object* v___y_806_){
_start:
{
uint8_t v___x_807_; 
v___x_807_ = lean_usize_dec_eq(v_i_803_, v_stop_804_);
if (v___x_807_ == 0)
{
lean_object* v_used_808_; lean_object* v_mapped_809_; lean_object* v_lastUse_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_829_; 
v_used_808_ = lean_ctor_get(v___y_806_, 0);
v_mapped_809_ = lean_ctor_get(v___y_806_, 1);
v_lastUse_810_ = lean_ctor_get(v___y_806_, 2);
v_isSharedCheck_829_ = !lean_is_exclusive(v___y_806_);
if (v_isSharedCheck_829_ == 0)
{
v___x_812_ = v___y_806_;
v_isShared_813_ = v_isSharedCheck_829_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_lastUse_810_);
lean_inc(v_mapped_809_);
lean_inc(v_used_808_);
lean_dec(v___y_806_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_829_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___y_818_; lean_object* v_prev_826_; lean_object* v___x_827_; uint8_t v___x_828_; 
v___x_814_ = lean_array_uget_borrowed(v_as_802_, v_i_803_);
v___x_815_ = l_Int_instInhabited;
v___x_816_ = lean_box(0);
v_prev_826_ = lean_array_get_borrowed(v___x_815_, v_lastUse_810_, v___x_814_);
lean_inc(v_id_801_);
v___x_827_ = lean_nat_to_int(v_id_801_);
v___x_828_ = lean_int_dec_le(v_prev_826_, v___x_827_);
if (v___x_828_ == 0)
{
lean_dec(v___x_827_);
lean_inc(v_prev_826_);
v___y_818_ = v_prev_826_;
goto v___jp_817_;
}
else
{
v___y_818_ = v___x_827_;
goto v___jp_817_;
}
v___jp_817_:
{
lean_object* v___x_819_; lean_object* v___x_821_; 
v___x_819_ = lean_array_set(v_lastUse_810_, v___x_814_, v___y_818_);
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 2, v___x_819_);
v___x_821_ = v___x_812_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_used_808_);
lean_ctor_set(v_reuseFailAlloc_825_, 1, v_mapped_809_);
lean_ctor_set(v_reuseFailAlloc_825_, 2, v___x_819_);
v___x_821_ = v_reuseFailAlloc_825_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
size_t v___x_822_; size_t v___x_823_; 
v___x_822_ = ((size_t)1ULL);
v___x_823_ = lean_usize_add(v_i_803_, v___x_822_);
v_i_803_ = v___x_823_;
v_b_805_ = v___x_816_;
v___y_806_ = v___x_821_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_830_; 
lean_dec(v_id_801_);
v___x_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_830_, 0, v_b_805_);
lean_ctor_set(v___x_830_, 1, v___y_806_);
return v___x_830_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2___redArg___boxed(lean_object* v_id_831_, lean_object* v_as_832_, lean_object* v_i_833_, lean_object* v_stop_834_, lean_object* v_b_835_, lean_object* v___y_836_){
_start:
{
size_t v_i_boxed_837_; size_t v_stop_boxed_838_; lean_object* v_res_839_; 
v_i_boxed_837_ = lean_unbox_usize(v_i_833_);
lean_dec(v_i_833_);
v_stop_boxed_838_ = lean_unbox_usize(v_stop_834_);
lean_dec(v_stop_834_);
v_res_839_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2___redArg(v_id_831_, v_as_832_, v_i_boxed_837_, v_stop_boxed_838_, v_b_835_, v___y_836_);
lean_dec_ref(v_as_832_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__4(lean_object* v_id_840_, lean_object* v_as_841_, size_t v_i_842_, size_t v_stop_843_, lean_object* v_b_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
uint8_t v___x_847_; 
v___x_847_ = lean_usize_dec_eq(v_i_842_, v_stop_843_);
if (v___x_847_ == 0)
{
lean_object* v_used_848_; lean_object* v_mapped_849_; lean_object* v_lastUse_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_869_; 
v_used_848_ = lean_ctor_get(v___y_846_, 0);
v_mapped_849_ = lean_ctor_get(v___y_846_, 1);
v_lastUse_850_ = lean_ctor_get(v___y_846_, 2);
v_isSharedCheck_869_ = !lean_is_exclusive(v___y_846_);
if (v_isSharedCheck_869_ == 0)
{
v___x_852_ = v___y_846_;
v_isShared_853_ = v_isSharedCheck_869_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_lastUse_850_);
lean_inc(v_mapped_849_);
lean_inc(v_used_848_);
lean_dec(v___y_846_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_869_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___y_858_; lean_object* v_prev_866_; lean_object* v___x_867_; uint8_t v___x_868_; 
v___x_854_ = lean_array_uget_borrowed(v_as_841_, v_i_842_);
v___x_855_ = l_Int_instInhabited;
v___x_856_ = lean_box(0);
v_prev_866_ = lean_array_get_borrowed(v___x_855_, v_lastUse_850_, v___x_854_);
lean_inc(v_id_840_);
v___x_867_ = lean_nat_to_int(v_id_840_);
v___x_868_ = lean_int_dec_le(v_prev_866_, v___x_867_);
if (v___x_868_ == 0)
{
lean_dec(v___x_867_);
lean_inc(v_prev_866_);
v___y_858_ = v_prev_866_;
goto v___jp_857_;
}
else
{
v___y_858_ = v___x_867_;
goto v___jp_857_;
}
v___jp_857_:
{
lean_object* v___x_859_; lean_object* v___x_861_; 
v___x_859_ = lean_array_set(v_lastUse_850_, v___x_854_, v___y_858_);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 2, v___x_859_);
v___x_861_ = v___x_852_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_used_848_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v_mapped_849_);
lean_ctor_set(v_reuseFailAlloc_865_, 2, v___x_859_);
v___x_861_ = v_reuseFailAlloc_865_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
size_t v___x_862_; size_t v___x_863_; lean_object* v___x_864_; 
v___x_862_ = ((size_t)1ULL);
v___x_863_ = lean_usize_add(v_i_842_, v___x_862_);
v___x_864_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2___redArg(v_id_840_, v_as_841_, v___x_863_, v_stop_843_, v___x_856_, v___x_861_);
return v___x_864_;
}
}
}
}
else
{
lean_object* v___x_870_; 
lean_dec(v_id_840_);
v___x_870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_870_, 0, v_b_844_);
lean_ctor_set(v___x_870_, 1, v___y_846_);
return v___x_870_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__4___boxed(lean_object* v_id_871_, lean_object* v_as_872_, lean_object* v_i_873_, lean_object* v_stop_874_, lean_object* v_b_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
size_t v_i_boxed_878_; size_t v_stop_boxed_879_; lean_object* v_res_880_; 
v_i_boxed_878_ = lean_unbox_usize(v_i_873_);
lean_dec(v_i_873_);
v_stop_boxed_879_ = lean_unbox_usize(v_stop_874_);
lean_dec(v_stop_874_);
v_res_880_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__4(v_id_871_, v_as_872_, v_i_boxed_878_, v_stop_boxed_879_, v_b_875_, v___y_876_, v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec_ref(v_as_872_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1_spec__1___redArg(lean_object* v_a_881_, lean_object* v_x_882_){
_start:
{
if (lean_obj_tag(v_x_882_) == 0)
{
lean_object* v___x_883_; 
v___x_883_ = lean_box(0);
return v___x_883_;
}
else
{
lean_object* v_key_884_; lean_object* v_value_885_; lean_object* v_tail_886_; uint8_t v___x_887_; 
v_key_884_ = lean_ctor_get(v_x_882_, 0);
v_value_885_ = lean_ctor_get(v_x_882_, 1);
v_tail_886_ = lean_ctor_get(v_x_882_, 2);
v___x_887_ = lean_nat_dec_eq(v_key_884_, v_a_881_);
if (v___x_887_ == 0)
{
v_x_882_ = v_tail_886_;
goto _start;
}
else
{
lean_object* v___x_889_; 
lean_inc(v_value_885_);
v___x_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_889_, 0, v_value_885_);
return v___x_889_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1_spec__1___redArg___boxed(lean_object* v_a_890_, lean_object* v_x_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1_spec__1___redArg(v_a_890_, v_x_891_);
lean_dec(v_x_891_);
lean_dec(v_a_890_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1___redArg(lean_object* v_m_893_, lean_object* v_a_894_){
_start:
{
lean_object* v_buckets_895_; lean_object* v___x_896_; uint64_t v___x_897_; uint64_t v___x_898_; uint64_t v___x_899_; uint64_t v_fold_900_; uint64_t v___x_901_; uint64_t v___x_902_; uint64_t v___x_903_; size_t v___x_904_; size_t v___x_905_; size_t v___x_906_; size_t v___x_907_; size_t v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v_buckets_895_ = lean_ctor_get(v_m_893_, 1);
v___x_896_ = lean_array_get_size(v_buckets_895_);
v___x_897_ = lean_uint64_of_nat(v_a_894_);
v___x_898_ = 32ULL;
v___x_899_ = lean_uint64_shift_right(v___x_897_, v___x_898_);
v_fold_900_ = lean_uint64_xor(v___x_897_, v___x_899_);
v___x_901_ = 16ULL;
v___x_902_ = lean_uint64_shift_right(v_fold_900_, v___x_901_);
v___x_903_ = lean_uint64_xor(v_fold_900_, v___x_902_);
v___x_904_ = lean_uint64_to_usize(v___x_903_);
v___x_905_ = lean_usize_of_nat(v___x_896_);
v___x_906_ = ((size_t)1ULL);
v___x_907_ = lean_usize_sub(v___x_905_, v___x_906_);
v___x_908_ = lean_usize_land(v___x_904_, v___x_907_);
v___x_909_ = lean_array_uget_borrowed(v_buckets_895_, v___x_908_);
v___x_910_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1_spec__1___redArg(v_a_894_, v___x_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1___redArg___boxed(lean_object* v_m_911_, lean_object* v_a_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1___redArg(v_m_911_, v_a_912_);
lean_dec(v_a_912_);
lean_dec_ref(v_m_911_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go(lean_object* v_worklist_914_, lean_object* v_a_915_, lean_object* v_a_916_){
_start:
{
lean_object* v___x_917_; lean_object* v___x_918_; uint8_t v___x_919_; 
v___x_917_ = lean_array_get_size(v_worklist_914_);
v___x_918_ = lean_unsigned_to_nat(0u);
v___x_919_ = lean_nat_dec_eq(v___x_917_, v___x_918_);
if (v___x_919_ == 0)
{
lean_object* v_proof_920_; lean_object* v_initialId_921_; lean_object* v_used_922_; lean_object* v_mapped_923_; lean_object* v_lastUse_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v_id_927_; lean_object* v_worklist_928_; lean_object* v___y_930_; lean_object* v_snd_931_; lean_object* v___y_935_; lean_object* v___y_936_; lean_object* v___y_939_; lean_object* v_snd_940_; lean_object* v___y_944_; lean_object* v___y_945_; lean_object* v___y_948_; lean_object* v___y_949_; lean_object* v_snd_950_; lean_object* v___y_955_; lean_object* v___y_956_; lean_object* v___y_957_; lean_object* v___y_960_; size_t v___y_961_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v_snd_975_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v___y_992_; lean_object* v_snd_995_; uint8_t v___y_1035_; lean_object* v___x_1052_; lean_object* v___x_1053_; uint8_t v___x_1054_; 
v_proof_920_ = lean_ctor_get(v_a_915_, 0);
v_initialId_921_ = lean_ctor_get(v_a_915_, 1);
v_used_922_ = lean_ctor_get(v_a_916_, 0);
v_mapped_923_ = lean_ctor_get(v_a_916_, 1);
v_lastUse_924_ = lean_ctor_get(v_a_916_, 2);
v___x_925_ = lean_unsigned_to_nat(1u);
v___x_926_ = lean_nat_sub(v___x_917_, v___x_925_);
v_id_927_ = lean_array_fget(v_worklist_914_, v___x_926_);
lean_dec(v___x_926_);
v_worklist_928_ = lean_array_pop(v_worklist_914_);
v___x_1052_ = lean_nat_sub(v_id_927_, v_initialId_921_);
v___x_1053_ = lean_byte_array_size(v_used_922_);
v___x_1054_ = lean_nat_dec_lt(v___x_1052_, v___x_1053_);
if (v___x_1054_ == 0)
{
uint8_t v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; uint8_t v___x_1058_; 
lean_dec(v___x_1052_);
v___x_1055_ = l_instInhabitedUInt8;
v___x_1056_ = lean_box(v___x_1055_);
v___x_1057_ = l_outOfBounds___redArg(v___x_1056_);
lean_dec(v___x_1056_);
v___x_1058_ = lean_unbox(v___x_1057_);
lean_dec(v___x_1057_);
v___y_1035_ = v___x_1058_;
goto v___jp_1034_;
}
else
{
uint8_t v___x_1059_; 
v___x_1059_ = lean_byte_array_fget(v_used_922_, v___x_1052_);
lean_dec(v___x_1052_);
v___y_1035_ = v___x_1059_;
goto v___jp_1034_;
}
v___jp_929_:
{
lean_object* v___x_932_; 
v___x_932_ = l_Array_append___redArg(v_worklist_928_, v___y_930_);
lean_dec_ref(v___y_930_);
v_worklist_914_ = v___x_932_;
v_a_916_ = v_snd_931_;
goto _start;
}
v___jp_934_:
{
lean_object* v_snd_937_; 
v_snd_937_ = lean_ctor_get(v___y_936_, 1);
lean_inc(v_snd_937_);
lean_dec_ref(v___y_936_);
v___y_930_ = v___y_935_;
v_snd_931_ = v_snd_937_;
goto v___jp_929_;
}
v___jp_938_:
{
lean_object* v___x_941_; 
v___x_941_ = l_Array_append___redArg(v_worklist_928_, v___y_939_);
lean_dec_ref(v___y_939_);
v_worklist_914_ = v___x_941_;
v_a_916_ = v_snd_940_;
goto _start;
}
v___jp_943_:
{
lean_object* v_snd_946_; 
v_snd_946_ = lean_ctor_get(v___y_945_, 1);
lean_inc(v_snd_946_);
lean_dec_ref(v___y_945_);
v___y_939_ = v___y_944_;
v_snd_940_ = v_snd_946_;
goto v___jp_938_;
}
v___jp_947_:
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = l_Array_append___redArg(v_worklist_928_, v___y_948_);
lean_dec_ref(v___y_948_);
v___x_952_ = l_Array_append___redArg(v___x_951_, v___y_949_);
lean_dec_ref(v___y_949_);
v_worklist_914_ = v___x_952_;
v_a_916_ = v_snd_950_;
goto _start;
}
v___jp_954_:
{
lean_object* v_snd_958_; 
v_snd_958_ = lean_ctor_get(v___y_957_, 1);
lean_inc(v_snd_958_);
lean_dec_ref(v___y_957_);
v___y_948_ = v___y_955_;
v___y_949_ = v___y_956_;
v_snd_950_ = v_snd_958_;
goto v___jp_947_;
}
v___jp_959_:
{
lean_object* v___x_965_; uint8_t v___x_966_; 
v___x_965_ = lean_array_get_size(v___y_964_);
v___x_966_ = lean_nat_dec_lt(v___x_918_, v___x_965_);
if (v___x_966_ == 0)
{
lean_dec(v_id_927_);
v___y_948_ = v___y_964_;
v___y_949_ = v___y_962_;
v_snd_950_ = v___y_963_;
goto v___jp_947_;
}
else
{
uint8_t v___x_967_; 
v___x_967_ = lean_nat_dec_le(v___x_965_, v___x_965_);
if (v___x_967_ == 0)
{
if (v___x_966_ == 0)
{
lean_dec(v_id_927_);
v___y_948_ = v___y_964_;
v___y_949_ = v___y_962_;
v_snd_950_ = v___y_963_;
goto v___jp_947_;
}
else
{
size_t v___x_968_; lean_object* v___x_969_; 
v___x_968_ = lean_usize_of_nat(v___x_965_);
v___x_969_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__4(v_id_927_, v___y_964_, v___y_961_, v___x_968_, v___y_960_, v_a_915_, v___y_963_);
v___y_955_ = v___y_964_;
v___y_956_ = v___y_962_;
v___y_957_ = v___x_969_;
goto v___jp_954_;
}
}
else
{
size_t v___x_970_; lean_object* v___x_971_; 
v___x_970_ = lean_usize_of_nat(v___x_965_);
v___x_971_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__4(v_id_927_, v___y_964_, v___y_961_, v___x_970_, v___y_960_, v_a_915_, v___y_963_);
v___y_955_ = v___y_964_;
v___y_956_ = v___y_962_;
v___y_957_ = v___x_971_;
goto v___jp_954_;
}
}
}
v___jp_972_:
{
lean_object* v___x_976_; size_t v_sz_977_; size_t v___x_978_; lean_object* v___x_979_; lean_object* v_snd_980_; lean_object* v___x_981_; lean_object* v___x_982_; uint8_t v___x_983_; 
v___x_976_ = lean_box(0);
v_sz_977_ = lean_array_size(v___y_974_);
v___x_978_ = ((size_t)0ULL);
lean_inc(v_id_927_);
v___x_979_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__3___redArg(v_id_927_, v___y_974_, v_sz_977_, v___x_978_, v___x_976_, v_snd_975_);
v_snd_980_ = lean_ctor_get(v___x_979_, 1);
lean_inc(v_snd_980_);
lean_dec_ref(v___x_979_);
v___x_981_ = lean_array_get_size(v___y_973_);
v___x_982_ = lean_mk_empty_array_with_capacity(v___x_981_);
v___x_983_ = lean_nat_dec_lt(v___x_918_, v___x_981_);
if (v___x_983_ == 0)
{
lean_dec_ref(v___y_973_);
v___y_960_ = v___x_976_;
v___y_961_ = v___x_978_;
v___y_962_ = v___y_974_;
v___y_963_ = v_snd_980_;
v___y_964_ = v___x_982_;
goto v___jp_959_;
}
else
{
uint8_t v___x_984_; 
v___x_984_ = lean_nat_dec_le(v___x_981_, v___x_981_);
if (v___x_984_ == 0)
{
if (v___x_983_ == 0)
{
lean_dec_ref(v___y_973_);
v___y_960_ = v___x_976_;
v___y_961_ = v___x_978_;
v___y_962_ = v___y_974_;
v___y_963_ = v_snd_980_;
v___y_964_ = v___x_982_;
goto v___jp_959_;
}
else
{
size_t v___x_985_; lean_object* v___x_986_; 
v___x_985_ = lean_usize_of_nat(v___x_981_);
v___x_986_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__5(v___y_973_, v___x_978_, v___x_985_, v___x_982_);
lean_dec_ref(v___y_973_);
v___y_960_ = v___x_976_;
v___y_961_ = v___x_978_;
v___y_962_ = v___y_974_;
v___y_963_ = v_snd_980_;
v___y_964_ = v___x_986_;
goto v___jp_959_;
}
}
else
{
size_t v___x_987_; lean_object* v___x_988_; 
v___x_987_ = lean_usize_of_nat(v___x_981_);
v___x_988_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__5(v___y_973_, v___x_978_, v___x_987_, v___x_982_);
lean_dec_ref(v___y_973_);
v___y_960_ = v___x_976_;
v___y_961_ = v___x_978_;
v___y_962_ = v___y_974_;
v___y_963_ = v_snd_980_;
v___y_964_ = v___x_988_;
goto v___jp_959_;
}
}
}
v___jp_989_:
{
lean_object* v_snd_993_; 
v_snd_993_ = lean_ctor_get(v___y_992_, 1);
lean_inc(v_snd_993_);
lean_dec_ref(v___y_992_);
v___y_973_ = v___y_990_;
v___y_974_ = v___y_991_;
v_snd_975_ = v_snd_993_;
goto v___jp_972_;
}
v___jp_994_:
{
lean_object* v___x_996_; 
v___x_996_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1___redArg(v_proof_920_, v_id_927_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_dec(v_id_927_);
v_worklist_914_ = v_worklist_928_;
v_a_916_ = v_snd_995_;
goto _start;
}
else
{
lean_object* v_val_998_; 
v_val_998_ = lean_ctor_get(v___x_996_, 0);
lean_inc(v_val_998_);
lean_dec_ref(v___x_996_);
switch(lean_obj_tag(v_val_998_))
{
case 0:
{
lean_object* v_rupHints_999_; lean_object* v___x_1000_; uint8_t v___x_1001_; 
v_rupHints_999_ = lean_ctor_get(v_val_998_, 1);
lean_inc_ref(v_rupHints_999_);
lean_dec_ref(v_val_998_);
v___x_1000_ = lean_array_get_size(v_rupHints_999_);
v___x_1001_ = lean_nat_dec_lt(v___x_918_, v___x_1000_);
if (v___x_1001_ == 0)
{
lean_dec(v_id_927_);
v___y_930_ = v_rupHints_999_;
v_snd_931_ = v_snd_995_;
goto v___jp_929_;
}
else
{
lean_object* v___x_1002_; uint8_t v___x_1003_; 
v___x_1002_ = lean_box(0);
v___x_1003_ = lean_nat_dec_le(v___x_1000_, v___x_1000_);
if (v___x_1003_ == 0)
{
if (v___x_1001_ == 0)
{
lean_dec(v_id_927_);
v___y_930_ = v_rupHints_999_;
v_snd_931_ = v_snd_995_;
goto v___jp_929_;
}
else
{
size_t v___x_1004_; size_t v___x_1005_; lean_object* v___x_1006_; 
v___x_1004_ = ((size_t)0ULL);
v___x_1005_ = lean_usize_of_nat(v___x_1000_);
v___x_1006_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2___redArg(v_id_927_, v_rupHints_999_, v___x_1004_, v___x_1005_, v___x_1002_, v_snd_995_);
v___y_935_ = v_rupHints_999_;
v___y_936_ = v___x_1006_;
goto v___jp_934_;
}
}
else
{
size_t v___x_1007_; size_t v___x_1008_; lean_object* v___x_1009_; 
v___x_1007_ = ((size_t)0ULL);
v___x_1008_ = lean_usize_of_nat(v___x_1000_);
v___x_1009_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2___redArg(v_id_927_, v_rupHints_999_, v___x_1007_, v___x_1008_, v___x_1002_, v_snd_995_);
v___y_935_ = v_rupHints_999_;
v___y_936_ = v___x_1009_;
goto v___jp_934_;
}
}
}
case 1:
{
lean_object* v_rupHints_1010_; lean_object* v___x_1011_; uint8_t v___x_1012_; 
v_rupHints_1010_ = lean_ctor_get(v_val_998_, 2);
lean_inc_ref(v_rupHints_1010_);
lean_dec_ref(v_val_998_);
v___x_1011_ = lean_array_get_size(v_rupHints_1010_);
v___x_1012_ = lean_nat_dec_lt(v___x_918_, v___x_1011_);
if (v___x_1012_ == 0)
{
lean_dec(v_id_927_);
v___y_939_ = v_rupHints_1010_;
v_snd_940_ = v_snd_995_;
goto v___jp_938_;
}
else
{
lean_object* v___x_1013_; uint8_t v___x_1014_; 
v___x_1013_ = lean_box(0);
v___x_1014_ = lean_nat_dec_le(v___x_1011_, v___x_1011_);
if (v___x_1014_ == 0)
{
if (v___x_1012_ == 0)
{
lean_dec(v_id_927_);
v___y_939_ = v_rupHints_1010_;
v_snd_940_ = v_snd_995_;
goto v___jp_938_;
}
else
{
size_t v___x_1015_; size_t v___x_1016_; lean_object* v___x_1017_; 
v___x_1015_ = ((size_t)0ULL);
v___x_1016_ = lean_usize_of_nat(v___x_1011_);
v___x_1017_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2___redArg(v_id_927_, v_rupHints_1010_, v___x_1015_, v___x_1016_, v___x_1013_, v_snd_995_);
v___y_944_ = v_rupHints_1010_;
v___y_945_ = v___x_1017_;
goto v___jp_943_;
}
}
else
{
size_t v___x_1018_; size_t v___x_1019_; lean_object* v___x_1020_; 
v___x_1018_ = ((size_t)0ULL);
v___x_1019_ = lean_usize_of_nat(v___x_1011_);
v___x_1020_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2___redArg(v_id_927_, v_rupHints_1010_, v___x_1018_, v___x_1019_, v___x_1013_, v_snd_995_);
v___y_944_ = v_rupHints_1010_;
v___y_945_ = v___x_1020_;
goto v___jp_943_;
}
}
}
case 2:
{
lean_object* v_rupHints_1021_; lean_object* v_ratHints_1022_; lean_object* v___x_1023_; uint8_t v___x_1024_; 
v_rupHints_1021_ = lean_ctor_get(v_val_998_, 3);
lean_inc_ref(v_rupHints_1021_);
v_ratHints_1022_ = lean_ctor_get(v_val_998_, 4);
lean_inc_ref(v_ratHints_1022_);
lean_dec_ref(v_val_998_);
v___x_1023_ = lean_array_get_size(v_rupHints_1021_);
v___x_1024_ = lean_nat_dec_lt(v___x_918_, v___x_1023_);
if (v___x_1024_ == 0)
{
v___y_973_ = v_ratHints_1022_;
v___y_974_ = v_rupHints_1021_;
v_snd_975_ = v_snd_995_;
goto v___jp_972_;
}
else
{
lean_object* v___x_1025_; uint8_t v___x_1026_; 
v___x_1025_ = lean_box(0);
v___x_1026_ = lean_nat_dec_le(v___x_1023_, v___x_1023_);
if (v___x_1026_ == 0)
{
if (v___x_1024_ == 0)
{
v___y_973_ = v_ratHints_1022_;
v___y_974_ = v_rupHints_1021_;
v_snd_975_ = v_snd_995_;
goto v___jp_972_;
}
else
{
size_t v___x_1027_; size_t v___x_1028_; lean_object* v___x_1029_; 
v___x_1027_ = ((size_t)0ULL);
v___x_1028_ = lean_usize_of_nat(v___x_1023_);
lean_inc(v_id_927_);
v___x_1029_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__4(v_id_927_, v_rupHints_1021_, v___x_1027_, v___x_1028_, v___x_1025_, v_a_915_, v_snd_995_);
v___y_990_ = v_ratHints_1022_;
v___y_991_ = v_rupHints_1021_;
v___y_992_ = v___x_1029_;
goto v___jp_989_;
}
}
else
{
size_t v___x_1030_; size_t v___x_1031_; lean_object* v___x_1032_; 
v___x_1030_ = ((size_t)0ULL);
v___x_1031_ = lean_usize_of_nat(v___x_1023_);
lean_inc(v_id_927_);
v___x_1032_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__4(v_id_927_, v_rupHints_1021_, v___x_1030_, v___x_1031_, v___x_1025_, v_a_915_, v_snd_995_);
v___y_990_ = v_ratHints_1022_;
v___y_991_ = v_rupHints_1021_;
v___y_992_ = v___x_1032_;
goto v___jp_989_;
}
}
}
default: 
{
lean_dec_ref(v_val_998_);
lean_dec(v_id_927_);
v_worklist_914_ = v_worklist_928_;
v_a_916_ = v_snd_995_;
goto _start;
}
}
}
}
v___jp_1034_:
{
uint8_t v___x_1036_; uint8_t v___x_1037_; 
v___x_1036_ = 1;
v___x_1037_ = lean_uint8_dec_eq(v___y_1035_, v___x_1036_);
if (v___x_1037_ == 0)
{
uint8_t v___x_1038_; 
v___x_1038_ = lean_nat_dec_le(v_initialId_921_, v_id_927_);
if (v___x_1038_ == 0)
{
v_snd_995_ = v_a_916_;
goto v___jp_994_;
}
else
{
lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1047_; 
lean_inc_ref(v_lastUse_924_);
lean_inc_ref(v_mapped_923_);
lean_inc_ref(v_used_922_);
v_isSharedCheck_1047_ = !lean_is_exclusive(v_a_916_);
if (v_isSharedCheck_1047_ == 0)
{
lean_object* v_unused_1048_; lean_object* v_unused_1049_; lean_object* v_unused_1050_; 
v_unused_1048_ = lean_ctor_get(v_a_916_, 2);
lean_dec(v_unused_1048_);
v_unused_1049_ = lean_ctor_get(v_a_916_, 1);
lean_dec(v_unused_1049_);
v_unused_1050_ = lean_ctor_get(v_a_916_, 0);
lean_dec(v_unused_1050_);
v___x_1040_ = v_a_916_;
v_isShared_1041_ = v_isSharedCheck_1047_;
goto v_resetjp_1039_;
}
else
{
lean_dec(v_a_916_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1047_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1045_; 
v___x_1042_ = lean_nat_sub(v_id_927_, v_initialId_921_);
v___x_1043_ = lean_byte_array_set(v_used_922_, v___x_1042_, v___x_1036_);
lean_dec(v___x_1042_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 0, v___x_1043_);
v___x_1045_ = v___x_1040_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v___x_1043_);
lean_ctor_set(v_reuseFailAlloc_1046_, 1, v_mapped_923_);
lean_ctor_set(v_reuseFailAlloc_1046_, 2, v_lastUse_924_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
v_snd_995_ = v___x_1045_;
goto v___jp_994_;
}
}
}
}
else
{
lean_dec(v_id_927_);
v_worklist_914_ = v_worklist_928_;
goto _start;
}
}
}
else
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
lean_dec_ref(v_worklist_914_);
v___x_1060_ = lean_box(0);
v___x_1061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
lean_ctor_set(v___x_1061_, 1, v_a_916_);
return v___x_1061_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go___boxed(lean_object* v_worklist_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l___private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go(v_worklist_1062_, v_a_1063_, v_a_1064_);
lean_dec_ref(v_a_1063_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1(lean_object* v_00_u03b2_1066_, lean_object* v_m_1067_, lean_object* v_a_1068_){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1___redArg(v_m_1067_, v_a_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1___boxed(lean_object* v_00_u03b2_1070_, lean_object* v_m_1071_, lean_object* v_a_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1(v_00_u03b2_1070_, v_m_1071_, v_a_1072_);
lean_dec(v_a_1072_);
lean_dec_ref(v_m_1071_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2(lean_object* v_id_1074_, lean_object* v_as_1075_, size_t v_i_1076_, size_t v_stop_1077_, lean_object* v_b_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v___x_1081_; 
v___x_1081_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2___redArg(v_id_1074_, v_as_1075_, v_i_1076_, v_stop_1077_, v_b_1078_, v___y_1080_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2___boxed(lean_object* v_id_1082_, lean_object* v_as_1083_, lean_object* v_i_1084_, lean_object* v_stop_1085_, lean_object* v_b_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
size_t v_i_boxed_1089_; size_t v_stop_boxed_1090_; lean_object* v_res_1091_; 
v_i_boxed_1089_ = lean_unbox_usize(v_i_1084_);
lean_dec(v_i_1084_);
v_stop_boxed_1090_ = lean_unbox_usize(v_stop_1085_);
lean_dec(v_stop_1085_);
v_res_1091_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2(v_id_1082_, v_as_1083_, v_i_boxed_1089_, v_stop_boxed_1090_, v_b_1086_, v___y_1087_, v___y_1088_);
lean_dec_ref(v___y_1087_);
lean_dec_ref(v_as_1083_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__3(lean_object* v_id_1092_, lean_object* v_as_1093_, size_t v_sz_1094_, size_t v_i_1095_, lean_object* v_b_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v___x_1099_; 
v___x_1099_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__3___redArg(v_id_1092_, v_as_1093_, v_sz_1094_, v_i_1095_, v_b_1096_, v___y_1098_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__3___boxed(lean_object* v_id_1100_, lean_object* v_as_1101_, lean_object* v_sz_1102_, lean_object* v_i_1103_, lean_object* v_b_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
size_t v_sz_boxed_1107_; size_t v_i_boxed_1108_; lean_object* v_res_1109_; 
v_sz_boxed_1107_ = lean_unbox_usize(v_sz_1102_);
lean_dec(v_sz_1102_);
v_i_boxed_1108_ = lean_unbox_usize(v_i_1103_);
lean_dec(v_i_1103_);
v_res_1109_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__3(v_id_1100_, v_as_1101_, v_sz_boxed_1107_, v_i_boxed_1108_, v_b_1104_, v___y_1105_, v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec_ref(v_as_1101_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1_spec__1(lean_object* v_00_u03b2_1110_, lean_object* v_a_1111_, lean_object* v_x_1112_){
_start:
{
lean_object* v___x_1113_; 
v___x_1113_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1_spec__1___redArg(v_a_1111_, v_x_1112_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1114_, lean_object* v_a_1115_, lean_object* v_x_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1_spec__1(v_00_u03b2_1114_, v_a_1115_, v_x_1116_);
lean_dec(v_x_1116_);
lean_dec(v_a_1115_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis(lean_object* v_a_1118_, lean_object* v_a_1119_){
_start:
{
lean_object* v_addEmptyId_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v_addEmptyId_1120_ = lean_ctor_get(v_a_1118_, 2);
v___x_1121_ = lean_unsigned_to_nat(1u);
v___x_1122_ = lean_mk_empty_array_with_capacity(v___x_1121_);
lean_inc(v_addEmptyId_1120_);
v___x_1123_ = lean_array_push(v___x_1122_, v_addEmptyId_1120_);
v___x_1124_ = l___private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go(v___x_1123_, v_a_1118_, v_a_1119_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis___boxed(lean_object* v_a_1125_, lean_object* v_a_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis(v_a_1125_, v_a_1126_);
lean_dec_ref(v_a_1125_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__0_spec__0___lam__0(lean_object* v_next_1128_, lean_object* v_x_1129_){
_start:
{
if (lean_obj_tag(v_x_1129_) == 0)
{
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1130_ = lean_unsigned_to_nat(1u);
v___x_1131_ = lean_mk_empty_array_with_capacity(v___x_1130_);
v___x_1132_ = lean_array_push(v___x_1131_, v_next_1128_);
v___x_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1132_);
return v___x_1133_;
}
else
{
lean_object* v_val_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1142_; 
v_val_1134_ = lean_ctor_get(v_x_1129_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v_x_1129_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1136_ = v_x_1129_;
v_isShared_1137_ = v_isSharedCheck_1142_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_val_1134_);
lean_dec(v_x_1129_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1142_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1138_; lean_object* v___x_1140_; 
v___x_1138_ = lean_array_push(v_val_1134_, v_next_1128_);
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 0, v___x_1138_);
v___x_1140_ = v___x_1136_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1138_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__0_spec__0(lean_object* v_next_1143_, lean_object* v_a_1144_, lean_object* v_x_1145_){
_start:
{
if (lean_obj_tag(v_x_1145_) == 0)
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v_val_1148_; lean_object* v___x_1149_; 
v___x_1146_ = lean_box(0);
v___x_1147_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__0_spec__0___lam__0(v_next_1143_, v___x_1146_);
v_val_1148_ = lean_ctor_get(v___x_1147_, 0);
lean_inc(v_val_1148_);
lean_dec(v___x_1147_);
v___x_1149_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1149_, 0, v_a_1144_);
lean_ctor_set(v___x_1149_, 1, v_val_1148_);
lean_ctor_set(v___x_1149_, 2, v_x_1145_);
return v___x_1149_;
}
else
{
lean_object* v_key_1150_; lean_object* v_value_1151_; lean_object* v_tail_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1167_; 
v_key_1150_ = lean_ctor_get(v_x_1145_, 0);
v_value_1151_ = lean_ctor_get(v_x_1145_, 1);
v_tail_1152_ = lean_ctor_get(v_x_1145_, 2);
v_isSharedCheck_1167_ = !lean_is_exclusive(v_x_1145_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1154_ = v_x_1145_;
v_isShared_1155_ = v_isSharedCheck_1167_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_tail_1152_);
lean_inc(v_value_1151_);
lean_inc(v_key_1150_);
lean_dec(v_x_1145_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1167_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
uint8_t v___x_1156_; 
v___x_1156_ = lean_nat_dec_eq(v_key_1150_, v_a_1144_);
if (v___x_1156_ == 0)
{
lean_object* v_tail_1157_; lean_object* v___x_1159_; 
v_tail_1157_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__0_spec__0(v_next_1143_, v_a_1144_, v_tail_1152_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 2, v_tail_1157_);
v___x_1159_ = v___x_1154_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_key_1150_);
lean_ctor_set(v_reuseFailAlloc_1160_, 1, v_value_1151_);
lean_ctor_set(v_reuseFailAlloc_1160_, 2, v_tail_1157_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
else
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v_val_1163_; lean_object* v___x_1165_; 
lean_dec(v_key_1150_);
v___x_1161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1161_, 0, v_value_1151_);
v___x_1162_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__0_spec__0___lam__0(v_next_1143_, v___x_1161_);
v_val_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc(v_val_1163_);
lean_dec(v___x_1162_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 1, v_val_1163_);
lean_ctor_set(v___x_1154_, 0, v_a_1144_);
v___x_1165_ = v___x_1154_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1144_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v_val_1163_);
lean_ctor_set(v_reuseFailAlloc_1166_, 2, v_tail_1152_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__0(lean_object* v_next_1168_, lean_object* v_m_1169_, lean_object* v_a_1170_){
_start:
{
lean_object* v_size_1171_; lean_object* v_buckets_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1222_; 
v_size_1171_ = lean_ctor_get(v_m_1169_, 0);
v_buckets_1172_ = lean_ctor_get(v_m_1169_, 1);
v_isSharedCheck_1222_ = !lean_is_exclusive(v_m_1169_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1174_ = v_m_1169_;
v_isShared_1175_ = v_isSharedCheck_1222_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_buckets_1172_);
lean_inc(v_size_1171_);
lean_dec(v_m_1169_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1222_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1176_; uint64_t v___x_1177_; uint64_t v___x_1178_; uint64_t v___x_1179_; uint64_t v_fold_1180_; uint64_t v___x_1181_; uint64_t v___x_1182_; uint64_t v___x_1183_; size_t v___x_1184_; size_t v___x_1185_; size_t v___x_1186_; size_t v___x_1187_; size_t v___x_1188_; lean_object* v_bkt_1189_; uint8_t v___x_1190_; 
v___x_1176_ = lean_array_get_size(v_buckets_1172_);
v___x_1177_ = lean_uint64_of_nat(v_a_1170_);
v___x_1178_ = 32ULL;
v___x_1179_ = lean_uint64_shift_right(v___x_1177_, v___x_1178_);
v_fold_1180_ = lean_uint64_xor(v___x_1177_, v___x_1179_);
v___x_1181_ = 16ULL;
v___x_1182_ = lean_uint64_shift_right(v_fold_1180_, v___x_1181_);
v___x_1183_ = lean_uint64_xor(v_fold_1180_, v___x_1182_);
v___x_1184_ = lean_uint64_to_usize(v___x_1183_);
v___x_1185_ = lean_usize_of_nat(v___x_1176_);
v___x_1186_ = ((size_t)1ULL);
v___x_1187_ = lean_usize_sub(v___x_1185_, v___x_1186_);
v___x_1188_ = lean_usize_land(v___x_1184_, v___x_1187_);
v_bkt_1189_ = lean_array_uget_borrowed(v_buckets_1172_, v___x_1188_);
v___x_1190_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__0___redArg(v_a_1170_, v_bkt_1189_);
if (v___x_1190_ == 0)
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v_size_x27_1194_; lean_object* v___x_1195_; lean_object* v_buckets_x27_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; uint8_t v___x_1202_; 
v___x_1191_ = lean_unsigned_to_nat(1u);
v___x_1192_ = lean_mk_empty_array_with_capacity(v___x_1191_);
v___x_1193_ = lean_array_push(v___x_1192_, v_next_1168_);
v_size_x27_1194_ = lean_nat_add(v_size_1171_, v___x_1191_);
lean_dec(v_size_1171_);
lean_inc(v_bkt_1189_);
v___x_1195_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1195_, 0, v_a_1170_);
lean_ctor_set(v___x_1195_, 1, v___x_1193_);
lean_ctor_set(v___x_1195_, 2, v_bkt_1189_);
v_buckets_x27_1196_ = lean_array_uset(v_buckets_1172_, v___x_1188_, v___x_1195_);
v___x_1197_ = lean_unsigned_to_nat(4u);
v___x_1198_ = lean_nat_mul(v_size_x27_1194_, v___x_1197_);
v___x_1199_ = lean_unsigned_to_nat(3u);
v___x_1200_ = lean_nat_div(v___x_1198_, v___x_1199_);
lean_dec(v___x_1198_);
v___x_1201_ = lean_array_get_size(v_buckets_x27_1196_);
v___x_1202_ = lean_nat_dec_le(v___x_1200_, v___x_1201_);
lean_dec(v___x_1200_);
if (v___x_1202_ == 0)
{
lean_object* v_val_1203_; lean_object* v___x_1205_; 
v_val_1203_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1___redArg(v_buckets_x27_1196_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 1, v_val_1203_);
lean_ctor_set(v___x_1174_, 0, v_size_x27_1194_);
v___x_1205_ = v___x_1174_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_size_x27_1194_);
lean_ctor_set(v_reuseFailAlloc_1206_, 1, v_val_1203_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
else
{
lean_object* v___x_1208_; 
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 1, v_buckets_x27_1196_);
lean_ctor_set(v___x_1174_, 0, v_size_x27_1194_);
v___x_1208_ = v___x_1174_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_size_x27_1194_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v_buckets_x27_1196_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
else
{
lean_object* v___x_1210_; lean_object* v_buckets_x27_1211_; lean_object* v_bkt_x27_1212_; lean_object* v___y_1214_; uint8_t v___x_1219_; 
lean_inc(v_bkt_1189_);
v___x_1210_ = lean_box(0);
v_buckets_x27_1211_ = lean_array_uset(v_buckets_1172_, v___x_1188_, v___x_1210_);
lean_inc(v_a_1170_);
v_bkt_x27_1212_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__0_spec__0(v_next_1168_, v_a_1170_, v_bkt_1189_);
v___x_1219_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__0___redArg(v_a_1170_, v_bkt_x27_1212_);
lean_dec(v_a_1170_);
if (v___x_1219_ == 0)
{
lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1220_ = lean_unsigned_to_nat(1u);
v___x_1221_ = lean_nat_sub(v_size_1171_, v___x_1220_);
lean_dec(v_size_1171_);
v___y_1214_ = v___x_1221_;
goto v___jp_1213_;
}
else
{
v___y_1214_ = v_size_1171_;
goto v___jp_1213_;
}
v___jp_1213_:
{
lean_object* v___x_1215_; lean_object* v___x_1217_; 
v___x_1215_ = lean_array_uset(v_buckets_x27_1211_, v___x_1188_, v_bkt_x27_1212_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 1, v___x_1215_);
lean_ctor_set(v___x_1174_, 0, v___y_1214_);
v___x_1217_ = v___x_1174_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v___y_1214_);
lean_ctor_set(v_reuseFailAlloc_1218_, 1, v___x_1215_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__1___redArg(lean_object* v_upperBound_1223_, lean_object* v___x_1224_, lean_object* v_a_1225_, lean_object* v_b_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v_a_1229_; lean_object* v_snd_1230_; uint8_t v___x_1234_; 
v___x_1234_ = lean_nat_dec_lt(v_a_1225_, v_upperBound_1223_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; 
lean_dec(v_a_1225_);
v___x_1235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1235_, 0, v_b_1226_);
lean_ctor_set(v___x_1235_, 1, v___y_1227_);
return v___x_1235_;
}
else
{
lean_object* v___x_1236_; lean_object* v___x_1237_; uint8_t v___x_1238_; 
v___x_1236_ = lean_array_fget_borrowed(v___x_1224_, v_a_1225_);
v___x_1237_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__1, &l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__1);
v___x_1238_ = lean_int_dec_eq(v___x_1236_, v___x_1237_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1239_ = lean_nat_abs(v___x_1236_);
lean_inc(v_a_1225_);
v___x_1240_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__0(v_a_1225_, v_b_1226_, v___x_1239_);
v_a_1229_ = v___x_1240_;
v_snd_1230_ = v___y_1227_;
goto v___jp_1228_;
}
else
{
v_a_1229_ = v_b_1226_;
v_snd_1230_ = v___y_1227_;
goto v___jp_1228_;
}
}
v___jp_1228_:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1231_ = lean_unsigned_to_nat(1u);
v___x_1232_ = lean_nat_add(v_a_1225_, v___x_1231_);
lean_dec(v_a_1225_);
v_a_1225_ = v___x_1232_;
v_b_1226_ = v_a_1229_;
v___y_1227_ = v_snd_1230_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__1___redArg___boxed(lean_object* v_upperBound_1241_, lean_object* v___x_1242_, lean_object* v_a_1243_, lean_object* v_b_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__1___redArg(v_upperBound_1241_, v___x_1242_, v_a_1243_, v_b_1244_, v___y_1245_);
lean_dec_ref(v___x_1242_);
lean_dec(v_upperBound_1241_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete(lean_object* v_a_1247_, lean_object* v_a_1248_){
_start:
{
lean_object* v_lastUse_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
v_lastUse_1249_ = lean_ctor_get(v_a_1248_, 2);
lean_inc_ref(v_lastUse_1249_);
v___x_1250_ = lean_unsigned_to_nat(0u);
v___x_1251_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__3, &l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__3);
v___x_1252_ = lean_array_get_size(v_lastUse_1249_);
v___x_1253_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__1___redArg(v___x_1252_, v_lastUse_1249_, v___x_1250_, v___x_1251_, v_a_1248_);
lean_dec_ref(v_lastUse_1249_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete___boxed(lean_object* v_a_1254_, lean_object* v_a_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete(v_a_1254_, v_a_1255_);
lean_dec_ref(v_a_1254_);
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__1(lean_object* v_upperBound_1257_, lean_object* v___x_1258_, lean_object* v_inst_1259_, lean_object* v_R_1260_, lean_object* v_a_1261_, lean_object* v_b_1262_, lean_object* v_c_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v___x_1266_; 
v___x_1266_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__1___redArg(v_upperBound_1257_, v___x_1258_, v_a_1261_, v_b_1262_, v___y_1265_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__1___boxed(lean_object* v_upperBound_1267_, lean_object* v___x_1268_, lean_object* v_inst_1269_, lean_object* v_R_1270_, lean_object* v_a_1271_, lean_object* v_b_1272_, lean_object* v_c_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__1(v_upperBound_1267_, v___x_1268_, v_inst_1269_, v_R_1270_, v_a_1271_, v_b_1272_, v_c_1273_, v___y_1274_, v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_dec_ref(v___x_1268_);
lean_dec(v_upperBound_1267_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__2(lean_object* v_msg_1277_){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1278_ = lean_obj_once(&l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__7, &l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__7_once, _init_l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__7);
v___x_1279_ = lean_panic_fn_borrowed(v___x_1278_, v_msg_1277_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0_spec__0___redArg(lean_object* v_next_1280_, lean_object* v_as_1281_, size_t v_sz_1282_, size_t v_i_1283_, lean_object* v_b_1284_, lean_object* v___y_1285_){
_start:
{
lean_object* v_a_1287_; lean_object* v_snd_1288_; uint8_t v___x_1292_; 
v___x_1292_ = lean_usize_dec_lt(v_i_1283_, v_sz_1282_);
if (v___x_1292_ == 0)
{
lean_object* v___x_1293_; 
lean_dec(v_next_1280_);
v___x_1293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1293_, 0, v_b_1284_);
lean_ctor_set(v___x_1293_, 1, v___y_1285_);
return v___x_1293_;
}
else
{
lean_object* v_lastUse_1294_; lean_object* v_a_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; uint8_t v___x_1299_; 
v_lastUse_1294_ = lean_ctor_get(v___y_1285_, 2);
v_a_1295_ = lean_array_uget_borrowed(v_as_1281_, v_i_1283_);
v___x_1296_ = l_Int_instInhabited;
v___x_1297_ = lean_array_get_borrowed(v___x_1296_, v_lastUse_1294_, v_a_1295_);
lean_inc(v_next_1280_);
v___x_1298_ = lean_nat_to_int(v_next_1280_);
v___x_1299_ = lean_int_dec_eq(v___x_1297_, v___x_1298_);
lean_dec(v___x_1298_);
if (v___x_1299_ == 0)
{
v_a_1287_ = v_b_1284_;
v_snd_1288_ = v___y_1285_;
goto v___jp_1286_;
}
else
{
lean_object* v___x_1300_; 
lean_inc(v_a_1295_);
v___x_1300_ = lean_array_push(v_b_1284_, v_a_1295_);
v_a_1287_ = v___x_1300_;
v_snd_1288_ = v___y_1285_;
goto v___jp_1286_;
}
}
v___jp_1286_:
{
size_t v___x_1289_; size_t v___x_1290_; 
v___x_1289_ = ((size_t)1ULL);
v___x_1290_ = lean_usize_add(v_i_1283_, v___x_1289_);
v_i_1283_ = v___x_1290_;
v_b_1284_ = v_a_1287_;
v___y_1285_ = v_snd_1288_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0_spec__0___redArg___boxed(lean_object* v_next_1301_, lean_object* v_as_1302_, lean_object* v_sz_1303_, lean_object* v_i_1304_, lean_object* v_b_1305_, lean_object* v___y_1306_){
_start:
{
size_t v_sz_boxed_1307_; size_t v_i_boxed_1308_; lean_object* v_res_1309_; 
v_sz_boxed_1307_ = lean_unbox_usize(v_sz_1303_);
lean_dec(v_sz_1303_);
v_i_boxed_1308_ = lean_unbox_usize(v_i_1304_);
lean_dec(v_i_1304_);
v_res_1309_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0_spec__0___redArg(v_next_1301_, v_as_1302_, v_sz_boxed_1307_, v_i_boxed_1308_, v_b_1305_, v___y_1306_);
lean_dec_ref(v_as_1302_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0(lean_object* v_next_1310_, lean_object* v_as_1311_, size_t v_sz_1312_, size_t v_i_1313_, lean_object* v_b_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v_a_1318_; lean_object* v_snd_1319_; uint8_t v___x_1323_; 
v___x_1323_ = lean_usize_dec_lt(v_i_1313_, v_sz_1312_);
if (v___x_1323_ == 0)
{
lean_object* v___x_1324_; 
lean_dec(v_next_1310_);
v___x_1324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1324_, 0, v_b_1314_);
lean_ctor_set(v___x_1324_, 1, v___y_1316_);
return v___x_1324_;
}
else
{
lean_object* v_lastUse_1325_; lean_object* v_a_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; uint8_t v___x_1330_; 
v_lastUse_1325_ = lean_ctor_get(v___y_1316_, 2);
v_a_1326_ = lean_array_uget_borrowed(v_as_1311_, v_i_1313_);
v___x_1327_ = l_Int_instInhabited;
v___x_1328_ = lean_array_get_borrowed(v___x_1327_, v_lastUse_1325_, v_a_1326_);
lean_inc(v_next_1310_);
v___x_1329_ = lean_nat_to_int(v_next_1310_);
v___x_1330_ = lean_int_dec_eq(v___x_1328_, v___x_1329_);
lean_dec(v___x_1329_);
if (v___x_1330_ == 0)
{
v_a_1318_ = v_b_1314_;
v_snd_1319_ = v___y_1316_;
goto v___jp_1317_;
}
else
{
lean_object* v___x_1331_; 
lean_inc(v_a_1326_);
v___x_1331_ = lean_array_push(v_b_1314_, v_a_1326_);
v_a_1318_ = v___x_1331_;
v_snd_1319_ = v___y_1316_;
goto v___jp_1317_;
}
}
v___jp_1317_:
{
size_t v___x_1320_; size_t v___x_1321_; lean_object* v___x_1322_; 
v___x_1320_ = ((size_t)1ULL);
v___x_1321_ = lean_usize_add(v_i_1313_, v___x_1320_);
v___x_1322_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0_spec__0___redArg(v_next_1310_, v_as_1311_, v_sz_1312_, v___x_1321_, v_a_1318_, v_snd_1319_);
return v___x_1322_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0___boxed(lean_object* v_next_1332_, lean_object* v_as_1333_, lean_object* v_sz_1334_, lean_object* v_i_1335_, lean_object* v_b_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
size_t v_sz_boxed_1339_; size_t v_i_boxed_1340_; lean_object* v_res_1341_; 
v_sz_boxed_1339_ = lean_unbox_usize(v_sz_1334_);
lean_dec(v_sz_1334_);
v_i_boxed_1340_ = lean_unbox_usize(v_i_1335_);
lean_dec(v_i_1335_);
v_res_1341_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0(v_next_1332_, v_as_1333_, v_sz_boxed_1339_, v_i_boxed_1340_, v_b_1336_, v___y_1337_, v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec_ref(v_as_1333_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__1_spec__2(lean_object* v_next_1342_, lean_object* v_as_1343_, size_t v_sz_1344_, size_t v_i_1345_, lean_object* v_b_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
uint8_t v___x_1349_; 
v___x_1349_ = lean_usize_dec_lt(v_i_1345_, v_sz_1344_);
if (v___x_1349_ == 0)
{
lean_object* v___x_1350_; 
lean_dec(v_next_1342_);
v___x_1350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1350_, 0, v_b_1346_);
lean_ctor_set(v___x_1350_, 1, v___y_1348_);
return v___x_1350_;
}
else
{
lean_object* v_a_1351_; lean_object* v_fst_1352_; lean_object* v_snd_1353_; lean_object* v_deletions_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v_lastUse_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; uint8_t v___x_1370_; 
v_a_1351_ = lean_array_uget_borrowed(v_as_1343_, v_i_1345_);
v_fst_1352_ = lean_ctor_get(v_a_1351_, 0);
v_snd_1353_ = lean_ctor_get(v_a_1351_, 1);
v_lastUse_1366_ = lean_ctor_get(v___y_1348_, 2);
v___x_1367_ = l_Int_instInhabited;
v___x_1368_ = lean_array_get_borrowed(v___x_1367_, v_lastUse_1366_, v_fst_1352_);
lean_inc(v_next_1342_);
v___x_1369_ = lean_nat_to_int(v_next_1342_);
v___x_1370_ = lean_int_dec_eq(v___x_1368_, v___x_1369_);
lean_dec(v___x_1369_);
if (v___x_1370_ == 0)
{
v_deletions_1355_ = v_b_1346_;
v___y_1356_ = v___y_1347_;
v___y_1357_ = v___y_1348_;
goto v___jp_1354_;
}
else
{
lean_object* v___x_1371_; 
lean_inc(v_fst_1352_);
v___x_1371_ = lean_array_push(v_b_1346_, v_fst_1352_);
v_deletions_1355_ = v___x_1371_;
v___y_1356_ = v___y_1347_;
v___y_1357_ = v___y_1348_;
goto v___jp_1354_;
}
v___jp_1354_:
{
size_t v_sz_1358_; size_t v___x_1359_; lean_object* v___x_1360_; lean_object* v_fst_1361_; lean_object* v_snd_1362_; size_t v___x_1363_; size_t v___x_1364_; 
v_sz_1358_ = lean_array_size(v_snd_1353_);
v___x_1359_ = ((size_t)0ULL);
lean_inc(v_next_1342_);
v___x_1360_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0(v_next_1342_, v_snd_1353_, v_sz_1358_, v___x_1359_, v_deletions_1355_, v___y_1356_, v___y_1357_);
v_fst_1361_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_fst_1361_);
v_snd_1362_ = lean_ctor_get(v___x_1360_, 1);
lean_inc(v_snd_1362_);
lean_dec_ref(v___x_1360_);
v___x_1363_ = ((size_t)1ULL);
v___x_1364_ = lean_usize_add(v_i_1345_, v___x_1363_);
v_i_1345_ = v___x_1364_;
v_b_1346_ = v_fst_1361_;
v___y_1348_ = v_snd_1362_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__1_spec__2___boxed(lean_object* v_next_1372_, lean_object* v_as_1373_, lean_object* v_sz_1374_, lean_object* v_i_1375_, lean_object* v_b_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
size_t v_sz_boxed_1379_; size_t v_i_boxed_1380_; lean_object* v_res_1381_; 
v_sz_boxed_1379_ = lean_unbox_usize(v_sz_1374_);
lean_dec(v_sz_1374_);
v_i_boxed_1380_ = lean_unbox_usize(v_i_1375_);
lean_dec(v_i_1375_);
v_res_1381_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__1_spec__2(v_next_1372_, v_as_1373_, v_sz_boxed_1379_, v_i_boxed_1380_, v_b_1376_, v___y_1377_, v___y_1378_);
lean_dec_ref(v___y_1377_);
lean_dec_ref(v_as_1373_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__1(lean_object* v_next_1382_, lean_object* v_as_1383_, size_t v_sz_1384_, size_t v_i_1385_, lean_object* v_b_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_){
_start:
{
uint8_t v___x_1389_; 
v___x_1389_ = lean_usize_dec_lt(v_i_1385_, v_sz_1384_);
if (v___x_1389_ == 0)
{
lean_object* v___x_1390_; 
lean_dec(v_next_1382_);
v___x_1390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1390_, 0, v_b_1386_);
lean_ctor_set(v___x_1390_, 1, v___y_1388_);
return v___x_1390_;
}
else
{
lean_object* v_a_1391_; lean_object* v_fst_1392_; lean_object* v_snd_1393_; lean_object* v_deletions_1395_; lean_object* v___y_1396_; lean_object* v___y_1397_; lean_object* v_lastUse_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; uint8_t v___x_1410_; 
v_a_1391_ = lean_array_uget_borrowed(v_as_1383_, v_i_1385_);
v_fst_1392_ = lean_ctor_get(v_a_1391_, 0);
v_snd_1393_ = lean_ctor_get(v_a_1391_, 1);
v_lastUse_1406_ = lean_ctor_get(v___y_1388_, 2);
v___x_1407_ = l_Int_instInhabited;
v___x_1408_ = lean_array_get_borrowed(v___x_1407_, v_lastUse_1406_, v_fst_1392_);
lean_inc(v_next_1382_);
v___x_1409_ = lean_nat_to_int(v_next_1382_);
v___x_1410_ = lean_int_dec_eq(v___x_1408_, v___x_1409_);
lean_dec(v___x_1409_);
if (v___x_1410_ == 0)
{
v_deletions_1395_ = v_b_1386_;
v___y_1396_ = v___y_1387_;
v___y_1397_ = v___y_1388_;
goto v___jp_1394_;
}
else
{
lean_object* v___x_1411_; 
lean_inc(v_fst_1392_);
v___x_1411_ = lean_array_push(v_b_1386_, v_fst_1392_);
v_deletions_1395_ = v___x_1411_;
v___y_1396_ = v___y_1387_;
v___y_1397_ = v___y_1388_;
goto v___jp_1394_;
}
v___jp_1394_:
{
size_t v_sz_1398_; size_t v___x_1399_; lean_object* v___x_1400_; lean_object* v_fst_1401_; lean_object* v_snd_1402_; size_t v___x_1403_; size_t v___x_1404_; lean_object* v___x_1405_; 
v_sz_1398_ = lean_array_size(v_snd_1393_);
v___x_1399_ = ((size_t)0ULL);
lean_inc(v_next_1382_);
v___x_1400_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0(v_next_1382_, v_snd_1393_, v_sz_1398_, v___x_1399_, v_deletions_1395_, v___y_1396_, v___y_1397_);
v_fst_1401_ = lean_ctor_get(v___x_1400_, 0);
lean_inc(v_fst_1401_);
v_snd_1402_ = lean_ctor_get(v___x_1400_, 1);
lean_inc(v_snd_1402_);
lean_dec_ref(v___x_1400_);
v___x_1403_ = ((size_t)1ULL);
v___x_1404_ = lean_usize_add(v_i_1385_, v___x_1403_);
v___x_1405_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__1_spec__2(v_next_1382_, v_as_1383_, v_sz_1384_, v___x_1404_, v_fst_1401_, v___y_1387_, v_snd_1402_);
return v___x_1405_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__1___boxed(lean_object* v_next_1412_, lean_object* v_as_1413_, lean_object* v_sz_1414_, lean_object* v_i_1415_, lean_object* v_b_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
size_t v_sz_boxed_1419_; size_t v_i_boxed_1420_; lean_object* v_res_1421_; 
v_sz_boxed_1419_ = lean_unbox_usize(v_sz_1414_);
lean_dec(v_sz_1414_);
v_i_boxed_1420_ = lean_unbox_usize(v_i_1415_);
lean_dec(v_i_1415_);
v_res_1421_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__1(v_next_1412_, v_as_1413_, v_sz_boxed_1419_, v_i_boxed_1420_, v_b_1416_, v___y_1417_, v___y_1418_);
lean_dec_ref(v___y_1417_);
lean_dec_ref(v_as_1413_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___lam__0(lean_object* v___y_1422_, lean_object* v_fst_1423_, lean_object* v_snd_1424_, uint8_t v___x_1425_, lean_object* v_____r_1426_, lean_object* v_deletions_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v___x_1430_; lean_object* v_fst_1431_; lean_object* v_snd_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1462_; 
v___x_1430_ = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep(v___y_1422_, v___y_1428_, v___y_1429_);
v_fst_1431_ = lean_ctor_get(v___x_1430_, 0);
v_snd_1432_ = lean_ctor_get(v___x_1430_, 1);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1434_ = v___x_1430_;
v_isShared_1435_ = v_isSharedCheck_1462_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_snd_1432_);
lean_inc(v_fst_1431_);
lean_dec(v___x_1430_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1462_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
size_t v_sz_1436_; size_t v___x_1437_; lean_object* v___x_1438_; lean_object* v_fst_1439_; lean_object* v_snd_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1461_; 
v_sz_1436_ = lean_array_size(v_deletions_1427_);
v___x_1437_ = ((size_t)0ULL);
v___x_1438_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__0(v_sz_1436_, v___x_1437_, v_deletions_1427_, v___y_1428_, v_snd_1432_);
v_fst_1439_ = lean_ctor_get(v___x_1438_, 0);
v_snd_1440_ = lean_ctor_get(v___x_1438_, 1);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1442_ = v___x_1438_;
v_isShared_1443_ = v_isSharedCheck_1461_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_snd_1440_);
lean_inc(v_fst_1439_);
lean_dec(v___x_1438_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1461_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v_newProof_1445_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; uint8_t v___x_1458_; 
v___x_1455_ = lean_array_push(v_snd_1424_, v_fst_1431_);
v___x_1456_ = lean_array_get_size(v_fst_1439_);
v___x_1457_ = lean_unsigned_to_nat(0u);
v___x_1458_ = lean_nat_dec_eq(v___x_1456_, v___x_1457_);
if (v___x_1458_ == 0)
{
if (v___x_1425_ == 0)
{
lean_dec(v_fst_1439_);
v_newProof_1445_ = v___x_1455_;
goto v___jp_1444_;
}
else
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1459_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1459_, 0, v_fst_1439_);
v___x_1460_ = lean_array_push(v___x_1455_, v___x_1459_);
v_newProof_1445_ = v___x_1460_;
goto v___jp_1444_;
}
}
else
{
lean_dec(v_fst_1439_);
v_newProof_1445_ = v___x_1455_;
goto v___jp_1444_;
}
v___jp_1444_:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1449_; 
v___x_1446_ = lean_unsigned_to_nat(1u);
v___x_1447_ = lean_nat_add(v_fst_1423_, v___x_1446_);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 1, v_newProof_1445_);
lean_ctor_set(v___x_1442_, 0, v___x_1447_);
v___x_1449_ = v___x_1442_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1447_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v_newProof_1445_);
v___x_1449_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
lean_object* v___x_1450_; lean_object* v___x_1452_; 
v___x_1450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1449_);
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 1, v_snd_1440_);
lean_ctor_set(v___x_1434_, 0, v___x_1450_);
v___x_1452_ = v___x_1434_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1450_);
lean_ctor_set(v_reuseFailAlloc_1453_, 1, v_snd_1440_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___lam__0___boxed(lean_object* v___y_1463_, lean_object* v_fst_1464_, lean_object* v_snd_1465_, lean_object* v___x_1466_, lean_object* v_____r_1467_, lean_object* v_deletions_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
uint8_t v___x_22194__boxed_1471_; lean_object* v_res_1472_; 
v___x_22194__boxed_1471_ = lean_unbox(v___x_1466_);
v_res_1472_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___lam__0(v___y_1463_, v_fst_1464_, v_snd_1465_, v___x_22194__boxed_1471_, v_____r_1467_, v_deletions_1468_, v___y_1469_, v___y_1470_);
lean_dec_ref(v___y_1469_);
lean_dec(v_fst_1464_);
return v_res_1472_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__4(void){
_start:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1478_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__3));
v___x_1479_ = lean_unsigned_to_nat(14u);
v___x_1480_ = lean_unsigned_to_nat(22u);
v___x_1481_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__2));
v___x_1482_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__1));
v___x_1483_ = l_mkPanicMessageWithDecl(v___x_1482_, v___x_1481_, v___x_1480_, v___x_1479_, v___x_1478_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg(lean_object* v_upperBound_1484_, lean_object* v___x_1485_, lean_object* v_a_1486_, lean_object* v_b_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
lean_object* v_a_1491_; lean_object* v_snd_1492_; lean_object* v___y_1497_; lean_object* v___y_1512_; lean_object* v___y_1513_; lean_object* v___y_1514_; uint8_t v___x_1517_; 
v___x_1517_ = lean_nat_dec_le(v_a_1486_, v_upperBound_1484_);
if (v___x_1517_ == 0)
{
lean_object* v___x_1518_; 
lean_dec(v_a_1486_);
v___x_1518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1518_, 0, v_b_1487_);
lean_ctor_set(v___x_1518_, 1, v___y_1489_);
return v___x_1518_;
}
else
{
lean_object* v_fst_1519_; lean_object* v_snd_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1592_; 
v_fst_1519_ = lean_ctor_get(v_b_1487_, 0);
v_snd_1520_ = lean_ctor_get(v_b_1487_, 1);
v_isSharedCheck_1592_ = !lean_is_exclusive(v_b_1487_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1522_ = v_b_1487_;
v_isShared_1523_ = v_isSharedCheck_1592_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_snd_1520_);
lean_inc(v_fst_1519_);
lean_dec(v_b_1487_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1592_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
uint8_t v___y_1525_; lean_object* v___y_1526_; uint8_t v___y_1527_; lean_object* v___y_1528_; lean_object* v_proof_1556_; lean_object* v_initialId_1557_; lean_object* v_used_1558_; lean_object* v_mapped_1559_; lean_object* v_lastUse_1560_; uint8_t v___y_1562_; lean_object* v___x_1584_; lean_object* v___x_1585_; uint8_t v___x_1586_; 
v_proof_1556_ = lean_ctor_get(v___y_1488_, 0);
v_initialId_1557_ = lean_ctor_get(v___y_1488_, 1);
v_used_1558_ = lean_ctor_get(v___y_1489_, 0);
v_mapped_1559_ = lean_ctor_get(v___y_1489_, 1);
v_lastUse_1560_ = lean_ctor_get(v___y_1489_, 2);
v___x_1584_ = lean_nat_sub(v_a_1486_, v_initialId_1557_);
v___x_1585_ = lean_byte_array_size(v_used_1558_);
v___x_1586_ = lean_nat_dec_lt(v___x_1584_, v___x_1585_);
if (v___x_1586_ == 0)
{
uint8_t v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; uint8_t v___x_1590_; 
lean_dec(v___x_1584_);
v___x_1587_ = l_instInhabitedUInt8;
v___x_1588_ = lean_box(v___x_1587_);
v___x_1589_ = l_outOfBounds___redArg(v___x_1588_);
lean_dec(v___x_1588_);
v___x_1590_ = lean_unbox(v___x_1589_);
lean_dec(v___x_1589_);
v___y_1562_ = v___x_1590_;
goto v___jp_1561_;
}
else
{
uint8_t v___x_1591_; 
v___x_1591_ = lean_byte_array_fget(v_used_1558_, v___x_1584_);
lean_dec(v___x_1584_);
v___y_1562_ = v___x_1591_;
goto v___jp_1561_;
}
v___jp_1524_:
{
lean_object* v___x_1529_; lean_object* v___f_1530_; lean_object* v___x_1531_; uint8_t v___x_1532_; 
v___x_1529_ = lean_box(v___y_1525_);
lean_inc(v_snd_1520_);
lean_inc(v_fst_1519_);
lean_inc_ref(v___y_1528_);
v___f_1530_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___lam__0___boxed), 8, 4);
lean_closure_set(v___f_1530_, 0, v___y_1528_);
lean_closure_set(v___f_1530_, 1, v_fst_1519_);
lean_closure_set(v___f_1530_, 2, v_snd_1520_);
lean_closure_set(v___f_1530_, 3, v___x_1529_);
v___x_1531_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__0));
v___x_1532_ = lean_nat_dec_eq(v_a_1486_, v___x_1485_);
if (v___x_1532_ == 0)
{
if (v___y_1527_ == 0)
{
lean_dec_ref(v___y_1528_);
lean_dec(v_snd_1520_);
lean_dec(v_fst_1519_);
v___y_1512_ = v___y_1526_;
v___y_1513_ = v___f_1530_;
v___y_1514_ = v___x_1531_;
goto v___jp_1511_;
}
else
{
lean_dec_ref(v___f_1530_);
switch(lean_obj_tag(v___y_1528_))
{
case 1:
{
lean_object* v_rupHints_1533_; size_t v_sz_1534_; size_t v___x_1535_; lean_object* v___x_1536_; lean_object* v_fst_1537_; lean_object* v_snd_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v_rupHints_1533_ = lean_ctor_get(v___y_1528_, 2);
v_sz_1534_ = lean_array_size(v_rupHints_1533_);
v___x_1535_ = ((size_t)0ULL);
lean_inc(v_a_1486_);
v___x_1536_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0(v_a_1486_, v_rupHints_1533_, v_sz_1534_, v___x_1535_, v___x_1531_, v___y_1488_, v___y_1526_);
v_fst_1537_ = lean_ctor_get(v___x_1536_, 0);
lean_inc(v_fst_1537_);
v_snd_1538_ = lean_ctor_get(v___x_1536_, 1);
lean_inc(v_snd_1538_);
lean_dec_ref(v___x_1536_);
v___x_1539_ = lean_box(0);
v___x_1540_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___lam__0(v___y_1528_, v_fst_1519_, v_snd_1520_, v___y_1525_, v___x_1539_, v_fst_1537_, v___y_1488_, v_snd_1538_);
lean_dec(v_fst_1519_);
v___y_1497_ = v___x_1540_;
goto v___jp_1496_;
}
case 2:
{
lean_object* v_rupHints_1541_; lean_object* v_ratHints_1542_; size_t v_sz_1543_; size_t v___x_1544_; lean_object* v___x_1545_; lean_object* v_fst_1546_; lean_object* v_snd_1547_; size_t v_sz_1548_; lean_object* v___x_1549_; lean_object* v_fst_1550_; lean_object* v_snd_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; 
v_rupHints_1541_ = lean_ctor_get(v___y_1528_, 3);
v_ratHints_1542_ = lean_ctor_get(v___y_1528_, 4);
v_sz_1543_ = lean_array_size(v_rupHints_1541_);
v___x_1544_ = ((size_t)0ULL);
lean_inc_n(v_a_1486_, 2);
v___x_1545_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0(v_a_1486_, v_rupHints_1541_, v_sz_1543_, v___x_1544_, v___x_1531_, v___y_1488_, v___y_1526_);
v_fst_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_fst_1546_);
v_snd_1547_ = lean_ctor_get(v___x_1545_, 1);
lean_inc(v_snd_1547_);
lean_dec_ref(v___x_1545_);
v_sz_1548_ = lean_array_size(v_ratHints_1542_);
v___x_1549_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__1(v_a_1486_, v_ratHints_1542_, v_sz_1548_, v___x_1544_, v_fst_1546_, v___y_1488_, v_snd_1547_);
v_fst_1550_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_fst_1550_);
v_snd_1551_ = lean_ctor_get(v___x_1549_, 1);
lean_inc(v_snd_1551_);
lean_dec_ref(v___x_1549_);
v___x_1552_ = lean_box(0);
v___x_1553_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___lam__0(v___y_1528_, v_fst_1519_, v_snd_1520_, v___y_1525_, v___x_1552_, v_fst_1550_, v___y_1488_, v_snd_1551_);
lean_dec(v_fst_1519_);
v___y_1497_ = v___x_1553_;
goto v___jp_1496_;
}
default: 
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1554_ = lean_box(0);
v___x_1555_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___lam__0(v___y_1528_, v_fst_1519_, v_snd_1520_, v___y_1525_, v___x_1554_, v___x_1531_, v___y_1488_, v___y_1526_);
lean_dec(v_fst_1519_);
v___y_1497_ = v___x_1555_;
goto v___jp_1496_;
}
}
}
}
else
{
lean_dec_ref(v___y_1528_);
lean_dec(v_snd_1520_);
lean_dec(v_fst_1519_);
v___y_1512_ = v___y_1526_;
v___y_1513_ = v___f_1530_;
v___y_1514_ = v___x_1531_;
goto v___jp_1511_;
}
}
v___jp_1561_:
{
uint8_t v___x_1563_; uint8_t v___x_1564_; 
v___x_1563_ = 1;
v___x_1564_ = lean_uint8_dec_eq(v___y_1562_, v___x_1563_);
if (v___x_1564_ == 0)
{
lean_object* v___x_1566_; 
if (v_isShared_1523_ == 0)
{
v___x_1566_ = v___x_1522_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_fst_1519_);
lean_ctor_set(v_reuseFailAlloc_1567_, 1, v_snd_1520_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
v_a_1491_ = v___x_1566_;
v_snd_1492_ = v___y_1489_;
goto v___jp_1490_;
}
}
else
{
lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1580_; 
lean_inc_ref(v_lastUse_1560_);
lean_inc_ref(v_mapped_1559_);
lean_inc_ref(v_used_1558_);
lean_del_object(v___x_1522_);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___y_1489_);
if (v_isSharedCheck_1580_ == 0)
{
lean_object* v_unused_1581_; lean_object* v_unused_1582_; lean_object* v_unused_1583_; 
v_unused_1581_ = lean_ctor_get(v___y_1489_, 2);
lean_dec(v_unused_1581_);
v_unused_1582_ = lean_ctor_get(v___y_1489_, 1);
lean_dec(v_unused_1582_);
v_unused_1583_ = lean_ctor_get(v___y_1489_, 0);
lean_dec(v_unused_1583_);
v___x_1569_ = v___y_1489_;
v_isShared_1570_ = v_isSharedCheck_1580_;
goto v_resetjp_1568_;
}
else
{
lean_dec(v___y_1489_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1580_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1574_; 
v___x_1571_ = lean_nat_sub(v_a_1486_, v_initialId_1557_);
lean_inc(v_fst_1519_);
v___x_1572_ = lean_array_set(v_mapped_1559_, v___x_1571_, v_fst_1519_);
lean_dec(v___x_1571_);
if (v_isShared_1570_ == 0)
{
lean_ctor_set(v___x_1569_, 1, v___x_1572_);
v___x_1574_ = v___x_1569_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_used_1558_);
lean_ctor_set(v_reuseFailAlloc_1579_, 1, v___x_1572_);
lean_ctor_set(v_reuseFailAlloc_1579_, 2, v_lastUse_1560_);
v___x_1574_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
lean_object* v___x_1575_; 
v___x_1575_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1___redArg(v_proof_1556_, v_a_1486_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1576_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__4);
v___x_1577_ = l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__2(v___x_1576_);
v___y_1525_ = v___x_1564_;
v___y_1526_ = v___x_1574_;
v___y_1527_ = v___x_1564_;
v___y_1528_ = v___x_1577_;
goto v___jp_1524_;
}
else
{
lean_object* v_val_1578_; 
v_val_1578_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_val_1578_);
lean_dec_ref(v___x_1575_);
v___y_1525_ = v___x_1564_;
v___y_1526_ = v___x_1574_;
v___y_1527_ = v___x_1564_;
v___y_1528_ = v_val_1578_;
goto v___jp_1524_;
}
}
}
}
}
}
}
v___jp_1490_:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1493_ = lean_unsigned_to_nat(1u);
v___x_1494_ = lean_nat_add(v_a_1486_, v___x_1493_);
lean_dec(v_a_1486_);
v_a_1486_ = v___x_1494_;
v_b_1487_ = v_a_1491_;
v___y_1489_ = v_snd_1492_;
goto _start;
}
v___jp_1496_:
{
lean_object* v_fst_1498_; 
v_fst_1498_ = lean_ctor_get(v___y_1497_, 0);
lean_inc(v_fst_1498_);
if (lean_obj_tag(v_fst_1498_) == 0)
{
lean_object* v_snd_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1507_; 
lean_dec(v_a_1486_);
v_snd_1499_ = lean_ctor_get(v___y_1497_, 1);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___y_1497_);
if (v_isSharedCheck_1507_ == 0)
{
lean_object* v_unused_1508_; 
v_unused_1508_ = lean_ctor_get(v___y_1497_, 0);
lean_dec(v_unused_1508_);
v___x_1501_ = v___y_1497_;
v_isShared_1502_ = v_isSharedCheck_1507_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_snd_1499_);
lean_dec(v___y_1497_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1507_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v_a_1503_; lean_object* v___x_1505_; 
v_a_1503_ = lean_ctor_get(v_fst_1498_, 0);
lean_inc(v_a_1503_);
lean_dec_ref(v_fst_1498_);
if (v_isShared_1502_ == 0)
{
lean_ctor_set(v___x_1501_, 0, v_a_1503_);
v___x_1505_ = v___x_1501_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1503_);
lean_ctor_set(v_reuseFailAlloc_1506_, 1, v_snd_1499_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
else
{
lean_object* v_snd_1509_; lean_object* v_a_1510_; 
v_snd_1509_ = lean_ctor_get(v___y_1497_, 1);
lean_inc(v_snd_1509_);
lean_dec_ref(v___y_1497_);
v_a_1510_ = lean_ctor_get(v_fst_1498_, 0);
lean_inc(v_a_1510_);
lean_dec_ref(v_fst_1498_);
v_a_1491_ = v_a_1510_;
v_snd_1492_ = v_snd_1509_;
goto v___jp_1490_;
}
}
v___jp_1511_:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1515_ = lean_box(0);
lean_inc_ref(v___y_1488_);
v___x_1516_ = lean_apply_4(v___y_1513_, v___x_1515_, v___y_1514_, v___y_1488_, v___y_1512_);
v___y_1497_ = v___x_1516_;
goto v___jp_1496_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___boxed(lean_object* v_upperBound_1593_, lean_object* v___x_1594_, lean_object* v_a_1595_, lean_object* v_b_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg(v_upperBound_1593_, v___x_1594_, v_a_1595_, v_b_1596_, v___y_1597_, v___y_1598_);
lean_dec_ref(v___y_1597_);
lean_dec(v___x_1594_);
lean_dec(v_upperBound_1593_);
return v_res_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping(lean_object* v_a_1602_, lean_object* v_a_1603_){
_start:
{
lean_object* v_initialId_1604_; lean_object* v_addEmptyId_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v_fst_1609_; lean_object* v_snd_1610_; lean_object* v_snd_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
v_initialId_1604_ = lean_ctor_get(v_a_1602_, 1);
v_addEmptyId_1605_ = lean_ctor_get(v_a_1602_, 2);
v___x_1606_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping___closed__0));
lean_inc_n(v_initialId_1604_, 2);
v___x_1607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1607_, 0, v_initialId_1604_);
lean_ctor_set(v___x_1607_, 1, v___x_1606_);
v___x_1608_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg(v_addEmptyId_1605_, v_addEmptyId_1605_, v_initialId_1604_, v___x_1607_, v_a_1602_, v_a_1603_);
v_fst_1609_ = lean_ctor_get(v___x_1608_, 0);
lean_inc(v_fst_1609_);
v_snd_1610_ = lean_ctor_get(v___x_1608_, 1);
lean_inc(v_snd_1610_);
lean_dec_ref(v___x_1608_);
v_snd_1611_ = lean_ctor_get(v_fst_1609_, 1);
v_isSharedCheck_1618_ = !lean_is_exclusive(v_fst_1609_);
if (v_isSharedCheck_1618_ == 0)
{
lean_object* v_unused_1619_; 
v_unused_1619_ = lean_ctor_get(v_fst_1609_, 0);
lean_dec(v_unused_1619_);
v___x_1613_ = v_fst_1609_;
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_snd_1611_);
lean_dec(v_fst_1609_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1616_; 
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 1, v_snd_1610_);
lean_ctor_set(v___x_1613_, 0, v_snd_1611_);
v___x_1616_ = v___x_1613_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_snd_1611_);
lean_ctor_set(v_reuseFailAlloc_1617_, 1, v_snd_1610_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping___boxed(lean_object* v_a_1620_, lean_object* v_a_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping(v_a_1620_, v_a_1621_);
lean_dec_ref(v_a_1620_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3(lean_object* v_upperBound_1623_, lean_object* v___x_1624_, lean_object* v_inst_1625_, lean_object* v_R_1626_, lean_object* v_a_1627_, lean_object* v_b_1628_, lean_object* v_c_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v___x_1632_; 
v___x_1632_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg(v_upperBound_1623_, v___x_1624_, v_a_1627_, v_b_1628_, v___y_1630_, v___y_1631_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___boxed(lean_object* v_upperBound_1633_, lean_object* v___x_1634_, lean_object* v_inst_1635_, lean_object* v_R_1636_, lean_object* v_a_1637_, lean_object* v_b_1638_, lean_object* v_c_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_){
_start:
{
lean_object* v_res_1642_; 
v_res_1642_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3(v_upperBound_1633_, v___x_1634_, v_inst_1635_, v_R_1636_, v_a_1637_, v_b_1638_, v_c_1639_, v___y_1640_, v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec(v___x_1634_);
lean_dec(v_upperBound_1633_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0_spec__0(lean_object* v_next_1643_, lean_object* v_as_1644_, size_t v_sz_1645_, size_t v_i_1646_, lean_object* v_b_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0_spec__0___redArg(v_next_1643_, v_as_1644_, v_sz_1645_, v_i_1646_, v_b_1647_, v___y_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0_spec__0___boxed(lean_object* v_next_1651_, lean_object* v_as_1652_, lean_object* v_sz_1653_, lean_object* v_i_1654_, lean_object* v_b_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_){
_start:
{
size_t v_sz_boxed_1658_; size_t v_i_boxed_1659_; lean_object* v_res_1660_; 
v_sz_boxed_1658_ = lean_unbox_usize(v_sz_1653_);
lean_dec(v_sz_1653_);
v_i_boxed_1659_ = lean_unbox_usize(v_i_1654_);
lean_dec(v_i_1654_);
v_res_1660_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0_spec__0(v_next_1651_, v_as_1652_, v_sz_boxed_1658_, v_i_boxed_1659_, v_b_1655_, v___y_1656_, v___y_1657_);
lean_dec_ref(v___y_1656_);
lean_dec_ref(v_as_1652_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_go(lean_object* v_a_1661_, lean_object* v_a_1662_){
_start:
{
lean_object* v___x_1663_; lean_object* v_snd_1664_; lean_object* v___x_1665_; 
v___x_1663_ = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis(v_a_1661_, v_a_1662_);
v_snd_1664_ = lean_ctor_get(v___x_1663_, 1);
lean_inc(v_snd_1664_);
lean_dec_ref(v___x_1663_);
v___x_1665_ = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping(v_a_1661_, v_snd_1664_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_go___boxed(lean_object* v_a_1666_, lean_object* v_a_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_go(v_a_1666_, v_a_1667_);
lean_dec_ref(v_a_1666_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim(lean_object* v_proof_1669_){
_start:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1670_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_LRAT_trim_go___boxed), 2, 0);
v___x_1671_ = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg(v_proof_1669_, v___x_1670_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim___boxed(lean_object* v_proof_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_Lean_Elab_Tactic_BVDecide_LRAT_trim(v_proof_1672_);
lean_dec_ref(v_proof_1672_);
return v_res_1673_;
}
}
lean_object* runtime_initialize_Init_Data_Nat_Fold(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Actions(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashMap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_LRAT_Trim(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Nat_Fold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Actions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_BVDecide_LRAT_Trim(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
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
res = runtime_initialize_Lean_Elab_Tactic_BVDecide_LRAT_Trim(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_BVDecide_LRAT_Trim(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_BVDecide_LRAT_Trim(builtin);
}
#ifdef __cplusplus
}
#endif
