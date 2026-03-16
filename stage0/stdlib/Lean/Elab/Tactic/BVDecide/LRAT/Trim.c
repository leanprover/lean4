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
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_go(lean_object*, lean_object*);
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
lean_object* v___f_521_; lean_object* v___f_522_; lean_object* v___f_523_; lean_object* v___f_524_; lean_object* v___f_525_; lean_object* v___f_526_; lean_object* v___f_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___f_531_; lean_object* v___f_532_; lean_object* v___f_533_; lean_object* v___f_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___f_543_; lean_object* v___x_4261__overap_544_; lean_object* v___x_545_; 
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
lean_inc_ref(v___x_530_);
v___f_531_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_531_, 0, v___x_530_);
lean_inc_ref(v___x_530_);
v___f_532_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_532_, 0, v___x_530_);
lean_inc_ref(v___x_530_);
v___f_533_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_533_, 0, v___x_530_);
lean_inc_ref(v___x_530_);
v___f_534_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_534_, 0, v___x_530_);
lean_inc_ref(v___x_530_);
v___x_535_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_535_, 0, lean_box(0));
lean_closure_set(v___x_535_, 1, lean_box(0));
lean_closure_set(v___x_535_, 2, v___x_530_);
v___x_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_535_);
lean_ctor_set(v___x_536_, 1, v___f_531_);
lean_inc_ref(v___x_530_);
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
v___x_4261__overap_544_ = lean_panic_fn(v___f_543_, v_msg_518_);
v___x_545_ = lean_apply_2(v___x_4261__overap_544_, v___y_519_, v___y_520_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__0(size_t v_sz_546_, size_t v_i_547_, lean_object* v_bs_548_, lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
uint8_t v___x_551_; 
v___x_551_ = lean_usize_dec_lt(v_i_547_, v_sz_546_);
if (v___x_551_ == 0)
{
lean_object* v___x_552_; 
v___x_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_552_, 0, v_bs_548_);
lean_ctor_set(v___x_552_, 1, v___y_550_);
return v___x_552_;
}
else
{
lean_object* v_initialId_553_; lean_object* v_v_554_; lean_object* v___x_555_; lean_object* v_bs_x27_556_; lean_object* v_fst_558_; lean_object* v_snd_559_; uint8_t v___x_564_; 
v_initialId_553_ = lean_ctor_get(v___y_549_, 1);
v_v_554_ = lean_array_uget(v_bs_548_, v_i_547_);
v___x_555_ = lean_unsigned_to_nat(0u);
v_bs_x27_556_ = lean_array_uset(v_bs_548_, v_i_547_, v___x_555_);
v___x_564_ = lean_nat_dec_lt(v_v_554_, v_initialId_553_);
if (v___x_564_ == 0)
{
lean_object* v_mapped_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v_mapped_565_ = lean_ctor_get(v___y_550_, 1);
v___x_566_ = lean_nat_sub(v_v_554_, v_initialId_553_);
lean_dec(v_v_554_);
v___x_567_ = lean_array_get(v___x_555_, v_mapped_565_, v___x_566_);
lean_dec(v___x_566_);
v_fst_558_ = v___x_567_;
v_snd_559_ = v___y_550_;
goto v___jp_557_;
}
else
{
v_fst_558_ = v_v_554_;
v_snd_559_ = v___y_550_;
goto v___jp_557_;
}
v___jp_557_:
{
size_t v___x_560_; size_t v___x_561_; lean_object* v___x_562_; 
v___x_560_ = ((size_t)1ULL);
v___x_561_ = lean_usize_add(v_i_547_, v___x_560_);
v___x_562_ = lean_array_uset(v_bs_x27_556_, v_i_547_, v_fst_558_);
v_i_547_ = v___x_561_;
v_bs_548_ = v___x_562_;
v___y_550_ = v_snd_559_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__0___boxed(lean_object* v_sz_568_, lean_object* v_i_569_, lean_object* v_bs_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
size_t v_sz_boxed_573_; size_t v_i_boxed_574_; lean_object* v_res_575_; 
v_sz_boxed_573_ = lean_unbox_usize(v_sz_568_);
lean_dec(v_sz_568_);
v_i_boxed_574_ = lean_unbox_usize(v_i_569_);
lean_dec(v_i_569_);
v_res_575_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__0(v_sz_boxed_573_, v_i_boxed_574_, v_bs_570_, v___y_571_, v___y_572_);
lean_dec_ref(v___y_571_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__1(size_t v_sz_576_, size_t v_i_577_, lean_object* v_bs_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
uint8_t v___x_581_; 
v___x_581_ = lean_usize_dec_lt(v_i_577_, v_sz_576_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; 
v___x_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_582_, 0, v_bs_578_);
lean_ctor_set(v___x_582_, 1, v___y_580_);
return v___x_582_;
}
else
{
lean_object* v_v_583_; lean_object* v_fst_584_; lean_object* v_initialId_585_; lean_object* v___x_586_; lean_object* v_bs_x27_587_; lean_object* v_fst_589_; lean_object* v_snd_590_; uint8_t v___x_608_; 
v_v_583_ = lean_array_uget(v_bs_578_, v_i_577_);
v_fst_584_ = lean_ctor_get(v_v_583_, 0);
v_initialId_585_ = lean_ctor_get(v___y_579_, 1);
v___x_586_ = lean_unsigned_to_nat(0u);
v_bs_x27_587_ = lean_array_uset(v_bs_578_, v_i_577_, v___x_586_);
v___x_608_ = lean_nat_dec_lt(v_fst_584_, v_initialId_585_);
if (v___x_608_ == 0)
{
lean_object* v_mapped_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v_mapped_609_ = lean_ctor_get(v___y_580_, 1);
v___x_610_ = lean_nat_sub(v_fst_584_, v_initialId_585_);
v___x_611_ = lean_array_get(v___x_586_, v_mapped_609_, v___x_610_);
lean_dec(v___x_610_);
v_fst_589_ = v___x_611_;
v_snd_590_ = v___y_580_;
goto v___jp_588_;
}
else
{
lean_inc(v_fst_584_);
v_fst_589_ = v_fst_584_;
v_snd_590_ = v___y_580_;
goto v___jp_588_;
}
v___jp_588_:
{
lean_object* v_snd_591_; size_t v_sz_592_; size_t v___x_593_; lean_object* v___x_594_; lean_object* v_fst_595_; lean_object* v_snd_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_607_; 
v_snd_591_ = lean_ctor_get(v_v_583_, 1);
lean_inc(v_snd_591_);
lean_dec(v_v_583_);
v_sz_592_ = lean_array_size(v_snd_591_);
v___x_593_ = ((size_t)0ULL);
v___x_594_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__0(v_sz_592_, v___x_593_, v_snd_591_, v___y_579_, v_snd_590_);
v_fst_595_ = lean_ctor_get(v___x_594_, 0);
v_snd_596_ = lean_ctor_get(v___x_594_, 1);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_607_ == 0)
{
v___x_598_ = v___x_594_;
v_isShared_599_ = v_isSharedCheck_607_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_snd_596_);
lean_inc(v_fst_595_);
lean_dec(v___x_594_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_607_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 1, v_fst_595_);
lean_ctor_set(v___x_598_, 0, v_fst_589_);
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_fst_589_);
lean_ctor_set(v_reuseFailAlloc_606_, 1, v_fst_595_);
v___x_601_ = v_reuseFailAlloc_606_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
size_t v___x_602_; size_t v___x_603_; lean_object* v___x_604_; 
v___x_602_ = ((size_t)1ULL);
v___x_603_ = lean_usize_add(v_i_577_, v___x_602_);
v___x_604_ = lean_array_uset(v_bs_x27_587_, v_i_577_, v___x_601_);
v_i_577_ = v___x_603_;
v_bs_578_ = v___x_604_;
v___y_580_ = v_snd_596_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__1___boxed(lean_object* v_sz_612_, lean_object* v_i_613_, lean_object* v_bs_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
size_t v_sz_boxed_617_; size_t v_i_boxed_618_; lean_object* v_res_619_; 
v_sz_boxed_617_ = lean_unbox_usize(v_sz_612_);
lean_dec(v_sz_612_);
v_i_boxed_618_ = lean_unbox_usize(v_i_613_);
lean_dec(v_i_613_);
v_res_619_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__1(v_sz_boxed_617_, v_i_boxed_618_, v_bs_614_, v___y_615_, v___y_616_);
lean_dec_ref(v___y_615_);
return v_res_619_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__3(void){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_623_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__2));
v___x_624_ = lean_unsigned_to_nat(15u);
v___x_625_ = lean_unsigned_to_nat(166u);
v___x_626_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__1));
v___x_627_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__0));
v___x_628_ = l_mkPanicMessageWithDecl(v___x_627_, v___x_626_, v___x_625_, v___x_624_, v___x_623_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep(lean_object* v_step_629_, lean_object* v_a_630_, lean_object* v_a_631_){
_start:
{
switch(lean_obj_tag(v_step_629_))
{
case 0:
{
lean_object* v_id_632_; lean_object* v_rupHints_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_661_; 
v_id_632_ = lean_ctor_get(v_step_629_, 0);
v_rupHints_633_ = lean_ctor_get(v_step_629_, 1);
v_isSharedCheck_661_ = !lean_is_exclusive(v_step_629_);
if (v_isSharedCheck_661_ == 0)
{
v___x_635_ = v_step_629_;
v_isShared_636_ = v_isSharedCheck_661_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_rupHints_633_);
lean_inc(v_id_632_);
lean_dec(v_step_629_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_661_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v_fst_638_; lean_object* v_snd_639_; lean_object* v_initialId_655_; uint8_t v___x_656_; 
v_initialId_655_ = lean_ctor_get(v_a_630_, 1);
v___x_656_ = lean_nat_dec_lt(v_id_632_, v_initialId_655_);
if (v___x_656_ == 0)
{
lean_object* v_mapped_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v_mapped_657_ = lean_ctor_get(v_a_631_, 1);
v___x_658_ = lean_nat_sub(v_id_632_, v_initialId_655_);
lean_dec(v_id_632_);
v___x_659_ = lean_unsigned_to_nat(0u);
v___x_660_ = lean_array_get(v___x_659_, v_mapped_657_, v___x_658_);
lean_dec(v___x_658_);
v_fst_638_ = v___x_660_;
v_snd_639_ = v_a_631_;
goto v___jp_637_;
}
else
{
v_fst_638_ = v_id_632_;
v_snd_639_ = v_a_631_;
goto v___jp_637_;
}
v___jp_637_:
{
size_t v_sz_640_; size_t v___x_641_; lean_object* v___x_642_; lean_object* v_fst_643_; lean_object* v_snd_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_654_; 
v_sz_640_ = lean_array_size(v_rupHints_633_);
v___x_641_ = ((size_t)0ULL);
v___x_642_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__0(v_sz_640_, v___x_641_, v_rupHints_633_, v_a_630_, v_snd_639_);
lean_dec_ref(v_a_630_);
v_fst_643_ = lean_ctor_get(v___x_642_, 0);
v_snd_644_ = lean_ctor_get(v___x_642_, 1);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_654_ == 0)
{
v___x_646_ = v___x_642_;
v_isShared_647_ = v_isSharedCheck_654_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_snd_644_);
lean_inc(v_fst_643_);
lean_dec(v___x_642_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_654_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_649_; 
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 1, v_fst_643_);
lean_ctor_set(v___x_635_, 0, v_fst_638_);
v___x_649_ = v___x_635_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_fst_638_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v_fst_643_);
v___x_649_ = v_reuseFailAlloc_653_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
lean_object* v___x_651_; 
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 0, v___x_649_);
v___x_651_ = v___x_646_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_649_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v_snd_644_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
}
}
case 1:
{
lean_object* v_id_662_; lean_object* v_c_663_; lean_object* v_rupHints_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_692_; 
v_id_662_ = lean_ctor_get(v_step_629_, 0);
v_c_663_ = lean_ctor_get(v_step_629_, 1);
v_rupHints_664_ = lean_ctor_get(v_step_629_, 2);
v_isSharedCheck_692_ = !lean_is_exclusive(v_step_629_);
if (v_isSharedCheck_692_ == 0)
{
v___x_666_ = v_step_629_;
v_isShared_667_ = v_isSharedCheck_692_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_rupHints_664_);
lean_inc(v_c_663_);
lean_inc(v_id_662_);
lean_dec(v_step_629_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_692_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v_fst_669_; lean_object* v_snd_670_; lean_object* v_initialId_686_; uint8_t v___x_687_; 
v_initialId_686_ = lean_ctor_get(v_a_630_, 1);
v___x_687_ = lean_nat_dec_lt(v_id_662_, v_initialId_686_);
if (v___x_687_ == 0)
{
lean_object* v_mapped_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v_mapped_688_ = lean_ctor_get(v_a_631_, 1);
v___x_689_ = lean_nat_sub(v_id_662_, v_initialId_686_);
lean_dec(v_id_662_);
v___x_690_ = lean_unsigned_to_nat(0u);
v___x_691_ = lean_array_get(v___x_690_, v_mapped_688_, v___x_689_);
lean_dec(v___x_689_);
v_fst_669_ = v___x_691_;
v_snd_670_ = v_a_631_;
goto v___jp_668_;
}
else
{
v_fst_669_ = v_id_662_;
v_snd_670_ = v_a_631_;
goto v___jp_668_;
}
v___jp_668_:
{
size_t v_sz_671_; size_t v___x_672_; lean_object* v___x_673_; lean_object* v_fst_674_; lean_object* v_snd_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_685_; 
v_sz_671_ = lean_array_size(v_rupHints_664_);
v___x_672_ = ((size_t)0ULL);
v___x_673_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__0(v_sz_671_, v___x_672_, v_rupHints_664_, v_a_630_, v_snd_670_);
lean_dec_ref(v_a_630_);
v_fst_674_ = lean_ctor_get(v___x_673_, 0);
v_snd_675_ = lean_ctor_get(v___x_673_, 1);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_685_ == 0)
{
v___x_677_ = v___x_673_;
v_isShared_678_ = v_isSharedCheck_685_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_snd_675_);
lean_inc(v_fst_674_);
lean_dec(v___x_673_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_685_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_680_; 
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 2, v_fst_674_);
lean_ctor_set(v___x_666_, 0, v_fst_669_);
v___x_680_ = v___x_666_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_fst_669_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v_c_663_);
lean_ctor_set(v_reuseFailAlloc_684_, 2, v_fst_674_);
v___x_680_ = v_reuseFailAlloc_684_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
lean_object* v___x_682_; 
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 0, v___x_680_);
v___x_682_ = v___x_677_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_680_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v_snd_675_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
}
}
}
case 2:
{
lean_object* v_id_693_; lean_object* v_c_694_; lean_object* v_pivot_695_; lean_object* v_rupHints_696_; lean_object* v_ratHints_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_729_; 
v_id_693_ = lean_ctor_get(v_step_629_, 0);
v_c_694_ = lean_ctor_get(v_step_629_, 1);
v_pivot_695_ = lean_ctor_get(v_step_629_, 2);
v_rupHints_696_ = lean_ctor_get(v_step_629_, 3);
v_ratHints_697_ = lean_ctor_get(v_step_629_, 4);
v_isSharedCheck_729_ = !lean_is_exclusive(v_step_629_);
if (v_isSharedCheck_729_ == 0)
{
v___x_699_ = v_step_629_;
v_isShared_700_ = v_isSharedCheck_729_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_ratHints_697_);
lean_inc(v_rupHints_696_);
lean_inc(v_pivot_695_);
lean_inc(v_c_694_);
lean_inc(v_id_693_);
lean_dec(v_step_629_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_729_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v_fst_702_; lean_object* v_snd_703_; lean_object* v_initialId_723_; uint8_t v___x_724_; 
v_initialId_723_ = lean_ctor_get(v_a_630_, 1);
v___x_724_ = lean_nat_dec_lt(v_id_693_, v_initialId_723_);
if (v___x_724_ == 0)
{
lean_object* v_mapped_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v_mapped_725_ = lean_ctor_get(v_a_631_, 1);
v___x_726_ = lean_nat_sub(v_id_693_, v_initialId_723_);
lean_dec(v_id_693_);
v___x_727_ = lean_unsigned_to_nat(0u);
v___x_728_ = lean_array_get(v___x_727_, v_mapped_725_, v___x_726_);
lean_dec(v___x_726_);
v_fst_702_ = v___x_728_;
v_snd_703_ = v_a_631_;
goto v___jp_701_;
}
else
{
v_fst_702_ = v_id_693_;
v_snd_703_ = v_a_631_;
goto v___jp_701_;
}
v___jp_701_:
{
size_t v_sz_704_; size_t v___x_705_; lean_object* v___x_706_; lean_object* v_fst_707_; lean_object* v_snd_708_; size_t v_sz_709_; lean_object* v___x_710_; lean_object* v_fst_711_; lean_object* v_snd_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_722_; 
v_sz_704_ = lean_array_size(v_rupHints_696_);
v___x_705_ = ((size_t)0ULL);
v___x_706_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__0(v_sz_704_, v___x_705_, v_rupHints_696_, v_a_630_, v_snd_703_);
v_fst_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_fst_707_);
v_snd_708_ = lean_ctor_get(v___x_706_, 1);
lean_inc(v_snd_708_);
lean_dec_ref(v___x_706_);
v_sz_709_ = lean_array_size(v_ratHints_697_);
v___x_710_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__1(v_sz_709_, v___x_705_, v_ratHints_697_, v_a_630_, v_snd_708_);
lean_dec_ref(v_a_630_);
v_fst_711_ = lean_ctor_get(v___x_710_, 0);
v_snd_712_ = lean_ctor_get(v___x_710_, 1);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_710_);
if (v_isSharedCheck_722_ == 0)
{
v___x_714_ = v___x_710_;
v_isShared_715_ = v_isSharedCheck_722_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_snd_712_);
lean_inc(v_fst_711_);
lean_dec(v___x_710_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_722_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 4, v_fst_711_);
lean_ctor_set(v___x_699_, 3, v_fst_707_);
lean_ctor_set(v___x_699_, 0, v_fst_702_);
v___x_717_ = v___x_699_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_fst_702_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_c_694_);
lean_ctor_set(v_reuseFailAlloc_721_, 2, v_pivot_695_);
lean_ctor_set(v_reuseFailAlloc_721_, 3, v_fst_707_);
lean_ctor_set(v_reuseFailAlloc_721_, 4, v_fst_711_);
v___x_717_ = v_reuseFailAlloc_721_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
lean_object* v___x_719_; 
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 0, v___x_717_);
v___x_719_ = v___x_714_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_717_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v_snd_712_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_730_; lean_object* v___x_731_; 
lean_dec_ref(v_step_629_);
v___x_730_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__3, &l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__3);
v___x_731_ = l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2(v___x_730_, v_a_630_, v_a_631_);
return v___x_731_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__0(lean_object* v_a_732_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = lean_nat_to_int(v_a_732_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__3___redArg(lean_object* v_id_734_, lean_object* v_as_735_, size_t v_sz_736_, size_t v_i_737_, lean_object* v_b_738_, lean_object* v___y_739_){
_start:
{
uint8_t v___x_740_; 
v___x_740_ = lean_usize_dec_lt(v_i_737_, v_sz_736_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; 
lean_dec(v_id_734_);
v___x_741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_741_, 0, v_b_738_);
lean_ctor_set(v___x_741_, 1, v___y_739_);
return v___x_741_;
}
else
{
lean_object* v_used_742_; lean_object* v_mapped_743_; lean_object* v_lastUse_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_763_; 
v_used_742_ = lean_ctor_get(v___y_739_, 0);
v_mapped_743_ = lean_ctor_get(v___y_739_, 1);
v_lastUse_744_ = lean_ctor_get(v___y_739_, 2);
v_isSharedCheck_763_ = !lean_is_exclusive(v___y_739_);
if (v_isSharedCheck_763_ == 0)
{
v___x_746_ = v___y_739_;
v_isShared_747_ = v_isSharedCheck_763_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_lastUse_744_);
lean_inc(v_mapped_743_);
lean_inc(v_used_742_);
lean_dec(v___y_739_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_763_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_748_; lean_object* v_a_749_; lean_object* v___y_751_; lean_object* v___x_759_; lean_object* v_prev_760_; lean_object* v___x_761_; uint8_t v___x_762_; 
v___x_748_ = lean_box(0);
v_a_749_ = lean_array_uget_borrowed(v_as_735_, v_i_737_);
v___x_759_ = l_Int_instInhabited;
v_prev_760_ = lean_array_get_borrowed(v___x_759_, v_lastUse_744_, v_a_749_);
lean_inc(v_id_734_);
v___x_761_ = lean_nat_to_int(v_id_734_);
v___x_762_ = lean_int_dec_le(v_prev_760_, v___x_761_);
if (v___x_762_ == 0)
{
lean_dec(v___x_761_);
lean_inc(v_prev_760_);
v___y_751_ = v_prev_760_;
goto v___jp_750_;
}
else
{
v___y_751_ = v___x_761_;
goto v___jp_750_;
}
v___jp_750_:
{
lean_object* v___x_752_; lean_object* v___x_754_; 
v___x_752_ = lean_array_set(v_lastUse_744_, v_a_749_, v___y_751_);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 2, v___x_752_);
v___x_754_ = v___x_746_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_used_742_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v_mapped_743_);
lean_ctor_set(v_reuseFailAlloc_758_, 2, v___x_752_);
v___x_754_ = v_reuseFailAlloc_758_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
size_t v___x_755_; size_t v___x_756_; 
v___x_755_ = ((size_t)1ULL);
v___x_756_ = lean_usize_add(v_i_737_, v___x_755_);
v_i_737_ = v___x_756_;
v_b_738_ = v___x_748_;
v___y_739_ = v___x_754_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__3___redArg___boxed(lean_object* v_id_764_, lean_object* v_as_765_, lean_object* v_sz_766_, lean_object* v_i_767_, lean_object* v_b_768_, lean_object* v___y_769_){
_start:
{
size_t v_sz_boxed_770_; size_t v_i_boxed_771_; lean_object* v_res_772_; 
v_sz_boxed_770_ = lean_unbox_usize(v_sz_766_);
lean_dec(v_sz_766_);
v_i_boxed_771_ = lean_unbox_usize(v_i_767_);
lean_dec(v_i_767_);
v_res_772_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__3___redArg(v_id_764_, v_as_765_, v_sz_boxed_770_, v_i_boxed_771_, v_b_768_, v___y_769_);
lean_dec_ref(v_as_765_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__5(lean_object* v_as_773_, size_t v_i_774_, size_t v_stop_775_, lean_object* v_b_776_){
_start:
{
uint8_t v___x_777_; 
v___x_777_ = lean_usize_dec_eq(v_i_774_, v_stop_775_);
if (v___x_777_ == 0)
{
lean_object* v___x_778_; lean_object* v_fst_779_; lean_object* v_snd_780_; lean_object* v___x_781_; lean_object* v___x_782_; size_t v___x_783_; size_t v___x_784_; 
v___x_778_ = lean_array_uget_borrowed(v_as_773_, v_i_774_);
v_fst_779_ = lean_ctor_get(v___x_778_, 0);
v_snd_780_ = lean_ctor_get(v___x_778_, 1);
lean_inc(v_fst_779_);
v___x_781_ = lean_array_push(v_b_776_, v_fst_779_);
v___x_782_ = l_Array_append___redArg(v___x_781_, v_snd_780_);
v___x_783_ = ((size_t)1ULL);
v___x_784_ = lean_usize_add(v_i_774_, v___x_783_);
v_i_774_ = v___x_784_;
v_b_776_ = v___x_782_;
goto _start;
}
else
{
return v_b_776_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__5___boxed(lean_object* v_as_786_, lean_object* v_i_787_, lean_object* v_stop_788_, lean_object* v_b_789_){
_start:
{
size_t v_i_boxed_790_; size_t v_stop_boxed_791_; lean_object* v_res_792_; 
v_i_boxed_790_ = lean_unbox_usize(v_i_787_);
lean_dec(v_i_787_);
v_stop_boxed_791_ = lean_unbox_usize(v_stop_788_);
lean_dec(v_stop_788_);
v_res_792_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__5(v_as_786_, v_i_boxed_790_, v_stop_boxed_791_, v_b_789_);
lean_dec_ref(v_as_786_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2___redArg(lean_object* v_id_793_, lean_object* v_as_794_, size_t v_i_795_, size_t v_stop_796_, lean_object* v_b_797_, lean_object* v___y_798_){
_start:
{
uint8_t v___x_799_; 
v___x_799_ = lean_usize_dec_eq(v_i_795_, v_stop_796_);
if (v___x_799_ == 0)
{
lean_object* v_used_800_; lean_object* v_mapped_801_; lean_object* v_lastUse_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_821_; 
v_used_800_ = lean_ctor_get(v___y_798_, 0);
v_mapped_801_ = lean_ctor_get(v___y_798_, 1);
v_lastUse_802_ = lean_ctor_get(v___y_798_, 2);
v_isSharedCheck_821_ = !lean_is_exclusive(v___y_798_);
if (v_isSharedCheck_821_ == 0)
{
v___x_804_ = v___y_798_;
v_isShared_805_ = v_isSharedCheck_821_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_lastUse_802_);
lean_inc(v_mapped_801_);
lean_inc(v_used_800_);
lean_dec(v___y_798_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_821_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___y_810_; lean_object* v_prev_818_; lean_object* v___x_819_; uint8_t v___x_820_; 
v___x_806_ = lean_array_uget_borrowed(v_as_794_, v_i_795_);
v___x_807_ = l_Int_instInhabited;
v___x_808_ = lean_box(0);
v_prev_818_ = lean_array_get_borrowed(v___x_807_, v_lastUse_802_, v___x_806_);
lean_inc(v_id_793_);
v___x_819_ = lean_nat_to_int(v_id_793_);
v___x_820_ = lean_int_dec_le(v_prev_818_, v___x_819_);
if (v___x_820_ == 0)
{
lean_dec(v___x_819_);
lean_inc(v_prev_818_);
v___y_810_ = v_prev_818_;
goto v___jp_809_;
}
else
{
v___y_810_ = v___x_819_;
goto v___jp_809_;
}
v___jp_809_:
{
lean_object* v___x_811_; lean_object* v___x_813_; 
v___x_811_ = lean_array_set(v_lastUse_802_, v___x_806_, v___y_810_);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 2, v___x_811_);
v___x_813_ = v___x_804_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_used_800_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v_mapped_801_);
lean_ctor_set(v_reuseFailAlloc_817_, 2, v___x_811_);
v___x_813_ = v_reuseFailAlloc_817_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
size_t v___x_814_; size_t v___x_815_; 
v___x_814_ = ((size_t)1ULL);
v___x_815_ = lean_usize_add(v_i_795_, v___x_814_);
v_i_795_ = v___x_815_;
v_b_797_ = v___x_808_;
v___y_798_ = v___x_813_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_822_; 
lean_dec(v_id_793_);
v___x_822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_822_, 0, v_b_797_);
lean_ctor_set(v___x_822_, 1, v___y_798_);
return v___x_822_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2___redArg___boxed(lean_object* v_id_823_, lean_object* v_as_824_, lean_object* v_i_825_, lean_object* v_stop_826_, lean_object* v_b_827_, lean_object* v___y_828_){
_start:
{
size_t v_i_boxed_829_; size_t v_stop_boxed_830_; lean_object* v_res_831_; 
v_i_boxed_829_ = lean_unbox_usize(v_i_825_);
lean_dec(v_i_825_);
v_stop_boxed_830_ = lean_unbox_usize(v_stop_826_);
lean_dec(v_stop_826_);
v_res_831_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2___redArg(v_id_823_, v_as_824_, v_i_boxed_829_, v_stop_boxed_830_, v_b_827_, v___y_828_);
lean_dec_ref(v_as_824_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__4(lean_object* v_id_832_, lean_object* v_as_833_, size_t v_i_834_, size_t v_stop_835_, lean_object* v_b_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
uint8_t v___x_839_; 
v___x_839_ = lean_usize_dec_eq(v_i_834_, v_stop_835_);
if (v___x_839_ == 0)
{
lean_object* v_used_840_; lean_object* v_mapped_841_; lean_object* v_lastUse_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_861_; 
v_used_840_ = lean_ctor_get(v___y_838_, 0);
v_mapped_841_ = lean_ctor_get(v___y_838_, 1);
v_lastUse_842_ = lean_ctor_get(v___y_838_, 2);
v_isSharedCheck_861_ = !lean_is_exclusive(v___y_838_);
if (v_isSharedCheck_861_ == 0)
{
v___x_844_ = v___y_838_;
v_isShared_845_ = v_isSharedCheck_861_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_lastUse_842_);
lean_inc(v_mapped_841_);
lean_inc(v_used_840_);
lean_dec(v___y_838_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_861_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___y_850_; lean_object* v_prev_858_; lean_object* v___x_859_; uint8_t v___x_860_; 
v___x_846_ = lean_array_uget_borrowed(v_as_833_, v_i_834_);
v___x_847_ = l_Int_instInhabited;
v___x_848_ = lean_box(0);
v_prev_858_ = lean_array_get_borrowed(v___x_847_, v_lastUse_842_, v___x_846_);
lean_inc(v_id_832_);
v___x_859_ = lean_nat_to_int(v_id_832_);
v___x_860_ = lean_int_dec_le(v_prev_858_, v___x_859_);
if (v___x_860_ == 0)
{
lean_dec(v___x_859_);
lean_inc(v_prev_858_);
v___y_850_ = v_prev_858_;
goto v___jp_849_;
}
else
{
v___y_850_ = v___x_859_;
goto v___jp_849_;
}
v___jp_849_:
{
lean_object* v___x_851_; lean_object* v___x_853_; 
v___x_851_ = lean_array_set(v_lastUse_842_, v___x_846_, v___y_850_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 2, v___x_851_);
v___x_853_ = v___x_844_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_used_840_);
lean_ctor_set(v_reuseFailAlloc_857_, 1, v_mapped_841_);
lean_ctor_set(v_reuseFailAlloc_857_, 2, v___x_851_);
v___x_853_ = v_reuseFailAlloc_857_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
size_t v___x_854_; size_t v___x_855_; lean_object* v___x_856_; 
v___x_854_ = ((size_t)1ULL);
v___x_855_ = lean_usize_add(v_i_834_, v___x_854_);
v___x_856_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2___redArg(v_id_832_, v_as_833_, v___x_855_, v_stop_835_, v___x_848_, v___x_853_);
return v___x_856_;
}
}
}
}
else
{
lean_object* v___x_862_; 
lean_dec(v_id_832_);
v___x_862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_862_, 0, v_b_836_);
lean_ctor_set(v___x_862_, 1, v___y_838_);
return v___x_862_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__4___boxed(lean_object* v_id_863_, lean_object* v_as_864_, lean_object* v_i_865_, lean_object* v_stop_866_, lean_object* v_b_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
size_t v_i_boxed_870_; size_t v_stop_boxed_871_; lean_object* v_res_872_; 
v_i_boxed_870_ = lean_unbox_usize(v_i_865_);
lean_dec(v_i_865_);
v_stop_boxed_871_ = lean_unbox_usize(v_stop_866_);
lean_dec(v_stop_866_);
v_res_872_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__4(v_id_863_, v_as_864_, v_i_boxed_870_, v_stop_boxed_871_, v_b_867_, v___y_868_, v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec_ref(v_as_864_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1_spec__1___redArg(lean_object* v_a_873_, lean_object* v_x_874_){
_start:
{
if (lean_obj_tag(v_x_874_) == 0)
{
lean_object* v___x_875_; 
v___x_875_ = lean_box(0);
return v___x_875_;
}
else
{
lean_object* v_key_876_; lean_object* v_value_877_; lean_object* v_tail_878_; uint8_t v___x_879_; 
v_key_876_ = lean_ctor_get(v_x_874_, 0);
v_value_877_ = lean_ctor_get(v_x_874_, 1);
v_tail_878_ = lean_ctor_get(v_x_874_, 2);
v___x_879_ = lean_nat_dec_eq(v_key_876_, v_a_873_);
if (v___x_879_ == 0)
{
v_x_874_ = v_tail_878_;
goto _start;
}
else
{
lean_object* v___x_881_; 
lean_inc(v_value_877_);
v___x_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_881_, 0, v_value_877_);
return v___x_881_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1_spec__1___redArg___boxed(lean_object* v_a_882_, lean_object* v_x_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1_spec__1___redArg(v_a_882_, v_x_883_);
lean_dec(v_x_883_);
lean_dec(v_a_882_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1___redArg(lean_object* v_m_885_, lean_object* v_a_886_){
_start:
{
lean_object* v_buckets_887_; lean_object* v___x_888_; uint64_t v___x_889_; uint64_t v___x_890_; uint64_t v___x_891_; uint64_t v_fold_892_; uint64_t v___x_893_; uint64_t v___x_894_; uint64_t v___x_895_; size_t v___x_896_; size_t v___x_897_; size_t v___x_898_; size_t v___x_899_; size_t v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v_buckets_887_ = lean_ctor_get(v_m_885_, 1);
v___x_888_ = lean_array_get_size(v_buckets_887_);
v___x_889_ = lean_uint64_of_nat(v_a_886_);
v___x_890_ = 32ULL;
v___x_891_ = lean_uint64_shift_right(v___x_889_, v___x_890_);
v_fold_892_ = lean_uint64_xor(v___x_889_, v___x_891_);
v___x_893_ = 16ULL;
v___x_894_ = lean_uint64_shift_right(v_fold_892_, v___x_893_);
v___x_895_ = lean_uint64_xor(v_fold_892_, v___x_894_);
v___x_896_ = lean_uint64_to_usize(v___x_895_);
v___x_897_ = lean_usize_of_nat(v___x_888_);
v___x_898_ = ((size_t)1ULL);
v___x_899_ = lean_usize_sub(v___x_897_, v___x_898_);
v___x_900_ = lean_usize_land(v___x_896_, v___x_899_);
v___x_901_ = lean_array_uget_borrowed(v_buckets_887_, v___x_900_);
v___x_902_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1_spec__1___redArg(v_a_886_, v___x_901_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1___redArg___boxed(lean_object* v_m_903_, lean_object* v_a_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1___redArg(v_m_903_, v_a_904_);
lean_dec(v_a_904_);
lean_dec_ref(v_m_903_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go(lean_object* v_worklist_906_, lean_object* v_a_907_, lean_object* v_a_908_){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; uint8_t v___x_911_; 
v___x_909_ = lean_array_get_size(v_worklist_906_);
v___x_910_ = lean_unsigned_to_nat(0u);
v___x_911_ = lean_nat_dec_eq(v___x_909_, v___x_910_);
if (v___x_911_ == 0)
{
lean_object* v_proof_912_; lean_object* v_initialId_913_; lean_object* v_used_914_; lean_object* v_mapped_915_; lean_object* v_lastUse_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v_id_919_; lean_object* v_worklist_920_; lean_object* v___y_922_; lean_object* v_snd_923_; lean_object* v___y_927_; lean_object* v___y_928_; lean_object* v___y_931_; lean_object* v_snd_932_; lean_object* v___y_936_; lean_object* v___y_937_; lean_object* v___y_940_; lean_object* v___y_941_; lean_object* v_snd_942_; lean_object* v___y_947_; lean_object* v___y_948_; lean_object* v___y_949_; lean_object* v___y_952_; lean_object* v___y_953_; size_t v___y_954_; lean_object* v___y_955_; lean_object* v___y_956_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v_snd_967_; lean_object* v___y_982_; lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v_snd_987_; uint8_t v___y_1027_; lean_object* v___x_1044_; lean_object* v___x_1045_; uint8_t v___x_1046_; 
v_proof_912_ = lean_ctor_get(v_a_907_, 0);
v_initialId_913_ = lean_ctor_get(v_a_907_, 1);
v_used_914_ = lean_ctor_get(v_a_908_, 0);
v_mapped_915_ = lean_ctor_get(v_a_908_, 1);
v_lastUse_916_ = lean_ctor_get(v_a_908_, 2);
v___x_917_ = lean_unsigned_to_nat(1u);
v___x_918_ = lean_nat_sub(v___x_909_, v___x_917_);
v_id_919_ = lean_array_fget(v_worklist_906_, v___x_918_);
lean_dec(v___x_918_);
v_worklist_920_ = lean_array_pop(v_worklist_906_);
v___x_1044_ = lean_nat_sub(v_id_919_, v_initialId_913_);
v___x_1045_ = lean_byte_array_size(v_used_914_);
v___x_1046_ = lean_nat_dec_lt(v___x_1044_, v___x_1045_);
if (v___x_1046_ == 0)
{
uint8_t v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; uint8_t v___x_1050_; 
lean_dec(v___x_1044_);
v___x_1047_ = l_instInhabitedUInt8;
v___x_1048_ = lean_box(v___x_1047_);
v___x_1049_ = l_outOfBounds___redArg(v___x_1048_);
v___x_1050_ = lean_unbox(v___x_1049_);
lean_dec(v___x_1049_);
v___y_1027_ = v___x_1050_;
goto v___jp_1026_;
}
else
{
uint8_t v___x_1051_; 
v___x_1051_ = lean_byte_array_fget(v_used_914_, v___x_1044_);
lean_dec(v___x_1044_);
v___y_1027_ = v___x_1051_;
goto v___jp_1026_;
}
v___jp_921_:
{
lean_object* v___x_924_; 
v___x_924_ = l_Array_append___redArg(v_worklist_920_, v___y_922_);
lean_dec_ref(v___y_922_);
v_worklist_906_ = v___x_924_;
v_a_908_ = v_snd_923_;
goto _start;
}
v___jp_926_:
{
lean_object* v_snd_929_; 
v_snd_929_ = lean_ctor_get(v___y_928_, 1);
lean_inc(v_snd_929_);
lean_dec_ref(v___y_928_);
v___y_922_ = v___y_927_;
v_snd_923_ = v_snd_929_;
goto v___jp_921_;
}
v___jp_930_:
{
lean_object* v___x_933_; 
v___x_933_ = l_Array_append___redArg(v_worklist_920_, v___y_931_);
lean_dec_ref(v___y_931_);
v_worklist_906_ = v___x_933_;
v_a_908_ = v_snd_932_;
goto _start;
}
v___jp_935_:
{
lean_object* v_snd_938_; 
v_snd_938_ = lean_ctor_get(v___y_937_, 1);
lean_inc(v_snd_938_);
lean_dec_ref(v___y_937_);
v___y_931_ = v___y_936_;
v_snd_932_ = v_snd_938_;
goto v___jp_930_;
}
v___jp_939_:
{
lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_943_ = l_Array_append___redArg(v_worklist_920_, v___y_940_);
lean_dec_ref(v___y_940_);
v___x_944_ = l_Array_append___redArg(v___x_943_, v___y_941_);
lean_dec_ref(v___y_941_);
v_worklist_906_ = v___x_944_;
v_a_908_ = v_snd_942_;
goto _start;
}
v___jp_946_:
{
lean_object* v_snd_950_; 
v_snd_950_ = lean_ctor_get(v___y_949_, 1);
lean_inc(v_snd_950_);
lean_dec_ref(v___y_949_);
v___y_940_ = v___y_947_;
v___y_941_ = v___y_948_;
v_snd_942_ = v_snd_950_;
goto v___jp_939_;
}
v___jp_951_:
{
lean_object* v___x_957_; uint8_t v___x_958_; 
v___x_957_ = lean_array_get_size(v___y_956_);
v___x_958_ = lean_nat_dec_lt(v___x_910_, v___x_957_);
if (v___x_958_ == 0)
{
lean_dec(v_id_919_);
v___y_940_ = v___y_956_;
v___y_941_ = v___y_955_;
v_snd_942_ = v___y_953_;
goto v___jp_939_;
}
else
{
uint8_t v___x_959_; 
v___x_959_ = lean_nat_dec_le(v___x_957_, v___x_957_);
if (v___x_959_ == 0)
{
if (v___x_958_ == 0)
{
lean_dec(v_id_919_);
v___y_940_ = v___y_956_;
v___y_941_ = v___y_955_;
v_snd_942_ = v___y_953_;
goto v___jp_939_;
}
else
{
size_t v___x_960_; lean_object* v___x_961_; 
v___x_960_ = lean_usize_of_nat(v___x_957_);
v___x_961_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__4(v_id_919_, v___y_956_, v___y_954_, v___x_960_, v___y_952_, v_a_907_, v___y_953_);
v___y_947_ = v___y_956_;
v___y_948_ = v___y_955_;
v___y_949_ = v___x_961_;
goto v___jp_946_;
}
}
else
{
size_t v___x_962_; lean_object* v___x_963_; 
v___x_962_ = lean_usize_of_nat(v___x_957_);
v___x_963_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__4(v_id_919_, v___y_956_, v___y_954_, v___x_962_, v___y_952_, v_a_907_, v___y_953_);
v___y_947_ = v___y_956_;
v___y_948_ = v___y_955_;
v___y_949_ = v___x_963_;
goto v___jp_946_;
}
}
}
v___jp_964_:
{
lean_object* v___x_968_; size_t v_sz_969_; size_t v___x_970_; lean_object* v___x_971_; lean_object* v_snd_972_; lean_object* v___x_973_; lean_object* v___x_974_; uint8_t v___x_975_; 
v___x_968_ = lean_box(0);
v_sz_969_ = lean_array_size(v___y_965_);
v___x_970_ = ((size_t)0ULL);
lean_inc(v_id_919_);
v___x_971_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__3___redArg(v_id_919_, v___y_965_, v_sz_969_, v___x_970_, v___x_968_, v_snd_967_);
v_snd_972_ = lean_ctor_get(v___x_971_, 1);
lean_inc(v_snd_972_);
lean_dec_ref(v___x_971_);
v___x_973_ = lean_array_get_size(v___y_966_);
v___x_974_ = lean_mk_empty_array_with_capacity(v___x_973_);
v___x_975_ = lean_nat_dec_lt(v___x_910_, v___x_973_);
if (v___x_975_ == 0)
{
lean_dec_ref(v___y_966_);
v___y_952_ = v___x_968_;
v___y_953_ = v_snd_972_;
v___y_954_ = v___x_970_;
v___y_955_ = v___y_965_;
v___y_956_ = v___x_974_;
goto v___jp_951_;
}
else
{
uint8_t v___x_976_; 
v___x_976_ = lean_nat_dec_le(v___x_973_, v___x_973_);
if (v___x_976_ == 0)
{
if (v___x_975_ == 0)
{
lean_dec_ref(v___y_966_);
v___y_952_ = v___x_968_;
v___y_953_ = v_snd_972_;
v___y_954_ = v___x_970_;
v___y_955_ = v___y_965_;
v___y_956_ = v___x_974_;
goto v___jp_951_;
}
else
{
size_t v___x_977_; lean_object* v___x_978_; 
v___x_977_ = lean_usize_of_nat(v___x_973_);
v___x_978_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__5(v___y_966_, v___x_970_, v___x_977_, v___x_974_);
lean_dec_ref(v___y_966_);
v___y_952_ = v___x_968_;
v___y_953_ = v_snd_972_;
v___y_954_ = v___x_970_;
v___y_955_ = v___y_965_;
v___y_956_ = v___x_978_;
goto v___jp_951_;
}
}
else
{
size_t v___x_979_; lean_object* v___x_980_; 
v___x_979_ = lean_usize_of_nat(v___x_973_);
v___x_980_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__5(v___y_966_, v___x_970_, v___x_979_, v___x_974_);
lean_dec_ref(v___y_966_);
v___y_952_ = v___x_968_;
v___y_953_ = v_snd_972_;
v___y_954_ = v___x_970_;
v___y_955_ = v___y_965_;
v___y_956_ = v___x_980_;
goto v___jp_951_;
}
}
}
v___jp_981_:
{
lean_object* v_snd_985_; 
v_snd_985_ = lean_ctor_get(v___y_984_, 1);
lean_inc(v_snd_985_);
lean_dec_ref(v___y_984_);
v___y_965_ = v___y_982_;
v___y_966_ = v___y_983_;
v_snd_967_ = v_snd_985_;
goto v___jp_964_;
}
v___jp_986_:
{
lean_object* v___x_988_; 
v___x_988_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1___redArg(v_proof_912_, v_id_919_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_dec(v_id_919_);
v_worklist_906_ = v_worklist_920_;
v_a_908_ = v_snd_987_;
goto _start;
}
else
{
lean_object* v_val_990_; 
v_val_990_ = lean_ctor_get(v___x_988_, 0);
lean_inc(v_val_990_);
lean_dec_ref(v___x_988_);
switch(lean_obj_tag(v_val_990_))
{
case 0:
{
lean_object* v_rupHints_991_; lean_object* v___x_992_; uint8_t v___x_993_; 
v_rupHints_991_ = lean_ctor_get(v_val_990_, 1);
lean_inc_ref(v_rupHints_991_);
lean_dec_ref(v_val_990_);
v___x_992_ = lean_array_get_size(v_rupHints_991_);
v___x_993_ = lean_nat_dec_lt(v___x_910_, v___x_992_);
if (v___x_993_ == 0)
{
lean_dec(v_id_919_);
v___y_922_ = v_rupHints_991_;
v_snd_923_ = v_snd_987_;
goto v___jp_921_;
}
else
{
lean_object* v___x_994_; uint8_t v___x_995_; 
v___x_994_ = lean_box(0);
v___x_995_ = lean_nat_dec_le(v___x_992_, v___x_992_);
if (v___x_995_ == 0)
{
if (v___x_993_ == 0)
{
lean_dec(v_id_919_);
v___y_922_ = v_rupHints_991_;
v_snd_923_ = v_snd_987_;
goto v___jp_921_;
}
else
{
size_t v___x_996_; size_t v___x_997_; lean_object* v___x_998_; 
v___x_996_ = ((size_t)0ULL);
v___x_997_ = lean_usize_of_nat(v___x_992_);
v___x_998_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2___redArg(v_id_919_, v_rupHints_991_, v___x_996_, v___x_997_, v___x_994_, v_snd_987_);
v___y_927_ = v_rupHints_991_;
v___y_928_ = v___x_998_;
goto v___jp_926_;
}
}
else
{
size_t v___x_999_; size_t v___x_1000_; lean_object* v___x_1001_; 
v___x_999_ = ((size_t)0ULL);
v___x_1000_ = lean_usize_of_nat(v___x_992_);
v___x_1001_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2___redArg(v_id_919_, v_rupHints_991_, v___x_999_, v___x_1000_, v___x_994_, v_snd_987_);
v___y_927_ = v_rupHints_991_;
v___y_928_ = v___x_1001_;
goto v___jp_926_;
}
}
}
case 1:
{
lean_object* v_rupHints_1002_; lean_object* v___x_1003_; uint8_t v___x_1004_; 
v_rupHints_1002_ = lean_ctor_get(v_val_990_, 2);
lean_inc_ref(v_rupHints_1002_);
lean_dec_ref(v_val_990_);
v___x_1003_ = lean_array_get_size(v_rupHints_1002_);
v___x_1004_ = lean_nat_dec_lt(v___x_910_, v___x_1003_);
if (v___x_1004_ == 0)
{
lean_dec(v_id_919_);
v___y_931_ = v_rupHints_1002_;
v_snd_932_ = v_snd_987_;
goto v___jp_930_;
}
else
{
lean_object* v___x_1005_; uint8_t v___x_1006_; 
v___x_1005_ = lean_box(0);
v___x_1006_ = lean_nat_dec_le(v___x_1003_, v___x_1003_);
if (v___x_1006_ == 0)
{
if (v___x_1004_ == 0)
{
lean_dec(v_id_919_);
v___y_931_ = v_rupHints_1002_;
v_snd_932_ = v_snd_987_;
goto v___jp_930_;
}
else
{
size_t v___x_1007_; size_t v___x_1008_; lean_object* v___x_1009_; 
v___x_1007_ = ((size_t)0ULL);
v___x_1008_ = lean_usize_of_nat(v___x_1003_);
v___x_1009_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2___redArg(v_id_919_, v_rupHints_1002_, v___x_1007_, v___x_1008_, v___x_1005_, v_snd_987_);
v___y_936_ = v_rupHints_1002_;
v___y_937_ = v___x_1009_;
goto v___jp_935_;
}
}
else
{
size_t v___x_1010_; size_t v___x_1011_; lean_object* v___x_1012_; 
v___x_1010_ = ((size_t)0ULL);
v___x_1011_ = lean_usize_of_nat(v___x_1003_);
v___x_1012_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2___redArg(v_id_919_, v_rupHints_1002_, v___x_1010_, v___x_1011_, v___x_1005_, v_snd_987_);
v___y_936_ = v_rupHints_1002_;
v___y_937_ = v___x_1012_;
goto v___jp_935_;
}
}
}
case 2:
{
lean_object* v_rupHints_1013_; lean_object* v_ratHints_1014_; lean_object* v___x_1015_; uint8_t v___x_1016_; 
v_rupHints_1013_ = lean_ctor_get(v_val_990_, 3);
lean_inc_ref(v_rupHints_1013_);
v_ratHints_1014_ = lean_ctor_get(v_val_990_, 4);
lean_inc_ref(v_ratHints_1014_);
lean_dec_ref(v_val_990_);
v___x_1015_ = lean_array_get_size(v_rupHints_1013_);
v___x_1016_ = lean_nat_dec_lt(v___x_910_, v___x_1015_);
if (v___x_1016_ == 0)
{
v___y_965_ = v_rupHints_1013_;
v___y_966_ = v_ratHints_1014_;
v_snd_967_ = v_snd_987_;
goto v___jp_964_;
}
else
{
lean_object* v___x_1017_; uint8_t v___x_1018_; 
v___x_1017_ = lean_box(0);
v___x_1018_ = lean_nat_dec_le(v___x_1015_, v___x_1015_);
if (v___x_1018_ == 0)
{
if (v___x_1016_ == 0)
{
v___y_965_ = v_rupHints_1013_;
v___y_966_ = v_ratHints_1014_;
v_snd_967_ = v_snd_987_;
goto v___jp_964_;
}
else
{
size_t v___x_1019_; size_t v___x_1020_; lean_object* v___x_1021_; 
v___x_1019_ = ((size_t)0ULL);
v___x_1020_ = lean_usize_of_nat(v___x_1015_);
lean_inc(v_id_919_);
v___x_1021_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__4(v_id_919_, v_rupHints_1013_, v___x_1019_, v___x_1020_, v___x_1017_, v_a_907_, v_snd_987_);
v___y_982_ = v_rupHints_1013_;
v___y_983_ = v_ratHints_1014_;
v___y_984_ = v___x_1021_;
goto v___jp_981_;
}
}
else
{
size_t v___x_1022_; size_t v___x_1023_; lean_object* v___x_1024_; 
v___x_1022_ = ((size_t)0ULL);
v___x_1023_ = lean_usize_of_nat(v___x_1015_);
lean_inc(v_id_919_);
v___x_1024_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__4(v_id_919_, v_rupHints_1013_, v___x_1022_, v___x_1023_, v___x_1017_, v_a_907_, v_snd_987_);
v___y_982_ = v_rupHints_1013_;
v___y_983_ = v_ratHints_1014_;
v___y_984_ = v___x_1024_;
goto v___jp_981_;
}
}
}
default: 
{
lean_dec_ref(v_val_990_);
lean_dec(v_id_919_);
v_worklist_906_ = v_worklist_920_;
v_a_908_ = v_snd_987_;
goto _start;
}
}
}
}
v___jp_1026_:
{
uint8_t v___x_1028_; uint8_t v___x_1029_; 
v___x_1028_ = 1;
v___x_1029_ = lean_uint8_dec_eq(v___y_1027_, v___x_1028_);
if (v___x_1029_ == 0)
{
uint8_t v___x_1030_; 
v___x_1030_ = lean_nat_dec_le(v_initialId_913_, v_id_919_);
if (v___x_1030_ == 0)
{
v_snd_987_ = v_a_908_;
goto v___jp_986_;
}
else
{
lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1039_; 
lean_inc_ref(v_lastUse_916_);
lean_inc_ref(v_mapped_915_);
lean_inc_ref(v_used_914_);
v_isSharedCheck_1039_ = !lean_is_exclusive(v_a_908_);
if (v_isSharedCheck_1039_ == 0)
{
lean_object* v_unused_1040_; lean_object* v_unused_1041_; lean_object* v_unused_1042_; 
v_unused_1040_ = lean_ctor_get(v_a_908_, 2);
lean_dec(v_unused_1040_);
v_unused_1041_ = lean_ctor_get(v_a_908_, 1);
lean_dec(v_unused_1041_);
v_unused_1042_ = lean_ctor_get(v_a_908_, 0);
lean_dec(v_unused_1042_);
v___x_1032_ = v_a_908_;
v_isShared_1033_ = v_isSharedCheck_1039_;
goto v_resetjp_1031_;
}
else
{
lean_dec(v_a_908_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1039_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1037_; 
v___x_1034_ = lean_nat_sub(v_id_919_, v_initialId_913_);
v___x_1035_ = lean_byte_array_set(v_used_914_, v___x_1034_, v___x_1028_);
lean_dec(v___x_1034_);
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 0, v___x_1035_);
v___x_1037_ = v___x_1032_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1035_);
lean_ctor_set(v_reuseFailAlloc_1038_, 1, v_mapped_915_);
lean_ctor_set(v_reuseFailAlloc_1038_, 2, v_lastUse_916_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
v_snd_987_ = v___x_1037_;
goto v___jp_986_;
}
}
}
}
else
{
lean_dec(v_id_919_);
v_worklist_906_ = v_worklist_920_;
goto _start;
}
}
}
else
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
lean_dec_ref(v_worklist_906_);
v___x_1052_ = lean_box(0);
v___x_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
lean_ctor_set(v___x_1053_, 1, v_a_908_);
return v___x_1053_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go___boxed(lean_object* v_worklist_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l___private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go(v_worklist_1054_, v_a_1055_, v_a_1056_);
lean_dec_ref(v_a_1055_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1(lean_object* v_00_u03b2_1058_, lean_object* v_m_1059_, lean_object* v_a_1060_){
_start:
{
lean_object* v___x_1061_; 
v___x_1061_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1___redArg(v_m_1059_, v_a_1060_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1___boxed(lean_object* v_00_u03b2_1062_, lean_object* v_m_1063_, lean_object* v_a_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1(v_00_u03b2_1062_, v_m_1063_, v_a_1064_);
lean_dec(v_a_1064_);
lean_dec_ref(v_m_1063_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2(lean_object* v_id_1066_, lean_object* v_as_1067_, size_t v_i_1068_, size_t v_stop_1069_, lean_object* v_b_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2___redArg(v_id_1066_, v_as_1067_, v_i_1068_, v_stop_1069_, v_b_1070_, v___y_1072_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2___boxed(lean_object* v_id_1074_, lean_object* v_as_1075_, lean_object* v_i_1076_, lean_object* v_stop_1077_, lean_object* v_b_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
size_t v_i_boxed_1081_; size_t v_stop_boxed_1082_; lean_object* v_res_1083_; 
v_i_boxed_1081_ = lean_unbox_usize(v_i_1076_);
lean_dec(v_i_1076_);
v_stop_boxed_1082_ = lean_unbox_usize(v_stop_1077_);
lean_dec(v_stop_1077_);
v_res_1083_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2(v_id_1074_, v_as_1075_, v_i_boxed_1081_, v_stop_boxed_1082_, v_b_1078_, v___y_1079_, v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec_ref(v_as_1075_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__3(lean_object* v_id_1084_, lean_object* v_as_1085_, size_t v_sz_1086_, size_t v_i_1087_, lean_object* v_b_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__3___redArg(v_id_1084_, v_as_1085_, v_sz_1086_, v_i_1087_, v_b_1088_, v___y_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__3___boxed(lean_object* v_id_1092_, lean_object* v_as_1093_, lean_object* v_sz_1094_, lean_object* v_i_1095_, lean_object* v_b_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
size_t v_sz_boxed_1099_; size_t v_i_boxed_1100_; lean_object* v_res_1101_; 
v_sz_boxed_1099_ = lean_unbox_usize(v_sz_1094_);
lean_dec(v_sz_1094_);
v_i_boxed_1100_ = lean_unbox_usize(v_i_1095_);
lean_dec(v_i_1095_);
v_res_1101_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__3(v_id_1092_, v_as_1093_, v_sz_boxed_1099_, v_i_boxed_1100_, v_b_1096_, v___y_1097_, v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec_ref(v_as_1093_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1_spec__1(lean_object* v_00_u03b2_1102_, lean_object* v_a_1103_, lean_object* v_x_1104_){
_start:
{
lean_object* v___x_1105_; 
v___x_1105_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1_spec__1___redArg(v_a_1103_, v_x_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1106_, lean_object* v_a_1107_, lean_object* v_x_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1_spec__1(v_00_u03b2_1106_, v_a_1107_, v_x_1108_);
lean_dec(v_x_1108_);
lean_dec(v_a_1107_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis(lean_object* v_a_1110_, lean_object* v_a_1111_){
_start:
{
lean_object* v_addEmptyId_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v_addEmptyId_1112_ = lean_ctor_get(v_a_1110_, 2);
v___x_1113_ = lean_unsigned_to_nat(1u);
v___x_1114_ = lean_mk_empty_array_with_capacity(v___x_1113_);
lean_inc(v_addEmptyId_1112_);
v___x_1115_ = lean_array_push(v___x_1114_, v_addEmptyId_1112_);
v___x_1116_ = l___private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go(v___x_1115_, v_a_1110_, v_a_1111_);
lean_dec_ref(v_a_1110_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__0_spec__0___lam__0(lean_object* v_next_1117_, lean_object* v_x_1118_){
_start:
{
if (lean_obj_tag(v_x_1118_) == 0)
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1119_ = lean_unsigned_to_nat(1u);
v___x_1120_ = lean_mk_empty_array_with_capacity(v___x_1119_);
v___x_1121_ = lean_array_push(v___x_1120_, v_next_1117_);
v___x_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1121_);
return v___x_1122_;
}
else
{
lean_object* v_val_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1131_; 
v_val_1123_ = lean_ctor_get(v_x_1118_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v_x_1118_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1125_ = v_x_1118_;
v_isShared_1126_ = v_isSharedCheck_1131_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_val_1123_);
lean_dec(v_x_1118_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1131_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1127_; lean_object* v___x_1129_; 
v___x_1127_ = lean_array_push(v_val_1123_, v_next_1117_);
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 0, v___x_1127_);
v___x_1129_ = v___x_1125_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v___x_1127_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__0_spec__0(lean_object* v_next_1132_, lean_object* v_a_1133_, lean_object* v_x_1134_){
_start:
{
if (lean_obj_tag(v_x_1134_) == 0)
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v_val_1137_; lean_object* v___x_1138_; 
v___x_1135_ = lean_box(0);
v___x_1136_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__0_spec__0___lam__0(v_next_1132_, v___x_1135_);
v_val_1137_ = lean_ctor_get(v___x_1136_, 0);
lean_inc(v_val_1137_);
lean_dec(v___x_1136_);
v___x_1138_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1138_, 0, v_a_1133_);
lean_ctor_set(v___x_1138_, 1, v_val_1137_);
lean_ctor_set(v___x_1138_, 2, v_x_1134_);
return v___x_1138_;
}
else
{
lean_object* v_key_1139_; lean_object* v_value_1140_; lean_object* v_tail_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1156_; 
v_key_1139_ = lean_ctor_get(v_x_1134_, 0);
v_value_1140_ = lean_ctor_get(v_x_1134_, 1);
v_tail_1141_ = lean_ctor_get(v_x_1134_, 2);
v_isSharedCheck_1156_ = !lean_is_exclusive(v_x_1134_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1143_ = v_x_1134_;
v_isShared_1144_ = v_isSharedCheck_1156_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_tail_1141_);
lean_inc(v_value_1140_);
lean_inc(v_key_1139_);
lean_dec(v_x_1134_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1156_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
uint8_t v___x_1145_; 
v___x_1145_ = lean_nat_dec_eq(v_key_1139_, v_a_1133_);
if (v___x_1145_ == 0)
{
lean_object* v_tail_1146_; lean_object* v___x_1148_; 
v_tail_1146_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__0_spec__0(v_next_1132_, v_a_1133_, v_tail_1141_);
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 2, v_tail_1146_);
v___x_1148_ = v___x_1143_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_key_1139_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_value_1140_);
lean_ctor_set(v_reuseFailAlloc_1149_, 2, v_tail_1146_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
else
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v_val_1152_; lean_object* v___x_1154_; 
lean_dec(v_key_1139_);
v___x_1150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1150_, 0, v_value_1140_);
v___x_1151_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__0_spec__0___lam__0(v_next_1132_, v___x_1150_);
v_val_1152_ = lean_ctor_get(v___x_1151_, 0);
lean_inc(v_val_1152_);
lean_dec(v___x_1151_);
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 1, v_val_1152_);
lean_ctor_set(v___x_1143_, 0, v_a_1133_);
v___x_1154_ = v___x_1143_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_a_1133_);
lean_ctor_set(v_reuseFailAlloc_1155_, 1, v_val_1152_);
lean_ctor_set(v_reuseFailAlloc_1155_, 2, v_tail_1141_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__0(lean_object* v_next_1157_, lean_object* v_m_1158_, lean_object* v_a_1159_){
_start:
{
lean_object* v_size_1160_; lean_object* v_buckets_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1211_; 
v_size_1160_ = lean_ctor_get(v_m_1158_, 0);
v_buckets_1161_ = lean_ctor_get(v_m_1158_, 1);
v_isSharedCheck_1211_ = !lean_is_exclusive(v_m_1158_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1163_ = v_m_1158_;
v_isShared_1164_ = v_isSharedCheck_1211_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_buckets_1161_);
lean_inc(v_size_1160_);
lean_dec(v_m_1158_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1211_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1165_; uint64_t v___x_1166_; uint64_t v___x_1167_; uint64_t v___x_1168_; uint64_t v_fold_1169_; uint64_t v___x_1170_; uint64_t v___x_1171_; uint64_t v___x_1172_; size_t v___x_1173_; size_t v___x_1174_; size_t v___x_1175_; size_t v___x_1176_; size_t v___x_1177_; lean_object* v_bkt_1178_; uint8_t v___x_1179_; 
v___x_1165_ = lean_array_get_size(v_buckets_1161_);
v___x_1166_ = lean_uint64_of_nat(v_a_1159_);
v___x_1167_ = 32ULL;
v___x_1168_ = lean_uint64_shift_right(v___x_1166_, v___x_1167_);
v_fold_1169_ = lean_uint64_xor(v___x_1166_, v___x_1168_);
v___x_1170_ = 16ULL;
v___x_1171_ = lean_uint64_shift_right(v_fold_1169_, v___x_1170_);
v___x_1172_ = lean_uint64_xor(v_fold_1169_, v___x_1171_);
v___x_1173_ = lean_uint64_to_usize(v___x_1172_);
v___x_1174_ = lean_usize_of_nat(v___x_1165_);
v___x_1175_ = ((size_t)1ULL);
v___x_1176_ = lean_usize_sub(v___x_1174_, v___x_1175_);
v___x_1177_ = lean_usize_land(v___x_1173_, v___x_1176_);
v_bkt_1178_ = lean_array_uget_borrowed(v_buckets_1161_, v___x_1177_);
v___x_1179_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__0___redArg(v_a_1159_, v_bkt_1178_);
if (v___x_1179_ == 0)
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v_size_x27_1183_; lean_object* v___x_1184_; lean_object* v_buckets_x27_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; uint8_t v___x_1191_; 
v___x_1180_ = lean_unsigned_to_nat(1u);
v___x_1181_ = lean_mk_empty_array_with_capacity(v___x_1180_);
v___x_1182_ = lean_array_push(v___x_1181_, v_next_1157_);
v_size_x27_1183_ = lean_nat_add(v_size_1160_, v___x_1180_);
lean_dec(v_size_1160_);
lean_inc(v_bkt_1178_);
v___x_1184_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1184_, 0, v_a_1159_);
lean_ctor_set(v___x_1184_, 1, v___x_1182_);
lean_ctor_set(v___x_1184_, 2, v_bkt_1178_);
v_buckets_x27_1185_ = lean_array_uset(v_buckets_1161_, v___x_1177_, v___x_1184_);
v___x_1186_ = lean_unsigned_to_nat(4u);
v___x_1187_ = lean_nat_mul(v_size_x27_1183_, v___x_1186_);
v___x_1188_ = lean_unsigned_to_nat(3u);
v___x_1189_ = lean_nat_div(v___x_1187_, v___x_1188_);
lean_dec(v___x_1187_);
v___x_1190_ = lean_array_get_size(v_buckets_x27_1185_);
v___x_1191_ = lean_nat_dec_le(v___x_1189_, v___x_1190_);
lean_dec(v___x_1189_);
if (v___x_1191_ == 0)
{
lean_object* v_val_1192_; lean_object* v___x_1194_; 
v_val_1192_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1___redArg(v_buckets_x27_1185_);
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 1, v_val_1192_);
lean_ctor_set(v___x_1163_, 0, v_size_x27_1183_);
v___x_1194_ = v___x_1163_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_size_x27_1183_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v_val_1192_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
else
{
lean_object* v___x_1197_; 
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 1, v_buckets_x27_1185_);
lean_ctor_set(v___x_1163_, 0, v_size_x27_1183_);
v___x_1197_ = v___x_1163_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_size_x27_1183_);
lean_ctor_set(v_reuseFailAlloc_1198_, 1, v_buckets_x27_1185_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
else
{
lean_object* v___x_1199_; lean_object* v_buckets_x27_1200_; lean_object* v_bkt_x27_1201_; lean_object* v___y_1203_; uint8_t v___x_1208_; 
lean_inc(v_bkt_1178_);
v___x_1199_ = lean_box(0);
v_buckets_x27_1200_ = lean_array_uset(v_buckets_1161_, v___x_1177_, v___x_1199_);
lean_inc(v_a_1159_);
v_bkt_x27_1201_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__0_spec__0(v_next_1157_, v_a_1159_, v_bkt_1178_);
v___x_1208_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__0___redArg(v_a_1159_, v_bkt_x27_1201_);
lean_dec(v_a_1159_);
if (v___x_1208_ == 0)
{
lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1209_ = lean_unsigned_to_nat(1u);
v___x_1210_ = lean_nat_sub(v_size_1160_, v___x_1209_);
lean_dec(v_size_1160_);
v___y_1203_ = v___x_1210_;
goto v___jp_1202_;
}
else
{
v___y_1203_ = v_size_1160_;
goto v___jp_1202_;
}
v___jp_1202_:
{
lean_object* v___x_1204_; lean_object* v___x_1206_; 
v___x_1204_ = lean_array_uset(v_buckets_x27_1200_, v___x_1177_, v_bkt_x27_1201_);
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 1, v___x_1204_);
lean_ctor_set(v___x_1163_, 0, v___y_1203_);
v___x_1206_ = v___x_1163_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___y_1203_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v___x_1204_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__1___redArg(lean_object* v_upperBound_1212_, lean_object* v___x_1213_, lean_object* v_a_1214_, lean_object* v_b_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v_a_1218_; lean_object* v_snd_1219_; uint8_t v___x_1223_; 
v___x_1223_ = lean_nat_dec_lt(v_a_1214_, v_upperBound_1212_);
if (v___x_1223_ == 0)
{
lean_object* v___x_1224_; 
lean_dec(v_a_1214_);
v___x_1224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1224_, 0, v_b_1215_);
lean_ctor_set(v___x_1224_, 1, v___y_1216_);
return v___x_1224_;
}
else
{
lean_object* v___x_1225_; lean_object* v___x_1226_; uint8_t v___x_1227_; 
v___x_1225_ = lean_array_fget_borrowed(v___x_1213_, v_a_1214_);
v___x_1226_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__1, &l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__1);
v___x_1227_ = lean_int_dec_eq(v___x_1225_, v___x_1226_);
if (v___x_1227_ == 0)
{
lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1228_ = lean_nat_abs(v___x_1225_);
lean_inc(v_a_1214_);
v___x_1229_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__0(v_a_1214_, v_b_1215_, v___x_1228_);
v_a_1218_ = v___x_1229_;
v_snd_1219_ = v___y_1216_;
goto v___jp_1217_;
}
else
{
v_a_1218_ = v_b_1215_;
v_snd_1219_ = v___y_1216_;
goto v___jp_1217_;
}
}
v___jp_1217_:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1220_ = lean_unsigned_to_nat(1u);
v___x_1221_ = lean_nat_add(v_a_1214_, v___x_1220_);
lean_dec(v_a_1214_);
v_a_1214_ = v___x_1221_;
v_b_1215_ = v_a_1218_;
v___y_1216_ = v_snd_1219_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__1___redArg___boxed(lean_object* v_upperBound_1230_, lean_object* v___x_1231_, lean_object* v_a_1232_, lean_object* v_b_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__1___redArg(v_upperBound_1230_, v___x_1231_, v_a_1232_, v_b_1233_, v___y_1234_);
lean_dec_ref(v___x_1231_);
lean_dec(v_upperBound_1230_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete(lean_object* v_a_1236_, lean_object* v_a_1237_){
_start:
{
lean_object* v_lastUse_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v_lastUse_1238_ = lean_ctor_get(v_a_1237_, 2);
lean_inc_ref(v_lastUse_1238_);
v___x_1239_ = lean_unsigned_to_nat(0u);
v___x_1240_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__3, &l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__3);
v___x_1241_ = lean_array_get_size(v_lastUse_1238_);
v___x_1242_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__1___redArg(v___x_1241_, v_lastUse_1238_, v___x_1239_, v___x_1240_, v_a_1237_);
lean_dec_ref(v_lastUse_1238_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete___boxed(lean_object* v_a_1243_, lean_object* v_a_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete(v_a_1243_, v_a_1244_);
lean_dec_ref(v_a_1243_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__1(lean_object* v_upperBound_1246_, lean_object* v___x_1247_, lean_object* v_inst_1248_, lean_object* v_R_1249_, lean_object* v_a_1250_, lean_object* v_b_1251_, lean_object* v_c_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v___x_1255_; 
v___x_1255_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__1___redArg(v_upperBound_1246_, v___x_1247_, v_a_1250_, v_b_1251_, v___y_1254_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__1___boxed(lean_object* v_upperBound_1256_, lean_object* v___x_1257_, lean_object* v_inst_1258_, lean_object* v_R_1259_, lean_object* v_a_1260_, lean_object* v_b_1261_, lean_object* v_c_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__1(v_upperBound_1256_, v___x_1257_, v_inst_1258_, v_R_1259_, v_a_1260_, v_b_1261_, v_c_1262_, v___y_1263_, v___y_1264_);
lean_dec_ref(v___y_1263_);
lean_dec_ref(v___x_1257_);
lean_dec(v_upperBound_1256_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__2(lean_object* v_msg_1266_){
_start:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1267_ = lean_obj_once(&l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__7, &l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__7_once, _init_l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__7);
v___x_1268_ = lean_panic_fn(v___x_1267_, v_msg_1266_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0_spec__0___redArg(lean_object* v_next_1269_, lean_object* v_as_1270_, size_t v_sz_1271_, size_t v_i_1272_, lean_object* v_b_1273_, lean_object* v___y_1274_){
_start:
{
lean_object* v_a_1276_; lean_object* v_snd_1277_; uint8_t v___x_1281_; 
v___x_1281_ = lean_usize_dec_lt(v_i_1272_, v_sz_1271_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; 
lean_dec(v_next_1269_);
v___x_1282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1282_, 0, v_b_1273_);
lean_ctor_set(v___x_1282_, 1, v___y_1274_);
return v___x_1282_;
}
else
{
lean_object* v_lastUse_1283_; lean_object* v_a_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; uint8_t v___x_1288_; 
v_lastUse_1283_ = lean_ctor_get(v___y_1274_, 2);
v_a_1284_ = lean_array_uget_borrowed(v_as_1270_, v_i_1272_);
v___x_1285_ = l_Int_instInhabited;
v___x_1286_ = lean_array_get_borrowed(v___x_1285_, v_lastUse_1283_, v_a_1284_);
lean_inc(v_next_1269_);
v___x_1287_ = lean_nat_to_int(v_next_1269_);
v___x_1288_ = lean_int_dec_eq(v___x_1286_, v___x_1287_);
lean_dec(v___x_1287_);
if (v___x_1288_ == 0)
{
v_a_1276_ = v_b_1273_;
v_snd_1277_ = v___y_1274_;
goto v___jp_1275_;
}
else
{
lean_object* v___x_1289_; 
lean_inc(v_a_1284_);
v___x_1289_ = lean_array_push(v_b_1273_, v_a_1284_);
v_a_1276_ = v___x_1289_;
v_snd_1277_ = v___y_1274_;
goto v___jp_1275_;
}
}
v___jp_1275_:
{
size_t v___x_1278_; size_t v___x_1279_; 
v___x_1278_ = ((size_t)1ULL);
v___x_1279_ = lean_usize_add(v_i_1272_, v___x_1278_);
v_i_1272_ = v___x_1279_;
v_b_1273_ = v_a_1276_;
v___y_1274_ = v_snd_1277_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0_spec__0___redArg___boxed(lean_object* v_next_1290_, lean_object* v_as_1291_, lean_object* v_sz_1292_, lean_object* v_i_1293_, lean_object* v_b_1294_, lean_object* v___y_1295_){
_start:
{
size_t v_sz_boxed_1296_; size_t v_i_boxed_1297_; lean_object* v_res_1298_; 
v_sz_boxed_1296_ = lean_unbox_usize(v_sz_1292_);
lean_dec(v_sz_1292_);
v_i_boxed_1297_ = lean_unbox_usize(v_i_1293_);
lean_dec(v_i_1293_);
v_res_1298_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0_spec__0___redArg(v_next_1290_, v_as_1291_, v_sz_boxed_1296_, v_i_boxed_1297_, v_b_1294_, v___y_1295_);
lean_dec_ref(v_as_1291_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0(lean_object* v_next_1299_, lean_object* v_as_1300_, size_t v_sz_1301_, size_t v_i_1302_, lean_object* v_b_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
lean_object* v_a_1307_; lean_object* v_snd_1308_; uint8_t v___x_1312_; 
v___x_1312_ = lean_usize_dec_lt(v_i_1302_, v_sz_1301_);
if (v___x_1312_ == 0)
{
lean_object* v___x_1313_; 
lean_dec(v_next_1299_);
v___x_1313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1313_, 0, v_b_1303_);
lean_ctor_set(v___x_1313_, 1, v___y_1305_);
return v___x_1313_;
}
else
{
lean_object* v_lastUse_1314_; lean_object* v_a_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; uint8_t v___x_1319_; 
v_lastUse_1314_ = lean_ctor_get(v___y_1305_, 2);
v_a_1315_ = lean_array_uget_borrowed(v_as_1300_, v_i_1302_);
v___x_1316_ = l_Int_instInhabited;
v___x_1317_ = lean_array_get_borrowed(v___x_1316_, v_lastUse_1314_, v_a_1315_);
lean_inc(v_next_1299_);
v___x_1318_ = lean_nat_to_int(v_next_1299_);
v___x_1319_ = lean_int_dec_eq(v___x_1317_, v___x_1318_);
lean_dec(v___x_1318_);
if (v___x_1319_ == 0)
{
v_a_1307_ = v_b_1303_;
v_snd_1308_ = v___y_1305_;
goto v___jp_1306_;
}
else
{
lean_object* v___x_1320_; 
lean_inc(v_a_1315_);
v___x_1320_ = lean_array_push(v_b_1303_, v_a_1315_);
v_a_1307_ = v___x_1320_;
v_snd_1308_ = v___y_1305_;
goto v___jp_1306_;
}
}
v___jp_1306_:
{
size_t v___x_1309_; size_t v___x_1310_; lean_object* v___x_1311_; 
v___x_1309_ = ((size_t)1ULL);
v___x_1310_ = lean_usize_add(v_i_1302_, v___x_1309_);
v___x_1311_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0_spec__0___redArg(v_next_1299_, v_as_1300_, v_sz_1301_, v___x_1310_, v_a_1307_, v_snd_1308_);
return v___x_1311_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0___boxed(lean_object* v_next_1321_, lean_object* v_as_1322_, lean_object* v_sz_1323_, lean_object* v_i_1324_, lean_object* v_b_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
size_t v_sz_boxed_1328_; size_t v_i_boxed_1329_; lean_object* v_res_1330_; 
v_sz_boxed_1328_ = lean_unbox_usize(v_sz_1323_);
lean_dec(v_sz_1323_);
v_i_boxed_1329_ = lean_unbox_usize(v_i_1324_);
lean_dec(v_i_1324_);
v_res_1330_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0(v_next_1321_, v_as_1322_, v_sz_boxed_1328_, v_i_boxed_1329_, v_b_1325_, v___y_1326_, v___y_1327_);
lean_dec_ref(v___y_1326_);
lean_dec_ref(v_as_1322_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__1_spec__2(lean_object* v_next_1331_, lean_object* v_as_1332_, size_t v_sz_1333_, size_t v_i_1334_, lean_object* v_b_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_){
_start:
{
uint8_t v___x_1338_; 
v___x_1338_ = lean_usize_dec_lt(v_i_1334_, v_sz_1333_);
if (v___x_1338_ == 0)
{
lean_object* v___x_1339_; 
lean_dec(v_next_1331_);
v___x_1339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1339_, 0, v_b_1335_);
lean_ctor_set(v___x_1339_, 1, v___y_1337_);
return v___x_1339_;
}
else
{
lean_object* v_a_1340_; lean_object* v_fst_1341_; lean_object* v_snd_1342_; lean_object* v_deletions_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v_lastUse_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; uint8_t v___x_1359_; 
v_a_1340_ = lean_array_uget_borrowed(v_as_1332_, v_i_1334_);
v_fst_1341_ = lean_ctor_get(v_a_1340_, 0);
v_snd_1342_ = lean_ctor_get(v_a_1340_, 1);
v_lastUse_1355_ = lean_ctor_get(v___y_1337_, 2);
v___x_1356_ = l_Int_instInhabited;
v___x_1357_ = lean_array_get_borrowed(v___x_1356_, v_lastUse_1355_, v_fst_1341_);
lean_inc(v_next_1331_);
v___x_1358_ = lean_nat_to_int(v_next_1331_);
v___x_1359_ = lean_int_dec_eq(v___x_1357_, v___x_1358_);
lean_dec(v___x_1358_);
if (v___x_1359_ == 0)
{
v_deletions_1344_ = v_b_1335_;
v___y_1345_ = v___y_1336_;
v___y_1346_ = v___y_1337_;
goto v___jp_1343_;
}
else
{
lean_object* v___x_1360_; 
lean_inc(v_fst_1341_);
v___x_1360_ = lean_array_push(v_b_1335_, v_fst_1341_);
v_deletions_1344_ = v___x_1360_;
v___y_1345_ = v___y_1336_;
v___y_1346_ = v___y_1337_;
goto v___jp_1343_;
}
v___jp_1343_:
{
size_t v_sz_1347_; size_t v___x_1348_; lean_object* v___x_1349_; lean_object* v_fst_1350_; lean_object* v_snd_1351_; size_t v___x_1352_; size_t v___x_1353_; 
v_sz_1347_ = lean_array_size(v_snd_1342_);
v___x_1348_ = ((size_t)0ULL);
lean_inc(v_next_1331_);
v___x_1349_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0(v_next_1331_, v_snd_1342_, v_sz_1347_, v___x_1348_, v_deletions_1344_, v___y_1345_, v___y_1346_);
v_fst_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc(v_fst_1350_);
v_snd_1351_ = lean_ctor_get(v___x_1349_, 1);
lean_inc(v_snd_1351_);
lean_dec_ref(v___x_1349_);
v___x_1352_ = ((size_t)1ULL);
v___x_1353_ = lean_usize_add(v_i_1334_, v___x_1352_);
v_i_1334_ = v___x_1353_;
v_b_1335_ = v_fst_1350_;
v___y_1337_ = v_snd_1351_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__1_spec__2___boxed(lean_object* v_next_1361_, lean_object* v_as_1362_, lean_object* v_sz_1363_, lean_object* v_i_1364_, lean_object* v_b_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
size_t v_sz_boxed_1368_; size_t v_i_boxed_1369_; lean_object* v_res_1370_; 
v_sz_boxed_1368_ = lean_unbox_usize(v_sz_1363_);
lean_dec(v_sz_1363_);
v_i_boxed_1369_ = lean_unbox_usize(v_i_1364_);
lean_dec(v_i_1364_);
v_res_1370_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__1_spec__2(v_next_1361_, v_as_1362_, v_sz_boxed_1368_, v_i_boxed_1369_, v_b_1365_, v___y_1366_, v___y_1367_);
lean_dec_ref(v___y_1366_);
lean_dec_ref(v_as_1362_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__1(lean_object* v_next_1371_, lean_object* v_as_1372_, size_t v_sz_1373_, size_t v_i_1374_, lean_object* v_b_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_){
_start:
{
uint8_t v___x_1378_; 
v___x_1378_ = lean_usize_dec_lt(v_i_1374_, v_sz_1373_);
if (v___x_1378_ == 0)
{
lean_object* v___x_1379_; 
lean_dec(v_next_1371_);
v___x_1379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1379_, 0, v_b_1375_);
lean_ctor_set(v___x_1379_, 1, v___y_1377_);
return v___x_1379_;
}
else
{
lean_object* v_a_1380_; lean_object* v_fst_1381_; lean_object* v_snd_1382_; lean_object* v_deletions_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v_lastUse_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; uint8_t v___x_1399_; 
v_a_1380_ = lean_array_uget_borrowed(v_as_1372_, v_i_1374_);
v_fst_1381_ = lean_ctor_get(v_a_1380_, 0);
v_snd_1382_ = lean_ctor_get(v_a_1380_, 1);
v_lastUse_1395_ = lean_ctor_get(v___y_1377_, 2);
v___x_1396_ = l_Int_instInhabited;
v___x_1397_ = lean_array_get_borrowed(v___x_1396_, v_lastUse_1395_, v_fst_1381_);
lean_inc(v_next_1371_);
v___x_1398_ = lean_nat_to_int(v_next_1371_);
v___x_1399_ = lean_int_dec_eq(v___x_1397_, v___x_1398_);
lean_dec(v___x_1398_);
if (v___x_1399_ == 0)
{
v_deletions_1384_ = v_b_1375_;
v___y_1385_ = v___y_1376_;
v___y_1386_ = v___y_1377_;
goto v___jp_1383_;
}
else
{
lean_object* v___x_1400_; 
lean_inc(v_fst_1381_);
v___x_1400_ = lean_array_push(v_b_1375_, v_fst_1381_);
v_deletions_1384_ = v___x_1400_;
v___y_1385_ = v___y_1376_;
v___y_1386_ = v___y_1377_;
goto v___jp_1383_;
}
v___jp_1383_:
{
size_t v_sz_1387_; size_t v___x_1388_; lean_object* v___x_1389_; lean_object* v_fst_1390_; lean_object* v_snd_1391_; size_t v___x_1392_; size_t v___x_1393_; lean_object* v___x_1394_; 
v_sz_1387_ = lean_array_size(v_snd_1382_);
v___x_1388_ = ((size_t)0ULL);
lean_inc(v_next_1371_);
v___x_1389_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0(v_next_1371_, v_snd_1382_, v_sz_1387_, v___x_1388_, v_deletions_1384_, v___y_1385_, v___y_1386_);
v_fst_1390_ = lean_ctor_get(v___x_1389_, 0);
lean_inc(v_fst_1390_);
v_snd_1391_ = lean_ctor_get(v___x_1389_, 1);
lean_inc(v_snd_1391_);
lean_dec_ref(v___x_1389_);
v___x_1392_ = ((size_t)1ULL);
v___x_1393_ = lean_usize_add(v_i_1374_, v___x_1392_);
v___x_1394_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__1_spec__2(v_next_1371_, v_as_1372_, v_sz_1373_, v___x_1393_, v_fst_1390_, v___y_1376_, v_snd_1391_);
return v___x_1394_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__1___boxed(lean_object* v_next_1401_, lean_object* v_as_1402_, lean_object* v_sz_1403_, lean_object* v_i_1404_, lean_object* v_b_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
size_t v_sz_boxed_1408_; size_t v_i_boxed_1409_; lean_object* v_res_1410_; 
v_sz_boxed_1408_ = lean_unbox_usize(v_sz_1403_);
lean_dec(v_sz_1403_);
v_i_boxed_1409_ = lean_unbox_usize(v_i_1404_);
lean_dec(v_i_1404_);
v_res_1410_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__1(v_next_1401_, v_as_1402_, v_sz_boxed_1408_, v_i_boxed_1409_, v_b_1405_, v___y_1406_, v___y_1407_);
lean_dec_ref(v___y_1406_);
lean_dec_ref(v_as_1402_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___lam__0(lean_object* v___y_1411_, lean_object* v_fst_1412_, lean_object* v_snd_1413_, uint8_t v___x_1414_, lean_object* v_____r_1415_, lean_object* v_deletions_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
lean_object* v___x_1419_; lean_object* v_fst_1420_; lean_object* v_snd_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1451_; 
lean_inc_ref(v___y_1417_);
v___x_1419_ = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep(v___y_1411_, v___y_1417_, v___y_1418_);
v_fst_1420_ = lean_ctor_get(v___x_1419_, 0);
v_snd_1421_ = lean_ctor_get(v___x_1419_, 1);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1423_ = v___x_1419_;
v_isShared_1424_ = v_isSharedCheck_1451_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_snd_1421_);
lean_inc(v_fst_1420_);
lean_dec(v___x_1419_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1451_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
size_t v_sz_1425_; size_t v___x_1426_; lean_object* v___x_1427_; lean_object* v_fst_1428_; lean_object* v_snd_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1450_; 
v_sz_1425_ = lean_array_size(v_deletions_1416_);
v___x_1426_ = ((size_t)0ULL);
v___x_1427_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__0(v_sz_1425_, v___x_1426_, v_deletions_1416_, v___y_1417_, v_snd_1421_);
lean_dec_ref(v___y_1417_);
v_fst_1428_ = lean_ctor_get(v___x_1427_, 0);
v_snd_1429_ = lean_ctor_get(v___x_1427_, 1);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1431_ = v___x_1427_;
v_isShared_1432_ = v_isSharedCheck_1450_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_snd_1429_);
lean_inc(v_fst_1428_);
lean_dec(v___x_1427_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1450_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v_newProof_1434_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; uint8_t v___x_1447_; 
v___x_1444_ = lean_array_push(v_snd_1413_, v_fst_1420_);
v___x_1445_ = lean_array_get_size(v_fst_1428_);
v___x_1446_ = lean_unsigned_to_nat(0u);
v___x_1447_ = lean_nat_dec_eq(v___x_1445_, v___x_1446_);
if (v___x_1447_ == 0)
{
if (v___x_1414_ == 0)
{
lean_dec(v_fst_1428_);
v_newProof_1434_ = v___x_1444_;
goto v___jp_1433_;
}
else
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1448_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1448_, 0, v_fst_1428_);
v___x_1449_ = lean_array_push(v___x_1444_, v___x_1448_);
v_newProof_1434_ = v___x_1449_;
goto v___jp_1433_;
}
}
else
{
lean_dec(v_fst_1428_);
v_newProof_1434_ = v___x_1444_;
goto v___jp_1433_;
}
v___jp_1433_:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1438_; 
v___x_1435_ = lean_unsigned_to_nat(1u);
v___x_1436_ = lean_nat_add(v_fst_1412_, v___x_1435_);
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 1, v_newProof_1434_);
lean_ctor_set(v___x_1431_, 0, v___x_1436_);
v___x_1438_ = v___x_1431_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1436_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v_newProof_1434_);
v___x_1438_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
lean_object* v___x_1439_; lean_object* v___x_1441_; 
v___x_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1438_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 1, v_snd_1429_);
lean_ctor_set(v___x_1423_, 0, v___x_1439_);
v___x_1441_ = v___x_1423_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1439_);
lean_ctor_set(v_reuseFailAlloc_1442_, 1, v_snd_1429_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___lam__0___boxed(lean_object* v___y_1452_, lean_object* v_fst_1453_, lean_object* v_snd_1454_, lean_object* v___x_1455_, lean_object* v_____r_1456_, lean_object* v_deletions_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_){
_start:
{
uint8_t v___x_22195__boxed_1460_; lean_object* v_res_1461_; 
v___x_22195__boxed_1460_ = lean_unbox(v___x_1455_);
v_res_1461_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___lam__0(v___y_1452_, v_fst_1453_, v_snd_1454_, v___x_22195__boxed_1460_, v_____r_1456_, v_deletions_1457_, v___y_1458_, v___y_1459_);
lean_dec(v_fst_1453_);
return v_res_1461_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__4(void){
_start:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1467_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__3));
v___x_1468_ = lean_unsigned_to_nat(14u);
v___x_1469_ = lean_unsigned_to_nat(22u);
v___x_1470_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__2));
v___x_1471_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__1));
v___x_1472_ = l_mkPanicMessageWithDecl(v___x_1471_, v___x_1470_, v___x_1469_, v___x_1468_, v___x_1467_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg(lean_object* v_upperBound_1473_, lean_object* v___x_1474_, lean_object* v_a_1475_, lean_object* v_b_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v_a_1480_; lean_object* v_snd_1481_; lean_object* v___y_1486_; lean_object* v___y_1501_; lean_object* v___y_1502_; lean_object* v___y_1503_; uint8_t v___x_1506_; 
v___x_1506_ = lean_nat_dec_le(v_a_1475_, v_upperBound_1473_);
if (v___x_1506_ == 0)
{
lean_object* v___x_1507_; 
lean_dec_ref(v___y_1477_);
lean_dec(v_a_1475_);
v___x_1507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1507_, 0, v_b_1476_);
lean_ctor_set(v___x_1507_, 1, v___y_1478_);
return v___x_1507_;
}
else
{
lean_object* v_fst_1508_; lean_object* v_snd_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1581_; 
v_fst_1508_ = lean_ctor_get(v_b_1476_, 0);
v_snd_1509_ = lean_ctor_get(v_b_1476_, 1);
v_isSharedCheck_1581_ = !lean_is_exclusive(v_b_1476_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1511_ = v_b_1476_;
v_isShared_1512_ = v_isSharedCheck_1581_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_snd_1509_);
lean_inc(v_fst_1508_);
lean_dec(v_b_1476_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1581_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
uint8_t v___y_1514_; lean_object* v___y_1515_; uint8_t v___y_1516_; lean_object* v___y_1517_; lean_object* v_proof_1545_; lean_object* v_initialId_1546_; lean_object* v_used_1547_; lean_object* v_mapped_1548_; lean_object* v_lastUse_1549_; uint8_t v___y_1551_; lean_object* v___x_1573_; lean_object* v___x_1574_; uint8_t v___x_1575_; 
v_proof_1545_ = lean_ctor_get(v___y_1477_, 0);
v_initialId_1546_ = lean_ctor_get(v___y_1477_, 1);
v_used_1547_ = lean_ctor_get(v___y_1478_, 0);
v_mapped_1548_ = lean_ctor_get(v___y_1478_, 1);
v_lastUse_1549_ = lean_ctor_get(v___y_1478_, 2);
v___x_1573_ = lean_nat_sub(v_a_1475_, v_initialId_1546_);
v___x_1574_ = lean_byte_array_size(v_used_1547_);
v___x_1575_ = lean_nat_dec_lt(v___x_1573_, v___x_1574_);
if (v___x_1575_ == 0)
{
uint8_t v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; uint8_t v___x_1579_; 
lean_dec(v___x_1573_);
v___x_1576_ = l_instInhabitedUInt8;
v___x_1577_ = lean_box(v___x_1576_);
v___x_1578_ = l_outOfBounds___redArg(v___x_1577_);
v___x_1579_ = lean_unbox(v___x_1578_);
lean_dec(v___x_1578_);
v___y_1551_ = v___x_1579_;
goto v___jp_1550_;
}
else
{
uint8_t v___x_1580_; 
v___x_1580_ = lean_byte_array_fget(v_used_1547_, v___x_1573_);
lean_dec(v___x_1573_);
v___y_1551_ = v___x_1580_;
goto v___jp_1550_;
}
v___jp_1513_:
{
lean_object* v___x_1518_; lean_object* v___f_1519_; lean_object* v___x_1520_; uint8_t v___x_1521_; 
v___x_1518_ = lean_box(v___y_1514_);
lean_inc(v_snd_1509_);
lean_inc(v_fst_1508_);
lean_inc_ref(v___y_1517_);
v___f_1519_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___lam__0___boxed), 8, 4);
lean_closure_set(v___f_1519_, 0, v___y_1517_);
lean_closure_set(v___f_1519_, 1, v_fst_1508_);
lean_closure_set(v___f_1519_, 2, v_snd_1509_);
lean_closure_set(v___f_1519_, 3, v___x_1518_);
v___x_1520_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__0));
v___x_1521_ = lean_nat_dec_eq(v_a_1475_, v___x_1474_);
if (v___x_1521_ == 0)
{
if (v___y_1516_ == 0)
{
lean_dec_ref(v___y_1517_);
lean_dec(v_snd_1509_);
lean_dec(v_fst_1508_);
v___y_1501_ = v___x_1520_;
v___y_1502_ = v___f_1519_;
v___y_1503_ = v___y_1515_;
goto v___jp_1500_;
}
else
{
lean_dec_ref(v___f_1519_);
switch(lean_obj_tag(v___y_1517_))
{
case 1:
{
lean_object* v_rupHints_1522_; size_t v_sz_1523_; size_t v___x_1524_; lean_object* v___x_1525_; lean_object* v_fst_1526_; lean_object* v_snd_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v_rupHints_1522_ = lean_ctor_get(v___y_1517_, 2);
v_sz_1523_ = lean_array_size(v_rupHints_1522_);
v___x_1524_ = ((size_t)0ULL);
lean_inc(v_a_1475_);
v___x_1525_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0(v_a_1475_, v_rupHints_1522_, v_sz_1523_, v___x_1524_, v___x_1520_, v___y_1477_, v___y_1515_);
v_fst_1526_ = lean_ctor_get(v___x_1525_, 0);
lean_inc(v_fst_1526_);
v_snd_1527_ = lean_ctor_get(v___x_1525_, 1);
lean_inc(v_snd_1527_);
lean_dec_ref(v___x_1525_);
v___x_1528_ = lean_box(0);
lean_inc_ref(v___y_1477_);
v___x_1529_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___lam__0(v___y_1517_, v_fst_1508_, v_snd_1509_, v___y_1514_, v___x_1528_, v_fst_1526_, v___y_1477_, v_snd_1527_);
lean_dec(v_fst_1508_);
v___y_1486_ = v___x_1529_;
goto v___jp_1485_;
}
case 2:
{
lean_object* v_rupHints_1530_; lean_object* v_ratHints_1531_; size_t v_sz_1532_; size_t v___x_1533_; lean_object* v___x_1534_; lean_object* v_fst_1535_; lean_object* v_snd_1536_; size_t v_sz_1537_; lean_object* v___x_1538_; lean_object* v_fst_1539_; lean_object* v_snd_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v_rupHints_1530_ = lean_ctor_get(v___y_1517_, 3);
v_ratHints_1531_ = lean_ctor_get(v___y_1517_, 4);
v_sz_1532_ = lean_array_size(v_rupHints_1530_);
v___x_1533_ = ((size_t)0ULL);
lean_inc(v_a_1475_);
v___x_1534_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0(v_a_1475_, v_rupHints_1530_, v_sz_1532_, v___x_1533_, v___x_1520_, v___y_1477_, v___y_1515_);
v_fst_1535_ = lean_ctor_get(v___x_1534_, 0);
lean_inc(v_fst_1535_);
v_snd_1536_ = lean_ctor_get(v___x_1534_, 1);
lean_inc(v_snd_1536_);
lean_dec_ref(v___x_1534_);
v_sz_1537_ = lean_array_size(v_ratHints_1531_);
lean_inc(v_a_1475_);
v___x_1538_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__1(v_a_1475_, v_ratHints_1531_, v_sz_1537_, v___x_1533_, v_fst_1535_, v___y_1477_, v_snd_1536_);
v_fst_1539_ = lean_ctor_get(v___x_1538_, 0);
lean_inc(v_fst_1539_);
v_snd_1540_ = lean_ctor_get(v___x_1538_, 1);
lean_inc(v_snd_1540_);
lean_dec_ref(v___x_1538_);
v___x_1541_ = lean_box(0);
lean_inc_ref(v___y_1477_);
v___x_1542_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___lam__0(v___y_1517_, v_fst_1508_, v_snd_1509_, v___y_1514_, v___x_1541_, v_fst_1539_, v___y_1477_, v_snd_1540_);
lean_dec(v_fst_1508_);
v___y_1486_ = v___x_1542_;
goto v___jp_1485_;
}
default: 
{
lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1543_ = lean_box(0);
lean_inc_ref(v___y_1477_);
v___x_1544_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___lam__0(v___y_1517_, v_fst_1508_, v_snd_1509_, v___y_1514_, v___x_1543_, v___x_1520_, v___y_1477_, v___y_1515_);
lean_dec(v_fst_1508_);
v___y_1486_ = v___x_1544_;
goto v___jp_1485_;
}
}
}
}
else
{
lean_dec_ref(v___y_1517_);
lean_dec(v_snd_1509_);
lean_dec(v_fst_1508_);
v___y_1501_ = v___x_1520_;
v___y_1502_ = v___f_1519_;
v___y_1503_ = v___y_1515_;
goto v___jp_1500_;
}
}
v___jp_1550_:
{
uint8_t v___x_1552_; uint8_t v___x_1553_; 
v___x_1552_ = 1;
v___x_1553_ = lean_uint8_dec_eq(v___y_1551_, v___x_1552_);
if (v___x_1553_ == 0)
{
lean_object* v___x_1555_; 
if (v_isShared_1512_ == 0)
{
v___x_1555_ = v___x_1511_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_fst_1508_);
lean_ctor_set(v_reuseFailAlloc_1556_, 1, v_snd_1509_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
v_a_1480_ = v___x_1555_;
v_snd_1481_ = v___y_1478_;
goto v___jp_1479_;
}
}
else
{
lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1569_; 
lean_inc_ref(v_lastUse_1549_);
lean_inc_ref(v_mapped_1548_);
lean_inc_ref(v_used_1547_);
lean_del_object(v___x_1511_);
v_isSharedCheck_1569_ = !lean_is_exclusive(v___y_1478_);
if (v_isSharedCheck_1569_ == 0)
{
lean_object* v_unused_1570_; lean_object* v_unused_1571_; lean_object* v_unused_1572_; 
v_unused_1570_ = lean_ctor_get(v___y_1478_, 2);
lean_dec(v_unused_1570_);
v_unused_1571_ = lean_ctor_get(v___y_1478_, 1);
lean_dec(v_unused_1571_);
v_unused_1572_ = lean_ctor_get(v___y_1478_, 0);
lean_dec(v_unused_1572_);
v___x_1558_ = v___y_1478_;
v_isShared_1559_ = v_isSharedCheck_1569_;
goto v_resetjp_1557_;
}
else
{
lean_dec(v___y_1478_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1569_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1563_; 
v___x_1560_ = lean_nat_sub(v_a_1475_, v_initialId_1546_);
lean_inc(v_fst_1508_);
v___x_1561_ = lean_array_set(v_mapped_1548_, v___x_1560_, v_fst_1508_);
lean_dec(v___x_1560_);
if (v_isShared_1559_ == 0)
{
lean_ctor_set(v___x_1558_, 1, v___x_1561_);
v___x_1563_ = v___x_1558_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v_used_1547_);
lean_ctor_set(v_reuseFailAlloc_1568_, 1, v___x_1561_);
lean_ctor_set(v_reuseFailAlloc_1568_, 2, v_lastUse_1549_);
v___x_1563_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
lean_object* v___x_1564_; 
v___x_1564_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_LRAT_Trim_0__Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1___redArg(v_proof_1545_, v_a_1475_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1565_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__4);
v___x_1566_ = l_panic___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__2(v___x_1565_);
v___y_1514_ = v___x_1553_;
v___y_1515_ = v___x_1563_;
v___y_1516_ = v___x_1553_;
v___y_1517_ = v___x_1566_;
goto v___jp_1513_;
}
else
{
lean_object* v_val_1567_; 
v_val_1567_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_val_1567_);
lean_dec_ref(v___x_1564_);
v___y_1514_ = v___x_1553_;
v___y_1515_ = v___x_1563_;
v___y_1516_ = v___x_1553_;
v___y_1517_ = v_val_1567_;
goto v___jp_1513_;
}
}
}
}
}
}
}
v___jp_1479_:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1482_ = lean_unsigned_to_nat(1u);
v___x_1483_ = lean_nat_add(v_a_1475_, v___x_1482_);
lean_dec(v_a_1475_);
v_a_1475_ = v___x_1483_;
v_b_1476_ = v_a_1480_;
v___y_1478_ = v_snd_1481_;
goto _start;
}
v___jp_1485_:
{
lean_object* v_fst_1487_; 
v_fst_1487_ = lean_ctor_get(v___y_1486_, 0);
lean_inc(v_fst_1487_);
if (lean_obj_tag(v_fst_1487_) == 0)
{
lean_object* v_snd_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1496_; 
lean_dec_ref(v___y_1477_);
lean_dec(v_a_1475_);
v_snd_1488_ = lean_ctor_get(v___y_1486_, 1);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___y_1486_);
if (v_isSharedCheck_1496_ == 0)
{
lean_object* v_unused_1497_; 
v_unused_1497_ = lean_ctor_get(v___y_1486_, 0);
lean_dec(v_unused_1497_);
v___x_1490_ = v___y_1486_;
v_isShared_1491_ = v_isSharedCheck_1496_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_snd_1488_);
lean_dec(v___y_1486_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1496_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v_a_1492_; lean_object* v___x_1494_; 
v_a_1492_ = lean_ctor_get(v_fst_1487_, 0);
lean_inc(v_a_1492_);
lean_dec_ref(v_fst_1487_);
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 0, v_a_1492_);
v___x_1494_ = v___x_1490_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_a_1492_);
lean_ctor_set(v_reuseFailAlloc_1495_, 1, v_snd_1488_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
else
{
lean_object* v_snd_1498_; lean_object* v_a_1499_; 
v_snd_1498_ = lean_ctor_get(v___y_1486_, 1);
lean_inc(v_snd_1498_);
lean_dec_ref(v___y_1486_);
v_a_1499_ = lean_ctor_get(v_fst_1487_, 0);
lean_inc(v_a_1499_);
lean_dec_ref(v_fst_1487_);
v_a_1480_ = v_a_1499_;
v_snd_1481_ = v_snd_1498_;
goto v___jp_1479_;
}
}
v___jp_1500_:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1504_ = lean_box(0);
lean_inc_ref(v___y_1477_);
v___x_1505_ = lean_apply_4(v___y_1502_, v___x_1504_, v___y_1501_, v___y_1477_, v___y_1503_);
v___y_1486_ = v___x_1505_;
goto v___jp_1485_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___boxed(lean_object* v_upperBound_1582_, lean_object* v___x_1583_, lean_object* v_a_1584_, lean_object* v_b_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg(v_upperBound_1582_, v___x_1583_, v_a_1584_, v_b_1585_, v___y_1586_, v___y_1587_);
lean_dec(v___x_1583_);
lean_dec(v_upperBound_1582_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping(lean_object* v_a_1591_, lean_object* v_a_1592_){
_start:
{
lean_object* v_initialId_1593_; lean_object* v_addEmptyId_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v_fst_1598_; lean_object* v_snd_1599_; lean_object* v_snd_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
v_initialId_1593_ = lean_ctor_get(v_a_1591_, 1);
lean_inc(v_initialId_1593_);
v_addEmptyId_1594_ = lean_ctor_get(v_a_1591_, 2);
lean_inc(v_addEmptyId_1594_);
v___x_1595_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping___closed__0));
lean_inc(v_initialId_1593_);
v___x_1596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1596_, 0, v_initialId_1593_);
lean_ctor_set(v___x_1596_, 1, v___x_1595_);
v___x_1597_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg(v_addEmptyId_1594_, v_addEmptyId_1594_, v_initialId_1593_, v___x_1596_, v_a_1591_, v_a_1592_);
lean_dec(v_addEmptyId_1594_);
v_fst_1598_ = lean_ctor_get(v___x_1597_, 0);
lean_inc(v_fst_1598_);
v_snd_1599_ = lean_ctor_get(v___x_1597_, 1);
lean_inc(v_snd_1599_);
lean_dec_ref(v___x_1597_);
v_snd_1600_ = lean_ctor_get(v_fst_1598_, 1);
v_isSharedCheck_1607_ = !lean_is_exclusive(v_fst_1598_);
if (v_isSharedCheck_1607_ == 0)
{
lean_object* v_unused_1608_; 
v_unused_1608_ = lean_ctor_get(v_fst_1598_, 0);
lean_dec(v_unused_1608_);
v___x_1602_ = v_fst_1598_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_snd_1600_);
lean_dec(v_fst_1598_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 1, v_snd_1599_);
lean_ctor_set(v___x_1602_, 0, v_snd_1600_);
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_snd_1600_);
lean_ctor_set(v_reuseFailAlloc_1606_, 1, v_snd_1599_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3(lean_object* v_upperBound_1609_, lean_object* v___x_1610_, lean_object* v_inst_1611_, lean_object* v_R_1612_, lean_object* v_a_1613_, lean_object* v_b_1614_, lean_object* v_c_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v___x_1618_; 
v___x_1618_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg(v_upperBound_1609_, v___x_1610_, v_a_1613_, v_b_1614_, v___y_1616_, v___y_1617_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3___boxed(lean_object* v_upperBound_1619_, lean_object* v___x_1620_, lean_object* v_inst_1621_, lean_object* v_R_1622_, lean_object* v_a_1623_, lean_object* v_b_1624_, lean_object* v_c_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
lean_object* v_res_1628_; 
v_res_1628_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__3(v_upperBound_1619_, v___x_1620_, v_inst_1621_, v_R_1622_, v_a_1623_, v_b_1624_, v_c_1625_, v___y_1626_, v___y_1627_);
lean_dec(v___x_1620_);
lean_dec(v_upperBound_1619_);
return v_res_1628_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0_spec__0(lean_object* v_next_1629_, lean_object* v_as_1630_, size_t v_sz_1631_, size_t v_i_1632_, lean_object* v_b_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
lean_object* v___x_1636_; 
v___x_1636_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0_spec__0___redArg(v_next_1629_, v_as_1630_, v_sz_1631_, v_i_1632_, v_b_1633_, v___y_1635_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0_spec__0___boxed(lean_object* v_next_1637_, lean_object* v_as_1638_, lean_object* v_sz_1639_, lean_object* v_i_1640_, lean_object* v_b_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
size_t v_sz_boxed_1644_; size_t v_i_boxed_1645_; lean_object* v_res_1646_; 
v_sz_boxed_1644_ = lean_unbox_usize(v_sz_1639_);
lean_dec(v_sz_1639_);
v_i_boxed_1645_ = lean_unbox_usize(v_i_1640_);
lean_dec(v_i_1640_);
v_res_1646_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping_spec__0_spec__0(v_next_1637_, v_as_1638_, v_sz_boxed_1644_, v_i_boxed_1645_, v_b_1641_, v___y_1642_, v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec_ref(v_as_1638_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_go(lean_object* v_a_1647_, lean_object* v_a_1648_){
_start:
{
lean_object* v___x_1649_; lean_object* v_snd_1650_; lean_object* v___x_1651_; 
lean_inc_ref(v_a_1647_);
v___x_1649_ = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_useAnalysis(v_a_1647_, v_a_1648_);
v_snd_1650_ = lean_ctor_get(v___x_1649_, 1);
lean_inc(v_snd_1650_);
lean_dec_ref(v___x_1649_);
v___x_1651_ = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_mapping(v_a_1647_, v_snd_1650_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim(lean_object* v_proof_1652_){
_start:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1653_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_LRAT_trim_go), 2, 0);
v___x_1654_ = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___redArg(v_proof_1652_, v___x_1653_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim___boxed(lean_object* v_proof_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l_Lean_Elab_Tactic_BVDecide_LRAT_trim(v_proof_1655_);
lean_dec_ref(v_proof_1655_);
return v_res_1656_;
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
