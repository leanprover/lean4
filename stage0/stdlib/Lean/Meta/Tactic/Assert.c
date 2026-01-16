// Lean compiler output
// Module: Lean.Meta.Tactic.Assert
// Imports: public import Lean.Meta.Tactic.FVarSubst public import Lean.Meta.Tactic.Intro public import Lean.Meta.Tactic.Revert public import Lean.Util.ForEachExpr import Lean.Meta.AppBuilder
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__3(lean_object*, size_t, size_t, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
uint8_t l_Array_isEmpty___redArg(lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
static lean_object* l_Lean_MVarId_assertHypotheses___closed__2;
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_revertAfter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_assertExt___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_MVarId_assertExt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assertExt___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkBVar(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__0;
static lean_object* l_Lean_MVarId_assert___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_define___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_MVarId_assertHypotheses___closed__0;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__2;
lean_object* l_Lean_LocalDecl_index(lean_object*);
static lean_object* l_Lean_MVarId_define___closed__0;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__1;
static lean_object* l_Lean_MVarId_assertExt___lam__0___closed__1;
lean_object* lean_st_ref_take(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___closed__1;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_MetavarContext_modifyExprMVarLCtx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_note(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assertAfter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assert___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assertExt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___closed__2;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
uint8_t l_Lean_instDecidableEqLocalDeclKind(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_MVarId_assert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__4___redArg(lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_setKind(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_define___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_assert___closed__0;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replace___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assertAfter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_define___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_note___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_MVarId_assert___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___closed__0;
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_assertAfter___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replace___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_define(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
static lean_object* l_Lean_MVarId_assertExt___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_MVarId_replace___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
static lean_object* l_Lean_MVarId_assertHypotheses___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_MVarId_assertAfter___closed__0;
size_t lean_usize_land(size_t, size_t);
static lean_object* l_Lean_MVarId_define___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replace___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assertExt___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_array_get_size(x_6);
x_9 = lean_nat_dec_lt(x_2, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_10 = lean_array_push(x_6, x_3);
x_11 = lean_array_push(x_7, x_4);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_fget_borrowed(x_6, x_2);
x_13 = l_Lean_instBEqMVarId_beq(x_3, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_2, x_14);
lean_dec(x_2);
x_2 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_array_fset(x_6, x_2, x_3);
x_18 = lean_array_fset(x_7, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_18);
lean_ctor_set(x_1, 0, x_17);
return x_1;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_21 = lean_array_get_size(x_19);
x_22 = lean_nat_dec_lt(x_2, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
x_23 = lean_array_push(x_19, x_3);
x_24 = lean_array_push(x_20, x_4);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_array_fget_borrowed(x_19, x_2);
x_27 = l_Lean_instBEqMVarId_beq(x_3, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_20);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_2, x_29);
lean_dec(x_2);
x_1 = x_28;
x_2 = x_30;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_array_fset(x_19, x_2, x_3);
x_33 = lean_array_fset(x_20, x_2, x_4);
lean_dec(x_2);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(x_1, x_4, x_2, x_3);
return x_5;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__0() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__0;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = 5;
x_8 = 1;
x_9 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__1;
x_10 = lean_usize_land(x_2, x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_array_get_size(x_6);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc_ref(x_6);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_14 = x_1;
} else {
 lean_dec_ref(x_1);
 x_14 = lean_box(0);
}
x_15 = lean_array_fget(x_6, x_11);
x_16 = lean_box(0);
x_17 = lean_array_fset(x_6, x_11, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
x_25 = l_Lean_instBEqMVarId_beq(x_4, x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_free_object(x_15);
x_26 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_23, x_24, x_4, x_5);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_18 = x_27;
goto block_21;
}
else
{
lean_dec(x_24);
lean_dec(x_23);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_18 = x_15;
goto block_21;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_15);
x_30 = l_Lean_instBEqMVarId_beq(x_4, x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_28, x_29, x_4, x_5);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_18 = x_32;
goto block_21;
}
else
{
lean_object* x_33; 
lean_dec(x_29);
lean_dec(x_28);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_4);
lean_ctor_set(x_33, 1, x_5);
x_18 = x_33;
goto block_21;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_usize_shift_right(x_2, x_7);
x_37 = lean_usize_add(x_3, x_8);
x_38 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_18 = x_15;
goto block_21;
}
else
{
lean_object* x_39; size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_15, 0);
lean_inc(x_39);
lean_dec(x_15);
x_40 = lean_usize_shift_right(x_2, x_7);
x_41 = lean_usize_add(x_3, x_8);
x_42 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg(x_39, x_40, x_41, x_4, x_5);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_18 = x_43;
goto block_21;
}
}
default: 
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_4);
lean_ctor_set(x_44, 1, x_5);
x_18 = x_44;
goto block_21;
}
}
block_21:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_array_fset(x_17, x_11, x_18);
lean_dec(x_11);
if (lean_is_scalar(x_14)) {
 x_20 = lean_alloc_ctor(0, 1, 0);
} else {
 x_20 = x_14;
}
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_1);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; size_t x_54; uint8_t x_55; 
x_46 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3___redArg(x_1, x_4, x_5);
x_54 = 7;
x_55 = lean_usize_dec_le(x_54, x_3);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_46);
x_57 = lean_unsigned_to_nat(4u);
x_58 = lean_nat_dec_lt(x_56, x_57);
lean_dec(x_56);
x_47 = x_58;
goto block_53;
}
else
{
x_47 = x_55;
goto block_53;
}
block_53:
{
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_46, 0);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc_ref(x_49);
lean_dec_ref(x_46);
x_50 = lean_unsigned_to_nat(0u);
x_51 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__2;
x_52 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___redArg(x_3, x_48, x_49, x_50, x_51);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
return x_52;
}
else
{
return x_46;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; size_t x_70; uint8_t x_71; 
x_59 = lean_ctor_get(x_1, 0);
x_60 = lean_ctor_get(x_1, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_1);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3___redArg(x_61, x_4, x_5);
x_70 = 7;
x_71 = lean_usize_dec_le(x_70, x_3);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_62);
x_73 = lean_unsigned_to_nat(4u);
x_74 = lean_nat_dec_lt(x_72, x_73);
lean_dec(x_72);
x_63 = x_74;
goto block_69;
}
else
{
x_63 = x_71;
goto block_69;
}
block_69:
{
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_62, 0);
lean_inc_ref(x_64);
x_65 = lean_ctor_get(x_62, 1);
lean_inc_ref(x_65);
lean_dec_ref(x_62);
x_66 = lean_unsigned_to_nat(0u);
x_67 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__2;
x_68 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___redArg(x_3, x_64, x_65, x_66, x_67);
lean_dec_ref(x_65);
lean_dec_ref(x_64);
return x_68;
}
else
{
return x_62;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___redArg(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_4, x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; uint64_t x_10; size_t x_11; size_t x_12; lean_object* x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_array_fget_borrowed(x_2, x_4);
x_9 = lean_array_fget_borrowed(x_3, x_4);
x_10 = l_Lean_instHashableMVarId_hash(x_8);
x_11 = lean_uint64_to_usize(x_10);
x_12 = 5;
x_13 = lean_unsigned_to_nat(1u);
x_14 = 1;
x_15 = lean_usize_sub(x_1, x_14);
x_16 = lean_usize_mul(x_12, x_15);
x_17 = lean_usize_shift_right(x_11, x_16);
x_18 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
lean_inc(x_9);
lean_inc(x_8);
x_19 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg(x_5, x_17, x_1, x_8, x_9);
x_4 = x_18;
x_5 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___redArg(x_6, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = l_Lean_instHashableMVarId_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_take(x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_7, 7);
x_10 = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0___redArg(x_9, x_1, x_2);
lean_ctor_set(x_7, 7, x_10);
x_11 = lean_st_ref_set(x_3, x_5);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_ctor_get(x_7, 5);
x_20 = lean_ctor_get(x_7, 6);
x_21 = lean_ctor_get(x_7, 7);
x_22 = lean_ctor_get(x_7, 8);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_23 = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0___redArg(x_21, x_1, x_2);
x_24 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_24, 0, x_14);
lean_ctor_set(x_24, 1, x_15);
lean_ctor_set(x_24, 2, x_16);
lean_ctor_set(x_24, 3, x_17);
lean_ctor_set(x_24, 4, x_18);
lean_ctor_set(x_24, 5, x_19);
lean_ctor_set(x_24, 6, x_20);
lean_ctor_set(x_24, 7, x_23);
lean_ctor_set(x_24, 8, x_22);
lean_ctor_set(x_5, 0, x_24);
x_25 = lean_st_ref_set(x_3, x_5);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_28 = lean_ctor_get(x_5, 0);
x_29 = lean_ctor_get(x_5, 1);
x_30 = lean_ctor_get(x_5, 2);
x_31 = lean_ctor_get(x_5, 3);
x_32 = lean_ctor_get(x_5, 4);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_5);
x_33 = lean_ctor_get(x_28, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_28, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_28, 3);
lean_inc_ref(x_36);
x_37 = lean_ctor_get(x_28, 4);
lean_inc_ref(x_37);
x_38 = lean_ctor_get(x_28, 5);
lean_inc_ref(x_38);
x_39 = lean_ctor_get(x_28, 6);
lean_inc_ref(x_39);
x_40 = lean_ctor_get(x_28, 7);
lean_inc_ref(x_40);
x_41 = lean_ctor_get(x_28, 8);
lean_inc_ref(x_41);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 lean_ctor_release(x_28, 3);
 lean_ctor_release(x_28, 4);
 lean_ctor_release(x_28, 5);
 lean_ctor_release(x_28, 6);
 lean_ctor_release(x_28, 7);
 lean_ctor_release(x_28, 8);
 x_42 = x_28;
} else {
 lean_dec_ref(x_28);
 x_42 = lean_box(0);
}
x_43 = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0___redArg(x_40, x_1, x_2);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 9, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_33);
lean_ctor_set(x_44, 1, x_34);
lean_ctor_set(x_44, 2, x_35);
lean_ctor_set(x_44, 3, x_36);
lean_ctor_set(x_44, 4, x_37);
lean_ctor_set(x_44, 5, x_38);
lean_ctor_set(x_44, 6, x_39);
lean_ctor_set(x_44, 7, x_43);
lean_ctor_set(x_44, 8, x_41);
x_45 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_29);
lean_ctor_set(x_45, 2, x_30);
lean_ctor_set(x_45, 3, x_31);
lean_ctor_set(x_45, 4, x_32);
x_46 = lean_st_ref_set(x_3, x_45);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assert___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
lean_inc(x_1);
x_11 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_dec_ref(x_11);
lean_inc(x_1);
x_12 = l_Lean_MVarId_getTag(x_1, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
lean_inc(x_1);
x_14 = l_Lean_MVarId_getType(x_1, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = 0;
x_17 = l_Lean_mkForall(x_3, x_16, x_4, x_15);
x_18 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_17, x_13, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
lean_inc(x_19);
x_20 = l_Lean_Expr_app___override(x_19, x_5);
x_21 = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(x_1, x_20, x_7);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
x_24 = l_Lean_Expr_mvarId_x21(x_19);
lean_dec(x_19);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_21);
x_25 = l_Lean_Expr_mvarId_x21(x_19);
lean_dec(x_19);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec_ref(x_5);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_18, 0);
lean_inc(x_28);
lean_dec(x_18);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_13);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_14);
if (x_30 == 0)
{
return x_14;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_14, 0);
lean_inc(x_31);
lean_dec(x_14);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_12);
if (x_33 == 0)
{
return x_12;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_12, 0);
lean_inc(x_34);
lean_dec(x_12);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_11);
if (x_36 == 0)
{
return x_11;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_11, 0);
lean_inc(x_37);
lean_dec(x_11);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assert___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_MVarId_assert___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
return x_11;
}
}
static lean_object* _init_l_Lean_MVarId_assert___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assert", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_assert___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_assert___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_MVarId_assert___closed__1;
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_MVarId_assert___lam__0___boxed), 10, 5);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_10);
lean_closure_set(x_11, 2, x_2);
lean_closure_set(x_11, 3, x_3);
lean_closure_set(x_11, 4, x_4);
x_12 = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(x_1, x_11, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_MVarId_assert(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(x_1, x_2, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2(x_1, x_2, x_7, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___redArg(x_2, x_3, x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; lean_object* x_9; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__4(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_note(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_20; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_3);
x_20 = lean_infer_type(x_3, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_10 = x_21;
x_11 = lean_box(0);
goto block_19;
}
else
{
uint8_t x_22; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_4, 0);
lean_inc(x_25);
lean_dec_ref(x_4);
x_10 = x_25;
x_11 = lean_box(0);
goto block_19;
}
block_19:
{
lean_object* x_12; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_12 = l_Lean_MVarId_assert(x_1, x_2, x_10, x_3, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = 1;
x_15 = l_Lean_Meta_intro1Core(x_13, x_14, x_5, x_6, x_7, x_8);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_note___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_MVarId_note(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_define___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
lean_inc(x_1);
x_11 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_dec_ref(x_11);
lean_inc(x_1);
x_12 = l_Lean_MVarId_getTag(x_1, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
lean_inc(x_1);
x_14 = l_Lean_MVarId_getType(x_1, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = 0;
x_17 = l_Lean_Expr_letE___override(x_3, x_4, x_5, x_15, x_16);
x_18 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_17, x_13, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
lean_inc(x_19);
x_20 = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(x_1, x_19, x_7);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = l_Lean_Expr_mvarId_x21(x_19);
lean_dec(x_19);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_20);
x_24 = l_Lean_Expr_mvarId_x21(x_19);
lean_dec(x_19);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_18);
if (x_26 == 0)
{
return x_18;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
lean_dec(x_18);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_13);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_14);
if (x_29 == 0)
{
return x_14;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_14, 0);
lean_inc(x_30);
lean_dec(x_14);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_12);
if (x_32 == 0)
{
return x_12;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_12, 0);
lean_inc(x_33);
lean_dec(x_12);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_11);
if (x_35 == 0)
{
return x_11;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_11, 0);
lean_inc(x_36);
lean_dec(x_11);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_define___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_MVarId_define___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
return x_11;
}
}
static lean_object* _init_l_Lean_MVarId_define___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("define", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_define___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_define___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_define(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_MVarId_define___closed__1;
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_MVarId_define___lam__0___boxed), 10, 5);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_10);
lean_closure_set(x_11, 2, x_2);
lean_closure_set(x_11, 3, x_3);
lean_closure_set(x_11, 4, x_4);
x_12 = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(x_1, x_11, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_define___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_MVarId_define(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_MVarId_assertExt___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_assertExt___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_assertExt___lam__0___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_assertExt___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_mkBVar(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertExt___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
lean_inc(x_1);
x_12 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_dec_ref(x_12);
lean_inc(x_1);
x_13 = l_Lean_MVarId_getTag(x_1, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
lean_inc(x_1);
x_15 = l_Lean_MVarId_getType(x_1, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_3);
x_17 = l_Lean_Meta_getLevel(x_3, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l_Lean_MVarId_assertExt___lam__0___closed__1;
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_mkConst(x_19, x_21);
x_23 = l_Lean_MVarId_assertExt___lam__0___closed__2;
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_24 = l_Lean_mkApp3(x_22, x_3, x_23, x_4);
x_25 = 0;
x_26 = l_Lean_mkForall(x_5, x_25, x_24, x_16);
x_27 = l_Lean_mkForall(x_6, x_25, x_3, x_26);
lean_inc_ref(x_7);
x_28 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_27, x_14, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
lean_inc(x_8);
lean_inc_ref(x_4);
x_30 = l_Lean_Meta_mkEqRefl(x_4, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
lean_inc(x_29);
x_32 = l_Lean_mkAppB(x_29, x_4, x_31);
x_33 = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(x_1, x_32, x_8);
lean_dec(x_8);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
x_36 = l_Lean_Expr_mvarId_x21(x_29);
lean_dec(x_29);
lean_ctor_set(x_33, 0, x_36);
return x_33;
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_33);
x_37 = l_Lean_Expr_mvarId_x21(x_29);
lean_dec(x_29);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_29);
lean_dec(x_8);
lean_dec_ref(x_4);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_30);
if (x_39 == 0)
{
return x_30;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_30, 0);
lean_inc(x_40);
lean_dec(x_30);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_28);
if (x_42 == 0)
{
return x_28;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_28, 0);
lean_inc(x_43);
lean_dec(x_28);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_17);
if (x_45 == 0)
{
return x_17;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_17, 0);
lean_inc(x_46);
lean_dec(x_17);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_15);
if (x_48 == 0)
{
return x_15;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_15, 0);
lean_inc(x_49);
lean_dec(x_15);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_13);
if (x_51 == 0)
{
return x_13;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_13, 0);
lean_inc(x_52);
lean_dec(x_13);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_12);
if (x_54 == 0)
{
return x_12;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_12, 0);
lean_inc(x_55);
lean_dec(x_12);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertExt___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_MVarId_assertExt___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertExt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_MVarId_assert___closed__1;
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_MVarId_assertExt___lam__0___boxed), 11, 6);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
lean_closure_set(x_12, 2, x_3);
lean_closure_set(x_12, 3, x_4);
lean_closure_set(x_12, 4, x_5);
lean_closure_set(x_12, 5, x_2);
x_13 = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(x_1, x_12, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertExt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_MVarId_assertExt(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_3, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_9, 2);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_4);
return x_15;
}
else
{
uint8_t x_16; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_16 = !lean_is_exclusive(x_9);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
x_17 = lean_ctor_get(x_9, 2);
lean_dec(x_17);
x_18 = lean_ctor_get(x_9, 1);
lean_dec(x_18);
x_19 = lean_ctor_get(x_9, 0);
lean_dec(x_19);
x_20 = lean_array_uget(x_1, x_3);
x_21 = lean_array_fget(x_11, x_12);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_12, x_22);
lean_dec(x_12);
lean_ctor_set(x_9, 1, x_23);
x_24 = l_Lean_mkFVar(x_21);
x_25 = l_Lean_Meta_FVarSubst_insert(x_10, x_20, x_24);
lean_ctor_set(x_4, 1, x_25);
x_26 = 1;
x_27 = lean_usize_add(x_3, x_26);
x_3 = x_27;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; 
lean_dec(x_9);
x_29 = lean_array_uget(x_1, x_3);
x_30 = lean_array_fget(x_11, x_12);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_12, x_31);
lean_dec(x_12);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_11);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_13);
x_34 = l_Lean_mkFVar(x_30);
x_35 = l_Lean_Meta_FVarSubst_insert(x_10, x_29, x_34);
lean_ctor_set(x_4, 1, x_35);
lean_ctor_set(x_4, 0, x_33);
x_36 = 1;
x_37 = lean_usize_add(x_3, x_36);
x_3 = x_37;
goto _start;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_39 = lean_ctor_get(x_4, 0);
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_4);
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 1);
x_43 = lean_ctor_get(x_39, 2);
x_44 = lean_nat_dec_lt(x_42, x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_39);
lean_ctor_set(x_45, 1, x_40);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; size_t x_56; size_t x_57; 
lean_inc(x_43);
lean_inc(x_42);
lean_inc_ref(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 x_47 = x_39;
} else {
 lean_dec_ref(x_39);
 x_47 = lean_box(0);
}
x_48 = lean_array_uget(x_1, x_3);
x_49 = lean_array_fget(x_41, x_42);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_nat_add(x_42, x_50);
lean_dec(x_42);
if (lean_is_scalar(x_47)) {
 x_52 = lean_alloc_ctor(0, 3, 0);
} else {
 x_52 = x_47;
}
lean_ctor_set(x_52, 0, x_41);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_52, 2, x_43);
x_53 = l_Lean_mkFVar(x_49);
x_54 = l_Lean_Meta_FVarSubst_insert(x_40, x_48, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
x_56 = 1;
x_57 = lean_usize_add(x_3, x_56);
x_3 = x_57;
x_4 = x_55;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__0___redArg(x_1, x_6, x_7, x_4);
lean_dec_ref(x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_MVarId_assertAfter___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assertAfter", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_assertAfter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_assertAfter___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertAfter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_MVarId_assertAfter___closed__1;
lean_inc(x_1);
x_12 = l_Lean_MVarId_checkNotAssigned(x_1, x_11, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_dec_ref(x_12);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_13 = l_Lean_MVarId_revertAfter(x_1, x_2, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_17 = l_Lean_MVarId_assert(x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = 1;
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_20 = l_Lean_Meta_intro1Core(x_18, x_19, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_array_get_size(x_15);
x_25 = lean_box(0);
x_26 = 0;
x_27 = l_Lean_Meta_introNCore(x_23, x_24, x_25, x_26, x_19, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
x_32 = lean_box(0);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_array_get_size(x_30);
x_35 = l_Array_toSubarray___redArg(x_30, x_33, x_34);
lean_ctor_set(x_28, 1, x_32);
lean_ctor_set(x_28, 0, x_35);
x_36 = lean_array_size(x_15);
x_37 = 0;
x_38 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__0___redArg(x_15, x_36, x_37, x_28);
lean_dec(x_15);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_42, 0, x_22);
lean_ctor_set(x_42, 1, x_31);
lean_ctor_set(x_42, 2, x_41);
lean_ctor_set(x_38, 0, x_42);
return x_38;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_38, 0);
lean_inc(x_43);
lean_dec(x_38);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_22);
lean_ctor_set(x_45, 1, x_31);
lean_ctor_set(x_45, 2, x_44);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_31);
lean_dec(x_22);
x_47 = !lean_is_exclusive(x_38);
if (x_47 == 0)
{
return x_38;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_38, 0);
lean_inc(x_48);
lean_dec(x_38);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; size_t x_57; size_t x_58; lean_object* x_59; 
x_50 = lean_ctor_get(x_28, 0);
x_51 = lean_ctor_get(x_28, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_28);
x_52 = lean_box(0);
x_53 = lean_unsigned_to_nat(0u);
x_54 = lean_array_get_size(x_50);
x_55 = l_Array_toSubarray___redArg(x_50, x_53, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_52);
x_57 = lean_array_size(x_15);
x_58 = 0;
x_59 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__0___redArg(x_15, x_57, x_58, x_56);
lean_dec(x_15);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 x_61 = x_59;
} else {
 lean_dec_ref(x_59);
 x_61 = lean_box(0);
}
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_63, 0, x_22);
lean_ctor_set(x_63, 1, x_51);
lean_ctor_set(x_63, 2, x_62);
if (lean_is_scalar(x_61)) {
 x_64 = lean_alloc_ctor(0, 1, 0);
} else {
 x_64 = x_61;
}
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_51);
lean_dec(x_22);
x_65 = lean_ctor_get(x_59, 0);
lean_inc(x_65);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 x_66 = x_59;
} else {
 lean_dec_ref(x_59);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 1, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_65);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_22);
lean_dec(x_15);
x_68 = !lean_is_exclusive(x_27);
if (x_68 == 0)
{
return x_27;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_27, 0);
lean_inc(x_69);
lean_dec(x_27);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_71 = !lean_is_exclusive(x_20);
if (x_71 == 0)
{
return x_20;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_20, 0);
lean_inc(x_72);
lean_dec(x_20);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_74 = !lean_is_exclusive(x_17);
if (x_74 == 0)
{
return x_17;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_17, 0);
lean_inc(x_75);
lean_dec(x_17);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_77 = !lean_is_exclusive(x_13);
if (x_77 == 0)
{
return x_13;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_13, 0);
lean_inc(x_78);
lean_dec(x_13);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_12);
if (x_80 == 0)
{
return x_12;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_12, 0);
lean_inc(x_81);
lean_dec(x_12);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertAfter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_MVarId_assertAfter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__0___redArg(x_1, x_2, x_3, x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_assertAfter_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_take(x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = l_Lean_MetavarContext_modifyExprMVarLCtx(x_7, x_1, x_2);
lean_ctor_set(x_5, 0, x_8);
x_9 = lean_st_ref_set(x_3, x_5);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
x_14 = lean_ctor_get(x_5, 2);
x_15 = lean_ctor_get(x_5, 3);
x_16 = lean_ctor_get(x_5, 4);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_17 = l_Lean_MetavarContext_modifyExprMVarLCtx(x_12, x_1, x_2);
x_18 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_14);
lean_ctor_set(x_18, 3, x_15);
lean_ctor_set(x_18, 4, x_16);
x_19 = lean_st_ref_set(x_3, x_18);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg(x_1, x_2, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_12; 
x_12 = lean_nat_dec_lt(x_5, x_1);
if (x_12 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_13; uint8_t x_14; uint8_t x_19; uint8_t x_20; 
x_13 = lean_array_fget_borrowed(x_2, x_5);
x_14 = lean_ctor_get_uint8(x_13, sizeof(void*)*3 + 1);
x_19 = 0;
x_20 = l_Lean_instDecidableEqLocalDeclKind(x_14, x_19);
if (x_20 == 0)
{
goto block_18;
}
else
{
if (x_4 == 0)
{
x_7 = x_6;
goto block_11;
}
else
{
goto block_18;
}
}
block_18:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_box(0);
x_16 = lean_array_get_borrowed(x_15, x_3, x_5);
lean_inc(x_16);
x_17 = l_Lean_LocalContext_setKind(x_6, x_16, x_14);
x_7 = x_17;
goto block_11;
}
}
block_11:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_5, x_8);
lean_dec(x_5);
x_5 = x_9;
x_6 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
x_8 = l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg(x_1, x_2, x_3, x_7, x_5, x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
x_8 = l_Lean_MVarId_assertHypotheses___lam__0(x_1, x_2, x_3, x_7, x_5, x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_6 = 1;
x_7 = lean_usize_sub(x_2, x_6);
x_8 = lean_array_uget(x_1, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc_ref(x_10);
x_11 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
lean_dec(x_8);
x_12 = l_Lean_Expr_forallE___override(x_9, x_10, x_4, x_11);
x_2 = x_7;
x_4 = x_12;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__3(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 2);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = l_Lean_Expr_app___override(x_4, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_8;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
lean_inc(x_1);
x_10 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
lean_dec_ref(x_10);
lean_inc(x_1);
x_11 = l_Lean_MVarId_getTag(x_1, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
lean_inc(x_1);
x_13 = l_Lean_MVarId_getType(x_1, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_35; uint8_t x_50; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_array_get_size(x_3);
x_16 = lean_unsigned_to_nat(0u);
x_50 = lean_nat_dec_lt(x_16, x_15);
if (x_50 == 0)
{
x_35 = x_14;
goto block_49;
}
else
{
size_t x_51; size_t x_52; lean_object* x_53; 
x_51 = lean_usize_of_nat(x_15);
x_52 = 0;
x_53 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__3(x_3, x_51, x_52, x_14);
x_35 = x_53;
goto block_49;
}
block_34:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = l_Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0___redArg(x_1, x_19, x_6);
lean_dec_ref(x_20);
x_21 = l_Lean_Expr_mvarId_x21(x_17);
lean_dec_ref(x_17);
x_22 = lean_box(0);
x_23 = 1;
lean_inc(x_6);
x_24 = l_Lean_Meta_introNCore(x_21, x_15, x_22, x_4, x_23, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = lean_ctor_get(x_25, 0);
x_27 = lean_ctor_get(x_25, 1);
x_28 = lean_box(x_4);
lean_inc(x_26);
x_29 = lean_alloc_closure((void*)(l_Lean_MVarId_assertHypotheses___lam__0___boxed), 6, 5);
lean_closure_set(x_29, 0, x_15);
lean_closure_set(x_29, 1, x_3);
lean_closure_set(x_29, 2, x_26);
lean_closure_set(x_29, 3, x_28);
lean_closure_set(x_29, 4, x_16);
lean_inc(x_27);
x_30 = l_Lean_MVarId_modifyLCtx___at___00Lean_MVarId_assertHypotheses_spec__1___redArg(x_27, x_29, x_6);
lean_dec(x_6);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_25);
return x_30;
}
else
{
lean_object* x_33; 
lean_dec(x_30);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_25);
return x_33;
}
}
else
{
lean_dec(x_6);
lean_dec_ref(x_3);
return x_24;
}
}
block_49:
{
lean_object* x_36; 
lean_inc_ref(x_5);
x_36 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_35, x_12, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
x_38 = lean_nat_dec_lt(x_16, x_15);
if (x_38 == 0)
{
lean_inc(x_37);
x_17 = x_37;
x_18 = lean_box(0);
x_19 = x_37;
goto block_34;
}
else
{
uint8_t x_39; 
x_39 = lean_nat_dec_le(x_15, x_15);
if (x_39 == 0)
{
if (x_38 == 0)
{
lean_inc(x_37);
x_17 = x_37;
x_18 = lean_box(0);
x_19 = x_37;
goto block_34;
}
else
{
size_t x_40; size_t x_41; lean_object* x_42; 
x_40 = 0;
x_41 = lean_usize_of_nat(x_15);
lean_inc(x_37);
x_42 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2(x_3, x_40, x_41, x_37);
x_17 = x_37;
x_18 = lean_box(0);
x_19 = x_42;
goto block_34;
}
}
else
{
size_t x_43; size_t x_44; lean_object* x_45; 
x_43 = 0;
x_44 = lean_usize_of_nat(x_15);
lean_inc(x_37);
x_45 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_assertHypotheses_spec__2(x_3, x_43, x_44, x_37);
x_17 = x_37;
x_18 = lean_box(0);
x_19 = x_45;
goto block_34;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_36);
if (x_46 == 0)
{
return x_36;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_36, 0);
lean_inc(x_47);
lean_dec(x_36);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_13);
if (x_54 == 0)
{
return x_13;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_13, 0);
lean_inc(x_55);
lean_dec(x_13);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_11);
if (x_57 == 0)
{
return x_11;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_11, 0);
lean_inc(x_58);
lean_dec(x_11);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_10);
if (x_60 == 0)
{
return x_10;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_10, 0);
lean_inc(x_61);
lean_dec(x_10);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
x_11 = l_Lean_MVarId_assertHypotheses___lam__1(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8);
return x_11;
}
}
static lean_object* _init_l_Lean_MVarId_assertHypotheses___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assertHypotheses", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_assertHypotheses___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_assertHypotheses___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_assertHypotheses___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = l_Array_isEmpty___redArg(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l_Lean_MVarId_assertHypotheses___closed__1;
x_10 = lean_box(x_8);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_MVarId_assertHypotheses___lam__1___boxed), 9, 4);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_9);
lean_closure_set(x_11, 2, x_2);
lean_closure_set(x_11, 3, x_10);
x_12 = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(x_1, x_11, x_3, x_4, x_5, x_6);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_13 = l_Lean_MVarId_assertHypotheses___closed__2;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assertHypotheses___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_assertHypotheses(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___redArg(x_1, x_2, x_3, x_4, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
x_11 = l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_assertHypotheses_spec__0(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Expr_isFVar(x_1);
if (x_8 == 0)
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_3);
x_9 = l_Lean_Expr_hasFVar(x_1);
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Expr_fvarId_x21(x_1);
x_13 = l_Lean_FVarId_getDecl___redArg(x_12, x_3, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_15 = x_13;
} else {
 lean_dec_ref(x_13);
 x_15 = lean_box(0);
}
x_16 = lean_st_ref_take(x_2);
x_23 = l_Lean_LocalDecl_index(x_16);
x_24 = l_Lean_LocalDecl_index(x_14);
x_25 = lean_nat_dec_lt(x_23, x_24);
lean_dec(x_24);
lean_dec(x_23);
if (x_25 == 0)
{
lean_dec(x_14);
x_17 = x_16;
goto block_22;
}
else
{
lean_dec(x_16);
x_17 = x_14;
goto block_22;
}
block_22:
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_st_ref_set(x_2, x_17);
x_19 = 0;
x_20 = lean_box(x_19);
if (lean_is_scalar(x_15)) {
 x_21 = lean_alloc_ctor(0, 1, 0);
} else {
 x_21 = x_15;
}
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_13, 0);
lean_inc(x_27);
lean_dec(x_13);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
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
x_6 = lean_expr_eqv(x_4, x_1);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__3___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec_ref(x_1);
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
x_8 = lean_expr_eqv(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__5___redArg(x_1, x_2, x_7);
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
x_13 = lean_expr_eqv(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__5___redArg(x_1, x_2, x_12);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_Expr_hash(x_4);
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
x_19 = lean_array_uget(x_1, x_18);
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
x_26 = l_Lean_Expr_hash(x_22);
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
x_38 = lean_array_uget(x_1, x_37);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__4_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__4___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__4_spec__5___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l_Lean_Expr_hash(x_2);
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
x_20 = lean_array_uget(x_6, x_19);
x_21 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__3___redArg(x_2, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_5, x_22);
lean_dec(x_5);
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
x_32 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__4___redArg(x_25);
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
x_33 = lean_box(0);
x_34 = lean_array_uset(x_6, x_19, x_33);
x_35 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__5___redArg(x_2, x_3, x_20);
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
x_40 = l_Lean_Expr_hash(x_2);
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
x_52 = lean_array_uget(x_38, x_51);
x_53 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__3___redArg(x_2, x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_add(x_37, x_54);
lean_dec(x_37);
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
x_64 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__4___redArg(x_57);
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
x_67 = lean_box(0);
x_68 = lean_array_uset(x_38, x_51, x_67);
x_69 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__5___redArg(x_2, x_3, x_52);
x_70 = lean_array_uset(x_68, x_51, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_37);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_expr_eqv(x_4, x_1);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Expr_hash(x_2);
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
x_17 = lean_array_uget(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0_spec__1___redArg(x_2, x_17);
lean_dec(x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_17; lean_object* x_20; lean_object* x_21; 
x_20 = lean_st_ref_get(x_3);
x_21 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0___redArg(x_20, x_2);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
lean_inc_ref(x_1);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_2);
x_22 = lean_apply_7(x_1, x_2, x_4, x_5, x_6, x_7, x_8, lean_box(0));
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_30; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_30 = lean_unbox(x_23);
lean_dec(x_23);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
x_31 = lean_box(0);
x_10 = x_31;
x_11 = lean_box(0);
goto block_16;
}
else
{
switch (lean_obj_tag(x_2)) {
case 7:
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_2, 1);
x_33 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_33);
lean_inc_ref(x_32);
x_24 = x_32;
x_25 = x_33;
x_26 = x_3;
goto block_29;
}
case 6:
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_2, 1);
x_35 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_35);
lean_inc_ref(x_34);
x_24 = x_34;
x_25 = x_35;
x_26 = x_3;
goto block_29;
}
case 8:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_2, 1);
x_37 = lean_ctor_get(x_2, 2);
x_38 = lean_ctor_get(x_2, 3);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_36);
lean_inc_ref(x_1);
x_39 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0(x_1, x_36, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
lean_dec_ref(x_39);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_37);
lean_inc_ref(x_1);
x_40 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0(x_1, x_37, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
lean_dec_ref(x_40);
lean_inc_ref(x_38);
x_41 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0(x_1, x_38, x_3, x_4, x_5, x_6, x_7, x_8);
x_17 = x_41;
goto block_19;
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
x_17 = x_40;
goto block_19;
}
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
x_17 = x_39;
goto block_19;
}
}
case 5:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_2, 0);
x_43 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_42);
lean_inc_ref(x_1);
x_44 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0(x_1, x_42, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
lean_dec_ref(x_44);
lean_inc_ref(x_43);
x_45 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0(x_1, x_43, x_3, x_4, x_5, x_6, x_7, x_8);
x_17 = x_45;
goto block_19;
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
x_17 = x_44;
goto block_19;
}
}
case 10:
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_46);
x_47 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0(x_1, x_46, x_3, x_4, x_5, x_6, x_7, x_8);
x_17 = x_47;
goto block_19;
}
case 11:
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_48);
x_49 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0(x_1, x_48, x_3, x_4, x_5, x_6, x_7, x_8);
x_17 = x_49;
goto block_19;
}
default: 
{
lean_object* x_50; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
x_50 = lean_box(0);
x_10 = x_50;
x_11 = lean_box(0);
goto block_16;
}
}
}
block_29:
{
lean_object* x_27; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_1);
x_27 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0(x_1, x_24, x_26, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
lean_dec_ref(x_27);
x_28 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0(x_1, x_25, x_26, x_4, x_5, x_6, x_7, x_8);
x_17 = x_28;
goto block_19;
}
else
{
lean_dec_ref(x_25);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
x_17 = x_27;
goto block_19;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_51 = !lean_is_exclusive(x_22);
if (x_51 == 0)
{
return x_22;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_22, 0);
lean_inc(x_52);
lean_dec(x_22);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_54 = !lean_is_exclusive(x_21);
if (x_54 == 0)
{
lean_ctor_set_tag(x_21, 0);
return x_21;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_21, 0);
lean_inc(x_55);
lean_dec(x_21);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
block_16:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_st_ref_take(x_3);
x_13 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1___redArg(x_12, x_2, x_10);
x_14 = lean_st_ref_set(x_3, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_10);
return x_15;
}
block_19:
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_10 = x_18;
x_11 = lean_box(0);
goto block_16;
}
else
{
lean_dec_ref(x_2);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___closed__0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___lam__0___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___closed__1;
x_9 = lean_st_mk_ref(x_8);
x_10 = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___closed__2;
x_11 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0(x_10, x_1, x_9, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_st_ref_get(x_9);
lean_dec(x_9);
lean_dec(x_13);
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_st_ref_get(x_9);
lean_dec(x_9);
lean_dec(x_15);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_14);
return x_16;
}
}
else
{
lean_dec(x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__0_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__3___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__3(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__4___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__5___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__4_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__4_spec__5___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replace___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
lean_inc_ref(x_5);
lean_inc(x_1);
x_10 = l_Lean_FVarId_getDecl___redArg(x_1, x_5, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
lean_inc(x_11);
x_12 = lean_st_mk_ref(x_11);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_12);
lean_inc_ref(x_4);
x_13 = l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar(x_4, x_12, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec_ref(x_13);
x_14 = lean_st_ref_get(x_12);
lean_dec(x_12);
x_15 = l_Lean_LocalDecl_fvarId(x_14);
lean_dec(x_14);
x_16 = l_Lean_LocalDecl_userName(x_11);
lean_dec(x_11);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_17 = l_Lean_MVarId_assertAfter(x_2, x_15, x_16, x_4, x_3, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l_Lean_Meta_saveState___redArg(x_6, x_8);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_ctor_get(x_18, 0);
x_22 = lean_ctor_get(x_18, 1);
x_23 = lean_ctor_get(x_18, 2);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_22);
x_24 = l_Lean_MVarId_clear(x_22, x_1, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
lean_inc(x_23);
lean_inc(x_21);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_6);
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_18, 2);
lean_dec(x_26);
x_27 = lean_ctor_get(x_18, 1);
lean_dec(x_27);
x_28 = lean_ctor_get(x_18, 0);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_24, 0);
lean_ctor_set(x_18, 1, x_30);
lean_ctor_set(x_24, 0, x_18);
return x_24;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_24, 0);
lean_inc(x_31);
lean_dec(x_24);
lean_ctor_set(x_18, 1, x_31);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_18);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_18);
x_33 = lean_ctor_get(x_24, 0);
lean_inc(x_33);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 x_34 = x_24;
} else {
 lean_dec_ref(x_24);
 x_34 = lean_box(0);
}
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_21);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_35, 2, x_23);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 1, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_24);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; uint8_t x_48; 
x_38 = lean_ctor_get(x_24, 0);
lean_inc(x_38);
x_48 = l_Lean_Exception_isInterrupt(x_38);
if (x_48 == 0)
{
uint8_t x_49; 
x_49 = l_Lean_Exception_isRuntime(x_38);
x_39 = x_49;
goto block_47;
}
else
{
lean_dec(x_38);
x_39 = x_48;
goto block_47;
}
block_47:
{
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec_ref(x_24);
x_40 = l_Lean_Meta_SavedState_restore___redArg(x_20, x_6, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_20);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
lean_ctor_set(x_40, 0, x_18);
return x_40;
}
else
{
lean_object* x_43; 
lean_dec(x_40);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_18);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_18);
x_44 = !lean_is_exclusive(x_40);
if (x_44 == 0)
{
return x_40;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_40, 0);
lean_inc(x_45);
lean_dec(x_40);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
else
{
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_6);
return x_24;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_60; 
x_50 = lean_ctor_get(x_24, 0);
lean_inc(x_50);
lean_dec(x_24);
lean_inc(x_50);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_60 = l_Lean_Exception_isInterrupt(x_50);
if (x_60 == 0)
{
uint8_t x_61; 
x_61 = l_Lean_Exception_isRuntime(x_50);
x_52 = x_61;
goto block_59;
}
else
{
lean_dec(x_50);
x_52 = x_60;
goto block_59;
}
block_59:
{
if (x_52 == 0)
{
lean_object* x_53; 
lean_dec_ref(x_51);
x_53 = l_Lean_Meta_SavedState_restore___redArg(x_20, x_6, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_20);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; 
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 x_54 = x_53;
} else {
 lean_dec_ref(x_53);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(0, 1, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_18);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_18);
x_56 = lean_ctor_get(x_53, 0);
lean_inc(x_56);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 x_57 = x_53;
} else {
 lean_dec_ref(x_53);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 1, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_56);
return x_58;
}
}
else
{
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_6);
return x_51;
}
}
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_19);
if (x_62 == 0)
{
return x_19;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_19, 0);
lean_inc(x_63);
lean_dec(x_19);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_17;
}
}
else
{
uint8_t x_65; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_13);
if (x_65 == 0)
{
return x_13;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_13, 0);
lean_inc(x_66);
lean_dec(x_13);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_10);
if (x_68 == 0)
{
return x_10;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_10, 0);
lean_inc(x_69);
lean_dec(x_10);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replace___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_MVarId_replace___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replace___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_9 = lean_infer_type(x_2, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = lean_apply_6(x_3, x_10, x_4, x_5, x_6, x_7, lean_box(0));
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec_ref(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec_ref(x_1);
x_16 = lean_apply_6(x_3, x_15, x_4, x_5, x_6, x_7, lean_box(0));
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replace___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_replace___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc_ref(x_3);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_MVarId_replace___lam__0___boxed), 9, 3);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_1);
lean_closure_set(x_10, 2, x_3);
x_11 = lean_alloc_closure((void*)(l_Lean_MVarId_replace___lam__1___boxed), 8, 3);
lean_closure_set(x_11, 0, x_4);
lean_closure_set(x_11, 1, x_3);
lean_closure_set(x_11, 2, x_10);
x_12 = l_Lean_MVarId_withContext___at___00Lean_MVarId_assert_spec__1___redArg(x_1, x_11, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_MVarId_replace(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* initialize_Lean_Meta_Tactic_FVarSubst(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Intro(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Revert(uint8_t builtin);
lean_object* initialize_Lean_Util_ForEachExpr(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Assert(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_FVarSubst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Revert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ForEachExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__0 = _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__0();
l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__1 = _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__1();
l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__2 = _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__2();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assert_spec__0_spec__0_spec__2___redArg___closed__2);
l_Lean_MVarId_assert___closed__0 = _init_l_Lean_MVarId_assert___closed__0();
lean_mark_persistent(l_Lean_MVarId_assert___closed__0);
l_Lean_MVarId_assert___closed__1 = _init_l_Lean_MVarId_assert___closed__1();
lean_mark_persistent(l_Lean_MVarId_assert___closed__1);
l_Lean_MVarId_define___closed__0 = _init_l_Lean_MVarId_define___closed__0();
lean_mark_persistent(l_Lean_MVarId_define___closed__0);
l_Lean_MVarId_define___closed__1 = _init_l_Lean_MVarId_define___closed__1();
lean_mark_persistent(l_Lean_MVarId_define___closed__1);
l_Lean_MVarId_assertExt___lam__0___closed__0 = _init_l_Lean_MVarId_assertExt___lam__0___closed__0();
lean_mark_persistent(l_Lean_MVarId_assertExt___lam__0___closed__0);
l_Lean_MVarId_assertExt___lam__0___closed__1 = _init_l_Lean_MVarId_assertExt___lam__0___closed__1();
lean_mark_persistent(l_Lean_MVarId_assertExt___lam__0___closed__1);
l_Lean_MVarId_assertExt___lam__0___closed__2 = _init_l_Lean_MVarId_assertExt___lam__0___closed__2();
lean_mark_persistent(l_Lean_MVarId_assertExt___lam__0___closed__2);
l_Lean_MVarId_assertAfter___closed__0 = _init_l_Lean_MVarId_assertAfter___closed__0();
lean_mark_persistent(l_Lean_MVarId_assertAfter___closed__0);
l_Lean_MVarId_assertAfter___closed__1 = _init_l_Lean_MVarId_assertAfter___closed__1();
lean_mark_persistent(l_Lean_MVarId_assertAfter___closed__1);
l_Lean_MVarId_assertHypotheses___closed__0 = _init_l_Lean_MVarId_assertHypotheses___closed__0();
lean_mark_persistent(l_Lean_MVarId_assertHypotheses___closed__0);
l_Lean_MVarId_assertHypotheses___closed__1 = _init_l_Lean_MVarId_assertHypotheses___closed__1();
lean_mark_persistent(l_Lean_MVarId_assertHypotheses___closed__1);
l_Lean_MVarId_assertHypotheses___closed__2 = _init_l_Lean_MVarId_assertHypotheses___closed__2();
lean_mark_persistent(l_Lean_MVarId_assertHypotheses___closed__2);
l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___closed__0 = _init_l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___closed__0);
l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___closed__1 = _init_l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___closed__1);
l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___closed__2 = _init_l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Assert_0__Lean_MVarId_replace_findMaxFVar___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
