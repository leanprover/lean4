// Lean compiler output
// Module: Lean.Meta.Tactic.Cleanup
// Imports: public import Lean.Meta.Basic import Lean.Meta.CollectFVars import Lean.Meta.Tactic.Util
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
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Expr_collectFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* lean_local_ctx_erase(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addDeps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addDeps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectProps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectProps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "cleanup"};
static const lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(117, 245, 2, 152, 78, 142, 12, 191)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_cleanup(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_cleanup___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(lean_object* v_k_1_, lean_object* v_t_2_){
_start:
{
if (lean_obj_tag(v_t_2_) == 0)
{
lean_object* v_k_3_; lean_object* v_l_4_; lean_object* v_r_5_; uint8_t v___x_6_; 
v_k_3_ = lean_ctor_get(v_t_2_, 1);
v_l_4_ = lean_ctor_get(v_t_2_, 3);
v_r_5_ = lean_ctor_get(v_t_2_, 4);
v___x_6_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1_, v_k_3_);
switch(v___x_6_)
{
case 0:
{
v_t_2_ = v_l_4_;
goto _start;
}
case 1:
{
uint8_t v___x_8_; 
v___x_8_ = 1;
return v___x_8_;
}
default: 
{
v_t_2_ = v_r_5_;
goto _start;
}
}
}
else
{
uint8_t v___x_10_; 
v___x_10_ = 0;
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg___boxed(lean_object* v_k_11_, lean_object* v_t_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v_k_11_, v_t_12_);
lean_dec(v_t_12_);
lean_dec(v_k_11_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0___redArg(lean_object* v_e_15_, lean_object* v___y_16_){
_start:
{
uint8_t v___x_18_; 
v___x_18_ = l_Lean_Expr_hasMVar(v_e_15_);
if (v___x_18_ == 0)
{
lean_object* v___x_19_; 
v___x_19_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_19_, 0, v_e_15_);
return v___x_19_;
}
else
{
lean_object* v___x_20_; lean_object* v_mctx_21_; lean_object* v___x_22_; lean_object* v_fst_23_; lean_object* v_snd_24_; lean_object* v___x_25_; lean_object* v_cache_26_; lean_object* v_zetaDeltaFVarIds_27_; lean_object* v_postponed_28_; lean_object* v_diag_29_; lean_object* v___x_31_; uint8_t v_isShared_32_; uint8_t v_isSharedCheck_38_; 
v___x_20_ = lean_st_ref_get(v___y_16_);
v_mctx_21_ = lean_ctor_get(v___x_20_, 0);
lean_inc_ref(v_mctx_21_);
lean_dec(v___x_20_);
v___x_22_ = l_Lean_instantiateMVarsCore(v_mctx_21_, v_e_15_);
v_fst_23_ = lean_ctor_get(v___x_22_, 0);
lean_inc(v_fst_23_);
v_snd_24_ = lean_ctor_get(v___x_22_, 1);
lean_inc(v_snd_24_);
lean_dec_ref(v___x_22_);
v___x_25_ = lean_st_ref_take(v___y_16_);
v_cache_26_ = lean_ctor_get(v___x_25_, 1);
v_zetaDeltaFVarIds_27_ = lean_ctor_get(v___x_25_, 2);
v_postponed_28_ = lean_ctor_get(v___x_25_, 3);
v_diag_29_ = lean_ctor_get(v___x_25_, 4);
v_isSharedCheck_38_ = !lean_is_exclusive(v___x_25_);
if (v_isSharedCheck_38_ == 0)
{
lean_object* v_unused_39_; 
v_unused_39_ = lean_ctor_get(v___x_25_, 0);
lean_dec(v_unused_39_);
v___x_31_ = v___x_25_;
v_isShared_32_ = v_isSharedCheck_38_;
goto v_resetjp_30_;
}
else
{
lean_inc(v_diag_29_);
lean_inc(v_postponed_28_);
lean_inc(v_zetaDeltaFVarIds_27_);
lean_inc(v_cache_26_);
lean_dec(v___x_25_);
v___x_31_ = lean_box(0);
v_isShared_32_ = v_isSharedCheck_38_;
goto v_resetjp_30_;
}
v_resetjp_30_:
{
lean_object* v___x_34_; 
if (v_isShared_32_ == 0)
{
lean_ctor_set(v___x_31_, 0, v_snd_24_);
v___x_34_ = v___x_31_;
goto v_reusejp_33_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v_snd_24_);
lean_ctor_set(v_reuseFailAlloc_37_, 1, v_cache_26_);
lean_ctor_set(v_reuseFailAlloc_37_, 2, v_zetaDeltaFVarIds_27_);
lean_ctor_set(v_reuseFailAlloc_37_, 3, v_postponed_28_);
lean_ctor_set(v_reuseFailAlloc_37_, 4, v_diag_29_);
v___x_34_ = v_reuseFailAlloc_37_;
goto v_reusejp_33_;
}
v_reusejp_33_:
{
lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_35_ = lean_st_ref_set(v___y_16_, v___x_34_);
v___x_36_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_36_, 0, v_fst_23_);
return v___x_36_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0___redArg___boxed(lean_object* v_e_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0___redArg(v_e_40_, v___y_41_);
lean_dec(v___y_41_);
return v_res_43_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__0(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_46_ = lean_box(0);
v___x_47_ = lean_unsigned_to_nat(16u);
v___x_48_ = lean_mk_array(v___x_47_, v___x_46_);
return v___x_48_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__1(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_49_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__0, &l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__0_once, _init_l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__0);
v___x_50_ = lean_unsigned_to_nat(0u);
v___x_51_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_51_, 0, v___x_50_);
lean_ctor_set(v___x_51_, 1, v___x_49_);
return v___x_51_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__3(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_52_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__2));
v___x_53_ = lean_box(1);
v___x_54_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__1, &l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__1);
v___x_55_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
lean_ctor_set(v___x_55_, 1, v___x_53_);
lean_ctor_set(v___x_55_, 2, v___x_52_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(lean_object* v_fvarId_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_){
_start:
{
lean_object* v___x_63_; lean_object* v_snd_64_; uint8_t v___x_65_; 
v___x_63_ = lean_st_ref_get(v_a_57_);
v_snd_64_ = lean_ctor_get(v___x_63_, 1);
lean_inc(v_snd_64_);
lean_dec(v___x_63_);
v___x_65_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v_fvarId_56_, v_snd_64_);
lean_dec(v_snd_64_);
if (v___x_65_ == 0)
{
lean_object* v___x_66_; lean_object* v_snd_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_79_; 
v___x_66_ = lean_st_ref_take(v_a_57_);
v_snd_67_ = lean_ctor_get(v___x_66_, 1);
v_isSharedCheck_79_ = !lean_is_exclusive(v___x_66_);
if (v_isSharedCheck_79_ == 0)
{
lean_object* v_unused_80_; 
v_unused_80_ = lean_ctor_get(v___x_66_, 0);
lean_dec(v_unused_80_);
v___x_69_ = v___x_66_;
v_isShared_70_ = v_isSharedCheck_79_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_snd_67_);
lean_dec(v___x_66_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_79_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
uint8_t v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_75_; 
v___x_71_ = 1;
lean_inc(v_fvarId_56_);
v___x_72_ = l_Lean_FVarIdSet_insert(v_snd_67_, v_fvarId_56_);
v___x_73_ = lean_box(v___x_71_);
if (v_isShared_70_ == 0)
{
lean_ctor_set(v___x_69_, 1, v___x_72_);
lean_ctor_set(v___x_69_, 0, v___x_73_);
v___x_75_ = v___x_69_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v___x_73_);
lean_ctor_set(v_reuseFailAlloc_78_, 1, v___x_72_);
v___x_75_ = v_reuseFailAlloc_78_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_76_ = lean_st_ref_set(v_a_57_, v___x_75_);
v___x_77_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addDeps(v_fvarId_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_);
return v___x_77_;
}
}
}
else
{
lean_object* v___x_81_; lean_object* v___x_82_; 
lean_dec(v_fvarId_56_);
v___x_81_ = lean_box(0);
v___x_82_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
return v___x_82_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__1(lean_object* v_init_83_, lean_object* v_x_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
if (lean_obj_tag(v_x_84_) == 0)
{
lean_object* v_k_91_; lean_object* v_l_92_; lean_object* v_r_93_; lean_object* v___x_94_; 
v_k_91_ = lean_ctor_get(v_x_84_, 1);
lean_inc(v_k_91_);
v_l_92_ = lean_ctor_get(v_x_84_, 3);
lean_inc(v_l_92_);
v_r_93_ = lean_ctor_get(v_x_84_, 4);
lean_inc(v_r_93_);
lean_dec_ref_known(v_x_84_, 5);
v___x_94_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__1(v_init_83_, v_l_92_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_);
if (lean_obj_tag(v___x_94_) == 0)
{
lean_object* v___x_95_; 
lean_dec_ref_known(v___x_94_, 1);
v___x_95_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v_k_91_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_);
if (lean_obj_tag(v___x_95_) == 0)
{
lean_object* v___x_96_; 
lean_dec_ref_known(v___x_95_, 1);
v___x_96_ = lean_box(0);
v_init_83_ = v___x_96_;
v_x_84_ = v_r_93_;
goto _start;
}
else
{
lean_object* v_a_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_105_; 
lean_dec(v_r_93_);
v_a_98_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_105_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_105_ == 0)
{
v___x_100_ = v___x_95_;
v_isShared_101_ = v_isSharedCheck_105_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_a_98_);
lean_dec(v___x_95_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_105_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_103_; 
if (v_isShared_101_ == 0)
{
v___x_103_ = v___x_100_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v_a_98_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
return v___x_103_;
}
}
}
}
else
{
lean_dec(v_r_93_);
lean_dec(v_k_91_);
return v___x_94_;
}
}
else
{
lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_106_, 0, v_init_83_);
v___x_107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
return v___x_107_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars(lean_object* v_e_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0___redArg(v_e_108_, v_a_111_);
if (lean_obj_tag(v___x_115_) == 0)
{
lean_object* v_a_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v_a_116_ = lean_ctor_get(v___x_115_, 0);
lean_inc(v_a_116_);
lean_dec_ref_known(v___x_115_, 1);
v___x_117_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__3, &l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__3);
v___x_118_ = lean_st_mk_ref(v___x_117_);
v___x_119_ = l_Lean_Expr_collectFVars(v_a_116_, v___x_118_, v_a_110_, v_a_111_, v_a_112_, v_a_113_);
if (lean_obj_tag(v___x_119_) == 0)
{
lean_object* v___x_120_; lean_object* v_fvarSet_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
lean_dec_ref_known(v___x_119_, 1);
v___x_120_ = lean_st_ref_get(v___x_118_);
lean_dec(v___x_118_);
v_fvarSet_121_ = lean_ctor_get(v___x_120_, 1);
lean_inc(v_fvarSet_121_);
lean_dec(v___x_120_);
v___x_122_ = lean_box(0);
v___x_123_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__1(v___x_122_, v_fvarSet_121_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_);
if (lean_obj_tag(v___x_123_) == 0)
{
lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_130_; 
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_123_);
if (v_isSharedCheck_130_ == 0)
{
lean_object* v_unused_131_; 
v_unused_131_ = lean_ctor_get(v___x_123_, 0);
lean_dec(v_unused_131_);
v___x_125_ = v___x_123_;
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
else
{
lean_dec(v___x_123_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_128_; 
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 0, v___x_122_);
v___x_128_ = v___x_125_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v___x_122_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
else
{
lean_object* v_a_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_139_; 
v_a_132_ = lean_ctor_get(v___x_123_, 0);
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_123_);
if (v_isSharedCheck_139_ == 0)
{
v___x_134_ = v___x_123_;
v_isShared_135_ = v_isSharedCheck_139_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_a_132_);
lean_dec(v___x_123_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_139_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_137_; 
if (v_isShared_135_ == 0)
{
v___x_137_ = v___x_134_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_a_132_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
}
else
{
lean_dec(v___x_118_);
return v___x_119_;
}
}
else
{
lean_object* v_a_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_147_; 
v_a_140_ = lean_ctor_get(v___x_115_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_147_ == 0)
{
v___x_142_ = v___x_115_;
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_a_140_);
lean_dec(v___x_115_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_145_; 
if (v_isShared_143_ == 0)
{
v___x_145_ = v___x_142_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_a_140_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addDeps(lean_object* v_fvarId_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_148_, v_a_150_, v_a_152_, v_a_153_);
if (lean_obj_tag(v___x_155_) == 0)
{
lean_object* v_a_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v_a_156_ = lean_ctor_get(v___x_155_, 0);
lean_inc(v_a_156_);
lean_dec_ref_known(v___x_155_, 1);
v___x_157_ = l_Lean_LocalDecl_type(v_a_156_);
v___x_158_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars(v___x_157_, v_a_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_);
if (lean_obj_tag(v___x_158_) == 0)
{
lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_170_; 
v_isSharedCheck_170_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_170_ == 0)
{
lean_object* v_unused_171_; 
v_unused_171_ = lean_ctor_get(v___x_158_, 0);
lean_dec(v_unused_171_);
v___x_160_ = v___x_158_;
v_isShared_161_ = v_isSharedCheck_170_;
goto v_resetjp_159_;
}
else
{
lean_dec(v___x_158_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_170_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
uint8_t v___x_162_; lean_object* v___x_163_; 
v___x_162_ = 0;
v___x_163_ = l_Lean_LocalDecl_value_x3f(v_a_156_, v___x_162_);
lean_dec(v_a_156_);
if (lean_obj_tag(v___x_163_) == 1)
{
lean_object* v_val_164_; lean_object* v___x_165_; 
lean_del_object(v___x_160_);
v_val_164_ = lean_ctor_get(v___x_163_, 0);
lean_inc(v_val_164_);
lean_dec_ref_known(v___x_163_, 1);
v___x_165_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars(v_val_164_, v_a_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_);
return v___x_165_;
}
else
{
lean_object* v___x_166_; lean_object* v___x_168_; 
lean_dec(v___x_163_);
v___x_166_ = lean_box(0);
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 0, v___x_166_);
v___x_168_ = v___x_160_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_166_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
}
}
}
}
else
{
lean_dec(v_a_156_);
return v___x_158_;
}
}
else
{
lean_object* v_a_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_179_; 
v_a_172_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_179_ == 0)
{
v___x_174_ = v___x_155_;
v_isShared_175_ = v_isSharedCheck_179_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_a_172_);
lean_dec(v___x_155_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_179_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_177_; 
if (v_isShared_175_ == 0)
{
v___x_177_ = v___x_174_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v_a_172_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addDeps___boxed(lean_object* v_fvarId_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addDeps(v_fvarId_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_);
lean_dec(v_a_185_);
lean_dec_ref(v_a_184_);
lean_dec(v_a_183_);
lean_dec_ref(v_a_182_);
lean_dec(v_a_181_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__1___boxed(lean_object* v_init_188_, lean_object* v_x_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__1(v_init_188_, v_x_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
lean_dec(v___y_190_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar___boxed(lean_object* v_fvarId_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v_fvarId_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_);
lean_dec(v_a_202_);
lean_dec_ref(v_a_201_);
lean_dec(v_a_200_);
lean_dec_ref(v_a_199_);
lean_dec(v_a_198_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___boxed(lean_object* v_e_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars(v_e_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_);
lean_dec(v_a_210_);
lean_dec_ref(v_a_209_);
lean_dec(v_a_208_);
lean_dec_ref(v_a_207_);
lean_dec(v_a_206_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0(lean_object* v_e_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0___redArg(v_e_213_, v___y_216_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0___boxed(lean_object* v_e_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0(v_e_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_);
lean_dec(v___y_226_);
lean_dec_ref(v___y_225_);
lean_dec(v___y_224_);
lean_dec_ref(v___y_223_);
lean_dec(v___y_222_);
return v_res_228_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3(lean_object* v_00_u03b2_229_, lean_object* v_k_230_, lean_object* v_t_231_){
_start:
{
uint8_t v___x_232_; 
v___x_232_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v_k_230_, v_t_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___boxed(lean_object* v_00_u03b2_233_, lean_object* v_k_234_, lean_object* v_t_235_){
_start:
{
uint8_t v_res_236_; lean_object* v_r_237_; 
v_res_236_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3(v_00_u03b2_233_, v_k_234_, v_t_235_);
lean_dec(v_t_235_);
lean_dec(v_k_234_);
v_r_237_ = lean_box(v_res_236_);
return v_r_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(lean_object* v_e_238_, lean_object* v_pf_239_, lean_object* v_pm_240_, lean_object* v___y_241_){
_start:
{
lean_object* v___x_243_; uint8_t v_fst_245_; lean_object* v_mctx_246_; lean_object* v___y_264_; lean_object* v_mctx_269_; lean_object* v___x_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v___x_243_ = lean_st_ref_get(v___y_241_);
v_mctx_269_ = lean_ctor_get(v___x_243_, 0);
lean_inc_ref_n(v_mctx_269_, 2);
lean_dec(v___x_243_);
v___x_270_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__1, &l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__1);
v___x_271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
lean_ctor_set(v___x_271_, 1, v_mctx_269_);
v___x_272_ = l_Lean_Expr_hasFVar(v_e_238_);
if (v___x_272_ == 0)
{
uint8_t v___x_273_; 
v___x_273_ = l_Lean_Expr_hasMVar(v_e_238_);
if (v___x_273_ == 0)
{
lean_dec_ref_known(v___x_271_, 2);
lean_dec_ref(v_pm_240_);
lean_dec_ref(v_pf_239_);
lean_dec_ref(v_e_238_);
v_fst_245_ = v___x_273_;
v_mctx_246_ = v_mctx_269_;
goto v___jp_244_;
}
else
{
lean_object* v___x_274_; 
lean_dec_ref(v_mctx_269_);
v___x_274_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v_pf_239_, v_pm_240_, v_e_238_, v___x_271_);
v___y_264_ = v___x_274_;
goto v___jp_263_;
}
}
else
{
lean_object* v___x_275_; 
lean_dec_ref(v_mctx_269_);
v___x_275_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v_pf_239_, v_pm_240_, v_e_238_, v___x_271_);
v___y_264_ = v___x_275_;
goto v___jp_263_;
}
v___jp_244_:
{
lean_object* v___x_247_; lean_object* v_cache_248_; lean_object* v_zetaDeltaFVarIds_249_; lean_object* v_postponed_250_; lean_object* v_diag_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_261_; 
v___x_247_ = lean_st_ref_take(v___y_241_);
v_cache_248_ = lean_ctor_get(v___x_247_, 1);
v_zetaDeltaFVarIds_249_ = lean_ctor_get(v___x_247_, 2);
v_postponed_250_ = lean_ctor_get(v___x_247_, 3);
v_diag_251_ = lean_ctor_get(v___x_247_, 4);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_261_ == 0)
{
lean_object* v_unused_262_; 
v_unused_262_ = lean_ctor_get(v___x_247_, 0);
lean_dec(v_unused_262_);
v___x_253_ = v___x_247_;
v_isShared_254_ = v_isSharedCheck_261_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_diag_251_);
lean_inc(v_postponed_250_);
lean_inc(v_zetaDeltaFVarIds_249_);
lean_inc(v_cache_248_);
lean_dec(v___x_247_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_261_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_256_; 
if (v_isShared_254_ == 0)
{
lean_ctor_set(v___x_253_, 0, v_mctx_246_);
v___x_256_ = v___x_253_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_mctx_246_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v_cache_248_);
lean_ctor_set(v_reuseFailAlloc_260_, 2, v_zetaDeltaFVarIds_249_);
lean_ctor_set(v_reuseFailAlloc_260_, 3, v_postponed_250_);
lean_ctor_set(v_reuseFailAlloc_260_, 4, v_diag_251_);
v___x_256_ = v_reuseFailAlloc_260_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_257_ = lean_st_ref_set(v___y_241_, v___x_256_);
v___x_258_ = lean_box(v_fst_245_);
v___x_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
return v___x_259_;
}
}
}
v___jp_263_:
{
lean_object* v_snd_265_; lean_object* v_fst_266_; lean_object* v_mctx_267_; uint8_t v___x_268_; 
v_snd_265_ = lean_ctor_get(v___y_264_, 1);
lean_inc(v_snd_265_);
v_fst_266_ = lean_ctor_get(v___y_264_, 0);
lean_inc(v_fst_266_);
lean_dec_ref(v___y_264_);
v_mctx_267_ = lean_ctor_get(v_snd_265_, 1);
lean_inc_ref(v_mctx_267_);
lean_dec(v_snd_265_);
v___x_268_ = lean_unbox(v_fst_266_);
lean_dec(v_fst_266_);
v_fst_245_ = v___x_268_;
v_mctx_246_ = v_mctx_267_;
goto v___jp_244_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg___boxed(lean_object* v_e_276_, lean_object* v_pf_277_, lean_object* v_pm_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v_e_276_, v_pf_277_, v_pm_278_, v___y_279_);
lean_dec(v___y_279_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0(lean_object* v_e_282_, lean_object* v_pf_283_, lean_object* v_pm_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v_e_282_, v_pf_283_, v_pm_284_, v___y_287_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___boxed(lean_object* v_e_292_, lean_object* v_pf_293_, lean_object* v_pm_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0(v_e_292_, v_pf_293_, v_pm_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
return v_res_301_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__0(lean_object* v_snd_302_, lean_object* v___y_303_){
_start:
{
uint8_t v___x_304_; 
v___x_304_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___y_303_, v_snd_302_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__0___boxed(lean_object* v_snd_305_, lean_object* v___y_306_){
_start:
{
uint8_t v_res_307_; lean_object* v_r_308_; 
v_res_307_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__0(v_snd_305_, v___y_306_);
lean_dec(v___y_306_);
lean_dec(v_snd_305_);
v_r_308_ = lean_box(v_res_307_);
return v_r_308_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__1(uint8_t v___x_309_, lean_object* v_x_310_){
_start:
{
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__1___boxed(lean_object* v___x_311_, lean_object* v_x_312_){
_start:
{
uint8_t v___x_9700__boxed_313_; uint8_t v_res_314_; lean_object* v_r_315_; 
v___x_9700__boxed_313_ = lean_unbox(v___x_311_);
v_res_314_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__1(v___x_9700__boxed_313_, v_x_312_);
lean_dec(v_x_312_);
v_r_315_ = lean_box(v_res_314_);
return v_r_315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2_spec__5(lean_object* v_as_316_, size_t v_sz_317_, size_t v_i_318_, lean_object* v_b_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
uint8_t v___x_326_; 
v___x_326_ = lean_usize_dec_lt(v_i_318_, v_sz_317_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; 
v___x_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_327_, 0, v_b_319_);
return v___x_327_;
}
else
{
lean_object* v_snd_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_411_; 
v_snd_328_ = lean_ctor_get(v_b_319_, 1);
v_isSharedCheck_411_ = !lean_is_exclusive(v_b_319_);
if (v_isSharedCheck_411_ == 0)
{
lean_object* v_unused_412_; 
v_unused_412_ = lean_ctor_get(v_b_319_, 0);
lean_dec(v_unused_412_);
v___x_330_ = v_b_319_;
v_isShared_331_ = v_isSharedCheck_411_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_snd_328_);
lean_dec(v_b_319_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_411_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_332_; lean_object* v_a_334_; lean_object* v_a_341_; 
v___x_332_ = lean_box(0);
v_a_341_ = lean_array_uget_borrowed(v_as_316_, v_i_318_);
if (lean_obj_tag(v_a_341_) == 0)
{
v_a_334_ = v_snd_328_;
goto v___jp_333_;
}
else
{
lean_object* v_val_342_; lean_object* v___x_343_; lean_object* v_snd_344_; lean_object* v___x_345_; lean_object* v___x_346_; uint8_t v___x_347_; 
lean_dec(v_snd_328_);
v_val_342_ = lean_ctor_get(v_a_341_, 0);
v___x_343_ = lean_st_ref_get(v___y_320_);
v_snd_344_ = lean_ctor_get(v___x_343_, 1);
lean_inc(v_snd_344_);
lean_dec(v___x_343_);
v___x_345_ = lean_box(0);
v___x_346_ = l_Lean_LocalDecl_fvarId(v_val_342_);
v___x_347_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_346_, v_snd_344_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = l_Lean_LocalDecl_type(v_val_342_);
lean_inc_ref(v___x_348_);
v___x_349_ = l_Lean_Meta_isProp(v___x_348_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
if (lean_obj_tag(v___x_349_) == 0)
{
lean_object* v_a_350_; lean_object* v___f_351_; lean_object* v___x_352_; lean_object* v___f_353_; lean_object* v___y_355_; lean_object* v___y_356_; lean_object* v___y_357_; lean_object* v___y_358_; lean_object* v___y_359_; uint8_t v___x_382_; 
v_a_350_ = lean_ctor_get(v___x_349_, 0);
lean_inc(v_a_350_);
lean_dec_ref_known(v___x_349_, 1);
v___f_351_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_351_, 0, v_snd_344_);
v___x_352_ = lean_box(v___x_347_);
v___f_353_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__1___boxed), 2, 1);
lean_closure_set(v___f_353_, 0, v___x_352_);
v___x_382_ = lean_unbox(v_a_350_);
lean_dec(v_a_350_);
if (v___x_382_ == 0)
{
lean_dec_ref(v___x_348_);
v___y_355_ = v___y_320_;
v___y_356_ = v___y_321_;
v___y_357_ = v___y_322_;
v___y_358_ = v___y_323_;
v___y_359_ = v___y_324_;
goto v___jp_354_;
}
else
{
lean_object* v___x_383_; 
lean_inc_ref(v___f_353_);
lean_inc_ref(v___f_351_);
v___x_383_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v___x_348_, v___f_351_, v___f_353_, v___y_322_);
if (lean_obj_tag(v___x_383_) == 0)
{
lean_object* v_a_384_; uint8_t v___x_385_; 
v_a_384_ = lean_ctor_get(v___x_383_, 0);
lean_inc(v_a_384_);
lean_dec_ref_known(v___x_383_, 1);
v___x_385_ = lean_unbox(v_a_384_);
lean_dec(v_a_384_);
if (v___x_385_ == 0)
{
v___y_355_ = v___y_320_;
v___y_356_ = v___y_321_;
v___y_357_ = v___y_322_;
v___y_358_ = v___y_323_;
v___y_359_ = v___y_324_;
goto v___jp_354_;
}
else
{
lean_object* v___x_386_; 
lean_inc(v___x_346_);
v___x_386_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_346_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
if (lean_obj_tag(v___x_386_) == 0)
{
lean_dec_ref_known(v___x_386_, 1);
v___y_355_ = v___y_320_;
v___y_356_ = v___y_321_;
v___y_357_ = v___y_322_;
v___y_358_ = v___y_323_;
v___y_359_ = v___y_324_;
goto v___jp_354_;
}
else
{
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_394_; 
lean_dec_ref(v___f_353_);
lean_dec_ref(v___f_351_);
lean_dec(v___x_346_);
lean_del_object(v___x_330_);
v_a_387_ = lean_ctor_get(v___x_386_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_394_ == 0)
{
v___x_389_ = v___x_386_;
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_386_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_392_; 
if (v_isShared_390_ == 0)
{
v___x_392_ = v___x_389_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_a_387_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
}
}
else
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_402_; 
lean_dec_ref(v___f_353_);
lean_dec_ref(v___f_351_);
lean_dec(v___x_346_);
lean_del_object(v___x_330_);
v_a_395_ = lean_ctor_get(v___x_383_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_402_ == 0)
{
v___x_397_ = v___x_383_;
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_383_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_400_; 
if (v_isShared_398_ == 0)
{
v___x_400_ = v___x_397_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_a_395_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
}
v___jp_354_:
{
lean_object* v___x_360_; 
v___x_360_ = l_Lean_LocalDecl_value_x3f(v_val_342_, v___x_347_);
if (lean_obj_tag(v___x_360_) == 1)
{
lean_object* v_val_361_; lean_object* v___x_362_; 
v_val_361_ = lean_ctor_get(v___x_360_, 0);
lean_inc(v_val_361_);
lean_dec_ref_known(v___x_360_, 1);
v___x_362_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v_val_361_, v___f_351_, v___f_353_, v___y_357_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_object* v_a_363_; uint8_t v___x_364_; 
v_a_363_ = lean_ctor_get(v___x_362_, 0);
lean_inc(v_a_363_);
lean_dec_ref_known(v___x_362_, 1);
v___x_364_ = lean_unbox(v_a_363_);
lean_dec(v_a_363_);
if (v___x_364_ == 0)
{
lean_dec(v___x_346_);
v_a_334_ = v___x_345_;
goto v___jp_333_;
}
else
{
lean_object* v___x_365_; 
v___x_365_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_346_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_);
if (lean_obj_tag(v___x_365_) == 0)
{
lean_dec_ref_known(v___x_365_, 1);
v_a_334_ = v___x_345_;
goto v___jp_333_;
}
else
{
lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_373_; 
lean_del_object(v___x_330_);
v_a_366_ = lean_ctor_get(v___x_365_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_373_ == 0)
{
v___x_368_ = v___x_365_;
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_365_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_371_; 
if (v_isShared_369_ == 0)
{
v___x_371_ = v___x_368_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_a_366_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
}
else
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_381_; 
lean_dec(v___x_346_);
lean_del_object(v___x_330_);
v_a_374_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_381_ == 0)
{
v___x_376_ = v___x_362_;
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_362_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_374_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
else
{
lean_dec(v___x_360_);
lean_dec_ref(v___f_353_);
lean_dec_ref(v___f_351_);
lean_dec(v___x_346_);
v_a_334_ = v___x_345_;
goto v___jp_333_;
}
}
}
else
{
lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_410_; 
lean_dec_ref(v___x_348_);
lean_dec(v___x_346_);
lean_dec(v_snd_344_);
lean_del_object(v___x_330_);
v_a_403_ = lean_ctor_get(v___x_349_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_410_ == 0)
{
v___x_405_ = v___x_349_;
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_349_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_408_; 
if (v_isShared_406_ == 0)
{
v___x_408_ = v___x_405_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_a_403_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
else
{
lean_dec(v___x_346_);
lean_dec(v_snd_344_);
v_a_334_ = v___x_345_;
goto v___jp_333_;
}
}
v___jp_333_:
{
lean_object* v___x_336_; 
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 1, v_a_334_);
lean_ctor_set(v___x_330_, 0, v___x_332_);
v___x_336_ = v___x_330_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_332_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v_a_334_);
v___x_336_ = v_reuseFailAlloc_340_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
size_t v___x_337_; size_t v___x_338_; 
v___x_337_ = ((size_t)1ULL);
v___x_338_ = lean_usize_add(v_i_318_, v___x_337_);
v_i_318_ = v___x_338_;
v_b_319_ = v___x_336_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2_spec__5___boxed(lean_object* v_as_413_, lean_object* v_sz_414_, lean_object* v_i_415_, lean_object* v_b_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
size_t v_sz_boxed_423_; size_t v_i_boxed_424_; lean_object* v_res_425_; 
v_sz_boxed_423_ = lean_unbox_usize(v_sz_414_);
lean_dec(v_sz_414_);
v_i_boxed_424_ = lean_unbox_usize(v_i_415_);
lean_dec(v_i_415_);
v_res_425_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2_spec__5(v_as_413_, v_sz_boxed_423_, v_i_boxed_424_, v_b_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
lean_dec(v___y_417_);
lean_dec_ref(v_as_413_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2(lean_object* v_as_426_, size_t v_sz_427_, size_t v_i_428_, lean_object* v_b_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
uint8_t v___x_436_; 
v___x_436_ = lean_usize_dec_lt(v_i_428_, v_sz_427_);
if (v___x_436_ == 0)
{
lean_object* v___x_437_; 
v___x_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_437_, 0, v_b_429_);
return v___x_437_;
}
else
{
lean_object* v_snd_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_521_; 
v_snd_438_ = lean_ctor_get(v_b_429_, 1);
v_isSharedCheck_521_ = !lean_is_exclusive(v_b_429_);
if (v_isSharedCheck_521_ == 0)
{
lean_object* v_unused_522_; 
v_unused_522_ = lean_ctor_get(v_b_429_, 0);
lean_dec(v_unused_522_);
v___x_440_ = v_b_429_;
v_isShared_441_ = v_isSharedCheck_521_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_snd_438_);
lean_dec(v_b_429_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_521_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_442_; lean_object* v_a_444_; lean_object* v_a_451_; 
v___x_442_ = lean_box(0);
v_a_451_ = lean_array_uget_borrowed(v_as_426_, v_i_428_);
if (lean_obj_tag(v_a_451_) == 0)
{
v_a_444_ = v_snd_438_;
goto v___jp_443_;
}
else
{
lean_object* v_val_452_; lean_object* v___x_453_; lean_object* v_snd_454_; lean_object* v___x_455_; lean_object* v___x_456_; uint8_t v___x_457_; 
lean_dec(v_snd_438_);
v_val_452_ = lean_ctor_get(v_a_451_, 0);
v___x_453_ = lean_st_ref_get(v___y_430_);
v_snd_454_ = lean_ctor_get(v___x_453_, 1);
lean_inc(v_snd_454_);
lean_dec(v___x_453_);
v___x_455_ = lean_box(0);
v___x_456_ = l_Lean_LocalDecl_fvarId(v_val_452_);
v___x_457_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_456_, v_snd_454_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = l_Lean_LocalDecl_type(v_val_452_);
lean_inc_ref(v___x_458_);
v___x_459_ = l_Lean_Meta_isProp(v___x_458_, v___y_431_, v___y_432_, v___y_433_, v___y_434_);
if (lean_obj_tag(v___x_459_) == 0)
{
lean_object* v_a_460_; lean_object* v___f_461_; lean_object* v___x_462_; lean_object* v___f_463_; lean_object* v___y_465_; lean_object* v___y_466_; lean_object* v___y_467_; lean_object* v___y_468_; lean_object* v___y_469_; uint8_t v___x_492_; 
v_a_460_ = lean_ctor_get(v___x_459_, 0);
lean_inc(v_a_460_);
lean_dec_ref_known(v___x_459_, 1);
v___f_461_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_461_, 0, v_snd_454_);
v___x_462_ = lean_box(v___x_457_);
v___f_463_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__1___boxed), 2, 1);
lean_closure_set(v___f_463_, 0, v___x_462_);
v___x_492_ = lean_unbox(v_a_460_);
lean_dec(v_a_460_);
if (v___x_492_ == 0)
{
lean_dec_ref(v___x_458_);
v___y_465_ = v___y_430_;
v___y_466_ = v___y_431_;
v___y_467_ = v___y_432_;
v___y_468_ = v___y_433_;
v___y_469_ = v___y_434_;
goto v___jp_464_;
}
else
{
lean_object* v___x_493_; 
lean_inc_ref(v___f_463_);
lean_inc_ref(v___f_461_);
v___x_493_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v___x_458_, v___f_461_, v___f_463_, v___y_432_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; uint8_t v___x_495_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc(v_a_494_);
lean_dec_ref_known(v___x_493_, 1);
v___x_495_ = lean_unbox(v_a_494_);
lean_dec(v_a_494_);
if (v___x_495_ == 0)
{
v___y_465_ = v___y_430_;
v___y_466_ = v___y_431_;
v___y_467_ = v___y_432_;
v___y_468_ = v___y_433_;
v___y_469_ = v___y_434_;
goto v___jp_464_;
}
else
{
lean_object* v___x_496_; 
lean_inc(v___x_456_);
v___x_496_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_456_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_dec_ref_known(v___x_496_, 1);
v___y_465_ = v___y_430_;
v___y_466_ = v___y_431_;
v___y_467_ = v___y_432_;
v___y_468_ = v___y_433_;
v___y_469_ = v___y_434_;
goto v___jp_464_;
}
else
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_504_; 
lean_dec_ref(v___f_463_);
lean_dec_ref(v___f_461_);
lean_dec(v___x_456_);
lean_del_object(v___x_440_);
v_a_497_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_504_ == 0)
{
v___x_499_ = v___x_496_;
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_496_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_502_; 
if (v_isShared_500_ == 0)
{
v___x_502_ = v___x_499_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_a_497_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
}
else
{
lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_512_; 
lean_dec_ref(v___f_463_);
lean_dec_ref(v___f_461_);
lean_dec(v___x_456_);
lean_del_object(v___x_440_);
v_a_505_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_512_ == 0)
{
v___x_507_ = v___x_493_;
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_dec(v___x_493_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_510_; 
if (v_isShared_508_ == 0)
{
v___x_510_ = v___x_507_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_a_505_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
}
v___jp_464_:
{
lean_object* v___x_470_; 
v___x_470_ = l_Lean_LocalDecl_value_x3f(v_val_452_, v___x_457_);
if (lean_obj_tag(v___x_470_) == 1)
{
lean_object* v_val_471_; lean_object* v___x_472_; 
v_val_471_ = lean_ctor_get(v___x_470_, 0);
lean_inc(v_val_471_);
lean_dec_ref_known(v___x_470_, 1);
v___x_472_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v_val_471_, v___f_461_, v___f_463_, v___y_467_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; uint8_t v___x_474_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
lean_inc(v_a_473_);
lean_dec_ref_known(v___x_472_, 1);
v___x_474_ = lean_unbox(v_a_473_);
lean_dec(v_a_473_);
if (v___x_474_ == 0)
{
lean_dec(v___x_456_);
v_a_444_ = v___x_455_;
goto v___jp_443_;
}
else
{
lean_object* v___x_475_; 
v___x_475_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_456_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_dec_ref_known(v___x_475_, 1);
v_a_444_ = v___x_455_;
goto v___jp_443_;
}
else
{
lean_object* v_a_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_483_; 
lean_del_object(v___x_440_);
v_a_476_ = lean_ctor_get(v___x_475_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_483_ == 0)
{
v___x_478_ = v___x_475_;
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_a_476_);
lean_dec(v___x_475_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_481_; 
if (v_isShared_479_ == 0)
{
v___x_481_ = v___x_478_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_a_476_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
}
}
else
{
lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_491_; 
lean_dec(v___x_456_);
lean_del_object(v___x_440_);
v_a_484_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_491_ == 0)
{
v___x_486_ = v___x_472_;
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v___x_472_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_489_; 
if (v_isShared_487_ == 0)
{
v___x_489_ = v___x_486_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_a_484_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
}
else
{
lean_dec(v___x_470_);
lean_dec_ref(v___f_463_);
lean_dec_ref(v___f_461_);
lean_dec(v___x_456_);
v_a_444_ = v___x_455_;
goto v___jp_443_;
}
}
}
else
{
lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_520_; 
lean_dec_ref(v___x_458_);
lean_dec(v___x_456_);
lean_dec(v_snd_454_);
lean_del_object(v___x_440_);
v_a_513_ = lean_ctor_get(v___x_459_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_520_ == 0)
{
v___x_515_ = v___x_459_;
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v___x_459_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_518_; 
if (v_isShared_516_ == 0)
{
v___x_518_ = v___x_515_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_a_513_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
}
else
{
lean_dec(v___x_456_);
lean_dec(v_snd_454_);
v_a_444_ = v___x_455_;
goto v___jp_443_;
}
}
v___jp_443_:
{
lean_object* v___x_446_; 
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 1, v_a_444_);
lean_ctor_set(v___x_440_, 0, v___x_442_);
v___x_446_ = v___x_440_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v___x_442_);
lean_ctor_set(v_reuseFailAlloc_450_, 1, v_a_444_);
v___x_446_ = v_reuseFailAlloc_450_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
size_t v___x_447_; size_t v___x_448_; lean_object* v___x_449_; 
v___x_447_ = ((size_t)1ULL);
v___x_448_ = lean_usize_add(v_i_428_, v___x_447_);
v___x_449_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2_spec__5(v_as_426_, v_sz_427_, v___x_448_, v___x_446_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_);
return v___x_449_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___boxed(lean_object* v_as_523_, lean_object* v_sz_524_, lean_object* v_i_525_, lean_object* v_b_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
size_t v_sz_boxed_533_; size_t v_i_boxed_534_; lean_object* v_res_535_; 
v_sz_boxed_533_ = lean_unbox_usize(v_sz_524_);
lean_dec(v_sz_524_);
v_i_boxed_534_ = lean_unbox_usize(v_i_525_);
lean_dec(v_i_525_);
v_res_535_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2(v_as_523_, v_sz_boxed_533_, v_i_boxed_534_, v_b_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
lean_dec(v___y_527_);
lean_dec_ref(v_as_523_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3_spec__4(lean_object* v_as_536_, size_t v_sz_537_, size_t v_i_538_, lean_object* v_b_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
uint8_t v___x_546_; 
v___x_546_ = lean_usize_dec_lt(v_i_538_, v_sz_537_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; 
v___x_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_547_, 0, v_b_539_);
return v___x_547_;
}
else
{
lean_object* v_snd_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_631_; 
v_snd_548_ = lean_ctor_get(v_b_539_, 1);
v_isSharedCheck_631_ = !lean_is_exclusive(v_b_539_);
if (v_isSharedCheck_631_ == 0)
{
lean_object* v_unused_632_; 
v_unused_632_ = lean_ctor_get(v_b_539_, 0);
lean_dec(v_unused_632_);
v___x_550_ = v_b_539_;
v_isShared_551_ = v_isSharedCheck_631_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_snd_548_);
lean_dec(v_b_539_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_631_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_552_; lean_object* v_a_554_; lean_object* v_a_561_; 
v___x_552_ = lean_box(0);
v_a_561_ = lean_array_uget_borrowed(v_as_536_, v_i_538_);
if (lean_obj_tag(v_a_561_) == 0)
{
v_a_554_ = v_snd_548_;
goto v___jp_553_;
}
else
{
lean_object* v_val_562_; lean_object* v___x_563_; lean_object* v_snd_564_; lean_object* v___x_565_; lean_object* v___x_566_; uint8_t v___x_567_; 
lean_dec(v_snd_548_);
v_val_562_ = lean_ctor_get(v_a_561_, 0);
v___x_563_ = lean_st_ref_get(v___y_540_);
v_snd_564_ = lean_ctor_get(v___x_563_, 1);
lean_inc(v_snd_564_);
lean_dec(v___x_563_);
v___x_565_ = lean_box(0);
v___x_566_ = l_Lean_LocalDecl_fvarId(v_val_562_);
v___x_567_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_566_, v_snd_564_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = l_Lean_LocalDecl_type(v_val_562_);
lean_inc_ref(v___x_568_);
v___x_569_ = l_Lean_Meta_isProp(v___x_568_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v_a_570_; lean_object* v___f_571_; lean_object* v___x_572_; lean_object* v___f_573_; lean_object* v___y_575_; lean_object* v___y_576_; lean_object* v___y_577_; lean_object* v___y_578_; lean_object* v___y_579_; uint8_t v___x_602_; 
v_a_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc(v_a_570_);
lean_dec_ref_known(v___x_569_, 1);
v___f_571_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_571_, 0, v_snd_564_);
v___x_572_ = lean_box(v___x_567_);
v___f_573_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__1___boxed), 2, 1);
lean_closure_set(v___f_573_, 0, v___x_572_);
v___x_602_ = lean_unbox(v_a_570_);
lean_dec(v_a_570_);
if (v___x_602_ == 0)
{
lean_dec_ref(v___x_568_);
v___y_575_ = v___y_540_;
v___y_576_ = v___y_541_;
v___y_577_ = v___y_542_;
v___y_578_ = v___y_543_;
v___y_579_ = v___y_544_;
goto v___jp_574_;
}
else
{
lean_object* v___x_603_; 
lean_inc_ref(v___f_573_);
lean_inc_ref(v___f_571_);
v___x_603_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v___x_568_, v___f_571_, v___f_573_, v___y_542_);
if (lean_obj_tag(v___x_603_) == 0)
{
lean_object* v_a_604_; uint8_t v___x_605_; 
v_a_604_ = lean_ctor_get(v___x_603_, 0);
lean_inc(v_a_604_);
lean_dec_ref_known(v___x_603_, 1);
v___x_605_ = lean_unbox(v_a_604_);
lean_dec(v_a_604_);
if (v___x_605_ == 0)
{
v___y_575_ = v___y_540_;
v___y_576_ = v___y_541_;
v___y_577_ = v___y_542_;
v___y_578_ = v___y_543_;
v___y_579_ = v___y_544_;
goto v___jp_574_;
}
else
{
lean_object* v___x_606_; 
lean_inc(v___x_566_);
v___x_606_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_566_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_dec_ref_known(v___x_606_, 1);
v___y_575_ = v___y_540_;
v___y_576_ = v___y_541_;
v___y_577_ = v___y_542_;
v___y_578_ = v___y_543_;
v___y_579_ = v___y_544_;
goto v___jp_574_;
}
else
{
lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_614_; 
lean_dec_ref(v___f_573_);
lean_dec_ref(v___f_571_);
lean_dec(v___x_566_);
lean_del_object(v___x_550_);
v_a_607_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_614_ == 0)
{
v___x_609_ = v___x_606_;
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_dec(v___x_606_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_612_; 
if (v_isShared_610_ == 0)
{
v___x_612_ = v___x_609_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_a_607_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
}
else
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_622_; 
lean_dec_ref(v___f_573_);
lean_dec_ref(v___f_571_);
lean_dec(v___x_566_);
lean_del_object(v___x_550_);
v_a_615_ = lean_ctor_get(v___x_603_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_622_ == 0)
{
v___x_617_ = v___x_603_;
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___x_603_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_620_; 
if (v_isShared_618_ == 0)
{
v___x_620_ = v___x_617_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_a_615_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
}
v___jp_574_:
{
lean_object* v___x_580_; 
v___x_580_ = l_Lean_LocalDecl_value_x3f(v_val_562_, v___x_567_);
if (lean_obj_tag(v___x_580_) == 1)
{
lean_object* v_val_581_; lean_object* v___x_582_; 
v_val_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_val_581_);
lean_dec_ref_known(v___x_580_, 1);
v___x_582_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v_val_581_, v___f_571_, v___f_573_, v___y_577_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v_a_583_; uint8_t v___x_584_; 
v_a_583_ = lean_ctor_get(v___x_582_, 0);
lean_inc(v_a_583_);
lean_dec_ref_known(v___x_582_, 1);
v___x_584_ = lean_unbox(v_a_583_);
lean_dec(v_a_583_);
if (v___x_584_ == 0)
{
lean_dec(v___x_566_);
v_a_554_ = v___x_565_;
goto v___jp_553_;
}
else
{
lean_object* v___x_585_; 
v___x_585_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_566_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_dec_ref_known(v___x_585_, 1);
v_a_554_ = v___x_565_;
goto v___jp_553_;
}
else
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_593_; 
lean_del_object(v___x_550_);
v_a_586_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_593_ == 0)
{
v___x_588_ = v___x_585_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_585_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_591_; 
if (v_isShared_589_ == 0)
{
v___x_591_ = v___x_588_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_a_586_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
}
else
{
lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_601_; 
lean_dec(v___x_566_);
lean_del_object(v___x_550_);
v_a_594_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_601_ == 0)
{
v___x_596_ = v___x_582_;
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_582_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_a_594_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
}
else
{
lean_dec(v___x_580_);
lean_dec_ref(v___f_573_);
lean_dec_ref(v___f_571_);
lean_dec(v___x_566_);
v_a_554_ = v___x_565_;
goto v___jp_553_;
}
}
}
else
{
lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
lean_dec_ref(v___x_568_);
lean_dec(v___x_566_);
lean_dec(v_snd_564_);
lean_del_object(v___x_550_);
v_a_623_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_630_ == 0)
{
v___x_625_ = v___x_569_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___x_569_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_a_623_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
else
{
lean_dec(v___x_566_);
lean_dec(v_snd_564_);
v_a_554_ = v___x_565_;
goto v___jp_553_;
}
}
v___jp_553_:
{
lean_object* v___x_556_; 
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 1, v_a_554_);
lean_ctor_set(v___x_550_, 0, v___x_552_);
v___x_556_ = v___x_550_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_552_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v_a_554_);
v___x_556_ = v_reuseFailAlloc_560_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
size_t v___x_557_; size_t v___x_558_; 
v___x_557_ = ((size_t)1ULL);
v___x_558_ = lean_usize_add(v_i_538_, v___x_557_);
v_i_538_ = v___x_558_;
v_b_539_ = v___x_556_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3_spec__4___boxed(lean_object* v_as_633_, lean_object* v_sz_634_, lean_object* v_i_635_, lean_object* v_b_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
size_t v_sz_boxed_643_; size_t v_i_boxed_644_; lean_object* v_res_645_; 
v_sz_boxed_643_ = lean_unbox_usize(v_sz_634_);
lean_dec(v_sz_634_);
v_i_boxed_644_ = lean_unbox_usize(v_i_635_);
lean_dec(v_i_635_);
v_res_645_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3_spec__4(v_as_633_, v_sz_boxed_643_, v_i_boxed_644_, v_b_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec(v___y_637_);
lean_dec_ref(v_as_633_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3(lean_object* v_as_646_, size_t v_sz_647_, size_t v_i_648_, lean_object* v_b_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
uint8_t v___x_656_; 
v___x_656_ = lean_usize_dec_lt(v_i_648_, v_sz_647_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; 
v___x_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_657_, 0, v_b_649_);
return v___x_657_;
}
else
{
lean_object* v_snd_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_741_; 
v_snd_658_ = lean_ctor_get(v_b_649_, 1);
v_isSharedCheck_741_ = !lean_is_exclusive(v_b_649_);
if (v_isSharedCheck_741_ == 0)
{
lean_object* v_unused_742_; 
v_unused_742_ = lean_ctor_get(v_b_649_, 0);
lean_dec(v_unused_742_);
v___x_660_ = v_b_649_;
v_isShared_661_ = v_isSharedCheck_741_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_snd_658_);
lean_dec(v_b_649_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_741_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_662_; lean_object* v_a_664_; lean_object* v_a_671_; 
v___x_662_ = lean_box(0);
v_a_671_ = lean_array_uget_borrowed(v_as_646_, v_i_648_);
if (lean_obj_tag(v_a_671_) == 0)
{
v_a_664_ = v_snd_658_;
goto v___jp_663_;
}
else
{
lean_object* v_val_672_; lean_object* v___x_673_; lean_object* v_snd_674_; lean_object* v___x_675_; lean_object* v___x_676_; uint8_t v___x_677_; 
lean_dec(v_snd_658_);
v_val_672_ = lean_ctor_get(v_a_671_, 0);
v___x_673_ = lean_st_ref_get(v___y_650_);
v_snd_674_ = lean_ctor_get(v___x_673_, 1);
lean_inc(v_snd_674_);
lean_dec(v___x_673_);
v___x_675_ = lean_box(0);
v___x_676_ = l_Lean_LocalDecl_fvarId(v_val_672_);
v___x_677_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_676_, v_snd_674_);
if (v___x_677_ == 0)
{
lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_678_ = l_Lean_LocalDecl_type(v_val_672_);
lean_inc_ref(v___x_678_);
v___x_679_ = l_Lean_Meta_isProp(v___x_678_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_object* v_a_680_; lean_object* v___f_681_; lean_object* v___x_682_; lean_object* v___f_683_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; uint8_t v___x_712_; 
v_a_680_ = lean_ctor_get(v___x_679_, 0);
lean_inc(v_a_680_);
lean_dec_ref_known(v___x_679_, 1);
v___f_681_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_681_, 0, v_snd_674_);
v___x_682_ = lean_box(v___x_677_);
v___f_683_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__1___boxed), 2, 1);
lean_closure_set(v___f_683_, 0, v___x_682_);
v___x_712_ = lean_unbox(v_a_680_);
lean_dec(v_a_680_);
if (v___x_712_ == 0)
{
lean_dec_ref(v___x_678_);
v___y_685_ = v___y_650_;
v___y_686_ = v___y_651_;
v___y_687_ = v___y_652_;
v___y_688_ = v___y_653_;
v___y_689_ = v___y_654_;
goto v___jp_684_;
}
else
{
lean_object* v___x_713_; 
lean_inc_ref(v___f_683_);
lean_inc_ref(v___f_681_);
v___x_713_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v___x_678_, v___f_681_, v___f_683_, v___y_652_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v_a_714_; uint8_t v___x_715_; 
v_a_714_ = lean_ctor_get(v___x_713_, 0);
lean_inc(v_a_714_);
lean_dec_ref_known(v___x_713_, 1);
v___x_715_ = lean_unbox(v_a_714_);
lean_dec(v_a_714_);
if (v___x_715_ == 0)
{
v___y_685_ = v___y_650_;
v___y_686_ = v___y_651_;
v___y_687_ = v___y_652_;
v___y_688_ = v___y_653_;
v___y_689_ = v___y_654_;
goto v___jp_684_;
}
else
{
lean_object* v___x_716_; 
lean_inc(v___x_676_);
v___x_716_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_676_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_dec_ref_known(v___x_716_, 1);
v___y_685_ = v___y_650_;
v___y_686_ = v___y_651_;
v___y_687_ = v___y_652_;
v___y_688_ = v___y_653_;
v___y_689_ = v___y_654_;
goto v___jp_684_;
}
else
{
lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_724_; 
lean_dec_ref(v___f_683_);
lean_dec_ref(v___f_681_);
lean_dec(v___x_676_);
lean_del_object(v___x_660_);
v_a_717_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_724_ == 0)
{
v___x_719_ = v___x_716_;
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v___x_716_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_722_; 
if (v_isShared_720_ == 0)
{
v___x_722_ = v___x_719_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_a_717_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
}
else
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
lean_dec_ref(v___f_683_);
lean_dec_ref(v___f_681_);
lean_dec(v___x_676_);
lean_del_object(v___x_660_);
v_a_725_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_713_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_713_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
v___jp_684_:
{
lean_object* v___x_690_; 
v___x_690_ = l_Lean_LocalDecl_value_x3f(v_val_672_, v___x_677_);
if (lean_obj_tag(v___x_690_) == 1)
{
lean_object* v_val_691_; lean_object* v___x_692_; 
v_val_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc(v_val_691_);
lean_dec_ref_known(v___x_690_, 1);
v___x_692_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v_val_691_, v___f_681_, v___f_683_, v___y_687_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; uint8_t v___x_694_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_a_693_);
lean_dec_ref_known(v___x_692_, 1);
v___x_694_ = lean_unbox(v_a_693_);
lean_dec(v_a_693_);
if (v___x_694_ == 0)
{
lean_dec(v___x_676_);
v_a_664_ = v___x_675_;
goto v___jp_663_;
}
else
{
lean_object* v___x_695_; 
v___x_695_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_676_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_dec_ref_known(v___x_695_, 1);
v_a_664_ = v___x_675_;
goto v___jp_663_;
}
else
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
lean_del_object(v___x_660_);
v_a_696_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_703_ == 0)
{
v___x_698_ = v___x_695_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_695_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_696_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
}
}
else
{
lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_711_; 
lean_dec(v___x_676_);
lean_del_object(v___x_660_);
v_a_704_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_711_ == 0)
{
v___x_706_ = v___x_692_;
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_dec(v___x_692_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_709_; 
if (v_isShared_707_ == 0)
{
v___x_709_ = v___x_706_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_a_704_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
else
{
lean_dec(v___x_690_);
lean_dec_ref(v___f_683_);
lean_dec_ref(v___f_681_);
lean_dec(v___x_676_);
v_a_664_ = v___x_675_;
goto v___jp_663_;
}
}
}
else
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_740_; 
lean_dec_ref(v___x_678_);
lean_dec(v___x_676_);
lean_dec(v_snd_674_);
lean_del_object(v___x_660_);
v_a_733_ = lean_ctor_get(v___x_679_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_740_ == 0)
{
v___x_735_ = v___x_679_;
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_679_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_738_; 
if (v_isShared_736_ == 0)
{
v___x_738_ = v___x_735_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_a_733_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
}
else
{
lean_dec(v___x_676_);
lean_dec(v_snd_674_);
v_a_664_ = v___x_675_;
goto v___jp_663_;
}
}
v___jp_663_:
{
lean_object* v___x_666_; 
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 1, v_a_664_);
lean_ctor_set(v___x_660_, 0, v___x_662_);
v___x_666_ = v___x_660_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_662_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v_a_664_);
v___x_666_ = v_reuseFailAlloc_670_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
size_t v___x_667_; size_t v___x_668_; lean_object* v___x_669_; 
v___x_667_ = ((size_t)1ULL);
v___x_668_ = lean_usize_add(v_i_648_, v___x_667_);
v___x_669_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3_spec__4(v_as_646_, v_sz_647_, v___x_668_, v___x_666_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
return v___x_669_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3___boxed(lean_object* v_as_743_, lean_object* v_sz_744_, lean_object* v_i_745_, lean_object* v_b_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
size_t v_sz_boxed_753_; size_t v_i_boxed_754_; lean_object* v_res_755_; 
v_sz_boxed_753_ = lean_unbox_usize(v_sz_744_);
lean_dec(v_sz_744_);
v_i_boxed_754_ = lean_unbox_usize(v_i_745_);
lean_dec(v_i_745_);
v_res_755_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3(v_as_743_, v_sz_boxed_753_, v_i_boxed_754_, v_b_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_747_);
lean_dec_ref(v_as_743_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1(lean_object* v_init_756_, lean_object* v_n_757_, lean_object* v_b_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
if (lean_obj_tag(v_n_757_) == 0)
{
lean_object* v_cs_765_; lean_object* v___x_766_; lean_object* v___x_767_; size_t v_sz_768_; size_t v___x_769_; lean_object* v___x_770_; 
v_cs_765_ = lean_ctor_get(v_n_757_, 0);
v___x_766_ = lean_box(0);
v___x_767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
lean_ctor_set(v___x_767_, 1, v_b_758_);
v_sz_768_ = lean_array_size(v_cs_765_);
v___x_769_ = ((size_t)0ULL);
v___x_770_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__2(v_init_756_, v_cs_765_, v_sz_768_, v___x_769_, v___x_767_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_785_; 
v_a_771_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_785_ == 0)
{
v___x_773_ = v___x_770_;
v_isShared_774_ = v_isSharedCheck_785_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_770_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_785_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v_fst_775_; 
v_fst_775_ = lean_ctor_get(v_a_771_, 0);
if (lean_obj_tag(v_fst_775_) == 0)
{
lean_object* v_snd_776_; lean_object* v___x_777_; lean_object* v___x_779_; 
v_snd_776_ = lean_ctor_get(v_a_771_, 1);
lean_inc(v_snd_776_);
lean_dec(v_a_771_);
v___x_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_777_, 0, v_snd_776_);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 0, v___x_777_);
v___x_779_ = v___x_773_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v___x_777_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
else
{
lean_object* v_val_781_; lean_object* v___x_783_; 
lean_inc_ref(v_fst_775_);
lean_dec(v_a_771_);
v_val_781_ = lean_ctor_get(v_fst_775_, 0);
lean_inc(v_val_781_);
lean_dec_ref_known(v_fst_775_, 1);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 0, v_val_781_);
v___x_783_ = v___x_773_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_val_781_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
else
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
v_a_786_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_793_ == 0)
{
v___x_788_ = v___x_770_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_770_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_789_ == 0)
{
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_a_786_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
else
{
lean_object* v_vs_794_; lean_object* v___x_795_; lean_object* v___x_796_; size_t v_sz_797_; size_t v___x_798_; lean_object* v___x_799_; 
v_vs_794_ = lean_ctor_get(v_n_757_, 0);
v___x_795_ = lean_box(0);
v___x_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_795_);
lean_ctor_set(v___x_796_, 1, v_b_758_);
v_sz_797_ = lean_array_size(v_vs_794_);
v___x_798_ = ((size_t)0ULL);
v___x_799_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3(v_vs_794_, v_sz_797_, v___x_798_, v___x_796_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_814_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_814_ == 0)
{
v___x_802_ = v___x_799_;
v_isShared_803_ = v_isSharedCheck_814_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_799_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_814_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v_fst_804_; 
v_fst_804_ = lean_ctor_get(v_a_800_, 0);
if (lean_obj_tag(v_fst_804_) == 0)
{
lean_object* v_snd_805_; lean_object* v___x_806_; lean_object* v___x_808_; 
v_snd_805_ = lean_ctor_get(v_a_800_, 1);
lean_inc(v_snd_805_);
lean_dec(v_a_800_);
v___x_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_806_, 0, v_snd_805_);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 0, v___x_806_);
v___x_808_ = v___x_802_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_806_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
else
{
lean_object* v_val_810_; lean_object* v___x_812_; 
lean_inc_ref(v_fst_804_);
lean_dec(v_a_800_);
v_val_810_ = lean_ctor_get(v_fst_804_, 0);
lean_inc(v_val_810_);
lean_dec_ref_known(v_fst_804_, 1);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 0, v_val_810_);
v___x_812_ = v___x_802_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_val_810_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
}
else
{
lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_822_; 
v_a_815_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_822_ == 0)
{
v___x_817_ = v___x_799_;
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v___x_799_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_820_; 
if (v_isShared_818_ == 0)
{
v___x_820_ = v___x_817_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_a_815_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__2(lean_object* v_init_823_, lean_object* v_as_824_, size_t v_sz_825_, size_t v_i_826_, lean_object* v_b_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
uint8_t v___x_834_; 
v___x_834_ = lean_usize_dec_lt(v_i_826_, v_sz_825_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; 
v___x_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_835_, 0, v_b_827_);
return v___x_835_;
}
else
{
lean_object* v_snd_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_870_; 
v_snd_836_ = lean_ctor_get(v_b_827_, 1);
v_isSharedCheck_870_ = !lean_is_exclusive(v_b_827_);
if (v_isSharedCheck_870_ == 0)
{
lean_object* v_unused_871_; 
v_unused_871_ = lean_ctor_get(v_b_827_, 0);
lean_dec(v_unused_871_);
v___x_838_ = v_b_827_;
v_isShared_839_ = v_isSharedCheck_870_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_snd_836_);
lean_dec(v_b_827_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_870_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v_a_840_; lean_object* v___x_841_; 
v_a_840_ = lean_array_uget_borrowed(v_as_824_, v_i_826_);
lean_inc(v_snd_836_);
v___x_841_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1(v_init_823_, v_a_840_, v_snd_836_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_861_; 
v_a_842_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_861_ == 0)
{
v___x_844_ = v___x_841_;
v_isShared_845_ = v_isSharedCheck_861_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_841_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_861_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
if (lean_obj_tag(v_a_842_) == 0)
{
lean_object* v___x_846_; lean_object* v___x_848_; 
v___x_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_846_, 0, v_a_842_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 0, v___x_846_);
v___x_848_ = v___x_838_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_846_);
lean_ctor_set(v_reuseFailAlloc_852_, 1, v_snd_836_);
v___x_848_ = v_reuseFailAlloc_852_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
lean_object* v___x_850_; 
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 0, v___x_848_);
v___x_850_ = v___x_844_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_848_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
else
{
lean_object* v_a_853_; lean_object* v___x_854_; lean_object* v___x_856_; 
lean_del_object(v___x_844_);
lean_dec(v_snd_836_);
v_a_853_ = lean_ctor_get(v_a_842_, 0);
lean_inc(v_a_853_);
lean_dec_ref_known(v_a_842_, 1);
v___x_854_ = lean_box(0);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 1, v_a_853_);
lean_ctor_set(v___x_838_, 0, v___x_854_);
v___x_856_ = v___x_838_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_854_);
lean_ctor_set(v_reuseFailAlloc_860_, 1, v_a_853_);
v___x_856_ = v_reuseFailAlloc_860_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
size_t v___x_857_; size_t v___x_858_; 
v___x_857_ = ((size_t)1ULL);
v___x_858_ = lean_usize_add(v_i_826_, v___x_857_);
v_i_826_ = v___x_858_;
v_b_827_ = v___x_856_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_869_; 
lean_del_object(v___x_838_);
lean_dec(v_snd_836_);
v_a_862_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_841_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_841_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_865_ == 0)
{
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_862_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__2___boxed(lean_object* v_init_872_, lean_object* v_as_873_, lean_object* v_sz_874_, lean_object* v_i_875_, lean_object* v_b_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
size_t v_sz_boxed_883_; size_t v_i_boxed_884_; lean_object* v_res_885_; 
v_sz_boxed_883_ = lean_unbox_usize(v_sz_874_);
lean_dec(v_sz_874_);
v_i_boxed_884_ = lean_unbox_usize(v_i_875_);
lean_dec(v_i_875_);
v_res_885_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__2(v_init_872_, v_as_873_, v_sz_boxed_883_, v_i_boxed_884_, v_b_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v_as_873_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1___boxed(lean_object* v_init_886_, lean_object* v_n_887_, lean_object* v_b_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1(v_init_886_, v_n_887_, v_b_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
lean_dec(v___y_889_);
lean_dec_ref(v_n_887_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1(lean_object* v_t_896_, lean_object* v_init_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
lean_object* v_root_904_; lean_object* v_tail_905_; lean_object* v___x_906_; 
v_root_904_ = lean_ctor_get(v_t_896_, 0);
v_tail_905_ = lean_ctor_get(v_t_896_, 1);
v___x_906_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1(v_init_897_, v_root_904_, v_init_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_);
if (lean_obj_tag(v___x_906_) == 0)
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_943_; 
v_a_907_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_943_ == 0)
{
v___x_909_ = v___x_906_;
v_isShared_910_ = v_isSharedCheck_943_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_906_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_943_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
if (lean_obj_tag(v_a_907_) == 0)
{
lean_object* v_a_911_; lean_object* v___x_913_; 
v_a_911_ = lean_ctor_get(v_a_907_, 0);
lean_inc(v_a_911_);
lean_dec_ref_known(v_a_907_, 1);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 0, v_a_911_);
v___x_913_ = v___x_909_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_a_911_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
else
{
lean_object* v_a_915_; lean_object* v___x_916_; lean_object* v___x_917_; size_t v_sz_918_; size_t v___x_919_; lean_object* v___x_920_; 
lean_del_object(v___x_909_);
v_a_915_ = lean_ctor_get(v_a_907_, 0);
lean_inc(v_a_915_);
lean_dec_ref_known(v_a_907_, 1);
v___x_916_ = lean_box(0);
v___x_917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_916_);
lean_ctor_set(v___x_917_, 1, v_a_915_);
v_sz_918_ = lean_array_size(v_tail_905_);
v___x_919_ = ((size_t)0ULL);
v___x_920_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2(v_tail_905_, v_sz_918_, v___x_919_, v___x_917_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_934_; 
v_a_921_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_934_ == 0)
{
v___x_923_ = v___x_920_;
v_isShared_924_ = v_isSharedCheck_934_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_920_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_934_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v_fst_925_; 
v_fst_925_ = lean_ctor_get(v_a_921_, 0);
if (lean_obj_tag(v_fst_925_) == 0)
{
lean_object* v_snd_926_; lean_object* v___x_928_; 
v_snd_926_ = lean_ctor_get(v_a_921_, 1);
lean_inc(v_snd_926_);
lean_dec(v_a_921_);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 0, v_snd_926_);
v___x_928_ = v___x_923_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_snd_926_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
else
{
lean_object* v_val_930_; lean_object* v___x_932_; 
lean_inc_ref(v_fst_925_);
lean_dec(v_a_921_);
v_val_930_ = lean_ctor_get(v_fst_925_, 0);
lean_inc(v_val_930_);
lean_dec_ref_known(v_fst_925_, 1);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 0, v_val_930_);
v___x_932_ = v___x_923_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_val_930_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
else
{
lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_942_; 
v_a_935_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_942_ == 0)
{
v___x_937_ = v___x_920_;
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v___x_920_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_940_; 
if (v_isShared_938_ == 0)
{
v___x_940_ = v___x_937_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_a_935_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
}
}
}
else
{
lean_object* v_a_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_951_; 
v_a_944_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_951_ == 0)
{
v___x_946_ = v___x_906_;
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_a_944_);
lean_dec(v___x_906_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_949_; 
if (v_isShared_947_ == 0)
{
v___x_949_ = v___x_946_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_a_944_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1___boxed(lean_object* v_t_952_, lean_object* v_init_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1(v_t_952_, v_init_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v_t_952_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep(lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_){
_start:
{
lean_object* v_lctx_967_; lean_object* v_decls_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v_lctx_967_ = lean_ctor_get(v_a_962_, 2);
v_decls_968_ = lean_ctor_get(v_lctx_967_, 1);
v___x_969_ = lean_box(0);
v___x_970_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1(v_decls_968_, v___x_969_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_977_; 
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_977_ == 0)
{
lean_object* v_unused_978_; 
v_unused_978_ = lean_ctor_get(v___x_970_, 0);
lean_dec(v_unused_978_);
v___x_972_ = v___x_970_;
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
else
{
lean_dec(v___x_970_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_975_; 
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 0, v___x_969_);
v___x_975_ = v___x_972_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_969_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
else
{
return v___x_970_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep___boxed(lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep(v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_);
lean_dec(v_a_983_);
lean_dec_ref(v_a_982_);
lean_dec(v_a_981_);
lean_dec_ref(v_a_980_);
lean_dec(v_a_979_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectProps(lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_){
_start:
{
lean_object* v___x_992_; lean_object* v_snd_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1017_; 
v___x_992_ = lean_st_ref_take(v_a_986_);
v_snd_993_ = lean_ctor_get(v___x_992_, 1);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1017_ == 0)
{
lean_object* v_unused_1018_; 
v_unused_1018_ = lean_ctor_get(v___x_992_, 0);
lean_dec(v_unused_1018_);
v___x_995_ = v___x_992_;
v_isShared_996_ = v_isSharedCheck_1017_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_snd_993_);
lean_dec(v___x_992_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1017_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
uint8_t v___x_997_; lean_object* v___x_998_; lean_object* v___x_1000_; 
v___x_997_ = 0;
v___x_998_ = lean_box(v___x_997_);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 0, v___x_998_);
v___x_1000_ = v___x_995_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v___x_998_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v_snd_993_);
v___x_1000_ = v_reuseFailAlloc_1016_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = lean_st_ref_set(v_a_986_, v___x_1000_);
v___x_1002_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep(v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1014_; 
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1014_ == 0)
{
lean_object* v_unused_1015_; 
v_unused_1015_ = lean_ctor_get(v___x_1002_, 0);
lean_dec(v_unused_1015_);
v___x_1004_ = v___x_1002_;
v_isShared_1005_ = v_isSharedCheck_1014_;
goto v_resetjp_1003_;
}
else
{
lean_dec(v___x_1002_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1014_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1006_; lean_object* v_fst_1007_; uint8_t v___x_1008_; 
v___x_1006_ = lean_st_ref_get(v_a_986_);
v_fst_1007_ = lean_ctor_get(v___x_1006_, 0);
lean_inc(v_fst_1007_);
lean_dec(v___x_1006_);
v___x_1008_ = lean_unbox(v_fst_1007_);
lean_dec(v_fst_1007_);
if (v___x_1008_ == 0)
{
lean_object* v___x_1009_; lean_object* v___x_1011_; 
v___x_1009_ = lean_box(0);
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 0, v___x_1009_);
v___x_1011_ = v___x_1004_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v___x_1009_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
else
{
lean_del_object(v___x_1004_);
goto _start;
}
}
}
else
{
return v___x_1002_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectProps___boxed(lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectProps(v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_);
lean_dec(v_a_1023_);
lean_dec_ref(v_a_1022_);
lean_dec(v_a_1021_);
lean_dec_ref(v_a_1020_);
lean_dec(v_a_1019_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed_spec__0(lean_object* v_as_1026_, size_t v_i_1027_, size_t v_stop_1028_, lean_object* v_b_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
uint8_t v___x_1036_; 
v___x_1036_ = lean_usize_dec_eq(v_i_1027_, v_stop_1028_);
if (v___x_1036_ == 0)
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = lean_array_uget_borrowed(v_as_1026_, v_i_1027_);
lean_inc(v___x_1037_);
v___x_1038_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_1037_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_object* v_a_1039_; size_t v___x_1040_; size_t v___x_1041_; 
v_a_1039_ = lean_ctor_get(v___x_1038_, 0);
lean_inc(v_a_1039_);
lean_dec_ref_known(v___x_1038_, 1);
v___x_1040_ = ((size_t)1ULL);
v___x_1041_ = lean_usize_add(v_i_1027_, v___x_1040_);
v_i_1027_ = v___x_1041_;
v_b_1029_ = v_a_1039_;
goto _start;
}
else
{
return v___x_1038_;
}
}
else
{
lean_object* v___x_1043_; 
v___x_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1043_, 0, v_b_1029_);
return v___x_1043_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed_spec__0___boxed(lean_object* v_as_1044_, lean_object* v_i_1045_, lean_object* v_stop_1046_, lean_object* v_b_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
size_t v_i_boxed_1054_; size_t v_stop_boxed_1055_; lean_object* v_res_1056_; 
v_i_boxed_1054_ = lean_unbox_usize(v_i_1045_);
lean_dec(v_i_1045_);
v_stop_boxed_1055_ = lean_unbox_usize(v_stop_1046_);
lean_dec(v_stop_1046_);
v_res_1056_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed_spec__0(v_as_1044_, v_i_boxed_1054_, v_stop_boxed_1055_, v_b_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec_ref(v_as_1044_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed(lean_object* v_mvarId_1057_, lean_object* v_toPreserve_1058_, uint8_t v_indirectProps_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_){
_start:
{
lean_object* v___y_1067_; lean_object* v___y_1082_; lean_object* v___x_1091_; 
v___x_1091_ = l_Lean_MVarId_getType(v_mvarId_1057_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v_a_1092_; lean_object* v___x_1093_; lean_object* v_a_1094_; lean_object* v___x_1095_; 
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
lean_inc(v_a_1092_);
lean_dec_ref_known(v___x_1091_, 1);
v___x_1093_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0___redArg(v_a_1092_, v_a_1062_);
v_a_1094_ = lean_ctor_get(v___x_1093_, 0);
lean_inc(v_a_1094_);
lean_dec_ref(v___x_1093_);
v___x_1095_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars(v_a_1094_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_object* v___x_1096_; lean_object* v___x_1097_; uint8_t v___x_1098_; 
lean_dec_ref_known(v___x_1095_, 1);
v___x_1096_ = lean_unsigned_to_nat(0u);
v___x_1097_ = lean_array_get_size(v_toPreserve_1058_);
v___x_1098_ = lean_nat_dec_lt(v___x_1096_, v___x_1097_);
if (v___x_1098_ == 0)
{
goto v___jp_1071_;
}
else
{
lean_object* v___x_1099_; uint8_t v___x_1100_; 
v___x_1099_ = lean_box(0);
v___x_1100_ = lean_nat_dec_le(v___x_1097_, v___x_1097_);
if (v___x_1100_ == 0)
{
if (v___x_1098_ == 0)
{
goto v___jp_1071_;
}
else
{
size_t v___x_1101_; size_t v___x_1102_; lean_object* v___x_1103_; 
v___x_1101_ = ((size_t)0ULL);
v___x_1102_ = lean_usize_of_nat(v___x_1097_);
v___x_1103_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed_spec__0(v_toPreserve_1058_, v___x_1101_, v___x_1102_, v___x_1099_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
v___y_1082_ = v___x_1103_;
goto v___jp_1081_;
}
}
else
{
size_t v___x_1104_; size_t v___x_1105_; lean_object* v___x_1106_; 
v___x_1104_ = ((size_t)0ULL);
v___x_1105_ = lean_usize_of_nat(v___x_1097_);
v___x_1106_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed_spec__0(v_toPreserve_1058_, v___x_1104_, v___x_1105_, v___x_1099_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
v___y_1082_ = v___x_1106_;
goto v___jp_1081_;
}
}
}
else
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
v_a_1107_ = lean_ctor_get(v___x_1095_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v___x_1095_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1095_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1110_ == 0)
{
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1107_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
else
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1122_; 
v_a_1115_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1117_ = v___x_1091_;
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1091_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1120_; 
if (v_isShared_1118_ == 0)
{
v___x_1120_ = v___x_1117_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_a_1115_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
v___jp_1066_:
{
lean_object* v___x_1068_; lean_object* v_snd_1069_; lean_object* v___x_1070_; 
v___x_1068_ = lean_st_ref_get(v___y_1067_);
v_snd_1069_ = lean_ctor_get(v___x_1068_, 1);
lean_inc(v_snd_1069_);
lean_dec(v___x_1068_);
v___x_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1070_, 0, v_snd_1069_);
return v___x_1070_;
}
v___jp_1071_:
{
if (v_indirectProps_1059_ == 0)
{
v___y_1067_ = v_a_1060_;
goto v___jp_1066_;
}
else
{
lean_object* v___x_1072_; 
v___x_1072_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectProps(v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_dec_ref_known(v___x_1072_, 1);
v___y_1067_ = v_a_1060_;
goto v___jp_1066_;
}
else
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1080_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1075_ = v___x_1072_;
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1072_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_a_1073_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
}
v___jp_1081_:
{
if (lean_obj_tag(v___y_1082_) == 0)
{
lean_dec_ref_known(v___y_1082_, 1);
goto v___jp_1071_;
}
else
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1090_; 
v_a_1083_ = lean_ctor_get(v___y_1082_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___y_1082_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1085_ = v___y_1082_;
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___y_1082_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_a_1083_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed___boxed(lean_object* v_mvarId_1123_, lean_object* v_toPreserve_1124_, lean_object* v_indirectProps_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_){
_start:
{
uint8_t v_indirectProps_boxed_1132_; lean_object* v_res_1133_; 
v_indirectProps_boxed_1132_ = lean_unbox(v_indirectProps_1125_);
v_res_1133_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed(v_mvarId_1123_, v_toPreserve_1124_, v_indirectProps_boxed_1132_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
lean_dec(v_a_1130_);
lean_dec_ref(v_a_1129_);
lean_dec(v_a_1128_);
lean_dec_ref(v_a_1127_);
lean_dec(v_a_1126_);
lean_dec_ref(v_toPreserve_1124_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___redArg(lean_object* v_e_1134_, lean_object* v___y_1135_){
_start:
{
uint8_t v___x_1137_; 
v___x_1137_ = l_Lean_Expr_hasMVar(v_e_1134_);
if (v___x_1137_ == 0)
{
lean_object* v___x_1138_; 
v___x_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1138_, 0, v_e_1134_);
return v___x_1138_;
}
else
{
lean_object* v___x_1139_; lean_object* v_mctx_1140_; lean_object* v___x_1141_; lean_object* v_fst_1142_; lean_object* v_snd_1143_; lean_object* v___x_1144_; lean_object* v_cache_1145_; lean_object* v_zetaDeltaFVarIds_1146_; lean_object* v_postponed_1147_; lean_object* v_diag_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1157_; 
v___x_1139_ = lean_st_ref_get(v___y_1135_);
v_mctx_1140_ = lean_ctor_get(v___x_1139_, 0);
lean_inc_ref(v_mctx_1140_);
lean_dec(v___x_1139_);
v___x_1141_ = l_Lean_instantiateMVarsCore(v_mctx_1140_, v_e_1134_);
v_fst_1142_ = lean_ctor_get(v___x_1141_, 0);
lean_inc(v_fst_1142_);
v_snd_1143_ = lean_ctor_get(v___x_1141_, 1);
lean_inc(v_snd_1143_);
lean_dec_ref(v___x_1141_);
v___x_1144_ = lean_st_ref_take(v___y_1135_);
v_cache_1145_ = lean_ctor_get(v___x_1144_, 1);
v_zetaDeltaFVarIds_1146_ = lean_ctor_get(v___x_1144_, 2);
v_postponed_1147_ = lean_ctor_get(v___x_1144_, 3);
v_diag_1148_ = lean_ctor_get(v___x_1144_, 4);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1157_ == 0)
{
lean_object* v_unused_1158_; 
v_unused_1158_ = lean_ctor_get(v___x_1144_, 0);
lean_dec(v_unused_1158_);
v___x_1150_ = v___x_1144_;
v_isShared_1151_ = v_isSharedCheck_1157_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_diag_1148_);
lean_inc(v_postponed_1147_);
lean_inc(v_zetaDeltaFVarIds_1146_);
lean_inc(v_cache_1145_);
lean_dec(v___x_1144_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1157_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1153_; 
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 0, v_snd_1143_);
v___x_1153_ = v___x_1150_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_snd_1143_);
lean_ctor_set(v_reuseFailAlloc_1156_, 1, v_cache_1145_);
lean_ctor_set(v_reuseFailAlloc_1156_, 2, v_zetaDeltaFVarIds_1146_);
lean_ctor_set(v_reuseFailAlloc_1156_, 3, v_postponed_1147_);
lean_ctor_set(v_reuseFailAlloc_1156_, 4, v_diag_1148_);
v___x_1153_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1154_ = lean_st_ref_set(v___y_1135_, v___x_1153_);
v___x_1155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1155_, 0, v_fst_1142_);
return v___x_1155_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___redArg___boxed(lean_object* v_e_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___redArg(v_e_1159_, v___y_1160_);
lean_dec(v___y_1160_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1(lean_object* v_e_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
lean_object* v___x_1169_; 
v___x_1169_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___redArg(v_e_1163_, v___y_1165_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___boxed(lean_object* v_e_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1(v_e_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
lean_dec(v___y_1174_);
lean_dec_ref(v___y_1173_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___redArg(lean_object* v_mvarId_1177_, lean_object* v_x_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v___x_1184_; 
v___x_1184_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1177_, v_x_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_);
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1192_; 
v_a_1185_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1187_ = v___x_1184_;
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_a_1185_);
lean_dec(v___x_1184_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1190_; 
if (v_isShared_1188_ == 0)
{
v___x_1190_ = v___x_1187_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_a_1185_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
else
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1200_; 
v_a_1193_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1195_ = v___x_1184_;
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1184_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1198_; 
if (v_isShared_1196_ == 0)
{
v___x_1198_ = v___x_1195_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_a_1193_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___redArg___boxed(lean_object* v_mvarId_1201_, lean_object* v_x_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___redArg(v_mvarId_1201_, v_x_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4(lean_object* v_00_u03b1_1209_, lean_object* v_mvarId_1210_, lean_object* v_x_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v___x_1217_; 
v___x_1217_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___redArg(v_mvarId_1210_, v_x_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___boxed(lean_object* v_00_u03b1_1218_, lean_object* v_mvarId_1219_, lean_object* v_x_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4(v_00_u03b1_1218_, v_mvarId_1219_, v_x_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__3(lean_object* v_a_1227_, lean_object* v_as_1228_, size_t v_i_1229_, size_t v_stop_1230_, lean_object* v_b_1231_){
_start:
{
lean_object* v___y_1233_; uint8_t v___x_1237_; 
v___x_1237_ = lean_usize_dec_eq(v_i_1229_, v_stop_1230_);
if (v___x_1237_ == 0)
{
lean_object* v___x_1238_; lean_object* v_fvar_1239_; lean_object* v___x_1240_; uint8_t v___x_1241_; 
v___x_1238_ = lean_array_uget_borrowed(v_as_1228_, v_i_1229_);
v_fvar_1239_ = lean_ctor_get(v___x_1238_, 1);
v___x_1240_ = l_Lean_Expr_fvarId_x21(v_fvar_1239_);
v___x_1241_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_1240_, v_a_1227_);
lean_dec(v___x_1240_);
if (v___x_1241_ == 0)
{
v___y_1233_ = v_b_1231_;
goto v___jp_1232_;
}
else
{
lean_object* v___x_1242_; 
lean_inc(v___x_1238_);
v___x_1242_ = lean_array_push(v_b_1231_, v___x_1238_);
v___y_1233_ = v___x_1242_;
goto v___jp_1232_;
}
}
else
{
return v_b_1231_;
}
v___jp_1232_:
{
size_t v___x_1234_; size_t v___x_1235_; 
v___x_1234_ = ((size_t)1ULL);
v___x_1235_ = lean_usize_add(v_i_1229_, v___x_1234_);
v_i_1229_ = v___x_1235_;
v_b_1231_ = v___y_1233_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__3___boxed(lean_object* v_a_1243_, lean_object* v_as_1244_, lean_object* v_i_1245_, lean_object* v_stop_1246_, lean_object* v_b_1247_){
_start:
{
size_t v_i_boxed_1248_; size_t v_stop_boxed_1249_; lean_object* v_res_1250_; 
v_i_boxed_1248_ = lean_unbox_usize(v_i_1245_);
lean_dec(v_i_1245_);
v_stop_boxed_1249_ = lean_unbox_usize(v_stop_1246_);
lean_dec(v_stop_1246_);
v_res_1250_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__3(v_a_1243_, v_as_1244_, v_i_boxed_1248_, v_stop_boxed_1249_, v_b_1247_);
lean_dec_ref(v_as_1244_);
lean_dec(v_a_1243_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12_spec__13___redArg(lean_object* v_x_1251_, lean_object* v_x_1252_, lean_object* v_x_1253_, lean_object* v_x_1254_){
_start:
{
lean_object* v_ks_1255_; lean_object* v_vs_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1280_; 
v_ks_1255_ = lean_ctor_get(v_x_1251_, 0);
v_vs_1256_ = lean_ctor_get(v_x_1251_, 1);
v_isSharedCheck_1280_ = !lean_is_exclusive(v_x_1251_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1258_ = v_x_1251_;
v_isShared_1259_ = v_isSharedCheck_1280_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_vs_1256_);
lean_inc(v_ks_1255_);
lean_dec(v_x_1251_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1280_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1260_; uint8_t v___x_1261_; 
v___x_1260_ = lean_array_get_size(v_ks_1255_);
v___x_1261_ = lean_nat_dec_lt(v_x_1252_, v___x_1260_);
if (v___x_1261_ == 0)
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1265_; 
lean_dec(v_x_1252_);
v___x_1262_ = lean_array_push(v_ks_1255_, v_x_1253_);
v___x_1263_ = lean_array_push(v_vs_1256_, v_x_1254_);
if (v_isShared_1259_ == 0)
{
lean_ctor_set(v___x_1258_, 1, v___x_1263_);
lean_ctor_set(v___x_1258_, 0, v___x_1262_);
v___x_1265_ = v___x_1258_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1262_);
lean_ctor_set(v_reuseFailAlloc_1266_, 1, v___x_1263_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
else
{
lean_object* v_k_x27_1267_; uint8_t v___x_1268_; 
v_k_x27_1267_ = lean_array_fget_borrowed(v_ks_1255_, v_x_1252_);
v___x_1268_ = l_Lean_instBEqMVarId_beq(v_x_1253_, v_k_x27_1267_);
if (v___x_1268_ == 0)
{
lean_object* v___x_1270_; 
if (v_isShared_1259_ == 0)
{
v___x_1270_ = v___x_1258_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_ks_1255_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v_vs_1256_);
v___x_1270_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1271_ = lean_unsigned_to_nat(1u);
v___x_1272_ = lean_nat_add(v_x_1252_, v___x_1271_);
lean_dec(v_x_1252_);
v_x_1251_ = v___x_1270_;
v_x_1252_ = v___x_1272_;
goto _start;
}
}
else
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1278_; 
v___x_1275_ = lean_array_fset(v_ks_1255_, v_x_1252_, v_x_1253_);
v___x_1276_ = lean_array_fset(v_vs_1256_, v_x_1252_, v_x_1254_);
lean_dec(v_x_1252_);
if (v_isShared_1259_ == 0)
{
lean_ctor_set(v___x_1258_, 1, v___x_1276_);
lean_ctor_set(v___x_1258_, 0, v___x_1275_);
v___x_1278_ = v___x_1258_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___x_1275_);
lean_ctor_set(v_reuseFailAlloc_1279_, 1, v___x_1276_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12___redArg(lean_object* v_n_1281_, lean_object* v_k_1282_, lean_object* v_v_1283_){
_start:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1284_ = lean_unsigned_to_nat(0u);
v___x_1285_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12_spec__13___redArg(v_n_1281_, v___x_1284_, v_k_1282_, v_v_1283_);
return v___x_1285_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1286_; 
v___x_1286_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg(lean_object* v_x_1287_, size_t v_x_1288_, size_t v_x_1289_, lean_object* v_x_1290_, lean_object* v_x_1291_){
_start:
{
if (lean_obj_tag(v_x_1287_) == 0)
{
lean_object* v_es_1292_; size_t v___x_1293_; size_t v___x_1294_; lean_object* v_j_1295_; lean_object* v___x_1296_; uint8_t v___x_1297_; 
v_es_1292_ = lean_ctor_get(v_x_1287_, 0);
v___x_1293_ = ((size_t)31ULL);
v___x_1294_ = lean_usize_land(v_x_1288_, v___x_1293_);
v_j_1295_ = lean_usize_to_nat(v___x_1294_);
v___x_1296_ = lean_array_get_size(v_es_1292_);
v___x_1297_ = lean_nat_dec_lt(v_j_1295_, v___x_1296_);
if (v___x_1297_ == 0)
{
lean_dec(v_j_1295_);
lean_dec(v_x_1291_);
lean_dec(v_x_1290_);
return v_x_1287_;
}
else
{
lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1336_; 
lean_inc_ref(v_es_1292_);
v_isSharedCheck_1336_ = !lean_is_exclusive(v_x_1287_);
if (v_isSharedCheck_1336_ == 0)
{
lean_object* v_unused_1337_; 
v_unused_1337_ = lean_ctor_get(v_x_1287_, 0);
lean_dec(v_unused_1337_);
v___x_1299_ = v_x_1287_;
v_isShared_1300_ = v_isSharedCheck_1336_;
goto v_resetjp_1298_;
}
else
{
lean_dec(v_x_1287_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1336_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v_v_1301_; lean_object* v___x_1302_; lean_object* v_xs_x27_1303_; lean_object* v___y_1305_; 
v_v_1301_ = lean_array_fget(v_es_1292_, v_j_1295_);
v___x_1302_ = lean_box(0);
v_xs_x27_1303_ = lean_array_fset(v_es_1292_, v_j_1295_, v___x_1302_);
switch(lean_obj_tag(v_v_1301_))
{
case 0:
{
lean_object* v_key_1310_; lean_object* v_val_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1321_; 
v_key_1310_ = lean_ctor_get(v_v_1301_, 0);
v_val_1311_ = lean_ctor_get(v_v_1301_, 1);
v_isSharedCheck_1321_ = !lean_is_exclusive(v_v_1301_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1313_ = v_v_1301_;
v_isShared_1314_ = v_isSharedCheck_1321_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_val_1311_);
lean_inc(v_key_1310_);
lean_dec(v_v_1301_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1321_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
uint8_t v___x_1315_; 
v___x_1315_ = l_Lean_instBEqMVarId_beq(v_x_1290_, v_key_1310_);
if (v___x_1315_ == 0)
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
lean_del_object(v___x_1313_);
v___x_1316_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1310_, v_val_1311_, v_x_1290_, v_x_1291_);
v___x_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1316_);
v___y_1305_ = v___x_1317_;
goto v___jp_1304_;
}
else
{
lean_object* v___x_1319_; 
lean_dec(v_val_1311_);
lean_dec(v_key_1310_);
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 1, v_x_1291_);
lean_ctor_set(v___x_1313_, 0, v_x_1290_);
v___x_1319_ = v___x_1313_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_x_1290_);
lean_ctor_set(v_reuseFailAlloc_1320_, 1, v_x_1291_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
v___y_1305_ = v___x_1319_;
goto v___jp_1304_;
}
}
}
}
case 1:
{
lean_object* v_node_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1334_; 
v_node_1322_ = lean_ctor_get(v_v_1301_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v_v_1301_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1324_ = v_v_1301_;
v_isShared_1325_ = v_isSharedCheck_1334_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_node_1322_);
lean_dec(v_v_1301_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1334_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
size_t v___x_1326_; size_t v___x_1327_; size_t v___x_1328_; size_t v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1332_; 
v___x_1326_ = ((size_t)5ULL);
v___x_1327_ = lean_usize_shift_right(v_x_1288_, v___x_1326_);
v___x_1328_ = ((size_t)1ULL);
v___x_1329_ = lean_usize_add(v_x_1289_, v___x_1328_);
v___x_1330_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg(v_node_1322_, v___x_1327_, v___x_1329_, v_x_1290_, v_x_1291_);
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 0, v___x_1330_);
v___x_1332_ = v___x_1324_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1330_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
v___y_1305_ = v___x_1332_;
goto v___jp_1304_;
}
}
}
default: 
{
lean_object* v___x_1335_; 
v___x_1335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1335_, 0, v_x_1290_);
lean_ctor_set(v___x_1335_, 1, v_x_1291_);
v___y_1305_ = v___x_1335_;
goto v___jp_1304_;
}
}
v___jp_1304_:
{
lean_object* v___x_1306_; lean_object* v___x_1308_; 
v___x_1306_ = lean_array_fset(v_xs_x27_1303_, v_j_1295_, v___y_1305_);
lean_dec(v_j_1295_);
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 0, v___x_1306_);
v___x_1308_ = v___x_1299_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v___x_1306_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
}
}
else
{
lean_object* v_ks_1338_; lean_object* v_vs_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1359_; 
v_ks_1338_ = lean_ctor_get(v_x_1287_, 0);
v_vs_1339_ = lean_ctor_get(v_x_1287_, 1);
v_isSharedCheck_1359_ = !lean_is_exclusive(v_x_1287_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1341_ = v_x_1287_;
v_isShared_1342_ = v_isSharedCheck_1359_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_vs_1339_);
lean_inc(v_ks_1338_);
lean_dec(v_x_1287_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1359_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1344_; 
if (v_isShared_1342_ == 0)
{
v___x_1344_ = v___x_1341_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_ks_1338_);
lean_ctor_set(v_reuseFailAlloc_1358_, 1, v_vs_1339_);
v___x_1344_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
lean_object* v_newNode_1345_; uint8_t v___y_1347_; size_t v___x_1353_; uint8_t v___x_1354_; 
v_newNode_1345_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12___redArg(v___x_1344_, v_x_1290_, v_x_1291_);
v___x_1353_ = ((size_t)7ULL);
v___x_1354_ = lean_usize_dec_le(v___x_1353_, v_x_1289_);
if (v___x_1354_ == 0)
{
lean_object* v___x_1355_; lean_object* v___x_1356_; uint8_t v___x_1357_; 
v___x_1355_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1345_);
v___x_1356_ = lean_unsigned_to_nat(4u);
v___x_1357_ = lean_nat_dec_lt(v___x_1355_, v___x_1356_);
lean_dec(v___x_1355_);
v___y_1347_ = v___x_1357_;
goto v___jp_1346_;
}
else
{
v___y_1347_ = v___x_1354_;
goto v___jp_1346_;
}
v___jp_1346_:
{
if (v___y_1347_ == 0)
{
lean_object* v_ks_1348_; lean_object* v_vs_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v_ks_1348_ = lean_ctor_get(v_newNode_1345_, 0);
lean_inc_ref(v_ks_1348_);
v_vs_1349_ = lean_ctor_get(v_newNode_1345_, 1);
lean_inc_ref(v_vs_1349_);
lean_dec_ref(v_newNode_1345_);
v___x_1350_ = lean_unsigned_to_nat(0u);
v___x_1351_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__0);
v___x_1352_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___redArg(v_x_1289_, v_ks_1348_, v_vs_1349_, v___x_1350_, v___x_1351_);
lean_dec_ref(v_vs_1349_);
lean_dec_ref(v_ks_1348_);
return v___x_1352_;
}
else
{
return v_newNode_1345_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___redArg(size_t v_depth_1360_, lean_object* v_keys_1361_, lean_object* v_vals_1362_, lean_object* v_i_1363_, lean_object* v_entries_1364_){
_start:
{
lean_object* v___x_1365_; uint8_t v___x_1366_; 
v___x_1365_ = lean_array_get_size(v_keys_1361_);
v___x_1366_ = lean_nat_dec_lt(v_i_1363_, v___x_1365_);
if (v___x_1366_ == 0)
{
lean_dec(v_i_1363_);
return v_entries_1364_;
}
else
{
lean_object* v_k_1367_; lean_object* v_v_1368_; uint64_t v___x_1369_; size_t v_h_1370_; size_t v___x_1371_; lean_object* v___x_1372_; size_t v___x_1373_; size_t v___x_1374_; size_t v___x_1375_; size_t v_h_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
v_k_1367_ = lean_array_fget_borrowed(v_keys_1361_, v_i_1363_);
v_v_1368_ = lean_array_fget_borrowed(v_vals_1362_, v_i_1363_);
v___x_1369_ = l_Lean_instHashableMVarId_hash(v_k_1367_);
v_h_1370_ = lean_uint64_to_usize(v___x_1369_);
v___x_1371_ = ((size_t)5ULL);
v___x_1372_ = lean_unsigned_to_nat(1u);
v___x_1373_ = ((size_t)1ULL);
v___x_1374_ = lean_usize_sub(v_depth_1360_, v___x_1373_);
v___x_1375_ = lean_usize_mul(v___x_1371_, v___x_1374_);
v_h_1376_ = lean_usize_shift_right(v_h_1370_, v___x_1375_);
v___x_1377_ = lean_nat_add(v_i_1363_, v___x_1372_);
lean_dec(v_i_1363_);
lean_inc(v_v_1368_);
lean_inc(v_k_1367_);
v___x_1378_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg(v_entries_1364_, v_h_1376_, v_depth_1360_, v_k_1367_, v_v_1368_);
v_i_1363_ = v___x_1377_;
v_entries_1364_ = v___x_1378_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___redArg___boxed(lean_object* v_depth_1380_, lean_object* v_keys_1381_, lean_object* v_vals_1382_, lean_object* v_i_1383_, lean_object* v_entries_1384_){
_start:
{
size_t v_depth_boxed_1385_; lean_object* v_res_1386_; 
v_depth_boxed_1385_ = lean_unbox_usize(v_depth_1380_);
lean_dec(v_depth_1380_);
v_res_1386_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___redArg(v_depth_boxed_1385_, v_keys_1381_, v_vals_1382_, v_i_1383_, v_entries_1384_);
lean_dec_ref(v_vals_1382_);
lean_dec_ref(v_keys_1381_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___boxed(lean_object* v_x_1387_, lean_object* v_x_1388_, lean_object* v_x_1389_, lean_object* v_x_1390_, lean_object* v_x_1391_){
_start:
{
size_t v_x_7474__boxed_1392_; size_t v_x_7475__boxed_1393_; lean_object* v_res_1394_; 
v_x_7474__boxed_1392_ = lean_unbox_usize(v_x_1388_);
lean_dec(v_x_1388_);
v_x_7475__boxed_1393_ = lean_unbox_usize(v_x_1389_);
lean_dec(v_x_1389_);
v_res_1394_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg(v_x_1387_, v_x_7474__boxed_1392_, v_x_7475__boxed_1393_, v_x_1390_, v_x_1391_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4___redArg(lean_object* v_x_1395_, lean_object* v_x_1396_, lean_object* v_x_1397_){
_start:
{
uint64_t v___x_1398_; size_t v___x_1399_; size_t v___x_1400_; lean_object* v___x_1401_; 
v___x_1398_ = l_Lean_instHashableMVarId_hash(v_x_1396_);
v___x_1399_ = lean_uint64_to_usize(v___x_1398_);
v___x_1400_ = ((size_t)1ULL);
v___x_1401_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg(v_x_1395_, v___x_1399_, v___x_1400_, v_x_1396_, v_x_1397_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___redArg(lean_object* v_mvarId_1402_, lean_object* v_val_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v___x_1406_; lean_object* v_mctx_1407_; lean_object* v_cache_1408_; lean_object* v_zetaDeltaFVarIds_1409_; lean_object* v_postponed_1410_; lean_object* v_diag_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1439_; 
v___x_1406_ = lean_st_ref_take(v___y_1404_);
v_mctx_1407_ = lean_ctor_get(v___x_1406_, 0);
v_cache_1408_ = lean_ctor_get(v___x_1406_, 1);
v_zetaDeltaFVarIds_1409_ = lean_ctor_get(v___x_1406_, 2);
v_postponed_1410_ = lean_ctor_get(v___x_1406_, 3);
v_diag_1411_ = lean_ctor_get(v___x_1406_, 4);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1413_ = v___x_1406_;
v_isShared_1414_ = v_isSharedCheck_1439_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_diag_1411_);
lean_inc(v_postponed_1410_);
lean_inc(v_zetaDeltaFVarIds_1409_);
lean_inc(v_cache_1408_);
lean_inc(v_mctx_1407_);
lean_dec(v___x_1406_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1439_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v_depth_1415_; lean_object* v_levelAssignDepth_1416_; lean_object* v_lmvarCounter_1417_; lean_object* v_mvarCounter_1418_; lean_object* v_lDecls_1419_; lean_object* v_decls_1420_; lean_object* v_userNames_1421_; lean_object* v_lAssignment_1422_; lean_object* v_eAssignment_1423_; lean_object* v_dAssignment_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1438_; 
v_depth_1415_ = lean_ctor_get(v_mctx_1407_, 0);
v_levelAssignDepth_1416_ = lean_ctor_get(v_mctx_1407_, 1);
v_lmvarCounter_1417_ = lean_ctor_get(v_mctx_1407_, 2);
v_mvarCounter_1418_ = lean_ctor_get(v_mctx_1407_, 3);
v_lDecls_1419_ = lean_ctor_get(v_mctx_1407_, 4);
v_decls_1420_ = lean_ctor_get(v_mctx_1407_, 5);
v_userNames_1421_ = lean_ctor_get(v_mctx_1407_, 6);
v_lAssignment_1422_ = lean_ctor_get(v_mctx_1407_, 7);
v_eAssignment_1423_ = lean_ctor_get(v_mctx_1407_, 8);
v_dAssignment_1424_ = lean_ctor_get(v_mctx_1407_, 9);
v_isSharedCheck_1438_ = !lean_is_exclusive(v_mctx_1407_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1426_ = v_mctx_1407_;
v_isShared_1427_ = v_isSharedCheck_1438_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_dAssignment_1424_);
lean_inc(v_eAssignment_1423_);
lean_inc(v_lAssignment_1422_);
lean_inc(v_userNames_1421_);
lean_inc(v_decls_1420_);
lean_inc(v_lDecls_1419_);
lean_inc(v_mvarCounter_1418_);
lean_inc(v_lmvarCounter_1417_);
lean_inc(v_levelAssignDepth_1416_);
lean_inc(v_depth_1415_);
lean_dec(v_mctx_1407_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1438_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1428_; lean_object* v___x_1430_; 
v___x_1428_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4___redArg(v_eAssignment_1423_, v_mvarId_1402_, v_val_1403_);
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 8, v___x_1428_);
v___x_1430_ = v___x_1426_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_depth_1415_);
lean_ctor_set(v_reuseFailAlloc_1437_, 1, v_levelAssignDepth_1416_);
lean_ctor_set(v_reuseFailAlloc_1437_, 2, v_lmvarCounter_1417_);
lean_ctor_set(v_reuseFailAlloc_1437_, 3, v_mvarCounter_1418_);
lean_ctor_set(v_reuseFailAlloc_1437_, 4, v_lDecls_1419_);
lean_ctor_set(v_reuseFailAlloc_1437_, 5, v_decls_1420_);
lean_ctor_set(v_reuseFailAlloc_1437_, 6, v_userNames_1421_);
lean_ctor_set(v_reuseFailAlloc_1437_, 7, v_lAssignment_1422_);
lean_ctor_set(v_reuseFailAlloc_1437_, 8, v___x_1428_);
lean_ctor_set(v_reuseFailAlloc_1437_, 9, v_dAssignment_1424_);
v___x_1430_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
lean_object* v___x_1432_; 
if (v_isShared_1414_ == 0)
{
lean_ctor_set(v___x_1413_, 0, v___x_1430_);
v___x_1432_ = v___x_1413_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v___x_1430_);
lean_ctor_set(v_reuseFailAlloc_1436_, 1, v_cache_1408_);
lean_ctor_set(v_reuseFailAlloc_1436_, 2, v_zetaDeltaFVarIds_1409_);
lean_ctor_set(v_reuseFailAlloc_1436_, 3, v_postponed_1410_);
lean_ctor_set(v_reuseFailAlloc_1436_, 4, v_diag_1411_);
v___x_1432_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1433_ = lean_st_ref_set(v___y_1404_, v___x_1432_);
v___x_1434_ = lean_box(0);
v___x_1435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1434_);
return v___x_1435_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___redArg___boxed(lean_object* v_mvarId_1440_, lean_object* v_val_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___redArg(v_mvarId_1440_, v_val_1441_, v___y_1442_);
lean_dec(v___y_1442_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___redArg(lean_object* v_a_1445_, lean_object* v_as_1446_, size_t v_sz_1447_, size_t v_i_1448_, lean_object* v_b_1449_){
_start:
{
uint8_t v___x_1451_; 
v___x_1451_ = lean_usize_dec_lt(v_i_1448_, v_sz_1447_);
if (v___x_1451_ == 0)
{
lean_object* v___x_1452_; 
v___x_1452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1452_, 0, v_b_1449_);
return v___x_1452_;
}
else
{
lean_object* v_snd_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1471_; 
v_snd_1453_ = lean_ctor_get(v_b_1449_, 1);
v_isSharedCheck_1471_ = !lean_is_exclusive(v_b_1449_);
if (v_isSharedCheck_1471_ == 0)
{
lean_object* v_unused_1472_; 
v_unused_1472_ = lean_ctor_get(v_b_1449_, 0);
lean_dec(v_unused_1472_);
v___x_1455_ = v_b_1449_;
v_isShared_1456_ = v_isSharedCheck_1471_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_snd_1453_);
lean_dec(v_b_1449_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1471_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1457_; lean_object* v_a_1459_; lean_object* v_a_1466_; 
v___x_1457_ = lean_box(0);
v_a_1466_ = lean_array_uget_borrowed(v_as_1446_, v_i_1448_);
if (lean_obj_tag(v_a_1466_) == 0)
{
v_a_1459_ = v_snd_1453_;
goto v___jp_1458_;
}
else
{
lean_object* v_val_1467_; lean_object* v___x_1468_; uint8_t v___x_1469_; 
v_val_1467_ = lean_ctor_get(v_a_1466_, 0);
v___x_1468_ = l_Lean_LocalDecl_fvarId(v_val_1467_);
v___x_1469_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_1468_, v_a_1445_);
if (v___x_1469_ == 0)
{
lean_object* v___x_1470_; 
v___x_1470_ = lean_local_ctx_erase(v_snd_1453_, v___x_1468_);
v_a_1459_ = v___x_1470_;
goto v___jp_1458_;
}
else
{
lean_dec(v___x_1468_);
v_a_1459_ = v_snd_1453_;
goto v___jp_1458_;
}
}
v___jp_1458_:
{
lean_object* v___x_1461_; 
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 1, v_a_1459_);
lean_ctor_set(v___x_1455_, 0, v___x_1457_);
v___x_1461_ = v___x_1455_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1457_);
lean_ctor_set(v_reuseFailAlloc_1465_, 1, v_a_1459_);
v___x_1461_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
size_t v___x_1462_; size_t v___x_1463_; 
v___x_1462_ = ((size_t)1ULL);
v___x_1463_ = lean_usize_add(v_i_1448_, v___x_1462_);
v_i_1448_ = v___x_1463_;
v_b_1449_ = v___x_1461_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___redArg___boxed(lean_object* v_a_1473_, lean_object* v_as_1474_, lean_object* v_sz_1475_, lean_object* v_i_1476_, lean_object* v_b_1477_, lean_object* v___y_1478_){
_start:
{
size_t v_sz_boxed_1479_; size_t v_i_boxed_1480_; lean_object* v_res_1481_; 
v_sz_boxed_1479_ = lean_unbox_usize(v_sz_1475_);
lean_dec(v_sz_1475_);
v_i_boxed_1480_ = lean_unbox_usize(v_i_1476_);
lean_dec(v_i_1476_);
v_res_1481_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___redArg(v_a_1473_, v_as_1474_, v_sz_boxed_1479_, v_i_boxed_1480_, v_b_1477_);
lean_dec_ref(v_as_1474_);
lean_dec(v_a_1473_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4(lean_object* v_a_1482_, lean_object* v_as_1483_, size_t v_sz_1484_, size_t v_i_1485_, lean_object* v_b_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
uint8_t v___x_1492_; 
v___x_1492_ = lean_usize_dec_lt(v_i_1485_, v_sz_1484_);
if (v___x_1492_ == 0)
{
lean_object* v___x_1493_; 
v___x_1493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1493_, 0, v_b_1486_);
return v___x_1493_;
}
else
{
lean_object* v_snd_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1512_; 
v_snd_1494_ = lean_ctor_get(v_b_1486_, 1);
v_isSharedCheck_1512_ = !lean_is_exclusive(v_b_1486_);
if (v_isSharedCheck_1512_ == 0)
{
lean_object* v_unused_1513_; 
v_unused_1513_ = lean_ctor_get(v_b_1486_, 0);
lean_dec(v_unused_1513_);
v___x_1496_ = v_b_1486_;
v_isShared_1497_ = v_isSharedCheck_1512_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_snd_1494_);
lean_dec(v_b_1486_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1512_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1498_; lean_object* v_a_1500_; lean_object* v_a_1507_; 
v___x_1498_ = lean_box(0);
v_a_1507_ = lean_array_uget_borrowed(v_as_1483_, v_i_1485_);
if (lean_obj_tag(v_a_1507_) == 0)
{
v_a_1500_ = v_snd_1494_;
goto v___jp_1499_;
}
else
{
lean_object* v_val_1508_; lean_object* v___x_1509_; uint8_t v___x_1510_; 
v_val_1508_ = lean_ctor_get(v_a_1507_, 0);
v___x_1509_ = l_Lean_LocalDecl_fvarId(v_val_1508_);
v___x_1510_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_1509_, v_a_1482_);
if (v___x_1510_ == 0)
{
lean_object* v___x_1511_; 
v___x_1511_ = lean_local_ctx_erase(v_snd_1494_, v___x_1509_);
v_a_1500_ = v___x_1511_;
goto v___jp_1499_;
}
else
{
lean_dec(v___x_1509_);
v_a_1500_ = v_snd_1494_;
goto v___jp_1499_;
}
}
v___jp_1499_:
{
lean_object* v___x_1502_; 
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 1, v_a_1500_);
lean_ctor_set(v___x_1496_, 0, v___x_1498_);
v___x_1502_ = v___x_1496_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1498_);
lean_ctor_set(v_reuseFailAlloc_1506_, 1, v_a_1500_);
v___x_1502_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
size_t v___x_1503_; size_t v___x_1504_; lean_object* v___x_1505_; 
v___x_1503_ = ((size_t)1ULL);
v___x_1504_ = lean_usize_add(v_i_1485_, v___x_1503_);
v___x_1505_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___redArg(v_a_1482_, v_as_1483_, v_sz_1484_, v___x_1504_, v___x_1502_);
return v___x_1505_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4___boxed(lean_object* v_a_1514_, lean_object* v_as_1515_, lean_object* v_sz_1516_, lean_object* v_i_1517_, lean_object* v_b_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_){
_start:
{
size_t v_sz_boxed_1524_; size_t v_i_boxed_1525_; lean_object* v_res_1526_; 
v_sz_boxed_1524_ = lean_unbox_usize(v_sz_1516_);
lean_dec(v_sz_1516_);
v_i_boxed_1525_ = lean_unbox_usize(v_i_1517_);
lean_dec(v_i_1517_);
v_res_1526_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4(v_a_1514_, v_as_1515_, v_sz_boxed_1524_, v_i_boxed_1525_, v_b_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec_ref(v_as_1515_);
lean_dec(v_a_1514_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0(lean_object* v_init_1527_, lean_object* v_a_1528_, lean_object* v_n_1529_, lean_object* v_b_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
if (lean_obj_tag(v_n_1529_) == 0)
{
lean_object* v_cs_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; size_t v_sz_1539_; size_t v___x_1540_; lean_object* v___x_1541_; 
v_cs_1536_ = lean_ctor_get(v_n_1529_, 0);
v___x_1537_ = lean_box(0);
v___x_1538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1537_);
lean_ctor_set(v___x_1538_, 1, v_b_1530_);
v_sz_1539_ = lean_array_size(v_cs_1536_);
v___x_1540_ = ((size_t)0ULL);
v___x_1541_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__3(v_init_1527_, v_a_1528_, v_cs_1536_, v_sz_1539_, v___x_1540_, v___x_1538_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1556_; 
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1544_ = v___x_1541_;
v_isShared_1545_ = v_isSharedCheck_1556_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v___x_1541_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1556_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v_fst_1546_; 
v_fst_1546_ = lean_ctor_get(v_a_1542_, 0);
if (lean_obj_tag(v_fst_1546_) == 0)
{
lean_object* v_snd_1547_; lean_object* v___x_1548_; lean_object* v___x_1550_; 
v_snd_1547_ = lean_ctor_get(v_a_1542_, 1);
lean_inc(v_snd_1547_);
lean_dec(v_a_1542_);
v___x_1548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1548_, 0, v_snd_1547_);
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 0, v___x_1548_);
v___x_1550_ = v___x_1544_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v___x_1548_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
else
{
lean_object* v_val_1552_; lean_object* v___x_1554_; 
lean_inc_ref(v_fst_1546_);
lean_dec(v_a_1542_);
v_val_1552_ = lean_ctor_get(v_fst_1546_, 0);
lean_inc(v_val_1552_);
lean_dec_ref_known(v_fst_1546_, 1);
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 0, v_val_1552_);
v___x_1554_ = v___x_1544_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_val_1552_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
}
else
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
v_a_1557_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1559_ = v___x_1541_;
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1541_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1557_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
}
else
{
lean_object* v_vs_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; size_t v_sz_1568_; size_t v___x_1569_; lean_object* v___x_1570_; 
v_vs_1565_ = lean_ctor_get(v_n_1529_, 0);
v___x_1566_ = lean_box(0);
v___x_1567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1566_);
lean_ctor_set(v___x_1567_, 1, v_b_1530_);
v_sz_1568_ = lean_array_size(v_vs_1565_);
v___x_1569_ = ((size_t)0ULL);
v___x_1570_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4(v_a_1528_, v_vs_1565_, v_sz_1568_, v___x_1569_, v___x_1567_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1585_; 
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1573_ = v___x_1570_;
v_isShared_1574_ = v_isSharedCheck_1585_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1570_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1585_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v_fst_1575_; 
v_fst_1575_ = lean_ctor_get(v_a_1571_, 0);
if (lean_obj_tag(v_fst_1575_) == 0)
{
lean_object* v_snd_1576_; lean_object* v___x_1577_; lean_object* v___x_1579_; 
v_snd_1576_ = lean_ctor_get(v_a_1571_, 1);
lean_inc(v_snd_1576_);
lean_dec(v_a_1571_);
v___x_1577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1577_, 0, v_snd_1576_);
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 0, v___x_1577_);
v___x_1579_ = v___x_1573_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1577_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
else
{
lean_object* v_val_1581_; lean_object* v___x_1583_; 
lean_inc_ref(v_fst_1575_);
lean_dec(v_a_1571_);
v_val_1581_ = lean_ctor_get(v_fst_1575_, 0);
lean_inc(v_val_1581_);
lean_dec_ref_known(v_fst_1575_, 1);
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 0, v_val_1581_);
v___x_1583_ = v___x_1573_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_val_1581_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
else
{
lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1593_; 
v_a_1586_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1588_ = v___x_1570_;
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1570_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1591_; 
if (v_isShared_1589_ == 0)
{
v___x_1591_ = v___x_1588_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_a_1586_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__3(lean_object* v_init_1594_, lean_object* v_a_1595_, lean_object* v_as_1596_, size_t v_sz_1597_, size_t v_i_1598_, lean_object* v_b_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_){
_start:
{
uint8_t v___x_1605_; 
v___x_1605_ = lean_usize_dec_lt(v_i_1598_, v_sz_1597_);
if (v___x_1605_ == 0)
{
lean_object* v___x_1606_; 
v___x_1606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1606_, 0, v_b_1599_);
return v___x_1606_;
}
else
{
lean_object* v_snd_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1641_; 
v_snd_1607_ = lean_ctor_get(v_b_1599_, 1);
v_isSharedCheck_1641_ = !lean_is_exclusive(v_b_1599_);
if (v_isSharedCheck_1641_ == 0)
{
lean_object* v_unused_1642_; 
v_unused_1642_ = lean_ctor_get(v_b_1599_, 0);
lean_dec(v_unused_1642_);
v___x_1609_ = v_b_1599_;
v_isShared_1610_ = v_isSharedCheck_1641_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_snd_1607_);
lean_dec(v_b_1599_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1641_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v_a_1611_; lean_object* v___x_1612_; 
v_a_1611_ = lean_array_uget_borrowed(v_as_1596_, v_i_1598_);
lean_inc(v_snd_1607_);
v___x_1612_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0(v_init_1594_, v_a_1595_, v_a_1611_, v_snd_1607_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
if (lean_obj_tag(v___x_1612_) == 0)
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1632_; 
v_a_1613_ = lean_ctor_get(v___x_1612_, 0);
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1615_ = v___x_1612_;
v_isShared_1616_ = v_isSharedCheck_1632_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1612_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1632_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
if (lean_obj_tag(v_a_1613_) == 0)
{
lean_object* v___x_1617_; lean_object* v___x_1619_; 
v___x_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1617_, 0, v_a_1613_);
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 0, v___x_1617_);
v___x_1619_ = v___x_1609_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v___x_1617_);
lean_ctor_set(v_reuseFailAlloc_1623_, 1, v_snd_1607_);
v___x_1619_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
lean_object* v___x_1621_; 
if (v_isShared_1616_ == 0)
{
lean_ctor_set(v___x_1615_, 0, v___x_1619_);
v___x_1621_ = v___x_1615_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v___x_1619_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
else
{
lean_object* v_a_1624_; lean_object* v___x_1625_; lean_object* v___x_1627_; 
lean_del_object(v___x_1615_);
lean_dec(v_snd_1607_);
v_a_1624_ = lean_ctor_get(v_a_1613_, 0);
lean_inc(v_a_1624_);
lean_dec_ref_known(v_a_1613_, 1);
v___x_1625_ = lean_box(0);
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 1, v_a_1624_);
lean_ctor_set(v___x_1609_, 0, v___x_1625_);
v___x_1627_ = v___x_1609_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v___x_1625_);
lean_ctor_set(v_reuseFailAlloc_1631_, 1, v_a_1624_);
v___x_1627_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
size_t v___x_1628_; size_t v___x_1629_; 
v___x_1628_ = ((size_t)1ULL);
v___x_1629_ = lean_usize_add(v_i_1598_, v___x_1628_);
v_i_1598_ = v___x_1629_;
v_b_1599_ = v___x_1627_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1640_; 
lean_del_object(v___x_1609_);
lean_dec(v_snd_1607_);
v_a_1633_ = lean_ctor_get(v___x_1612_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1635_ = v___x_1612_;
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1612_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1638_; 
if (v_isShared_1636_ == 0)
{
v___x_1638_ = v___x_1635_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_a_1633_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__3___boxed(lean_object* v_init_1643_, lean_object* v_a_1644_, lean_object* v_as_1645_, lean_object* v_sz_1646_, lean_object* v_i_1647_, lean_object* v_b_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_){
_start:
{
size_t v_sz_boxed_1654_; size_t v_i_boxed_1655_; lean_object* v_res_1656_; 
v_sz_boxed_1654_ = lean_unbox_usize(v_sz_1646_);
lean_dec(v_sz_1646_);
v_i_boxed_1655_ = lean_unbox_usize(v_i_1647_);
lean_dec(v_i_1647_);
v_res_1656_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__3(v_init_1643_, v_a_1644_, v_as_1645_, v_sz_boxed_1654_, v_i_boxed_1655_, v_b_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec(v___y_1650_);
lean_dec_ref(v___y_1649_);
lean_dec_ref(v_as_1645_);
lean_dec(v_a_1644_);
lean_dec_ref(v_init_1643_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0___boxed(lean_object* v_init_1657_, lean_object* v_a_1658_, lean_object* v_n_1659_, lean_object* v_b_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0(v_init_1657_, v_a_1658_, v_n_1659_, v_b_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
lean_dec_ref(v_n_1659_);
lean_dec(v_a_1658_);
lean_dec_ref(v_init_1657_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___redArg(lean_object* v_a_1667_, lean_object* v_as_1668_, size_t v_sz_1669_, size_t v_i_1670_, lean_object* v_b_1671_){
_start:
{
uint8_t v___x_1673_; 
v___x_1673_ = lean_usize_dec_lt(v_i_1670_, v_sz_1669_);
if (v___x_1673_ == 0)
{
lean_object* v___x_1674_; 
v___x_1674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1674_, 0, v_b_1671_);
return v___x_1674_;
}
else
{
lean_object* v_snd_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1693_; 
v_snd_1675_ = lean_ctor_get(v_b_1671_, 1);
v_isSharedCheck_1693_ = !lean_is_exclusive(v_b_1671_);
if (v_isSharedCheck_1693_ == 0)
{
lean_object* v_unused_1694_; 
v_unused_1694_ = lean_ctor_get(v_b_1671_, 0);
lean_dec(v_unused_1694_);
v___x_1677_ = v_b_1671_;
v_isShared_1678_ = v_isSharedCheck_1693_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_snd_1675_);
lean_dec(v_b_1671_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1693_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1679_; lean_object* v_a_1681_; lean_object* v_a_1688_; 
v___x_1679_ = lean_box(0);
v_a_1688_ = lean_array_uget_borrowed(v_as_1668_, v_i_1670_);
if (lean_obj_tag(v_a_1688_) == 0)
{
v_a_1681_ = v_snd_1675_;
goto v___jp_1680_;
}
else
{
lean_object* v_val_1689_; lean_object* v___x_1690_; uint8_t v___x_1691_; 
v_val_1689_ = lean_ctor_get(v_a_1688_, 0);
v___x_1690_ = l_Lean_LocalDecl_fvarId(v_val_1689_);
v___x_1691_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_1690_, v_a_1667_);
if (v___x_1691_ == 0)
{
lean_object* v___x_1692_; 
v___x_1692_ = lean_local_ctx_erase(v_snd_1675_, v___x_1690_);
v_a_1681_ = v___x_1692_;
goto v___jp_1680_;
}
else
{
lean_dec(v___x_1690_);
v_a_1681_ = v_snd_1675_;
goto v___jp_1680_;
}
}
v___jp_1680_:
{
lean_object* v___x_1683_; 
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 1, v_a_1681_);
lean_ctor_set(v___x_1677_, 0, v___x_1679_);
v___x_1683_ = v___x_1677_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1679_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v_a_1681_);
v___x_1683_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
size_t v___x_1684_; size_t v___x_1685_; 
v___x_1684_ = ((size_t)1ULL);
v___x_1685_ = lean_usize_add(v_i_1670_, v___x_1684_);
v_i_1670_ = v___x_1685_;
v_b_1671_ = v___x_1683_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___redArg___boxed(lean_object* v_a_1695_, lean_object* v_as_1696_, lean_object* v_sz_1697_, lean_object* v_i_1698_, lean_object* v_b_1699_, lean_object* v___y_1700_){
_start:
{
size_t v_sz_boxed_1701_; size_t v_i_boxed_1702_; lean_object* v_res_1703_; 
v_sz_boxed_1701_ = lean_unbox_usize(v_sz_1697_);
lean_dec(v_sz_1697_);
v_i_boxed_1702_ = lean_unbox_usize(v_i_1698_);
lean_dec(v_i_1698_);
v_res_1703_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___redArg(v_a_1695_, v_as_1696_, v_sz_boxed_1701_, v_i_boxed_1702_, v_b_1699_);
lean_dec_ref(v_as_1696_);
lean_dec(v_a_1695_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1(lean_object* v_a_1704_, lean_object* v_as_1705_, size_t v_sz_1706_, size_t v_i_1707_, lean_object* v_b_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
uint8_t v___x_1714_; 
v___x_1714_ = lean_usize_dec_lt(v_i_1707_, v_sz_1706_);
if (v___x_1714_ == 0)
{
lean_object* v___x_1715_; 
v___x_1715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1715_, 0, v_b_1708_);
return v___x_1715_;
}
else
{
lean_object* v_snd_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1734_; 
v_snd_1716_ = lean_ctor_get(v_b_1708_, 1);
v_isSharedCheck_1734_ = !lean_is_exclusive(v_b_1708_);
if (v_isSharedCheck_1734_ == 0)
{
lean_object* v_unused_1735_; 
v_unused_1735_ = lean_ctor_get(v_b_1708_, 0);
lean_dec(v_unused_1735_);
v___x_1718_ = v_b_1708_;
v_isShared_1719_ = v_isSharedCheck_1734_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_snd_1716_);
lean_dec(v_b_1708_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1734_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1720_; lean_object* v_a_1722_; lean_object* v_a_1729_; 
v___x_1720_ = lean_box(0);
v_a_1729_ = lean_array_uget_borrowed(v_as_1705_, v_i_1707_);
if (lean_obj_tag(v_a_1729_) == 0)
{
v_a_1722_ = v_snd_1716_;
goto v___jp_1721_;
}
else
{
lean_object* v_val_1730_; lean_object* v___x_1731_; uint8_t v___x_1732_; 
v_val_1730_ = lean_ctor_get(v_a_1729_, 0);
v___x_1731_ = l_Lean_LocalDecl_fvarId(v_val_1730_);
v___x_1732_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_1731_, v_a_1704_);
if (v___x_1732_ == 0)
{
lean_object* v___x_1733_; 
v___x_1733_ = lean_local_ctx_erase(v_snd_1716_, v___x_1731_);
v_a_1722_ = v___x_1733_;
goto v___jp_1721_;
}
else
{
lean_dec(v___x_1731_);
v_a_1722_ = v_snd_1716_;
goto v___jp_1721_;
}
}
v___jp_1721_:
{
lean_object* v___x_1724_; 
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 1, v_a_1722_);
lean_ctor_set(v___x_1718_, 0, v___x_1720_);
v___x_1724_ = v___x_1718_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1720_);
lean_ctor_set(v_reuseFailAlloc_1728_, 1, v_a_1722_);
v___x_1724_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
size_t v___x_1725_; size_t v___x_1726_; lean_object* v___x_1727_; 
v___x_1725_ = ((size_t)1ULL);
v___x_1726_ = lean_usize_add(v_i_1707_, v___x_1725_);
v___x_1727_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___redArg(v_a_1704_, v_as_1705_, v_sz_1706_, v___x_1726_, v___x_1724_);
return v___x_1727_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1___boxed(lean_object* v_a_1736_, lean_object* v_as_1737_, lean_object* v_sz_1738_, lean_object* v_i_1739_, lean_object* v_b_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
size_t v_sz_boxed_1746_; size_t v_i_boxed_1747_; lean_object* v_res_1748_; 
v_sz_boxed_1746_ = lean_unbox_usize(v_sz_1738_);
lean_dec(v_sz_1738_);
v_i_boxed_1747_ = lean_unbox_usize(v_i_1739_);
lean_dec(v_i_1739_);
v_res_1748_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1(v_a_1736_, v_as_1737_, v_sz_boxed_1746_, v_i_boxed_1747_, v_b_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec_ref(v_as_1737_);
lean_dec(v_a_1736_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0(lean_object* v_a_1749_, lean_object* v_t_1750_, lean_object* v_init_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
lean_object* v_root_1757_; lean_object* v_tail_1758_; lean_object* v___x_1759_; 
v_root_1757_ = lean_ctor_get(v_t_1750_, 0);
v_tail_1758_ = lean_ctor_get(v_t_1750_, 1);
lean_inc_ref(v_init_1751_);
v___x_1759_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0(v_init_1751_, v_a_1749_, v_root_1757_, v_init_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_);
lean_dec_ref(v_init_1751_);
if (lean_obj_tag(v___x_1759_) == 0)
{
lean_object* v_a_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1796_; 
v_a_1760_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1762_ = v___x_1759_;
v_isShared_1763_ = v_isSharedCheck_1796_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_a_1760_);
lean_dec(v___x_1759_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1796_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
if (lean_obj_tag(v_a_1760_) == 0)
{
lean_object* v_a_1764_; lean_object* v___x_1766_; 
v_a_1764_ = lean_ctor_get(v_a_1760_, 0);
lean_inc(v_a_1764_);
lean_dec_ref_known(v_a_1760_, 1);
if (v_isShared_1763_ == 0)
{
lean_ctor_set(v___x_1762_, 0, v_a_1764_);
v___x_1766_ = v___x_1762_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1764_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
else
{
lean_object* v_a_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; size_t v_sz_1771_; size_t v___x_1772_; lean_object* v___x_1773_; 
lean_del_object(v___x_1762_);
v_a_1768_ = lean_ctor_get(v_a_1760_, 0);
lean_inc(v_a_1768_);
lean_dec_ref_known(v_a_1760_, 1);
v___x_1769_ = lean_box(0);
v___x_1770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1769_);
lean_ctor_set(v___x_1770_, 1, v_a_1768_);
v_sz_1771_ = lean_array_size(v_tail_1758_);
v___x_1772_ = ((size_t)0ULL);
v___x_1773_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1(v_a_1749_, v_tail_1758_, v_sz_1771_, v___x_1772_, v___x_1770_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_a_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1787_; 
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1776_ = v___x_1773_;
v_isShared_1777_ = v_isSharedCheck_1787_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_a_1774_);
lean_dec(v___x_1773_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1787_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v_fst_1778_; 
v_fst_1778_ = lean_ctor_get(v_a_1774_, 0);
if (lean_obj_tag(v_fst_1778_) == 0)
{
lean_object* v_snd_1779_; lean_object* v___x_1781_; 
v_snd_1779_ = lean_ctor_get(v_a_1774_, 1);
lean_inc(v_snd_1779_);
lean_dec(v_a_1774_);
if (v_isShared_1777_ == 0)
{
lean_ctor_set(v___x_1776_, 0, v_snd_1779_);
v___x_1781_ = v___x_1776_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_snd_1779_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
else
{
lean_object* v_val_1783_; lean_object* v___x_1785_; 
lean_inc_ref(v_fst_1778_);
lean_dec(v_a_1774_);
v_val_1783_ = lean_ctor_get(v_fst_1778_, 0);
lean_inc(v_val_1783_);
lean_dec_ref_known(v_fst_1778_, 1);
if (v_isShared_1777_ == 0)
{
lean_ctor_set(v___x_1776_, 0, v_val_1783_);
v___x_1785_ = v___x_1776_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_val_1783_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
}
else
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1795_; 
v_a_1788_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1790_ = v___x_1773_;
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1773_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1793_; 
if (v_isShared_1791_ == 0)
{
v___x_1793_ = v___x_1790_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_a_1788_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
}
}
}
else
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1804_; 
v_a_1797_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1799_ = v___x_1759_;
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1759_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1802_; 
if (v_isShared_1800_ == 0)
{
v___x_1802_ = v___x_1799_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_a_1797_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0___boxed(lean_object* v_a_1805_, lean_object* v_t_1806_, lean_object* v_init_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0(v_a_1805_, v_t_1806_, v_init_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec_ref(v_t_1806_);
lean_dec(v_a_1805_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___lam__0(lean_object* v_mvarId_1816_, lean_object* v___x_1817_, lean_object* v___x_1818_, lean_object* v_toPreserve_1819_, uint8_t v_indirectProps_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
lean_object* v___x_1826_; 
lean_inc(v_mvarId_1816_);
v___x_1826_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1816_, v___x_1817_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
if (lean_obj_tag(v___x_1826_) == 0)
{
uint8_t v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
lean_dec_ref_known(v___x_1826_, 1);
v___x_1827_ = 0;
v___x_1828_ = lean_box(v___x_1827_);
v___x_1829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1828_);
lean_ctor_set(v___x_1829_, 1, v___x_1818_);
v___x_1830_ = lean_st_mk_ref(v___x_1829_);
lean_inc(v_mvarId_1816_);
v___x_1831_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed(v_mvarId_1816_, v_toPreserve_1819_, v_indirectProps_1820_, v___x_1830_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v_a_1832_; lean_object* v___x_1833_; lean_object* v_lctx_1834_; lean_object* v_localInstances_1835_; lean_object* v_decls_1836_; lean_object* v___x_1837_; 
v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
lean_inc(v_a_1832_);
lean_dec_ref_known(v___x_1831_, 1);
v___x_1833_ = lean_st_ref_get(v___x_1830_);
lean_dec(v___x_1830_);
lean_dec(v___x_1833_);
v_lctx_1834_ = lean_ctor_get(v___y_1821_, 2);
v_localInstances_1835_ = lean_ctor_get(v___y_1821_, 3);
v_decls_1836_ = lean_ctor_get(v_lctx_1834_, 1);
lean_inc_ref(v_lctx_1834_);
v___x_1837_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0(v_a_1832_, v_decls_1836_, v_lctx_1834_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v_a_1838_; lean_object* v___x_1839_; lean_object* v___y_1841_; lean_object* v___x_1885_; lean_object* v___x_1886_; uint8_t v___x_1887_; 
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
lean_inc(v_a_1838_);
lean_dec_ref_known(v___x_1837_, 1);
v___x_1839_ = lean_unsigned_to_nat(0u);
v___x_1885_ = lean_array_get_size(v_localInstances_1835_);
v___x_1886_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___lam__0___closed__0));
v___x_1887_ = lean_nat_dec_lt(v___x_1839_, v___x_1885_);
if (v___x_1887_ == 0)
{
lean_dec(v_a_1832_);
v___y_1841_ = v___x_1886_;
goto v___jp_1840_;
}
else
{
uint8_t v___x_1888_; 
v___x_1888_ = lean_nat_dec_le(v___x_1885_, v___x_1885_);
if (v___x_1888_ == 0)
{
if (v___x_1887_ == 0)
{
lean_dec(v_a_1832_);
v___y_1841_ = v___x_1886_;
goto v___jp_1840_;
}
else
{
size_t v___x_1889_; size_t v___x_1890_; lean_object* v___x_1891_; 
v___x_1889_ = ((size_t)0ULL);
v___x_1890_ = lean_usize_of_nat(v___x_1885_);
v___x_1891_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__3(v_a_1832_, v_localInstances_1835_, v___x_1889_, v___x_1890_, v___x_1886_);
lean_dec(v_a_1832_);
v___y_1841_ = v___x_1891_;
goto v___jp_1840_;
}
}
else
{
size_t v___x_1892_; size_t v___x_1893_; lean_object* v___x_1894_; 
v___x_1892_ = ((size_t)0ULL);
v___x_1893_ = lean_usize_of_nat(v___x_1885_);
v___x_1894_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__3(v_a_1832_, v_localInstances_1835_, v___x_1892_, v___x_1893_, v___x_1886_);
lean_dec(v_a_1832_);
v___y_1841_ = v___x_1894_;
goto v___jp_1840_;
}
}
v___jp_1840_:
{
lean_object* v___x_1842_; 
lean_inc(v_mvarId_1816_);
v___x_1842_ = l_Lean_MVarId_getType(v_mvarId_1816_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_object* v_a_1843_; lean_object* v___x_1844_; lean_object* v_a_1845_; lean_object* v___x_1846_; 
v_a_1843_ = lean_ctor_get(v___x_1842_, 0);
lean_inc(v_a_1843_);
lean_dec_ref_known(v___x_1842_, 1);
v___x_1844_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___redArg(v_a_1843_, v___y_1822_);
v_a_1845_ = lean_ctor_get(v___x_1844_, 0);
lean_inc(v_a_1845_);
lean_dec_ref(v___x_1844_);
lean_inc(v_mvarId_1816_);
v___x_1846_ = l_Lean_MVarId_getTag(v_mvarId_1816_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; uint8_t v___x_1848_; lean_object* v___x_1849_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
lean_inc(v_a_1847_);
lean_dec_ref_known(v___x_1846_, 1);
v___x_1848_ = 2;
v___x_1849_ = l_Lean_Meta_mkFreshExprMVarAt(v_a_1838_, v___y_1841_, v_a_1845_, v___x_1848_, v_a_1847_, v___x_1839_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
lean_dec_ref(v___y_1821_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v_a_1850_; lean_object* v___x_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1859_; 
v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
lean_inc_n(v_a_1850_, 2);
lean_dec_ref_known(v___x_1849_, 1);
v___x_1851_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___redArg(v_mvarId_1816_, v_a_1850_, v___y_1822_);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1859_ == 0)
{
lean_object* v_unused_1860_; 
v_unused_1860_ = lean_ctor_get(v___x_1851_, 0);
lean_dec(v_unused_1860_);
v___x_1853_ = v___x_1851_;
v_isShared_1854_ = v_isSharedCheck_1859_;
goto v_resetjp_1852_;
}
else
{
lean_dec(v___x_1851_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1859_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1855_; lean_object* v___x_1857_; 
v___x_1855_ = l_Lean_Expr_mvarId_x21(v_a_1850_);
lean_dec(v_a_1850_);
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 0, v___x_1855_);
v___x_1857_ = v___x_1853_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1855_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
else
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
lean_dec(v_mvarId_1816_);
v_a_1861_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1849_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1849_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1861_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
else
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1876_; 
lean_dec(v_a_1845_);
lean_dec_ref(v___y_1841_);
lean_dec(v_a_1838_);
lean_dec_ref(v___y_1821_);
lean_dec(v_mvarId_1816_);
v_a_1869_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1871_ = v___x_1846_;
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1846_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1872_ == 0)
{
v___x_1874_ = v___x_1871_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_a_1869_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
}
else
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
lean_dec_ref(v___y_1841_);
lean_dec(v_a_1838_);
lean_dec_ref(v___y_1821_);
lean_dec(v_mvarId_1816_);
v_a_1877_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1879_ = v___x_1842_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1842_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1877_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
}
else
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1902_; 
lean_dec(v_a_1832_);
lean_dec_ref(v___y_1821_);
lean_dec(v_mvarId_1816_);
v_a_1895_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1897_ = v___x_1837_;
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1837_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1900_; 
if (v_isShared_1898_ == 0)
{
v___x_1900_ = v___x_1897_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_a_1895_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
}
else
{
lean_object* v_a_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1910_; 
lean_dec(v___x_1830_);
lean_dec_ref(v___y_1821_);
lean_dec(v_mvarId_1816_);
v_a_1903_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1905_ = v___x_1831_;
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_a_1903_);
lean_dec(v___x_1831_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1908_; 
if (v_isShared_1906_ == 0)
{
v___x_1908_ = v___x_1905_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_a_1903_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
return v___x_1908_;
}
}
}
}
else
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1918_; 
lean_dec_ref(v___y_1821_);
lean_dec(v___x_1818_);
lean_dec(v_mvarId_1816_);
v_a_1911_ = lean_ctor_get(v___x_1826_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1913_ = v___x_1826_;
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v___x_1826_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1916_; 
if (v_isShared_1914_ == 0)
{
v___x_1916_ = v___x_1913_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1911_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___lam__0___boxed(lean_object* v_mvarId_1919_, lean_object* v___x_1920_, lean_object* v___x_1921_, lean_object* v_toPreserve_1922_, lean_object* v_indirectProps_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_){
_start:
{
uint8_t v_indirectProps_boxed_1929_; lean_object* v_res_1930_; 
v_indirectProps_boxed_1929_ = lean_unbox(v_indirectProps_1923_);
v_res_1930_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___lam__0(v_mvarId_1919_, v___x_1920_, v___x_1921_, v_toPreserve_1922_, v_indirectProps_boxed_1929_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
lean_dec(v___y_1927_);
lean_dec_ref(v___y_1926_);
lean_dec(v___y_1925_);
lean_dec_ref(v_toPreserve_1922_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(lean_object* v_mvarId_1934_, lean_object* v_toPreserve_1935_, uint8_t v_indirectProps_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_){
_start:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___f_1945_; lean_object* v___x_1946_; 
v___x_1942_ = lean_box(1);
v___x_1943_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___closed__1));
v___x_1944_ = lean_box(v_indirectProps_1936_);
lean_inc(v_mvarId_1934_);
v___f_1945_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1945_, 0, v_mvarId_1934_);
lean_closure_set(v___f_1945_, 1, v___x_1943_);
lean_closure_set(v___f_1945_, 2, v___x_1942_);
lean_closure_set(v___f_1945_, 3, v_toPreserve_1935_);
lean_closure_set(v___f_1945_, 4, v___x_1944_);
v___x_1946_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___redArg(v_mvarId_1934_, v___f_1945_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___boxed(lean_object* v_mvarId_1947_, lean_object* v_toPreserve_1948_, lean_object* v_indirectProps_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_){
_start:
{
uint8_t v_indirectProps_boxed_1955_; lean_object* v_res_1956_; 
v_indirectProps_boxed_1955_ = lean_unbox(v_indirectProps_1949_);
v_res_1956_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(v_mvarId_1947_, v_toPreserve_1948_, v_indirectProps_boxed_1955_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_);
lean_dec(v_a_1953_);
lean_dec_ref(v_a_1952_);
lean_dec(v_a_1951_);
lean_dec_ref(v_a_1950_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2(lean_object* v_mvarId_1957_, lean_object* v_val_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
lean_object* v___x_1964_; 
v___x_1964_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___redArg(v_mvarId_1957_, v_val_1958_, v___y_1960_);
return v___x_1964_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___boxed(lean_object* v_mvarId_1965_, lean_object* v_val_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2(v_mvarId_1965_, v_val_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4(lean_object* v_00_u03b2_1973_, lean_object* v_x_1974_, lean_object* v_x_1975_, lean_object* v_x_1976_){
_start:
{
lean_object* v___x_1977_; 
v___x_1977_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4___redArg(v_x_1974_, v_x_1975_, v_x_1976_);
return v___x_1977_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6(lean_object* v_a_1978_, lean_object* v_as_1979_, size_t v_sz_1980_, size_t v_i_1981_, lean_object* v_b_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
lean_object* v___x_1988_; 
v___x_1988_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___redArg(v_a_1978_, v_as_1979_, v_sz_1980_, v_i_1981_, v_b_1982_);
return v___x_1988_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___boxed(lean_object* v_a_1989_, lean_object* v_as_1990_, lean_object* v_sz_1991_, lean_object* v_i_1992_, lean_object* v_b_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
size_t v_sz_boxed_1999_; size_t v_i_boxed_2000_; lean_object* v_res_2001_; 
v_sz_boxed_1999_ = lean_unbox_usize(v_sz_1991_);
lean_dec(v_sz_1991_);
v_i_boxed_2000_ = lean_unbox_usize(v_i_1992_);
lean_dec(v_i_1992_);
v_res_2001_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6(v_a_1989_, v_as_1990_, v_sz_boxed_1999_, v_i_boxed_2000_, v_b_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
lean_dec(v___y_1995_);
lean_dec_ref(v___y_1994_);
lean_dec_ref(v_as_1990_);
lean_dec(v_a_1989_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9(lean_object* v_00_u03b2_2002_, lean_object* v_x_2003_, size_t v_x_2004_, size_t v_x_2005_, lean_object* v_x_2006_, lean_object* v_x_2007_){
_start:
{
lean_object* v___x_2008_; 
v___x_2008_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg(v_x_2003_, v_x_2004_, v_x_2005_, v_x_2006_, v_x_2007_);
return v___x_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___boxed(lean_object* v_00_u03b2_2009_, lean_object* v_x_2010_, lean_object* v_x_2011_, lean_object* v_x_2012_, lean_object* v_x_2013_, lean_object* v_x_2014_){
_start:
{
size_t v_x_8491__boxed_2015_; size_t v_x_8492__boxed_2016_; lean_object* v_res_2017_; 
v_x_8491__boxed_2015_ = lean_unbox_usize(v_x_2011_);
lean_dec(v_x_2011_);
v_x_8492__boxed_2016_ = lean_unbox_usize(v_x_2012_);
lean_dec(v_x_2012_);
v_res_2017_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9(v_00_u03b2_2009_, v_x_2010_, v_x_8491__boxed_2015_, v_x_8492__boxed_2016_, v_x_2013_, v_x_2014_);
return v_res_2017_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7(lean_object* v_a_2018_, lean_object* v_as_2019_, size_t v_sz_2020_, size_t v_i_2021_, lean_object* v_b_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_){
_start:
{
lean_object* v___x_2028_; 
v___x_2028_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___redArg(v_a_2018_, v_as_2019_, v_sz_2020_, v_i_2021_, v_b_2022_);
return v___x_2028_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___boxed(lean_object* v_a_2029_, lean_object* v_as_2030_, lean_object* v_sz_2031_, lean_object* v_i_2032_, lean_object* v_b_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_){
_start:
{
size_t v_sz_boxed_2039_; size_t v_i_boxed_2040_; lean_object* v_res_2041_; 
v_sz_boxed_2039_ = lean_unbox_usize(v_sz_2031_);
lean_dec(v_sz_2031_);
v_i_boxed_2040_ = lean_unbox_usize(v_i_2032_);
lean_dec(v_i_2032_);
v_res_2041_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7(v_a_2029_, v_as_2030_, v_sz_boxed_2039_, v_i_boxed_2040_, v_b_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
lean_dec(v___y_2035_);
lean_dec_ref(v___y_2034_);
lean_dec_ref(v_as_2030_);
lean_dec(v_a_2029_);
return v_res_2041_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12(lean_object* v_00_u03b2_2042_, lean_object* v_n_2043_, lean_object* v_k_2044_, lean_object* v_v_2045_){
_start:
{
lean_object* v___x_2046_; 
v___x_2046_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12___redArg(v_n_2043_, v_k_2044_, v_v_2045_);
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13(lean_object* v_00_u03b2_2047_, size_t v_depth_2048_, lean_object* v_keys_2049_, lean_object* v_vals_2050_, lean_object* v_heq_2051_, lean_object* v_i_2052_, lean_object* v_entries_2053_){
_start:
{
lean_object* v___x_2054_; 
v___x_2054_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___redArg(v_depth_2048_, v_keys_2049_, v_vals_2050_, v_i_2052_, v_entries_2053_);
return v___x_2054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___boxed(lean_object* v_00_u03b2_2055_, lean_object* v_depth_2056_, lean_object* v_keys_2057_, lean_object* v_vals_2058_, lean_object* v_heq_2059_, lean_object* v_i_2060_, lean_object* v_entries_2061_){
_start:
{
size_t v_depth_boxed_2062_; lean_object* v_res_2063_; 
v_depth_boxed_2062_ = lean_unbox_usize(v_depth_2056_);
lean_dec(v_depth_2056_);
v_res_2063_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13(v_00_u03b2_2055_, v_depth_boxed_2062_, v_keys_2057_, v_vals_2058_, v_heq_2059_, v_i_2060_, v_entries_2061_);
lean_dec_ref(v_vals_2058_);
lean_dec_ref(v_keys_2057_);
return v_res_2063_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12_spec__13(lean_object* v_00_u03b2_2064_, lean_object* v_x_2065_, lean_object* v_x_2066_, lean_object* v_x_2067_, lean_object* v_x_2068_){
_start:
{
lean_object* v___x_2069_; 
v___x_2069_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12_spec__13___redArg(v_x_2065_, v_x_2066_, v_x_2067_, v_x_2068_);
return v___x_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_cleanup(lean_object* v_mvarId_2070_, lean_object* v_toPreserve_2071_, uint8_t v_indirectProps_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_){
_start:
{
lean_object* v___x_2078_; 
v___x_2078_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(v_mvarId_2070_, v_toPreserve_2071_, v_indirectProps_2072_, v_a_2073_, v_a_2074_, v_a_2075_, v_a_2076_);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_cleanup___boxed(lean_object* v_mvarId_2079_, lean_object* v_toPreserve_2080_, lean_object* v_indirectProps_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_){
_start:
{
uint8_t v_indirectProps_boxed_2087_; lean_object* v_res_2088_; 
v_indirectProps_boxed_2087_ = lean_unbox(v_indirectProps_2081_);
v_res_2088_ = l_Lean_MVarId_cleanup(v_mvarId_2079_, v_toPreserve_2080_, v_indirectProps_boxed_2087_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_);
lean_dec(v_a_2085_);
lean_dec_ref(v_a_2084_);
lean_dec(v_a_2083_);
lean_dec_ref(v_a_2082_);
return v_res_2088_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CollectFVars(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Util(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Cleanup(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_CollectFVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Cleanup(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_CollectFVars(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Cleanup(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CollectFVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cleanup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Cleanup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Cleanup(builtin);
}
#ifdef __cplusplus
}
#endif
