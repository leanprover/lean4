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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_CollectFVars_State_ofFVarSet(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Expr_collectFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_LocalContext_erase(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_array_object l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__1;
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
static lean_once_cell_t l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__2(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__2___boxed(lean_object*, lean_object*);
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
v___x_35_ = lean_st_ref_put(v___y_16_, v___x_34_);
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__1(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_46_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__0));
v___x_47_ = lean_box(1);
v___x_48_ = l_Lean_CollectFVars_State_ofFVarSet(v___x_47_, v___x_46_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(lean_object* v_fvarId_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_){
_start:
{
lean_object* v___x_56_; lean_object* v_snd_57_; uint8_t v___x_58_; 
v___x_56_ = lean_st_ref_get(v_a_50_);
v_snd_57_ = lean_ctor_get(v___x_56_, 1);
lean_inc(v_snd_57_);
lean_dec(v___x_56_);
v___x_58_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v_fvarId_49_, v_snd_57_);
lean_dec(v_snd_57_);
if (v___x_58_ == 0)
{
uint8_t v___x_59_; lean_object* v___x_60_; lean_object* v_snd_61_; lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_72_; 
v___x_59_ = 1;
v___x_60_ = lean_st_ref_take(v_a_50_);
v_snd_61_ = lean_ctor_get(v___x_60_, 1);
v_isSharedCheck_72_ = !lean_is_exclusive(v___x_60_);
if (v_isSharedCheck_72_ == 0)
{
lean_object* v_unused_73_; 
v_unused_73_ = lean_ctor_get(v___x_60_, 0);
lean_dec(v_unused_73_);
v___x_63_ = v___x_60_;
v_isShared_64_ = v_isSharedCheck_72_;
goto v_resetjp_62_;
}
else
{
lean_inc(v_snd_61_);
lean_dec(v___x_60_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_72_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_68_; 
lean_inc(v_fvarId_49_);
v___x_65_ = l_Lean_FVarIdSet_insert(v_snd_61_, v_fvarId_49_);
v___x_66_ = lean_box(v___x_59_);
if (v_isShared_64_ == 0)
{
lean_ctor_set(v___x_63_, 1, v___x_65_);
lean_ctor_set(v___x_63_, 0, v___x_66_);
v___x_68_ = v___x_63_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v___x_66_);
lean_ctor_set(v_reuseFailAlloc_71_, 1, v___x_65_);
v___x_68_ = v_reuseFailAlloc_71_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = lean_st_ref_put(v_a_50_, v___x_68_);
v___x_70_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addDeps(v_fvarId_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_);
return v___x_70_;
}
}
}
else
{
lean_object* v___x_74_; lean_object* v___x_75_; 
lean_dec(v_fvarId_49_);
v___x_74_ = lean_box(0);
v___x_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
return v___x_75_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__1(lean_object* v_init_76_, lean_object* v_x_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
if (lean_obj_tag(v_x_77_) == 0)
{
lean_object* v_k_84_; lean_object* v_l_85_; lean_object* v_r_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v_k_84_ = lean_ctor_get(v_x_77_, 1);
lean_inc(v_k_84_);
v_l_85_ = lean_ctor_get(v_x_77_, 3);
lean_inc(v_l_85_);
v_r_86_ = lean_ctor_get(v_x_77_, 4);
lean_inc(v_r_86_);
lean_dec_ref_known(v_x_77_, 5);
v___x_87_ = lean_box(0);
v___x_88_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__1(v_init_76_, v_l_85_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_);
if (lean_obj_tag(v___x_88_) == 0)
{
lean_object* v___x_89_; 
lean_dec_ref_known(v___x_88_, 1);
v___x_89_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v_k_84_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_);
if (lean_obj_tag(v___x_89_) == 0)
{
lean_dec_ref_known(v___x_89_, 1);
v_init_76_ = v___x_87_;
v_x_77_ = v_r_86_;
goto _start;
}
else
{
lean_object* v_a_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_98_; 
lean_dec(v_r_86_);
v_a_91_ = lean_ctor_get(v___x_89_, 0);
v_isSharedCheck_98_ = !lean_is_exclusive(v___x_89_);
if (v_isSharedCheck_98_ == 0)
{
v___x_93_ = v___x_89_;
v_isShared_94_ = v_isSharedCheck_98_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_a_91_);
lean_dec(v___x_89_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_98_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v___x_96_; 
if (v_isShared_94_ == 0)
{
v___x_96_ = v___x_93_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v_a_91_);
v___x_96_ = v_reuseFailAlloc_97_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
return v___x_96_;
}
}
}
}
else
{
lean_dec(v_r_86_);
lean_dec(v_k_84_);
return v___x_88_;
}
}
else
{
lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_99_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_99_, 0, v_init_76_);
v___x_100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
return v___x_100_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars(lean_object* v_e_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0___redArg(v_e_101_, v_a_104_);
if (lean_obj_tag(v___x_108_) == 0)
{
lean_object* v_a_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v_a_109_ = lean_ctor_get(v___x_108_, 0);
lean_inc(v_a_109_);
lean_dec_ref_known(v___x_108_, 1);
v___x_110_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__1, &l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__1);
v___x_111_ = lean_st_mk_ref(v___x_110_);
v___x_112_ = l_Lean_Expr_collectFVars(v_a_109_, v___x_111_, v_a_103_, v_a_104_, v_a_105_, v_a_106_);
if (lean_obj_tag(v___x_112_) == 0)
{
lean_object* v___x_113_; lean_object* v_fvarSet_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
lean_dec_ref_known(v___x_112_, 1);
v___x_113_ = lean_st_ref_get(v___x_111_);
lean_dec(v___x_111_);
v_fvarSet_114_ = lean_ctor_get(v___x_113_, 1);
lean_inc(v_fvarSet_114_);
lean_dec(v___x_113_);
v___x_115_ = lean_box(0);
v___x_116_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__1(v___x_115_, v_fvarSet_114_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_);
if (lean_obj_tag(v___x_116_) == 0)
{
lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_123_; 
v_isSharedCheck_123_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_123_ == 0)
{
lean_object* v_unused_124_; 
v_unused_124_ = lean_ctor_get(v___x_116_, 0);
lean_dec(v_unused_124_);
v___x_118_ = v___x_116_;
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
else
{
lean_dec(v___x_116_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_121_; 
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 0, v___x_115_);
v___x_121_ = v___x_118_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v___x_115_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
else
{
lean_object* v_a_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_132_; 
v_a_125_ = lean_ctor_get(v___x_116_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_132_ == 0)
{
v___x_127_ = v___x_116_;
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_a_125_);
lean_dec(v___x_116_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_130_; 
if (v_isShared_128_ == 0)
{
v___x_130_ = v___x_127_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_a_125_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
}
else
{
lean_dec(v___x_111_);
return v___x_112_;
}
}
else
{
lean_object* v_a_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_140_; 
v_a_133_ = lean_ctor_get(v___x_108_, 0);
v_isSharedCheck_140_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_140_ == 0)
{
v___x_135_ = v___x_108_;
v_isShared_136_ = v_isSharedCheck_140_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_a_133_);
lean_dec(v___x_108_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_140_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_138_; 
if (v_isShared_136_ == 0)
{
v___x_138_ = v___x_135_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_a_133_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addDeps(lean_object* v_fvarId_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_141_, v_a_143_, v_a_145_, v_a_146_);
if (lean_obj_tag(v___x_148_) == 0)
{
lean_object* v_a_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v_a_149_ = lean_ctor_get(v___x_148_, 0);
lean_inc(v_a_149_);
lean_dec_ref_known(v___x_148_, 1);
v___x_150_ = l_Lean_LocalDecl_type(v_a_149_);
v___x_151_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars(v___x_150_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_);
if (lean_obj_tag(v___x_151_) == 0)
{
lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_163_; 
v_isSharedCheck_163_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_163_ == 0)
{
lean_object* v_unused_164_; 
v_unused_164_ = lean_ctor_get(v___x_151_, 0);
lean_dec(v_unused_164_);
v___x_153_ = v___x_151_;
v_isShared_154_ = v_isSharedCheck_163_;
goto v_resetjp_152_;
}
else
{
lean_dec(v___x_151_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_163_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
uint8_t v___x_155_; lean_object* v___x_156_; 
v___x_155_ = 0;
v___x_156_ = l_Lean_LocalDecl_value_x3f(v_a_149_, v___x_155_);
lean_dec(v_a_149_);
if (lean_obj_tag(v___x_156_) == 1)
{
lean_object* v_val_157_; lean_object* v___x_158_; 
lean_del_object(v___x_153_);
v_val_157_ = lean_ctor_get(v___x_156_, 0);
lean_inc(v_val_157_);
lean_dec_ref_known(v___x_156_, 1);
v___x_158_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars(v_val_157_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_);
return v___x_158_;
}
else
{
lean_object* v___x_159_; lean_object* v___x_161_; 
lean_dec(v___x_156_);
v___x_159_ = lean_box(0);
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 0, v___x_159_);
v___x_161_ = v___x_153_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v___x_159_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
}
}
else
{
lean_dec(v_a_149_);
return v___x_151_;
}
}
else
{
lean_object* v_a_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_172_; 
v_a_165_ = lean_ctor_get(v___x_148_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_148_);
if (v_isSharedCheck_172_ == 0)
{
v___x_167_ = v___x_148_;
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_a_165_);
lean_dec(v___x_148_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_170_; 
if (v_isShared_168_ == 0)
{
v___x_170_ = v___x_167_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_a_165_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addDeps___boxed(lean_object* v_fvarId_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addDeps(v_fvarId_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_);
lean_dec(v_a_178_);
lean_dec_ref(v_a_177_);
lean_dec(v_a_176_);
lean_dec_ref(v_a_175_);
lean_dec(v_a_174_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__1___boxed(lean_object* v_init_181_, lean_object* v_x_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__1(v_init_181_, v_x_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_);
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
lean_dec(v___y_183_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar___boxed(lean_object* v_fvarId_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v_fvarId_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_);
lean_dec(v_a_195_);
lean_dec_ref(v_a_194_);
lean_dec(v_a_193_);
lean_dec_ref(v_a_192_);
lean_dec(v_a_191_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___boxed(lean_object* v_e_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars(v_e_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_);
lean_dec(v_a_203_);
lean_dec_ref(v_a_202_);
lean_dec(v_a_201_);
lean_dec_ref(v_a_200_);
lean_dec(v_a_199_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0(lean_object* v_e_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0___redArg(v_e_206_, v___y_209_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0___boxed(lean_object* v_e_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0(v_e_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_);
lean_dec(v___y_219_);
lean_dec_ref(v___y_218_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
lean_dec(v___y_215_);
return v_res_221_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3(lean_object* v_00_u03b2_222_, lean_object* v_k_223_, lean_object* v_t_224_){
_start:
{
uint8_t v___x_225_; 
v___x_225_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v_k_223_, v_t_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___boxed(lean_object* v_00_u03b2_226_, lean_object* v_k_227_, lean_object* v_t_228_){
_start:
{
uint8_t v_res_229_; lean_object* v_r_230_; 
v_res_229_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3(v_00_u03b2_226_, v_k_227_, v_t_228_);
lean_dec(v_t_228_);
lean_dec(v_k_227_);
v_r_230_ = lean_box(v_res_229_);
return v_r_230_;
}
}
static lean_object* _init_l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_231_ = lean_box(0);
v___x_232_ = lean_unsigned_to_nat(16u);
v___x_233_ = lean_mk_array(v___x_232_, v___x_231_);
return v___x_233_;
}
}
static lean_object* _init_l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_234_ = lean_obj_once(&l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg___closed__0, &l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg___closed__0_once, _init_l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg___closed__0);
v___x_235_ = lean_unsigned_to_nat(0u);
v___x_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
lean_ctor_set(v___x_236_, 1, v___x_234_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(lean_object* v_e_237_, lean_object* v_pf_238_, lean_object* v_pm_239_, lean_object* v___y_240_){
_start:
{
lean_object* v___x_242_; uint8_t v_fst_244_; lean_object* v_mctx_245_; lean_object* v___y_263_; lean_object* v_mctx_268_; lean_object* v___x_269_; lean_object* v___x_270_; uint8_t v___x_271_; 
v___x_242_ = lean_st_ref_get(v___y_240_);
v_mctx_268_ = lean_ctor_get(v___x_242_, 0);
lean_inc_ref_n(v_mctx_268_, 2);
lean_dec(v___x_242_);
v___x_269_ = lean_obj_once(&l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg___closed__1, &l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg___closed__1_once, _init_l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg___closed__1);
v___x_270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
lean_ctor_set(v___x_270_, 1, v_mctx_268_);
v___x_271_ = l_Lean_Expr_hasFVar(v_e_237_);
if (v___x_271_ == 0)
{
uint8_t v___x_272_; 
v___x_272_ = l_Lean_Expr_hasMVar(v_e_237_);
if (v___x_272_ == 0)
{
lean_dec_ref_known(v___x_270_, 2);
lean_dec_ref(v_pm_239_);
lean_dec_ref(v_pf_238_);
lean_dec_ref(v_e_237_);
v_fst_244_ = v___x_272_;
v_mctx_245_ = v_mctx_268_;
goto v___jp_243_;
}
else
{
lean_object* v___x_273_; 
lean_dec_ref(v_mctx_268_);
v___x_273_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v_pf_238_, v_pm_239_, v_e_237_, v___x_270_);
v___y_263_ = v___x_273_;
goto v___jp_262_;
}
}
else
{
lean_object* v___x_274_; 
lean_dec_ref(v_mctx_268_);
v___x_274_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v_pf_238_, v_pm_239_, v_e_237_, v___x_270_);
v___y_263_ = v___x_274_;
goto v___jp_262_;
}
v___jp_243_:
{
lean_object* v___x_246_; lean_object* v_cache_247_; lean_object* v_zetaDeltaFVarIds_248_; lean_object* v_postponed_249_; lean_object* v_diag_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_260_; 
v___x_246_ = lean_st_ref_take(v___y_240_);
v_cache_247_ = lean_ctor_get(v___x_246_, 1);
v_zetaDeltaFVarIds_248_ = lean_ctor_get(v___x_246_, 2);
v_postponed_249_ = lean_ctor_get(v___x_246_, 3);
v_diag_250_ = lean_ctor_get(v___x_246_, 4);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_246_);
if (v_isSharedCheck_260_ == 0)
{
lean_object* v_unused_261_; 
v_unused_261_ = lean_ctor_get(v___x_246_, 0);
lean_dec(v_unused_261_);
v___x_252_ = v___x_246_;
v_isShared_253_ = v_isSharedCheck_260_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_diag_250_);
lean_inc(v_postponed_249_);
lean_inc(v_zetaDeltaFVarIds_248_);
lean_inc(v_cache_247_);
lean_dec(v___x_246_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_260_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_255_; 
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 0, v_mctx_245_);
v___x_255_ = v___x_252_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_mctx_245_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v_cache_247_);
lean_ctor_set(v_reuseFailAlloc_259_, 2, v_zetaDeltaFVarIds_248_);
lean_ctor_set(v_reuseFailAlloc_259_, 3, v_postponed_249_);
lean_ctor_set(v_reuseFailAlloc_259_, 4, v_diag_250_);
v___x_255_ = v_reuseFailAlloc_259_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_256_ = lean_st_ref_put(v___y_240_, v___x_255_);
v___x_257_ = lean_box(v_fst_244_);
v___x_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
return v___x_258_;
}
}
}
v___jp_262_:
{
lean_object* v_snd_264_; lean_object* v_fst_265_; lean_object* v_mctx_266_; uint8_t v___x_267_; 
v_snd_264_ = lean_ctor_get(v___y_263_, 1);
lean_inc(v_snd_264_);
v_fst_265_ = lean_ctor_get(v___y_263_, 0);
lean_inc(v_fst_265_);
lean_dec_ref(v___y_263_);
v_mctx_266_ = lean_ctor_get(v_snd_264_, 1);
lean_inc_ref(v_mctx_266_);
lean_dec(v_snd_264_);
v___x_267_ = lean_unbox(v_fst_265_);
lean_dec(v_fst_265_);
v_fst_244_ = v___x_267_;
v_mctx_245_ = v_mctx_266_;
goto v___jp_243_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg___boxed(lean_object* v_e_275_, lean_object* v_pf_276_, lean_object* v_pm_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v_e_275_, v_pf_276_, v_pm_277_, v___y_278_);
lean_dec(v___y_278_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0(lean_object* v_e_281_, lean_object* v_pf_282_, lean_object* v_pm_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v_e_281_, v_pf_282_, v_pm_283_, v___y_286_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___boxed(lean_object* v_e_291_, lean_object* v_pf_292_, lean_object* v_pm_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0(v_e_291_, v_pf_292_, v_pm_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_);
lean_dec(v___y_298_);
lean_dec_ref(v___y_297_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
lean_dec(v___y_294_);
return v_res_300_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__0(lean_object* v_snd_301_, lean_object* v___y_302_){
_start:
{
uint8_t v___x_303_; 
v___x_303_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___y_302_, v_snd_301_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__0___boxed(lean_object* v_snd_304_, lean_object* v___y_305_){
_start:
{
uint8_t v_res_306_; lean_object* v_r_307_; 
v_res_306_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__0(v_snd_304_, v___y_305_);
lean_dec(v___y_305_);
lean_dec(v_snd_304_);
v_r_307_ = lean_box(v_res_306_);
return v_r_307_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__2(uint8_t v___x_308_, lean_object* v_x_309_){
_start:
{
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__2___boxed(lean_object* v___x_310_, lean_object* v_x_311_){
_start:
{
uint8_t v___x_8979__boxed_312_; uint8_t v_res_313_; lean_object* v_r_314_; 
v___x_8979__boxed_312_ = lean_unbox(v___x_310_);
v_res_313_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__2(v___x_8979__boxed_312_, v_x_311_);
lean_dec(v_x_311_);
v_r_314_ = lean_box(v_res_313_);
return v_r_314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2_spec__5(lean_object* v_as_315_, size_t v_sz_316_, size_t v_i_317_, lean_object* v_b_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
uint8_t v___x_325_; 
v___x_325_ = lean_usize_dec_lt(v_i_317_, v_sz_316_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; 
v___x_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_326_, 0, v_b_318_);
return v___x_326_;
}
else
{
lean_object* v_snd_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_410_; 
v_snd_327_ = lean_ctor_get(v_b_318_, 1);
v_isSharedCheck_410_ = !lean_is_exclusive(v_b_318_);
if (v_isSharedCheck_410_ == 0)
{
lean_object* v_unused_411_; 
v_unused_411_ = lean_ctor_get(v_b_318_, 0);
lean_dec(v_unused_411_);
v___x_329_ = v_b_318_;
v_isShared_330_ = v_isSharedCheck_410_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_snd_327_);
lean_dec(v_b_318_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_410_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_331_; lean_object* v_a_333_; lean_object* v_a_340_; 
v___x_331_ = lean_box(0);
v_a_340_ = lean_array_uget_borrowed(v_as_315_, v_i_317_);
if (lean_obj_tag(v_a_340_) == 0)
{
v_a_333_ = v_snd_327_;
goto v___jp_332_;
}
else
{
lean_object* v_val_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v_snd_344_; lean_object* v___x_345_; uint8_t v___x_346_; 
lean_dec(v_snd_327_);
v_val_341_ = lean_ctor_get(v_a_340_, 0);
v___x_342_ = lean_box(0);
v___x_343_ = lean_st_ref_get(v___y_319_);
v_snd_344_ = lean_ctor_get(v___x_343_, 1);
lean_inc(v_snd_344_);
lean_dec(v___x_343_);
v___x_345_ = l_Lean_LocalDecl_fvarId(v_val_341_);
v___x_346_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_345_, v_snd_344_);
if (v___x_346_ == 0)
{
lean_object* v___f_347_; lean_object* v___x_348_; lean_object* v___f_349_; lean_object* v___y_351_; lean_object* v___y_352_; lean_object* v___y_353_; lean_object* v___y_354_; lean_object* v___y_355_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___f_347_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_347_, 0, v_snd_344_);
v___x_348_ = lean_box(v___x_346_);
v___f_349_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__2___boxed), 2, 1);
lean_closure_set(v___f_349_, 0, v___x_348_);
v___x_378_ = l_Lean_LocalDecl_type(v_val_341_);
lean_inc_ref(v___x_378_);
v___x_379_ = l_Lean_Meta_isProp(v___x_378_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v_a_380_; uint8_t v___x_381_; 
v_a_380_ = lean_ctor_get(v___x_379_, 0);
lean_inc(v_a_380_);
lean_dec_ref_known(v___x_379_, 1);
v___x_381_ = lean_unbox(v_a_380_);
lean_dec(v_a_380_);
if (v___x_381_ == 0)
{
lean_dec_ref(v___x_378_);
v___y_351_ = v___y_319_;
v___y_352_ = v___y_320_;
v___y_353_ = v___y_321_;
v___y_354_ = v___y_322_;
v___y_355_ = v___y_323_;
goto v___jp_350_;
}
else
{
lean_object* v___x_382_; 
lean_inc_ref(v___f_349_);
lean_inc_ref(v___f_347_);
v___x_382_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v___x_378_, v___f_347_, v___f_349_, v___y_321_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_object* v_a_383_; uint8_t v___x_384_; 
v_a_383_ = lean_ctor_get(v___x_382_, 0);
lean_inc(v_a_383_);
lean_dec_ref_known(v___x_382_, 1);
v___x_384_ = lean_unbox(v_a_383_);
lean_dec(v_a_383_);
if (v___x_384_ == 0)
{
v___y_351_ = v___y_319_;
v___y_352_ = v___y_320_;
v___y_353_ = v___y_321_;
v___y_354_ = v___y_322_;
v___y_355_ = v___y_323_;
goto v___jp_350_;
}
else
{
lean_object* v___x_385_; 
lean_inc(v___x_345_);
v___x_385_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_345_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_dec_ref_known(v___x_385_, 1);
v___y_351_ = v___y_319_;
v___y_352_ = v___y_320_;
v___y_353_ = v___y_321_;
v___y_354_ = v___y_322_;
v___y_355_ = v___y_323_;
goto v___jp_350_;
}
else
{
lean_object* v_a_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_393_; 
lean_dec_ref(v___f_349_);
lean_dec_ref(v___f_347_);
lean_dec(v___x_345_);
lean_del_object(v___x_329_);
v_a_386_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_393_ == 0)
{
v___x_388_ = v___x_385_;
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_a_386_);
lean_dec(v___x_385_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_391_; 
if (v_isShared_389_ == 0)
{
v___x_391_ = v___x_388_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_a_386_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
}
}
else
{
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_401_; 
lean_dec_ref(v___f_349_);
lean_dec_ref(v___f_347_);
lean_dec(v___x_345_);
lean_del_object(v___x_329_);
v_a_394_ = lean_ctor_get(v___x_382_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_401_ == 0)
{
v___x_396_ = v___x_382_;
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v___x_382_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_399_; 
if (v_isShared_397_ == 0)
{
v___x_399_ = v___x_396_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_a_394_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
}
}
else
{
lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_409_; 
lean_dec_ref(v___x_378_);
lean_dec_ref(v___f_349_);
lean_dec_ref(v___f_347_);
lean_dec(v___x_345_);
lean_del_object(v___x_329_);
v_a_402_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_409_ == 0)
{
v___x_404_ = v___x_379_;
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_379_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_407_; 
if (v_isShared_405_ == 0)
{
v___x_407_ = v___x_404_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_a_402_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
v___jp_350_:
{
lean_object* v___x_356_; 
v___x_356_ = l_Lean_LocalDecl_value_x3f(v_val_341_, v___x_346_);
if (lean_obj_tag(v___x_356_) == 1)
{
lean_object* v_val_357_; lean_object* v___x_358_; 
v_val_357_ = lean_ctor_get(v___x_356_, 0);
lean_inc(v_val_357_);
lean_dec_ref_known(v___x_356_, 1);
v___x_358_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v_val_357_, v___f_347_, v___f_349_, v___y_353_);
if (lean_obj_tag(v___x_358_) == 0)
{
lean_object* v_a_359_; uint8_t v___x_360_; 
v_a_359_ = lean_ctor_get(v___x_358_, 0);
lean_inc(v_a_359_);
lean_dec_ref_known(v___x_358_, 1);
v___x_360_ = lean_unbox(v_a_359_);
lean_dec(v_a_359_);
if (v___x_360_ == 0)
{
lean_dec(v___x_345_);
v_a_333_ = v___x_342_;
goto v___jp_332_;
}
else
{
lean_object* v___x_361_; 
v___x_361_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_345_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_);
if (lean_obj_tag(v___x_361_) == 0)
{
lean_dec_ref_known(v___x_361_, 1);
v_a_333_ = v___x_342_;
goto v___jp_332_;
}
else
{
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_369_; 
lean_del_object(v___x_329_);
v_a_362_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_369_ == 0)
{
v___x_364_ = v___x_361_;
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_361_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_365_ == 0)
{
v___x_367_ = v___x_364_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_a_362_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
}
}
else
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_377_; 
lean_dec(v___x_345_);
lean_del_object(v___x_329_);
v_a_370_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_377_ == 0)
{
v___x_372_ = v___x_358_;
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_358_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_375_; 
if (v_isShared_373_ == 0)
{
v___x_375_ = v___x_372_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_a_370_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
}
else
{
lean_dec(v___x_356_);
lean_dec_ref(v___f_349_);
lean_dec_ref(v___f_347_);
lean_dec(v___x_345_);
v_a_333_ = v___x_342_;
goto v___jp_332_;
}
}
}
else
{
lean_dec(v___x_345_);
lean_dec(v_snd_344_);
v_a_333_ = v___x_342_;
goto v___jp_332_;
}
}
v___jp_332_:
{
lean_object* v___x_335_; 
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 1, v_a_333_);
lean_ctor_set(v___x_329_, 0, v___x_331_);
v___x_335_ = v___x_329_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_331_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v_a_333_);
v___x_335_ = v_reuseFailAlloc_339_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
size_t v___x_336_; size_t v___x_337_; 
v___x_336_ = ((size_t)1ULL);
v___x_337_ = lean_usize_add(v_i_317_, v___x_336_);
v_i_317_ = v___x_337_;
v_b_318_ = v___x_335_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2_spec__5___boxed(lean_object* v_as_412_, lean_object* v_sz_413_, lean_object* v_i_414_, lean_object* v_b_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
size_t v_sz_boxed_422_; size_t v_i_boxed_423_; lean_object* v_res_424_; 
v_sz_boxed_422_ = lean_unbox_usize(v_sz_413_);
lean_dec(v_sz_413_);
v_i_boxed_423_ = lean_unbox_usize(v_i_414_);
lean_dec(v_i_414_);
v_res_424_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2_spec__5(v_as_412_, v_sz_boxed_422_, v_i_boxed_423_, v_b_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v___y_416_);
lean_dec_ref(v_as_412_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2(lean_object* v_as_425_, size_t v_sz_426_, size_t v_i_427_, lean_object* v_b_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
uint8_t v___x_435_; 
v___x_435_ = lean_usize_dec_lt(v_i_427_, v_sz_426_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; 
v___x_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_436_, 0, v_b_428_);
return v___x_436_;
}
else
{
lean_object* v_snd_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_520_; 
v_snd_437_ = lean_ctor_get(v_b_428_, 1);
v_isSharedCheck_520_ = !lean_is_exclusive(v_b_428_);
if (v_isSharedCheck_520_ == 0)
{
lean_object* v_unused_521_; 
v_unused_521_ = lean_ctor_get(v_b_428_, 0);
lean_dec(v_unused_521_);
v___x_439_ = v_b_428_;
v_isShared_440_ = v_isSharedCheck_520_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_snd_437_);
lean_dec(v_b_428_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_520_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_441_; lean_object* v_a_443_; lean_object* v_a_450_; 
v___x_441_ = lean_box(0);
v_a_450_ = lean_array_uget_borrowed(v_as_425_, v_i_427_);
if (lean_obj_tag(v_a_450_) == 0)
{
v_a_443_ = v_snd_437_;
goto v___jp_442_;
}
else
{
lean_object* v_val_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v_snd_454_; lean_object* v___x_455_; uint8_t v___x_456_; 
lean_dec(v_snd_437_);
v_val_451_ = lean_ctor_get(v_a_450_, 0);
v___x_452_ = lean_box(0);
v___x_453_ = lean_st_ref_get(v___y_429_);
v_snd_454_ = lean_ctor_get(v___x_453_, 1);
lean_inc(v_snd_454_);
lean_dec(v___x_453_);
v___x_455_ = l_Lean_LocalDecl_fvarId(v_val_451_);
v___x_456_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_455_, v_snd_454_);
if (v___x_456_ == 0)
{
lean_object* v___f_457_; lean_object* v___x_458_; lean_object* v___f_459_; lean_object* v___y_461_; lean_object* v___y_462_; lean_object* v___y_463_; lean_object* v___y_464_; lean_object* v___y_465_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___f_457_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_457_, 0, v_snd_454_);
v___x_458_ = lean_box(v___x_456_);
v___f_459_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__2___boxed), 2, 1);
lean_closure_set(v___f_459_, 0, v___x_458_);
v___x_488_ = l_Lean_LocalDecl_type(v_val_451_);
lean_inc_ref(v___x_488_);
v___x_489_ = l_Lean_Meta_isProp(v___x_488_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v_a_490_; uint8_t v___x_491_; 
v_a_490_ = lean_ctor_get(v___x_489_, 0);
lean_inc(v_a_490_);
lean_dec_ref_known(v___x_489_, 1);
v___x_491_ = lean_unbox(v_a_490_);
lean_dec(v_a_490_);
if (v___x_491_ == 0)
{
lean_dec_ref(v___x_488_);
v___y_461_ = v___y_429_;
v___y_462_ = v___y_430_;
v___y_463_ = v___y_431_;
v___y_464_ = v___y_432_;
v___y_465_ = v___y_433_;
goto v___jp_460_;
}
else
{
lean_object* v___x_492_; 
lean_inc_ref(v___f_459_);
lean_inc_ref(v___f_457_);
v___x_492_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v___x_488_, v___f_457_, v___f_459_, v___y_431_);
if (lean_obj_tag(v___x_492_) == 0)
{
lean_object* v_a_493_; uint8_t v___x_494_; 
v_a_493_ = lean_ctor_get(v___x_492_, 0);
lean_inc(v_a_493_);
lean_dec_ref_known(v___x_492_, 1);
v___x_494_ = lean_unbox(v_a_493_);
lean_dec(v_a_493_);
if (v___x_494_ == 0)
{
v___y_461_ = v___y_429_;
v___y_462_ = v___y_430_;
v___y_463_ = v___y_431_;
v___y_464_ = v___y_432_;
v___y_465_ = v___y_433_;
goto v___jp_460_;
}
else
{
lean_object* v___x_495_; 
lean_inc(v___x_455_);
v___x_495_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_455_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_dec_ref_known(v___x_495_, 1);
v___y_461_ = v___y_429_;
v___y_462_ = v___y_430_;
v___y_463_ = v___y_431_;
v___y_464_ = v___y_432_;
v___y_465_ = v___y_433_;
goto v___jp_460_;
}
else
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_503_; 
lean_dec_ref(v___f_459_);
lean_dec_ref(v___f_457_);
lean_dec(v___x_455_);
lean_del_object(v___x_439_);
v_a_496_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_503_ == 0)
{
v___x_498_ = v___x_495_;
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_495_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_501_; 
if (v_isShared_499_ == 0)
{
v___x_501_ = v___x_498_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_a_496_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
}
else
{
lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_511_; 
lean_dec_ref(v___f_459_);
lean_dec_ref(v___f_457_);
lean_dec(v___x_455_);
lean_del_object(v___x_439_);
v_a_504_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_511_ == 0)
{
v___x_506_ = v___x_492_;
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_492_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_509_; 
if (v_isShared_507_ == 0)
{
v___x_509_ = v___x_506_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_a_504_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
}
}
else
{
lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_519_; 
lean_dec_ref(v___x_488_);
lean_dec_ref(v___f_459_);
lean_dec_ref(v___f_457_);
lean_dec(v___x_455_);
lean_del_object(v___x_439_);
v_a_512_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_519_ == 0)
{
v___x_514_ = v___x_489_;
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v___x_489_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_517_; 
if (v_isShared_515_ == 0)
{
v___x_517_ = v___x_514_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_a_512_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
v___jp_460_:
{
lean_object* v___x_466_; 
v___x_466_ = l_Lean_LocalDecl_value_x3f(v_val_451_, v___x_456_);
if (lean_obj_tag(v___x_466_) == 1)
{
lean_object* v_val_467_; lean_object* v___x_468_; 
v_val_467_ = lean_ctor_get(v___x_466_, 0);
lean_inc(v_val_467_);
lean_dec_ref_known(v___x_466_, 1);
v___x_468_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v_val_467_, v___f_457_, v___f_459_, v___y_463_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; uint8_t v___x_470_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc(v_a_469_);
lean_dec_ref_known(v___x_468_, 1);
v___x_470_ = lean_unbox(v_a_469_);
lean_dec(v_a_469_);
if (v___x_470_ == 0)
{
lean_dec(v___x_455_);
v_a_443_ = v___x_452_;
goto v___jp_442_;
}
else
{
lean_object* v___x_471_; 
v___x_471_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_455_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_dec_ref_known(v___x_471_, 1);
v_a_443_ = v___x_452_;
goto v___jp_442_;
}
else
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_479_; 
lean_del_object(v___x_439_);
v_a_472_ = lean_ctor_get(v___x_471_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_479_ == 0)
{
v___x_474_ = v___x_471_;
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_471_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_477_; 
if (v_isShared_475_ == 0)
{
v___x_477_ = v___x_474_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_a_472_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
}
else
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_487_; 
lean_dec(v___x_455_);
lean_del_object(v___x_439_);
v_a_480_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_487_ == 0)
{
v___x_482_ = v___x_468_;
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_468_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_485_; 
if (v_isShared_483_ == 0)
{
v___x_485_ = v___x_482_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_a_480_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
else
{
lean_dec(v___x_466_);
lean_dec_ref(v___f_459_);
lean_dec_ref(v___f_457_);
lean_dec(v___x_455_);
v_a_443_ = v___x_452_;
goto v___jp_442_;
}
}
}
else
{
lean_dec(v___x_455_);
lean_dec(v_snd_454_);
v_a_443_ = v___x_452_;
goto v___jp_442_;
}
}
v___jp_442_:
{
lean_object* v___x_445_; 
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 1, v_a_443_);
lean_ctor_set(v___x_439_, 0, v___x_441_);
v___x_445_ = v___x_439_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_441_);
lean_ctor_set(v_reuseFailAlloc_449_, 1, v_a_443_);
v___x_445_ = v_reuseFailAlloc_449_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
size_t v___x_446_; size_t v___x_447_; lean_object* v___x_448_; 
v___x_446_ = ((size_t)1ULL);
v___x_447_ = lean_usize_add(v_i_427_, v___x_446_);
v___x_448_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2_spec__5(v_as_425_, v_sz_426_, v___x_447_, v___x_445_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
return v___x_448_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___boxed(lean_object* v_as_522_, lean_object* v_sz_523_, lean_object* v_i_524_, lean_object* v_b_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
size_t v_sz_boxed_532_; size_t v_i_boxed_533_; lean_object* v_res_534_; 
v_sz_boxed_532_ = lean_unbox_usize(v_sz_523_);
lean_dec(v_sz_523_);
v_i_boxed_533_ = lean_unbox_usize(v_i_524_);
lean_dec(v_i_524_);
v_res_534_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2(v_as_522_, v_sz_boxed_532_, v_i_boxed_533_, v_b_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec_ref(v_as_522_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3_spec__4(lean_object* v_as_535_, size_t v_sz_536_, size_t v_i_537_, lean_object* v_b_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
uint8_t v___x_545_; 
v___x_545_ = lean_usize_dec_lt(v_i_537_, v_sz_536_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; 
v___x_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_546_, 0, v_b_538_);
return v___x_546_;
}
else
{
lean_object* v_snd_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_630_; 
v_snd_547_ = lean_ctor_get(v_b_538_, 1);
v_isSharedCheck_630_ = !lean_is_exclusive(v_b_538_);
if (v_isSharedCheck_630_ == 0)
{
lean_object* v_unused_631_; 
v_unused_631_ = lean_ctor_get(v_b_538_, 0);
lean_dec(v_unused_631_);
v___x_549_ = v_b_538_;
v_isShared_550_ = v_isSharedCheck_630_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_snd_547_);
lean_dec(v_b_538_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_630_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_551_; lean_object* v_a_553_; lean_object* v_a_560_; 
v___x_551_ = lean_box(0);
v_a_560_ = lean_array_uget_borrowed(v_as_535_, v_i_537_);
if (lean_obj_tag(v_a_560_) == 0)
{
v_a_553_ = v_snd_547_;
goto v___jp_552_;
}
else
{
lean_object* v_val_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v_snd_564_; lean_object* v___x_565_; uint8_t v___x_566_; 
lean_dec(v_snd_547_);
v_val_561_ = lean_ctor_get(v_a_560_, 0);
v___x_562_ = lean_box(0);
v___x_563_ = lean_st_ref_get(v___y_539_);
v_snd_564_ = lean_ctor_get(v___x_563_, 1);
lean_inc(v_snd_564_);
lean_dec(v___x_563_);
v___x_565_ = l_Lean_LocalDecl_fvarId(v_val_561_);
v___x_566_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_565_, v_snd_564_);
if (v___x_566_ == 0)
{
lean_object* v___f_567_; lean_object* v___x_568_; lean_object* v___f_569_; lean_object* v___y_571_; lean_object* v___y_572_; lean_object* v___y_573_; lean_object* v___y_574_; lean_object* v___y_575_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___f_567_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_567_, 0, v_snd_564_);
v___x_568_ = lean_box(v___x_566_);
v___f_569_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__2___boxed), 2, 1);
lean_closure_set(v___f_569_, 0, v___x_568_);
v___x_598_ = l_Lean_LocalDecl_type(v_val_561_);
lean_inc_ref(v___x_598_);
v___x_599_ = l_Lean_Meta_isProp(v___x_598_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v_a_600_; uint8_t v___x_601_; 
v_a_600_ = lean_ctor_get(v___x_599_, 0);
lean_inc(v_a_600_);
lean_dec_ref_known(v___x_599_, 1);
v___x_601_ = lean_unbox(v_a_600_);
lean_dec(v_a_600_);
if (v___x_601_ == 0)
{
lean_dec_ref(v___x_598_);
v___y_571_ = v___y_539_;
v___y_572_ = v___y_540_;
v___y_573_ = v___y_541_;
v___y_574_ = v___y_542_;
v___y_575_ = v___y_543_;
goto v___jp_570_;
}
else
{
lean_object* v___x_602_; 
lean_inc_ref(v___f_569_);
lean_inc_ref(v___f_567_);
v___x_602_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v___x_598_, v___f_567_, v___f_569_, v___y_541_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v_a_603_; uint8_t v___x_604_; 
v_a_603_ = lean_ctor_get(v___x_602_, 0);
lean_inc(v_a_603_);
lean_dec_ref_known(v___x_602_, 1);
v___x_604_ = lean_unbox(v_a_603_);
lean_dec(v_a_603_);
if (v___x_604_ == 0)
{
v___y_571_ = v___y_539_;
v___y_572_ = v___y_540_;
v___y_573_ = v___y_541_;
v___y_574_ = v___y_542_;
v___y_575_ = v___y_543_;
goto v___jp_570_;
}
else
{
lean_object* v___x_605_; 
lean_inc(v___x_565_);
v___x_605_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_565_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
if (lean_obj_tag(v___x_605_) == 0)
{
lean_dec_ref_known(v___x_605_, 1);
v___y_571_ = v___y_539_;
v___y_572_ = v___y_540_;
v___y_573_ = v___y_541_;
v___y_574_ = v___y_542_;
v___y_575_ = v___y_543_;
goto v___jp_570_;
}
else
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
lean_dec_ref(v___f_569_);
lean_dec_ref(v___f_567_);
lean_dec(v___x_565_);
lean_del_object(v___x_549_);
v_a_606_ = lean_ctor_get(v___x_605_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_613_ == 0)
{
v___x_608_ = v___x_605_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_605_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_a_606_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
}
else
{
lean_object* v_a_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_621_; 
lean_dec_ref(v___f_569_);
lean_dec_ref(v___f_567_);
lean_dec(v___x_565_);
lean_del_object(v___x_549_);
v_a_614_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_621_ == 0)
{
v___x_616_ = v___x_602_;
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_a_614_);
lean_dec(v___x_602_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_619_; 
if (v_isShared_617_ == 0)
{
v___x_619_ = v___x_616_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_a_614_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
}
}
else
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_629_; 
lean_dec_ref(v___x_598_);
lean_dec_ref(v___f_569_);
lean_dec_ref(v___f_567_);
lean_dec(v___x_565_);
lean_del_object(v___x_549_);
v_a_622_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_629_ == 0)
{
v___x_624_ = v___x_599_;
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_599_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_627_; 
if (v_isShared_625_ == 0)
{
v___x_627_ = v___x_624_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_a_622_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
v___jp_570_:
{
lean_object* v___x_576_; 
v___x_576_ = l_Lean_LocalDecl_value_x3f(v_val_561_, v___x_566_);
if (lean_obj_tag(v___x_576_) == 1)
{
lean_object* v_val_577_; lean_object* v___x_578_; 
v_val_577_ = lean_ctor_get(v___x_576_, 0);
lean_inc(v_val_577_);
lean_dec_ref_known(v___x_576_, 1);
v___x_578_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v_val_577_, v___f_567_, v___f_569_, v___y_573_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v_a_579_; uint8_t v___x_580_; 
v_a_579_ = lean_ctor_get(v___x_578_, 0);
lean_inc(v_a_579_);
lean_dec_ref_known(v___x_578_, 1);
v___x_580_ = lean_unbox(v_a_579_);
lean_dec(v_a_579_);
if (v___x_580_ == 0)
{
lean_dec(v___x_565_);
v_a_553_ = v___x_562_;
goto v___jp_552_;
}
else
{
lean_object* v___x_581_; 
v___x_581_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_565_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_dec_ref_known(v___x_581_, 1);
v_a_553_ = v___x_562_;
goto v___jp_552_;
}
else
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_589_; 
lean_del_object(v___x_549_);
v_a_582_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_589_ == 0)
{
v___x_584_ = v___x_581_;
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_581_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
if (v_isShared_585_ == 0)
{
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_a_582_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
}
}
else
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_597_; 
lean_dec(v___x_565_);
lean_del_object(v___x_549_);
v_a_590_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_597_ == 0)
{
v___x_592_ = v___x_578_;
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_578_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_a_590_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
}
else
{
lean_dec(v___x_576_);
lean_dec_ref(v___f_569_);
lean_dec_ref(v___f_567_);
lean_dec(v___x_565_);
v_a_553_ = v___x_562_;
goto v___jp_552_;
}
}
}
else
{
lean_dec(v___x_565_);
lean_dec(v_snd_564_);
v_a_553_ = v___x_562_;
goto v___jp_552_;
}
}
v___jp_552_:
{
lean_object* v___x_555_; 
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 1, v_a_553_);
lean_ctor_set(v___x_549_, 0, v___x_551_);
v___x_555_ = v___x_549_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_551_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v_a_553_);
v___x_555_ = v_reuseFailAlloc_559_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
size_t v___x_556_; size_t v___x_557_; 
v___x_556_ = ((size_t)1ULL);
v___x_557_ = lean_usize_add(v_i_537_, v___x_556_);
v_i_537_ = v___x_557_;
v_b_538_ = v___x_555_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3_spec__4___boxed(lean_object* v_as_632_, lean_object* v_sz_633_, lean_object* v_i_634_, lean_object* v_b_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
size_t v_sz_boxed_642_; size_t v_i_boxed_643_; lean_object* v_res_644_; 
v_sz_boxed_642_ = lean_unbox_usize(v_sz_633_);
lean_dec(v_sz_633_);
v_i_boxed_643_ = lean_unbox_usize(v_i_634_);
lean_dec(v_i_634_);
v_res_644_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3_spec__4(v_as_632_, v_sz_boxed_642_, v_i_boxed_643_, v_b_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec(v___y_636_);
lean_dec_ref(v_as_632_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3(lean_object* v_as_645_, size_t v_sz_646_, size_t v_i_647_, lean_object* v_b_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
uint8_t v___x_655_; 
v___x_655_ = lean_usize_dec_lt(v_i_647_, v_sz_646_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; 
v___x_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_656_, 0, v_b_648_);
return v___x_656_;
}
else
{
lean_object* v_snd_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_740_; 
v_snd_657_ = lean_ctor_get(v_b_648_, 1);
v_isSharedCheck_740_ = !lean_is_exclusive(v_b_648_);
if (v_isSharedCheck_740_ == 0)
{
lean_object* v_unused_741_; 
v_unused_741_ = lean_ctor_get(v_b_648_, 0);
lean_dec(v_unused_741_);
v___x_659_ = v_b_648_;
v_isShared_660_ = v_isSharedCheck_740_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_snd_657_);
lean_dec(v_b_648_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_740_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_661_; lean_object* v_a_663_; lean_object* v_a_670_; 
v___x_661_ = lean_box(0);
v_a_670_ = lean_array_uget_borrowed(v_as_645_, v_i_647_);
if (lean_obj_tag(v_a_670_) == 0)
{
v_a_663_ = v_snd_657_;
goto v___jp_662_;
}
else
{
lean_object* v_val_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v_snd_674_; lean_object* v___x_675_; uint8_t v___x_676_; 
lean_dec(v_snd_657_);
v_val_671_ = lean_ctor_get(v_a_670_, 0);
v___x_672_ = lean_box(0);
v___x_673_ = lean_st_ref_get(v___y_649_);
v_snd_674_ = lean_ctor_get(v___x_673_, 1);
lean_inc(v_snd_674_);
lean_dec(v___x_673_);
v___x_675_ = l_Lean_LocalDecl_fvarId(v_val_671_);
v___x_676_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_675_, v_snd_674_);
if (v___x_676_ == 0)
{
lean_object* v___f_677_; lean_object* v___x_678_; lean_object* v___f_679_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___f_677_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_677_, 0, v_snd_674_);
v___x_678_ = lean_box(v___x_676_);
v___f_679_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__2___boxed), 2, 1);
lean_closure_set(v___f_679_, 0, v___x_678_);
v___x_708_ = l_Lean_LocalDecl_type(v_val_671_);
lean_inc_ref(v___x_708_);
v___x_709_ = l_Lean_Meta_isProp(v___x_708_, v___y_650_, v___y_651_, v___y_652_, v___y_653_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; uint8_t v___x_711_; 
v_a_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_a_710_);
lean_dec_ref_known(v___x_709_, 1);
v___x_711_ = lean_unbox(v_a_710_);
lean_dec(v_a_710_);
if (v___x_711_ == 0)
{
lean_dec_ref(v___x_708_);
v___y_681_ = v___y_649_;
v___y_682_ = v___y_650_;
v___y_683_ = v___y_651_;
v___y_684_ = v___y_652_;
v___y_685_ = v___y_653_;
goto v___jp_680_;
}
else
{
lean_object* v___x_712_; 
lean_inc_ref(v___f_679_);
lean_inc_ref(v___f_677_);
v___x_712_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v___x_708_, v___f_677_, v___f_679_, v___y_651_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v_a_713_; uint8_t v___x_714_; 
v_a_713_ = lean_ctor_get(v___x_712_, 0);
lean_inc(v_a_713_);
lean_dec_ref_known(v___x_712_, 1);
v___x_714_ = lean_unbox(v_a_713_);
lean_dec(v_a_713_);
if (v___x_714_ == 0)
{
v___y_681_ = v___y_649_;
v___y_682_ = v___y_650_;
v___y_683_ = v___y_651_;
v___y_684_ = v___y_652_;
v___y_685_ = v___y_653_;
goto v___jp_680_;
}
else
{
lean_object* v___x_715_; 
lean_inc(v___x_675_);
v___x_715_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_675_, v___y_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_dec_ref_known(v___x_715_, 1);
v___y_681_ = v___y_649_;
v___y_682_ = v___y_650_;
v___y_683_ = v___y_651_;
v___y_684_ = v___y_652_;
v___y_685_ = v___y_653_;
goto v___jp_680_;
}
else
{
lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_723_; 
lean_dec_ref(v___f_679_);
lean_dec_ref(v___f_677_);
lean_dec(v___x_675_);
lean_del_object(v___x_659_);
v_a_716_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_723_ == 0)
{
v___x_718_ = v___x_715_;
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v___x_715_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_721_; 
if (v_isShared_719_ == 0)
{
v___x_721_ = v___x_718_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_a_716_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
}
else
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
lean_dec_ref(v___f_679_);
lean_dec_ref(v___f_677_);
lean_dec(v___x_675_);
lean_del_object(v___x_659_);
v_a_724_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_731_ == 0)
{
v___x_726_ = v___x_712_;
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_712_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_729_; 
if (v_isShared_727_ == 0)
{
v___x_729_ = v___x_726_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_a_724_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
}
else
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_739_; 
lean_dec_ref(v___x_708_);
lean_dec_ref(v___f_679_);
lean_dec_ref(v___f_677_);
lean_dec(v___x_675_);
lean_del_object(v___x_659_);
v_a_732_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_739_ == 0)
{
v___x_734_ = v___x_709_;
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___x_709_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_737_; 
if (v_isShared_735_ == 0)
{
v___x_737_ = v___x_734_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_a_732_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
v___jp_680_:
{
lean_object* v___x_686_; 
v___x_686_ = l_Lean_LocalDecl_value_x3f(v_val_671_, v___x_676_);
if (lean_obj_tag(v___x_686_) == 1)
{
lean_object* v_val_687_; lean_object* v___x_688_; 
v_val_687_ = lean_ctor_get(v___x_686_, 0);
lean_inc(v_val_687_);
lean_dec_ref_known(v___x_686_, 1);
v___x_688_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v_val_687_, v___f_677_, v___f_679_, v___y_683_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_a_689_; uint8_t v___x_690_; 
v_a_689_ = lean_ctor_get(v___x_688_, 0);
lean_inc(v_a_689_);
lean_dec_ref_known(v___x_688_, 1);
v___x_690_ = lean_unbox(v_a_689_);
lean_dec(v_a_689_);
if (v___x_690_ == 0)
{
lean_dec(v___x_675_);
v_a_663_ = v___x_672_;
goto v___jp_662_;
}
else
{
lean_object* v___x_691_; 
v___x_691_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_675_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_dec_ref_known(v___x_691_, 1);
v_a_663_ = v___x_672_;
goto v___jp_662_;
}
else
{
lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_699_; 
lean_del_object(v___x_659_);
v_a_692_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_699_ == 0)
{
v___x_694_ = v___x_691_;
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_dec(v___x_691_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_697_; 
if (v_isShared_695_ == 0)
{
v___x_697_ = v___x_694_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_a_692_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
}
else
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
lean_dec(v___x_675_);
lean_del_object(v___x_659_);
v_a_700_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_707_ == 0)
{
v___x_702_ = v___x_688_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_688_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_703_ == 0)
{
v___x_705_ = v___x_702_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_a_700_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
else
{
lean_dec(v___x_686_);
lean_dec_ref(v___f_679_);
lean_dec_ref(v___f_677_);
lean_dec(v___x_675_);
v_a_663_ = v___x_672_;
goto v___jp_662_;
}
}
}
else
{
lean_dec(v___x_675_);
lean_dec(v_snd_674_);
v_a_663_ = v___x_672_;
goto v___jp_662_;
}
}
v___jp_662_:
{
lean_object* v___x_665_; 
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 1, v_a_663_);
lean_ctor_set(v___x_659_, 0, v___x_661_);
v___x_665_ = v___x_659_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_661_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v_a_663_);
v___x_665_ = v_reuseFailAlloc_669_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
size_t v___x_666_; size_t v___x_667_; lean_object* v___x_668_; 
v___x_666_ = ((size_t)1ULL);
v___x_667_ = lean_usize_add(v_i_647_, v___x_666_);
v___x_668_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3_spec__4(v_as_645_, v_sz_646_, v___x_667_, v___x_665_, v___y_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_);
return v___x_668_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3___boxed(lean_object* v_as_742_, lean_object* v_sz_743_, lean_object* v_i_744_, lean_object* v_b_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_){
_start:
{
size_t v_sz_boxed_752_; size_t v_i_boxed_753_; lean_object* v_res_754_; 
v_sz_boxed_752_ = lean_unbox_usize(v_sz_743_);
lean_dec(v_sz_743_);
v_i_boxed_753_ = lean_unbox_usize(v_i_744_);
lean_dec(v_i_744_);
v_res_754_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3(v_as_742_, v_sz_boxed_752_, v_i_boxed_753_, v_b_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v___y_746_);
lean_dec_ref(v_as_742_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1(lean_object* v_init_755_, lean_object* v_n_756_, lean_object* v_b_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
if (lean_obj_tag(v_n_756_) == 0)
{
lean_object* v_cs_764_; lean_object* v___x_765_; lean_object* v___x_766_; size_t v_sz_767_; size_t v___x_768_; lean_object* v___x_769_; 
v_cs_764_ = lean_ctor_get(v_n_756_, 0);
v___x_765_ = lean_box(0);
v___x_766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_766_, 0, v___x_765_);
lean_ctor_set(v___x_766_, 1, v_b_757_);
v_sz_767_ = lean_array_size(v_cs_764_);
v___x_768_ = ((size_t)0ULL);
v___x_769_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__2(v_init_755_, v_cs_764_, v_sz_767_, v___x_768_, v___x_766_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_784_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_784_ == 0)
{
v___x_772_ = v___x_769_;
v_isShared_773_ = v_isSharedCheck_784_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_769_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_784_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v_fst_774_; 
v_fst_774_ = lean_ctor_get(v_a_770_, 0);
if (lean_obj_tag(v_fst_774_) == 0)
{
lean_object* v_snd_775_; lean_object* v___x_776_; lean_object* v___x_778_; 
v_snd_775_ = lean_ctor_get(v_a_770_, 1);
lean_inc(v_snd_775_);
lean_dec(v_a_770_);
v___x_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_776_, 0, v_snd_775_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 0, v___x_776_);
v___x_778_ = v___x_772_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_776_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
else
{
lean_object* v_val_780_; lean_object* v___x_782_; 
lean_inc_ref(v_fst_774_);
lean_dec(v_a_770_);
v_val_780_ = lean_ctor_get(v_fst_774_, 0);
lean_inc(v_val_780_);
lean_dec_ref_known(v_fst_774_, 1);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 0, v_val_780_);
v___x_782_ = v___x_772_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_val_780_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
}
else
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_792_; 
v_a_785_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_792_ == 0)
{
v___x_787_ = v___x_769_;
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_769_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_790_; 
if (v_isShared_788_ == 0)
{
v___x_790_ = v___x_787_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_a_785_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
}
else
{
lean_object* v_vs_793_; lean_object* v___x_794_; lean_object* v___x_795_; size_t v_sz_796_; size_t v___x_797_; lean_object* v___x_798_; 
v_vs_793_ = lean_ctor_get(v_n_756_, 0);
v___x_794_ = lean_box(0);
v___x_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_795_, 0, v___x_794_);
lean_ctor_set(v___x_795_, 1, v_b_757_);
v_sz_796_ = lean_array_size(v_vs_793_);
v___x_797_ = ((size_t)0ULL);
v___x_798_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3(v_vs_793_, v_sz_796_, v___x_797_, v___x_795_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_813_; 
v_a_799_ = lean_ctor_get(v___x_798_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_813_ == 0)
{
v___x_801_ = v___x_798_;
v_isShared_802_ = v_isSharedCheck_813_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_798_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_813_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v_fst_803_; 
v_fst_803_ = lean_ctor_get(v_a_799_, 0);
if (lean_obj_tag(v_fst_803_) == 0)
{
lean_object* v_snd_804_; lean_object* v___x_805_; lean_object* v___x_807_; 
v_snd_804_ = lean_ctor_get(v_a_799_, 1);
lean_inc(v_snd_804_);
lean_dec(v_a_799_);
v___x_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_805_, 0, v_snd_804_);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 0, v___x_805_);
v___x_807_ = v___x_801_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_805_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
else
{
lean_object* v_val_809_; lean_object* v___x_811_; 
lean_inc_ref(v_fst_803_);
lean_dec(v_a_799_);
v_val_809_ = lean_ctor_get(v_fst_803_, 0);
lean_inc(v_val_809_);
lean_dec_ref_known(v_fst_803_, 1);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 0, v_val_809_);
v___x_811_ = v___x_801_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_val_809_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
else
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_821_; 
v_a_814_ = lean_ctor_get(v___x_798_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_821_ == 0)
{
v___x_816_ = v___x_798_;
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_798_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_819_; 
if (v_isShared_817_ == 0)
{
v___x_819_ = v___x_816_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_a_814_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__2(lean_object* v_init_822_, lean_object* v_as_823_, size_t v_sz_824_, size_t v_i_825_, lean_object* v_b_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
uint8_t v___x_833_; 
v___x_833_ = lean_usize_dec_lt(v_i_825_, v_sz_824_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; 
v___x_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_834_, 0, v_b_826_);
return v___x_834_;
}
else
{
lean_object* v_snd_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_869_; 
v_snd_835_ = lean_ctor_get(v_b_826_, 1);
v_isSharedCheck_869_ = !lean_is_exclusive(v_b_826_);
if (v_isSharedCheck_869_ == 0)
{
lean_object* v_unused_870_; 
v_unused_870_ = lean_ctor_get(v_b_826_, 0);
lean_dec(v_unused_870_);
v___x_837_ = v_b_826_;
v_isShared_838_ = v_isSharedCheck_869_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_snd_835_);
lean_dec(v_b_826_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_869_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_839_; lean_object* v_a_840_; lean_object* v___x_841_; 
v___x_839_ = lean_box(0);
v_a_840_ = lean_array_uget_borrowed(v_as_823_, v_i_825_);
lean_inc(v_snd_835_);
v___x_841_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1(v_init_822_, v_a_840_, v_snd_835_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_860_; 
v_a_842_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_860_ == 0)
{
v___x_844_ = v___x_841_;
v_isShared_845_ = v_isSharedCheck_860_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_841_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_860_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
if (lean_obj_tag(v_a_842_) == 0)
{
lean_object* v___x_846_; lean_object* v___x_848_; 
v___x_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_846_, 0, v_a_842_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 0, v___x_846_);
v___x_848_ = v___x_837_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_846_);
lean_ctor_set(v_reuseFailAlloc_852_, 1, v_snd_835_);
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
lean_object* v_a_853_; lean_object* v___x_855_; 
lean_del_object(v___x_844_);
lean_dec(v_snd_835_);
v_a_853_ = lean_ctor_get(v_a_842_, 0);
lean_inc(v_a_853_);
lean_dec_ref_known(v_a_842_, 1);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 1, v_a_853_);
lean_ctor_set(v___x_837_, 0, v___x_839_);
v___x_855_ = v___x_837_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___x_839_);
lean_ctor_set(v_reuseFailAlloc_859_, 1, v_a_853_);
v___x_855_ = v_reuseFailAlloc_859_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
size_t v___x_856_; size_t v___x_857_; 
v___x_856_ = ((size_t)1ULL);
v___x_857_ = lean_usize_add(v_i_825_, v___x_856_);
v_i_825_ = v___x_857_;
v_b_826_ = v___x_855_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_868_; 
lean_del_object(v___x_837_);
lean_dec(v_snd_835_);
v_a_861_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_868_ == 0)
{
v___x_863_ = v___x_841_;
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_841_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_866_; 
if (v_isShared_864_ == 0)
{
v___x_866_ = v___x_863_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_a_861_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__2___boxed(lean_object* v_init_871_, lean_object* v_as_872_, lean_object* v_sz_873_, lean_object* v_i_874_, lean_object* v_b_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
size_t v_sz_boxed_882_; size_t v_i_boxed_883_; lean_object* v_res_884_; 
v_sz_boxed_882_ = lean_unbox_usize(v_sz_873_);
lean_dec(v_sz_873_);
v_i_boxed_883_ = lean_unbox_usize(v_i_874_);
lean_dec(v_i_874_);
v_res_884_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__2(v_init_871_, v_as_872_, v_sz_boxed_882_, v_i_boxed_883_, v_b_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
lean_dec(v___y_876_);
lean_dec_ref(v_as_872_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1___boxed(lean_object* v_init_885_, lean_object* v_n_886_, lean_object* v_b_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1(v_init_885_, v_n_886_, v_b_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
lean_dec(v___y_888_);
lean_dec_ref(v_n_886_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1(lean_object* v_t_895_, lean_object* v_init_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
lean_object* v_root_903_; lean_object* v_tail_904_; lean_object* v___x_905_; 
v_root_903_ = lean_ctor_get(v_t_895_, 0);
v_tail_904_ = lean_ctor_get(v_t_895_, 1);
v___x_905_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1(v_init_896_, v_root_903_, v_init_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
if (lean_obj_tag(v___x_905_) == 0)
{
lean_object* v_a_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_942_; 
v_a_906_ = lean_ctor_get(v___x_905_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_942_ == 0)
{
v___x_908_ = v___x_905_;
v_isShared_909_ = v_isSharedCheck_942_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_a_906_);
lean_dec(v___x_905_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_942_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
if (lean_obj_tag(v_a_906_) == 0)
{
lean_object* v_a_910_; lean_object* v___x_912_; 
v_a_910_ = lean_ctor_get(v_a_906_, 0);
lean_inc(v_a_910_);
lean_dec_ref_known(v_a_906_, 1);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 0, v_a_910_);
v___x_912_ = v___x_908_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_a_910_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
else
{
lean_object* v_a_914_; lean_object* v___x_915_; lean_object* v___x_916_; size_t v_sz_917_; size_t v___x_918_; lean_object* v___x_919_; 
lean_del_object(v___x_908_);
v_a_914_ = lean_ctor_get(v_a_906_, 0);
lean_inc(v_a_914_);
lean_dec_ref_known(v_a_906_, 1);
v___x_915_ = lean_box(0);
v___x_916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
lean_ctor_set(v___x_916_, 1, v_a_914_);
v_sz_917_ = lean_array_size(v_tail_904_);
v___x_918_ = ((size_t)0ULL);
v___x_919_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2(v_tail_904_, v_sz_917_, v___x_918_, v___x_916_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_933_; 
v_a_920_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_933_ == 0)
{
v___x_922_ = v___x_919_;
v_isShared_923_ = v_isSharedCheck_933_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_919_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_933_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v_fst_924_; 
v_fst_924_ = lean_ctor_get(v_a_920_, 0);
if (lean_obj_tag(v_fst_924_) == 0)
{
lean_object* v_snd_925_; lean_object* v___x_927_; 
v_snd_925_ = lean_ctor_get(v_a_920_, 1);
lean_inc(v_snd_925_);
lean_dec(v_a_920_);
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 0, v_snd_925_);
v___x_927_ = v___x_922_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_snd_925_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
else
{
lean_object* v_val_929_; lean_object* v___x_931_; 
lean_inc_ref(v_fst_924_);
lean_dec(v_a_920_);
v_val_929_ = lean_ctor_get(v_fst_924_, 0);
lean_inc(v_val_929_);
lean_dec_ref_known(v_fst_924_, 1);
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 0, v_val_929_);
v___x_931_ = v___x_922_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_val_929_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
else
{
lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_941_; 
v_a_934_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_941_ == 0)
{
v___x_936_ = v___x_919_;
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___x_919_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_939_; 
if (v_isShared_937_ == 0)
{
v___x_939_ = v___x_936_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_a_934_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
}
}
else
{
lean_object* v_a_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_950_; 
v_a_943_ = lean_ctor_get(v___x_905_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_950_ == 0)
{
v___x_945_ = v___x_905_;
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_dec(v___x_905_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_948_; 
if (v_isShared_946_ == 0)
{
v___x_948_ = v___x_945_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_a_943_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1___boxed(lean_object* v_t_951_, lean_object* v_init_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1(v_t_951_, v_init_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v___y_953_);
lean_dec_ref(v_t_951_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep(lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_){
_start:
{
lean_object* v_lctx_966_; lean_object* v_decls_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v_lctx_966_ = lean_ctor_get(v_a_961_, 2);
v_decls_967_ = lean_ctor_get(v_lctx_966_, 1);
v___x_968_ = lean_box(0);
v___x_969_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1(v_decls_967_, v___x_968_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_976_; 
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_976_ == 0)
{
lean_object* v_unused_977_; 
v_unused_977_ = lean_ctor_get(v___x_969_, 0);
lean_dec(v_unused_977_);
v___x_971_ = v___x_969_;
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
else
{
lean_dec(v___x_969_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_974_; 
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 0, v___x_968_);
v___x_974_ = v___x_971_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v___x_968_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
else
{
return v___x_969_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep___boxed(lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep(v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_);
lean_dec(v_a_982_);
lean_dec_ref(v_a_981_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
lean_dec(v_a_978_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectProps(lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_){
_start:
{
lean_object* v___x_991_; lean_object* v_snd_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1016_; 
v___x_991_ = lean_st_ref_take(v_a_985_);
v_snd_992_ = lean_ctor_get(v___x_991_, 1);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1016_ == 0)
{
lean_object* v_unused_1017_; 
v_unused_1017_ = lean_ctor_get(v___x_991_, 0);
lean_dec(v_unused_1017_);
v___x_994_ = v___x_991_;
v_isShared_995_ = v_isSharedCheck_1016_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_snd_992_);
lean_dec(v___x_991_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1016_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
uint8_t v___x_996_; lean_object* v___x_997_; lean_object* v___x_999_; 
v___x_996_ = 0;
v___x_997_ = lean_box(v___x_996_);
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 0, v___x_997_);
v___x_999_ = v___x_994_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v___x_997_);
lean_ctor_set(v_reuseFailAlloc_1015_, 1, v_snd_992_);
v___x_999_ = v_reuseFailAlloc_1015_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = lean_st_ref_put(v_a_985_, v___x_999_);
v___x_1001_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep(v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1013_; 
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1013_ == 0)
{
lean_object* v_unused_1014_; 
v_unused_1014_ = lean_ctor_get(v___x_1001_, 0);
lean_dec(v_unused_1014_);
v___x_1003_ = v___x_1001_;
v_isShared_1004_ = v_isSharedCheck_1013_;
goto v_resetjp_1002_;
}
else
{
lean_dec(v___x_1001_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1013_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1005_; lean_object* v_fst_1006_; uint8_t v___x_1007_; 
v___x_1005_ = lean_st_ref_get(v_a_985_);
v_fst_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc(v_fst_1006_);
lean_dec(v___x_1005_);
v___x_1007_ = lean_unbox(v_fst_1006_);
lean_dec(v_fst_1006_);
if (v___x_1007_ == 0)
{
lean_object* v___x_1008_; lean_object* v___x_1010_; 
v___x_1008_ = lean_box(0);
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 0, v___x_1008_);
v___x_1010_ = v___x_1003_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1008_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
else
{
lean_del_object(v___x_1003_);
goto _start;
}
}
}
else
{
return v___x_1001_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectProps___boxed(lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectProps(v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
lean_dec(v_a_1022_);
lean_dec_ref(v_a_1021_);
lean_dec(v_a_1020_);
lean_dec_ref(v_a_1019_);
lean_dec(v_a_1018_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed_spec__0(lean_object* v_as_1025_, size_t v_i_1026_, size_t v_stop_1027_, lean_object* v_b_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
uint8_t v___x_1035_; 
v___x_1035_ = lean_usize_dec_eq(v_i_1026_, v_stop_1027_);
if (v___x_1035_ == 0)
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1036_ = lean_array_uget_borrowed(v_as_1025_, v_i_1026_);
lean_inc(v___x_1036_);
v___x_1037_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_1036_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_object* v_a_1038_; size_t v___x_1039_; size_t v___x_1040_; 
v_a_1038_ = lean_ctor_get(v___x_1037_, 0);
lean_inc(v_a_1038_);
lean_dec_ref_known(v___x_1037_, 1);
v___x_1039_ = ((size_t)1ULL);
v___x_1040_ = lean_usize_add(v_i_1026_, v___x_1039_);
v_i_1026_ = v___x_1040_;
v_b_1028_ = v_a_1038_;
goto _start;
}
else
{
return v___x_1037_;
}
}
else
{
lean_object* v___x_1042_; 
v___x_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1042_, 0, v_b_1028_);
return v___x_1042_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed_spec__0___boxed(lean_object* v_as_1043_, lean_object* v_i_1044_, lean_object* v_stop_1045_, lean_object* v_b_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
size_t v_i_boxed_1053_; size_t v_stop_boxed_1054_; lean_object* v_res_1055_; 
v_i_boxed_1053_ = lean_unbox_usize(v_i_1044_);
lean_dec(v_i_1044_);
v_stop_boxed_1054_ = lean_unbox_usize(v_stop_1045_);
lean_dec(v_stop_1045_);
v_res_1055_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed_spec__0(v_as_1043_, v_i_boxed_1053_, v_stop_boxed_1054_, v_b_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec_ref(v_as_1043_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed(lean_object* v_mvarId_1056_, lean_object* v_toPreserve_1057_, uint8_t v_indirectProps_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_){
_start:
{
lean_object* v___y_1066_; lean_object* v___x_1080_; 
v___x_1080_ = l_Lean_MVarId_getType(v_mvarId_1056_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v___x_1082_; lean_object* v_a_1083_; lean_object* v___x_1084_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
lean_inc(v_a_1081_);
lean_dec_ref_known(v___x_1080_, 1);
v___x_1082_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0___redArg(v_a_1081_, v_a_1061_);
v_a_1083_ = lean_ctor_get(v___x_1082_, 0);
lean_inc(v_a_1083_);
lean_dec_ref(v___x_1082_);
v___x_1084_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars(v_a_1083_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v___x_1085_; lean_object* v___x_1086_; uint8_t v___x_1087_; 
lean_dec_ref_known(v___x_1084_, 1);
v___x_1085_ = lean_unsigned_to_nat(0u);
v___x_1086_ = lean_array_get_size(v_toPreserve_1057_);
v___x_1087_ = lean_nat_dec_lt(v___x_1085_, v___x_1086_);
if (v___x_1087_ == 0)
{
goto v___jp_1070_;
}
else
{
lean_object* v___x_1088_; size_t v___x_1089_; size_t v___x_1090_; lean_object* v___x_1091_; 
v___x_1088_ = lean_box(0);
v___x_1089_ = ((size_t)0ULL);
v___x_1090_ = lean_usize_of_nat(v___x_1086_);
v___x_1091_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed_spec__0(v_toPreserve_1057_, v___x_1089_, v___x_1090_, v___x_1088_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_dec_ref_known(v___x_1091_, 1);
goto v___jp_1070_;
}
else
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1099_; 
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1094_ = v___x_1091_;
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_1091_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1097_; 
if (v_isShared_1095_ == 0)
{
v___x_1097_ = v___x_1094_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_a_1092_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
}
else
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
v_a_1100_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1084_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1084_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
v_a_1108_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___x_1080_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1080_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
v___jp_1065_:
{
lean_object* v___x_1067_; lean_object* v_snd_1068_; lean_object* v___x_1069_; 
v___x_1067_ = lean_st_ref_get(v___y_1066_);
v_snd_1068_ = lean_ctor_get(v___x_1067_, 1);
lean_inc(v_snd_1068_);
lean_dec(v___x_1067_);
v___x_1069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1069_, 0, v_snd_1068_);
return v___x_1069_;
}
v___jp_1070_:
{
if (v_indirectProps_1058_ == 0)
{
v___y_1066_ = v_a_1059_;
goto v___jp_1065_;
}
else
{
lean_object* v___x_1071_; 
v___x_1071_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectProps(v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_dec_ref_known(v___x_1071_, 1);
v___y_1066_ = v_a_1059_;
goto v___jp_1065_;
}
else
{
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1079_; 
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1074_ = v___x_1071_;
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_1071_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1077_; 
if (v_isShared_1075_ == 0)
{
v___x_1077_ = v___x_1074_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_a_1072_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed___boxed(lean_object* v_mvarId_1116_, lean_object* v_toPreserve_1117_, lean_object* v_indirectProps_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_){
_start:
{
uint8_t v_indirectProps_boxed_1125_; lean_object* v_res_1126_; 
v_indirectProps_boxed_1125_ = lean_unbox(v_indirectProps_1118_);
v_res_1126_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed(v_mvarId_1116_, v_toPreserve_1117_, v_indirectProps_boxed_1125_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_);
lean_dec(v_a_1123_);
lean_dec_ref(v_a_1122_);
lean_dec(v_a_1121_);
lean_dec_ref(v_a_1120_);
lean_dec(v_a_1119_);
lean_dec_ref(v_toPreserve_1117_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___redArg(lean_object* v_e_1127_, lean_object* v___y_1128_){
_start:
{
uint8_t v___x_1130_; 
v___x_1130_ = l_Lean_Expr_hasMVar(v_e_1127_);
if (v___x_1130_ == 0)
{
lean_object* v___x_1131_; 
v___x_1131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1131_, 0, v_e_1127_);
return v___x_1131_;
}
else
{
lean_object* v___x_1132_; lean_object* v_mctx_1133_; lean_object* v___x_1134_; lean_object* v_fst_1135_; lean_object* v_snd_1136_; lean_object* v___x_1137_; lean_object* v_cache_1138_; lean_object* v_zetaDeltaFVarIds_1139_; lean_object* v_postponed_1140_; lean_object* v_diag_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1150_; 
v___x_1132_ = lean_st_ref_get(v___y_1128_);
v_mctx_1133_ = lean_ctor_get(v___x_1132_, 0);
lean_inc_ref(v_mctx_1133_);
lean_dec(v___x_1132_);
v___x_1134_ = l_Lean_instantiateMVarsCore(v_mctx_1133_, v_e_1127_);
v_fst_1135_ = lean_ctor_get(v___x_1134_, 0);
lean_inc(v_fst_1135_);
v_snd_1136_ = lean_ctor_get(v___x_1134_, 1);
lean_inc(v_snd_1136_);
lean_dec_ref(v___x_1134_);
v___x_1137_ = lean_st_ref_take(v___y_1128_);
v_cache_1138_ = lean_ctor_get(v___x_1137_, 1);
v_zetaDeltaFVarIds_1139_ = lean_ctor_get(v___x_1137_, 2);
v_postponed_1140_ = lean_ctor_get(v___x_1137_, 3);
v_diag_1141_ = lean_ctor_get(v___x_1137_, 4);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1150_ == 0)
{
lean_object* v_unused_1151_; 
v_unused_1151_ = lean_ctor_get(v___x_1137_, 0);
lean_dec(v_unused_1151_);
v___x_1143_ = v___x_1137_;
v_isShared_1144_ = v_isSharedCheck_1150_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_diag_1141_);
lean_inc(v_postponed_1140_);
lean_inc(v_zetaDeltaFVarIds_1139_);
lean_inc(v_cache_1138_);
lean_dec(v___x_1137_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1150_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 0, v_snd_1136_);
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_snd_1136_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_cache_1138_);
lean_ctor_set(v_reuseFailAlloc_1149_, 2, v_zetaDeltaFVarIds_1139_);
lean_ctor_set(v_reuseFailAlloc_1149_, 3, v_postponed_1140_);
lean_ctor_set(v_reuseFailAlloc_1149_, 4, v_diag_1141_);
v___x_1146_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1147_ = lean_st_ref_put(v___y_1128_, v___x_1146_);
v___x_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1148_, 0, v_fst_1135_);
return v___x_1148_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___redArg___boxed(lean_object* v_e_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___redArg(v_e_1152_, v___y_1153_);
lean_dec(v___y_1153_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1(lean_object* v_e_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v___x_1162_; 
v___x_1162_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___redArg(v_e_1156_, v___y_1158_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___boxed(lean_object* v_e_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1(v_e_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___redArg(lean_object* v_mvarId_1170_, lean_object* v_x_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
lean_object* v___x_1177_; 
v___x_1177_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1170_, v_x_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v___x_1177_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1177_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1178_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
else
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1193_; 
v_a_1186_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1188_ = v___x_1177_;
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1177_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1191_; 
if (v_isShared_1189_ == 0)
{
v___x_1191_ = v___x_1188_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1186_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___redArg___boxed(lean_object* v_mvarId_1194_, lean_object* v_x_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___redArg(v_mvarId_1194_, v_x_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4(lean_object* v_00_u03b1_1202_, lean_object* v_mvarId_1203_, lean_object* v_x_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v___x_1210_; 
v___x_1210_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___redArg(v_mvarId_1203_, v_x_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___boxed(lean_object* v_00_u03b1_1211_, lean_object* v_mvarId_1212_, lean_object* v_x_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4(v_00_u03b1_1211_, v_mvarId_1212_, v_x_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__3(lean_object* v_a_1220_, lean_object* v_as_1221_, size_t v_i_1222_, size_t v_stop_1223_, lean_object* v_b_1224_){
_start:
{
lean_object* v___y_1226_; uint8_t v___x_1230_; 
v___x_1230_ = lean_usize_dec_eq(v_i_1222_, v_stop_1223_);
if (v___x_1230_ == 0)
{
lean_object* v___x_1231_; lean_object* v_fvar_1232_; lean_object* v___x_1233_; uint8_t v___x_1234_; 
v___x_1231_ = lean_array_uget_borrowed(v_as_1221_, v_i_1222_);
v_fvar_1232_ = lean_ctor_get(v___x_1231_, 1);
v___x_1233_ = l_Lean_Expr_fvarId_x21(v_fvar_1232_);
v___x_1234_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_1233_, v_a_1220_);
lean_dec(v___x_1233_);
if (v___x_1234_ == 0)
{
v___y_1226_ = v_b_1224_;
goto v___jp_1225_;
}
else
{
lean_object* v___x_1235_; 
lean_inc(v___x_1231_);
v___x_1235_ = lean_array_push(v_b_1224_, v___x_1231_);
v___y_1226_ = v___x_1235_;
goto v___jp_1225_;
}
}
else
{
return v_b_1224_;
}
v___jp_1225_:
{
size_t v___x_1227_; size_t v___x_1228_; 
v___x_1227_ = ((size_t)1ULL);
v___x_1228_ = lean_usize_add(v_i_1222_, v___x_1227_);
v_i_1222_ = v___x_1228_;
v_b_1224_ = v___y_1226_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__3___boxed(lean_object* v_a_1236_, lean_object* v_as_1237_, lean_object* v_i_1238_, lean_object* v_stop_1239_, lean_object* v_b_1240_){
_start:
{
size_t v_i_boxed_1241_; size_t v_stop_boxed_1242_; lean_object* v_res_1243_; 
v_i_boxed_1241_ = lean_unbox_usize(v_i_1238_);
lean_dec(v_i_1238_);
v_stop_boxed_1242_ = lean_unbox_usize(v_stop_1239_);
lean_dec(v_stop_1239_);
v_res_1243_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__3(v_a_1236_, v_as_1237_, v_i_boxed_1241_, v_stop_boxed_1242_, v_b_1240_);
lean_dec_ref(v_as_1237_);
lean_dec(v_a_1236_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12_spec__13___redArg(lean_object* v_x_1244_, lean_object* v_x_1245_, lean_object* v_x_1246_, lean_object* v_x_1247_){
_start:
{
lean_object* v_ks_1248_; lean_object* v_vs_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1273_; 
v_ks_1248_ = lean_ctor_get(v_x_1244_, 0);
v_vs_1249_ = lean_ctor_get(v_x_1244_, 1);
v_isSharedCheck_1273_ = !lean_is_exclusive(v_x_1244_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1251_ = v_x_1244_;
v_isShared_1252_ = v_isSharedCheck_1273_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_vs_1249_);
lean_inc(v_ks_1248_);
lean_dec(v_x_1244_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1273_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1253_; uint8_t v___x_1254_; 
v___x_1253_ = lean_array_get_size(v_ks_1248_);
v___x_1254_ = lean_nat_dec_lt(v_x_1245_, v___x_1253_);
if (v___x_1254_ == 0)
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1258_; 
lean_dec(v_x_1245_);
v___x_1255_ = lean_array_push(v_ks_1248_, v_x_1246_);
v___x_1256_ = lean_array_push(v_vs_1249_, v_x_1247_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 1, v___x_1256_);
lean_ctor_set(v___x_1251_, 0, v___x_1255_);
v___x_1258_ = v___x_1251_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v___x_1255_);
lean_ctor_set(v_reuseFailAlloc_1259_, 1, v___x_1256_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
else
{
lean_object* v_k_x27_1260_; uint8_t v___x_1261_; 
v_k_x27_1260_ = lean_array_fget_borrowed(v_ks_1248_, v_x_1245_);
v___x_1261_ = l_Lean_instBEqMVarId_beq(v_x_1246_, v_k_x27_1260_);
if (v___x_1261_ == 0)
{
lean_object* v___x_1263_; 
if (v_isShared_1252_ == 0)
{
v___x_1263_ = v___x_1251_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_ks_1248_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v_vs_1249_);
v___x_1263_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1264_ = lean_unsigned_to_nat(1u);
v___x_1265_ = lean_nat_add(v_x_1245_, v___x_1264_);
lean_dec(v_x_1245_);
v_x_1244_ = v___x_1263_;
v_x_1245_ = v___x_1265_;
goto _start;
}
}
else
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1271_; 
v___x_1268_ = lean_array_fset(v_ks_1248_, v_x_1245_, v_x_1246_);
v___x_1269_ = lean_array_fset(v_vs_1249_, v_x_1245_, v_x_1247_);
lean_dec(v_x_1245_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 1, v___x_1269_);
lean_ctor_set(v___x_1251_, 0, v___x_1268_);
v___x_1271_ = v___x_1251_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___x_1268_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v___x_1269_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12___redArg(lean_object* v_n_1274_, lean_object* v_k_1275_, lean_object* v_v_1276_){
_start:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1277_ = lean_unsigned_to_nat(0u);
v___x_1278_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12_spec__13___redArg(v_n_1274_, v___x_1277_, v_k_1275_, v_v_1276_);
return v___x_1278_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1279_; 
v___x_1279_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg(lean_object* v_x_1280_, size_t v_x_1281_, size_t v_x_1282_, lean_object* v_x_1283_, lean_object* v_x_1284_){
_start:
{
if (lean_obj_tag(v_x_1280_) == 0)
{
lean_object* v_es_1285_; size_t v___x_1286_; size_t v___x_1287_; lean_object* v_j_1288_; lean_object* v___x_1289_; uint8_t v___x_1290_; 
v_es_1285_ = lean_ctor_get(v_x_1280_, 0);
v___x_1286_ = ((size_t)31ULL);
v___x_1287_ = lean_usize_land(v_x_1281_, v___x_1286_);
v_j_1288_ = lean_usize_to_nat(v___x_1287_);
v___x_1289_ = lean_array_get_size(v_es_1285_);
v___x_1290_ = lean_nat_dec_lt(v_j_1288_, v___x_1289_);
if (v___x_1290_ == 0)
{
lean_dec(v_j_1288_);
lean_dec(v_x_1284_);
lean_dec(v_x_1283_);
return v_x_1280_;
}
else
{
lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1329_; 
lean_inc_ref(v_es_1285_);
v_isSharedCheck_1329_ = !lean_is_exclusive(v_x_1280_);
if (v_isSharedCheck_1329_ == 0)
{
lean_object* v_unused_1330_; 
v_unused_1330_ = lean_ctor_get(v_x_1280_, 0);
lean_dec(v_unused_1330_);
v___x_1292_ = v_x_1280_;
v_isShared_1293_ = v_isSharedCheck_1329_;
goto v_resetjp_1291_;
}
else
{
lean_dec(v_x_1280_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1329_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v_v_1294_; lean_object* v___x_1295_; lean_object* v_xs_x27_1296_; lean_object* v___y_1298_; 
v_v_1294_ = lean_array_fget(v_es_1285_, v_j_1288_);
v___x_1295_ = lean_box(0);
v_xs_x27_1296_ = lean_array_fset(v_es_1285_, v_j_1288_, v___x_1295_);
switch(lean_obj_tag(v_v_1294_))
{
case 0:
{
lean_object* v_key_1303_; lean_object* v_val_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1314_; 
v_key_1303_ = lean_ctor_get(v_v_1294_, 0);
v_val_1304_ = lean_ctor_get(v_v_1294_, 1);
v_isSharedCheck_1314_ = !lean_is_exclusive(v_v_1294_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1306_ = v_v_1294_;
v_isShared_1307_ = v_isSharedCheck_1314_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_val_1304_);
lean_inc(v_key_1303_);
lean_dec(v_v_1294_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1314_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
uint8_t v___x_1308_; 
v___x_1308_ = l_Lean_instBEqMVarId_beq(v_x_1283_, v_key_1303_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
lean_del_object(v___x_1306_);
v___x_1309_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1303_, v_val_1304_, v_x_1283_, v_x_1284_);
v___x_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1309_);
v___y_1298_ = v___x_1310_;
goto v___jp_1297_;
}
else
{
lean_object* v___x_1312_; 
lean_dec(v_val_1304_);
lean_dec(v_key_1303_);
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 1, v_x_1284_);
lean_ctor_set(v___x_1306_, 0, v_x_1283_);
v___x_1312_ = v___x_1306_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_x_1283_);
lean_ctor_set(v_reuseFailAlloc_1313_, 1, v_x_1284_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
v___y_1298_ = v___x_1312_;
goto v___jp_1297_;
}
}
}
}
case 1:
{
lean_object* v_node_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1327_; 
v_node_1315_ = lean_ctor_get(v_v_1294_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v_v_1294_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1317_ = v_v_1294_;
v_isShared_1318_ = v_isSharedCheck_1327_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_node_1315_);
lean_dec(v_v_1294_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1327_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
size_t v___x_1319_; size_t v___x_1320_; size_t v___x_1321_; size_t v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1325_; 
v___x_1319_ = ((size_t)5ULL);
v___x_1320_ = lean_usize_shift_right(v_x_1281_, v___x_1319_);
v___x_1321_ = ((size_t)1ULL);
v___x_1322_ = lean_usize_add(v_x_1282_, v___x_1321_);
v___x_1323_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg(v_node_1315_, v___x_1320_, v___x_1322_, v_x_1283_, v_x_1284_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 0, v___x_1323_);
v___x_1325_ = v___x_1317_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v___x_1323_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
v___y_1298_ = v___x_1325_;
goto v___jp_1297_;
}
}
}
default: 
{
lean_object* v___x_1328_; 
v___x_1328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1328_, 0, v_x_1283_);
lean_ctor_set(v___x_1328_, 1, v_x_1284_);
v___y_1298_ = v___x_1328_;
goto v___jp_1297_;
}
}
v___jp_1297_:
{
lean_object* v___x_1299_; lean_object* v___x_1301_; 
v___x_1299_ = lean_array_fset(v_xs_x27_1296_, v_j_1288_, v___y_1298_);
lean_dec(v_j_1288_);
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 0, v___x_1299_);
v___x_1301_ = v___x_1292_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___x_1299_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
}
else
{
lean_object* v_ks_1331_; lean_object* v_vs_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1350_; 
v_ks_1331_ = lean_ctor_get(v_x_1280_, 0);
v_vs_1332_ = lean_ctor_get(v_x_1280_, 1);
v_isSharedCheck_1350_ = !lean_is_exclusive(v_x_1280_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1334_ = v_x_1280_;
v_isShared_1335_ = v_isSharedCheck_1350_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_vs_1332_);
lean_inc(v_ks_1331_);
lean_dec(v_x_1280_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1350_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1337_; 
if (v_isShared_1335_ == 0)
{
v___x_1337_ = v___x_1334_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_ks_1331_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v_vs_1332_);
v___x_1337_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
lean_object* v_newNode_1338_; size_t v___x_1339_; uint8_t v___x_1340_; 
v_newNode_1338_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12___redArg(v___x_1337_, v_x_1283_, v_x_1284_);
v___x_1339_ = ((size_t)7ULL);
v___x_1340_ = lean_usize_dec_le(v___x_1339_, v_x_1282_);
if (v___x_1340_ == 0)
{
lean_object* v___x_1341_; lean_object* v___x_1342_; uint8_t v___x_1343_; 
v___x_1341_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1338_);
v___x_1342_ = lean_unsigned_to_nat(4u);
v___x_1343_ = lean_nat_dec_lt(v___x_1341_, v___x_1342_);
lean_dec(v___x_1341_);
if (v___x_1343_ == 0)
{
lean_object* v_ks_1344_; lean_object* v_vs_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v_ks_1344_ = lean_ctor_get(v_newNode_1338_, 0);
lean_inc_ref(v_ks_1344_);
v_vs_1345_ = lean_ctor_get(v_newNode_1338_, 1);
lean_inc_ref(v_vs_1345_);
lean_dec_ref(v_newNode_1338_);
v___x_1346_ = lean_unsigned_to_nat(0u);
v___x_1347_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__0);
v___x_1348_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___redArg(v_x_1282_, v_ks_1344_, v_vs_1345_, v___x_1346_, v___x_1347_);
lean_dec_ref(v_vs_1345_);
lean_dec_ref(v_ks_1344_);
return v___x_1348_;
}
else
{
return v_newNode_1338_;
}
}
else
{
return v_newNode_1338_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___redArg(size_t v_depth_1351_, lean_object* v_keys_1352_, lean_object* v_vals_1353_, lean_object* v_i_1354_, lean_object* v_entries_1355_){
_start:
{
lean_object* v___x_1356_; uint8_t v___x_1357_; 
v___x_1356_ = lean_array_get_size(v_keys_1352_);
v___x_1357_ = lean_nat_dec_lt(v_i_1354_, v___x_1356_);
if (v___x_1357_ == 0)
{
lean_dec(v_i_1354_);
return v_entries_1355_;
}
else
{
lean_object* v_k_1358_; lean_object* v_v_1359_; uint64_t v___x_1360_; size_t v_h_1361_; size_t v___x_1362_; lean_object* v___x_1363_; size_t v___x_1364_; size_t v___x_1365_; size_t v___x_1366_; size_t v_h_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
v_k_1358_ = lean_array_fget_borrowed(v_keys_1352_, v_i_1354_);
v_v_1359_ = lean_array_fget_borrowed(v_vals_1353_, v_i_1354_);
v___x_1360_ = l_Lean_instHashableMVarId_hash(v_k_1358_);
v_h_1361_ = lean_uint64_to_usize(v___x_1360_);
v___x_1362_ = ((size_t)5ULL);
v___x_1363_ = lean_unsigned_to_nat(1u);
v___x_1364_ = ((size_t)1ULL);
v___x_1365_ = lean_usize_sub(v_depth_1351_, v___x_1364_);
v___x_1366_ = lean_usize_mul(v___x_1362_, v___x_1365_);
v_h_1367_ = lean_usize_shift_right(v_h_1361_, v___x_1366_);
v___x_1368_ = lean_nat_add(v_i_1354_, v___x_1363_);
lean_dec(v_i_1354_);
lean_inc(v_v_1359_);
lean_inc(v_k_1358_);
v___x_1369_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg(v_entries_1355_, v_h_1367_, v_depth_1351_, v_k_1358_, v_v_1359_);
v_i_1354_ = v___x_1368_;
v_entries_1355_ = v___x_1369_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___redArg___boxed(lean_object* v_depth_1371_, lean_object* v_keys_1372_, lean_object* v_vals_1373_, lean_object* v_i_1374_, lean_object* v_entries_1375_){
_start:
{
size_t v_depth_boxed_1376_; lean_object* v_res_1377_; 
v_depth_boxed_1376_ = lean_unbox_usize(v_depth_1371_);
lean_dec(v_depth_1371_);
v_res_1377_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___redArg(v_depth_boxed_1376_, v_keys_1372_, v_vals_1373_, v_i_1374_, v_entries_1375_);
lean_dec_ref(v_vals_1373_);
lean_dec_ref(v_keys_1372_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___boxed(lean_object* v_x_1378_, lean_object* v_x_1379_, lean_object* v_x_1380_, lean_object* v_x_1381_, lean_object* v_x_1382_){
_start:
{
size_t v_x_7412__boxed_1383_; size_t v_x_7413__boxed_1384_; lean_object* v_res_1385_; 
v_x_7412__boxed_1383_ = lean_unbox_usize(v_x_1379_);
lean_dec(v_x_1379_);
v_x_7413__boxed_1384_ = lean_unbox_usize(v_x_1380_);
lean_dec(v_x_1380_);
v_res_1385_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg(v_x_1378_, v_x_7412__boxed_1383_, v_x_7413__boxed_1384_, v_x_1381_, v_x_1382_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4___redArg(lean_object* v_x_1386_, lean_object* v_x_1387_, lean_object* v_x_1388_){
_start:
{
uint64_t v___x_1389_; size_t v___x_1390_; size_t v___x_1391_; lean_object* v___x_1392_; 
v___x_1389_ = l_Lean_instHashableMVarId_hash(v_x_1387_);
v___x_1390_ = lean_uint64_to_usize(v___x_1389_);
v___x_1391_ = ((size_t)1ULL);
v___x_1392_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg(v_x_1386_, v___x_1390_, v___x_1391_, v_x_1387_, v_x_1388_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___redArg(lean_object* v_mvarId_1393_, lean_object* v_val_1394_, lean_object* v___y_1395_){
_start:
{
lean_object* v___x_1397_; lean_object* v_mctx_1398_; lean_object* v_cache_1399_; lean_object* v_zetaDeltaFVarIds_1400_; lean_object* v_postponed_1401_; lean_object* v_diag_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1432_; 
v___x_1397_ = lean_st_ref_take(v___y_1395_);
v_mctx_1398_ = lean_ctor_get(v___x_1397_, 0);
v_cache_1399_ = lean_ctor_get(v___x_1397_, 1);
v_zetaDeltaFVarIds_1400_ = lean_ctor_get(v___x_1397_, 2);
v_postponed_1401_ = lean_ctor_get(v___x_1397_, 3);
v_diag_1402_ = lean_ctor_get(v___x_1397_, 4);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1404_ = v___x_1397_;
v_isShared_1405_ = v_isSharedCheck_1432_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_diag_1402_);
lean_inc(v_postponed_1401_);
lean_inc(v_zetaDeltaFVarIds_1400_);
lean_inc(v_cache_1399_);
lean_inc(v_mctx_1398_);
lean_dec(v___x_1397_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1432_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v_depth_1406_; lean_object* v_levelAssignDepth_1407_; lean_object* v_lmvarCounter_1408_; lean_object* v_mvarCounter_1409_; lean_object* v_lDecls_1410_; lean_object* v_decls_1411_; lean_object* v_userNames_1412_; lean_object* v_lAssignment_1413_; lean_object* v_eAssignment_1414_; lean_object* v_dAssignment_1415_; lean_object* v_instanceTypedMVars_1416_; lean_object* v_synthNormMemo_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1431_; 
v_depth_1406_ = lean_ctor_get(v_mctx_1398_, 0);
v_levelAssignDepth_1407_ = lean_ctor_get(v_mctx_1398_, 1);
v_lmvarCounter_1408_ = lean_ctor_get(v_mctx_1398_, 2);
v_mvarCounter_1409_ = lean_ctor_get(v_mctx_1398_, 3);
v_lDecls_1410_ = lean_ctor_get(v_mctx_1398_, 4);
v_decls_1411_ = lean_ctor_get(v_mctx_1398_, 5);
v_userNames_1412_ = lean_ctor_get(v_mctx_1398_, 6);
v_lAssignment_1413_ = lean_ctor_get(v_mctx_1398_, 7);
v_eAssignment_1414_ = lean_ctor_get(v_mctx_1398_, 8);
v_dAssignment_1415_ = lean_ctor_get(v_mctx_1398_, 9);
v_instanceTypedMVars_1416_ = lean_ctor_get(v_mctx_1398_, 10);
v_synthNormMemo_1417_ = lean_ctor_get(v_mctx_1398_, 11);
v_isSharedCheck_1431_ = !lean_is_exclusive(v_mctx_1398_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1419_ = v_mctx_1398_;
v_isShared_1420_ = v_isSharedCheck_1431_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_synthNormMemo_1417_);
lean_inc(v_instanceTypedMVars_1416_);
lean_inc(v_dAssignment_1415_);
lean_inc(v_eAssignment_1414_);
lean_inc(v_lAssignment_1413_);
lean_inc(v_userNames_1412_);
lean_inc(v_decls_1411_);
lean_inc(v_lDecls_1410_);
lean_inc(v_mvarCounter_1409_);
lean_inc(v_lmvarCounter_1408_);
lean_inc(v_levelAssignDepth_1407_);
lean_inc(v_depth_1406_);
lean_dec(v_mctx_1398_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1431_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1424_; 
v___x_1421_ = lean_box(0);
v___x_1422_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4___redArg(v_eAssignment_1414_, v_mvarId_1393_, v_val_1394_);
if (v_isShared_1420_ == 0)
{
lean_ctor_set(v___x_1419_, 8, v___x_1422_);
v___x_1424_ = v___x_1419_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_depth_1406_);
lean_ctor_set(v_reuseFailAlloc_1430_, 1, v_levelAssignDepth_1407_);
lean_ctor_set(v_reuseFailAlloc_1430_, 2, v_lmvarCounter_1408_);
lean_ctor_set(v_reuseFailAlloc_1430_, 3, v_mvarCounter_1409_);
lean_ctor_set(v_reuseFailAlloc_1430_, 4, v_lDecls_1410_);
lean_ctor_set(v_reuseFailAlloc_1430_, 5, v_decls_1411_);
lean_ctor_set(v_reuseFailAlloc_1430_, 6, v_userNames_1412_);
lean_ctor_set(v_reuseFailAlloc_1430_, 7, v_lAssignment_1413_);
lean_ctor_set(v_reuseFailAlloc_1430_, 8, v___x_1422_);
lean_ctor_set(v_reuseFailAlloc_1430_, 9, v_dAssignment_1415_);
lean_ctor_set(v_reuseFailAlloc_1430_, 10, v_instanceTypedMVars_1416_);
lean_ctor_set(v_reuseFailAlloc_1430_, 11, v_synthNormMemo_1417_);
v___x_1424_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
lean_object* v___x_1426_; 
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 0, v___x_1424_);
v___x_1426_ = v___x_1404_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v___x_1424_);
lean_ctor_set(v_reuseFailAlloc_1429_, 1, v_cache_1399_);
lean_ctor_set(v_reuseFailAlloc_1429_, 2, v_zetaDeltaFVarIds_1400_);
lean_ctor_set(v_reuseFailAlloc_1429_, 3, v_postponed_1401_);
lean_ctor_set(v_reuseFailAlloc_1429_, 4, v_diag_1402_);
v___x_1426_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1427_ = lean_st_ref_put(v___y_1395_, v___x_1426_);
v___x_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1421_);
return v___x_1428_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___redArg___boxed(lean_object* v_mvarId_1433_, lean_object* v_val_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___redArg(v_mvarId_1433_, v_val_1434_, v___y_1435_);
lean_dec(v___y_1435_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___redArg(lean_object* v_a_1438_, lean_object* v_as_1439_, size_t v_sz_1440_, size_t v_i_1441_, lean_object* v_b_1442_){
_start:
{
uint8_t v___x_1444_; 
v___x_1444_ = lean_usize_dec_lt(v_i_1441_, v_sz_1440_);
if (v___x_1444_ == 0)
{
lean_object* v___x_1445_; 
v___x_1445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1445_, 0, v_b_1442_);
return v___x_1445_;
}
else
{
lean_object* v_snd_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1464_; 
v_snd_1446_ = lean_ctor_get(v_b_1442_, 1);
v_isSharedCheck_1464_ = !lean_is_exclusive(v_b_1442_);
if (v_isSharedCheck_1464_ == 0)
{
lean_object* v_unused_1465_; 
v_unused_1465_ = lean_ctor_get(v_b_1442_, 0);
lean_dec(v_unused_1465_);
v___x_1448_ = v_b_1442_;
v_isShared_1449_ = v_isSharedCheck_1464_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_snd_1446_);
lean_dec(v_b_1442_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1464_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1450_; lean_object* v_a_1452_; lean_object* v_a_1459_; 
v___x_1450_ = lean_box(0);
v_a_1459_ = lean_array_uget_borrowed(v_as_1439_, v_i_1441_);
if (lean_obj_tag(v_a_1459_) == 0)
{
v_a_1452_ = v_snd_1446_;
goto v___jp_1451_;
}
else
{
lean_object* v_val_1460_; lean_object* v___x_1461_; uint8_t v___x_1462_; 
v_val_1460_ = lean_ctor_get(v_a_1459_, 0);
v___x_1461_ = l_Lean_LocalDecl_fvarId(v_val_1460_);
v___x_1462_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_1461_, v_a_1438_);
if (v___x_1462_ == 0)
{
lean_object* v___x_1463_; 
v___x_1463_ = l_Lean_LocalContext_erase(v_snd_1446_, v___x_1461_);
lean_dec(v___x_1461_);
v_a_1452_ = v___x_1463_;
goto v___jp_1451_;
}
else
{
lean_dec(v___x_1461_);
v_a_1452_ = v_snd_1446_;
goto v___jp_1451_;
}
}
v___jp_1451_:
{
lean_object* v___x_1454_; 
if (v_isShared_1449_ == 0)
{
lean_ctor_set(v___x_1448_, 1, v_a_1452_);
lean_ctor_set(v___x_1448_, 0, v___x_1450_);
v___x_1454_ = v___x_1448_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___x_1450_);
lean_ctor_set(v_reuseFailAlloc_1458_, 1, v_a_1452_);
v___x_1454_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
size_t v___x_1455_; size_t v___x_1456_; 
v___x_1455_ = ((size_t)1ULL);
v___x_1456_ = lean_usize_add(v_i_1441_, v___x_1455_);
v_i_1441_ = v___x_1456_;
v_b_1442_ = v___x_1454_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___redArg___boxed(lean_object* v_a_1466_, lean_object* v_as_1467_, lean_object* v_sz_1468_, lean_object* v_i_1469_, lean_object* v_b_1470_, lean_object* v___y_1471_){
_start:
{
size_t v_sz_boxed_1472_; size_t v_i_boxed_1473_; lean_object* v_res_1474_; 
v_sz_boxed_1472_ = lean_unbox_usize(v_sz_1468_);
lean_dec(v_sz_1468_);
v_i_boxed_1473_ = lean_unbox_usize(v_i_1469_);
lean_dec(v_i_1469_);
v_res_1474_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___redArg(v_a_1466_, v_as_1467_, v_sz_boxed_1472_, v_i_boxed_1473_, v_b_1470_);
lean_dec_ref(v_as_1467_);
lean_dec(v_a_1466_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4(lean_object* v_a_1475_, lean_object* v_as_1476_, size_t v_sz_1477_, size_t v_i_1478_, lean_object* v_b_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
uint8_t v___x_1485_; 
v___x_1485_ = lean_usize_dec_lt(v_i_1478_, v_sz_1477_);
if (v___x_1485_ == 0)
{
lean_object* v___x_1486_; 
v___x_1486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1486_, 0, v_b_1479_);
return v___x_1486_;
}
else
{
lean_object* v_snd_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1505_; 
v_snd_1487_ = lean_ctor_get(v_b_1479_, 1);
v_isSharedCheck_1505_ = !lean_is_exclusive(v_b_1479_);
if (v_isSharedCheck_1505_ == 0)
{
lean_object* v_unused_1506_; 
v_unused_1506_ = lean_ctor_get(v_b_1479_, 0);
lean_dec(v_unused_1506_);
v___x_1489_ = v_b_1479_;
v_isShared_1490_ = v_isSharedCheck_1505_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_snd_1487_);
lean_dec(v_b_1479_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1505_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1491_; lean_object* v_a_1493_; lean_object* v_a_1500_; 
v___x_1491_ = lean_box(0);
v_a_1500_ = lean_array_uget_borrowed(v_as_1476_, v_i_1478_);
if (lean_obj_tag(v_a_1500_) == 0)
{
v_a_1493_ = v_snd_1487_;
goto v___jp_1492_;
}
else
{
lean_object* v_val_1501_; lean_object* v___x_1502_; uint8_t v___x_1503_; 
v_val_1501_ = lean_ctor_get(v_a_1500_, 0);
v___x_1502_ = l_Lean_LocalDecl_fvarId(v_val_1501_);
v___x_1503_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_1502_, v_a_1475_);
if (v___x_1503_ == 0)
{
lean_object* v___x_1504_; 
v___x_1504_ = l_Lean_LocalContext_erase(v_snd_1487_, v___x_1502_);
lean_dec(v___x_1502_);
v_a_1493_ = v___x_1504_;
goto v___jp_1492_;
}
else
{
lean_dec(v___x_1502_);
v_a_1493_ = v_snd_1487_;
goto v___jp_1492_;
}
}
v___jp_1492_:
{
lean_object* v___x_1495_; 
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 1, v_a_1493_);
lean_ctor_set(v___x_1489_, 0, v___x_1491_);
v___x_1495_ = v___x_1489_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v___x_1491_);
lean_ctor_set(v_reuseFailAlloc_1499_, 1, v_a_1493_);
v___x_1495_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
size_t v___x_1496_; size_t v___x_1497_; lean_object* v___x_1498_; 
v___x_1496_ = ((size_t)1ULL);
v___x_1497_ = lean_usize_add(v_i_1478_, v___x_1496_);
v___x_1498_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___redArg(v_a_1475_, v_as_1476_, v_sz_1477_, v___x_1497_, v___x_1495_);
return v___x_1498_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4___boxed(lean_object* v_a_1507_, lean_object* v_as_1508_, lean_object* v_sz_1509_, lean_object* v_i_1510_, lean_object* v_b_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_){
_start:
{
size_t v_sz_boxed_1517_; size_t v_i_boxed_1518_; lean_object* v_res_1519_; 
v_sz_boxed_1517_ = lean_unbox_usize(v_sz_1509_);
lean_dec(v_sz_1509_);
v_i_boxed_1518_ = lean_unbox_usize(v_i_1510_);
lean_dec(v_i_1510_);
v_res_1519_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4(v_a_1507_, v_as_1508_, v_sz_boxed_1517_, v_i_boxed_1518_, v_b_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
lean_dec_ref(v_as_1508_);
lean_dec(v_a_1507_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0(lean_object* v_init_1520_, lean_object* v_a_1521_, lean_object* v_n_1522_, lean_object* v_b_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
if (lean_obj_tag(v_n_1522_) == 0)
{
lean_object* v_cs_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; size_t v_sz_1532_; size_t v___x_1533_; lean_object* v___x_1534_; 
v_cs_1529_ = lean_ctor_get(v_n_1522_, 0);
v___x_1530_ = lean_box(0);
v___x_1531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1530_);
lean_ctor_set(v___x_1531_, 1, v_b_1523_);
v_sz_1532_ = lean_array_size(v_cs_1529_);
v___x_1533_ = ((size_t)0ULL);
v___x_1534_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__3(v_init_1520_, v_a_1521_, v_cs_1529_, v_sz_1532_, v___x_1533_, v___x_1531_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1549_; 
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1537_ = v___x_1534_;
v_isShared_1538_ = v_isSharedCheck_1549_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v___x_1534_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1549_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v_fst_1539_; 
v_fst_1539_ = lean_ctor_get(v_a_1535_, 0);
if (lean_obj_tag(v_fst_1539_) == 0)
{
lean_object* v_snd_1540_; lean_object* v___x_1541_; lean_object* v___x_1543_; 
v_snd_1540_ = lean_ctor_get(v_a_1535_, 1);
lean_inc(v_snd_1540_);
lean_dec(v_a_1535_);
v___x_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1541_, 0, v_snd_1540_);
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 0, v___x_1541_);
v___x_1543_ = v___x_1537_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1541_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
else
{
lean_object* v_val_1545_; lean_object* v___x_1547_; 
lean_inc_ref(v_fst_1539_);
lean_dec(v_a_1535_);
v_val_1545_ = lean_ctor_get(v_fst_1539_, 0);
lean_inc(v_val_1545_);
lean_dec_ref_known(v_fst_1539_, 1);
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 0, v_val_1545_);
v___x_1547_ = v___x_1537_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_val_1545_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
}
}
else
{
lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1557_; 
v_a_1550_ = lean_ctor_get(v___x_1534_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1552_ = v___x_1534_;
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v___x_1534_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1555_; 
if (v_isShared_1553_ == 0)
{
v___x_1555_ = v___x_1552_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_a_1550_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
}
else
{
lean_object* v_vs_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; size_t v_sz_1561_; size_t v___x_1562_; lean_object* v___x_1563_; 
v_vs_1558_ = lean_ctor_get(v_n_1522_, 0);
v___x_1559_ = lean_box(0);
v___x_1560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1559_);
lean_ctor_set(v___x_1560_, 1, v_b_1523_);
v_sz_1561_ = lean_array_size(v_vs_1558_);
v___x_1562_ = ((size_t)0ULL);
v___x_1563_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4(v_a_1521_, v_vs_1558_, v_sz_1561_, v___x_1562_, v___x_1560_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1578_; 
v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1566_ = v___x_1563_;
v_isShared_1567_ = v_isSharedCheck_1578_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1563_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1578_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v_fst_1568_; 
v_fst_1568_ = lean_ctor_get(v_a_1564_, 0);
if (lean_obj_tag(v_fst_1568_) == 0)
{
lean_object* v_snd_1569_; lean_object* v___x_1570_; lean_object* v___x_1572_; 
v_snd_1569_ = lean_ctor_get(v_a_1564_, 1);
lean_inc(v_snd_1569_);
lean_dec(v_a_1564_);
v___x_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1570_, 0, v_snd_1569_);
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 0, v___x_1570_);
v___x_1572_ = v___x_1566_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v___x_1570_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
else
{
lean_object* v_val_1574_; lean_object* v___x_1576_; 
lean_inc_ref(v_fst_1568_);
lean_dec(v_a_1564_);
v_val_1574_ = lean_ctor_get(v_fst_1568_, 0);
lean_inc(v_val_1574_);
lean_dec_ref_known(v_fst_1568_, 1);
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 0, v_val_1574_);
v___x_1576_ = v___x_1566_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_val_1574_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
}
else
{
lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1586_; 
v_a_1579_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1581_ = v___x_1563_;
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_a_1579_);
lean_dec(v___x_1563_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1584_; 
if (v_isShared_1582_ == 0)
{
v___x_1584_ = v___x_1581_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_a_1579_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__3(lean_object* v_init_1587_, lean_object* v_a_1588_, lean_object* v_as_1589_, size_t v_sz_1590_, size_t v_i_1591_, lean_object* v_b_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
uint8_t v___x_1598_; 
v___x_1598_ = lean_usize_dec_lt(v_i_1591_, v_sz_1590_);
if (v___x_1598_ == 0)
{
lean_object* v___x_1599_; 
v___x_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1599_, 0, v_b_1592_);
return v___x_1599_;
}
else
{
lean_object* v_snd_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1634_; 
v_snd_1600_ = lean_ctor_get(v_b_1592_, 1);
v_isSharedCheck_1634_ = !lean_is_exclusive(v_b_1592_);
if (v_isSharedCheck_1634_ == 0)
{
lean_object* v_unused_1635_; 
v_unused_1635_ = lean_ctor_get(v_b_1592_, 0);
lean_dec(v_unused_1635_);
v___x_1602_ = v_b_1592_;
v_isShared_1603_ = v_isSharedCheck_1634_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_snd_1600_);
lean_dec(v_b_1592_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1634_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1604_; lean_object* v_a_1605_; lean_object* v___x_1606_; 
v___x_1604_ = lean_box(0);
v_a_1605_ = lean_array_uget_borrowed(v_as_1589_, v_i_1591_);
lean_inc(v_snd_1600_);
v___x_1606_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0(v_init_1587_, v_a_1588_, v_a_1605_, v_snd_1600_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_);
if (lean_obj_tag(v___x_1606_) == 0)
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1625_; 
v_a_1607_ = lean_ctor_get(v___x_1606_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1609_ = v___x_1606_;
v_isShared_1610_ = v_isSharedCheck_1625_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1606_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1625_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
if (lean_obj_tag(v_a_1607_) == 0)
{
lean_object* v___x_1611_; lean_object* v___x_1613_; 
v___x_1611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1611_, 0, v_a_1607_);
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 0, v___x_1611_);
v___x_1613_ = v___x_1602_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v___x_1611_);
lean_ctor_set(v_reuseFailAlloc_1617_, 1, v_snd_1600_);
v___x_1613_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
lean_object* v___x_1615_; 
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 0, v___x_1613_);
v___x_1615_ = v___x_1609_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v___x_1613_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
else
{
lean_object* v_a_1618_; lean_object* v___x_1620_; 
lean_del_object(v___x_1609_);
lean_dec(v_snd_1600_);
v_a_1618_ = lean_ctor_get(v_a_1607_, 0);
lean_inc(v_a_1618_);
lean_dec_ref_known(v_a_1607_, 1);
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 1, v_a_1618_);
lean_ctor_set(v___x_1602_, 0, v___x_1604_);
v___x_1620_ = v___x_1602_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v___x_1604_);
lean_ctor_set(v_reuseFailAlloc_1624_, 1, v_a_1618_);
v___x_1620_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
size_t v___x_1621_; size_t v___x_1622_; 
v___x_1621_ = ((size_t)1ULL);
v___x_1622_ = lean_usize_add(v_i_1591_, v___x_1621_);
v_i_1591_ = v___x_1622_;
v_b_1592_ = v___x_1620_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1633_; 
lean_del_object(v___x_1602_);
lean_dec(v_snd_1600_);
v_a_1626_ = lean_ctor_get(v___x_1606_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1628_ = v___x_1606_;
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1606_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1631_; 
if (v_isShared_1629_ == 0)
{
v___x_1631_ = v___x_1628_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_a_1626_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__3___boxed(lean_object* v_init_1636_, lean_object* v_a_1637_, lean_object* v_as_1638_, lean_object* v_sz_1639_, lean_object* v_i_1640_, lean_object* v_b_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
size_t v_sz_boxed_1647_; size_t v_i_boxed_1648_; lean_object* v_res_1649_; 
v_sz_boxed_1647_ = lean_unbox_usize(v_sz_1639_);
lean_dec(v_sz_1639_);
v_i_boxed_1648_ = lean_unbox_usize(v_i_1640_);
lean_dec(v_i_1640_);
v_res_1649_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__3(v_init_1636_, v_a_1637_, v_as_1638_, v_sz_boxed_1647_, v_i_boxed_1648_, v_b_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec_ref(v_as_1638_);
lean_dec(v_a_1637_);
lean_dec_ref(v_init_1636_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0___boxed(lean_object* v_init_1650_, lean_object* v_a_1651_, lean_object* v_n_1652_, lean_object* v_b_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0(v_init_1650_, v_a_1651_, v_n_1652_, v_b_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_);
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1656_);
lean_dec(v___y_1655_);
lean_dec_ref(v___y_1654_);
lean_dec_ref(v_n_1652_);
lean_dec(v_a_1651_);
lean_dec_ref(v_init_1650_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___redArg(lean_object* v_a_1660_, lean_object* v_as_1661_, size_t v_sz_1662_, size_t v_i_1663_, lean_object* v_b_1664_){
_start:
{
uint8_t v___x_1666_; 
v___x_1666_ = lean_usize_dec_lt(v_i_1663_, v_sz_1662_);
if (v___x_1666_ == 0)
{
lean_object* v___x_1667_; 
v___x_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1667_, 0, v_b_1664_);
return v___x_1667_;
}
else
{
lean_object* v_snd_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1686_; 
v_snd_1668_ = lean_ctor_get(v_b_1664_, 1);
v_isSharedCheck_1686_ = !lean_is_exclusive(v_b_1664_);
if (v_isSharedCheck_1686_ == 0)
{
lean_object* v_unused_1687_; 
v_unused_1687_ = lean_ctor_get(v_b_1664_, 0);
lean_dec(v_unused_1687_);
v___x_1670_ = v_b_1664_;
v_isShared_1671_ = v_isSharedCheck_1686_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_snd_1668_);
lean_dec(v_b_1664_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1686_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1672_; lean_object* v_a_1674_; lean_object* v_a_1681_; 
v___x_1672_ = lean_box(0);
v_a_1681_ = lean_array_uget_borrowed(v_as_1661_, v_i_1663_);
if (lean_obj_tag(v_a_1681_) == 0)
{
v_a_1674_ = v_snd_1668_;
goto v___jp_1673_;
}
else
{
lean_object* v_val_1682_; lean_object* v___x_1683_; uint8_t v___x_1684_; 
v_val_1682_ = lean_ctor_get(v_a_1681_, 0);
v___x_1683_ = l_Lean_LocalDecl_fvarId(v_val_1682_);
v___x_1684_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_1683_, v_a_1660_);
if (v___x_1684_ == 0)
{
lean_object* v___x_1685_; 
v___x_1685_ = l_Lean_LocalContext_erase(v_snd_1668_, v___x_1683_);
lean_dec(v___x_1683_);
v_a_1674_ = v___x_1685_;
goto v___jp_1673_;
}
else
{
lean_dec(v___x_1683_);
v_a_1674_ = v_snd_1668_;
goto v___jp_1673_;
}
}
v___jp_1673_:
{
lean_object* v___x_1676_; 
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 1, v_a_1674_);
lean_ctor_set(v___x_1670_, 0, v___x_1672_);
v___x_1676_ = v___x_1670_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v___x_1672_);
lean_ctor_set(v_reuseFailAlloc_1680_, 1, v_a_1674_);
v___x_1676_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
size_t v___x_1677_; size_t v___x_1678_; 
v___x_1677_ = ((size_t)1ULL);
v___x_1678_ = lean_usize_add(v_i_1663_, v___x_1677_);
v_i_1663_ = v___x_1678_;
v_b_1664_ = v___x_1676_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___redArg___boxed(lean_object* v_a_1688_, lean_object* v_as_1689_, lean_object* v_sz_1690_, lean_object* v_i_1691_, lean_object* v_b_1692_, lean_object* v___y_1693_){
_start:
{
size_t v_sz_boxed_1694_; size_t v_i_boxed_1695_; lean_object* v_res_1696_; 
v_sz_boxed_1694_ = lean_unbox_usize(v_sz_1690_);
lean_dec(v_sz_1690_);
v_i_boxed_1695_ = lean_unbox_usize(v_i_1691_);
lean_dec(v_i_1691_);
v_res_1696_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___redArg(v_a_1688_, v_as_1689_, v_sz_boxed_1694_, v_i_boxed_1695_, v_b_1692_);
lean_dec_ref(v_as_1689_);
lean_dec(v_a_1688_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1(lean_object* v_a_1697_, lean_object* v_as_1698_, size_t v_sz_1699_, size_t v_i_1700_, lean_object* v_b_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
uint8_t v___x_1707_; 
v___x_1707_ = lean_usize_dec_lt(v_i_1700_, v_sz_1699_);
if (v___x_1707_ == 0)
{
lean_object* v___x_1708_; 
v___x_1708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1708_, 0, v_b_1701_);
return v___x_1708_;
}
else
{
lean_object* v_snd_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1727_; 
v_snd_1709_ = lean_ctor_get(v_b_1701_, 1);
v_isSharedCheck_1727_ = !lean_is_exclusive(v_b_1701_);
if (v_isSharedCheck_1727_ == 0)
{
lean_object* v_unused_1728_; 
v_unused_1728_ = lean_ctor_get(v_b_1701_, 0);
lean_dec(v_unused_1728_);
v___x_1711_ = v_b_1701_;
v_isShared_1712_ = v_isSharedCheck_1727_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_snd_1709_);
lean_dec(v_b_1701_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1727_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1713_; lean_object* v_a_1715_; lean_object* v_a_1722_; 
v___x_1713_ = lean_box(0);
v_a_1722_ = lean_array_uget_borrowed(v_as_1698_, v_i_1700_);
if (lean_obj_tag(v_a_1722_) == 0)
{
v_a_1715_ = v_snd_1709_;
goto v___jp_1714_;
}
else
{
lean_object* v_val_1723_; lean_object* v___x_1724_; uint8_t v___x_1725_; 
v_val_1723_ = lean_ctor_get(v_a_1722_, 0);
v___x_1724_ = l_Lean_LocalDecl_fvarId(v_val_1723_);
v___x_1725_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_1724_, v_a_1697_);
if (v___x_1725_ == 0)
{
lean_object* v___x_1726_; 
v___x_1726_ = l_Lean_LocalContext_erase(v_snd_1709_, v___x_1724_);
lean_dec(v___x_1724_);
v_a_1715_ = v___x_1726_;
goto v___jp_1714_;
}
else
{
lean_dec(v___x_1724_);
v_a_1715_ = v_snd_1709_;
goto v___jp_1714_;
}
}
v___jp_1714_:
{
lean_object* v___x_1717_; 
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 1, v_a_1715_);
lean_ctor_set(v___x_1711_, 0, v___x_1713_);
v___x_1717_ = v___x_1711_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v___x_1713_);
lean_ctor_set(v_reuseFailAlloc_1721_, 1, v_a_1715_);
v___x_1717_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
size_t v___x_1718_; size_t v___x_1719_; lean_object* v___x_1720_; 
v___x_1718_ = ((size_t)1ULL);
v___x_1719_ = lean_usize_add(v_i_1700_, v___x_1718_);
v___x_1720_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___redArg(v_a_1697_, v_as_1698_, v_sz_1699_, v___x_1719_, v___x_1717_);
return v___x_1720_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1___boxed(lean_object* v_a_1729_, lean_object* v_as_1730_, lean_object* v_sz_1731_, lean_object* v_i_1732_, lean_object* v_b_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
size_t v_sz_boxed_1739_; size_t v_i_boxed_1740_; lean_object* v_res_1741_; 
v_sz_boxed_1739_ = lean_unbox_usize(v_sz_1731_);
lean_dec(v_sz_1731_);
v_i_boxed_1740_ = lean_unbox_usize(v_i_1732_);
lean_dec(v_i_1732_);
v_res_1741_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1(v_a_1729_, v_as_1730_, v_sz_boxed_1739_, v_i_boxed_1740_, v_b_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec_ref(v_as_1730_);
lean_dec(v_a_1729_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0(lean_object* v_a_1742_, lean_object* v_t_1743_, lean_object* v_init_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v_root_1750_; lean_object* v_tail_1751_; lean_object* v___x_1752_; 
v_root_1750_ = lean_ctor_get(v_t_1743_, 0);
v_tail_1751_ = lean_ctor_get(v_t_1743_, 1);
lean_inc_ref(v_init_1744_);
v___x_1752_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0(v_init_1744_, v_a_1742_, v_root_1750_, v_init_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
lean_dec_ref(v_init_1744_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1789_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1755_ = v___x_1752_;
v_isShared_1756_ = v_isSharedCheck_1789_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1752_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1789_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
if (lean_obj_tag(v_a_1753_) == 0)
{
lean_object* v_a_1757_; lean_object* v___x_1759_; 
v_a_1757_ = lean_ctor_get(v_a_1753_, 0);
lean_inc(v_a_1757_);
lean_dec_ref_known(v_a_1753_, 1);
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 0, v_a_1757_);
v___x_1759_ = v___x_1755_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1757_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
else
{
lean_object* v_a_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; size_t v_sz_1764_; size_t v___x_1765_; lean_object* v___x_1766_; 
lean_del_object(v___x_1755_);
v_a_1761_ = lean_ctor_get(v_a_1753_, 0);
lean_inc(v_a_1761_);
lean_dec_ref_known(v_a_1753_, 1);
v___x_1762_ = lean_box(0);
v___x_1763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1762_);
lean_ctor_set(v___x_1763_, 1, v_a_1761_);
v_sz_1764_ = lean_array_size(v_tail_1751_);
v___x_1765_ = ((size_t)0ULL);
v___x_1766_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1(v_a_1742_, v_tail_1751_, v_sz_1764_, v___x_1765_, v___x_1763_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1780_; 
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1769_ = v___x_1766_;
v_isShared_1770_ = v_isSharedCheck_1780_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___x_1766_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1780_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v_fst_1771_; 
v_fst_1771_ = lean_ctor_get(v_a_1767_, 0);
if (lean_obj_tag(v_fst_1771_) == 0)
{
lean_object* v_snd_1772_; lean_object* v___x_1774_; 
v_snd_1772_ = lean_ctor_get(v_a_1767_, 1);
lean_inc(v_snd_1772_);
lean_dec(v_a_1767_);
if (v_isShared_1770_ == 0)
{
lean_ctor_set(v___x_1769_, 0, v_snd_1772_);
v___x_1774_ = v___x_1769_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_snd_1772_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
else
{
lean_object* v_val_1776_; lean_object* v___x_1778_; 
lean_inc_ref(v_fst_1771_);
lean_dec(v_a_1767_);
v_val_1776_ = lean_ctor_get(v_fst_1771_, 0);
lean_inc(v_val_1776_);
lean_dec_ref_known(v_fst_1771_, 1);
if (v_isShared_1770_ == 0)
{
lean_ctor_set(v___x_1769_, 0, v_val_1776_);
v___x_1778_ = v___x_1769_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_val_1776_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
}
else
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
v_a_1781_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1766_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1766_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1781_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
}
}
}
else
{
lean_object* v_a_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1797_; 
v_a_1790_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1792_ = v___x_1752_;
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_a_1790_);
lean_dec(v___x_1752_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1795_; 
if (v_isShared_1793_ == 0)
{
v___x_1795_ = v___x_1792_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_a_1790_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0___boxed(lean_object* v_a_1798_, lean_object* v_t_1799_, lean_object* v_init_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0(v_a_1798_, v_t_1799_, v_init_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec_ref(v_t_1799_);
lean_dec(v_a_1798_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___lam__0(lean_object* v_mvarId_1809_, lean_object* v___x_1810_, lean_object* v___x_1811_, lean_object* v_toPreserve_1812_, uint8_t v_indirectProps_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_){
_start:
{
lean_object* v___x_1819_; 
lean_inc(v_mvarId_1809_);
v___x_1819_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1809_, v___x_1810_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
if (lean_obj_tag(v___x_1819_) == 0)
{
uint8_t v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
lean_dec_ref_known(v___x_1819_, 1);
v___x_1820_ = 0;
v___x_1821_ = lean_box(v___x_1820_);
v___x_1822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1821_);
lean_ctor_set(v___x_1822_, 1, v___x_1811_);
v___x_1823_ = lean_st_mk_ref(v___x_1822_);
lean_inc(v_mvarId_1809_);
v___x_1824_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed(v_mvarId_1809_, v_toPreserve_1812_, v_indirectProps_1813_, v___x_1823_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v_a_1825_; lean_object* v___x_1826_; lean_object* v_lctx_1827_; lean_object* v_localInstances_1828_; lean_object* v_decls_1829_; lean_object* v___x_1830_; 
v_a_1825_ = lean_ctor_get(v___x_1824_, 0);
lean_inc(v_a_1825_);
lean_dec_ref_known(v___x_1824_, 1);
v___x_1826_ = lean_st_ref_get(v___x_1823_);
lean_dec(v___x_1823_);
lean_dec(v___x_1826_);
v_lctx_1827_ = lean_ctor_get(v___y_1814_, 2);
v_localInstances_1828_ = lean_ctor_get(v___y_1814_, 3);
v_decls_1829_ = lean_ctor_get(v_lctx_1827_, 1);
lean_inc_ref(v_lctx_1827_);
v___x_1830_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0(v_a_1825_, v_decls_1829_, v_lctx_1827_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v_a_1831_; lean_object* v___x_1832_; lean_object* v___y_1834_; lean_object* v___x_1878_; lean_object* v___x_1879_; uint8_t v___x_1880_; 
v_a_1831_ = lean_ctor_get(v___x_1830_, 0);
lean_inc(v_a_1831_);
lean_dec_ref_known(v___x_1830_, 1);
v___x_1832_ = lean_unsigned_to_nat(0u);
v___x_1878_ = lean_array_get_size(v_localInstances_1828_);
v___x_1879_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___lam__0___closed__0));
v___x_1880_ = lean_nat_dec_lt(v___x_1832_, v___x_1878_);
if (v___x_1880_ == 0)
{
lean_dec(v_a_1825_);
v___y_1834_ = v___x_1879_;
goto v___jp_1833_;
}
else
{
size_t v___x_1881_; size_t v___x_1882_; lean_object* v___x_1883_; 
v___x_1881_ = ((size_t)0ULL);
v___x_1882_ = lean_usize_of_nat(v___x_1878_);
v___x_1883_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__3(v_a_1825_, v_localInstances_1828_, v___x_1881_, v___x_1882_, v___x_1879_);
lean_dec(v_a_1825_);
v___y_1834_ = v___x_1883_;
goto v___jp_1833_;
}
v___jp_1833_:
{
lean_object* v___x_1835_; 
lean_inc(v_mvarId_1809_);
v___x_1835_ = l_Lean_MVarId_getType(v_mvarId_1809_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; lean_object* v___x_1837_; lean_object* v_a_1838_; lean_object* v___x_1839_; 
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
lean_inc(v_a_1836_);
lean_dec_ref_known(v___x_1835_, 1);
v___x_1837_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___redArg(v_a_1836_, v___y_1815_);
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
lean_inc(v_a_1838_);
lean_dec_ref(v___x_1837_);
lean_inc(v_mvarId_1809_);
v___x_1839_ = l_Lean_MVarId_getTag(v_mvarId_1809_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_object* v_a_1840_; uint8_t v___x_1841_; lean_object* v___x_1842_; 
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
lean_inc(v_a_1840_);
lean_dec_ref_known(v___x_1839_, 1);
v___x_1841_ = 2;
v___x_1842_ = l_Lean_Meta_mkFreshExprMVarAt(v_a_1831_, v___y_1834_, v_a_1838_, v___x_1841_, v_a_1840_, v___x_1832_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
lean_dec_ref(v___y_1814_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_object* v_a_1843_; lean_object* v___x_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1852_; 
v_a_1843_ = lean_ctor_get(v___x_1842_, 0);
lean_inc_n(v_a_1843_, 2);
lean_dec_ref_known(v___x_1842_, 1);
v___x_1844_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___redArg(v_mvarId_1809_, v_a_1843_, v___y_1815_);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1852_ == 0)
{
lean_object* v_unused_1853_; 
v_unused_1853_ = lean_ctor_get(v___x_1844_, 0);
lean_dec(v_unused_1853_);
v___x_1846_ = v___x_1844_;
v_isShared_1847_ = v_isSharedCheck_1852_;
goto v_resetjp_1845_;
}
else
{
lean_dec(v___x_1844_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1852_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1848_; lean_object* v___x_1850_; 
v___x_1848_ = l_Lean_Expr_mvarId_x21(v_a_1843_);
lean_dec(v_a_1843_);
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 0, v___x_1848_);
v___x_1850_ = v___x_1846_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v___x_1848_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
}
else
{
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1861_; 
lean_dec(v_mvarId_1809_);
v_a_1854_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1856_ = v___x_1842_;
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1842_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1859_; 
if (v_isShared_1857_ == 0)
{
v___x_1859_ = v___x_1856_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_a_1854_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
}
}
else
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1869_; 
lean_dec(v_a_1838_);
lean_dec_ref(v___y_1834_);
lean_dec(v_a_1831_);
lean_dec_ref(v___y_1814_);
lean_dec(v_mvarId_1809_);
v_a_1862_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1864_ = v___x_1839_;
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___x_1839_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1867_; 
if (v_isShared_1865_ == 0)
{
v___x_1867_ = v___x_1864_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_a_1862_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
}
else
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
lean_dec_ref(v___y_1834_);
lean_dec(v_a_1831_);
lean_dec_ref(v___y_1814_);
lean_dec(v_mvarId_1809_);
v_a_1870_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___x_1835_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1835_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1870_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
}
else
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1891_; 
lean_dec(v_a_1825_);
lean_dec_ref(v___y_1814_);
lean_dec(v_mvarId_1809_);
v_a_1884_ = lean_ctor_get(v___x_1830_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1886_ = v___x_1830_;
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1830_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1889_; 
if (v_isShared_1887_ == 0)
{
v___x_1889_ = v___x_1886_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_a_1884_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
}
else
{
lean_object* v_a_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1899_; 
lean_dec(v___x_1823_);
lean_dec_ref(v___y_1814_);
lean_dec(v_mvarId_1809_);
v_a_1892_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1894_ = v___x_1824_;
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_a_1892_);
lean_dec(v___x_1824_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___x_1897_; 
if (v_isShared_1895_ == 0)
{
v___x_1897_ = v___x_1894_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_a_1892_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
return v___x_1897_;
}
}
}
}
else
{
lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1907_; 
lean_dec_ref(v___y_1814_);
lean_dec(v___x_1811_);
lean_dec(v_mvarId_1809_);
v_a_1900_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1902_ = v___x_1819_;
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_dec(v___x_1819_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1905_; 
if (v_isShared_1903_ == 0)
{
v___x_1905_ = v___x_1902_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v_a_1900_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
return v___x_1905_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___lam__0___boxed(lean_object* v_mvarId_1908_, lean_object* v___x_1909_, lean_object* v___x_1910_, lean_object* v_toPreserve_1911_, lean_object* v_indirectProps_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_){
_start:
{
uint8_t v_indirectProps_boxed_1918_; lean_object* v_res_1919_; 
v_indirectProps_boxed_1918_ = lean_unbox(v_indirectProps_1912_);
v_res_1919_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___lam__0(v_mvarId_1908_, v___x_1909_, v___x_1910_, v_toPreserve_1911_, v_indirectProps_boxed_1918_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
lean_dec(v___y_1916_);
lean_dec_ref(v___y_1915_);
lean_dec(v___y_1914_);
lean_dec_ref(v_toPreserve_1911_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(lean_object* v_mvarId_1923_, lean_object* v_toPreserve_1924_, uint8_t v_indirectProps_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_){
_start:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___f_1934_; lean_object* v___x_1935_; 
v___x_1931_ = lean_box(1);
v___x_1932_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___closed__1));
v___x_1933_ = lean_box(v_indirectProps_1925_);
lean_inc(v_mvarId_1923_);
v___f_1934_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1934_, 0, v_mvarId_1923_);
lean_closure_set(v___f_1934_, 1, v___x_1932_);
lean_closure_set(v___f_1934_, 2, v___x_1931_);
lean_closure_set(v___f_1934_, 3, v_toPreserve_1924_);
lean_closure_set(v___f_1934_, 4, v___x_1933_);
v___x_1935_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___redArg(v_mvarId_1923_, v___f_1934_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_);
return v___x_1935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___boxed(lean_object* v_mvarId_1936_, lean_object* v_toPreserve_1937_, lean_object* v_indirectProps_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_){
_start:
{
uint8_t v_indirectProps_boxed_1944_; lean_object* v_res_1945_; 
v_indirectProps_boxed_1944_ = lean_unbox(v_indirectProps_1938_);
v_res_1945_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(v_mvarId_1936_, v_toPreserve_1937_, v_indirectProps_boxed_1944_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_);
lean_dec(v_a_1942_);
lean_dec_ref(v_a_1941_);
lean_dec(v_a_1940_);
lean_dec_ref(v_a_1939_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2(lean_object* v_mvarId_1946_, lean_object* v_val_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_){
_start:
{
lean_object* v___x_1953_; 
v___x_1953_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___redArg(v_mvarId_1946_, v_val_1947_, v___y_1949_);
return v___x_1953_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___boxed(lean_object* v_mvarId_1954_, lean_object* v_val_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2(v_mvarId_1954_, v_val_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4(lean_object* v_00_u03b2_1962_, lean_object* v_x_1963_, lean_object* v_x_1964_, lean_object* v_x_1965_){
_start:
{
lean_object* v___x_1966_; 
v___x_1966_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4___redArg(v_x_1963_, v_x_1964_, v_x_1965_);
return v___x_1966_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6(lean_object* v_a_1967_, lean_object* v_as_1968_, size_t v_sz_1969_, size_t v_i_1970_, lean_object* v_b_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
lean_object* v___x_1977_; 
v___x_1977_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___redArg(v_a_1967_, v_as_1968_, v_sz_1969_, v_i_1970_, v_b_1971_);
return v___x_1977_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___boxed(lean_object* v_a_1978_, lean_object* v_as_1979_, lean_object* v_sz_1980_, lean_object* v_i_1981_, lean_object* v_b_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_){
_start:
{
size_t v_sz_boxed_1988_; size_t v_i_boxed_1989_; lean_object* v_res_1990_; 
v_sz_boxed_1988_ = lean_unbox_usize(v_sz_1980_);
lean_dec(v_sz_1980_);
v_i_boxed_1989_ = lean_unbox_usize(v_i_1981_);
lean_dec(v_i_1981_);
v_res_1990_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6(v_a_1978_, v_as_1979_, v_sz_boxed_1988_, v_i_boxed_1989_, v_b_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec_ref(v_as_1979_);
lean_dec(v_a_1978_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9(lean_object* v_00_u03b2_1991_, lean_object* v_x_1992_, size_t v_x_1993_, size_t v_x_1994_, lean_object* v_x_1995_, lean_object* v_x_1996_){
_start:
{
lean_object* v___x_1997_; 
v___x_1997_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg(v_x_1992_, v_x_1993_, v_x_1994_, v_x_1995_, v_x_1996_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___boxed(lean_object* v_00_u03b2_1998_, lean_object* v_x_1999_, lean_object* v_x_2000_, lean_object* v_x_2001_, lean_object* v_x_2002_, lean_object* v_x_2003_){
_start:
{
size_t v_x_8417__boxed_2004_; size_t v_x_8418__boxed_2005_; lean_object* v_res_2006_; 
v_x_8417__boxed_2004_ = lean_unbox_usize(v_x_2000_);
lean_dec(v_x_2000_);
v_x_8418__boxed_2005_ = lean_unbox_usize(v_x_2001_);
lean_dec(v_x_2001_);
v_res_2006_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9(v_00_u03b2_1998_, v_x_1999_, v_x_8417__boxed_2004_, v_x_8418__boxed_2005_, v_x_2002_, v_x_2003_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7(lean_object* v_a_2007_, lean_object* v_as_2008_, size_t v_sz_2009_, size_t v_i_2010_, lean_object* v_b_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_){
_start:
{
lean_object* v___x_2017_; 
v___x_2017_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___redArg(v_a_2007_, v_as_2008_, v_sz_2009_, v_i_2010_, v_b_2011_);
return v___x_2017_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___boxed(lean_object* v_a_2018_, lean_object* v_as_2019_, lean_object* v_sz_2020_, lean_object* v_i_2021_, lean_object* v_b_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_){
_start:
{
size_t v_sz_boxed_2028_; size_t v_i_boxed_2029_; lean_object* v_res_2030_; 
v_sz_boxed_2028_ = lean_unbox_usize(v_sz_2020_);
lean_dec(v_sz_2020_);
v_i_boxed_2029_ = lean_unbox_usize(v_i_2021_);
lean_dec(v_i_2021_);
v_res_2030_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7(v_a_2018_, v_as_2019_, v_sz_boxed_2028_, v_i_boxed_2029_, v_b_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec_ref(v_as_2019_);
lean_dec(v_a_2018_);
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12(lean_object* v_00_u03b2_2031_, lean_object* v_n_2032_, lean_object* v_k_2033_, lean_object* v_v_2034_){
_start:
{
lean_object* v___x_2035_; 
v___x_2035_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12___redArg(v_n_2032_, v_k_2033_, v_v_2034_);
return v___x_2035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13(lean_object* v_00_u03b2_2036_, size_t v_depth_2037_, lean_object* v_keys_2038_, lean_object* v_vals_2039_, lean_object* v_heq_2040_, lean_object* v_i_2041_, lean_object* v_entries_2042_){
_start:
{
lean_object* v___x_2043_; 
v___x_2043_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___redArg(v_depth_2037_, v_keys_2038_, v_vals_2039_, v_i_2041_, v_entries_2042_);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___boxed(lean_object* v_00_u03b2_2044_, lean_object* v_depth_2045_, lean_object* v_keys_2046_, lean_object* v_vals_2047_, lean_object* v_heq_2048_, lean_object* v_i_2049_, lean_object* v_entries_2050_){
_start:
{
size_t v_depth_boxed_2051_; lean_object* v_res_2052_; 
v_depth_boxed_2051_ = lean_unbox_usize(v_depth_2045_);
lean_dec(v_depth_2045_);
v_res_2052_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13(v_00_u03b2_2044_, v_depth_boxed_2051_, v_keys_2046_, v_vals_2047_, v_heq_2048_, v_i_2049_, v_entries_2050_);
lean_dec_ref(v_vals_2047_);
lean_dec_ref(v_keys_2046_);
return v_res_2052_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12_spec__13(lean_object* v_00_u03b2_2053_, lean_object* v_x_2054_, lean_object* v_x_2055_, lean_object* v_x_2056_, lean_object* v_x_2057_){
_start:
{
lean_object* v___x_2058_; 
v___x_2058_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12_spec__13___redArg(v_x_2054_, v_x_2055_, v_x_2056_, v_x_2057_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_cleanup(lean_object* v_mvarId_2059_, lean_object* v_toPreserve_2060_, uint8_t v_indirectProps_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_){
_start:
{
lean_object* v___x_2067_; 
v___x_2067_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(v_mvarId_2059_, v_toPreserve_2060_, v_indirectProps_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_);
return v___x_2067_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_cleanup___boxed(lean_object* v_mvarId_2068_, lean_object* v_toPreserve_2069_, lean_object* v_indirectProps_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_){
_start:
{
uint8_t v_indirectProps_boxed_2076_; lean_object* v_res_2077_; 
v_indirectProps_boxed_2076_ = lean_unbox(v_indirectProps_2070_);
v_res_2077_ = l_Lean_MVarId_cleanup(v_mvarId_2068_, v_toPreserve_2069_, v_indirectProps_boxed_2076_, v_a_2071_, v_a_2072_, v_a_2073_, v_a_2074_);
lean_dec(v_a_2074_);
lean_dec_ref(v_a_2073_);
lean_dec(v_a_2072_);
lean_dec_ref(v_a_2071_);
return v_res_2077_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CollectFVars(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Cleanup(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
