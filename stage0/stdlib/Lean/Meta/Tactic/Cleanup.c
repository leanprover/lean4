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
uint8_t lean_bool_not(uint8_t);
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
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
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
uint8_t v___x_18_; uint8_t v___x_19_; 
v___x_18_ = l_Lean_Expr_hasMVar(v_e_15_);
v___x_19_ = lean_bool_not(v___x_18_);
if (v___x_19_ == 0)
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
else
{
lean_object* v___x_40_; 
v___x_40_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_40_, 0, v_e_15_);
return v___x_40_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0___redArg___boxed(lean_object* v_e_41_, lean_object* v___y_42_, lean_object* v___y_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0___redArg(v_e_41_, v___y_42_);
lean_dec(v___y_42_);
return v_res_44_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__0(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_47_ = lean_box(0);
v___x_48_ = lean_unsigned_to_nat(16u);
v___x_49_ = lean_mk_array(v___x_48_, v___x_47_);
return v___x_49_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__1(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_50_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__0, &l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__0_once, _init_l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__0);
v___x_51_ = lean_unsigned_to_nat(0u);
v___x_52_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
lean_ctor_set(v___x_52_, 1, v___x_50_);
return v___x_52_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__3(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_53_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__2));
v___x_54_ = lean_box(1);
v___x_55_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__1, &l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__1);
v___x_56_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
lean_ctor_set(v___x_56_, 1, v___x_54_);
lean_ctor_set(v___x_56_, 2, v___x_53_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(lean_object* v_fvarId_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_){
_start:
{
lean_object* v___x_64_; lean_object* v_snd_65_; uint8_t v___x_66_; 
v___x_64_ = lean_st_ref_get(v_a_58_);
v_snd_65_ = lean_ctor_get(v___x_64_, 1);
lean_inc(v_snd_65_);
lean_dec(v___x_64_);
v___x_66_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v_fvarId_57_, v_snd_65_);
lean_dec(v_snd_65_);
if (v___x_66_ == 0)
{
lean_object* v___x_67_; lean_object* v_snd_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_80_; 
v___x_67_ = lean_st_ref_take(v_a_58_);
v_snd_68_ = lean_ctor_get(v___x_67_, 1);
v_isSharedCheck_80_ = !lean_is_exclusive(v___x_67_);
if (v_isSharedCheck_80_ == 0)
{
lean_object* v_unused_81_; 
v_unused_81_ = lean_ctor_get(v___x_67_, 0);
lean_dec(v_unused_81_);
v___x_70_ = v___x_67_;
v_isShared_71_ = v_isSharedCheck_80_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_snd_68_);
lean_dec(v___x_67_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_80_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
uint8_t v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_76_; 
v___x_72_ = 1;
lean_inc(v_fvarId_57_);
v___x_73_ = l_Lean_FVarIdSet_insert(v_snd_68_, v_fvarId_57_);
v___x_74_ = lean_box(v___x_72_);
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 1, v___x_73_);
lean_ctor_set(v___x_70_, 0, v___x_74_);
v___x_76_ = v___x_70_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v___x_74_);
lean_ctor_set(v_reuseFailAlloc_79_, 1, v___x_73_);
v___x_76_ = v_reuseFailAlloc_79_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = lean_st_ref_set(v_a_58_, v___x_76_);
v___x_78_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addDeps(v_fvarId_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_);
return v___x_78_;
}
}
}
else
{
lean_object* v___x_82_; lean_object* v___x_83_; 
lean_dec(v_fvarId_57_);
v___x_82_ = lean_box(0);
v___x_83_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
return v___x_83_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__1(lean_object* v_init_84_, lean_object* v_x_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_){
_start:
{
if (lean_obj_tag(v_x_85_) == 0)
{
lean_object* v_k_92_; lean_object* v_l_93_; lean_object* v_r_94_; lean_object* v___x_95_; 
v_k_92_ = lean_ctor_get(v_x_85_, 1);
lean_inc(v_k_92_);
v_l_93_ = lean_ctor_get(v_x_85_, 3);
lean_inc(v_l_93_);
v_r_94_ = lean_ctor_get(v_x_85_, 4);
lean_inc(v_r_94_);
lean_dec_ref_known(v_x_85_, 5);
v___x_95_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__1(v_init_84_, v_l_93_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_);
if (lean_obj_tag(v___x_95_) == 0)
{
lean_object* v___x_96_; 
lean_dec_ref_known(v___x_95_, 1);
v___x_96_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v_k_92_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_);
if (lean_obj_tag(v___x_96_) == 0)
{
lean_object* v___x_97_; 
lean_dec_ref_known(v___x_96_, 1);
v___x_97_ = lean_box(0);
v_init_84_ = v___x_97_;
v_x_85_ = v_r_94_;
goto _start;
}
else
{
lean_object* v_a_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_106_; 
lean_dec(v_r_94_);
v_a_99_ = lean_ctor_get(v___x_96_, 0);
v_isSharedCheck_106_ = !lean_is_exclusive(v___x_96_);
if (v_isSharedCheck_106_ == 0)
{
v___x_101_ = v___x_96_;
v_isShared_102_ = v_isSharedCheck_106_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_a_99_);
lean_dec(v___x_96_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_106_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_104_; 
if (v_isShared_102_ == 0)
{
v___x_104_ = v___x_101_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v_a_99_);
v___x_104_ = v_reuseFailAlloc_105_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
return v___x_104_;
}
}
}
}
else
{
lean_dec(v_r_94_);
lean_dec(v_k_92_);
return v___x_95_;
}
}
else
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_107_, 0, v_init_84_);
v___x_108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
return v___x_108_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars(lean_object* v_e_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0___redArg(v_e_109_, v_a_112_);
if (lean_obj_tag(v___x_116_) == 0)
{
lean_object* v_a_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v_a_117_ = lean_ctor_get(v___x_116_, 0);
lean_inc(v_a_117_);
lean_dec_ref_known(v___x_116_, 1);
v___x_118_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__3, &l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__3);
v___x_119_ = lean_st_mk_ref(v___x_118_);
v___x_120_ = l_Lean_Expr_collectFVars(v_a_117_, v___x_119_, v_a_111_, v_a_112_, v_a_113_, v_a_114_);
if (lean_obj_tag(v___x_120_) == 0)
{
lean_object* v___x_121_; lean_object* v_fvarSet_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
lean_dec_ref_known(v___x_120_, 1);
v___x_121_ = lean_st_ref_get(v___x_119_);
lean_dec(v___x_119_);
v_fvarSet_122_ = lean_ctor_get(v___x_121_, 1);
lean_inc(v_fvarSet_122_);
lean_dec(v___x_121_);
v___x_123_ = lean_box(0);
v___x_124_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__1(v___x_123_, v_fvarSet_122_, v_a_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_);
if (lean_obj_tag(v___x_124_) == 0)
{
lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_131_; 
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_131_ == 0)
{
lean_object* v_unused_132_; 
v_unused_132_ = lean_ctor_get(v___x_124_, 0);
lean_dec(v_unused_132_);
v___x_126_ = v___x_124_;
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
else
{
lean_dec(v___x_124_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_129_; 
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 0, v___x_123_);
v___x_129_ = v___x_126_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v___x_123_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
else
{
lean_object* v_a_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_140_; 
v_a_133_ = lean_ctor_get(v___x_124_, 0);
v_isSharedCheck_140_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_140_ == 0)
{
v___x_135_ = v___x_124_;
v_isShared_136_ = v_isSharedCheck_140_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_a_133_);
lean_dec(v___x_124_);
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
else
{
lean_dec(v___x_119_);
return v___x_120_;
}
}
else
{
lean_object* v_a_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_148_; 
v_a_141_ = lean_ctor_get(v___x_116_, 0);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_148_ == 0)
{
v___x_143_ = v___x_116_;
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_a_141_);
lean_dec(v___x_116_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_146_; 
if (v_isShared_144_ == 0)
{
v___x_146_ = v___x_143_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_a_141_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addDeps(lean_object* v_fvarId_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_149_, v_a_151_, v_a_153_, v_a_154_);
if (lean_obj_tag(v___x_156_) == 0)
{
lean_object* v_a_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v_a_157_ = lean_ctor_get(v___x_156_, 0);
lean_inc(v_a_157_);
lean_dec_ref_known(v___x_156_, 1);
v___x_158_ = l_Lean_LocalDecl_type(v_a_157_);
v___x_159_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars(v___x_158_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_);
if (lean_obj_tag(v___x_159_) == 0)
{
lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_171_; 
v_isSharedCheck_171_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_171_ == 0)
{
lean_object* v_unused_172_; 
v_unused_172_ = lean_ctor_get(v___x_159_, 0);
lean_dec(v_unused_172_);
v___x_161_ = v___x_159_;
v_isShared_162_ = v_isSharedCheck_171_;
goto v_resetjp_160_;
}
else
{
lean_dec(v___x_159_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_171_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
uint8_t v___x_163_; lean_object* v___x_164_; 
v___x_163_ = 0;
v___x_164_ = l_Lean_LocalDecl_value_x3f(v_a_157_, v___x_163_);
lean_dec(v_a_157_);
if (lean_obj_tag(v___x_164_) == 1)
{
lean_object* v_val_165_; lean_object* v___x_166_; 
lean_del_object(v___x_161_);
v_val_165_ = lean_ctor_get(v___x_164_, 0);
lean_inc(v_val_165_);
lean_dec_ref_known(v___x_164_, 1);
v___x_166_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars(v_val_165_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_);
return v___x_166_;
}
else
{
lean_object* v___x_167_; lean_object* v___x_169_; 
lean_dec(v___x_164_);
v___x_167_ = lean_box(0);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 0, v___x_167_);
v___x_169_ = v___x_161_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v___x_167_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
}
else
{
lean_dec(v_a_157_);
return v___x_159_;
}
}
else
{
lean_object* v_a_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_180_; 
v_a_173_ = lean_ctor_get(v___x_156_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v___x_156_);
if (v_isSharedCheck_180_ == 0)
{
v___x_175_ = v___x_156_;
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_a_173_);
lean_dec(v___x_156_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_178_; 
if (v_isShared_176_ == 0)
{
v___x_178_ = v___x_175_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_a_173_);
v___x_178_ = v_reuseFailAlloc_179_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
return v___x_178_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addDeps___boxed(lean_object* v_fvarId_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addDeps(v_fvarId_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_);
lean_dec(v_a_186_);
lean_dec_ref(v_a_185_);
lean_dec(v_a_184_);
lean_dec_ref(v_a_183_);
lean_dec(v_a_182_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__1___boxed(lean_object* v_init_189_, lean_object* v_x_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__1(v_init_189_, v_x_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
lean_dec(v___y_191_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar___boxed(lean_object* v_fvarId_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v_fvarId_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_);
lean_dec(v_a_203_);
lean_dec_ref(v_a_202_);
lean_dec(v_a_201_);
lean_dec_ref(v_a_200_);
lean_dec(v_a_199_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___boxed(lean_object* v_e_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars(v_e_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_);
lean_dec(v_a_211_);
lean_dec_ref(v_a_210_);
lean_dec(v_a_209_);
lean_dec_ref(v_a_208_);
lean_dec(v_a_207_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0(lean_object* v_e_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0___redArg(v_e_214_, v___y_217_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0___boxed(lean_object* v_e_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0(v_e_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
lean_dec(v___y_225_);
lean_dec_ref(v___y_224_);
lean_dec(v___y_223_);
return v_res_229_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3(lean_object* v_00_u03b2_230_, lean_object* v_k_231_, lean_object* v_t_232_){
_start:
{
uint8_t v___x_233_; 
v___x_233_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v_k_231_, v_t_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___boxed(lean_object* v_00_u03b2_234_, lean_object* v_k_235_, lean_object* v_t_236_){
_start:
{
uint8_t v_res_237_; lean_object* v_r_238_; 
v_res_237_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3(v_00_u03b2_234_, v_k_235_, v_t_236_);
lean_dec(v_t_236_);
lean_dec(v_k_235_);
v_r_238_ = lean_box(v_res_237_);
return v_r_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(lean_object* v_e_239_, lean_object* v_pf_240_, lean_object* v_pm_241_, lean_object* v___y_242_){
_start:
{
lean_object* v___x_244_; uint8_t v_fst_246_; lean_object* v_mctx_247_; lean_object* v_mctx_264_; lean_object* v___x_265_; lean_object* v___x_266_; uint8_t v___y_268_; uint8_t v___x_275_; uint8_t v___x_276_; 
v___x_244_ = lean_st_ref_get(v___y_242_);
v_mctx_264_ = lean_ctor_get(v___x_244_, 0);
lean_inc_ref_n(v_mctx_264_, 2);
lean_dec(v___x_244_);
v___x_265_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__1, &l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__1);
v___x_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
lean_ctor_set(v___x_266_, 1, v_mctx_264_);
v___x_275_ = l_Lean_Expr_hasFVar(v_e_239_);
v___x_276_ = lean_bool_not(v___x_275_);
if (v___x_276_ == 0)
{
v___y_268_ = v___x_276_;
goto v___jp_267_;
}
else
{
uint8_t v___x_277_; uint8_t v___x_278_; 
v___x_277_ = l_Lean_Expr_hasMVar(v_e_239_);
v___x_278_ = lean_bool_not(v___x_277_);
v___y_268_ = v___x_278_;
goto v___jp_267_;
}
v___jp_245_:
{
lean_object* v___x_248_; lean_object* v_cache_249_; lean_object* v_zetaDeltaFVarIds_250_; lean_object* v_postponed_251_; lean_object* v_diag_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_262_; 
v___x_248_ = lean_st_ref_take(v___y_242_);
v_cache_249_ = lean_ctor_get(v___x_248_, 1);
v_zetaDeltaFVarIds_250_ = lean_ctor_get(v___x_248_, 2);
v_postponed_251_ = lean_ctor_get(v___x_248_, 3);
v_diag_252_ = lean_ctor_get(v___x_248_, 4);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_262_ == 0)
{
lean_object* v_unused_263_; 
v_unused_263_ = lean_ctor_get(v___x_248_, 0);
lean_dec(v_unused_263_);
v___x_254_ = v___x_248_;
v_isShared_255_ = v_isSharedCheck_262_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_diag_252_);
lean_inc(v_postponed_251_);
lean_inc(v_zetaDeltaFVarIds_250_);
lean_inc(v_cache_249_);
lean_dec(v___x_248_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_262_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_257_; 
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 0, v_mctx_247_);
v___x_257_ = v___x_254_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_mctx_247_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v_cache_249_);
lean_ctor_set(v_reuseFailAlloc_261_, 2, v_zetaDeltaFVarIds_250_);
lean_ctor_set(v_reuseFailAlloc_261_, 3, v_postponed_251_);
lean_ctor_set(v_reuseFailAlloc_261_, 4, v_diag_252_);
v___x_257_ = v_reuseFailAlloc_261_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_258_ = lean_st_ref_set(v___y_242_, v___x_257_);
v___x_259_ = lean_box(v_fst_246_);
v___x_260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
return v___x_260_;
}
}
}
v___jp_267_:
{
if (v___y_268_ == 0)
{
lean_object* v___x_269_; lean_object* v_snd_270_; lean_object* v_fst_271_; lean_object* v_mctx_272_; uint8_t v___x_273_; 
lean_dec_ref(v_mctx_264_);
v___x_269_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v_pf_240_, v_pm_241_, v_e_239_, v___x_266_);
v_snd_270_ = lean_ctor_get(v___x_269_, 1);
lean_inc(v_snd_270_);
v_fst_271_ = lean_ctor_get(v___x_269_, 0);
lean_inc(v_fst_271_);
lean_dec_ref(v___x_269_);
v_mctx_272_ = lean_ctor_get(v_snd_270_, 1);
lean_inc_ref(v_mctx_272_);
lean_dec(v_snd_270_);
v___x_273_ = lean_unbox(v_fst_271_);
lean_dec(v_fst_271_);
v_fst_246_ = v___x_273_;
v_mctx_247_ = v_mctx_272_;
goto v___jp_245_;
}
else
{
uint8_t v___x_274_; 
lean_dec_ref_known(v___x_266_, 2);
lean_dec_ref(v_pm_241_);
lean_dec_ref(v_pf_240_);
lean_dec_ref(v_e_239_);
v___x_274_ = 0;
v_fst_246_ = v___x_274_;
v_mctx_247_ = v_mctx_264_;
goto v___jp_245_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg___boxed(lean_object* v_e_279_, lean_object* v_pf_280_, lean_object* v_pm_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v_e_279_, v_pf_280_, v_pm_281_, v___y_282_);
lean_dec(v___y_282_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0(lean_object* v_e_285_, lean_object* v_pf_286_, lean_object* v_pm_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v_e_285_, v_pf_286_, v_pm_287_, v___y_290_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___boxed(lean_object* v_e_295_, lean_object* v_pf_296_, lean_object* v_pm_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0(v_e_295_, v_pf_296_, v_pm_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
lean_dec(v___y_298_);
return v_res_304_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__0(lean_object* v_snd_305_, lean_object* v___y_306_){
_start:
{
uint8_t v___x_307_; 
v___x_307_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___y_306_, v_snd_305_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__0___boxed(lean_object* v_snd_308_, lean_object* v___y_309_){
_start:
{
uint8_t v_res_310_; lean_object* v_r_311_; 
v_res_310_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__0(v_snd_308_, v___y_309_);
lean_dec(v___y_309_);
lean_dec(v_snd_308_);
v_r_311_ = lean_box(v_res_310_);
return v_r_311_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__1(uint8_t v___x_312_, lean_object* v_x_313_){
_start:
{
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__1___boxed(lean_object* v___x_314_, lean_object* v_x_315_){
_start:
{
uint8_t v___x_9791__boxed_316_; uint8_t v_res_317_; lean_object* v_r_318_; 
v___x_9791__boxed_316_ = lean_unbox(v___x_314_);
v_res_317_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__1(v___x_9791__boxed_316_, v_x_315_);
lean_dec(v_x_315_);
v_r_318_ = lean_box(v_res_317_);
return v_r_318_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2_spec__5(lean_object* v_as_319_, size_t v_sz_320_, size_t v_i_321_, lean_object* v_b_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
uint8_t v___x_329_; 
v___x_329_ = lean_usize_dec_lt(v_i_321_, v_sz_320_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; 
v___x_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_330_, 0, v_b_322_);
return v___x_330_;
}
else
{
lean_object* v_snd_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_414_; 
v_snd_331_ = lean_ctor_get(v_b_322_, 1);
v_isSharedCheck_414_ = !lean_is_exclusive(v_b_322_);
if (v_isSharedCheck_414_ == 0)
{
lean_object* v_unused_415_; 
v_unused_415_ = lean_ctor_get(v_b_322_, 0);
lean_dec(v_unused_415_);
v___x_333_ = v_b_322_;
v_isShared_334_ = v_isSharedCheck_414_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_snd_331_);
lean_dec(v_b_322_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_414_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_335_; lean_object* v_a_337_; lean_object* v_a_344_; 
v___x_335_ = lean_box(0);
v_a_344_ = lean_array_uget_borrowed(v_as_319_, v_i_321_);
if (lean_obj_tag(v_a_344_) == 0)
{
v_a_337_ = v_snd_331_;
goto v___jp_336_;
}
else
{
lean_object* v_val_345_; lean_object* v___x_346_; lean_object* v_snd_347_; lean_object* v___x_348_; lean_object* v___x_349_; uint8_t v___x_350_; 
lean_dec(v_snd_331_);
v_val_345_ = lean_ctor_get(v_a_344_, 0);
v___x_346_ = lean_st_ref_get(v___y_323_);
v_snd_347_ = lean_ctor_get(v___x_346_, 1);
lean_inc(v_snd_347_);
lean_dec(v___x_346_);
v___x_348_ = lean_box(0);
v___x_349_ = l_Lean_LocalDecl_fvarId(v_val_345_);
v___x_350_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_349_, v_snd_347_);
if (v___x_350_ == 0)
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = l_Lean_LocalDecl_type(v_val_345_);
lean_inc_ref(v___x_351_);
v___x_352_ = l_Lean_Meta_isProp(v___x_351_, v___y_324_, v___y_325_, v___y_326_, v___y_327_);
if (lean_obj_tag(v___x_352_) == 0)
{
lean_object* v_a_353_; lean_object* v___f_354_; lean_object* v___x_355_; lean_object* v___f_356_; lean_object* v___y_358_; lean_object* v___y_359_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___y_362_; uint8_t v___x_385_; 
v_a_353_ = lean_ctor_get(v___x_352_, 0);
lean_inc(v_a_353_);
lean_dec_ref_known(v___x_352_, 1);
v___f_354_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_354_, 0, v_snd_347_);
v___x_355_ = lean_box(v___x_350_);
v___f_356_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__1___boxed), 2, 1);
lean_closure_set(v___f_356_, 0, v___x_355_);
v___x_385_ = lean_unbox(v_a_353_);
lean_dec(v_a_353_);
if (v___x_385_ == 0)
{
lean_dec_ref(v___x_351_);
v___y_358_ = v___y_323_;
v___y_359_ = v___y_324_;
v___y_360_ = v___y_325_;
v___y_361_ = v___y_326_;
v___y_362_ = v___y_327_;
goto v___jp_357_;
}
else
{
lean_object* v___x_386_; 
lean_inc_ref(v___f_356_);
lean_inc_ref(v___f_354_);
v___x_386_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v___x_351_, v___f_354_, v___f_356_, v___y_325_);
if (lean_obj_tag(v___x_386_) == 0)
{
lean_object* v_a_387_; uint8_t v___x_388_; 
v_a_387_ = lean_ctor_get(v___x_386_, 0);
lean_inc(v_a_387_);
lean_dec_ref_known(v___x_386_, 1);
v___x_388_ = lean_unbox(v_a_387_);
lean_dec(v_a_387_);
if (v___x_388_ == 0)
{
v___y_358_ = v___y_323_;
v___y_359_ = v___y_324_;
v___y_360_ = v___y_325_;
v___y_361_ = v___y_326_;
v___y_362_ = v___y_327_;
goto v___jp_357_;
}
else
{
lean_object* v___x_389_; 
lean_inc(v___x_349_);
v___x_389_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_349_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_);
if (lean_obj_tag(v___x_389_) == 0)
{
lean_dec_ref_known(v___x_389_, 1);
v___y_358_ = v___y_323_;
v___y_359_ = v___y_324_;
v___y_360_ = v___y_325_;
v___y_361_ = v___y_326_;
v___y_362_ = v___y_327_;
goto v___jp_357_;
}
else
{
lean_object* v_a_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_397_; 
lean_dec_ref(v___f_356_);
lean_dec_ref(v___f_354_);
lean_dec(v___x_349_);
lean_del_object(v___x_333_);
v_a_390_ = lean_ctor_get(v___x_389_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_397_ == 0)
{
v___x_392_ = v___x_389_;
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_a_390_);
lean_dec(v___x_389_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_395_; 
if (v_isShared_393_ == 0)
{
v___x_395_ = v___x_392_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_a_390_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
}
else
{
lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_405_; 
lean_dec_ref(v___f_356_);
lean_dec_ref(v___f_354_);
lean_dec(v___x_349_);
lean_del_object(v___x_333_);
v_a_398_ = lean_ctor_get(v___x_386_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_405_ == 0)
{
v___x_400_ = v___x_386_;
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v___x_386_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_403_; 
if (v_isShared_401_ == 0)
{
v___x_403_ = v___x_400_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_a_398_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
v___jp_357_:
{
lean_object* v___x_363_; 
v___x_363_ = l_Lean_LocalDecl_value_x3f(v_val_345_, v___x_350_);
if (lean_obj_tag(v___x_363_) == 1)
{
lean_object* v_val_364_; lean_object* v___x_365_; 
v_val_364_ = lean_ctor_get(v___x_363_, 0);
lean_inc(v_val_364_);
lean_dec_ref_known(v___x_363_, 1);
v___x_365_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v_val_364_, v___f_354_, v___f_356_, v___y_360_);
if (lean_obj_tag(v___x_365_) == 0)
{
lean_object* v_a_366_; uint8_t v___x_367_; 
v_a_366_ = lean_ctor_get(v___x_365_, 0);
lean_inc(v_a_366_);
lean_dec_ref_known(v___x_365_, 1);
v___x_367_ = lean_unbox(v_a_366_);
lean_dec(v_a_366_);
if (v___x_367_ == 0)
{
lean_dec(v___x_349_);
v_a_337_ = v___x_348_;
goto v___jp_336_;
}
else
{
lean_object* v___x_368_; 
v___x_368_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_349_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_dec_ref_known(v___x_368_, 1);
v_a_337_ = v___x_348_;
goto v___jp_336_;
}
else
{
lean_object* v_a_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_376_; 
lean_del_object(v___x_333_);
v_a_369_ = lean_ctor_get(v___x_368_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_376_ == 0)
{
v___x_371_ = v___x_368_;
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_a_369_);
lean_dec(v___x_368_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_374_; 
if (v_isShared_372_ == 0)
{
v___x_374_ = v___x_371_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_a_369_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
}
}
else
{
lean_object* v_a_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_384_; 
lean_dec(v___x_349_);
lean_del_object(v___x_333_);
v_a_377_ = lean_ctor_get(v___x_365_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_384_ == 0)
{
v___x_379_ = v___x_365_;
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_a_377_);
lean_dec(v___x_365_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_382_; 
if (v_isShared_380_ == 0)
{
v___x_382_ = v___x_379_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_a_377_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
}
else
{
lean_dec(v___x_363_);
lean_dec_ref(v___f_356_);
lean_dec_ref(v___f_354_);
lean_dec(v___x_349_);
v_a_337_ = v___x_348_;
goto v___jp_336_;
}
}
}
else
{
lean_object* v_a_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_413_; 
lean_dec_ref(v___x_351_);
lean_dec(v___x_349_);
lean_dec(v_snd_347_);
lean_del_object(v___x_333_);
v_a_406_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_413_ == 0)
{
v___x_408_ = v___x_352_;
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_a_406_);
lean_dec(v___x_352_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_411_; 
if (v_isShared_409_ == 0)
{
v___x_411_ = v___x_408_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_a_406_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
}
else
{
lean_dec(v___x_349_);
lean_dec(v_snd_347_);
v_a_337_ = v___x_348_;
goto v___jp_336_;
}
}
v___jp_336_:
{
lean_object* v___x_339_; 
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 1, v_a_337_);
lean_ctor_set(v___x_333_, 0, v___x_335_);
v___x_339_ = v___x_333_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v___x_335_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v_a_337_);
v___x_339_ = v_reuseFailAlloc_343_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
size_t v___x_340_; size_t v___x_341_; 
v___x_340_ = ((size_t)1ULL);
v___x_341_ = lean_usize_add(v_i_321_, v___x_340_);
v_i_321_ = v___x_341_;
v_b_322_ = v___x_339_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2_spec__5___boxed(lean_object* v_as_416_, lean_object* v_sz_417_, lean_object* v_i_418_, lean_object* v_b_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
size_t v_sz_boxed_426_; size_t v_i_boxed_427_; lean_object* v_res_428_; 
v_sz_boxed_426_ = lean_unbox_usize(v_sz_417_);
lean_dec(v_sz_417_);
v_i_boxed_427_ = lean_unbox_usize(v_i_418_);
lean_dec(v_i_418_);
v_res_428_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2_spec__5(v_as_416_, v_sz_boxed_426_, v_i_boxed_427_, v_b_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
lean_dec(v___y_420_);
lean_dec_ref(v_as_416_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2(lean_object* v_as_429_, size_t v_sz_430_, size_t v_i_431_, lean_object* v_b_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
uint8_t v___x_439_; 
v___x_439_ = lean_usize_dec_lt(v_i_431_, v_sz_430_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; 
v___x_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_440_, 0, v_b_432_);
return v___x_440_;
}
else
{
lean_object* v_snd_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_524_; 
v_snd_441_ = lean_ctor_get(v_b_432_, 1);
v_isSharedCheck_524_ = !lean_is_exclusive(v_b_432_);
if (v_isSharedCheck_524_ == 0)
{
lean_object* v_unused_525_; 
v_unused_525_ = lean_ctor_get(v_b_432_, 0);
lean_dec(v_unused_525_);
v___x_443_ = v_b_432_;
v_isShared_444_ = v_isSharedCheck_524_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_snd_441_);
lean_dec(v_b_432_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_524_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_445_; lean_object* v_a_447_; lean_object* v_a_454_; 
v___x_445_ = lean_box(0);
v_a_454_ = lean_array_uget_borrowed(v_as_429_, v_i_431_);
if (lean_obj_tag(v_a_454_) == 0)
{
v_a_447_ = v_snd_441_;
goto v___jp_446_;
}
else
{
lean_object* v_val_455_; lean_object* v___x_456_; lean_object* v_snd_457_; lean_object* v___x_458_; lean_object* v___x_459_; uint8_t v___x_460_; 
lean_dec(v_snd_441_);
v_val_455_ = lean_ctor_get(v_a_454_, 0);
v___x_456_ = lean_st_ref_get(v___y_433_);
v_snd_457_ = lean_ctor_get(v___x_456_, 1);
lean_inc(v_snd_457_);
lean_dec(v___x_456_);
v___x_458_ = lean_box(0);
v___x_459_ = l_Lean_LocalDecl_fvarId(v_val_455_);
v___x_460_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_459_, v_snd_457_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = l_Lean_LocalDecl_type(v_val_455_);
lean_inc_ref(v___x_461_);
v___x_462_ = l_Lean_Meta_isProp(v___x_461_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v_a_463_; lean_object* v___f_464_; lean_object* v___x_465_; lean_object* v___f_466_; lean_object* v___y_468_; lean_object* v___y_469_; lean_object* v___y_470_; lean_object* v___y_471_; lean_object* v___y_472_; uint8_t v___x_495_; 
v_a_463_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_a_463_);
lean_dec_ref_known(v___x_462_, 1);
v___f_464_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_464_, 0, v_snd_457_);
v___x_465_ = lean_box(v___x_460_);
v___f_466_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__1___boxed), 2, 1);
lean_closure_set(v___f_466_, 0, v___x_465_);
v___x_495_ = lean_unbox(v_a_463_);
lean_dec(v_a_463_);
if (v___x_495_ == 0)
{
lean_dec_ref(v___x_461_);
v___y_468_ = v___y_433_;
v___y_469_ = v___y_434_;
v___y_470_ = v___y_435_;
v___y_471_ = v___y_436_;
v___y_472_ = v___y_437_;
goto v___jp_467_;
}
else
{
lean_object* v___x_496_; 
lean_inc_ref(v___f_466_);
lean_inc_ref(v___f_464_);
v___x_496_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v___x_461_, v___f_464_, v___f_466_, v___y_435_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v_a_497_; uint8_t v___x_498_; 
v_a_497_ = lean_ctor_get(v___x_496_, 0);
lean_inc(v_a_497_);
lean_dec_ref_known(v___x_496_, 1);
v___x_498_ = lean_unbox(v_a_497_);
lean_dec(v_a_497_);
if (v___x_498_ == 0)
{
v___y_468_ = v___y_433_;
v___y_469_ = v___y_434_;
v___y_470_ = v___y_435_;
v___y_471_ = v___y_436_;
v___y_472_ = v___y_437_;
goto v___jp_467_;
}
else
{
lean_object* v___x_499_; 
lean_inc(v___x_459_);
v___x_499_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_459_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_dec_ref_known(v___x_499_, 1);
v___y_468_ = v___y_433_;
v___y_469_ = v___y_434_;
v___y_470_ = v___y_435_;
v___y_471_ = v___y_436_;
v___y_472_ = v___y_437_;
goto v___jp_467_;
}
else
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_507_; 
lean_dec_ref(v___f_466_);
lean_dec_ref(v___f_464_);
lean_dec(v___x_459_);
lean_del_object(v___x_443_);
v_a_500_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_507_ == 0)
{
v___x_502_ = v___x_499_;
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v___x_499_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_505_; 
if (v_isShared_503_ == 0)
{
v___x_505_ = v___x_502_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_a_500_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
}
}
else
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_515_; 
lean_dec_ref(v___f_466_);
lean_dec_ref(v___f_464_);
lean_dec(v___x_459_);
lean_del_object(v___x_443_);
v_a_508_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_515_ == 0)
{
v___x_510_ = v___x_496_;
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_496_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_513_; 
if (v_isShared_511_ == 0)
{
v___x_513_ = v___x_510_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_a_508_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
v___jp_467_:
{
lean_object* v___x_473_; 
v___x_473_ = l_Lean_LocalDecl_value_x3f(v_val_455_, v___x_460_);
if (lean_obj_tag(v___x_473_) == 1)
{
lean_object* v_val_474_; lean_object* v___x_475_; 
v_val_474_ = lean_ctor_get(v___x_473_, 0);
lean_inc(v_val_474_);
lean_dec_ref_known(v___x_473_, 1);
v___x_475_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v_val_474_, v___f_464_, v___f_466_, v___y_470_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_object* v_a_476_; uint8_t v___x_477_; 
v_a_476_ = lean_ctor_get(v___x_475_, 0);
lean_inc(v_a_476_);
lean_dec_ref_known(v___x_475_, 1);
v___x_477_ = lean_unbox(v_a_476_);
lean_dec(v_a_476_);
if (v___x_477_ == 0)
{
lean_dec(v___x_459_);
v_a_447_ = v___x_458_;
goto v___jp_446_;
}
else
{
lean_object* v___x_478_; 
v___x_478_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_459_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_dec_ref_known(v___x_478_, 1);
v_a_447_ = v___x_458_;
goto v___jp_446_;
}
else
{
lean_object* v_a_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_486_; 
lean_del_object(v___x_443_);
v_a_479_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_486_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_486_ == 0)
{
v___x_481_ = v___x_478_;
v_isShared_482_ = v_isSharedCheck_486_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_a_479_);
lean_dec(v___x_478_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_486_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_484_; 
if (v_isShared_482_ == 0)
{
v___x_484_ = v___x_481_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_a_479_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
}
}
}
else
{
lean_object* v_a_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_494_; 
lean_dec(v___x_459_);
lean_del_object(v___x_443_);
v_a_487_ = lean_ctor_get(v___x_475_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_494_ == 0)
{
v___x_489_ = v___x_475_;
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_a_487_);
lean_dec(v___x_475_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_492_; 
if (v_isShared_490_ == 0)
{
v___x_492_ = v___x_489_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_a_487_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
}
else
{
lean_dec(v___x_473_);
lean_dec_ref(v___f_466_);
lean_dec_ref(v___f_464_);
lean_dec(v___x_459_);
v_a_447_ = v___x_458_;
goto v___jp_446_;
}
}
}
else
{
lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_523_; 
lean_dec_ref(v___x_461_);
lean_dec(v___x_459_);
lean_dec(v_snd_457_);
lean_del_object(v___x_443_);
v_a_516_ = lean_ctor_get(v___x_462_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_523_ == 0)
{
v___x_518_ = v___x_462_;
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___x_462_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_521_; 
if (v_isShared_519_ == 0)
{
v___x_521_ = v___x_518_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_a_516_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
else
{
lean_dec(v___x_459_);
lean_dec(v_snd_457_);
v_a_447_ = v___x_458_;
goto v___jp_446_;
}
}
v___jp_446_:
{
lean_object* v___x_449_; 
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 1, v_a_447_);
lean_ctor_set(v___x_443_, 0, v___x_445_);
v___x_449_ = v___x_443_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_445_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v_a_447_);
v___x_449_ = v_reuseFailAlloc_453_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
size_t v___x_450_; size_t v___x_451_; lean_object* v___x_452_; 
v___x_450_ = ((size_t)1ULL);
v___x_451_ = lean_usize_add(v_i_431_, v___x_450_);
v___x_452_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2_spec__5(v_as_429_, v_sz_430_, v___x_451_, v___x_449_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
return v___x_452_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___boxed(lean_object* v_as_526_, lean_object* v_sz_527_, lean_object* v_i_528_, lean_object* v_b_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
size_t v_sz_boxed_536_; size_t v_i_boxed_537_; lean_object* v_res_538_; 
v_sz_boxed_536_ = lean_unbox_usize(v_sz_527_);
lean_dec(v_sz_527_);
v_i_boxed_537_ = lean_unbox_usize(v_i_528_);
lean_dec(v_i_528_);
v_res_538_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2(v_as_526_, v_sz_boxed_536_, v_i_boxed_537_, v_b_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
lean_dec(v___y_530_);
lean_dec_ref(v_as_526_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3_spec__4(lean_object* v_as_539_, size_t v_sz_540_, size_t v_i_541_, lean_object* v_b_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
uint8_t v___x_549_; 
v___x_549_ = lean_usize_dec_lt(v_i_541_, v_sz_540_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; 
v___x_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_550_, 0, v_b_542_);
return v___x_550_;
}
else
{
lean_object* v_snd_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_634_; 
v_snd_551_ = lean_ctor_get(v_b_542_, 1);
v_isSharedCheck_634_ = !lean_is_exclusive(v_b_542_);
if (v_isSharedCheck_634_ == 0)
{
lean_object* v_unused_635_; 
v_unused_635_ = lean_ctor_get(v_b_542_, 0);
lean_dec(v_unused_635_);
v___x_553_ = v_b_542_;
v_isShared_554_ = v_isSharedCheck_634_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_snd_551_);
lean_dec(v_b_542_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_634_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_555_; lean_object* v_a_557_; lean_object* v_a_564_; 
v___x_555_ = lean_box(0);
v_a_564_ = lean_array_uget_borrowed(v_as_539_, v_i_541_);
if (lean_obj_tag(v_a_564_) == 0)
{
v_a_557_ = v_snd_551_;
goto v___jp_556_;
}
else
{
lean_object* v_val_565_; lean_object* v___x_566_; lean_object* v_snd_567_; lean_object* v___x_568_; lean_object* v___x_569_; uint8_t v___x_570_; 
lean_dec(v_snd_551_);
v_val_565_ = lean_ctor_get(v_a_564_, 0);
v___x_566_ = lean_st_ref_get(v___y_543_);
v_snd_567_ = lean_ctor_get(v___x_566_, 1);
lean_inc(v_snd_567_);
lean_dec(v___x_566_);
v___x_568_ = lean_box(0);
v___x_569_ = l_Lean_LocalDecl_fvarId(v_val_565_);
v___x_570_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_569_, v_snd_567_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = l_Lean_LocalDecl_type(v_val_565_);
lean_inc_ref(v___x_571_);
v___x_572_ = l_Lean_Meta_isProp(v___x_571_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_573_; lean_object* v___f_574_; lean_object* v___x_575_; lean_object* v___f_576_; lean_object* v___y_578_; lean_object* v___y_579_; lean_object* v___y_580_; lean_object* v___y_581_; lean_object* v___y_582_; uint8_t v___x_605_; 
v_a_573_ = lean_ctor_get(v___x_572_, 0);
lean_inc(v_a_573_);
lean_dec_ref_known(v___x_572_, 1);
v___f_574_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_574_, 0, v_snd_567_);
v___x_575_ = lean_box(v___x_570_);
v___f_576_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__1___boxed), 2, 1);
lean_closure_set(v___f_576_, 0, v___x_575_);
v___x_605_ = lean_unbox(v_a_573_);
lean_dec(v_a_573_);
if (v___x_605_ == 0)
{
lean_dec_ref(v___x_571_);
v___y_578_ = v___y_543_;
v___y_579_ = v___y_544_;
v___y_580_ = v___y_545_;
v___y_581_ = v___y_546_;
v___y_582_ = v___y_547_;
goto v___jp_577_;
}
else
{
lean_object* v___x_606_; 
lean_inc_ref(v___f_576_);
lean_inc_ref(v___f_574_);
v___x_606_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v___x_571_, v___f_574_, v___f_576_, v___y_545_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v_a_607_; uint8_t v___x_608_; 
v_a_607_ = lean_ctor_get(v___x_606_, 0);
lean_inc(v_a_607_);
lean_dec_ref_known(v___x_606_, 1);
v___x_608_ = lean_unbox(v_a_607_);
lean_dec(v_a_607_);
if (v___x_608_ == 0)
{
v___y_578_ = v___y_543_;
v___y_579_ = v___y_544_;
v___y_580_ = v___y_545_;
v___y_581_ = v___y_546_;
v___y_582_ = v___y_547_;
goto v___jp_577_;
}
else
{
lean_object* v___x_609_; 
lean_inc(v___x_569_);
v___x_609_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_569_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
if (lean_obj_tag(v___x_609_) == 0)
{
lean_dec_ref_known(v___x_609_, 1);
v___y_578_ = v___y_543_;
v___y_579_ = v___y_544_;
v___y_580_ = v___y_545_;
v___y_581_ = v___y_546_;
v___y_582_ = v___y_547_;
goto v___jp_577_;
}
else
{
lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_617_; 
lean_dec_ref(v___f_576_);
lean_dec_ref(v___f_574_);
lean_dec(v___x_569_);
lean_del_object(v___x_553_);
v_a_610_ = lean_ctor_get(v___x_609_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_617_ == 0)
{
v___x_612_ = v___x_609_;
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_609_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_615_; 
if (v_isShared_613_ == 0)
{
v___x_615_ = v___x_612_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_a_610_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
}
else
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_625_; 
lean_dec_ref(v___f_576_);
lean_dec_ref(v___f_574_);
lean_dec(v___x_569_);
lean_del_object(v___x_553_);
v_a_618_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_625_ == 0)
{
v___x_620_ = v___x_606_;
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_606_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_623_; 
if (v_isShared_621_ == 0)
{
v___x_623_ = v___x_620_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_618_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
v___jp_577_:
{
lean_object* v___x_583_; 
v___x_583_ = l_Lean_LocalDecl_value_x3f(v_val_565_, v___x_570_);
if (lean_obj_tag(v___x_583_) == 1)
{
lean_object* v_val_584_; lean_object* v___x_585_; 
v_val_584_ = lean_ctor_get(v___x_583_, 0);
lean_inc(v_val_584_);
lean_dec_ref_known(v___x_583_, 1);
v___x_585_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v_val_584_, v___f_574_, v___f_576_, v___y_580_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v_a_586_; uint8_t v___x_587_; 
v_a_586_ = lean_ctor_get(v___x_585_, 0);
lean_inc(v_a_586_);
lean_dec_ref_known(v___x_585_, 1);
v___x_587_ = lean_unbox(v_a_586_);
lean_dec(v_a_586_);
if (v___x_587_ == 0)
{
lean_dec(v___x_569_);
v_a_557_ = v___x_568_;
goto v___jp_556_;
}
else
{
lean_object* v___x_588_; 
v___x_588_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_569_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_dec_ref_known(v___x_588_, 1);
v_a_557_ = v___x_568_;
goto v___jp_556_;
}
else
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
lean_del_object(v___x_553_);
v_a_589_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_596_ == 0)
{
v___x_591_ = v___x_588_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_588_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_594_; 
if (v_isShared_592_ == 0)
{
v___x_594_ = v___x_591_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_a_589_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
}
else
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_604_; 
lean_dec(v___x_569_);
lean_del_object(v___x_553_);
v_a_597_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_604_ == 0)
{
v___x_599_ = v___x_585_;
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_585_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_602_; 
if (v_isShared_600_ == 0)
{
v___x_602_ = v___x_599_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_a_597_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
else
{
lean_dec(v___x_583_);
lean_dec_ref(v___f_576_);
lean_dec_ref(v___f_574_);
lean_dec(v___x_569_);
v_a_557_ = v___x_568_;
goto v___jp_556_;
}
}
}
else
{
lean_object* v_a_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_633_; 
lean_dec_ref(v___x_571_);
lean_dec(v___x_569_);
lean_dec(v_snd_567_);
lean_del_object(v___x_553_);
v_a_626_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_633_ == 0)
{
v___x_628_ = v___x_572_;
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_a_626_);
lean_dec(v___x_572_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_631_; 
if (v_isShared_629_ == 0)
{
v___x_631_ = v___x_628_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_a_626_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
else
{
lean_dec(v___x_569_);
lean_dec(v_snd_567_);
v_a_557_ = v___x_568_;
goto v___jp_556_;
}
}
v___jp_556_:
{
lean_object* v___x_559_; 
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 1, v_a_557_);
lean_ctor_set(v___x_553_, 0, v___x_555_);
v___x_559_ = v___x_553_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_555_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v_a_557_);
v___x_559_ = v_reuseFailAlloc_563_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
size_t v___x_560_; size_t v___x_561_; 
v___x_560_ = ((size_t)1ULL);
v___x_561_ = lean_usize_add(v_i_541_, v___x_560_);
v_i_541_ = v___x_561_;
v_b_542_ = v___x_559_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3_spec__4___boxed(lean_object* v_as_636_, lean_object* v_sz_637_, lean_object* v_i_638_, lean_object* v_b_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
size_t v_sz_boxed_646_; size_t v_i_boxed_647_; lean_object* v_res_648_; 
v_sz_boxed_646_ = lean_unbox_usize(v_sz_637_);
lean_dec(v_sz_637_);
v_i_boxed_647_ = lean_unbox_usize(v_i_638_);
lean_dec(v_i_638_);
v_res_648_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3_spec__4(v_as_636_, v_sz_boxed_646_, v_i_boxed_647_, v_b_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec(v___y_640_);
lean_dec_ref(v_as_636_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3(lean_object* v_as_649_, size_t v_sz_650_, size_t v_i_651_, lean_object* v_b_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
uint8_t v___x_659_; 
v___x_659_ = lean_usize_dec_lt(v_i_651_, v_sz_650_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; 
v___x_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_660_, 0, v_b_652_);
return v___x_660_;
}
else
{
lean_object* v_snd_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_744_; 
v_snd_661_ = lean_ctor_get(v_b_652_, 1);
v_isSharedCheck_744_ = !lean_is_exclusive(v_b_652_);
if (v_isSharedCheck_744_ == 0)
{
lean_object* v_unused_745_; 
v_unused_745_ = lean_ctor_get(v_b_652_, 0);
lean_dec(v_unused_745_);
v___x_663_ = v_b_652_;
v_isShared_664_ = v_isSharedCheck_744_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_snd_661_);
lean_dec(v_b_652_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_744_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_665_; lean_object* v_a_667_; lean_object* v_a_674_; 
v___x_665_ = lean_box(0);
v_a_674_ = lean_array_uget_borrowed(v_as_649_, v_i_651_);
if (lean_obj_tag(v_a_674_) == 0)
{
v_a_667_ = v_snd_661_;
goto v___jp_666_;
}
else
{
lean_object* v_val_675_; lean_object* v___x_676_; lean_object* v_snd_677_; lean_object* v___x_678_; lean_object* v___x_679_; uint8_t v___x_680_; 
lean_dec(v_snd_661_);
v_val_675_ = lean_ctor_get(v_a_674_, 0);
v___x_676_ = lean_st_ref_get(v___y_653_);
v_snd_677_ = lean_ctor_get(v___x_676_, 1);
lean_inc(v_snd_677_);
lean_dec(v___x_676_);
v___x_678_ = lean_box(0);
v___x_679_ = l_Lean_LocalDecl_fvarId(v_val_675_);
v___x_680_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_679_, v_snd_677_);
if (v___x_680_ == 0)
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = l_Lean_LocalDecl_type(v_val_675_);
lean_inc_ref(v___x_681_);
v___x_682_ = l_Lean_Meta_isProp(v___x_681_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
if (lean_obj_tag(v___x_682_) == 0)
{
lean_object* v_a_683_; lean_object* v___f_684_; lean_object* v___x_685_; lean_object* v___f_686_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; uint8_t v___x_715_; 
v_a_683_ = lean_ctor_get(v___x_682_, 0);
lean_inc(v_a_683_);
lean_dec_ref_known(v___x_682_, 1);
v___f_684_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_684_, 0, v_snd_677_);
v___x_685_ = lean_box(v___x_680_);
v___f_686_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__1___boxed), 2, 1);
lean_closure_set(v___f_686_, 0, v___x_685_);
v___x_715_ = lean_unbox(v_a_683_);
lean_dec(v_a_683_);
if (v___x_715_ == 0)
{
lean_dec_ref(v___x_681_);
v___y_688_ = v___y_653_;
v___y_689_ = v___y_654_;
v___y_690_ = v___y_655_;
v___y_691_ = v___y_656_;
v___y_692_ = v___y_657_;
goto v___jp_687_;
}
else
{
lean_object* v___x_716_; 
lean_inc_ref(v___f_686_);
lean_inc_ref(v___f_684_);
v___x_716_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v___x_681_, v___f_684_, v___f_686_, v___y_655_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v_a_717_; uint8_t v___x_718_; 
v_a_717_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_a_717_);
lean_dec_ref_known(v___x_716_, 1);
v___x_718_ = lean_unbox(v_a_717_);
lean_dec(v_a_717_);
if (v___x_718_ == 0)
{
v___y_688_ = v___y_653_;
v___y_689_ = v___y_654_;
v___y_690_ = v___y_655_;
v___y_691_ = v___y_656_;
v___y_692_ = v___y_657_;
goto v___jp_687_;
}
else
{
lean_object* v___x_719_; 
lean_inc(v___x_679_);
v___x_719_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_679_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_dec_ref_known(v___x_719_, 1);
v___y_688_ = v___y_653_;
v___y_689_ = v___y_654_;
v___y_690_ = v___y_655_;
v___y_691_ = v___y_656_;
v___y_692_ = v___y_657_;
goto v___jp_687_;
}
else
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_727_; 
lean_dec_ref(v___f_686_);
lean_dec_ref(v___f_684_);
lean_dec(v___x_679_);
lean_del_object(v___x_663_);
v_a_720_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_727_ == 0)
{
v___x_722_ = v___x_719_;
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_719_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_725_; 
if (v_isShared_723_ == 0)
{
v___x_725_ = v___x_722_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_a_720_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
}
}
else
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_735_; 
lean_dec_ref(v___f_686_);
lean_dec_ref(v___f_684_);
lean_dec(v___x_679_);
lean_del_object(v___x_663_);
v_a_728_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_735_ == 0)
{
v___x_730_ = v___x_716_;
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_716_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_a_728_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
}
v___jp_687_:
{
lean_object* v___x_693_; 
v___x_693_ = l_Lean_LocalDecl_value_x3f(v_val_675_, v___x_680_);
if (lean_obj_tag(v___x_693_) == 1)
{
lean_object* v_val_694_; lean_object* v___x_695_; 
v_val_694_ = lean_ctor_get(v___x_693_, 0);
lean_inc(v_val_694_);
lean_dec_ref_known(v___x_693_, 1);
v___x_695_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v_val_694_, v___f_684_, v___f_686_, v___y_690_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v_a_696_; uint8_t v___x_697_; 
v_a_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_a_696_);
lean_dec_ref_known(v___x_695_, 1);
v___x_697_ = lean_unbox(v_a_696_);
lean_dec(v_a_696_);
if (v___x_697_ == 0)
{
lean_dec(v___x_679_);
v_a_667_ = v___x_678_;
goto v___jp_666_;
}
else
{
lean_object* v___x_698_; 
v___x_698_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_679_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_dec_ref_known(v___x_698_, 1);
v_a_667_ = v___x_678_;
goto v___jp_666_;
}
else
{
lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
lean_del_object(v___x_663_);
v_a_699_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_706_ == 0)
{
v___x_701_ = v___x_698_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_698_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_704_; 
if (v_isShared_702_ == 0)
{
v___x_704_ = v___x_701_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_a_699_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
}
else
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
lean_dec(v___x_679_);
lean_del_object(v___x_663_);
v_a_707_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v___x_695_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_695_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_a_707_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
else
{
lean_dec(v___x_693_);
lean_dec_ref(v___f_686_);
lean_dec_ref(v___f_684_);
lean_dec(v___x_679_);
v_a_667_ = v___x_678_;
goto v___jp_666_;
}
}
}
else
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
lean_dec_ref(v___x_681_);
lean_dec(v___x_679_);
lean_dec(v_snd_677_);
lean_del_object(v___x_663_);
v_a_736_ = lean_ctor_get(v___x_682_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_743_ == 0)
{
v___x_738_ = v___x_682_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_682_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_a_736_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
else
{
lean_dec(v___x_679_);
lean_dec(v_snd_677_);
v_a_667_ = v___x_678_;
goto v___jp_666_;
}
}
v___jp_666_:
{
lean_object* v___x_669_; 
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 1, v_a_667_);
lean_ctor_set(v___x_663_, 0, v___x_665_);
v___x_669_ = v___x_663_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_665_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v_a_667_);
v___x_669_ = v_reuseFailAlloc_673_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
size_t v___x_670_; size_t v___x_671_; lean_object* v___x_672_; 
v___x_670_ = ((size_t)1ULL);
v___x_671_ = lean_usize_add(v_i_651_, v___x_670_);
v___x_672_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3_spec__4(v_as_649_, v_sz_650_, v___x_671_, v___x_669_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
return v___x_672_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3___boxed(lean_object* v_as_746_, lean_object* v_sz_747_, lean_object* v_i_748_, lean_object* v_b_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
size_t v_sz_boxed_756_; size_t v_i_boxed_757_; lean_object* v_res_758_; 
v_sz_boxed_756_ = lean_unbox_usize(v_sz_747_);
lean_dec(v_sz_747_);
v_i_boxed_757_ = lean_unbox_usize(v_i_748_);
lean_dec(v_i_748_);
v_res_758_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3(v_as_746_, v_sz_boxed_756_, v_i_boxed_757_, v_b_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec(v___y_750_);
lean_dec_ref(v_as_746_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1(lean_object* v_init_759_, lean_object* v_n_760_, lean_object* v_b_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
if (lean_obj_tag(v_n_760_) == 0)
{
lean_object* v_cs_768_; lean_object* v___x_769_; lean_object* v___x_770_; size_t v_sz_771_; size_t v___x_772_; lean_object* v___x_773_; 
v_cs_768_ = lean_ctor_get(v_n_760_, 0);
v___x_769_ = lean_box(0);
v___x_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_770_, 0, v___x_769_);
lean_ctor_set(v___x_770_, 1, v_b_761_);
v_sz_771_ = lean_array_size(v_cs_768_);
v___x_772_ = ((size_t)0ULL);
v___x_773_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__2(v_init_759_, v_cs_768_, v_sz_771_, v___x_772_, v___x_770_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_788_; 
v_a_774_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_788_ == 0)
{
v___x_776_ = v___x_773_;
v_isShared_777_ = v_isSharedCheck_788_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_773_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_788_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v_fst_778_; 
v_fst_778_ = lean_ctor_get(v_a_774_, 0);
if (lean_obj_tag(v_fst_778_) == 0)
{
lean_object* v_snd_779_; lean_object* v___x_780_; lean_object* v___x_782_; 
v_snd_779_ = lean_ctor_get(v_a_774_, 1);
lean_inc(v_snd_779_);
lean_dec(v_a_774_);
v___x_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_780_, 0, v_snd_779_);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 0, v___x_780_);
v___x_782_ = v___x_776_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_780_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
else
{
lean_object* v_val_784_; lean_object* v___x_786_; 
lean_inc_ref(v_fst_778_);
lean_dec(v_a_774_);
v_val_784_ = lean_ctor_get(v_fst_778_, 0);
lean_inc(v_val_784_);
lean_dec_ref_known(v_fst_778_, 1);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 0, v_val_784_);
v___x_786_ = v___x_776_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_val_784_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
else
{
lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_796_; 
v_a_789_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_796_ == 0)
{
v___x_791_ = v___x_773_;
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___x_773_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_794_; 
if (v_isShared_792_ == 0)
{
v___x_794_ = v___x_791_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_a_789_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
}
else
{
lean_object* v_vs_797_; lean_object* v___x_798_; lean_object* v___x_799_; size_t v_sz_800_; size_t v___x_801_; lean_object* v___x_802_; 
v_vs_797_ = lean_ctor_get(v_n_760_, 0);
v___x_798_ = lean_box(0);
v___x_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
lean_ctor_set(v___x_799_, 1, v_b_761_);
v_sz_800_ = lean_array_size(v_vs_797_);
v___x_801_ = ((size_t)0ULL);
v___x_802_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3(v_vs_797_, v_sz_800_, v___x_801_, v___x_799_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_817_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_817_ == 0)
{
v___x_805_ = v___x_802_;
v_isShared_806_ = v_isSharedCheck_817_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v___x_802_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_817_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v_fst_807_; 
v_fst_807_ = lean_ctor_get(v_a_803_, 0);
if (lean_obj_tag(v_fst_807_) == 0)
{
lean_object* v_snd_808_; lean_object* v___x_809_; lean_object* v___x_811_; 
v_snd_808_ = lean_ctor_get(v_a_803_, 1);
lean_inc(v_snd_808_);
lean_dec(v_a_803_);
v___x_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_809_, 0, v_snd_808_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 0, v___x_809_);
v___x_811_ = v___x_805_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_809_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
else
{
lean_object* v_val_813_; lean_object* v___x_815_; 
lean_inc_ref(v_fst_807_);
lean_dec(v_a_803_);
v_val_813_ = lean_ctor_get(v_fst_807_, 0);
lean_inc(v_val_813_);
lean_dec_ref_known(v_fst_807_, 1);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 0, v_val_813_);
v___x_815_ = v___x_805_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_val_813_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
else
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_825_; 
v_a_818_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_825_ == 0)
{
v___x_820_ = v___x_802_;
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_802_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_823_; 
if (v_isShared_821_ == 0)
{
v___x_823_ = v___x_820_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_a_818_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__2(lean_object* v_init_826_, lean_object* v_as_827_, size_t v_sz_828_, size_t v_i_829_, lean_object* v_b_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
uint8_t v___x_837_; 
v___x_837_ = lean_usize_dec_lt(v_i_829_, v_sz_828_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; 
v___x_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_838_, 0, v_b_830_);
return v___x_838_;
}
else
{
lean_object* v_snd_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_873_; 
v_snd_839_ = lean_ctor_get(v_b_830_, 1);
v_isSharedCheck_873_ = !lean_is_exclusive(v_b_830_);
if (v_isSharedCheck_873_ == 0)
{
lean_object* v_unused_874_; 
v_unused_874_ = lean_ctor_get(v_b_830_, 0);
lean_dec(v_unused_874_);
v___x_841_ = v_b_830_;
v_isShared_842_ = v_isSharedCheck_873_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_snd_839_);
lean_dec(v_b_830_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_873_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v_a_843_; lean_object* v___x_844_; 
v_a_843_ = lean_array_uget_borrowed(v_as_827_, v_i_829_);
lean_inc(v_snd_839_);
v___x_844_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1(v_init_826_, v_a_843_, v_snd_839_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_864_; 
v_a_845_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_864_ == 0)
{
v___x_847_ = v___x_844_;
v_isShared_848_ = v_isSharedCheck_864_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_844_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_864_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
if (lean_obj_tag(v_a_845_) == 0)
{
lean_object* v___x_849_; lean_object* v___x_851_; 
v___x_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_849_, 0, v_a_845_);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 0, v___x_849_);
v___x_851_ = v___x_841_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_849_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v_snd_839_);
v___x_851_ = v_reuseFailAlloc_855_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
lean_object* v___x_853_; 
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 0, v___x_851_);
v___x_853_ = v___x_847_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_851_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
else
{
lean_object* v_a_856_; lean_object* v___x_857_; lean_object* v___x_859_; 
lean_del_object(v___x_847_);
lean_dec(v_snd_839_);
v_a_856_ = lean_ctor_get(v_a_845_, 0);
lean_inc(v_a_856_);
lean_dec_ref_known(v_a_845_, 1);
v___x_857_ = lean_box(0);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 1, v_a_856_);
lean_ctor_set(v___x_841_, 0, v___x_857_);
v___x_859_ = v___x_841_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_857_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v_a_856_);
v___x_859_ = v_reuseFailAlloc_863_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
size_t v___x_860_; size_t v___x_861_; 
v___x_860_ = ((size_t)1ULL);
v___x_861_ = lean_usize_add(v_i_829_, v___x_860_);
v_i_829_ = v___x_861_;
v_b_830_ = v___x_859_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_872_; 
lean_del_object(v___x_841_);
lean_dec(v_snd_839_);
v_a_865_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_872_ == 0)
{
v___x_867_ = v___x_844_;
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_844_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_870_; 
if (v_isShared_868_ == 0)
{
v___x_870_ = v___x_867_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_a_865_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__2___boxed(lean_object* v_init_875_, lean_object* v_as_876_, lean_object* v_sz_877_, lean_object* v_i_878_, lean_object* v_b_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
size_t v_sz_boxed_886_; size_t v_i_boxed_887_; lean_object* v_res_888_; 
v_sz_boxed_886_ = lean_unbox_usize(v_sz_877_);
lean_dec(v_sz_877_);
v_i_boxed_887_ = lean_unbox_usize(v_i_878_);
lean_dec(v_i_878_);
v_res_888_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__2(v_init_875_, v_as_876_, v_sz_boxed_886_, v_i_boxed_887_, v_b_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v___y_880_);
lean_dec_ref(v_as_876_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1___boxed(lean_object* v_init_889_, lean_object* v_n_890_, lean_object* v_b_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1(v_init_889_, v_n_890_, v_b_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
lean_dec(v___y_892_);
lean_dec_ref(v_n_890_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1(lean_object* v_t_899_, lean_object* v_init_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v_root_907_; lean_object* v_tail_908_; lean_object* v___x_909_; 
v_root_907_ = lean_ctor_get(v_t_899_, 0);
v_tail_908_ = lean_ctor_get(v_t_899_, 1);
v___x_909_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1(v_init_900_, v_root_907_, v_init_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_946_; 
v_a_910_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_946_ == 0)
{
v___x_912_ = v___x_909_;
v_isShared_913_ = v_isSharedCheck_946_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_909_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_946_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
if (lean_obj_tag(v_a_910_) == 0)
{
lean_object* v_a_914_; lean_object* v___x_916_; 
v_a_914_ = lean_ctor_get(v_a_910_, 0);
lean_inc(v_a_914_);
lean_dec_ref_known(v_a_910_, 1);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 0, v_a_914_);
v___x_916_ = v___x_912_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_a_914_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
else
{
lean_object* v_a_918_; lean_object* v___x_919_; lean_object* v___x_920_; size_t v_sz_921_; size_t v___x_922_; lean_object* v___x_923_; 
lean_del_object(v___x_912_);
v_a_918_ = lean_ctor_get(v_a_910_, 0);
lean_inc(v_a_918_);
lean_dec_ref_known(v_a_910_, 1);
v___x_919_ = lean_box(0);
v___x_920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_919_);
lean_ctor_set(v___x_920_, 1, v_a_918_);
v_sz_921_ = lean_array_size(v_tail_908_);
v___x_922_ = ((size_t)0ULL);
v___x_923_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2(v_tail_908_, v_sz_921_, v___x_922_, v___x_920_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
if (lean_obj_tag(v___x_923_) == 0)
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_937_; 
v_a_924_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_937_ == 0)
{
v___x_926_ = v___x_923_;
v_isShared_927_ = v_isSharedCheck_937_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_923_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_937_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v_fst_928_; 
v_fst_928_ = lean_ctor_get(v_a_924_, 0);
if (lean_obj_tag(v_fst_928_) == 0)
{
lean_object* v_snd_929_; lean_object* v___x_931_; 
v_snd_929_ = lean_ctor_get(v_a_924_, 1);
lean_inc(v_snd_929_);
lean_dec(v_a_924_);
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 0, v_snd_929_);
v___x_931_ = v___x_926_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_snd_929_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
else
{
lean_object* v_val_933_; lean_object* v___x_935_; 
lean_inc_ref(v_fst_928_);
lean_dec(v_a_924_);
v_val_933_ = lean_ctor_get(v_fst_928_, 0);
lean_inc(v_val_933_);
lean_dec_ref_known(v_fst_928_, 1);
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 0, v_val_933_);
v___x_935_ = v___x_926_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_val_933_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
else
{
lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_945_; 
v_a_938_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_945_ == 0)
{
v___x_940_ = v___x_923_;
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_923_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_943_; 
if (v_isShared_941_ == 0)
{
v___x_943_ = v___x_940_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_a_938_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
}
}
else
{
lean_object* v_a_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_954_; 
v_a_947_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_954_ == 0)
{
v___x_949_ = v___x_909_;
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_a_947_);
lean_dec(v___x_909_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_952_; 
if (v_isShared_950_ == 0)
{
v___x_952_ = v___x_949_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_a_947_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1___boxed(lean_object* v_t_955_, lean_object* v_init_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1(v_t_955_, v_init_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v_t_955_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep(lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_){
_start:
{
lean_object* v_lctx_970_; lean_object* v_decls_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v_lctx_970_ = lean_ctor_get(v_a_965_, 2);
v_decls_971_ = lean_ctor_get(v_lctx_970_, 1);
v___x_972_ = lean_box(0);
v___x_973_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1(v_decls_971_, v___x_972_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_980_; 
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_980_ == 0)
{
lean_object* v_unused_981_; 
v_unused_981_ = lean_ctor_get(v___x_973_, 0);
lean_dec(v_unused_981_);
v___x_975_ = v___x_973_;
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
else
{
lean_dec(v___x_973_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v___x_972_);
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v___x_972_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
else
{
return v___x_973_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep___boxed(lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep(v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_);
lean_dec(v_a_986_);
lean_dec_ref(v_a_985_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
lean_dec(v_a_982_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectProps(lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_){
_start:
{
lean_object* v___x_995_; lean_object* v_snd_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1020_; 
v___x_995_ = lean_st_ref_take(v_a_989_);
v_snd_996_ = lean_ctor_get(v___x_995_, 1);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1020_ == 0)
{
lean_object* v_unused_1021_; 
v_unused_1021_ = lean_ctor_get(v___x_995_, 0);
lean_dec(v_unused_1021_);
v___x_998_ = v___x_995_;
v_isShared_999_ = v_isSharedCheck_1020_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_snd_996_);
lean_dec(v___x_995_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1020_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
uint8_t v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1003_; 
v___x_1000_ = 0;
v___x_1001_ = lean_box(v___x_1000_);
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 0, v___x_1001_);
v___x_1003_ = v___x_998_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_1001_);
lean_ctor_set(v_reuseFailAlloc_1019_, 1, v_snd_996_);
v___x_1003_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1004_ = lean_st_ref_set(v_a_989_, v___x_1003_);
v___x_1005_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep(v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1017_; 
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1017_ == 0)
{
lean_object* v_unused_1018_; 
v_unused_1018_ = lean_ctor_get(v___x_1005_, 0);
lean_dec(v_unused_1018_);
v___x_1007_ = v___x_1005_;
v_isShared_1008_ = v_isSharedCheck_1017_;
goto v_resetjp_1006_;
}
else
{
lean_dec(v___x_1005_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1017_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1009_; lean_object* v_fst_1010_; uint8_t v___x_1011_; 
v___x_1009_ = lean_st_ref_get(v_a_989_);
v_fst_1010_ = lean_ctor_get(v___x_1009_, 0);
lean_inc(v_fst_1010_);
lean_dec(v___x_1009_);
v___x_1011_ = lean_unbox(v_fst_1010_);
lean_dec(v_fst_1010_);
if (v___x_1011_ == 0)
{
lean_object* v___x_1012_; lean_object* v___x_1014_; 
v___x_1012_ = lean_box(0);
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 0, v___x_1012_);
v___x_1014_ = v___x_1007_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v___x_1012_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
else
{
lean_del_object(v___x_1007_);
goto _start;
}
}
}
else
{
return v___x_1005_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectProps___boxed(lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectProps(v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_);
lean_dec(v_a_1026_);
lean_dec_ref(v_a_1025_);
lean_dec(v_a_1024_);
lean_dec_ref(v_a_1023_);
lean_dec(v_a_1022_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed_spec__0(lean_object* v_as_1029_, size_t v_i_1030_, size_t v_stop_1031_, lean_object* v_b_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
uint8_t v___x_1039_; 
v___x_1039_ = lean_usize_dec_eq(v_i_1030_, v_stop_1031_);
if (v___x_1039_ == 0)
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = lean_array_uget_borrowed(v_as_1029_, v_i_1030_);
lean_inc(v___x_1040_);
v___x_1041_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_1040_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_);
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_object* v_a_1042_; size_t v___x_1043_; size_t v___x_1044_; 
v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
lean_inc(v_a_1042_);
lean_dec_ref_known(v___x_1041_, 1);
v___x_1043_ = ((size_t)1ULL);
v___x_1044_ = lean_usize_add(v_i_1030_, v___x_1043_);
v_i_1030_ = v___x_1044_;
v_b_1032_ = v_a_1042_;
goto _start;
}
else
{
return v___x_1041_;
}
}
else
{
lean_object* v___x_1046_; 
v___x_1046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1046_, 0, v_b_1032_);
return v___x_1046_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed_spec__0___boxed(lean_object* v_as_1047_, lean_object* v_i_1048_, lean_object* v_stop_1049_, lean_object* v_b_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
size_t v_i_boxed_1057_; size_t v_stop_boxed_1058_; lean_object* v_res_1059_; 
v_i_boxed_1057_ = lean_unbox_usize(v_i_1048_);
lean_dec(v_i_1048_);
v_stop_boxed_1058_ = lean_unbox_usize(v_stop_1049_);
lean_dec(v_stop_1049_);
v_res_1059_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed_spec__0(v_as_1047_, v_i_boxed_1057_, v_stop_boxed_1058_, v_b_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec_ref(v_as_1047_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed(lean_object* v_mvarId_1060_, lean_object* v_toPreserve_1061_, uint8_t v_indirectProps_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_){
_start:
{
lean_object* v___y_1070_; lean_object* v___y_1085_; lean_object* v___x_1094_; 
v___x_1094_ = l_Lean_MVarId_getType(v_mvarId_1060_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
if (lean_obj_tag(v___x_1094_) == 0)
{
lean_object* v_a_1095_; lean_object* v___x_1096_; lean_object* v_a_1097_; lean_object* v___x_1098_; 
v_a_1095_ = lean_ctor_get(v___x_1094_, 0);
lean_inc(v_a_1095_);
lean_dec_ref_known(v___x_1094_, 1);
v___x_1096_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0___redArg(v_a_1095_, v_a_1065_);
v_a_1097_ = lean_ctor_get(v___x_1096_, 0);
lean_inc(v_a_1097_);
lean_dec_ref(v___x_1096_);
v___x_1098_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars(v_a_1097_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v___x_1099_; lean_object* v___x_1100_; uint8_t v___x_1101_; 
lean_dec_ref_known(v___x_1098_, 1);
v___x_1099_ = lean_unsigned_to_nat(0u);
v___x_1100_ = lean_array_get_size(v_toPreserve_1061_);
v___x_1101_ = lean_nat_dec_lt(v___x_1099_, v___x_1100_);
if (v___x_1101_ == 0)
{
goto v___jp_1074_;
}
else
{
lean_object* v___x_1102_; uint8_t v___x_1103_; 
v___x_1102_ = lean_box(0);
v___x_1103_ = lean_nat_dec_le(v___x_1100_, v___x_1100_);
if (v___x_1103_ == 0)
{
if (v___x_1101_ == 0)
{
goto v___jp_1074_;
}
else
{
size_t v___x_1104_; size_t v___x_1105_; lean_object* v___x_1106_; 
v___x_1104_ = ((size_t)0ULL);
v___x_1105_ = lean_usize_of_nat(v___x_1100_);
v___x_1106_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed_spec__0(v_toPreserve_1061_, v___x_1104_, v___x_1105_, v___x_1102_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
v___y_1085_ = v___x_1106_;
goto v___jp_1084_;
}
}
else
{
size_t v___x_1107_; size_t v___x_1108_; lean_object* v___x_1109_; 
v___x_1107_ = ((size_t)0ULL);
v___x_1108_ = lean_usize_of_nat(v___x_1100_);
v___x_1109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed_spec__0(v_toPreserve_1061_, v___x_1107_, v___x_1108_, v___x_1102_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
v___y_1085_ = v___x_1109_;
goto v___jp_1084_;
}
}
}
else
{
lean_object* v_a_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1117_; 
v_a_1110_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1112_ = v___x_1098_;
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_a_1110_);
lean_dec(v___x_1098_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1115_; 
if (v_isShared_1113_ == 0)
{
v___x_1115_ = v___x_1112_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_a_1110_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
else
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
v_a_1118_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1120_ = v___x_1094_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1094_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1118_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
v___jp_1069_:
{
lean_object* v___x_1071_; lean_object* v_snd_1072_; lean_object* v___x_1073_; 
v___x_1071_ = lean_st_ref_get(v___y_1070_);
v_snd_1072_ = lean_ctor_get(v___x_1071_, 1);
lean_inc(v_snd_1072_);
lean_dec(v___x_1071_);
v___x_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1073_, 0, v_snd_1072_);
return v___x_1073_;
}
v___jp_1074_:
{
if (v_indirectProps_1062_ == 0)
{
v___y_1070_ = v_a_1063_;
goto v___jp_1069_;
}
else
{
lean_object* v___x_1075_; 
v___x_1075_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectProps(v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_dec_ref_known(v___x_1075_, 1);
v___y_1070_ = v_a_1063_;
goto v___jp_1069_;
}
else
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1083_; 
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1078_ = v___x_1075_;
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_1075_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1081_; 
if (v_isShared_1079_ == 0)
{
v___x_1081_ = v___x_1078_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_a_1076_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
}
}
v___jp_1084_:
{
if (lean_obj_tag(v___y_1085_) == 0)
{
lean_dec_ref_known(v___y_1085_, 1);
goto v___jp_1074_;
}
else
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1093_; 
v_a_1086_ = lean_ctor_get(v___y_1085_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___y_1085_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1088_ = v___y_1085_;
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___y_1085_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1091_; 
if (v_isShared_1089_ == 0)
{
v___x_1091_ = v___x_1088_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_a_1086_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed___boxed(lean_object* v_mvarId_1126_, lean_object* v_toPreserve_1127_, lean_object* v_indirectProps_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_){
_start:
{
uint8_t v_indirectProps_boxed_1135_; lean_object* v_res_1136_; 
v_indirectProps_boxed_1135_ = lean_unbox(v_indirectProps_1128_);
v_res_1136_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed(v_mvarId_1126_, v_toPreserve_1127_, v_indirectProps_boxed_1135_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_);
lean_dec(v_a_1133_);
lean_dec_ref(v_a_1132_);
lean_dec(v_a_1131_);
lean_dec_ref(v_a_1130_);
lean_dec(v_a_1129_);
lean_dec_ref(v_toPreserve_1127_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___redArg(lean_object* v_e_1137_, lean_object* v___y_1138_){
_start:
{
uint8_t v___x_1140_; uint8_t v___x_1141_; 
v___x_1140_ = l_Lean_Expr_hasMVar(v_e_1137_);
v___x_1141_ = lean_bool_not(v___x_1140_);
if (v___x_1141_ == 0)
{
lean_object* v___x_1142_; lean_object* v_mctx_1143_; lean_object* v___x_1144_; lean_object* v_fst_1145_; lean_object* v_snd_1146_; lean_object* v___x_1147_; lean_object* v_cache_1148_; lean_object* v_zetaDeltaFVarIds_1149_; lean_object* v_postponed_1150_; lean_object* v_diag_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1160_; 
v___x_1142_ = lean_st_ref_get(v___y_1138_);
v_mctx_1143_ = lean_ctor_get(v___x_1142_, 0);
lean_inc_ref(v_mctx_1143_);
lean_dec(v___x_1142_);
v___x_1144_ = l_Lean_instantiateMVarsCore(v_mctx_1143_, v_e_1137_);
v_fst_1145_ = lean_ctor_get(v___x_1144_, 0);
lean_inc(v_fst_1145_);
v_snd_1146_ = lean_ctor_get(v___x_1144_, 1);
lean_inc(v_snd_1146_);
lean_dec_ref(v___x_1144_);
v___x_1147_ = lean_st_ref_take(v___y_1138_);
v_cache_1148_ = lean_ctor_get(v___x_1147_, 1);
v_zetaDeltaFVarIds_1149_ = lean_ctor_get(v___x_1147_, 2);
v_postponed_1150_ = lean_ctor_get(v___x_1147_, 3);
v_diag_1151_ = lean_ctor_get(v___x_1147_, 4);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1160_ == 0)
{
lean_object* v_unused_1161_; 
v_unused_1161_ = lean_ctor_get(v___x_1147_, 0);
lean_dec(v_unused_1161_);
v___x_1153_ = v___x_1147_;
v_isShared_1154_ = v_isSharedCheck_1160_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_diag_1151_);
lean_inc(v_postponed_1150_);
lean_inc(v_zetaDeltaFVarIds_1149_);
lean_inc(v_cache_1148_);
lean_dec(v___x_1147_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1160_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1156_; 
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 0, v_snd_1146_);
v___x_1156_ = v___x_1153_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_snd_1146_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v_cache_1148_);
lean_ctor_set(v_reuseFailAlloc_1159_, 2, v_zetaDeltaFVarIds_1149_);
lean_ctor_set(v_reuseFailAlloc_1159_, 3, v_postponed_1150_);
lean_ctor_set(v_reuseFailAlloc_1159_, 4, v_diag_1151_);
v___x_1156_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1157_ = lean_st_ref_set(v___y_1138_, v___x_1156_);
v___x_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1158_, 0, v_fst_1145_);
return v___x_1158_;
}
}
}
else
{
lean_object* v___x_1162_; 
v___x_1162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1162_, 0, v_e_1137_);
return v___x_1162_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___redArg___boxed(lean_object* v_e_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___redArg(v_e_1163_, v___y_1164_);
lean_dec(v___y_1164_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1(lean_object* v_e_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v___x_1173_; 
v___x_1173_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___redArg(v_e_1167_, v___y_1169_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___boxed(lean_object* v_e_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1(v_e_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___redArg(lean_object* v_mvarId_1181_, lean_object* v_x_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_){
_start:
{
lean_object* v___x_1188_; 
v___x_1188_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1181_, v_x_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
if (lean_obj_tag(v___x_1188_) == 0)
{
lean_object* v_a_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1196_; 
v_a_1189_ = lean_ctor_get(v___x_1188_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1191_ = v___x_1188_;
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_a_1189_);
lean_dec(v___x_1188_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1194_; 
if (v_isShared_1192_ == 0)
{
v___x_1194_ = v___x_1191_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_a_1189_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
else
{
lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1204_; 
v_a_1197_ = lean_ctor_get(v___x_1188_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1199_ = v___x_1188_;
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_dec(v___x_1188_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1202_; 
if (v_isShared_1200_ == 0)
{
v___x_1202_ = v___x_1199_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_a_1197_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___redArg___boxed(lean_object* v_mvarId_1205_, lean_object* v_x_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___redArg(v_mvarId_1205_, v_x_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4(lean_object* v_00_u03b1_1213_, lean_object* v_mvarId_1214_, lean_object* v_x_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v___x_1221_; 
v___x_1221_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___redArg(v_mvarId_1214_, v_x_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___boxed(lean_object* v_00_u03b1_1222_, lean_object* v_mvarId_1223_, lean_object* v_x_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4(v_00_u03b1_1222_, v_mvarId_1223_, v_x_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__3(lean_object* v_a_1231_, lean_object* v_as_1232_, size_t v_i_1233_, size_t v_stop_1234_, lean_object* v_b_1235_){
_start:
{
lean_object* v___y_1237_; uint8_t v___x_1241_; 
v___x_1241_ = lean_usize_dec_eq(v_i_1233_, v_stop_1234_);
if (v___x_1241_ == 0)
{
lean_object* v___x_1242_; lean_object* v_fvar_1243_; lean_object* v___x_1244_; uint8_t v___x_1245_; 
v___x_1242_ = lean_array_uget_borrowed(v_as_1232_, v_i_1233_);
v_fvar_1243_ = lean_ctor_get(v___x_1242_, 1);
v___x_1244_ = l_Lean_Expr_fvarId_x21(v_fvar_1243_);
v___x_1245_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_1244_, v_a_1231_);
lean_dec(v___x_1244_);
if (v___x_1245_ == 0)
{
v___y_1237_ = v_b_1235_;
goto v___jp_1236_;
}
else
{
lean_object* v___x_1246_; 
lean_inc(v___x_1242_);
v___x_1246_ = lean_array_push(v_b_1235_, v___x_1242_);
v___y_1237_ = v___x_1246_;
goto v___jp_1236_;
}
}
else
{
return v_b_1235_;
}
v___jp_1236_:
{
size_t v___x_1238_; size_t v___x_1239_; 
v___x_1238_ = ((size_t)1ULL);
v___x_1239_ = lean_usize_add(v_i_1233_, v___x_1238_);
v_i_1233_ = v___x_1239_;
v_b_1235_ = v___y_1237_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__3___boxed(lean_object* v_a_1247_, lean_object* v_as_1248_, lean_object* v_i_1249_, lean_object* v_stop_1250_, lean_object* v_b_1251_){
_start:
{
size_t v_i_boxed_1252_; size_t v_stop_boxed_1253_; lean_object* v_res_1254_; 
v_i_boxed_1252_ = lean_unbox_usize(v_i_1249_);
lean_dec(v_i_1249_);
v_stop_boxed_1253_ = lean_unbox_usize(v_stop_1250_);
lean_dec(v_stop_1250_);
v_res_1254_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__3(v_a_1247_, v_as_1248_, v_i_boxed_1252_, v_stop_boxed_1253_, v_b_1251_);
lean_dec_ref(v_as_1248_);
lean_dec(v_a_1247_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12_spec__13___redArg(lean_object* v_x_1255_, lean_object* v_x_1256_, lean_object* v_x_1257_, lean_object* v_x_1258_){
_start:
{
lean_object* v_ks_1259_; lean_object* v_vs_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1284_; 
v_ks_1259_ = lean_ctor_get(v_x_1255_, 0);
v_vs_1260_ = lean_ctor_get(v_x_1255_, 1);
v_isSharedCheck_1284_ = !lean_is_exclusive(v_x_1255_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1262_ = v_x_1255_;
v_isShared_1263_ = v_isSharedCheck_1284_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_vs_1260_);
lean_inc(v_ks_1259_);
lean_dec(v_x_1255_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1284_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1264_; uint8_t v___x_1265_; 
v___x_1264_ = lean_array_get_size(v_ks_1259_);
v___x_1265_ = lean_nat_dec_lt(v_x_1256_, v___x_1264_);
if (v___x_1265_ == 0)
{
lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1269_; 
lean_dec(v_x_1256_);
v___x_1266_ = lean_array_push(v_ks_1259_, v_x_1257_);
v___x_1267_ = lean_array_push(v_vs_1260_, v_x_1258_);
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 1, v___x_1267_);
lean_ctor_set(v___x_1262_, 0, v___x_1266_);
v___x_1269_ = v___x_1262_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1266_);
lean_ctor_set(v_reuseFailAlloc_1270_, 1, v___x_1267_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
else
{
lean_object* v_k_x27_1271_; uint8_t v___x_1272_; 
v_k_x27_1271_ = lean_array_fget_borrowed(v_ks_1259_, v_x_1256_);
v___x_1272_ = l_Lean_instBEqMVarId_beq(v_x_1257_, v_k_x27_1271_);
if (v___x_1272_ == 0)
{
lean_object* v___x_1274_; 
if (v_isShared_1263_ == 0)
{
v___x_1274_ = v___x_1262_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_ks_1259_);
lean_ctor_set(v_reuseFailAlloc_1278_, 1, v_vs_1260_);
v___x_1274_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1275_ = lean_unsigned_to_nat(1u);
v___x_1276_ = lean_nat_add(v_x_1256_, v___x_1275_);
lean_dec(v_x_1256_);
v_x_1255_ = v___x_1274_;
v_x_1256_ = v___x_1276_;
goto _start;
}
}
else
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1282_; 
v___x_1279_ = lean_array_fset(v_ks_1259_, v_x_1256_, v_x_1257_);
v___x_1280_ = lean_array_fset(v_vs_1260_, v_x_1256_, v_x_1258_);
lean_dec(v_x_1256_);
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 1, v___x_1280_);
lean_ctor_set(v___x_1262_, 0, v___x_1279_);
v___x_1282_ = v___x_1262_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1279_);
lean_ctor_set(v_reuseFailAlloc_1283_, 1, v___x_1280_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12___redArg(lean_object* v_n_1285_, lean_object* v_k_1286_, lean_object* v_v_1287_){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1288_ = lean_unsigned_to_nat(0u);
v___x_1289_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12_spec__13___redArg(v_n_1285_, v___x_1288_, v_k_1286_, v_v_1287_);
return v___x_1289_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1290_; 
v___x_1290_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg(lean_object* v_x_1291_, size_t v_x_1292_, size_t v_x_1293_, lean_object* v_x_1294_, lean_object* v_x_1295_){
_start:
{
if (lean_obj_tag(v_x_1291_) == 0)
{
lean_object* v_es_1296_; size_t v___x_1297_; size_t v___x_1298_; lean_object* v_j_1299_; lean_object* v___x_1300_; uint8_t v___x_1301_; 
v_es_1296_ = lean_ctor_get(v_x_1291_, 0);
v___x_1297_ = ((size_t)31ULL);
v___x_1298_ = lean_usize_land(v_x_1292_, v___x_1297_);
v_j_1299_ = lean_usize_to_nat(v___x_1298_);
v___x_1300_ = lean_array_get_size(v_es_1296_);
v___x_1301_ = lean_nat_dec_lt(v_j_1299_, v___x_1300_);
if (v___x_1301_ == 0)
{
lean_dec(v_j_1299_);
lean_dec(v_x_1295_);
lean_dec(v_x_1294_);
return v_x_1291_;
}
else
{
lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1340_; 
lean_inc_ref(v_es_1296_);
v_isSharedCheck_1340_ = !lean_is_exclusive(v_x_1291_);
if (v_isSharedCheck_1340_ == 0)
{
lean_object* v_unused_1341_; 
v_unused_1341_ = lean_ctor_get(v_x_1291_, 0);
lean_dec(v_unused_1341_);
v___x_1303_ = v_x_1291_;
v_isShared_1304_ = v_isSharedCheck_1340_;
goto v_resetjp_1302_;
}
else
{
lean_dec(v_x_1291_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1340_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v_v_1305_; lean_object* v___x_1306_; lean_object* v_xs_x27_1307_; lean_object* v___y_1309_; 
v_v_1305_ = lean_array_fget(v_es_1296_, v_j_1299_);
v___x_1306_ = lean_box(0);
v_xs_x27_1307_ = lean_array_fset(v_es_1296_, v_j_1299_, v___x_1306_);
switch(lean_obj_tag(v_v_1305_))
{
case 0:
{
lean_object* v_key_1314_; lean_object* v_val_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1325_; 
v_key_1314_ = lean_ctor_get(v_v_1305_, 0);
v_val_1315_ = lean_ctor_get(v_v_1305_, 1);
v_isSharedCheck_1325_ = !lean_is_exclusive(v_v_1305_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1317_ = v_v_1305_;
v_isShared_1318_ = v_isSharedCheck_1325_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_val_1315_);
lean_inc(v_key_1314_);
lean_dec(v_v_1305_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1325_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
uint8_t v___x_1319_; 
v___x_1319_ = l_Lean_instBEqMVarId_beq(v_x_1294_, v_key_1314_);
if (v___x_1319_ == 0)
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
lean_del_object(v___x_1317_);
v___x_1320_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1314_, v_val_1315_, v_x_1294_, v_x_1295_);
v___x_1321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1320_);
v___y_1309_ = v___x_1321_;
goto v___jp_1308_;
}
else
{
lean_object* v___x_1323_; 
lean_dec(v_val_1315_);
lean_dec(v_key_1314_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 1, v_x_1295_);
lean_ctor_set(v___x_1317_, 0, v_x_1294_);
v___x_1323_ = v___x_1317_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_x_1294_);
lean_ctor_set(v_reuseFailAlloc_1324_, 1, v_x_1295_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
v___y_1309_ = v___x_1323_;
goto v___jp_1308_;
}
}
}
}
case 1:
{
lean_object* v_node_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1338_; 
v_node_1326_ = lean_ctor_get(v_v_1305_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v_v_1305_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1328_ = v_v_1305_;
v_isShared_1329_ = v_isSharedCheck_1338_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_node_1326_);
lean_dec(v_v_1305_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1338_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
size_t v___x_1330_; size_t v___x_1331_; size_t v___x_1332_; size_t v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1336_; 
v___x_1330_ = ((size_t)5ULL);
v___x_1331_ = lean_usize_shift_right(v_x_1292_, v___x_1330_);
v___x_1332_ = ((size_t)1ULL);
v___x_1333_ = lean_usize_add(v_x_1293_, v___x_1332_);
v___x_1334_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg(v_node_1326_, v___x_1331_, v___x_1333_, v_x_1294_, v_x_1295_);
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 0, v___x_1334_);
v___x_1336_ = v___x_1328_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v___x_1334_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
v___y_1309_ = v___x_1336_;
goto v___jp_1308_;
}
}
}
default: 
{
lean_object* v___x_1339_; 
v___x_1339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1339_, 0, v_x_1294_);
lean_ctor_set(v___x_1339_, 1, v_x_1295_);
v___y_1309_ = v___x_1339_;
goto v___jp_1308_;
}
}
v___jp_1308_:
{
lean_object* v___x_1310_; lean_object* v___x_1312_; 
v___x_1310_ = lean_array_fset(v_xs_x27_1307_, v_j_1299_, v___y_1309_);
lean_dec(v_j_1299_);
if (v_isShared_1304_ == 0)
{
lean_ctor_set(v___x_1303_, 0, v___x_1310_);
v___x_1312_ = v___x_1303_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v___x_1310_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
}
}
else
{
lean_object* v_ks_1342_; lean_object* v_vs_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1363_; 
v_ks_1342_ = lean_ctor_get(v_x_1291_, 0);
v_vs_1343_ = lean_ctor_get(v_x_1291_, 1);
v_isSharedCheck_1363_ = !lean_is_exclusive(v_x_1291_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1345_ = v_x_1291_;
v_isShared_1346_ = v_isSharedCheck_1363_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_vs_1343_);
lean_inc(v_ks_1342_);
lean_dec(v_x_1291_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1363_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1348_; 
if (v_isShared_1346_ == 0)
{
v___x_1348_ = v___x_1345_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_ks_1342_);
lean_ctor_set(v_reuseFailAlloc_1362_, 1, v_vs_1343_);
v___x_1348_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
lean_object* v_newNode_1349_; uint8_t v___y_1351_; size_t v___x_1357_; uint8_t v___x_1358_; 
v_newNode_1349_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12___redArg(v___x_1348_, v_x_1294_, v_x_1295_);
v___x_1357_ = ((size_t)7ULL);
v___x_1358_ = lean_usize_dec_le(v___x_1357_, v_x_1293_);
if (v___x_1358_ == 0)
{
lean_object* v___x_1359_; lean_object* v___x_1360_; uint8_t v___x_1361_; 
v___x_1359_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1349_);
v___x_1360_ = lean_unsigned_to_nat(4u);
v___x_1361_ = lean_nat_dec_lt(v___x_1359_, v___x_1360_);
lean_dec(v___x_1359_);
v___y_1351_ = v___x_1361_;
goto v___jp_1350_;
}
else
{
v___y_1351_ = v___x_1358_;
goto v___jp_1350_;
}
v___jp_1350_:
{
if (v___y_1351_ == 0)
{
lean_object* v_ks_1352_; lean_object* v_vs_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v_ks_1352_ = lean_ctor_get(v_newNode_1349_, 0);
lean_inc_ref(v_ks_1352_);
v_vs_1353_ = lean_ctor_get(v_newNode_1349_, 1);
lean_inc_ref(v_vs_1353_);
lean_dec_ref(v_newNode_1349_);
v___x_1354_ = lean_unsigned_to_nat(0u);
v___x_1355_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__0);
v___x_1356_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___redArg(v_x_1293_, v_ks_1352_, v_vs_1353_, v___x_1354_, v___x_1355_);
lean_dec_ref(v_vs_1353_);
lean_dec_ref(v_ks_1352_);
return v___x_1356_;
}
else
{
return v_newNode_1349_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___redArg(size_t v_depth_1364_, lean_object* v_keys_1365_, lean_object* v_vals_1366_, lean_object* v_i_1367_, lean_object* v_entries_1368_){
_start:
{
lean_object* v___x_1369_; uint8_t v___x_1370_; 
v___x_1369_ = lean_array_get_size(v_keys_1365_);
v___x_1370_ = lean_nat_dec_lt(v_i_1367_, v___x_1369_);
if (v___x_1370_ == 0)
{
lean_dec(v_i_1367_);
return v_entries_1368_;
}
else
{
lean_object* v_k_1371_; lean_object* v_v_1372_; uint64_t v___x_1373_; size_t v_h_1374_; size_t v___x_1375_; lean_object* v___x_1376_; size_t v___x_1377_; size_t v___x_1378_; size_t v___x_1379_; size_t v_h_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v_k_1371_ = lean_array_fget_borrowed(v_keys_1365_, v_i_1367_);
v_v_1372_ = lean_array_fget_borrowed(v_vals_1366_, v_i_1367_);
v___x_1373_ = l_Lean_instHashableMVarId_hash(v_k_1371_);
v_h_1374_ = lean_uint64_to_usize(v___x_1373_);
v___x_1375_ = ((size_t)5ULL);
v___x_1376_ = lean_unsigned_to_nat(1u);
v___x_1377_ = ((size_t)1ULL);
v___x_1378_ = lean_usize_sub(v_depth_1364_, v___x_1377_);
v___x_1379_ = lean_usize_mul(v___x_1375_, v___x_1378_);
v_h_1380_ = lean_usize_shift_right(v_h_1374_, v___x_1379_);
v___x_1381_ = lean_nat_add(v_i_1367_, v___x_1376_);
lean_dec(v_i_1367_);
lean_inc(v_v_1372_);
lean_inc(v_k_1371_);
v___x_1382_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg(v_entries_1368_, v_h_1380_, v_depth_1364_, v_k_1371_, v_v_1372_);
v_i_1367_ = v___x_1381_;
v_entries_1368_ = v___x_1382_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___redArg___boxed(lean_object* v_depth_1384_, lean_object* v_keys_1385_, lean_object* v_vals_1386_, lean_object* v_i_1387_, lean_object* v_entries_1388_){
_start:
{
size_t v_depth_boxed_1389_; lean_object* v_res_1390_; 
v_depth_boxed_1389_ = lean_unbox_usize(v_depth_1384_);
lean_dec(v_depth_1384_);
v_res_1390_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___redArg(v_depth_boxed_1389_, v_keys_1385_, v_vals_1386_, v_i_1387_, v_entries_1388_);
lean_dec_ref(v_vals_1386_);
lean_dec_ref(v_keys_1385_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___boxed(lean_object* v_x_1391_, lean_object* v_x_1392_, lean_object* v_x_1393_, lean_object* v_x_1394_, lean_object* v_x_1395_){
_start:
{
size_t v_x_7478__boxed_1396_; size_t v_x_7479__boxed_1397_; lean_object* v_res_1398_; 
v_x_7478__boxed_1396_ = lean_unbox_usize(v_x_1392_);
lean_dec(v_x_1392_);
v_x_7479__boxed_1397_ = lean_unbox_usize(v_x_1393_);
lean_dec(v_x_1393_);
v_res_1398_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg(v_x_1391_, v_x_7478__boxed_1396_, v_x_7479__boxed_1397_, v_x_1394_, v_x_1395_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4___redArg(lean_object* v_x_1399_, lean_object* v_x_1400_, lean_object* v_x_1401_){
_start:
{
uint64_t v___x_1402_; size_t v___x_1403_; size_t v___x_1404_; lean_object* v___x_1405_; 
v___x_1402_ = l_Lean_instHashableMVarId_hash(v_x_1400_);
v___x_1403_ = lean_uint64_to_usize(v___x_1402_);
v___x_1404_ = ((size_t)1ULL);
v___x_1405_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg(v_x_1399_, v___x_1403_, v___x_1404_, v_x_1400_, v_x_1401_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___redArg(lean_object* v_mvarId_1406_, lean_object* v_val_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v___x_1410_; lean_object* v_mctx_1411_; lean_object* v_cache_1412_; lean_object* v_zetaDeltaFVarIds_1413_; lean_object* v_postponed_1414_; lean_object* v_diag_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1443_; 
v___x_1410_ = lean_st_ref_take(v___y_1408_);
v_mctx_1411_ = lean_ctor_get(v___x_1410_, 0);
v_cache_1412_ = lean_ctor_get(v___x_1410_, 1);
v_zetaDeltaFVarIds_1413_ = lean_ctor_get(v___x_1410_, 2);
v_postponed_1414_ = lean_ctor_get(v___x_1410_, 3);
v_diag_1415_ = lean_ctor_get(v___x_1410_, 4);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1417_ = v___x_1410_;
v_isShared_1418_ = v_isSharedCheck_1443_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_diag_1415_);
lean_inc(v_postponed_1414_);
lean_inc(v_zetaDeltaFVarIds_1413_);
lean_inc(v_cache_1412_);
lean_inc(v_mctx_1411_);
lean_dec(v___x_1410_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1443_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v_depth_1419_; lean_object* v_levelAssignDepth_1420_; lean_object* v_lmvarCounter_1421_; lean_object* v_mvarCounter_1422_; lean_object* v_lDecls_1423_; lean_object* v_decls_1424_; lean_object* v_userNames_1425_; lean_object* v_lAssignment_1426_; lean_object* v_eAssignment_1427_; lean_object* v_dAssignment_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1442_; 
v_depth_1419_ = lean_ctor_get(v_mctx_1411_, 0);
v_levelAssignDepth_1420_ = lean_ctor_get(v_mctx_1411_, 1);
v_lmvarCounter_1421_ = lean_ctor_get(v_mctx_1411_, 2);
v_mvarCounter_1422_ = lean_ctor_get(v_mctx_1411_, 3);
v_lDecls_1423_ = lean_ctor_get(v_mctx_1411_, 4);
v_decls_1424_ = lean_ctor_get(v_mctx_1411_, 5);
v_userNames_1425_ = lean_ctor_get(v_mctx_1411_, 6);
v_lAssignment_1426_ = lean_ctor_get(v_mctx_1411_, 7);
v_eAssignment_1427_ = lean_ctor_get(v_mctx_1411_, 8);
v_dAssignment_1428_ = lean_ctor_get(v_mctx_1411_, 9);
v_isSharedCheck_1442_ = !lean_is_exclusive(v_mctx_1411_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1430_ = v_mctx_1411_;
v_isShared_1431_ = v_isSharedCheck_1442_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_dAssignment_1428_);
lean_inc(v_eAssignment_1427_);
lean_inc(v_lAssignment_1426_);
lean_inc(v_userNames_1425_);
lean_inc(v_decls_1424_);
lean_inc(v_lDecls_1423_);
lean_inc(v_mvarCounter_1422_);
lean_inc(v_lmvarCounter_1421_);
lean_inc(v_levelAssignDepth_1420_);
lean_inc(v_depth_1419_);
lean_dec(v_mctx_1411_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1442_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1432_; lean_object* v___x_1434_; 
v___x_1432_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4___redArg(v_eAssignment_1427_, v_mvarId_1406_, v_val_1407_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 8, v___x_1432_);
v___x_1434_ = v___x_1430_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_depth_1419_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v_levelAssignDepth_1420_);
lean_ctor_set(v_reuseFailAlloc_1441_, 2, v_lmvarCounter_1421_);
lean_ctor_set(v_reuseFailAlloc_1441_, 3, v_mvarCounter_1422_);
lean_ctor_set(v_reuseFailAlloc_1441_, 4, v_lDecls_1423_);
lean_ctor_set(v_reuseFailAlloc_1441_, 5, v_decls_1424_);
lean_ctor_set(v_reuseFailAlloc_1441_, 6, v_userNames_1425_);
lean_ctor_set(v_reuseFailAlloc_1441_, 7, v_lAssignment_1426_);
lean_ctor_set(v_reuseFailAlloc_1441_, 8, v___x_1432_);
lean_ctor_set(v_reuseFailAlloc_1441_, 9, v_dAssignment_1428_);
v___x_1434_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
lean_object* v___x_1436_; 
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 0, v___x_1434_);
v___x_1436_ = v___x_1417_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v___x_1434_);
lean_ctor_set(v_reuseFailAlloc_1440_, 1, v_cache_1412_);
lean_ctor_set(v_reuseFailAlloc_1440_, 2, v_zetaDeltaFVarIds_1413_);
lean_ctor_set(v_reuseFailAlloc_1440_, 3, v_postponed_1414_);
lean_ctor_set(v_reuseFailAlloc_1440_, 4, v_diag_1415_);
v___x_1436_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1437_ = lean_st_ref_set(v___y_1408_, v___x_1436_);
v___x_1438_ = lean_box(0);
v___x_1439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1438_);
return v___x_1439_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___redArg___boxed(lean_object* v_mvarId_1444_, lean_object* v_val_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___redArg(v_mvarId_1444_, v_val_1445_, v___y_1446_);
lean_dec(v___y_1446_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___redArg(lean_object* v_a_1449_, lean_object* v_as_1450_, size_t v_sz_1451_, size_t v_i_1452_, lean_object* v_b_1453_){
_start:
{
uint8_t v___x_1455_; 
v___x_1455_ = lean_usize_dec_lt(v_i_1452_, v_sz_1451_);
if (v___x_1455_ == 0)
{
lean_object* v___x_1456_; 
v___x_1456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1456_, 0, v_b_1453_);
return v___x_1456_;
}
else
{
lean_object* v_snd_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1475_; 
v_snd_1457_ = lean_ctor_get(v_b_1453_, 1);
v_isSharedCheck_1475_ = !lean_is_exclusive(v_b_1453_);
if (v_isSharedCheck_1475_ == 0)
{
lean_object* v_unused_1476_; 
v_unused_1476_ = lean_ctor_get(v_b_1453_, 0);
lean_dec(v_unused_1476_);
v___x_1459_ = v_b_1453_;
v_isShared_1460_ = v_isSharedCheck_1475_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_snd_1457_);
lean_dec(v_b_1453_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1475_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1461_; lean_object* v_a_1463_; lean_object* v_a_1470_; 
v___x_1461_ = lean_box(0);
v_a_1470_ = lean_array_uget_borrowed(v_as_1450_, v_i_1452_);
if (lean_obj_tag(v_a_1470_) == 0)
{
v_a_1463_ = v_snd_1457_;
goto v___jp_1462_;
}
else
{
lean_object* v_val_1471_; lean_object* v___x_1472_; uint8_t v___x_1473_; 
v_val_1471_ = lean_ctor_get(v_a_1470_, 0);
v___x_1472_ = l_Lean_LocalDecl_fvarId(v_val_1471_);
v___x_1473_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_1472_, v_a_1449_);
if (v___x_1473_ == 0)
{
lean_object* v___x_1474_; 
v___x_1474_ = lean_local_ctx_erase(v_snd_1457_, v___x_1472_);
v_a_1463_ = v___x_1474_;
goto v___jp_1462_;
}
else
{
lean_dec(v___x_1472_);
v_a_1463_ = v_snd_1457_;
goto v___jp_1462_;
}
}
v___jp_1462_:
{
lean_object* v___x_1465_; 
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 1, v_a_1463_);
lean_ctor_set(v___x_1459_, 0, v___x_1461_);
v___x_1465_ = v___x_1459_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v___x_1461_);
lean_ctor_set(v_reuseFailAlloc_1469_, 1, v_a_1463_);
v___x_1465_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
size_t v___x_1466_; size_t v___x_1467_; 
v___x_1466_ = ((size_t)1ULL);
v___x_1467_ = lean_usize_add(v_i_1452_, v___x_1466_);
v_i_1452_ = v___x_1467_;
v_b_1453_ = v___x_1465_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___redArg___boxed(lean_object* v_a_1477_, lean_object* v_as_1478_, lean_object* v_sz_1479_, lean_object* v_i_1480_, lean_object* v_b_1481_, lean_object* v___y_1482_){
_start:
{
size_t v_sz_boxed_1483_; size_t v_i_boxed_1484_; lean_object* v_res_1485_; 
v_sz_boxed_1483_ = lean_unbox_usize(v_sz_1479_);
lean_dec(v_sz_1479_);
v_i_boxed_1484_ = lean_unbox_usize(v_i_1480_);
lean_dec(v_i_1480_);
v_res_1485_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___redArg(v_a_1477_, v_as_1478_, v_sz_boxed_1483_, v_i_boxed_1484_, v_b_1481_);
lean_dec_ref(v_as_1478_);
lean_dec(v_a_1477_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4(lean_object* v_a_1486_, lean_object* v_as_1487_, size_t v_sz_1488_, size_t v_i_1489_, lean_object* v_b_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_){
_start:
{
uint8_t v___x_1496_; 
v___x_1496_ = lean_usize_dec_lt(v_i_1489_, v_sz_1488_);
if (v___x_1496_ == 0)
{
lean_object* v___x_1497_; 
v___x_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1497_, 0, v_b_1490_);
return v___x_1497_;
}
else
{
lean_object* v_snd_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1516_; 
v_snd_1498_ = lean_ctor_get(v_b_1490_, 1);
v_isSharedCheck_1516_ = !lean_is_exclusive(v_b_1490_);
if (v_isSharedCheck_1516_ == 0)
{
lean_object* v_unused_1517_; 
v_unused_1517_ = lean_ctor_get(v_b_1490_, 0);
lean_dec(v_unused_1517_);
v___x_1500_ = v_b_1490_;
v_isShared_1501_ = v_isSharedCheck_1516_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_snd_1498_);
lean_dec(v_b_1490_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1516_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1502_; lean_object* v_a_1504_; lean_object* v_a_1511_; 
v___x_1502_ = lean_box(0);
v_a_1511_ = lean_array_uget_borrowed(v_as_1487_, v_i_1489_);
if (lean_obj_tag(v_a_1511_) == 0)
{
v_a_1504_ = v_snd_1498_;
goto v___jp_1503_;
}
else
{
lean_object* v_val_1512_; lean_object* v___x_1513_; uint8_t v___x_1514_; 
v_val_1512_ = lean_ctor_get(v_a_1511_, 0);
v___x_1513_ = l_Lean_LocalDecl_fvarId(v_val_1512_);
v___x_1514_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_1513_, v_a_1486_);
if (v___x_1514_ == 0)
{
lean_object* v___x_1515_; 
v___x_1515_ = lean_local_ctx_erase(v_snd_1498_, v___x_1513_);
v_a_1504_ = v___x_1515_;
goto v___jp_1503_;
}
else
{
lean_dec(v___x_1513_);
v_a_1504_ = v_snd_1498_;
goto v___jp_1503_;
}
}
v___jp_1503_:
{
lean_object* v___x_1506_; 
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 1, v_a_1504_);
lean_ctor_set(v___x_1500_, 0, v___x_1502_);
v___x_1506_ = v___x_1500_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1502_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v_a_1504_);
v___x_1506_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
size_t v___x_1507_; size_t v___x_1508_; lean_object* v___x_1509_; 
v___x_1507_ = ((size_t)1ULL);
v___x_1508_ = lean_usize_add(v_i_1489_, v___x_1507_);
v___x_1509_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___redArg(v_a_1486_, v_as_1487_, v_sz_1488_, v___x_1508_, v___x_1506_);
return v___x_1509_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4___boxed(lean_object* v_a_1518_, lean_object* v_as_1519_, lean_object* v_sz_1520_, lean_object* v_i_1521_, lean_object* v_b_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
size_t v_sz_boxed_1528_; size_t v_i_boxed_1529_; lean_object* v_res_1530_; 
v_sz_boxed_1528_ = lean_unbox_usize(v_sz_1520_);
lean_dec(v_sz_1520_);
v_i_boxed_1529_ = lean_unbox_usize(v_i_1521_);
lean_dec(v_i_1521_);
v_res_1530_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4(v_a_1518_, v_as_1519_, v_sz_boxed_1528_, v_i_boxed_1529_, v_b_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
lean_dec_ref(v_as_1519_);
lean_dec(v_a_1518_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0(lean_object* v_init_1531_, lean_object* v_a_1532_, lean_object* v_n_1533_, lean_object* v_b_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
if (lean_obj_tag(v_n_1533_) == 0)
{
lean_object* v_cs_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; size_t v_sz_1543_; size_t v___x_1544_; lean_object* v___x_1545_; 
v_cs_1540_ = lean_ctor_get(v_n_1533_, 0);
v___x_1541_ = lean_box(0);
v___x_1542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1541_);
lean_ctor_set(v___x_1542_, 1, v_b_1534_);
v_sz_1543_ = lean_array_size(v_cs_1540_);
v___x_1544_ = ((size_t)0ULL);
v___x_1545_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__3(v_init_1531_, v_a_1532_, v_cs_1540_, v_sz_1543_, v___x_1544_, v___x_1542_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1560_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1548_ = v___x_1545_;
v_isShared_1549_ = v_isSharedCheck_1560_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1545_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1560_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v_fst_1550_; 
v_fst_1550_ = lean_ctor_get(v_a_1546_, 0);
if (lean_obj_tag(v_fst_1550_) == 0)
{
lean_object* v_snd_1551_; lean_object* v___x_1552_; lean_object* v___x_1554_; 
v_snd_1551_ = lean_ctor_get(v_a_1546_, 1);
lean_inc(v_snd_1551_);
lean_dec(v_a_1546_);
v___x_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1552_, 0, v_snd_1551_);
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 0, v___x_1552_);
v___x_1554_ = v___x_1548_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1552_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
else
{
lean_object* v_val_1556_; lean_object* v___x_1558_; 
lean_inc_ref(v_fst_1550_);
lean_dec(v_a_1546_);
v_val_1556_ = lean_ctor_get(v_fst_1550_, 0);
lean_inc(v_val_1556_);
lean_dec_ref_known(v_fst_1550_, 1);
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 0, v_val_1556_);
v___x_1558_ = v___x_1548_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_val_1556_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
}
else
{
lean_object* v_a_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1568_; 
v_a_1561_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1563_ = v___x_1545_;
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_dec(v___x_1545_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1566_; 
if (v_isShared_1564_ == 0)
{
v___x_1566_ = v___x_1563_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_a_1561_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
}
else
{
lean_object* v_vs_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; size_t v_sz_1572_; size_t v___x_1573_; lean_object* v___x_1574_; 
v_vs_1569_ = lean_ctor_get(v_n_1533_, 0);
v___x_1570_ = lean_box(0);
v___x_1571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1570_);
lean_ctor_set(v___x_1571_, 1, v_b_1534_);
v_sz_1572_ = lean_array_size(v_vs_1569_);
v___x_1573_ = ((size_t)0ULL);
v___x_1574_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4(v_a_1532_, v_vs_1569_, v_sz_1572_, v___x_1573_, v___x_1571_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1589_; 
v_a_1575_ = lean_ctor_get(v___x_1574_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1577_ = v___x_1574_;
v_isShared_1578_ = v_isSharedCheck_1589_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_dec(v___x_1574_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1589_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v_fst_1579_; 
v_fst_1579_ = lean_ctor_get(v_a_1575_, 0);
if (lean_obj_tag(v_fst_1579_) == 0)
{
lean_object* v_snd_1580_; lean_object* v___x_1581_; lean_object* v___x_1583_; 
v_snd_1580_ = lean_ctor_get(v_a_1575_, 1);
lean_inc(v_snd_1580_);
lean_dec(v_a_1575_);
v___x_1581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1581_, 0, v_snd_1580_);
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 0, v___x_1581_);
v___x_1583_ = v___x_1577_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1581_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
else
{
lean_object* v_val_1585_; lean_object* v___x_1587_; 
lean_inc_ref(v_fst_1579_);
lean_dec(v_a_1575_);
v_val_1585_ = lean_ctor_get(v_fst_1579_, 0);
lean_inc(v_val_1585_);
lean_dec_ref_known(v_fst_1579_, 1);
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 0, v_val_1585_);
v___x_1587_ = v___x_1577_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_val_1585_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
else
{
lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1597_; 
v_a_1590_ = lean_ctor_get(v___x_1574_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1592_ = v___x_1574_;
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1574_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1595_; 
if (v_isShared_1593_ == 0)
{
v___x_1595_ = v___x_1592_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_a_1590_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__3(lean_object* v_init_1598_, lean_object* v_a_1599_, lean_object* v_as_1600_, size_t v_sz_1601_, size_t v_i_1602_, lean_object* v_b_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
uint8_t v___x_1609_; 
v___x_1609_ = lean_usize_dec_lt(v_i_1602_, v_sz_1601_);
if (v___x_1609_ == 0)
{
lean_object* v___x_1610_; 
v___x_1610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1610_, 0, v_b_1603_);
return v___x_1610_;
}
else
{
lean_object* v_snd_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1645_; 
v_snd_1611_ = lean_ctor_get(v_b_1603_, 1);
v_isSharedCheck_1645_ = !lean_is_exclusive(v_b_1603_);
if (v_isSharedCheck_1645_ == 0)
{
lean_object* v_unused_1646_; 
v_unused_1646_ = lean_ctor_get(v_b_1603_, 0);
lean_dec(v_unused_1646_);
v___x_1613_ = v_b_1603_;
v_isShared_1614_ = v_isSharedCheck_1645_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_snd_1611_);
lean_dec(v_b_1603_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1645_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v_a_1615_; lean_object* v___x_1616_; 
v_a_1615_ = lean_array_uget_borrowed(v_as_1600_, v_i_1602_);
lean_inc(v_snd_1611_);
v___x_1616_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0(v_init_1598_, v_a_1599_, v_a_1615_, v_snd_1611_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1636_; 
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1619_ = v___x_1616_;
v_isShared_1620_ = v_isSharedCheck_1636_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v___x_1616_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1636_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
if (lean_obj_tag(v_a_1617_) == 0)
{
lean_object* v___x_1621_; lean_object* v___x_1623_; 
v___x_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1621_, 0, v_a_1617_);
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 0, v___x_1621_);
v___x_1623_ = v___x_1613_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v___x_1621_);
lean_ctor_set(v_reuseFailAlloc_1627_, 1, v_snd_1611_);
v___x_1623_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
lean_object* v___x_1625_; 
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 0, v___x_1623_);
v___x_1625_ = v___x_1619_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v___x_1623_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
else
{
lean_object* v_a_1628_; lean_object* v___x_1629_; lean_object* v___x_1631_; 
lean_del_object(v___x_1619_);
lean_dec(v_snd_1611_);
v_a_1628_ = lean_ctor_get(v_a_1617_, 0);
lean_inc(v_a_1628_);
lean_dec_ref_known(v_a_1617_, 1);
v___x_1629_ = lean_box(0);
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 1, v_a_1628_);
lean_ctor_set(v___x_1613_, 0, v___x_1629_);
v___x_1631_ = v___x_1613_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v___x_1629_);
lean_ctor_set(v_reuseFailAlloc_1635_, 1, v_a_1628_);
v___x_1631_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
size_t v___x_1632_; size_t v___x_1633_; 
v___x_1632_ = ((size_t)1ULL);
v___x_1633_ = lean_usize_add(v_i_1602_, v___x_1632_);
v_i_1602_ = v___x_1633_;
v_b_1603_ = v___x_1631_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1644_; 
lean_del_object(v___x_1613_);
lean_dec(v_snd_1611_);
v_a_1637_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1639_ = v___x_1616_;
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1616_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1642_; 
if (v_isShared_1640_ == 0)
{
v___x_1642_ = v___x_1639_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_a_1637_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__3___boxed(lean_object* v_init_1647_, lean_object* v_a_1648_, lean_object* v_as_1649_, lean_object* v_sz_1650_, lean_object* v_i_1651_, lean_object* v_b_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_){
_start:
{
size_t v_sz_boxed_1658_; size_t v_i_boxed_1659_; lean_object* v_res_1660_; 
v_sz_boxed_1658_ = lean_unbox_usize(v_sz_1650_);
lean_dec(v_sz_1650_);
v_i_boxed_1659_ = lean_unbox_usize(v_i_1651_);
lean_dec(v_i_1651_);
v_res_1660_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__3(v_init_1647_, v_a_1648_, v_as_1649_, v_sz_boxed_1658_, v_i_boxed_1659_, v_b_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1655_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec_ref(v_as_1649_);
lean_dec(v_a_1648_);
lean_dec_ref(v_init_1647_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0___boxed(lean_object* v_init_1661_, lean_object* v_a_1662_, lean_object* v_n_1663_, lean_object* v_b_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0(v_init_1661_, v_a_1662_, v_n_1663_, v_b_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec_ref(v_n_1663_);
lean_dec(v_a_1662_);
lean_dec_ref(v_init_1661_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___redArg(lean_object* v_a_1671_, lean_object* v_as_1672_, size_t v_sz_1673_, size_t v_i_1674_, lean_object* v_b_1675_){
_start:
{
uint8_t v___x_1677_; 
v___x_1677_ = lean_usize_dec_lt(v_i_1674_, v_sz_1673_);
if (v___x_1677_ == 0)
{
lean_object* v___x_1678_; 
v___x_1678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1678_, 0, v_b_1675_);
return v___x_1678_;
}
else
{
lean_object* v_snd_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1697_; 
v_snd_1679_ = lean_ctor_get(v_b_1675_, 1);
v_isSharedCheck_1697_ = !lean_is_exclusive(v_b_1675_);
if (v_isSharedCheck_1697_ == 0)
{
lean_object* v_unused_1698_; 
v_unused_1698_ = lean_ctor_get(v_b_1675_, 0);
lean_dec(v_unused_1698_);
v___x_1681_ = v_b_1675_;
v_isShared_1682_ = v_isSharedCheck_1697_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_snd_1679_);
lean_dec(v_b_1675_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1697_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1683_; lean_object* v_a_1685_; lean_object* v_a_1692_; 
v___x_1683_ = lean_box(0);
v_a_1692_ = lean_array_uget_borrowed(v_as_1672_, v_i_1674_);
if (lean_obj_tag(v_a_1692_) == 0)
{
v_a_1685_ = v_snd_1679_;
goto v___jp_1684_;
}
else
{
lean_object* v_val_1693_; lean_object* v___x_1694_; uint8_t v___x_1695_; 
v_val_1693_ = lean_ctor_get(v_a_1692_, 0);
v___x_1694_ = l_Lean_LocalDecl_fvarId(v_val_1693_);
v___x_1695_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_1694_, v_a_1671_);
if (v___x_1695_ == 0)
{
lean_object* v___x_1696_; 
v___x_1696_ = lean_local_ctx_erase(v_snd_1679_, v___x_1694_);
v_a_1685_ = v___x_1696_;
goto v___jp_1684_;
}
else
{
lean_dec(v___x_1694_);
v_a_1685_ = v_snd_1679_;
goto v___jp_1684_;
}
}
v___jp_1684_:
{
lean_object* v___x_1687_; 
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 1, v_a_1685_);
lean_ctor_set(v___x_1681_, 0, v___x_1683_);
v___x_1687_ = v___x_1681_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v___x_1683_);
lean_ctor_set(v_reuseFailAlloc_1691_, 1, v_a_1685_);
v___x_1687_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
size_t v___x_1688_; size_t v___x_1689_; 
v___x_1688_ = ((size_t)1ULL);
v___x_1689_ = lean_usize_add(v_i_1674_, v___x_1688_);
v_i_1674_ = v___x_1689_;
v_b_1675_ = v___x_1687_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___redArg___boxed(lean_object* v_a_1699_, lean_object* v_as_1700_, lean_object* v_sz_1701_, lean_object* v_i_1702_, lean_object* v_b_1703_, lean_object* v___y_1704_){
_start:
{
size_t v_sz_boxed_1705_; size_t v_i_boxed_1706_; lean_object* v_res_1707_; 
v_sz_boxed_1705_ = lean_unbox_usize(v_sz_1701_);
lean_dec(v_sz_1701_);
v_i_boxed_1706_ = lean_unbox_usize(v_i_1702_);
lean_dec(v_i_1702_);
v_res_1707_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___redArg(v_a_1699_, v_as_1700_, v_sz_boxed_1705_, v_i_boxed_1706_, v_b_1703_);
lean_dec_ref(v_as_1700_);
lean_dec(v_a_1699_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1(lean_object* v_a_1708_, lean_object* v_as_1709_, size_t v_sz_1710_, size_t v_i_1711_, lean_object* v_b_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
uint8_t v___x_1718_; 
v___x_1718_ = lean_usize_dec_lt(v_i_1711_, v_sz_1710_);
if (v___x_1718_ == 0)
{
lean_object* v___x_1719_; 
v___x_1719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1719_, 0, v_b_1712_);
return v___x_1719_;
}
else
{
lean_object* v_snd_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1738_; 
v_snd_1720_ = lean_ctor_get(v_b_1712_, 1);
v_isSharedCheck_1738_ = !lean_is_exclusive(v_b_1712_);
if (v_isSharedCheck_1738_ == 0)
{
lean_object* v_unused_1739_; 
v_unused_1739_ = lean_ctor_get(v_b_1712_, 0);
lean_dec(v_unused_1739_);
v___x_1722_ = v_b_1712_;
v_isShared_1723_ = v_isSharedCheck_1738_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_snd_1720_);
lean_dec(v_b_1712_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1738_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1724_; lean_object* v_a_1726_; lean_object* v_a_1733_; 
v___x_1724_ = lean_box(0);
v_a_1733_ = lean_array_uget_borrowed(v_as_1709_, v_i_1711_);
if (lean_obj_tag(v_a_1733_) == 0)
{
v_a_1726_ = v_snd_1720_;
goto v___jp_1725_;
}
else
{
lean_object* v_val_1734_; lean_object* v___x_1735_; uint8_t v___x_1736_; 
v_val_1734_ = lean_ctor_get(v_a_1733_, 0);
v___x_1735_ = l_Lean_LocalDecl_fvarId(v_val_1734_);
v___x_1736_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_1735_, v_a_1708_);
if (v___x_1736_ == 0)
{
lean_object* v___x_1737_; 
v___x_1737_ = lean_local_ctx_erase(v_snd_1720_, v___x_1735_);
v_a_1726_ = v___x_1737_;
goto v___jp_1725_;
}
else
{
lean_dec(v___x_1735_);
v_a_1726_ = v_snd_1720_;
goto v___jp_1725_;
}
}
v___jp_1725_:
{
lean_object* v___x_1728_; 
if (v_isShared_1723_ == 0)
{
lean_ctor_set(v___x_1722_, 1, v_a_1726_);
lean_ctor_set(v___x_1722_, 0, v___x_1724_);
v___x_1728_ = v___x_1722_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v___x_1724_);
lean_ctor_set(v_reuseFailAlloc_1732_, 1, v_a_1726_);
v___x_1728_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
size_t v___x_1729_; size_t v___x_1730_; lean_object* v___x_1731_; 
v___x_1729_ = ((size_t)1ULL);
v___x_1730_ = lean_usize_add(v_i_1711_, v___x_1729_);
v___x_1731_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___redArg(v_a_1708_, v_as_1709_, v_sz_1710_, v___x_1730_, v___x_1728_);
return v___x_1731_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1___boxed(lean_object* v_a_1740_, lean_object* v_as_1741_, lean_object* v_sz_1742_, lean_object* v_i_1743_, lean_object* v_b_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
size_t v_sz_boxed_1750_; size_t v_i_boxed_1751_; lean_object* v_res_1752_; 
v_sz_boxed_1750_ = lean_unbox_usize(v_sz_1742_);
lean_dec(v_sz_1742_);
v_i_boxed_1751_ = lean_unbox_usize(v_i_1743_);
lean_dec(v_i_1743_);
v_res_1752_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1(v_a_1740_, v_as_1741_, v_sz_boxed_1750_, v_i_boxed_1751_, v_b_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
lean_dec(v___y_1746_);
lean_dec_ref(v___y_1745_);
lean_dec_ref(v_as_1741_);
lean_dec(v_a_1740_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0(lean_object* v_a_1753_, lean_object* v_t_1754_, lean_object* v_init_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
lean_object* v_root_1761_; lean_object* v_tail_1762_; lean_object* v___x_1763_; 
v_root_1761_ = lean_ctor_get(v_t_1754_, 0);
v_tail_1762_ = lean_ctor_get(v_t_1754_, 1);
lean_inc_ref(v_init_1755_);
v___x_1763_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0(v_init_1755_, v_a_1753_, v_root_1761_, v_init_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_);
lean_dec_ref(v_init_1755_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_a_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1800_; 
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1766_ = v___x_1763_;
v_isShared_1767_ = v_isSharedCheck_1800_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_a_1764_);
lean_dec(v___x_1763_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1800_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
if (lean_obj_tag(v_a_1764_) == 0)
{
lean_object* v_a_1768_; lean_object* v___x_1770_; 
v_a_1768_ = lean_ctor_get(v_a_1764_, 0);
lean_inc(v_a_1768_);
lean_dec_ref_known(v_a_1764_, 1);
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 0, v_a_1768_);
v___x_1770_ = v___x_1766_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_a_1768_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
else
{
lean_object* v_a_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; size_t v_sz_1775_; size_t v___x_1776_; lean_object* v___x_1777_; 
lean_del_object(v___x_1766_);
v_a_1772_ = lean_ctor_get(v_a_1764_, 0);
lean_inc(v_a_1772_);
lean_dec_ref_known(v_a_1764_, 1);
v___x_1773_ = lean_box(0);
v___x_1774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1773_);
lean_ctor_set(v___x_1774_, 1, v_a_1772_);
v_sz_1775_ = lean_array_size(v_tail_1762_);
v___x_1776_ = ((size_t)0ULL);
v___x_1777_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1(v_a_1753_, v_tail_1762_, v_sz_1775_, v___x_1776_, v___x_1774_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1791_; 
v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1780_ = v___x_1777_;
v_isShared_1781_ = v_isSharedCheck_1791_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1777_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1791_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v_fst_1782_; 
v_fst_1782_ = lean_ctor_get(v_a_1778_, 0);
if (lean_obj_tag(v_fst_1782_) == 0)
{
lean_object* v_snd_1783_; lean_object* v___x_1785_; 
v_snd_1783_ = lean_ctor_get(v_a_1778_, 1);
lean_inc(v_snd_1783_);
lean_dec(v_a_1778_);
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 0, v_snd_1783_);
v___x_1785_ = v___x_1780_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_snd_1783_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
else
{
lean_object* v_val_1787_; lean_object* v___x_1789_; 
lean_inc_ref(v_fst_1782_);
lean_dec(v_a_1778_);
v_val_1787_ = lean_ctor_get(v_fst_1782_, 0);
lean_inc(v_val_1787_);
lean_dec_ref_known(v_fst_1782_, 1);
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 0, v_val_1787_);
v___x_1789_ = v___x_1780_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_val_1787_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
}
else
{
lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1799_; 
v_a_1792_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1794_ = v___x_1777_;
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_dec(v___x_1777_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1797_; 
if (v_isShared_1795_ == 0)
{
v___x_1797_ = v___x_1794_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_a_1792_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
}
}
}
else
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1808_; 
v_a_1801_ = lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1803_ = v___x_1763_;
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1763_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1804_ == 0)
{
v___x_1806_ = v___x_1803_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_a_1801_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0___boxed(lean_object* v_a_1809_, lean_object* v_t_1810_, lean_object* v_init_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
lean_object* v_res_1817_; 
v_res_1817_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0(v_a_1809_, v_t_1810_, v_init_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
lean_dec_ref(v_t_1810_);
lean_dec(v_a_1809_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___lam__0(lean_object* v_mvarId_1820_, lean_object* v___x_1821_, lean_object* v___x_1822_, lean_object* v_toPreserve_1823_, uint8_t v_indirectProps_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_){
_start:
{
lean_object* v___x_1830_; 
lean_inc(v_mvarId_1820_);
v___x_1830_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1820_, v___x_1821_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
if (lean_obj_tag(v___x_1830_) == 0)
{
uint8_t v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
lean_dec_ref_known(v___x_1830_, 1);
v___x_1831_ = 0;
v___x_1832_ = lean_box(v___x_1831_);
v___x_1833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1832_);
lean_ctor_set(v___x_1833_, 1, v___x_1822_);
v___x_1834_ = lean_st_mk_ref(v___x_1833_);
lean_inc(v_mvarId_1820_);
v___x_1835_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed(v_mvarId_1820_, v_toPreserve_1823_, v_indirectProps_1824_, v___x_1834_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; lean_object* v___x_1837_; lean_object* v_lctx_1838_; lean_object* v_localInstances_1839_; lean_object* v_decls_1840_; lean_object* v___x_1841_; 
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
lean_inc(v_a_1836_);
lean_dec_ref_known(v___x_1835_, 1);
v___x_1837_ = lean_st_ref_get(v___x_1834_);
lean_dec(v___x_1834_);
lean_dec(v___x_1837_);
v_lctx_1838_ = lean_ctor_get(v___y_1825_, 2);
v_localInstances_1839_ = lean_ctor_get(v___y_1825_, 3);
v_decls_1840_ = lean_ctor_get(v_lctx_1838_, 1);
lean_inc_ref(v_lctx_1838_);
v___x_1841_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0(v_a_1836_, v_decls_1840_, v_lctx_1838_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; lean_object* v___x_1843_; lean_object* v___y_1845_; lean_object* v___x_1889_; lean_object* v___x_1890_; uint8_t v___x_1891_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc(v_a_1842_);
lean_dec_ref_known(v___x_1841_, 1);
v___x_1843_ = lean_unsigned_to_nat(0u);
v___x_1889_ = lean_array_get_size(v_localInstances_1839_);
v___x_1890_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___lam__0___closed__0));
v___x_1891_ = lean_nat_dec_lt(v___x_1843_, v___x_1889_);
if (v___x_1891_ == 0)
{
lean_dec(v_a_1836_);
v___y_1845_ = v___x_1890_;
goto v___jp_1844_;
}
else
{
uint8_t v___x_1892_; 
v___x_1892_ = lean_nat_dec_le(v___x_1889_, v___x_1889_);
if (v___x_1892_ == 0)
{
if (v___x_1891_ == 0)
{
lean_dec(v_a_1836_);
v___y_1845_ = v___x_1890_;
goto v___jp_1844_;
}
else
{
size_t v___x_1893_; size_t v___x_1894_; lean_object* v___x_1895_; 
v___x_1893_ = ((size_t)0ULL);
v___x_1894_ = lean_usize_of_nat(v___x_1889_);
v___x_1895_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__3(v_a_1836_, v_localInstances_1839_, v___x_1893_, v___x_1894_, v___x_1890_);
lean_dec(v_a_1836_);
v___y_1845_ = v___x_1895_;
goto v___jp_1844_;
}
}
else
{
size_t v___x_1896_; size_t v___x_1897_; lean_object* v___x_1898_; 
v___x_1896_ = ((size_t)0ULL);
v___x_1897_ = lean_usize_of_nat(v___x_1889_);
v___x_1898_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__3(v_a_1836_, v_localInstances_1839_, v___x_1896_, v___x_1897_, v___x_1890_);
lean_dec(v_a_1836_);
v___y_1845_ = v___x_1898_;
goto v___jp_1844_;
}
}
v___jp_1844_:
{
lean_object* v___x_1846_; 
lean_inc(v_mvarId_1820_);
v___x_1846_ = l_Lean_MVarId_getType(v_mvarId_1820_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; lean_object* v___x_1848_; lean_object* v_a_1849_; lean_object* v___x_1850_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
lean_inc(v_a_1847_);
lean_dec_ref_known(v___x_1846_, 1);
v___x_1848_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___redArg(v_a_1847_, v___y_1826_);
v_a_1849_ = lean_ctor_get(v___x_1848_, 0);
lean_inc(v_a_1849_);
lean_dec_ref(v___x_1848_);
lean_inc(v_mvarId_1820_);
v___x_1850_ = l_Lean_MVarId_getTag(v_mvarId_1820_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_object* v_a_1851_; uint8_t v___x_1852_; lean_object* v___x_1853_; 
v_a_1851_ = lean_ctor_get(v___x_1850_, 0);
lean_inc(v_a_1851_);
lean_dec_ref_known(v___x_1850_, 1);
v___x_1852_ = 2;
v___x_1853_ = l_Lean_Meta_mkFreshExprMVarAt(v_a_1842_, v___y_1845_, v_a_1849_, v___x_1852_, v_a_1851_, v___x_1843_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
lean_dec_ref(v___y_1825_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v_a_1854_; lean_object* v___x_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1863_; 
v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
lean_inc_n(v_a_1854_, 2);
lean_dec_ref_known(v___x_1853_, 1);
v___x_1855_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___redArg(v_mvarId_1820_, v_a_1854_, v___y_1826_);
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1863_ == 0)
{
lean_object* v_unused_1864_; 
v_unused_1864_ = lean_ctor_get(v___x_1855_, 0);
lean_dec(v_unused_1864_);
v___x_1857_ = v___x_1855_;
v_isShared_1858_ = v_isSharedCheck_1863_;
goto v_resetjp_1856_;
}
else
{
lean_dec(v___x_1855_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1863_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1859_; lean_object* v___x_1861_; 
v___x_1859_ = l_Lean_Expr_mvarId_x21(v_a_1854_);
lean_dec(v_a_1854_);
if (v_isShared_1858_ == 0)
{
lean_ctor_set(v___x_1857_, 0, v___x_1859_);
v___x_1861_ = v___x_1857_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v___x_1859_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
}
else
{
lean_object* v_a_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1872_; 
lean_dec(v_mvarId_1820_);
v_a_1865_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1867_ = v___x_1853_;
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v___x_1853_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1870_; 
if (v_isShared_1868_ == 0)
{
v___x_1870_ = v___x_1867_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_a_1865_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
}
}
else
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1880_; 
lean_dec(v_a_1849_);
lean_dec_ref(v___y_1845_);
lean_dec(v_a_1842_);
lean_dec_ref(v___y_1825_);
lean_dec(v_mvarId_1820_);
v_a_1873_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1875_ = v___x_1850_;
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1850_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1876_ == 0)
{
v___x_1878_ = v___x_1875_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_a_1873_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
else
{
lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1888_; 
lean_dec_ref(v___y_1845_);
lean_dec(v_a_1842_);
lean_dec_ref(v___y_1825_);
lean_dec(v_mvarId_1820_);
v_a_1881_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1888_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1883_ = v___x_1846_;
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_dec(v___x_1846_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1886_; 
if (v_isShared_1884_ == 0)
{
v___x_1886_ = v___x_1883_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_a_1881_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
}
}
}
else
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1906_; 
lean_dec(v_a_1836_);
lean_dec_ref(v___y_1825_);
lean_dec(v_mvarId_1820_);
v_a_1899_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1901_ = v___x_1841_;
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1841_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1904_; 
if (v_isShared_1902_ == 0)
{
v___x_1904_ = v___x_1901_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_a_1899_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
}
}
else
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1914_; 
lean_dec(v___x_1834_);
lean_dec_ref(v___y_1825_);
lean_dec(v_mvarId_1820_);
v_a_1907_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1909_ = v___x_1835_;
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1835_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1912_; 
if (v_isShared_1910_ == 0)
{
v___x_1912_ = v___x_1909_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_a_1907_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
}
else
{
lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1922_; 
lean_dec_ref(v___y_1825_);
lean_dec(v___x_1822_);
lean_dec(v_mvarId_1820_);
v_a_1915_ = lean_ctor_get(v___x_1830_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1917_ = v___x_1830_;
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1830_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1920_; 
if (v_isShared_1918_ == 0)
{
v___x_1920_ = v___x_1917_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_a_1915_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___lam__0___boxed(lean_object* v_mvarId_1923_, lean_object* v___x_1924_, lean_object* v___x_1925_, lean_object* v_toPreserve_1926_, lean_object* v_indirectProps_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_){
_start:
{
uint8_t v_indirectProps_boxed_1933_; lean_object* v_res_1934_; 
v_indirectProps_boxed_1933_ = lean_unbox(v_indirectProps_1927_);
v_res_1934_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___lam__0(v_mvarId_1923_, v___x_1924_, v___x_1925_, v_toPreserve_1926_, v_indirectProps_boxed_1933_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
lean_dec(v___y_1929_);
lean_dec_ref(v_toPreserve_1926_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(lean_object* v_mvarId_1938_, lean_object* v_toPreserve_1939_, uint8_t v_indirectProps_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_){
_start:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___f_1949_; lean_object* v___x_1950_; 
v___x_1946_ = lean_box(1);
v___x_1947_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___closed__1));
v___x_1948_ = lean_box(v_indirectProps_1940_);
lean_inc(v_mvarId_1938_);
v___f_1949_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1949_, 0, v_mvarId_1938_);
lean_closure_set(v___f_1949_, 1, v___x_1947_);
lean_closure_set(v___f_1949_, 2, v___x_1946_);
lean_closure_set(v___f_1949_, 3, v_toPreserve_1939_);
lean_closure_set(v___f_1949_, 4, v___x_1948_);
v___x_1950_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___redArg(v_mvarId_1938_, v___f_1949_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___boxed(lean_object* v_mvarId_1951_, lean_object* v_toPreserve_1952_, lean_object* v_indirectProps_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_){
_start:
{
uint8_t v_indirectProps_boxed_1959_; lean_object* v_res_1960_; 
v_indirectProps_boxed_1959_ = lean_unbox(v_indirectProps_1953_);
v_res_1960_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(v_mvarId_1951_, v_toPreserve_1952_, v_indirectProps_boxed_1959_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_);
lean_dec(v_a_1957_);
lean_dec_ref(v_a_1956_);
lean_dec(v_a_1955_);
lean_dec_ref(v_a_1954_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2(lean_object* v_mvarId_1961_, lean_object* v_val_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
lean_object* v___x_1968_; 
v___x_1968_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___redArg(v_mvarId_1961_, v_val_1962_, v___y_1964_);
return v___x_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___boxed(lean_object* v_mvarId_1969_, lean_object* v_val_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2(v_mvarId_1969_, v_val_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4(lean_object* v_00_u03b2_1977_, lean_object* v_x_1978_, lean_object* v_x_1979_, lean_object* v_x_1980_){
_start:
{
lean_object* v___x_1981_; 
v___x_1981_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4___redArg(v_x_1978_, v_x_1979_, v_x_1980_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6(lean_object* v_a_1982_, lean_object* v_as_1983_, size_t v_sz_1984_, size_t v_i_1985_, lean_object* v_b_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_){
_start:
{
lean_object* v___x_1992_; 
v___x_1992_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___redArg(v_a_1982_, v_as_1983_, v_sz_1984_, v_i_1985_, v_b_1986_);
return v___x_1992_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___boxed(lean_object* v_a_1993_, lean_object* v_as_1994_, lean_object* v_sz_1995_, lean_object* v_i_1996_, lean_object* v_b_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
size_t v_sz_boxed_2003_; size_t v_i_boxed_2004_; lean_object* v_res_2005_; 
v_sz_boxed_2003_ = lean_unbox_usize(v_sz_1995_);
lean_dec(v_sz_1995_);
v_i_boxed_2004_ = lean_unbox_usize(v_i_1996_);
lean_dec(v_i_1996_);
v_res_2005_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6(v_a_1993_, v_as_1994_, v_sz_boxed_2003_, v_i_boxed_2004_, v_b_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec_ref(v_as_1994_);
lean_dec(v_a_1993_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9(lean_object* v_00_u03b2_2006_, lean_object* v_x_2007_, size_t v_x_2008_, size_t v_x_2009_, lean_object* v_x_2010_, lean_object* v_x_2011_){
_start:
{
lean_object* v___x_2012_; 
v___x_2012_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg(v_x_2007_, v_x_2008_, v_x_2009_, v_x_2010_, v_x_2011_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___boxed(lean_object* v_00_u03b2_2013_, lean_object* v_x_2014_, lean_object* v_x_2015_, lean_object* v_x_2016_, lean_object* v_x_2017_, lean_object* v_x_2018_){
_start:
{
size_t v_x_8495__boxed_2019_; size_t v_x_8496__boxed_2020_; lean_object* v_res_2021_; 
v_x_8495__boxed_2019_ = lean_unbox_usize(v_x_2015_);
lean_dec(v_x_2015_);
v_x_8496__boxed_2020_ = lean_unbox_usize(v_x_2016_);
lean_dec(v_x_2016_);
v_res_2021_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9(v_00_u03b2_2013_, v_x_2014_, v_x_8495__boxed_2019_, v_x_8496__boxed_2020_, v_x_2017_, v_x_2018_);
return v_res_2021_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7(lean_object* v_a_2022_, lean_object* v_as_2023_, size_t v_sz_2024_, size_t v_i_2025_, lean_object* v_b_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_){
_start:
{
lean_object* v___x_2032_; 
v___x_2032_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___redArg(v_a_2022_, v_as_2023_, v_sz_2024_, v_i_2025_, v_b_2026_);
return v___x_2032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___boxed(lean_object* v_a_2033_, lean_object* v_as_2034_, lean_object* v_sz_2035_, lean_object* v_i_2036_, lean_object* v_b_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
size_t v_sz_boxed_2043_; size_t v_i_boxed_2044_; lean_object* v_res_2045_; 
v_sz_boxed_2043_ = lean_unbox_usize(v_sz_2035_);
lean_dec(v_sz_2035_);
v_i_boxed_2044_ = lean_unbox_usize(v_i_2036_);
lean_dec(v_i_2036_);
v_res_2045_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7(v_a_2033_, v_as_2034_, v_sz_boxed_2043_, v_i_boxed_2044_, v_b_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec_ref(v_as_2034_);
lean_dec(v_a_2033_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12(lean_object* v_00_u03b2_2046_, lean_object* v_n_2047_, lean_object* v_k_2048_, lean_object* v_v_2049_){
_start:
{
lean_object* v___x_2050_; 
v___x_2050_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12___redArg(v_n_2047_, v_k_2048_, v_v_2049_);
return v___x_2050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13(lean_object* v_00_u03b2_2051_, size_t v_depth_2052_, lean_object* v_keys_2053_, lean_object* v_vals_2054_, lean_object* v_heq_2055_, lean_object* v_i_2056_, lean_object* v_entries_2057_){
_start:
{
lean_object* v___x_2058_; 
v___x_2058_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___redArg(v_depth_2052_, v_keys_2053_, v_vals_2054_, v_i_2056_, v_entries_2057_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___boxed(lean_object* v_00_u03b2_2059_, lean_object* v_depth_2060_, lean_object* v_keys_2061_, lean_object* v_vals_2062_, lean_object* v_heq_2063_, lean_object* v_i_2064_, lean_object* v_entries_2065_){
_start:
{
size_t v_depth_boxed_2066_; lean_object* v_res_2067_; 
v_depth_boxed_2066_ = lean_unbox_usize(v_depth_2060_);
lean_dec(v_depth_2060_);
v_res_2067_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13(v_00_u03b2_2059_, v_depth_boxed_2066_, v_keys_2061_, v_vals_2062_, v_heq_2063_, v_i_2064_, v_entries_2065_);
lean_dec_ref(v_vals_2062_);
lean_dec_ref(v_keys_2061_);
return v_res_2067_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12_spec__13(lean_object* v_00_u03b2_2068_, lean_object* v_x_2069_, lean_object* v_x_2070_, lean_object* v_x_2071_, lean_object* v_x_2072_){
_start:
{
lean_object* v___x_2073_; 
v___x_2073_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12_spec__13___redArg(v_x_2069_, v_x_2070_, v_x_2071_, v_x_2072_);
return v___x_2073_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_cleanup(lean_object* v_mvarId_2074_, lean_object* v_toPreserve_2075_, uint8_t v_indirectProps_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_){
_start:
{
lean_object* v___x_2082_; 
v___x_2082_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(v_mvarId_2074_, v_toPreserve_2075_, v_indirectProps_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_);
return v___x_2082_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_cleanup___boxed(lean_object* v_mvarId_2083_, lean_object* v_toPreserve_2084_, lean_object* v_indirectProps_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_){
_start:
{
uint8_t v_indirectProps_boxed_2091_; lean_object* v_res_2092_; 
v_indirectProps_boxed_2091_ = lean_unbox(v_indirectProps_2085_);
v_res_2092_ = l_Lean_MVarId_cleanup(v_mvarId_2083_, v_toPreserve_2084_, v_indirectProps_boxed_2091_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_);
lean_dec(v_a_2089_);
lean_dec_ref(v_a_2088_);
lean_dec(v_a_2087_);
lean_dec_ref(v_a_2086_);
return v_res_2092_;
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
