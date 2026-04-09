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
size_t lean_usize_shift_left(size_t, size_t);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
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
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__2;
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
lean_dec_ref(v_x_84_);
v___x_94_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__1(v_init_83_, v_l_92_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_);
if (lean_obj_tag(v___x_94_) == 0)
{
lean_object* v___x_95_; 
lean_dec_ref(v___x_94_);
v___x_95_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v_k_91_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_);
if (lean_obj_tag(v___x_95_) == 0)
{
lean_object* v___x_96_; 
lean_dec_ref(v___x_95_);
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
lean_dec_ref(v___x_115_);
v___x_117_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__3, &l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__3);
v___x_118_ = lean_st_mk_ref(v___x_117_);
v___x_119_ = l_Lean_Expr_collectFVars(v_a_116_, v___x_118_, v_a_110_, v_a_111_, v_a_112_, v_a_113_);
if (lean_obj_tag(v___x_119_) == 0)
{
lean_object* v___x_120_; lean_object* v_fvarSet_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
lean_dec_ref(v___x_119_);
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
lean_dec_ref(v___x_155_);
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
lean_dec_ref(v___x_163_);
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
lean_dec_ref(v___x_271_);
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
uint8_t v___x_9653__boxed_313_; uint8_t v_res_314_; lean_object* v_r_315_; 
v___x_9653__boxed_313_ = lean_unbox(v___x_311_);
v_res_314_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__1(v___x_9653__boxed_313_, v_x_312_);
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
lean_dec_ref(v___x_349_);
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
lean_dec_ref(v___x_383_);
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
lean_dec_ref(v___x_386_);
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
lean_dec_ref(v___x_360_);
v___x_362_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v_val_361_, v___f_351_, v___f_353_, v___y_357_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_object* v_a_363_; uint8_t v___x_364_; 
v_a_363_ = lean_ctor_get(v___x_362_, 0);
lean_inc(v_a_363_);
lean_dec_ref(v___x_362_);
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
lean_dec_ref(v___x_365_);
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
lean_dec_ref(v___x_459_);
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
lean_dec_ref(v___x_493_);
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
lean_dec_ref(v___x_496_);
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
lean_dec_ref(v___x_470_);
v___x_472_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v_val_471_, v___f_461_, v___f_463_, v___y_467_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; uint8_t v___x_474_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
lean_inc(v_a_473_);
lean_dec_ref(v___x_472_);
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
lean_dec_ref(v___x_475_);
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
lean_dec_ref(v___x_569_);
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
lean_dec_ref(v___x_603_);
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
lean_dec_ref(v___x_606_);
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
lean_dec_ref(v___x_580_);
v___x_582_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v_val_581_, v___f_571_, v___f_573_, v___y_577_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v_a_583_; uint8_t v___x_584_; 
v_a_583_ = lean_ctor_get(v___x_582_, 0);
lean_inc(v_a_583_);
lean_dec_ref(v___x_582_);
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
lean_dec_ref(v___x_585_);
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
lean_dec_ref(v___x_679_);
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
lean_dec_ref(v___x_713_);
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
lean_dec_ref(v___x_716_);
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
lean_dec_ref(v___x_690_);
v___x_692_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v_val_691_, v___f_681_, v___f_683_, v___y_687_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; uint8_t v___x_694_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_a_693_);
lean_dec_ref(v___x_692_);
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
lean_dec_ref(v___x_695_);
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
lean_object* v_cs_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_799_; 
v_cs_765_ = lean_ctor_get(v_n_757_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v_n_757_);
if (v_isSharedCheck_799_ == 0)
{
v___x_767_ = v_n_757_;
v_isShared_768_ = v_isSharedCheck_799_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_cs_765_);
lean_dec(v_n_757_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_799_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_769_; lean_object* v___x_770_; size_t v_sz_771_; size_t v___x_772_; lean_object* v___x_773_; 
v___x_769_ = lean_box(0);
v___x_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_770_, 0, v___x_769_);
lean_ctor_set(v___x_770_, 1, v_b_758_);
v_sz_771_ = lean_array_size(v_cs_765_);
v___x_772_ = ((size_t)0ULL);
v___x_773_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__2(v_init_756_, v_cs_765_, v_sz_771_, v___x_772_, v___x_770_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
lean_dec_ref(v_cs_765_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_790_; 
v_a_774_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_790_ == 0)
{
v___x_776_ = v___x_773_;
v_isShared_777_ = v_isSharedCheck_790_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_773_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_790_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v_fst_778_; 
v_fst_778_ = lean_ctor_get(v_a_774_, 0);
if (lean_obj_tag(v_fst_778_) == 0)
{
lean_object* v_snd_779_; lean_object* v___x_781_; 
v_snd_779_ = lean_ctor_get(v_a_774_, 1);
lean_inc(v_snd_779_);
lean_dec(v_a_774_);
if (v_isShared_768_ == 0)
{
lean_ctor_set_tag(v___x_767_, 1);
lean_ctor_set(v___x_767_, 0, v_snd_779_);
v___x_781_ = v___x_767_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_snd_779_);
v___x_781_ = v_reuseFailAlloc_785_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
lean_object* v___x_783_; 
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 0, v___x_781_);
v___x_783_ = v___x_776_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_781_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
else
{
lean_object* v_val_786_; lean_object* v___x_788_; 
lean_inc_ref(v_fst_778_);
lean_dec(v_a_774_);
lean_del_object(v___x_767_);
v_val_786_ = lean_ctor_get(v_fst_778_, 0);
lean_inc(v_val_786_);
lean_dec_ref(v_fst_778_);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 0, v_val_786_);
v___x_788_ = v___x_776_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_val_786_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
else
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
lean_del_object(v___x_767_);
v_a_791_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v___x_773_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_773_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_791_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
}
else
{
lean_object* v_vs_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_834_; 
v_vs_800_ = lean_ctor_get(v_n_757_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v_n_757_);
if (v_isSharedCheck_834_ == 0)
{
v___x_802_ = v_n_757_;
v_isShared_803_ = v_isSharedCheck_834_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_vs_800_);
lean_dec(v_n_757_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_834_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_804_; lean_object* v___x_805_; size_t v_sz_806_; size_t v___x_807_; lean_object* v___x_808_; 
v___x_804_ = lean_box(0);
v___x_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_805_, 0, v___x_804_);
lean_ctor_set(v___x_805_, 1, v_b_758_);
v_sz_806_ = lean_array_size(v_vs_800_);
v___x_807_ = ((size_t)0ULL);
v___x_808_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3(v_vs_800_, v_sz_806_, v___x_807_, v___x_805_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
lean_dec_ref(v_vs_800_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_825_; 
v_a_809_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_825_ == 0)
{
v___x_811_ = v___x_808_;
v_isShared_812_ = v_isSharedCheck_825_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_808_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_825_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v_fst_813_; 
v_fst_813_ = lean_ctor_get(v_a_809_, 0);
if (lean_obj_tag(v_fst_813_) == 0)
{
lean_object* v_snd_814_; lean_object* v___x_816_; 
v_snd_814_ = lean_ctor_get(v_a_809_, 1);
lean_inc(v_snd_814_);
lean_dec(v_a_809_);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 0, v_snd_814_);
v___x_816_ = v___x_802_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_snd_814_);
v___x_816_ = v_reuseFailAlloc_820_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
lean_object* v___x_818_; 
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 0, v___x_816_);
v___x_818_ = v___x_811_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_816_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
else
{
lean_object* v_val_821_; lean_object* v___x_823_; 
lean_inc_ref(v_fst_813_);
lean_dec(v_a_809_);
lean_del_object(v___x_802_);
v_val_821_ = lean_ctor_get(v_fst_813_, 0);
lean_inc(v_val_821_);
lean_dec_ref(v_fst_813_);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 0, v_val_821_);
v___x_823_ = v___x_811_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_val_821_);
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
else
{
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_833_; 
lean_del_object(v___x_802_);
v_a_826_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_833_ == 0)
{
v___x_828_ = v___x_808_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_808_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_831_; 
if (v_isShared_829_ == 0)
{
v___x_831_ = v___x_828_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_a_826_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__2(lean_object* v_init_835_, lean_object* v_as_836_, size_t v_sz_837_, size_t v_i_838_, lean_object* v_b_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
uint8_t v___x_846_; 
v___x_846_ = lean_usize_dec_lt(v_i_838_, v_sz_837_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; 
v___x_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_847_, 0, v_b_839_);
return v___x_847_;
}
else
{
lean_object* v_snd_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_882_; 
v_snd_848_ = lean_ctor_get(v_b_839_, 1);
v_isSharedCheck_882_ = !lean_is_exclusive(v_b_839_);
if (v_isSharedCheck_882_ == 0)
{
lean_object* v_unused_883_; 
v_unused_883_ = lean_ctor_get(v_b_839_, 0);
lean_dec(v_unused_883_);
v___x_850_ = v_b_839_;
v_isShared_851_ = v_isSharedCheck_882_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_snd_848_);
lean_dec(v_b_839_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_882_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v_a_852_; lean_object* v___x_853_; 
v_a_852_ = lean_array_uget_borrowed(v_as_836_, v_i_838_);
lean_inc(v_snd_848_);
lean_inc(v_a_852_);
v___x_853_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1(v_init_835_, v_a_852_, v_snd_848_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_873_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_873_ == 0)
{
v___x_856_ = v___x_853_;
v_isShared_857_ = v_isSharedCheck_873_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_853_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_873_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
if (lean_obj_tag(v_a_854_) == 0)
{
lean_object* v___x_858_; lean_object* v___x_860_; 
v___x_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_858_, 0, v_a_854_);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 0, v___x_858_);
v___x_860_ = v___x_850_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_858_);
lean_ctor_set(v_reuseFailAlloc_864_, 1, v_snd_848_);
v___x_860_ = v_reuseFailAlloc_864_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
lean_object* v___x_862_; 
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 0, v___x_860_);
v___x_862_ = v___x_856_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_860_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
else
{
lean_object* v_a_865_; lean_object* v___x_866_; lean_object* v___x_868_; 
lean_del_object(v___x_856_);
lean_dec(v_snd_848_);
v_a_865_ = lean_ctor_get(v_a_854_, 0);
lean_inc(v_a_865_);
lean_dec_ref(v_a_854_);
v___x_866_ = lean_box(0);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 1, v_a_865_);
lean_ctor_set(v___x_850_, 0, v___x_866_);
v___x_868_ = v___x_850_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_866_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v_a_865_);
v___x_868_ = v_reuseFailAlloc_872_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
size_t v___x_869_; size_t v___x_870_; 
v___x_869_ = ((size_t)1ULL);
v___x_870_ = lean_usize_add(v_i_838_, v___x_869_);
v_i_838_ = v___x_870_;
v_b_839_ = v___x_868_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_881_; 
lean_del_object(v___x_850_);
lean_dec(v_snd_848_);
v_a_874_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_881_ == 0)
{
v___x_876_ = v___x_853_;
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_853_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_879_; 
if (v_isShared_877_ == 0)
{
v___x_879_ = v___x_876_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_a_874_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__2___boxed(lean_object* v_init_884_, lean_object* v_as_885_, lean_object* v_sz_886_, lean_object* v_i_887_, lean_object* v_b_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
size_t v_sz_boxed_895_; size_t v_i_boxed_896_; lean_object* v_res_897_; 
v_sz_boxed_895_ = lean_unbox_usize(v_sz_886_);
lean_dec(v_sz_886_);
v_i_boxed_896_ = lean_unbox_usize(v_i_887_);
lean_dec(v_i_887_);
v_res_897_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__2(v_init_884_, v_as_885_, v_sz_boxed_895_, v_i_boxed_896_, v_b_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
lean_dec(v___y_889_);
lean_dec_ref(v_as_885_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1___boxed(lean_object* v_init_898_, lean_object* v_n_899_, lean_object* v_b_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1(v_init_898_, v_n_899_, v_b_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___y_901_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1(lean_object* v_t_908_, lean_object* v_init_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v_root_916_; lean_object* v_tail_917_; lean_object* v___x_918_; 
v_root_916_ = lean_ctor_get(v_t_908_, 0);
lean_inc_ref(v_root_916_);
v_tail_917_ = lean_ctor_get(v_t_908_, 1);
lean_inc_ref(v_tail_917_);
lean_dec_ref(v_t_908_);
v___x_918_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1(v_init_909_, v_root_916_, v_init_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_);
if (lean_obj_tag(v___x_918_) == 0)
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_955_; 
v_a_919_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_955_ == 0)
{
v___x_921_ = v___x_918_;
v_isShared_922_ = v_isSharedCheck_955_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_918_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_955_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
if (lean_obj_tag(v_a_919_) == 0)
{
lean_object* v_a_923_; lean_object* v___x_925_; 
lean_dec_ref(v_tail_917_);
v_a_923_ = lean_ctor_get(v_a_919_, 0);
lean_inc(v_a_923_);
lean_dec_ref(v_a_919_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 0, v_a_923_);
v___x_925_ = v___x_921_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_a_923_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
else
{
lean_object* v_a_927_; lean_object* v___x_928_; lean_object* v___x_929_; size_t v_sz_930_; size_t v___x_931_; lean_object* v___x_932_; 
lean_del_object(v___x_921_);
v_a_927_ = lean_ctor_get(v_a_919_, 0);
lean_inc(v_a_927_);
lean_dec_ref(v_a_919_);
v___x_928_ = lean_box(0);
v___x_929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
lean_ctor_set(v___x_929_, 1, v_a_927_);
v_sz_930_ = lean_array_size(v_tail_917_);
v___x_931_ = ((size_t)0ULL);
v___x_932_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2(v_tail_917_, v_sz_930_, v___x_931_, v___x_929_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_);
lean_dec_ref(v_tail_917_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_946_; 
v_a_933_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_946_ == 0)
{
v___x_935_ = v___x_932_;
v_isShared_936_ = v_isSharedCheck_946_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v___x_932_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_946_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v_fst_937_; 
v_fst_937_ = lean_ctor_get(v_a_933_, 0);
if (lean_obj_tag(v_fst_937_) == 0)
{
lean_object* v_snd_938_; lean_object* v___x_940_; 
v_snd_938_ = lean_ctor_get(v_a_933_, 1);
lean_inc(v_snd_938_);
lean_dec(v_a_933_);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 0, v_snd_938_);
v___x_940_ = v___x_935_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_snd_938_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
else
{
lean_object* v_val_942_; lean_object* v___x_944_; 
lean_inc_ref(v_fst_937_);
lean_dec(v_a_933_);
v_val_942_ = lean_ctor_get(v_fst_937_, 0);
lean_inc(v_val_942_);
lean_dec_ref(v_fst_937_);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 0, v_val_942_);
v___x_944_ = v___x_935_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_val_942_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
}
else
{
lean_object* v_a_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_954_; 
v_a_947_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_954_ == 0)
{
v___x_949_ = v___x_932_;
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_a_947_);
lean_dec(v___x_932_);
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
}
else
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_963_; 
lean_dec_ref(v_tail_917_);
v_a_956_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_963_ == 0)
{
v___x_958_ = v___x_918_;
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_918_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_961_; 
if (v_isShared_959_ == 0)
{
v___x_961_ = v___x_958_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_956_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1___boxed(lean_object* v_t_964_, lean_object* v_init_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1(v_t_964_, v_init_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep(lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_){
_start:
{
lean_object* v_lctx_979_; lean_object* v_decls_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v_lctx_979_ = lean_ctor_get(v_a_974_, 2);
v_decls_980_ = lean_ctor_get(v_lctx_979_, 1);
v___x_981_ = lean_box(0);
lean_inc_ref(v_decls_980_);
v___x_982_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1(v_decls_980_, v___x_981_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_989_; 
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_989_ == 0)
{
lean_object* v_unused_990_; 
v_unused_990_ = lean_ctor_get(v___x_982_, 0);
lean_dec(v_unused_990_);
v___x_984_ = v___x_982_;
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
else
{
lean_dec(v___x_982_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_987_; 
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 0, v___x_981_);
v___x_987_ = v___x_984_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v___x_981_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
else
{
return v___x_982_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep___boxed(lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep(v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_);
lean_dec(v_a_995_);
lean_dec_ref(v_a_994_);
lean_dec(v_a_993_);
lean_dec_ref(v_a_992_);
lean_dec(v_a_991_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectProps(lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_){
_start:
{
lean_object* v___x_1004_; lean_object* v_snd_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1029_; 
v___x_1004_ = lean_st_ref_take(v_a_998_);
v_snd_1005_ = lean_ctor_get(v___x_1004_, 1);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1029_ == 0)
{
lean_object* v_unused_1030_; 
v_unused_1030_ = lean_ctor_get(v___x_1004_, 0);
lean_dec(v_unused_1030_);
v___x_1007_ = v___x_1004_;
v_isShared_1008_ = v_isSharedCheck_1029_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_snd_1005_);
lean_dec(v___x_1004_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1029_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
uint8_t v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1012_; 
v___x_1009_ = 0;
v___x_1010_ = lean_box(v___x_1009_);
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 0, v___x_1010_);
v___x_1012_ = v___x_1007_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1010_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v_snd_1005_);
v___x_1012_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = lean_st_ref_set(v_a_998_, v___x_1012_);
v___x_1014_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep(v_a_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1026_; 
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1026_ == 0)
{
lean_object* v_unused_1027_; 
v_unused_1027_ = lean_ctor_get(v___x_1014_, 0);
lean_dec(v_unused_1027_);
v___x_1016_ = v___x_1014_;
v_isShared_1017_ = v_isSharedCheck_1026_;
goto v_resetjp_1015_;
}
else
{
lean_dec(v___x_1014_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1026_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1018_; lean_object* v_fst_1019_; uint8_t v___x_1020_; 
v___x_1018_ = lean_st_ref_get(v_a_998_);
v_fst_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc(v_fst_1019_);
lean_dec(v___x_1018_);
v___x_1020_ = lean_unbox(v_fst_1019_);
lean_dec(v_fst_1019_);
if (v___x_1020_ == 0)
{
lean_object* v___x_1021_; lean_object* v___x_1023_; 
v___x_1021_ = lean_box(0);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 0, v___x_1021_);
v___x_1023_ = v___x_1016_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1021_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
else
{
lean_del_object(v___x_1016_);
goto _start;
}
}
}
else
{
return v___x_1014_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectProps___boxed(lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectProps(v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_);
lean_dec(v_a_1035_);
lean_dec_ref(v_a_1034_);
lean_dec(v_a_1033_);
lean_dec_ref(v_a_1032_);
lean_dec(v_a_1031_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed_spec__0(lean_object* v_as_1038_, size_t v_i_1039_, size_t v_stop_1040_, lean_object* v_b_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
uint8_t v___x_1048_; 
v___x_1048_ = lean_usize_dec_eq(v_i_1039_, v_stop_1040_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = lean_array_uget_borrowed(v_as_1038_, v_i_1039_);
lean_inc(v___x_1049_);
v___x_1050_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_1049_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v_a_1051_; size_t v___x_1052_; size_t v___x_1053_; 
v_a_1051_ = lean_ctor_get(v___x_1050_, 0);
lean_inc(v_a_1051_);
lean_dec_ref(v___x_1050_);
v___x_1052_ = ((size_t)1ULL);
v___x_1053_ = lean_usize_add(v_i_1039_, v___x_1052_);
v_i_1039_ = v___x_1053_;
v_b_1041_ = v_a_1051_;
goto _start;
}
else
{
return v___x_1050_;
}
}
else
{
lean_object* v___x_1055_; 
v___x_1055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1055_, 0, v_b_1041_);
return v___x_1055_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed_spec__0___boxed(lean_object* v_as_1056_, lean_object* v_i_1057_, lean_object* v_stop_1058_, lean_object* v_b_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
size_t v_i_boxed_1066_; size_t v_stop_boxed_1067_; lean_object* v_res_1068_; 
v_i_boxed_1066_ = lean_unbox_usize(v_i_1057_);
lean_dec(v_i_1057_);
v_stop_boxed_1067_ = lean_unbox_usize(v_stop_1058_);
lean_dec(v_stop_1058_);
v_res_1068_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed_spec__0(v_as_1056_, v_i_boxed_1066_, v_stop_boxed_1067_, v_b_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v___y_1060_);
lean_dec_ref(v_as_1056_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed(lean_object* v_mvarId_1069_, lean_object* v_toPreserve_1070_, uint8_t v_indirectProps_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_){
_start:
{
lean_object* v___y_1079_; lean_object* v___y_1094_; lean_object* v___x_1103_; 
v___x_1103_ = l_Lean_MVarId_getType(v_mvarId_1069_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_object* v_a_1104_; lean_object* v___x_1105_; lean_object* v_a_1106_; lean_object* v___x_1107_; 
v_a_1104_ = lean_ctor_get(v___x_1103_, 0);
lean_inc(v_a_1104_);
lean_dec_ref(v___x_1103_);
v___x_1105_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0___redArg(v_a_1104_, v_a_1074_);
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_a_1106_);
lean_dec_ref(v___x_1105_);
v___x_1107_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars(v_a_1106_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_object* v___x_1108_; lean_object* v___x_1109_; uint8_t v___x_1110_; 
lean_dec_ref(v___x_1107_);
v___x_1108_ = lean_unsigned_to_nat(0u);
v___x_1109_ = lean_array_get_size(v_toPreserve_1070_);
v___x_1110_ = lean_nat_dec_lt(v___x_1108_, v___x_1109_);
if (v___x_1110_ == 0)
{
goto v___jp_1083_;
}
else
{
lean_object* v___x_1111_; uint8_t v___x_1112_; 
v___x_1111_ = lean_box(0);
v___x_1112_ = lean_nat_dec_le(v___x_1109_, v___x_1109_);
if (v___x_1112_ == 0)
{
if (v___x_1110_ == 0)
{
goto v___jp_1083_;
}
else
{
size_t v___x_1113_; size_t v___x_1114_; lean_object* v___x_1115_; 
v___x_1113_ = ((size_t)0ULL);
v___x_1114_ = lean_usize_of_nat(v___x_1109_);
v___x_1115_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed_spec__0(v_toPreserve_1070_, v___x_1113_, v___x_1114_, v___x_1111_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_);
v___y_1094_ = v___x_1115_;
goto v___jp_1093_;
}
}
else
{
size_t v___x_1116_; size_t v___x_1117_; lean_object* v___x_1118_; 
v___x_1116_ = ((size_t)0ULL);
v___x_1117_ = lean_usize_of_nat(v___x_1109_);
v___x_1118_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed_spec__0(v_toPreserve_1070_, v___x_1116_, v___x_1117_, v___x_1111_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_);
v___y_1094_ = v___x_1118_;
goto v___jp_1093_;
}
}
}
else
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1126_; 
v_a_1119_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1121_ = v___x_1107_;
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1107_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1124_; 
if (v_isShared_1122_ == 0)
{
v___x_1124_ = v___x_1121_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_a_1119_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
}
else
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1134_; 
v_a_1127_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1129_ = v___x_1103_;
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1103_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
if (v_isShared_1130_ == 0)
{
v___x_1132_ = v___x_1129_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1127_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
v___jp_1078_:
{
lean_object* v___x_1080_; lean_object* v_snd_1081_; lean_object* v___x_1082_; 
v___x_1080_ = lean_st_ref_get(v___y_1079_);
v_snd_1081_ = lean_ctor_get(v___x_1080_, 1);
lean_inc(v_snd_1081_);
lean_dec(v___x_1080_);
v___x_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1082_, 0, v_snd_1081_);
return v___x_1082_;
}
v___jp_1083_:
{
if (v_indirectProps_1071_ == 0)
{
v___y_1079_ = v_a_1072_;
goto v___jp_1078_;
}
else
{
lean_object* v___x_1084_; 
v___x_1084_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectProps(v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_dec_ref(v___x_1084_);
v___y_1079_ = v_a_1072_;
goto v___jp_1078_;
}
else
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1092_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1087_ = v___x_1084_;
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1084_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1090_; 
if (v_isShared_1088_ == 0)
{
v___x_1090_ = v___x_1087_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_a_1085_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
}
v___jp_1093_:
{
if (lean_obj_tag(v___y_1094_) == 0)
{
lean_dec_ref(v___y_1094_);
goto v___jp_1083_;
}
else
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
v_a_1095_ = lean_ctor_get(v___y_1094_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___y_1094_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___y_1094_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___y_1094_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed___boxed(lean_object* v_mvarId_1135_, lean_object* v_toPreserve_1136_, lean_object* v_indirectProps_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_){
_start:
{
uint8_t v_indirectProps_boxed_1144_; lean_object* v_res_1145_; 
v_indirectProps_boxed_1144_ = lean_unbox(v_indirectProps_1137_);
v_res_1145_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed(v_mvarId_1135_, v_toPreserve_1136_, v_indirectProps_boxed_1144_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
lean_dec(v_a_1142_);
lean_dec_ref(v_a_1141_);
lean_dec(v_a_1140_);
lean_dec_ref(v_a_1139_);
lean_dec(v_a_1138_);
lean_dec_ref(v_toPreserve_1136_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___redArg(lean_object* v_e_1146_, lean_object* v___y_1147_){
_start:
{
uint8_t v___x_1149_; 
v___x_1149_ = l_Lean_Expr_hasMVar(v_e_1146_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; 
v___x_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1150_, 0, v_e_1146_);
return v___x_1150_;
}
else
{
lean_object* v___x_1151_; lean_object* v_mctx_1152_; lean_object* v___x_1153_; lean_object* v_fst_1154_; lean_object* v_snd_1155_; lean_object* v___x_1156_; lean_object* v_cache_1157_; lean_object* v_zetaDeltaFVarIds_1158_; lean_object* v_postponed_1159_; lean_object* v_diag_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1169_; 
v___x_1151_ = lean_st_ref_get(v___y_1147_);
v_mctx_1152_ = lean_ctor_get(v___x_1151_, 0);
lean_inc_ref(v_mctx_1152_);
lean_dec(v___x_1151_);
v___x_1153_ = l_Lean_instantiateMVarsCore(v_mctx_1152_, v_e_1146_);
v_fst_1154_ = lean_ctor_get(v___x_1153_, 0);
lean_inc(v_fst_1154_);
v_snd_1155_ = lean_ctor_get(v___x_1153_, 1);
lean_inc(v_snd_1155_);
lean_dec_ref(v___x_1153_);
v___x_1156_ = lean_st_ref_take(v___y_1147_);
v_cache_1157_ = lean_ctor_get(v___x_1156_, 1);
v_zetaDeltaFVarIds_1158_ = lean_ctor_get(v___x_1156_, 2);
v_postponed_1159_ = lean_ctor_get(v___x_1156_, 3);
v_diag_1160_ = lean_ctor_get(v___x_1156_, 4);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1169_ == 0)
{
lean_object* v_unused_1170_; 
v_unused_1170_ = lean_ctor_get(v___x_1156_, 0);
lean_dec(v_unused_1170_);
v___x_1162_ = v___x_1156_;
v_isShared_1163_ = v_isSharedCheck_1169_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_diag_1160_);
lean_inc(v_postponed_1159_);
lean_inc(v_zetaDeltaFVarIds_1158_);
lean_inc(v_cache_1157_);
lean_dec(v___x_1156_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1169_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1165_; 
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 0, v_snd_1155_);
v___x_1165_ = v___x_1162_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_snd_1155_);
lean_ctor_set(v_reuseFailAlloc_1168_, 1, v_cache_1157_);
lean_ctor_set(v_reuseFailAlloc_1168_, 2, v_zetaDeltaFVarIds_1158_);
lean_ctor_set(v_reuseFailAlloc_1168_, 3, v_postponed_1159_);
lean_ctor_set(v_reuseFailAlloc_1168_, 4, v_diag_1160_);
v___x_1165_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = lean_st_ref_set(v___y_1147_, v___x_1165_);
v___x_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1167_, 0, v_fst_1154_);
return v___x_1167_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___redArg___boxed(lean_object* v_e_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___redArg(v_e_1171_, v___y_1172_);
lean_dec(v___y_1172_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1(lean_object* v_e_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v___x_1181_; 
v___x_1181_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___redArg(v_e_1175_, v___y_1177_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___boxed(lean_object* v_e_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1(v_e_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___redArg(lean_object* v_mvarId_1189_, lean_object* v_x_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1189_, v_x_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1204_; 
v_a_1197_ = lean_ctor_get(v___x_1196_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1199_ = v___x_1196_;
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_dec(v___x_1196_);
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
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1212_; 
v_a_1205_ = lean_ctor_get(v___x_1196_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1207_ = v___x_1196_;
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_a_1205_);
lean_dec(v___x_1196_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1210_; 
if (v_isShared_1208_ == 0)
{
v___x_1210_ = v___x_1207_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_a_1205_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___redArg___boxed(lean_object* v_mvarId_1213_, lean_object* v_x_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___redArg(v_mvarId_1213_, v_x_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4(lean_object* v_00_u03b1_1221_, lean_object* v_mvarId_1222_, lean_object* v_x_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___redArg(v_mvarId_1222_, v_x_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___boxed(lean_object* v_00_u03b1_1230_, lean_object* v_mvarId_1231_, lean_object* v_x_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4(v_00_u03b1_1230_, v_mvarId_1231_, v_x_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__3(lean_object* v_a_1239_, lean_object* v_as_1240_, size_t v_i_1241_, size_t v_stop_1242_, lean_object* v_b_1243_){
_start:
{
lean_object* v___y_1245_; uint8_t v___x_1249_; 
v___x_1249_ = lean_usize_dec_eq(v_i_1241_, v_stop_1242_);
if (v___x_1249_ == 0)
{
lean_object* v___x_1250_; lean_object* v_fvar_1251_; lean_object* v___x_1252_; uint8_t v___x_1253_; 
v___x_1250_ = lean_array_uget_borrowed(v_as_1240_, v_i_1241_);
v_fvar_1251_ = lean_ctor_get(v___x_1250_, 1);
v___x_1252_ = l_Lean_Expr_fvarId_x21(v_fvar_1251_);
v___x_1253_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_1252_, v_a_1239_);
lean_dec(v___x_1252_);
if (v___x_1253_ == 0)
{
v___y_1245_ = v_b_1243_;
goto v___jp_1244_;
}
else
{
lean_object* v___x_1254_; 
lean_inc(v___x_1250_);
v___x_1254_ = lean_array_push(v_b_1243_, v___x_1250_);
v___y_1245_ = v___x_1254_;
goto v___jp_1244_;
}
}
else
{
return v_b_1243_;
}
v___jp_1244_:
{
size_t v___x_1246_; size_t v___x_1247_; 
v___x_1246_ = ((size_t)1ULL);
v___x_1247_ = lean_usize_add(v_i_1241_, v___x_1246_);
v_i_1241_ = v___x_1247_;
v_b_1243_ = v___y_1245_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__3___boxed(lean_object* v_a_1255_, lean_object* v_as_1256_, lean_object* v_i_1257_, lean_object* v_stop_1258_, lean_object* v_b_1259_){
_start:
{
size_t v_i_boxed_1260_; size_t v_stop_boxed_1261_; lean_object* v_res_1262_; 
v_i_boxed_1260_ = lean_unbox_usize(v_i_1257_);
lean_dec(v_i_1257_);
v_stop_boxed_1261_ = lean_unbox_usize(v_stop_1258_);
lean_dec(v_stop_1258_);
v_res_1262_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__3(v_a_1255_, v_as_1256_, v_i_boxed_1260_, v_stop_boxed_1261_, v_b_1259_);
lean_dec_ref(v_as_1256_);
lean_dec(v_a_1255_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12_spec__13___redArg(lean_object* v_x_1263_, lean_object* v_x_1264_, lean_object* v_x_1265_, lean_object* v_x_1266_){
_start:
{
lean_object* v_ks_1267_; lean_object* v_vs_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1292_; 
v_ks_1267_ = lean_ctor_get(v_x_1263_, 0);
v_vs_1268_ = lean_ctor_get(v_x_1263_, 1);
v_isSharedCheck_1292_ = !lean_is_exclusive(v_x_1263_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1270_ = v_x_1263_;
v_isShared_1271_ = v_isSharedCheck_1292_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_vs_1268_);
lean_inc(v_ks_1267_);
lean_dec(v_x_1263_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1292_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1272_; uint8_t v___x_1273_; 
v___x_1272_ = lean_array_get_size(v_ks_1267_);
v___x_1273_ = lean_nat_dec_lt(v_x_1264_, v___x_1272_);
if (v___x_1273_ == 0)
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1277_; 
lean_dec(v_x_1264_);
v___x_1274_ = lean_array_push(v_ks_1267_, v_x_1265_);
v___x_1275_ = lean_array_push(v_vs_1268_, v_x_1266_);
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 1, v___x_1275_);
lean_ctor_set(v___x_1270_, 0, v___x_1274_);
v___x_1277_ = v___x_1270_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v___x_1274_);
lean_ctor_set(v_reuseFailAlloc_1278_, 1, v___x_1275_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
else
{
lean_object* v_k_x27_1279_; uint8_t v___x_1280_; 
v_k_x27_1279_ = lean_array_fget_borrowed(v_ks_1267_, v_x_1264_);
v___x_1280_ = l_Lean_instBEqMVarId_beq(v_x_1265_, v_k_x27_1279_);
if (v___x_1280_ == 0)
{
lean_object* v___x_1282_; 
if (v_isShared_1271_ == 0)
{
v___x_1282_ = v___x_1270_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_ks_1267_);
lean_ctor_set(v_reuseFailAlloc_1286_, 1, v_vs_1268_);
v___x_1282_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1283_ = lean_unsigned_to_nat(1u);
v___x_1284_ = lean_nat_add(v_x_1264_, v___x_1283_);
lean_dec(v_x_1264_);
v_x_1263_ = v___x_1282_;
v_x_1264_ = v___x_1284_;
goto _start;
}
}
else
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1290_; 
v___x_1287_ = lean_array_fset(v_ks_1267_, v_x_1264_, v_x_1265_);
v___x_1288_ = lean_array_fset(v_vs_1268_, v_x_1264_, v_x_1266_);
lean_dec(v_x_1264_);
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 1, v___x_1288_);
lean_ctor_set(v___x_1270_, 0, v___x_1287_);
v___x_1290_ = v___x_1270_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1287_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v___x_1288_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12___redArg(lean_object* v_n_1293_, lean_object* v_k_1294_, lean_object* v_v_1295_){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1296_ = lean_unsigned_to_nat(0u);
v___x_1297_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12_spec__13___redArg(v_n_1293_, v___x_1296_, v_k_1294_, v_v_1295_);
return v___x_1297_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__0(void){
_start:
{
size_t v___x_1298_; size_t v___x_1299_; size_t v___x_1300_; 
v___x_1298_ = ((size_t)5ULL);
v___x_1299_ = ((size_t)1ULL);
v___x_1300_ = lean_usize_shift_left(v___x_1299_, v___x_1298_);
return v___x_1300_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__1(void){
_start:
{
size_t v___x_1301_; size_t v___x_1302_; size_t v___x_1303_; 
v___x_1301_ = ((size_t)1ULL);
v___x_1302_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__0);
v___x_1303_ = lean_usize_sub(v___x_1302_, v___x_1301_);
return v___x_1303_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_1304_; 
v___x_1304_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg(lean_object* v_x_1305_, size_t v_x_1306_, size_t v_x_1307_, lean_object* v_x_1308_, lean_object* v_x_1309_){
_start:
{
if (lean_obj_tag(v_x_1305_) == 0)
{
lean_object* v_es_1310_; size_t v___x_1311_; size_t v___x_1312_; size_t v___x_1313_; size_t v___x_1314_; lean_object* v_j_1315_; lean_object* v___x_1316_; uint8_t v___x_1317_; 
v_es_1310_ = lean_ctor_get(v_x_1305_, 0);
v___x_1311_ = ((size_t)5ULL);
v___x_1312_ = ((size_t)1ULL);
v___x_1313_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__1);
v___x_1314_ = lean_usize_land(v_x_1306_, v___x_1313_);
v_j_1315_ = lean_usize_to_nat(v___x_1314_);
v___x_1316_ = lean_array_get_size(v_es_1310_);
v___x_1317_ = lean_nat_dec_lt(v_j_1315_, v___x_1316_);
if (v___x_1317_ == 0)
{
lean_dec(v_j_1315_);
lean_dec(v_x_1309_);
lean_dec(v_x_1308_);
return v_x_1305_;
}
else
{
lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1354_; 
lean_inc_ref(v_es_1310_);
v_isSharedCheck_1354_ = !lean_is_exclusive(v_x_1305_);
if (v_isSharedCheck_1354_ == 0)
{
lean_object* v_unused_1355_; 
v_unused_1355_ = lean_ctor_get(v_x_1305_, 0);
lean_dec(v_unused_1355_);
v___x_1319_ = v_x_1305_;
v_isShared_1320_ = v_isSharedCheck_1354_;
goto v_resetjp_1318_;
}
else
{
lean_dec(v_x_1305_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1354_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v_v_1321_; lean_object* v___x_1322_; lean_object* v_xs_x27_1323_; lean_object* v___y_1325_; 
v_v_1321_ = lean_array_fget(v_es_1310_, v_j_1315_);
v___x_1322_ = lean_box(0);
v_xs_x27_1323_ = lean_array_fset(v_es_1310_, v_j_1315_, v___x_1322_);
switch(lean_obj_tag(v_v_1321_))
{
case 0:
{
lean_object* v_key_1330_; lean_object* v_val_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1341_; 
v_key_1330_ = lean_ctor_get(v_v_1321_, 0);
v_val_1331_ = lean_ctor_get(v_v_1321_, 1);
v_isSharedCheck_1341_ = !lean_is_exclusive(v_v_1321_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1333_ = v_v_1321_;
v_isShared_1334_ = v_isSharedCheck_1341_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_val_1331_);
lean_inc(v_key_1330_);
lean_dec(v_v_1321_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1341_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
uint8_t v___x_1335_; 
v___x_1335_ = l_Lean_instBEqMVarId_beq(v_x_1308_, v_key_1330_);
if (v___x_1335_ == 0)
{
lean_object* v___x_1336_; lean_object* v___x_1337_; 
lean_del_object(v___x_1333_);
v___x_1336_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1330_, v_val_1331_, v_x_1308_, v_x_1309_);
v___x_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1336_);
v___y_1325_ = v___x_1337_;
goto v___jp_1324_;
}
else
{
lean_object* v___x_1339_; 
lean_dec(v_val_1331_);
lean_dec(v_key_1330_);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 1, v_x_1309_);
lean_ctor_set(v___x_1333_, 0, v_x_1308_);
v___x_1339_ = v___x_1333_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_x_1308_);
lean_ctor_set(v_reuseFailAlloc_1340_, 1, v_x_1309_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
v___y_1325_ = v___x_1339_;
goto v___jp_1324_;
}
}
}
}
case 1:
{
lean_object* v_node_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1352_; 
v_node_1342_ = lean_ctor_get(v_v_1321_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v_v_1321_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1344_ = v_v_1321_;
v_isShared_1345_ = v_isSharedCheck_1352_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_node_1342_);
lean_dec(v_v_1321_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1352_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
size_t v___x_1346_; size_t v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1350_; 
v___x_1346_ = lean_usize_shift_right(v_x_1306_, v___x_1311_);
v___x_1347_ = lean_usize_add(v_x_1307_, v___x_1312_);
v___x_1348_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg(v_node_1342_, v___x_1346_, v___x_1347_, v_x_1308_, v_x_1309_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 0, v___x_1348_);
v___x_1350_ = v___x_1344_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v___x_1348_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
v___y_1325_ = v___x_1350_;
goto v___jp_1324_;
}
}
}
default: 
{
lean_object* v___x_1353_; 
v___x_1353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1353_, 0, v_x_1308_);
lean_ctor_set(v___x_1353_, 1, v_x_1309_);
v___y_1325_ = v___x_1353_;
goto v___jp_1324_;
}
}
v___jp_1324_:
{
lean_object* v___x_1326_; lean_object* v___x_1328_; 
v___x_1326_ = lean_array_fset(v_xs_x27_1323_, v_j_1315_, v___y_1325_);
lean_dec(v_j_1315_);
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 0, v___x_1326_);
v___x_1328_ = v___x_1319_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v___x_1326_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
}
}
else
{
lean_object* v_ks_1356_; lean_object* v_vs_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1377_; 
v_ks_1356_ = lean_ctor_get(v_x_1305_, 0);
v_vs_1357_ = lean_ctor_get(v_x_1305_, 1);
v_isSharedCheck_1377_ = !lean_is_exclusive(v_x_1305_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1359_ = v_x_1305_;
v_isShared_1360_ = v_isSharedCheck_1377_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_vs_1357_);
lean_inc(v_ks_1356_);
lean_dec(v_x_1305_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1377_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_ks_1356_);
lean_ctor_set(v_reuseFailAlloc_1376_, 1, v_vs_1357_);
v___x_1362_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
lean_object* v_newNode_1363_; uint8_t v___y_1365_; size_t v___x_1371_; uint8_t v___x_1372_; 
v_newNode_1363_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12___redArg(v___x_1362_, v_x_1308_, v_x_1309_);
v___x_1371_ = ((size_t)7ULL);
v___x_1372_ = lean_usize_dec_le(v___x_1371_, v_x_1307_);
if (v___x_1372_ == 0)
{
lean_object* v___x_1373_; lean_object* v___x_1374_; uint8_t v___x_1375_; 
v___x_1373_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1363_);
v___x_1374_ = lean_unsigned_to_nat(4u);
v___x_1375_ = lean_nat_dec_lt(v___x_1373_, v___x_1374_);
lean_dec(v___x_1373_);
v___y_1365_ = v___x_1375_;
goto v___jp_1364_;
}
else
{
v___y_1365_ = v___x_1372_;
goto v___jp_1364_;
}
v___jp_1364_:
{
if (v___y_1365_ == 0)
{
lean_object* v_ks_1366_; lean_object* v_vs_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; 
v_ks_1366_ = lean_ctor_get(v_newNode_1363_, 0);
lean_inc_ref(v_ks_1366_);
v_vs_1367_ = lean_ctor_get(v_newNode_1363_, 1);
lean_inc_ref(v_vs_1367_);
lean_dec_ref(v_newNode_1363_);
v___x_1368_ = lean_unsigned_to_nat(0u);
v___x_1369_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__2);
v___x_1370_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___redArg(v_x_1307_, v_ks_1366_, v_vs_1367_, v___x_1368_, v___x_1369_);
lean_dec_ref(v_vs_1367_);
lean_dec_ref(v_ks_1366_);
return v___x_1370_;
}
else
{
return v_newNode_1363_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___redArg(size_t v_depth_1378_, lean_object* v_keys_1379_, lean_object* v_vals_1380_, lean_object* v_i_1381_, lean_object* v_entries_1382_){
_start:
{
lean_object* v___x_1383_; uint8_t v___x_1384_; 
v___x_1383_ = lean_array_get_size(v_keys_1379_);
v___x_1384_ = lean_nat_dec_lt(v_i_1381_, v___x_1383_);
if (v___x_1384_ == 0)
{
lean_dec(v_i_1381_);
return v_entries_1382_;
}
else
{
lean_object* v_k_1385_; lean_object* v_v_1386_; uint64_t v___x_1387_; size_t v_h_1388_; size_t v___x_1389_; lean_object* v___x_1390_; size_t v___x_1391_; size_t v___x_1392_; size_t v___x_1393_; size_t v_h_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v_k_1385_ = lean_array_fget_borrowed(v_keys_1379_, v_i_1381_);
v_v_1386_ = lean_array_fget_borrowed(v_vals_1380_, v_i_1381_);
v___x_1387_ = l_Lean_instHashableMVarId_hash(v_k_1385_);
v_h_1388_ = lean_uint64_to_usize(v___x_1387_);
v___x_1389_ = ((size_t)5ULL);
v___x_1390_ = lean_unsigned_to_nat(1u);
v___x_1391_ = ((size_t)1ULL);
v___x_1392_ = lean_usize_sub(v_depth_1378_, v___x_1391_);
v___x_1393_ = lean_usize_mul(v___x_1389_, v___x_1392_);
v_h_1394_ = lean_usize_shift_right(v_h_1388_, v___x_1393_);
v___x_1395_ = lean_nat_add(v_i_1381_, v___x_1390_);
lean_dec(v_i_1381_);
lean_inc(v_v_1386_);
lean_inc(v_k_1385_);
v___x_1396_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg(v_entries_1382_, v_h_1394_, v_depth_1378_, v_k_1385_, v_v_1386_);
v_i_1381_ = v___x_1395_;
v_entries_1382_ = v___x_1396_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___redArg___boxed(lean_object* v_depth_1398_, lean_object* v_keys_1399_, lean_object* v_vals_1400_, lean_object* v_i_1401_, lean_object* v_entries_1402_){
_start:
{
size_t v_depth_boxed_1403_; lean_object* v_res_1404_; 
v_depth_boxed_1403_ = lean_unbox_usize(v_depth_1398_);
lean_dec(v_depth_1398_);
v_res_1404_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___redArg(v_depth_boxed_1403_, v_keys_1399_, v_vals_1400_, v_i_1401_, v_entries_1402_);
lean_dec_ref(v_vals_1400_);
lean_dec_ref(v_keys_1399_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___boxed(lean_object* v_x_1405_, lean_object* v_x_1406_, lean_object* v_x_1407_, lean_object* v_x_1408_, lean_object* v_x_1409_){
_start:
{
size_t v_x_7488__boxed_1410_; size_t v_x_7489__boxed_1411_; lean_object* v_res_1412_; 
v_x_7488__boxed_1410_ = lean_unbox_usize(v_x_1406_);
lean_dec(v_x_1406_);
v_x_7489__boxed_1411_ = lean_unbox_usize(v_x_1407_);
lean_dec(v_x_1407_);
v_res_1412_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg(v_x_1405_, v_x_7488__boxed_1410_, v_x_7489__boxed_1411_, v_x_1408_, v_x_1409_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4___redArg(lean_object* v_x_1413_, lean_object* v_x_1414_, lean_object* v_x_1415_){
_start:
{
uint64_t v___x_1416_; size_t v___x_1417_; size_t v___x_1418_; lean_object* v___x_1419_; 
v___x_1416_ = l_Lean_instHashableMVarId_hash(v_x_1414_);
v___x_1417_ = lean_uint64_to_usize(v___x_1416_);
v___x_1418_ = ((size_t)1ULL);
v___x_1419_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg(v_x_1413_, v___x_1417_, v___x_1418_, v_x_1414_, v_x_1415_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___redArg(lean_object* v_mvarId_1420_, lean_object* v_val_1421_, lean_object* v___y_1422_){
_start:
{
lean_object* v___x_1424_; lean_object* v_mctx_1425_; lean_object* v_cache_1426_; lean_object* v_zetaDeltaFVarIds_1427_; lean_object* v_postponed_1428_; lean_object* v_diag_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1457_; 
v___x_1424_ = lean_st_ref_take(v___y_1422_);
v_mctx_1425_ = lean_ctor_get(v___x_1424_, 0);
v_cache_1426_ = lean_ctor_get(v___x_1424_, 1);
v_zetaDeltaFVarIds_1427_ = lean_ctor_get(v___x_1424_, 2);
v_postponed_1428_ = lean_ctor_get(v___x_1424_, 3);
v_diag_1429_ = lean_ctor_get(v___x_1424_, 4);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1431_ = v___x_1424_;
v_isShared_1432_ = v_isSharedCheck_1457_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_diag_1429_);
lean_inc(v_postponed_1428_);
lean_inc(v_zetaDeltaFVarIds_1427_);
lean_inc(v_cache_1426_);
lean_inc(v_mctx_1425_);
lean_dec(v___x_1424_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1457_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v_depth_1433_; lean_object* v_levelAssignDepth_1434_; lean_object* v_lmvarCounter_1435_; lean_object* v_mvarCounter_1436_; lean_object* v_lDecls_1437_; lean_object* v_decls_1438_; lean_object* v_userNames_1439_; lean_object* v_lAssignment_1440_; lean_object* v_eAssignment_1441_; lean_object* v_dAssignment_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1456_; 
v_depth_1433_ = lean_ctor_get(v_mctx_1425_, 0);
v_levelAssignDepth_1434_ = lean_ctor_get(v_mctx_1425_, 1);
v_lmvarCounter_1435_ = lean_ctor_get(v_mctx_1425_, 2);
v_mvarCounter_1436_ = lean_ctor_get(v_mctx_1425_, 3);
v_lDecls_1437_ = lean_ctor_get(v_mctx_1425_, 4);
v_decls_1438_ = lean_ctor_get(v_mctx_1425_, 5);
v_userNames_1439_ = lean_ctor_get(v_mctx_1425_, 6);
v_lAssignment_1440_ = lean_ctor_get(v_mctx_1425_, 7);
v_eAssignment_1441_ = lean_ctor_get(v_mctx_1425_, 8);
v_dAssignment_1442_ = lean_ctor_get(v_mctx_1425_, 9);
v_isSharedCheck_1456_ = !lean_is_exclusive(v_mctx_1425_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1444_ = v_mctx_1425_;
v_isShared_1445_ = v_isSharedCheck_1456_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_dAssignment_1442_);
lean_inc(v_eAssignment_1441_);
lean_inc(v_lAssignment_1440_);
lean_inc(v_userNames_1439_);
lean_inc(v_decls_1438_);
lean_inc(v_lDecls_1437_);
lean_inc(v_mvarCounter_1436_);
lean_inc(v_lmvarCounter_1435_);
lean_inc(v_levelAssignDepth_1434_);
lean_inc(v_depth_1433_);
lean_dec(v_mctx_1425_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1456_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1446_; lean_object* v___x_1448_; 
v___x_1446_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4___redArg(v_eAssignment_1441_, v_mvarId_1420_, v_val_1421_);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 8, v___x_1446_);
v___x_1448_ = v___x_1444_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_depth_1433_);
lean_ctor_set(v_reuseFailAlloc_1455_, 1, v_levelAssignDepth_1434_);
lean_ctor_set(v_reuseFailAlloc_1455_, 2, v_lmvarCounter_1435_);
lean_ctor_set(v_reuseFailAlloc_1455_, 3, v_mvarCounter_1436_);
lean_ctor_set(v_reuseFailAlloc_1455_, 4, v_lDecls_1437_);
lean_ctor_set(v_reuseFailAlloc_1455_, 5, v_decls_1438_);
lean_ctor_set(v_reuseFailAlloc_1455_, 6, v_userNames_1439_);
lean_ctor_set(v_reuseFailAlloc_1455_, 7, v_lAssignment_1440_);
lean_ctor_set(v_reuseFailAlloc_1455_, 8, v___x_1446_);
lean_ctor_set(v_reuseFailAlloc_1455_, 9, v_dAssignment_1442_);
v___x_1448_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
lean_object* v___x_1450_; 
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 0, v___x_1448_);
v___x_1450_ = v___x_1431_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1448_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v_cache_1426_);
lean_ctor_set(v_reuseFailAlloc_1454_, 2, v_zetaDeltaFVarIds_1427_);
lean_ctor_set(v_reuseFailAlloc_1454_, 3, v_postponed_1428_);
lean_ctor_set(v_reuseFailAlloc_1454_, 4, v_diag_1429_);
v___x_1450_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1451_ = lean_st_ref_set(v___y_1422_, v___x_1450_);
v___x_1452_ = lean_box(0);
v___x_1453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1452_);
return v___x_1453_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___redArg___boxed(lean_object* v_mvarId_1458_, lean_object* v_val_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___redArg(v_mvarId_1458_, v_val_1459_, v___y_1460_);
lean_dec(v___y_1460_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___redArg(lean_object* v_a_1463_, lean_object* v_as_1464_, size_t v_sz_1465_, size_t v_i_1466_, lean_object* v_b_1467_){
_start:
{
uint8_t v___x_1469_; 
v___x_1469_ = lean_usize_dec_lt(v_i_1466_, v_sz_1465_);
if (v___x_1469_ == 0)
{
lean_object* v___x_1470_; 
v___x_1470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1470_, 0, v_b_1467_);
return v___x_1470_;
}
else
{
lean_object* v_snd_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1489_; 
v_snd_1471_ = lean_ctor_get(v_b_1467_, 1);
v_isSharedCheck_1489_ = !lean_is_exclusive(v_b_1467_);
if (v_isSharedCheck_1489_ == 0)
{
lean_object* v_unused_1490_; 
v_unused_1490_ = lean_ctor_get(v_b_1467_, 0);
lean_dec(v_unused_1490_);
v___x_1473_ = v_b_1467_;
v_isShared_1474_ = v_isSharedCheck_1489_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_snd_1471_);
lean_dec(v_b_1467_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1489_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1475_; lean_object* v_a_1477_; lean_object* v_a_1484_; 
v___x_1475_ = lean_box(0);
v_a_1484_ = lean_array_uget_borrowed(v_as_1464_, v_i_1466_);
if (lean_obj_tag(v_a_1484_) == 0)
{
v_a_1477_ = v_snd_1471_;
goto v___jp_1476_;
}
else
{
lean_object* v_val_1485_; lean_object* v___x_1486_; uint8_t v___x_1487_; 
v_val_1485_ = lean_ctor_get(v_a_1484_, 0);
v___x_1486_ = l_Lean_LocalDecl_fvarId(v_val_1485_);
v___x_1487_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_1486_, v_a_1463_);
if (v___x_1487_ == 0)
{
lean_object* v___x_1488_; 
v___x_1488_ = lean_local_ctx_erase(v_snd_1471_, v___x_1486_);
v_a_1477_ = v___x_1488_;
goto v___jp_1476_;
}
else
{
lean_dec(v___x_1486_);
v_a_1477_ = v_snd_1471_;
goto v___jp_1476_;
}
}
v___jp_1476_:
{
lean_object* v___x_1479_; 
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 1, v_a_1477_);
lean_ctor_set(v___x_1473_, 0, v___x_1475_);
v___x_1479_ = v___x_1473_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1475_);
lean_ctor_set(v_reuseFailAlloc_1483_, 1, v_a_1477_);
v___x_1479_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
size_t v___x_1480_; size_t v___x_1481_; 
v___x_1480_ = ((size_t)1ULL);
v___x_1481_ = lean_usize_add(v_i_1466_, v___x_1480_);
v_i_1466_ = v___x_1481_;
v_b_1467_ = v___x_1479_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___redArg___boxed(lean_object* v_a_1491_, lean_object* v_as_1492_, lean_object* v_sz_1493_, lean_object* v_i_1494_, lean_object* v_b_1495_, lean_object* v___y_1496_){
_start:
{
size_t v_sz_boxed_1497_; size_t v_i_boxed_1498_; lean_object* v_res_1499_; 
v_sz_boxed_1497_ = lean_unbox_usize(v_sz_1493_);
lean_dec(v_sz_1493_);
v_i_boxed_1498_ = lean_unbox_usize(v_i_1494_);
lean_dec(v_i_1494_);
v_res_1499_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___redArg(v_a_1491_, v_as_1492_, v_sz_boxed_1497_, v_i_boxed_1498_, v_b_1495_);
lean_dec_ref(v_as_1492_);
lean_dec(v_a_1491_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4(lean_object* v_a_1500_, lean_object* v_as_1501_, size_t v_sz_1502_, size_t v_i_1503_, lean_object* v_b_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
uint8_t v___x_1510_; 
v___x_1510_ = lean_usize_dec_lt(v_i_1503_, v_sz_1502_);
if (v___x_1510_ == 0)
{
lean_object* v___x_1511_; 
v___x_1511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1511_, 0, v_b_1504_);
return v___x_1511_;
}
else
{
lean_object* v_snd_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1530_; 
v_snd_1512_ = lean_ctor_get(v_b_1504_, 1);
v_isSharedCheck_1530_ = !lean_is_exclusive(v_b_1504_);
if (v_isSharedCheck_1530_ == 0)
{
lean_object* v_unused_1531_; 
v_unused_1531_ = lean_ctor_get(v_b_1504_, 0);
lean_dec(v_unused_1531_);
v___x_1514_ = v_b_1504_;
v_isShared_1515_ = v_isSharedCheck_1530_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_snd_1512_);
lean_dec(v_b_1504_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1530_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1516_; lean_object* v_a_1518_; lean_object* v_a_1525_; 
v___x_1516_ = lean_box(0);
v_a_1525_ = lean_array_uget_borrowed(v_as_1501_, v_i_1503_);
if (lean_obj_tag(v_a_1525_) == 0)
{
v_a_1518_ = v_snd_1512_;
goto v___jp_1517_;
}
else
{
lean_object* v_val_1526_; lean_object* v___x_1527_; uint8_t v___x_1528_; 
v_val_1526_ = lean_ctor_get(v_a_1525_, 0);
v___x_1527_ = l_Lean_LocalDecl_fvarId(v_val_1526_);
v___x_1528_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_1527_, v_a_1500_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; 
v___x_1529_ = lean_local_ctx_erase(v_snd_1512_, v___x_1527_);
v_a_1518_ = v___x_1529_;
goto v___jp_1517_;
}
else
{
lean_dec(v___x_1527_);
v_a_1518_ = v_snd_1512_;
goto v___jp_1517_;
}
}
v___jp_1517_:
{
lean_object* v___x_1520_; 
if (v_isShared_1515_ == 0)
{
lean_ctor_set(v___x_1514_, 1, v_a_1518_);
lean_ctor_set(v___x_1514_, 0, v___x_1516_);
v___x_1520_ = v___x_1514_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1516_);
lean_ctor_set(v_reuseFailAlloc_1524_, 1, v_a_1518_);
v___x_1520_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
size_t v___x_1521_; size_t v___x_1522_; lean_object* v___x_1523_; 
v___x_1521_ = ((size_t)1ULL);
v___x_1522_ = lean_usize_add(v_i_1503_, v___x_1521_);
v___x_1523_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___redArg(v_a_1500_, v_as_1501_, v_sz_1502_, v___x_1522_, v___x_1520_);
return v___x_1523_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4___boxed(lean_object* v_a_1532_, lean_object* v_as_1533_, lean_object* v_sz_1534_, lean_object* v_i_1535_, lean_object* v_b_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
size_t v_sz_boxed_1542_; size_t v_i_boxed_1543_; lean_object* v_res_1544_; 
v_sz_boxed_1542_ = lean_unbox_usize(v_sz_1534_);
lean_dec(v_sz_1534_);
v_i_boxed_1543_ = lean_unbox_usize(v_i_1535_);
lean_dec(v_i_1535_);
v_res_1544_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4(v_a_1532_, v_as_1533_, v_sz_boxed_1542_, v_i_boxed_1543_, v_b_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec_ref(v_as_1533_);
lean_dec(v_a_1532_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0(lean_object* v_init_1545_, lean_object* v_a_1546_, lean_object* v_n_1547_, lean_object* v_b_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_){
_start:
{
if (lean_obj_tag(v_n_1547_) == 0)
{
lean_object* v_cs_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1588_; 
v_cs_1554_ = lean_ctor_get(v_n_1547_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v_n_1547_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1556_ = v_n_1547_;
v_isShared_1557_ = v_isSharedCheck_1588_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_cs_1554_);
lean_dec(v_n_1547_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1588_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; size_t v_sz_1560_; size_t v___x_1561_; lean_object* v___x_1562_; 
v___x_1558_ = lean_box(0);
v___x_1559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1558_);
lean_ctor_set(v___x_1559_, 1, v_b_1548_);
v_sz_1560_ = lean_array_size(v_cs_1554_);
v___x_1561_ = ((size_t)0ULL);
v___x_1562_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__3(v_init_1545_, v_a_1546_, v_cs_1554_, v_sz_1560_, v___x_1561_, v___x_1559_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
lean_dec_ref(v_cs_1554_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1579_; 
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1565_ = v___x_1562_;
v_isShared_1566_ = v_isSharedCheck_1579_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1562_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1579_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v_fst_1567_; 
v_fst_1567_ = lean_ctor_get(v_a_1563_, 0);
if (lean_obj_tag(v_fst_1567_) == 0)
{
lean_object* v_snd_1568_; lean_object* v___x_1570_; 
v_snd_1568_ = lean_ctor_get(v_a_1563_, 1);
lean_inc(v_snd_1568_);
lean_dec(v_a_1563_);
if (v_isShared_1557_ == 0)
{
lean_ctor_set_tag(v___x_1556_, 1);
lean_ctor_set(v___x_1556_, 0, v_snd_1568_);
v___x_1570_ = v___x_1556_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_snd_1568_);
v___x_1570_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
lean_object* v___x_1572_; 
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 0, v___x_1570_);
v___x_1572_ = v___x_1565_;
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
}
else
{
lean_object* v_val_1575_; lean_object* v___x_1577_; 
lean_inc_ref(v_fst_1567_);
lean_dec(v_a_1563_);
lean_del_object(v___x_1556_);
v_val_1575_ = lean_ctor_get(v_fst_1567_, 0);
lean_inc(v_val_1575_);
lean_dec_ref(v_fst_1567_);
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 0, v_val_1575_);
v___x_1577_ = v___x_1565_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_val_1575_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
else
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1587_; 
lean_del_object(v___x_1556_);
v_a_1580_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1582_ = v___x_1562_;
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1562_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1585_; 
if (v_isShared_1583_ == 0)
{
v___x_1585_ = v___x_1582_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_a_1580_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
}
}
else
{
lean_object* v_vs_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1623_; 
v_vs_1589_ = lean_ctor_get(v_n_1547_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v_n_1547_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1591_ = v_n_1547_;
v_isShared_1592_ = v_isSharedCheck_1623_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_vs_1589_);
lean_dec(v_n_1547_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1623_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; size_t v_sz_1595_; size_t v___x_1596_; lean_object* v___x_1597_; 
v___x_1593_ = lean_box(0);
v___x_1594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1593_);
lean_ctor_set(v___x_1594_, 1, v_b_1548_);
v_sz_1595_ = lean_array_size(v_vs_1589_);
v___x_1596_ = ((size_t)0ULL);
v___x_1597_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4(v_a_1546_, v_vs_1589_, v_sz_1595_, v___x_1596_, v___x_1594_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
lean_dec_ref(v_vs_1589_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1614_; 
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1600_ = v___x_1597_;
v_isShared_1601_ = v_isSharedCheck_1614_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1597_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1614_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v_fst_1602_; 
v_fst_1602_ = lean_ctor_get(v_a_1598_, 0);
if (lean_obj_tag(v_fst_1602_) == 0)
{
lean_object* v_snd_1603_; lean_object* v___x_1605_; 
v_snd_1603_ = lean_ctor_get(v_a_1598_, 1);
lean_inc(v_snd_1603_);
lean_dec(v_a_1598_);
if (v_isShared_1592_ == 0)
{
lean_ctor_set(v___x_1591_, 0, v_snd_1603_);
v___x_1605_ = v___x_1591_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_snd_1603_);
v___x_1605_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
lean_object* v___x_1607_; 
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 0, v___x_1605_);
v___x_1607_ = v___x_1600_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v___x_1605_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
else
{
lean_object* v_val_1610_; lean_object* v___x_1612_; 
lean_inc_ref(v_fst_1602_);
lean_dec(v_a_1598_);
lean_del_object(v___x_1591_);
v_val_1610_ = lean_ctor_get(v_fst_1602_, 0);
lean_inc(v_val_1610_);
lean_dec_ref(v_fst_1602_);
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 0, v_val_1610_);
v___x_1612_ = v___x_1600_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_val_1610_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
else
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1622_; 
lean_del_object(v___x_1591_);
v_a_1615_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1617_ = v___x_1597_;
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1597_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1620_; 
if (v_isShared_1618_ == 0)
{
v___x_1620_ = v___x_1617_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_a_1615_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__3(lean_object* v_init_1624_, lean_object* v_a_1625_, lean_object* v_as_1626_, size_t v_sz_1627_, size_t v_i_1628_, lean_object* v_b_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
uint8_t v___x_1635_; 
v___x_1635_ = lean_usize_dec_lt(v_i_1628_, v_sz_1627_);
if (v___x_1635_ == 0)
{
lean_object* v___x_1636_; 
v___x_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1636_, 0, v_b_1629_);
return v___x_1636_;
}
else
{
lean_object* v_snd_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1671_; 
v_snd_1637_ = lean_ctor_get(v_b_1629_, 1);
v_isSharedCheck_1671_ = !lean_is_exclusive(v_b_1629_);
if (v_isSharedCheck_1671_ == 0)
{
lean_object* v_unused_1672_; 
v_unused_1672_ = lean_ctor_get(v_b_1629_, 0);
lean_dec(v_unused_1672_);
v___x_1639_ = v_b_1629_;
v_isShared_1640_ = v_isSharedCheck_1671_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_snd_1637_);
lean_dec(v_b_1629_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1671_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v_a_1641_; lean_object* v___x_1642_; 
v_a_1641_ = lean_array_uget_borrowed(v_as_1626_, v_i_1628_);
lean_inc(v_snd_1637_);
lean_inc(v_a_1641_);
v___x_1642_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0(v_init_1624_, v_a_1625_, v_a_1641_, v_snd_1637_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1662_; 
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1645_ = v___x_1642_;
v_isShared_1646_ = v_isSharedCheck_1662_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1642_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1662_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
if (lean_obj_tag(v_a_1643_) == 0)
{
lean_object* v___x_1647_; lean_object* v___x_1649_; 
v___x_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1647_, 0, v_a_1643_);
if (v_isShared_1640_ == 0)
{
lean_ctor_set(v___x_1639_, 0, v___x_1647_);
v___x_1649_ = v___x_1639_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v___x_1647_);
lean_ctor_set(v_reuseFailAlloc_1653_, 1, v_snd_1637_);
v___x_1649_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
lean_object* v___x_1651_; 
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 0, v___x_1649_);
v___x_1651_ = v___x_1645_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v___x_1649_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
else
{
lean_object* v_a_1654_; lean_object* v___x_1655_; lean_object* v___x_1657_; 
lean_del_object(v___x_1645_);
lean_dec(v_snd_1637_);
v_a_1654_ = lean_ctor_get(v_a_1643_, 0);
lean_inc(v_a_1654_);
lean_dec_ref(v_a_1643_);
v___x_1655_ = lean_box(0);
if (v_isShared_1640_ == 0)
{
lean_ctor_set(v___x_1639_, 1, v_a_1654_);
lean_ctor_set(v___x_1639_, 0, v___x_1655_);
v___x_1657_ = v___x_1639_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v___x_1655_);
lean_ctor_set(v_reuseFailAlloc_1661_, 1, v_a_1654_);
v___x_1657_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
size_t v___x_1658_; size_t v___x_1659_; 
v___x_1658_ = ((size_t)1ULL);
v___x_1659_ = lean_usize_add(v_i_1628_, v___x_1658_);
v_i_1628_ = v___x_1659_;
v_b_1629_ = v___x_1657_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1670_; 
lean_del_object(v___x_1639_);
lean_dec(v_snd_1637_);
v_a_1663_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1665_ = v___x_1642_;
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_a_1663_);
lean_dec(v___x_1642_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1668_; 
if (v_isShared_1666_ == 0)
{
v___x_1668_ = v___x_1665_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_a_1663_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__3___boxed(lean_object* v_init_1673_, lean_object* v_a_1674_, lean_object* v_as_1675_, lean_object* v_sz_1676_, lean_object* v_i_1677_, lean_object* v_b_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
size_t v_sz_boxed_1684_; size_t v_i_boxed_1685_; lean_object* v_res_1686_; 
v_sz_boxed_1684_ = lean_unbox_usize(v_sz_1676_);
lean_dec(v_sz_1676_);
v_i_boxed_1685_ = lean_unbox_usize(v_i_1677_);
lean_dec(v_i_1677_);
v_res_1686_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__3(v_init_1673_, v_a_1674_, v_as_1675_, v_sz_boxed_1684_, v_i_boxed_1685_, v_b_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec_ref(v_as_1675_);
lean_dec(v_a_1674_);
lean_dec_ref(v_init_1673_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0___boxed(lean_object* v_init_1687_, lean_object* v_a_1688_, lean_object* v_n_1689_, lean_object* v_b_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0(v_init_1687_, v_a_1688_, v_n_1689_, v_b_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v_a_1688_);
lean_dec_ref(v_init_1687_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___redArg(lean_object* v_a_1697_, lean_object* v_as_1698_, size_t v_sz_1699_, size_t v_i_1700_, lean_object* v_b_1701_){
_start:
{
uint8_t v___x_1703_; 
v___x_1703_ = lean_usize_dec_lt(v_i_1700_, v_sz_1699_);
if (v___x_1703_ == 0)
{
lean_object* v___x_1704_; 
v___x_1704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1704_, 0, v_b_1701_);
return v___x_1704_;
}
else
{
lean_object* v_snd_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1723_; 
v_snd_1705_ = lean_ctor_get(v_b_1701_, 1);
v_isSharedCheck_1723_ = !lean_is_exclusive(v_b_1701_);
if (v_isSharedCheck_1723_ == 0)
{
lean_object* v_unused_1724_; 
v_unused_1724_ = lean_ctor_get(v_b_1701_, 0);
lean_dec(v_unused_1724_);
v___x_1707_ = v_b_1701_;
v_isShared_1708_ = v_isSharedCheck_1723_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_snd_1705_);
lean_dec(v_b_1701_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1723_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1709_; lean_object* v_a_1711_; lean_object* v_a_1718_; 
v___x_1709_ = lean_box(0);
v_a_1718_ = lean_array_uget_borrowed(v_as_1698_, v_i_1700_);
if (lean_obj_tag(v_a_1718_) == 0)
{
v_a_1711_ = v_snd_1705_;
goto v___jp_1710_;
}
else
{
lean_object* v_val_1719_; lean_object* v___x_1720_; uint8_t v___x_1721_; 
v_val_1719_ = lean_ctor_get(v_a_1718_, 0);
v___x_1720_ = l_Lean_LocalDecl_fvarId(v_val_1719_);
v___x_1721_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_1720_, v_a_1697_);
if (v___x_1721_ == 0)
{
lean_object* v___x_1722_; 
v___x_1722_ = lean_local_ctx_erase(v_snd_1705_, v___x_1720_);
v_a_1711_ = v___x_1722_;
goto v___jp_1710_;
}
else
{
lean_dec(v___x_1720_);
v_a_1711_ = v_snd_1705_;
goto v___jp_1710_;
}
}
v___jp_1710_:
{
lean_object* v___x_1713_; 
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 1, v_a_1711_);
lean_ctor_set(v___x_1707_, 0, v___x_1709_);
v___x_1713_ = v___x_1707_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v___x_1709_);
lean_ctor_set(v_reuseFailAlloc_1717_, 1, v_a_1711_);
v___x_1713_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
size_t v___x_1714_; size_t v___x_1715_; 
v___x_1714_ = ((size_t)1ULL);
v___x_1715_ = lean_usize_add(v_i_1700_, v___x_1714_);
v_i_1700_ = v___x_1715_;
v_b_1701_ = v___x_1713_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___redArg___boxed(lean_object* v_a_1725_, lean_object* v_as_1726_, lean_object* v_sz_1727_, lean_object* v_i_1728_, lean_object* v_b_1729_, lean_object* v___y_1730_){
_start:
{
size_t v_sz_boxed_1731_; size_t v_i_boxed_1732_; lean_object* v_res_1733_; 
v_sz_boxed_1731_ = lean_unbox_usize(v_sz_1727_);
lean_dec(v_sz_1727_);
v_i_boxed_1732_ = lean_unbox_usize(v_i_1728_);
lean_dec(v_i_1728_);
v_res_1733_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___redArg(v_a_1725_, v_as_1726_, v_sz_boxed_1731_, v_i_boxed_1732_, v_b_1729_);
lean_dec_ref(v_as_1726_);
lean_dec(v_a_1725_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1(lean_object* v_a_1734_, lean_object* v_as_1735_, size_t v_sz_1736_, size_t v_i_1737_, lean_object* v_b_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_){
_start:
{
uint8_t v___x_1744_; 
v___x_1744_ = lean_usize_dec_lt(v_i_1737_, v_sz_1736_);
if (v___x_1744_ == 0)
{
lean_object* v___x_1745_; 
v___x_1745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1745_, 0, v_b_1738_);
return v___x_1745_;
}
else
{
lean_object* v_snd_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1764_; 
v_snd_1746_ = lean_ctor_get(v_b_1738_, 1);
v_isSharedCheck_1764_ = !lean_is_exclusive(v_b_1738_);
if (v_isSharedCheck_1764_ == 0)
{
lean_object* v_unused_1765_; 
v_unused_1765_ = lean_ctor_get(v_b_1738_, 0);
lean_dec(v_unused_1765_);
v___x_1748_ = v_b_1738_;
v_isShared_1749_ = v_isSharedCheck_1764_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_snd_1746_);
lean_dec(v_b_1738_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1764_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1750_; lean_object* v_a_1752_; lean_object* v_a_1759_; 
v___x_1750_ = lean_box(0);
v_a_1759_ = lean_array_uget_borrowed(v_as_1735_, v_i_1737_);
if (lean_obj_tag(v_a_1759_) == 0)
{
v_a_1752_ = v_snd_1746_;
goto v___jp_1751_;
}
else
{
lean_object* v_val_1760_; lean_object* v___x_1761_; uint8_t v___x_1762_; 
v_val_1760_ = lean_ctor_get(v_a_1759_, 0);
v___x_1761_ = l_Lean_LocalDecl_fvarId(v_val_1760_);
v___x_1762_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_1761_, v_a_1734_);
if (v___x_1762_ == 0)
{
lean_object* v___x_1763_; 
v___x_1763_ = lean_local_ctx_erase(v_snd_1746_, v___x_1761_);
v_a_1752_ = v___x_1763_;
goto v___jp_1751_;
}
else
{
lean_dec(v___x_1761_);
v_a_1752_ = v_snd_1746_;
goto v___jp_1751_;
}
}
v___jp_1751_:
{
lean_object* v___x_1754_; 
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 1, v_a_1752_);
lean_ctor_set(v___x_1748_, 0, v___x_1750_);
v___x_1754_ = v___x_1748_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1750_);
lean_ctor_set(v_reuseFailAlloc_1758_, 1, v_a_1752_);
v___x_1754_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
size_t v___x_1755_; size_t v___x_1756_; lean_object* v___x_1757_; 
v___x_1755_ = ((size_t)1ULL);
v___x_1756_ = lean_usize_add(v_i_1737_, v___x_1755_);
v___x_1757_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___redArg(v_a_1734_, v_as_1735_, v_sz_1736_, v___x_1756_, v___x_1754_);
return v___x_1757_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1___boxed(lean_object* v_a_1766_, lean_object* v_as_1767_, lean_object* v_sz_1768_, lean_object* v_i_1769_, lean_object* v_b_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_){
_start:
{
size_t v_sz_boxed_1776_; size_t v_i_boxed_1777_; lean_object* v_res_1778_; 
v_sz_boxed_1776_ = lean_unbox_usize(v_sz_1768_);
lean_dec(v_sz_1768_);
v_i_boxed_1777_ = lean_unbox_usize(v_i_1769_);
lean_dec(v_i_1769_);
v_res_1778_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1(v_a_1766_, v_as_1767_, v_sz_boxed_1776_, v_i_boxed_1777_, v_b_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
lean_dec(v___y_1774_);
lean_dec_ref(v___y_1773_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec_ref(v_as_1767_);
lean_dec(v_a_1766_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0(lean_object* v_a_1779_, lean_object* v_t_1780_, lean_object* v_init_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_){
_start:
{
lean_object* v_root_1787_; lean_object* v_tail_1788_; lean_object* v___x_1789_; 
v_root_1787_ = lean_ctor_get(v_t_1780_, 0);
lean_inc_ref(v_root_1787_);
v_tail_1788_ = lean_ctor_get(v_t_1780_, 1);
lean_inc_ref(v_tail_1788_);
lean_dec_ref(v_t_1780_);
lean_inc_ref(v_init_1781_);
v___x_1789_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0(v_init_1781_, v_a_1779_, v_root_1787_, v_init_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_);
lean_dec_ref(v_init_1781_);
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_object* v_a_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1826_; 
v_a_1790_ = lean_ctor_get(v___x_1789_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1792_ = v___x_1789_;
v_isShared_1793_ = v_isSharedCheck_1826_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_a_1790_);
lean_dec(v___x_1789_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1826_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
if (lean_obj_tag(v_a_1790_) == 0)
{
lean_object* v_a_1794_; lean_object* v___x_1796_; 
lean_dec_ref(v_tail_1788_);
v_a_1794_ = lean_ctor_get(v_a_1790_, 0);
lean_inc(v_a_1794_);
lean_dec_ref(v_a_1790_);
if (v_isShared_1793_ == 0)
{
lean_ctor_set(v___x_1792_, 0, v_a_1794_);
v___x_1796_ = v___x_1792_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_a_1794_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
else
{
lean_object* v_a_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; size_t v_sz_1801_; size_t v___x_1802_; lean_object* v___x_1803_; 
lean_del_object(v___x_1792_);
v_a_1798_ = lean_ctor_get(v_a_1790_, 0);
lean_inc(v_a_1798_);
lean_dec_ref(v_a_1790_);
v___x_1799_ = lean_box(0);
v___x_1800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1799_);
lean_ctor_set(v___x_1800_, 1, v_a_1798_);
v_sz_1801_ = lean_array_size(v_tail_1788_);
v___x_1802_ = ((size_t)0ULL);
v___x_1803_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1(v_a_1779_, v_tail_1788_, v_sz_1801_, v___x_1802_, v___x_1800_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_);
lean_dec_ref(v_tail_1788_);
if (lean_obj_tag(v___x_1803_) == 0)
{
lean_object* v_a_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1817_; 
v_a_1804_ = lean_ctor_get(v___x_1803_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1806_ = v___x_1803_;
v_isShared_1807_ = v_isSharedCheck_1817_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_a_1804_);
lean_dec(v___x_1803_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1817_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v_fst_1808_; 
v_fst_1808_ = lean_ctor_get(v_a_1804_, 0);
if (lean_obj_tag(v_fst_1808_) == 0)
{
lean_object* v_snd_1809_; lean_object* v___x_1811_; 
v_snd_1809_ = lean_ctor_get(v_a_1804_, 1);
lean_inc(v_snd_1809_);
lean_dec(v_a_1804_);
if (v_isShared_1807_ == 0)
{
lean_ctor_set(v___x_1806_, 0, v_snd_1809_);
v___x_1811_ = v___x_1806_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_snd_1809_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
else
{
lean_object* v_val_1813_; lean_object* v___x_1815_; 
lean_inc_ref(v_fst_1808_);
lean_dec(v_a_1804_);
v_val_1813_ = lean_ctor_get(v_fst_1808_, 0);
lean_inc(v_val_1813_);
lean_dec_ref(v_fst_1808_);
if (v_isShared_1807_ == 0)
{
lean_ctor_set(v___x_1806_, 0, v_val_1813_);
v___x_1815_ = v___x_1806_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_val_1813_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
}
else
{
lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1825_; 
v_a_1818_ = lean_ctor_get(v___x_1803_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1820_ = v___x_1803_;
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v___x_1803_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1823_; 
if (v_isShared_1821_ == 0)
{
v___x_1823_ = v___x_1820_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_a_1818_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
}
}
}
}
else
{
lean_object* v_a_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1834_; 
lean_dec_ref(v_tail_1788_);
v_a_1827_ = lean_ctor_get(v___x_1789_, 0);
v_isSharedCheck_1834_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1829_ = v___x_1789_;
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_a_1827_);
lean_dec(v___x_1789_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1832_; 
if (v_isShared_1830_ == 0)
{
v___x_1832_ = v___x_1829_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_a_1827_);
v___x_1832_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
return v___x_1832_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0___boxed(lean_object* v_a_1835_, lean_object* v_t_1836_, lean_object* v_init_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0(v_a_1835_, v_t_1836_, v_init_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec(v_a_1835_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___lam__0(lean_object* v_mvarId_1846_, lean_object* v___x_1847_, lean_object* v___x_1848_, lean_object* v_toPreserve_1849_, uint8_t v_indirectProps_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_){
_start:
{
lean_object* v___x_1856_; 
lean_inc(v_mvarId_1846_);
v___x_1856_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1846_, v___x_1847_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
if (lean_obj_tag(v___x_1856_) == 0)
{
uint8_t v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
lean_dec_ref(v___x_1856_);
v___x_1857_ = 0;
v___x_1858_ = lean_box(v___x_1857_);
v___x_1859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1858_);
lean_ctor_set(v___x_1859_, 1, v___x_1848_);
v___x_1860_ = lean_st_mk_ref(v___x_1859_);
lean_inc(v_mvarId_1846_);
v___x_1861_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed(v_mvarId_1846_, v_toPreserve_1849_, v_indirectProps_1850_, v___x_1860_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
if (lean_obj_tag(v___x_1861_) == 0)
{
lean_object* v_a_1862_; lean_object* v___x_1863_; lean_object* v_lctx_1864_; lean_object* v_localInstances_1865_; lean_object* v_decls_1866_; lean_object* v___x_1867_; 
v_a_1862_ = lean_ctor_get(v___x_1861_, 0);
lean_inc(v_a_1862_);
lean_dec_ref(v___x_1861_);
v___x_1863_ = lean_st_ref_get(v___x_1860_);
lean_dec(v___x_1860_);
lean_dec(v___x_1863_);
v_lctx_1864_ = lean_ctor_get(v___y_1851_, 2);
v_localInstances_1865_ = lean_ctor_get(v___y_1851_, 3);
v_decls_1866_ = lean_ctor_get(v_lctx_1864_, 1);
lean_inc_ref(v_lctx_1864_);
lean_inc_ref(v_decls_1866_);
v___x_1867_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0(v_a_1862_, v_decls_1866_, v_lctx_1864_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
if (lean_obj_tag(v___x_1867_) == 0)
{
lean_object* v_a_1868_; lean_object* v___x_1869_; lean_object* v___y_1871_; lean_object* v___x_1915_; lean_object* v___x_1916_; uint8_t v___x_1917_; 
v_a_1868_ = lean_ctor_get(v___x_1867_, 0);
lean_inc(v_a_1868_);
lean_dec_ref(v___x_1867_);
v___x_1869_ = lean_unsigned_to_nat(0u);
v___x_1915_ = lean_array_get_size(v_localInstances_1865_);
v___x_1916_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___lam__0___closed__0));
v___x_1917_ = lean_nat_dec_lt(v___x_1869_, v___x_1915_);
if (v___x_1917_ == 0)
{
lean_dec(v_a_1862_);
v___y_1871_ = v___x_1916_;
goto v___jp_1870_;
}
else
{
uint8_t v___x_1918_; 
v___x_1918_ = lean_nat_dec_le(v___x_1915_, v___x_1915_);
if (v___x_1918_ == 0)
{
if (v___x_1917_ == 0)
{
lean_dec(v_a_1862_);
v___y_1871_ = v___x_1916_;
goto v___jp_1870_;
}
else
{
size_t v___x_1919_; size_t v___x_1920_; lean_object* v___x_1921_; 
v___x_1919_ = ((size_t)0ULL);
v___x_1920_ = lean_usize_of_nat(v___x_1915_);
v___x_1921_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__3(v_a_1862_, v_localInstances_1865_, v___x_1919_, v___x_1920_, v___x_1916_);
lean_dec(v_a_1862_);
v___y_1871_ = v___x_1921_;
goto v___jp_1870_;
}
}
else
{
size_t v___x_1922_; size_t v___x_1923_; lean_object* v___x_1924_; 
v___x_1922_ = ((size_t)0ULL);
v___x_1923_ = lean_usize_of_nat(v___x_1915_);
v___x_1924_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__3(v_a_1862_, v_localInstances_1865_, v___x_1922_, v___x_1923_, v___x_1916_);
lean_dec(v_a_1862_);
v___y_1871_ = v___x_1924_;
goto v___jp_1870_;
}
}
v___jp_1870_:
{
lean_object* v___x_1872_; 
lean_inc(v_mvarId_1846_);
v___x_1872_ = l_Lean_MVarId_getType(v_mvarId_1846_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; lean_object* v___x_1874_; lean_object* v_a_1875_; lean_object* v___x_1876_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_a_1873_);
lean_dec_ref(v___x_1872_);
v___x_1874_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___redArg(v_a_1873_, v___y_1852_);
v_a_1875_ = lean_ctor_get(v___x_1874_, 0);
lean_inc(v_a_1875_);
lean_dec_ref(v___x_1874_);
lean_inc(v_mvarId_1846_);
v___x_1876_ = l_Lean_MVarId_getTag(v_mvarId_1846_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_a_1877_; uint8_t v___x_1878_; lean_object* v___x_1879_; 
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
lean_inc(v_a_1877_);
lean_dec_ref(v___x_1876_);
v___x_1878_ = 2;
v___x_1879_ = l_Lean_Meta_mkFreshExprMVarAt(v_a_1868_, v___y_1871_, v_a_1875_, v___x_1878_, v_a_1877_, v___x_1869_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
lean_dec_ref(v___y_1851_);
if (lean_obj_tag(v___x_1879_) == 0)
{
lean_object* v_a_1880_; lean_object* v___x_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1889_; 
v_a_1880_ = lean_ctor_get(v___x_1879_, 0);
lean_inc_n(v_a_1880_, 2);
lean_dec_ref(v___x_1879_);
v___x_1881_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___redArg(v_mvarId_1846_, v_a_1880_, v___y_1852_);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1889_ == 0)
{
lean_object* v_unused_1890_; 
v_unused_1890_ = lean_ctor_get(v___x_1881_, 0);
lean_dec(v_unused_1890_);
v___x_1883_ = v___x_1881_;
v_isShared_1884_ = v_isSharedCheck_1889_;
goto v_resetjp_1882_;
}
else
{
lean_dec(v___x_1881_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1889_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1885_; lean_object* v___x_1887_; 
v___x_1885_ = l_Lean_Expr_mvarId_x21(v_a_1880_);
lean_dec(v_a_1880_);
if (v_isShared_1884_ == 0)
{
lean_ctor_set(v___x_1883_, 0, v___x_1885_);
v___x_1887_ = v___x_1883_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v___x_1885_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
else
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1898_; 
lean_dec(v_mvarId_1846_);
v_a_1891_ = lean_ctor_get(v___x_1879_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1893_ = v___x_1879_;
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1879_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1896_; 
if (v_isShared_1894_ == 0)
{
v___x_1896_ = v___x_1893_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1891_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
}
else
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1906_; 
lean_dec(v_a_1875_);
lean_dec_ref(v___y_1871_);
lean_dec(v_a_1868_);
lean_dec_ref(v___y_1851_);
lean_dec(v_mvarId_1846_);
v_a_1899_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1901_ = v___x_1876_;
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1876_);
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
lean_dec_ref(v___y_1871_);
lean_dec(v_a_1868_);
lean_dec_ref(v___y_1851_);
lean_dec(v_mvarId_1846_);
v_a_1907_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1909_ = v___x_1872_;
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1872_);
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
}
else
{
lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1932_; 
lean_dec(v_a_1862_);
lean_dec_ref(v___y_1851_);
lean_dec(v_mvarId_1846_);
v_a_1925_ = lean_ctor_get(v___x_1867_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1927_ = v___x_1867_;
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___x_1867_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___x_1930_; 
if (v_isShared_1928_ == 0)
{
v___x_1930_ = v___x_1927_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_a_1925_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
}
}
else
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1940_; 
lean_dec(v___x_1860_);
lean_dec_ref(v___y_1851_);
lean_dec(v_mvarId_1846_);
v_a_1933_ = lean_ctor_get(v___x_1861_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1861_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1935_ = v___x_1861_;
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1861_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1938_; 
if (v_isShared_1936_ == 0)
{
v___x_1938_ = v___x_1935_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1933_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
}
else
{
lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1948_; 
lean_dec_ref(v___y_1851_);
lean_dec(v___x_1848_);
lean_dec(v_mvarId_1846_);
v_a_1941_ = lean_ctor_get(v___x_1856_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1943_ = v___x_1856_;
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1856_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1946_; 
if (v_isShared_1944_ == 0)
{
v___x_1946_ = v___x_1943_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1941_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___lam__0___boxed(lean_object* v_mvarId_1949_, lean_object* v___x_1950_, lean_object* v___x_1951_, lean_object* v_toPreserve_1952_, lean_object* v_indirectProps_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
uint8_t v_indirectProps_boxed_1959_; lean_object* v_res_1960_; 
v_indirectProps_boxed_1959_ = lean_unbox(v_indirectProps_1953_);
v_res_1960_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___lam__0(v_mvarId_1949_, v___x_1950_, v___x_1951_, v_toPreserve_1952_, v_indirectProps_boxed_1959_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec_ref(v_toPreserve_1952_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(lean_object* v_mvarId_1964_, lean_object* v_toPreserve_1965_, uint8_t v_indirectProps_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_){
_start:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___f_1975_; lean_object* v___x_1976_; 
v___x_1972_ = lean_box(1);
v___x_1973_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___closed__1));
v___x_1974_ = lean_box(v_indirectProps_1966_);
lean_inc(v_mvarId_1964_);
v___f_1975_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1975_, 0, v_mvarId_1964_);
lean_closure_set(v___f_1975_, 1, v___x_1973_);
lean_closure_set(v___f_1975_, 2, v___x_1972_);
lean_closure_set(v___f_1975_, 3, v_toPreserve_1965_);
lean_closure_set(v___f_1975_, 4, v___x_1974_);
v___x_1976_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___redArg(v_mvarId_1964_, v___f_1975_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_);
return v___x_1976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___boxed(lean_object* v_mvarId_1977_, lean_object* v_toPreserve_1978_, lean_object* v_indirectProps_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_){
_start:
{
uint8_t v_indirectProps_boxed_1985_; lean_object* v_res_1986_; 
v_indirectProps_boxed_1985_ = lean_unbox(v_indirectProps_1979_);
v_res_1986_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(v_mvarId_1977_, v_toPreserve_1978_, v_indirectProps_boxed_1985_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_);
lean_dec(v_a_1983_);
lean_dec_ref(v_a_1982_);
lean_dec(v_a_1981_);
lean_dec_ref(v_a_1980_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2(lean_object* v_mvarId_1987_, lean_object* v_val_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
lean_object* v___x_1994_; 
v___x_1994_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___redArg(v_mvarId_1987_, v_val_1988_, v___y_1990_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___boxed(lean_object* v_mvarId_1995_, lean_object* v_val_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_){
_start:
{
lean_object* v_res_2002_; 
v_res_2002_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2(v_mvarId_1995_, v_val_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
return v_res_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4(lean_object* v_00_u03b2_2003_, lean_object* v_x_2004_, lean_object* v_x_2005_, lean_object* v_x_2006_){
_start:
{
lean_object* v___x_2007_; 
v___x_2007_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4___redArg(v_x_2004_, v_x_2005_, v_x_2006_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6(lean_object* v_a_2008_, lean_object* v_as_2009_, size_t v_sz_2010_, size_t v_i_2011_, lean_object* v_b_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
lean_object* v___x_2018_; 
v___x_2018_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___redArg(v_a_2008_, v_as_2009_, v_sz_2010_, v_i_2011_, v_b_2012_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___boxed(lean_object* v_a_2019_, lean_object* v_as_2020_, lean_object* v_sz_2021_, lean_object* v_i_2022_, lean_object* v_b_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
size_t v_sz_boxed_2029_; size_t v_i_boxed_2030_; lean_object* v_res_2031_; 
v_sz_boxed_2029_ = lean_unbox_usize(v_sz_2021_);
lean_dec(v_sz_2021_);
v_i_boxed_2030_ = lean_unbox_usize(v_i_2022_);
lean_dec(v_i_2022_);
v_res_2031_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6(v_a_2019_, v_as_2020_, v_sz_boxed_2029_, v_i_boxed_2030_, v_b_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec_ref(v_as_2020_);
lean_dec(v_a_2019_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9(lean_object* v_00_u03b2_2032_, lean_object* v_x_2033_, size_t v_x_2034_, size_t v_x_2035_, lean_object* v_x_2036_, lean_object* v_x_2037_){
_start:
{
lean_object* v___x_2038_; 
v___x_2038_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg(v_x_2033_, v_x_2034_, v_x_2035_, v_x_2036_, v_x_2037_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___boxed(lean_object* v_00_u03b2_2039_, lean_object* v_x_2040_, lean_object* v_x_2041_, lean_object* v_x_2042_, lean_object* v_x_2043_, lean_object* v_x_2044_){
_start:
{
size_t v_x_8535__boxed_2045_; size_t v_x_8536__boxed_2046_; lean_object* v_res_2047_; 
v_x_8535__boxed_2045_ = lean_unbox_usize(v_x_2041_);
lean_dec(v_x_2041_);
v_x_8536__boxed_2046_ = lean_unbox_usize(v_x_2042_);
lean_dec(v_x_2042_);
v_res_2047_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9(v_00_u03b2_2039_, v_x_2040_, v_x_8535__boxed_2045_, v_x_8536__boxed_2046_, v_x_2043_, v_x_2044_);
return v_res_2047_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7(lean_object* v_a_2048_, lean_object* v_as_2049_, size_t v_sz_2050_, size_t v_i_2051_, lean_object* v_b_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_){
_start:
{
lean_object* v___x_2058_; 
v___x_2058_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___redArg(v_a_2048_, v_as_2049_, v_sz_2050_, v_i_2051_, v_b_2052_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___boxed(lean_object* v_a_2059_, lean_object* v_as_2060_, lean_object* v_sz_2061_, lean_object* v_i_2062_, lean_object* v_b_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_){
_start:
{
size_t v_sz_boxed_2069_; size_t v_i_boxed_2070_; lean_object* v_res_2071_; 
v_sz_boxed_2069_ = lean_unbox_usize(v_sz_2061_);
lean_dec(v_sz_2061_);
v_i_boxed_2070_ = lean_unbox_usize(v_i_2062_);
lean_dec(v_i_2062_);
v_res_2071_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7(v_a_2059_, v_as_2060_, v_sz_boxed_2069_, v_i_boxed_2070_, v_b_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
lean_dec(v___y_2067_);
lean_dec_ref(v___y_2066_);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
lean_dec_ref(v_as_2060_);
lean_dec(v_a_2059_);
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12(lean_object* v_00_u03b2_2072_, lean_object* v_n_2073_, lean_object* v_k_2074_, lean_object* v_v_2075_){
_start:
{
lean_object* v___x_2076_; 
v___x_2076_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12___redArg(v_n_2073_, v_k_2074_, v_v_2075_);
return v___x_2076_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13(lean_object* v_00_u03b2_2077_, size_t v_depth_2078_, lean_object* v_keys_2079_, lean_object* v_vals_2080_, lean_object* v_heq_2081_, lean_object* v_i_2082_, lean_object* v_entries_2083_){
_start:
{
lean_object* v___x_2084_; 
v___x_2084_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___redArg(v_depth_2078_, v_keys_2079_, v_vals_2080_, v_i_2082_, v_entries_2083_);
return v___x_2084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___boxed(lean_object* v_00_u03b2_2085_, lean_object* v_depth_2086_, lean_object* v_keys_2087_, lean_object* v_vals_2088_, lean_object* v_heq_2089_, lean_object* v_i_2090_, lean_object* v_entries_2091_){
_start:
{
size_t v_depth_boxed_2092_; lean_object* v_res_2093_; 
v_depth_boxed_2092_ = lean_unbox_usize(v_depth_2086_);
lean_dec(v_depth_2086_);
v_res_2093_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13(v_00_u03b2_2085_, v_depth_boxed_2092_, v_keys_2087_, v_vals_2088_, v_heq_2089_, v_i_2090_, v_entries_2091_);
lean_dec_ref(v_vals_2088_);
lean_dec_ref(v_keys_2087_);
return v_res_2093_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12_spec__13(lean_object* v_00_u03b2_2094_, lean_object* v_x_2095_, lean_object* v_x_2096_, lean_object* v_x_2097_, lean_object* v_x_2098_){
_start:
{
lean_object* v___x_2099_; 
v___x_2099_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12_spec__13___redArg(v_x_2095_, v_x_2096_, v_x_2097_, v_x_2098_);
return v___x_2099_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_cleanup(lean_object* v_mvarId_2100_, lean_object* v_toPreserve_2101_, uint8_t v_indirectProps_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_){
_start:
{
lean_object* v___x_2108_; 
v___x_2108_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(v_mvarId_2100_, v_toPreserve_2101_, v_indirectProps_2102_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_);
return v___x_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_cleanup___boxed(lean_object* v_mvarId_2109_, lean_object* v_toPreserve_2110_, lean_object* v_indirectProps_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_){
_start:
{
uint8_t v_indirectProps_boxed_2117_; lean_object* v_res_2118_; 
v_indirectProps_boxed_2117_ = lean_unbox(v_indirectProps_2111_);
v_res_2118_ = l_Lean_MVarId_cleanup(v_mvarId_2109_, v_toPreserve_2110_, v_indirectProps_boxed_2117_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_);
lean_dec(v_a_2115_);
lean_dec_ref(v_a_2114_);
lean_dec(v_a_2113_);
lean_dec_ref(v_a_2112_);
return v_res_2118_;
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
