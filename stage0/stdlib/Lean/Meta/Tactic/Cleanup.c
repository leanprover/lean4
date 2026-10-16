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
lean_object* lean_mk_array(lean_object*, lean_object*);
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
uint8_t v___x_66_; lean_object* v___x_67_; lean_object* v_snd_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_79_; 
v___x_66_ = 1;
v___x_67_ = lean_st_ref_take(v_a_57_);
v_snd_68_ = lean_ctor_get(v___x_67_, 1);
v_isSharedCheck_79_ = !lean_is_exclusive(v___x_67_);
if (v_isSharedCheck_79_ == 0)
{
lean_object* v_unused_80_; 
v_unused_80_ = lean_ctor_get(v___x_67_, 0);
lean_dec(v_unused_80_);
v___x_70_ = v___x_67_;
v_isShared_71_ = v_isSharedCheck_79_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_snd_68_);
lean_dec(v___x_67_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_79_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_75_; 
lean_inc(v_fvarId_56_);
v___x_72_ = l_Lean_FVarIdSet_insert(v_snd_68_, v_fvarId_56_);
v___x_73_ = lean_box(v___x_66_);
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 1, v___x_72_);
lean_ctor_set(v___x_70_, 0, v___x_73_);
v___x_75_ = v___x_70_;
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
v___x_76_ = lean_st_ref_put(v_a_57_, v___x_75_);
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
lean_object* v_k_91_; lean_object* v_l_92_; lean_object* v_r_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v_k_91_ = lean_ctor_get(v_x_84_, 1);
lean_inc(v_k_91_);
v_l_92_ = lean_ctor_get(v_x_84_, 3);
lean_inc(v_l_92_);
v_r_93_ = lean_ctor_get(v_x_84_, 4);
lean_inc(v_r_93_);
lean_dec_ref_known(v_x_84_, 5);
v___x_94_ = lean_box(0);
v___x_95_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__1(v_init_83_, v_l_92_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_);
if (lean_obj_tag(v___x_95_) == 0)
{
lean_object* v___x_96_; 
lean_dec_ref_known(v___x_95_, 1);
v___x_96_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v_k_91_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_);
if (lean_obj_tag(v___x_96_) == 0)
{
lean_dec_ref_known(v___x_96_, 1);
v_init_83_ = v___x_94_;
v_x_84_ = v_r_93_;
goto _start;
}
else
{
lean_object* v_a_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_105_; 
lean_dec(v_r_93_);
v_a_98_ = lean_ctor_get(v___x_96_, 0);
v_isSharedCheck_105_ = !lean_is_exclusive(v___x_96_);
if (v_isSharedCheck_105_ == 0)
{
v___x_100_ = v___x_96_;
v_isShared_101_ = v_isSharedCheck_105_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_a_98_);
lean_dec(v___x_96_);
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
return v___x_95_;
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
v___x_257_ = lean_st_ref_put(v___y_241_, v___x_256_);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__2(uint8_t v___x_309_, lean_object* v_x_310_){
_start:
{
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__2___boxed(lean_object* v___x_311_, lean_object* v_x_312_){
_start:
{
uint8_t v___x_8971__boxed_313_; uint8_t v_res_314_; lean_object* v_r_315_; 
v___x_8971__boxed_313_ = lean_unbox(v___x_311_);
v_res_314_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__2(v___x_8971__boxed_313_, v_x_312_);
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
lean_object* v_val_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v_snd_345_; lean_object* v___x_346_; uint8_t v___x_347_; 
lean_dec(v_snd_328_);
v_val_342_ = lean_ctor_get(v_a_341_, 0);
v___x_343_ = lean_box(0);
v___x_344_ = lean_st_ref_get(v___y_320_);
v_snd_345_ = lean_ctor_get(v___x_344_, 1);
lean_inc(v_snd_345_);
lean_dec(v___x_344_);
v___x_346_ = l_Lean_LocalDecl_fvarId(v_val_342_);
v___x_347_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_346_, v_snd_345_);
if (v___x_347_ == 0)
{
lean_object* v___f_348_; lean_object* v___x_349_; lean_object* v___f_350_; lean_object* v___y_352_; lean_object* v___y_353_; lean_object* v___y_354_; lean_object* v___y_355_; lean_object* v___y_356_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___f_348_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_348_, 0, v_snd_345_);
v___x_349_ = lean_box(v___x_347_);
v___f_350_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__2___boxed), 2, 1);
lean_closure_set(v___f_350_, 0, v___x_349_);
v___x_379_ = l_Lean_LocalDecl_type(v_val_342_);
lean_inc_ref(v___x_379_);
v___x_380_ = l_Lean_Meta_isProp(v___x_379_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_a_381_; uint8_t v___x_382_; 
v_a_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc(v_a_381_);
lean_dec_ref_known(v___x_380_, 1);
v___x_382_ = lean_unbox(v_a_381_);
lean_dec(v_a_381_);
if (v___x_382_ == 0)
{
lean_dec_ref(v___x_379_);
v___y_352_ = v___y_320_;
v___y_353_ = v___y_321_;
v___y_354_ = v___y_322_;
v___y_355_ = v___y_323_;
v___y_356_ = v___y_324_;
goto v___jp_351_;
}
else
{
lean_object* v___x_383_; 
lean_inc_ref(v___f_350_);
lean_inc_ref(v___f_348_);
v___x_383_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v___x_379_, v___f_348_, v___f_350_, v___y_322_);
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
v___y_352_ = v___y_320_;
v___y_353_ = v___y_321_;
v___y_354_ = v___y_322_;
v___y_355_ = v___y_323_;
v___y_356_ = v___y_324_;
goto v___jp_351_;
}
else
{
lean_object* v___x_386_; 
lean_inc(v___x_346_);
v___x_386_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_346_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
if (lean_obj_tag(v___x_386_) == 0)
{
lean_dec_ref_known(v___x_386_, 1);
v___y_352_ = v___y_320_;
v___y_353_ = v___y_321_;
v___y_354_ = v___y_322_;
v___y_355_ = v___y_323_;
v___y_356_ = v___y_324_;
goto v___jp_351_;
}
else
{
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_394_; 
lean_dec_ref(v___f_350_);
lean_dec_ref(v___f_348_);
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
lean_dec_ref(v___f_350_);
lean_dec_ref(v___f_348_);
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
}
else
{
lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_410_; 
lean_dec_ref(v___x_379_);
lean_dec_ref(v___f_350_);
lean_dec_ref(v___f_348_);
lean_dec(v___x_346_);
lean_del_object(v___x_330_);
v_a_403_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_410_ == 0)
{
v___x_405_ = v___x_380_;
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_380_);
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
v___jp_351_:
{
lean_object* v___x_357_; 
v___x_357_ = l_Lean_LocalDecl_value_x3f(v_val_342_, v___x_347_);
if (lean_obj_tag(v___x_357_) == 1)
{
lean_object* v_val_358_; lean_object* v___x_359_; 
v_val_358_ = lean_ctor_get(v___x_357_, 0);
lean_inc(v_val_358_);
lean_dec_ref_known(v___x_357_, 1);
v___x_359_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v_val_358_, v___f_348_, v___f_350_, v___y_354_);
if (lean_obj_tag(v___x_359_) == 0)
{
lean_object* v_a_360_; uint8_t v___x_361_; 
v_a_360_ = lean_ctor_get(v___x_359_, 0);
lean_inc(v_a_360_);
lean_dec_ref_known(v___x_359_, 1);
v___x_361_ = lean_unbox(v_a_360_);
lean_dec(v_a_360_);
if (v___x_361_ == 0)
{
lean_dec(v___x_346_);
v_a_334_ = v___x_343_;
goto v___jp_333_;
}
else
{
lean_object* v___x_362_; 
v___x_362_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_346_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_dec_ref_known(v___x_362_, 1);
v_a_334_ = v___x_343_;
goto v___jp_333_;
}
else
{
lean_object* v_a_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_370_; 
lean_del_object(v___x_330_);
v_a_363_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_370_ == 0)
{
v___x_365_ = v___x_362_;
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_a_363_);
lean_dec(v___x_362_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_368_; 
if (v_isShared_366_ == 0)
{
v___x_368_ = v___x_365_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_a_363_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
}
}
else
{
lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_378_; 
lean_dec(v___x_346_);
lean_del_object(v___x_330_);
v_a_371_ = lean_ctor_get(v___x_359_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_378_ == 0)
{
v___x_373_ = v___x_359_;
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_359_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_376_; 
if (v_isShared_374_ == 0)
{
v___x_376_ = v___x_373_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_a_371_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
}
else
{
lean_dec(v___x_357_);
lean_dec_ref(v___f_350_);
lean_dec_ref(v___f_348_);
lean_dec(v___x_346_);
v_a_334_ = v___x_343_;
goto v___jp_333_;
}
}
}
else
{
lean_dec(v___x_346_);
lean_dec(v_snd_345_);
v_a_334_ = v___x_343_;
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
lean_object* v_val_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v_snd_455_; lean_object* v___x_456_; uint8_t v___x_457_; 
lean_dec(v_snd_438_);
v_val_452_ = lean_ctor_get(v_a_451_, 0);
v___x_453_ = lean_box(0);
v___x_454_ = lean_st_ref_get(v___y_430_);
v_snd_455_ = lean_ctor_get(v___x_454_, 1);
lean_inc(v_snd_455_);
lean_dec(v___x_454_);
v___x_456_ = l_Lean_LocalDecl_fvarId(v_val_452_);
v___x_457_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_456_, v_snd_455_);
if (v___x_457_ == 0)
{
lean_object* v___f_458_; lean_object* v___x_459_; lean_object* v___f_460_; lean_object* v___y_462_; lean_object* v___y_463_; lean_object* v___y_464_; lean_object* v___y_465_; lean_object* v___y_466_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___f_458_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_458_, 0, v_snd_455_);
v___x_459_ = lean_box(v___x_457_);
v___f_460_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__2___boxed), 2, 1);
lean_closure_set(v___f_460_, 0, v___x_459_);
v___x_489_ = l_Lean_LocalDecl_type(v_val_452_);
lean_inc_ref(v___x_489_);
v___x_490_ = l_Lean_Meta_isProp(v___x_489_, v___y_431_, v___y_432_, v___y_433_, v___y_434_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v_a_491_; uint8_t v___x_492_; 
v_a_491_ = lean_ctor_get(v___x_490_, 0);
lean_inc(v_a_491_);
lean_dec_ref_known(v___x_490_, 1);
v___x_492_ = lean_unbox(v_a_491_);
lean_dec(v_a_491_);
if (v___x_492_ == 0)
{
lean_dec_ref(v___x_489_);
v___y_462_ = v___y_430_;
v___y_463_ = v___y_431_;
v___y_464_ = v___y_432_;
v___y_465_ = v___y_433_;
v___y_466_ = v___y_434_;
goto v___jp_461_;
}
else
{
lean_object* v___x_493_; 
lean_inc_ref(v___f_460_);
lean_inc_ref(v___f_458_);
v___x_493_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v___x_489_, v___f_458_, v___f_460_, v___y_432_);
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
v___y_462_ = v___y_430_;
v___y_463_ = v___y_431_;
v___y_464_ = v___y_432_;
v___y_465_ = v___y_433_;
v___y_466_ = v___y_434_;
goto v___jp_461_;
}
else
{
lean_object* v___x_496_; 
lean_inc(v___x_456_);
v___x_496_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_456_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_dec_ref_known(v___x_496_, 1);
v___y_462_ = v___y_430_;
v___y_463_ = v___y_431_;
v___y_464_ = v___y_432_;
v___y_465_ = v___y_433_;
v___y_466_ = v___y_434_;
goto v___jp_461_;
}
else
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_504_; 
lean_dec_ref(v___f_460_);
lean_dec_ref(v___f_458_);
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
lean_dec_ref(v___f_460_);
lean_dec_ref(v___f_458_);
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
}
else
{
lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_520_; 
lean_dec_ref(v___x_489_);
lean_dec_ref(v___f_460_);
lean_dec_ref(v___f_458_);
lean_dec(v___x_456_);
lean_del_object(v___x_440_);
v_a_513_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_520_ == 0)
{
v___x_515_ = v___x_490_;
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v___x_490_);
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
v___jp_461_:
{
lean_object* v___x_467_; 
v___x_467_ = l_Lean_LocalDecl_value_x3f(v_val_452_, v___x_457_);
if (lean_obj_tag(v___x_467_) == 1)
{
lean_object* v_val_468_; lean_object* v___x_469_; 
v_val_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc(v_val_468_);
lean_dec_ref_known(v___x_467_, 1);
v___x_469_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v_val_468_, v___f_458_, v___f_460_, v___y_464_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v_a_470_; uint8_t v___x_471_; 
v_a_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_a_470_);
lean_dec_ref_known(v___x_469_, 1);
v___x_471_ = lean_unbox(v_a_470_);
lean_dec(v_a_470_);
if (v___x_471_ == 0)
{
lean_dec(v___x_456_);
v_a_444_ = v___x_453_;
goto v___jp_443_;
}
else
{
lean_object* v___x_472_; 
v___x_472_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_456_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_dec_ref_known(v___x_472_, 1);
v_a_444_ = v___x_453_;
goto v___jp_443_;
}
else
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_480_; 
lean_del_object(v___x_440_);
v_a_473_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_480_ == 0)
{
v___x_475_ = v___x_472_;
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___x_472_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_478_; 
if (v_isShared_476_ == 0)
{
v___x_478_ = v___x_475_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_a_473_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
}
else
{
lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_488_; 
lean_dec(v___x_456_);
lean_del_object(v___x_440_);
v_a_481_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_488_ == 0)
{
v___x_483_ = v___x_469_;
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v___x_469_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_486_; 
if (v_isShared_484_ == 0)
{
v___x_486_ = v___x_483_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_a_481_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
else
{
lean_dec(v___x_467_);
lean_dec_ref(v___f_460_);
lean_dec_ref(v___f_458_);
lean_dec(v___x_456_);
v_a_444_ = v___x_453_;
goto v___jp_443_;
}
}
}
else
{
lean_dec(v___x_456_);
lean_dec(v_snd_455_);
v_a_444_ = v___x_453_;
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
lean_object* v_val_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v_snd_565_; lean_object* v___x_566_; uint8_t v___x_567_; 
lean_dec(v_snd_548_);
v_val_562_ = lean_ctor_get(v_a_561_, 0);
v___x_563_ = lean_box(0);
v___x_564_ = lean_st_ref_get(v___y_540_);
v_snd_565_ = lean_ctor_get(v___x_564_, 1);
lean_inc(v_snd_565_);
lean_dec(v___x_564_);
v___x_566_ = l_Lean_LocalDecl_fvarId(v_val_562_);
v___x_567_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_566_, v_snd_565_);
if (v___x_567_ == 0)
{
lean_object* v___f_568_; lean_object* v___x_569_; lean_object* v___f_570_; lean_object* v___y_572_; lean_object* v___y_573_; lean_object* v___y_574_; lean_object* v___y_575_; lean_object* v___y_576_; lean_object* v___x_599_; lean_object* v___x_600_; 
v___f_568_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_568_, 0, v_snd_565_);
v___x_569_ = lean_box(v___x_567_);
v___f_570_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__2___boxed), 2, 1);
lean_closure_set(v___f_570_, 0, v___x_569_);
v___x_599_ = l_Lean_LocalDecl_type(v_val_562_);
lean_inc_ref(v___x_599_);
v___x_600_ = l_Lean_Meta_isProp(v___x_599_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v_a_601_; uint8_t v___x_602_; 
v_a_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_a_601_);
lean_dec_ref_known(v___x_600_, 1);
v___x_602_ = lean_unbox(v_a_601_);
lean_dec(v_a_601_);
if (v___x_602_ == 0)
{
lean_dec_ref(v___x_599_);
v___y_572_ = v___y_540_;
v___y_573_ = v___y_541_;
v___y_574_ = v___y_542_;
v___y_575_ = v___y_543_;
v___y_576_ = v___y_544_;
goto v___jp_571_;
}
else
{
lean_object* v___x_603_; 
lean_inc_ref(v___f_570_);
lean_inc_ref(v___f_568_);
v___x_603_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v___x_599_, v___f_568_, v___f_570_, v___y_542_);
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
v___y_572_ = v___y_540_;
v___y_573_ = v___y_541_;
v___y_574_ = v___y_542_;
v___y_575_ = v___y_543_;
v___y_576_ = v___y_544_;
goto v___jp_571_;
}
else
{
lean_object* v___x_606_; 
lean_inc(v___x_566_);
v___x_606_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_566_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_dec_ref_known(v___x_606_, 1);
v___y_572_ = v___y_540_;
v___y_573_ = v___y_541_;
v___y_574_ = v___y_542_;
v___y_575_ = v___y_543_;
v___y_576_ = v___y_544_;
goto v___jp_571_;
}
else
{
lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_614_; 
lean_dec_ref(v___f_570_);
lean_dec_ref(v___f_568_);
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
lean_dec_ref(v___f_570_);
lean_dec_ref(v___f_568_);
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
}
else
{
lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
lean_dec_ref(v___x_599_);
lean_dec_ref(v___f_570_);
lean_dec_ref(v___f_568_);
lean_dec(v___x_566_);
lean_del_object(v___x_550_);
v_a_623_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_630_ == 0)
{
v___x_625_ = v___x_600_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___x_600_);
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
v___jp_571_:
{
lean_object* v___x_577_; 
v___x_577_ = l_Lean_LocalDecl_value_x3f(v_val_562_, v___x_567_);
if (lean_obj_tag(v___x_577_) == 1)
{
lean_object* v_val_578_; lean_object* v___x_579_; 
v_val_578_ = lean_ctor_get(v___x_577_, 0);
lean_inc(v_val_578_);
lean_dec_ref_known(v___x_577_, 1);
v___x_579_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v_val_578_, v___f_568_, v___f_570_, v___y_574_);
if (lean_obj_tag(v___x_579_) == 0)
{
lean_object* v_a_580_; uint8_t v___x_581_; 
v_a_580_ = lean_ctor_get(v___x_579_, 0);
lean_inc(v_a_580_);
lean_dec_ref_known(v___x_579_, 1);
v___x_581_ = lean_unbox(v_a_580_);
lean_dec(v_a_580_);
if (v___x_581_ == 0)
{
lean_dec(v___x_566_);
v_a_554_ = v___x_563_;
goto v___jp_553_;
}
else
{
lean_object* v___x_582_; 
v___x_582_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_566_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_dec_ref_known(v___x_582_, 1);
v_a_554_ = v___x_563_;
goto v___jp_553_;
}
else
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_590_; 
lean_del_object(v___x_550_);
v_a_583_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_590_ == 0)
{
v___x_585_ = v___x_582_;
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_582_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_583_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
}
else
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_598_; 
lean_dec(v___x_566_);
lean_del_object(v___x_550_);
v_a_591_ = lean_ctor_get(v___x_579_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_598_ == 0)
{
v___x_593_ = v___x_579_;
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_579_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_596_; 
if (v_isShared_594_ == 0)
{
v___x_596_ = v___x_593_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_a_591_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
}
else
{
lean_dec(v___x_577_);
lean_dec_ref(v___f_570_);
lean_dec_ref(v___f_568_);
lean_dec(v___x_566_);
v_a_554_ = v___x_563_;
goto v___jp_553_;
}
}
}
else
{
lean_dec(v___x_566_);
lean_dec(v_snd_565_);
v_a_554_ = v___x_563_;
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
lean_object* v_val_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v_snd_675_; lean_object* v___x_676_; uint8_t v___x_677_; 
lean_dec(v_snd_658_);
v_val_672_ = lean_ctor_get(v_a_671_, 0);
v___x_673_ = lean_box(0);
v___x_674_ = lean_st_ref_get(v___y_650_);
v_snd_675_ = lean_ctor_get(v___x_674_, 1);
lean_inc(v_snd_675_);
lean_dec(v___x_674_);
v___x_676_ = l_Lean_LocalDecl_fvarId(v_val_672_);
v___x_677_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_676_, v_snd_675_);
if (v___x_677_ == 0)
{
lean_object* v___f_678_; lean_object* v___x_679_; lean_object* v___f_680_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___x_709_; lean_object* v___x_710_; 
v___f_678_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_678_, 0, v_snd_675_);
v___x_679_ = lean_box(v___x_677_);
v___f_680_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__2___boxed), 2, 1);
lean_closure_set(v___f_680_, 0, v___x_679_);
v___x_709_ = l_Lean_LocalDecl_type(v_val_672_);
lean_inc_ref(v___x_709_);
v___x_710_ = l_Lean_Meta_isProp(v___x_709_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
if (lean_obj_tag(v___x_710_) == 0)
{
lean_object* v_a_711_; uint8_t v___x_712_; 
v_a_711_ = lean_ctor_get(v___x_710_, 0);
lean_inc(v_a_711_);
lean_dec_ref_known(v___x_710_, 1);
v___x_712_ = lean_unbox(v_a_711_);
lean_dec(v_a_711_);
if (v___x_712_ == 0)
{
lean_dec_ref(v___x_709_);
v___y_682_ = v___y_650_;
v___y_683_ = v___y_651_;
v___y_684_ = v___y_652_;
v___y_685_ = v___y_653_;
v___y_686_ = v___y_654_;
goto v___jp_681_;
}
else
{
lean_object* v___x_713_; 
lean_inc_ref(v___f_680_);
lean_inc_ref(v___f_678_);
v___x_713_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v___x_709_, v___f_678_, v___f_680_, v___y_652_);
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
v___y_682_ = v___y_650_;
v___y_683_ = v___y_651_;
v___y_684_ = v___y_652_;
v___y_685_ = v___y_653_;
v___y_686_ = v___y_654_;
goto v___jp_681_;
}
else
{
lean_object* v___x_716_; 
lean_inc(v___x_676_);
v___x_716_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_676_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_dec_ref_known(v___x_716_, 1);
v___y_682_ = v___y_650_;
v___y_683_ = v___y_651_;
v___y_684_ = v___y_652_;
v___y_685_ = v___y_653_;
v___y_686_ = v___y_654_;
goto v___jp_681_;
}
else
{
lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_724_; 
lean_dec_ref(v___f_680_);
lean_dec_ref(v___f_678_);
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
lean_dec_ref(v___f_680_);
lean_dec_ref(v___f_678_);
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
}
else
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_740_; 
lean_dec_ref(v___x_709_);
lean_dec_ref(v___f_680_);
lean_dec_ref(v___f_678_);
lean_dec(v___x_676_);
lean_del_object(v___x_660_);
v_a_733_ = lean_ctor_get(v___x_710_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_710_);
if (v_isSharedCheck_740_ == 0)
{
v___x_735_ = v___x_710_;
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_710_);
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
v___jp_681_:
{
lean_object* v___x_687_; 
v___x_687_ = l_Lean_LocalDecl_value_x3f(v_val_672_, v___x_677_);
if (lean_obj_tag(v___x_687_) == 1)
{
lean_object* v_val_688_; lean_object* v___x_689_; 
v_val_688_ = lean_ctor_get(v___x_687_, 0);
lean_inc(v_val_688_);
lean_dec_ref_known(v___x_687_, 1);
v___x_689_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v_val_688_, v___f_678_, v___f_680_, v___y_684_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v_a_690_; uint8_t v___x_691_; 
v_a_690_ = lean_ctor_get(v___x_689_, 0);
lean_inc(v_a_690_);
lean_dec_ref_known(v___x_689_, 1);
v___x_691_ = lean_unbox(v_a_690_);
lean_dec(v_a_690_);
if (v___x_691_ == 0)
{
lean_dec(v___x_676_);
v_a_664_ = v___x_673_;
goto v___jp_663_;
}
else
{
lean_object* v___x_692_; 
v___x_692_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_676_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_dec_ref_known(v___x_692_, 1);
v_a_664_ = v___x_673_;
goto v___jp_663_;
}
else
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_700_; 
lean_del_object(v___x_660_);
v_a_693_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_700_ == 0)
{
v___x_695_ = v___x_692_;
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_692_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_698_; 
if (v_isShared_696_ == 0)
{
v___x_698_ = v___x_695_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_a_693_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
}
else
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
lean_dec(v___x_676_);
lean_del_object(v___x_660_);
v_a_701_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_708_ == 0)
{
v___x_703_ = v___x_689_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_689_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_704_ == 0)
{
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
else
{
lean_dec(v___x_687_);
lean_dec_ref(v___f_680_);
lean_dec_ref(v___f_678_);
lean_dec(v___x_676_);
v_a_664_ = v___x_673_;
goto v___jp_663_;
}
}
}
else
{
lean_dec(v___x_676_);
lean_dec(v_snd_675_);
v_a_664_ = v___x_673_;
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
lean_object* v___x_840_; lean_object* v_a_841_; lean_object* v___x_842_; 
v___x_840_ = lean_box(0);
v_a_841_ = lean_array_uget_borrowed(v_as_824_, v_i_826_);
lean_inc(v_snd_836_);
v___x_842_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1(v_init_823_, v_a_841_, v_snd_836_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_861_; 
v_a_843_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_861_ == 0)
{
v___x_845_ = v___x_842_;
v_isShared_846_ = v_isSharedCheck_861_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_842_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_861_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
if (lean_obj_tag(v_a_843_) == 0)
{
lean_object* v___x_847_; lean_object* v___x_849_; 
v___x_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_847_, 0, v_a_843_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 0, v___x_847_);
v___x_849_ = v___x_838_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v___x_847_);
lean_ctor_set(v_reuseFailAlloc_853_, 1, v_snd_836_);
v___x_849_ = v_reuseFailAlloc_853_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
lean_object* v___x_851_; 
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 0, v___x_849_);
v___x_851_ = v___x_845_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_849_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
else
{
lean_object* v_a_854_; lean_object* v___x_856_; 
lean_del_object(v___x_845_);
lean_dec(v_snd_836_);
v_a_854_ = lean_ctor_get(v_a_843_, 0);
lean_inc(v_a_854_);
lean_dec_ref_known(v_a_843_, 1);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 1, v_a_854_);
lean_ctor_set(v___x_838_, 0, v___x_840_);
v___x_856_ = v___x_838_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_840_);
lean_ctor_set(v_reuseFailAlloc_860_, 1, v_a_854_);
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
v_a_862_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_842_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_842_);
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
v___x_1001_ = lean_st_ref_put(v_a_986_, v___x_1000_);
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
lean_object* v___y_1067_; lean_object* v___x_1081_; 
v___x_1081_ = l_Lean_MVarId_getType(v_mvarId_1057_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v_a_1082_; lean_object* v___x_1083_; lean_object* v_a_1084_; lean_object* v___x_1085_; 
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
lean_inc(v_a_1082_);
lean_dec_ref_known(v___x_1081_, 1);
v___x_1083_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0___redArg(v_a_1082_, v_a_1062_);
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
lean_inc(v_a_1084_);
lean_dec_ref(v___x_1083_);
v___x_1085_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars(v_a_1084_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v___x_1086_; lean_object* v___x_1087_; uint8_t v___x_1088_; 
lean_dec_ref_known(v___x_1085_, 1);
v___x_1086_ = lean_unsigned_to_nat(0u);
v___x_1087_ = lean_array_get_size(v_toPreserve_1058_);
v___x_1088_ = lean_nat_dec_lt(v___x_1086_, v___x_1087_);
if (v___x_1088_ == 0)
{
goto v___jp_1071_;
}
else
{
lean_object* v___x_1089_; size_t v___x_1090_; size_t v___x_1091_; lean_object* v___x_1092_; 
v___x_1089_ = lean_box(0);
v___x_1090_ = ((size_t)0ULL);
v___x_1091_ = lean_usize_of_nat(v___x_1087_);
v___x_1092_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed_spec__0(v_toPreserve_1058_, v___x_1090_, v___x_1091_, v___x_1089_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_dec_ref_known(v___x_1092_, 1);
goto v___jp_1071_;
}
else
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1100_; 
v_a_1093_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1095_ = v___x_1092_;
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1092_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1098_; 
if (v_isShared_1096_ == 0)
{
v___x_1098_ = v___x_1095_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_a_1093_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
}
}
else
{
lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
v_a_1101_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1103_ = v___x_1085_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___x_1085_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1101_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
}
else
{
lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1116_; 
v_a_1109_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1111_ = v___x_1081_;
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v___x_1081_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1114_; 
if (v_isShared_1112_ == 0)
{
v___x_1114_ = v___x_1111_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_a_1109_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed___boxed(lean_object* v_mvarId_1117_, lean_object* v_toPreserve_1118_, lean_object* v_indirectProps_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_){
_start:
{
uint8_t v_indirectProps_boxed_1126_; lean_object* v_res_1127_; 
v_indirectProps_boxed_1126_ = lean_unbox(v_indirectProps_1119_);
v_res_1127_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed(v_mvarId_1117_, v_toPreserve_1118_, v_indirectProps_boxed_1126_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_);
lean_dec(v_a_1124_);
lean_dec_ref(v_a_1123_);
lean_dec(v_a_1122_);
lean_dec_ref(v_a_1121_);
lean_dec(v_a_1120_);
lean_dec_ref(v_toPreserve_1118_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___redArg(lean_object* v_e_1128_, lean_object* v___y_1129_){
_start:
{
uint8_t v___x_1131_; 
v___x_1131_ = l_Lean_Expr_hasMVar(v_e_1128_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; 
v___x_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1132_, 0, v_e_1128_);
return v___x_1132_;
}
else
{
lean_object* v___x_1133_; lean_object* v_mctx_1134_; lean_object* v___x_1135_; lean_object* v_fst_1136_; lean_object* v_snd_1137_; lean_object* v___x_1138_; lean_object* v_cache_1139_; lean_object* v_zetaDeltaFVarIds_1140_; lean_object* v_postponed_1141_; lean_object* v_diag_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1151_; 
v___x_1133_ = lean_st_ref_get(v___y_1129_);
v_mctx_1134_ = lean_ctor_get(v___x_1133_, 0);
lean_inc_ref(v_mctx_1134_);
lean_dec(v___x_1133_);
v___x_1135_ = l_Lean_instantiateMVarsCore(v_mctx_1134_, v_e_1128_);
v_fst_1136_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_fst_1136_);
v_snd_1137_ = lean_ctor_get(v___x_1135_, 1);
lean_inc(v_snd_1137_);
lean_dec_ref(v___x_1135_);
v___x_1138_ = lean_st_ref_take(v___y_1129_);
v_cache_1139_ = lean_ctor_get(v___x_1138_, 1);
v_zetaDeltaFVarIds_1140_ = lean_ctor_get(v___x_1138_, 2);
v_postponed_1141_ = lean_ctor_get(v___x_1138_, 3);
v_diag_1142_ = lean_ctor_get(v___x_1138_, 4);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1151_ == 0)
{
lean_object* v_unused_1152_; 
v_unused_1152_ = lean_ctor_get(v___x_1138_, 0);
lean_dec(v_unused_1152_);
v___x_1144_ = v___x_1138_;
v_isShared_1145_ = v_isSharedCheck_1151_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_diag_1142_);
lean_inc(v_postponed_1141_);
lean_inc(v_zetaDeltaFVarIds_1140_);
lean_inc(v_cache_1139_);
lean_dec(v___x_1138_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1151_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1147_; 
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 0, v_snd_1137_);
v___x_1147_ = v___x_1144_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_snd_1137_);
lean_ctor_set(v_reuseFailAlloc_1150_, 1, v_cache_1139_);
lean_ctor_set(v_reuseFailAlloc_1150_, 2, v_zetaDeltaFVarIds_1140_);
lean_ctor_set(v_reuseFailAlloc_1150_, 3, v_postponed_1141_);
lean_ctor_set(v_reuseFailAlloc_1150_, 4, v_diag_1142_);
v___x_1147_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1148_ = lean_st_ref_put(v___y_1129_, v___x_1147_);
v___x_1149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1149_, 0, v_fst_1136_);
return v___x_1149_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___redArg___boxed(lean_object* v_e_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___redArg(v_e_1153_, v___y_1154_);
lean_dec(v___y_1154_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1(lean_object* v_e_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
lean_object* v___x_1163_; 
v___x_1163_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___redArg(v_e_1157_, v___y_1159_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___boxed(lean_object* v_e_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1(v_e_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___redArg(lean_object* v_mvarId_1171_, lean_object* v_x_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1171_, v_x_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1186_; 
v_a_1179_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1181_ = v___x_1178_;
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v___x_1178_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1184_; 
if (v_isShared_1182_ == 0)
{
v___x_1184_ = v___x_1181_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_a_1179_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
else
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1194_; 
v_a_1187_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1189_ = v___x_1178_;
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1178_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1192_; 
if (v_isShared_1190_ == 0)
{
v___x_1192_ = v___x_1189_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_a_1187_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___redArg___boxed(lean_object* v_mvarId_1195_, lean_object* v_x_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___redArg(v_mvarId_1195_, v_x_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4(lean_object* v_00_u03b1_1203_, lean_object* v_mvarId_1204_, lean_object* v_x_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v___x_1211_; 
v___x_1211_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___redArg(v_mvarId_1204_, v_x_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___boxed(lean_object* v_00_u03b1_1212_, lean_object* v_mvarId_1213_, lean_object* v_x_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4(v_00_u03b1_1212_, v_mvarId_1213_, v_x_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__3(lean_object* v_a_1221_, lean_object* v_as_1222_, size_t v_i_1223_, size_t v_stop_1224_, lean_object* v_b_1225_){
_start:
{
lean_object* v___y_1227_; uint8_t v___x_1231_; 
v___x_1231_ = lean_usize_dec_eq(v_i_1223_, v_stop_1224_);
if (v___x_1231_ == 0)
{
lean_object* v___x_1232_; lean_object* v_fvar_1233_; lean_object* v___x_1234_; uint8_t v___x_1235_; 
v___x_1232_ = lean_array_uget_borrowed(v_as_1222_, v_i_1223_);
v_fvar_1233_ = lean_ctor_get(v___x_1232_, 1);
v___x_1234_ = l_Lean_Expr_fvarId_x21(v_fvar_1233_);
v___x_1235_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_1234_, v_a_1221_);
lean_dec(v___x_1234_);
if (v___x_1235_ == 0)
{
v___y_1227_ = v_b_1225_;
goto v___jp_1226_;
}
else
{
lean_object* v___x_1236_; 
lean_inc(v___x_1232_);
v___x_1236_ = lean_array_push(v_b_1225_, v___x_1232_);
v___y_1227_ = v___x_1236_;
goto v___jp_1226_;
}
}
else
{
return v_b_1225_;
}
v___jp_1226_:
{
size_t v___x_1228_; size_t v___x_1229_; 
v___x_1228_ = ((size_t)1ULL);
v___x_1229_ = lean_usize_add(v_i_1223_, v___x_1228_);
v_i_1223_ = v___x_1229_;
v_b_1225_ = v___y_1227_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__3___boxed(lean_object* v_a_1237_, lean_object* v_as_1238_, lean_object* v_i_1239_, lean_object* v_stop_1240_, lean_object* v_b_1241_){
_start:
{
size_t v_i_boxed_1242_; size_t v_stop_boxed_1243_; lean_object* v_res_1244_; 
v_i_boxed_1242_ = lean_unbox_usize(v_i_1239_);
lean_dec(v_i_1239_);
v_stop_boxed_1243_ = lean_unbox_usize(v_stop_1240_);
lean_dec(v_stop_1240_);
v_res_1244_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__3(v_a_1237_, v_as_1238_, v_i_boxed_1242_, v_stop_boxed_1243_, v_b_1241_);
lean_dec_ref(v_as_1238_);
lean_dec(v_a_1237_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12_spec__13___redArg(lean_object* v_x_1245_, lean_object* v_x_1246_, lean_object* v_x_1247_, lean_object* v_x_1248_){
_start:
{
lean_object* v_ks_1249_; lean_object* v_vs_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1274_; 
v_ks_1249_ = lean_ctor_get(v_x_1245_, 0);
v_vs_1250_ = lean_ctor_get(v_x_1245_, 1);
v_isSharedCheck_1274_ = !lean_is_exclusive(v_x_1245_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1252_ = v_x_1245_;
v_isShared_1253_ = v_isSharedCheck_1274_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_vs_1250_);
lean_inc(v_ks_1249_);
lean_dec(v_x_1245_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1274_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1254_; uint8_t v___x_1255_; 
v___x_1254_ = lean_array_get_size(v_ks_1249_);
v___x_1255_ = lean_nat_dec_lt(v_x_1246_, v___x_1254_);
if (v___x_1255_ == 0)
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1259_; 
lean_dec(v_x_1246_);
v___x_1256_ = lean_array_push(v_ks_1249_, v_x_1247_);
v___x_1257_ = lean_array_push(v_vs_1250_, v_x_1248_);
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 1, v___x_1257_);
lean_ctor_set(v___x_1252_, 0, v___x_1256_);
v___x_1259_ = v___x_1252_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1256_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v___x_1257_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
else
{
lean_object* v_k_x27_1261_; uint8_t v___x_1262_; 
v_k_x27_1261_ = lean_array_fget_borrowed(v_ks_1249_, v_x_1246_);
v___x_1262_ = l_Lean_instBEqMVarId_beq(v_x_1247_, v_k_x27_1261_);
if (v___x_1262_ == 0)
{
lean_object* v___x_1264_; 
if (v_isShared_1253_ == 0)
{
v___x_1264_ = v___x_1252_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_ks_1249_);
lean_ctor_set(v_reuseFailAlloc_1268_, 1, v_vs_1250_);
v___x_1264_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1265_ = lean_unsigned_to_nat(1u);
v___x_1266_ = lean_nat_add(v_x_1246_, v___x_1265_);
lean_dec(v_x_1246_);
v_x_1245_ = v___x_1264_;
v_x_1246_ = v___x_1266_;
goto _start;
}
}
else
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1272_; 
v___x_1269_ = lean_array_fset(v_ks_1249_, v_x_1246_, v_x_1247_);
v___x_1270_ = lean_array_fset(v_vs_1250_, v_x_1246_, v_x_1248_);
lean_dec(v_x_1246_);
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 1, v___x_1270_);
lean_ctor_set(v___x_1252_, 0, v___x_1269_);
v___x_1272_ = v___x_1252_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v___x_1269_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v___x_1270_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12___redArg(lean_object* v_n_1275_, lean_object* v_k_1276_, lean_object* v_v_1277_){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1278_ = lean_unsigned_to_nat(0u);
v___x_1279_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12_spec__13___redArg(v_n_1275_, v___x_1278_, v_k_1276_, v_v_1277_);
return v___x_1279_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1280_; 
v___x_1280_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg(lean_object* v_x_1281_, size_t v_x_1282_, size_t v_x_1283_, lean_object* v_x_1284_, lean_object* v_x_1285_){
_start:
{
if (lean_obj_tag(v_x_1281_) == 0)
{
lean_object* v_es_1286_; size_t v___x_1287_; size_t v___x_1288_; lean_object* v_j_1289_; lean_object* v___x_1290_; uint8_t v___x_1291_; 
v_es_1286_ = lean_ctor_get(v_x_1281_, 0);
v___x_1287_ = ((size_t)31ULL);
v___x_1288_ = lean_usize_land(v_x_1282_, v___x_1287_);
v_j_1289_ = lean_usize_to_nat(v___x_1288_);
v___x_1290_ = lean_array_get_size(v_es_1286_);
v___x_1291_ = lean_nat_dec_lt(v_j_1289_, v___x_1290_);
if (v___x_1291_ == 0)
{
lean_dec(v_j_1289_);
lean_dec(v_x_1285_);
lean_dec(v_x_1284_);
return v_x_1281_;
}
else
{
lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1330_; 
lean_inc_ref(v_es_1286_);
v_isSharedCheck_1330_ = !lean_is_exclusive(v_x_1281_);
if (v_isSharedCheck_1330_ == 0)
{
lean_object* v_unused_1331_; 
v_unused_1331_ = lean_ctor_get(v_x_1281_, 0);
lean_dec(v_unused_1331_);
v___x_1293_ = v_x_1281_;
v_isShared_1294_ = v_isSharedCheck_1330_;
goto v_resetjp_1292_;
}
else
{
lean_dec(v_x_1281_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1330_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v_v_1295_; lean_object* v___x_1296_; lean_object* v_xs_x27_1297_; lean_object* v___y_1299_; 
v_v_1295_ = lean_array_fget(v_es_1286_, v_j_1289_);
v___x_1296_ = lean_box(0);
v_xs_x27_1297_ = lean_array_fset(v_es_1286_, v_j_1289_, v___x_1296_);
switch(lean_obj_tag(v_v_1295_))
{
case 0:
{
lean_object* v_key_1304_; lean_object* v_val_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1315_; 
v_key_1304_ = lean_ctor_get(v_v_1295_, 0);
v_val_1305_ = lean_ctor_get(v_v_1295_, 1);
v_isSharedCheck_1315_ = !lean_is_exclusive(v_v_1295_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1307_ = v_v_1295_;
v_isShared_1308_ = v_isSharedCheck_1315_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_val_1305_);
lean_inc(v_key_1304_);
lean_dec(v_v_1295_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1315_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
uint8_t v___x_1309_; 
v___x_1309_ = l_Lean_instBEqMVarId_beq(v_x_1284_, v_key_1304_);
if (v___x_1309_ == 0)
{
lean_object* v___x_1310_; lean_object* v___x_1311_; 
lean_del_object(v___x_1307_);
v___x_1310_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1304_, v_val_1305_, v_x_1284_, v_x_1285_);
v___x_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1310_);
v___y_1299_ = v___x_1311_;
goto v___jp_1298_;
}
else
{
lean_object* v___x_1313_; 
lean_dec(v_val_1305_);
lean_dec(v_key_1304_);
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 1, v_x_1285_);
lean_ctor_set(v___x_1307_, 0, v_x_1284_);
v___x_1313_ = v___x_1307_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v_x_1284_);
lean_ctor_set(v_reuseFailAlloc_1314_, 1, v_x_1285_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
v___y_1299_ = v___x_1313_;
goto v___jp_1298_;
}
}
}
}
case 1:
{
lean_object* v_node_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1328_; 
v_node_1316_ = lean_ctor_get(v_v_1295_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v_v_1295_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1318_ = v_v_1295_;
v_isShared_1319_ = v_isSharedCheck_1328_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_node_1316_);
lean_dec(v_v_1295_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1328_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
size_t v___x_1320_; size_t v___x_1321_; size_t v___x_1322_; size_t v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1326_; 
v___x_1320_ = ((size_t)5ULL);
v___x_1321_ = lean_usize_shift_right(v_x_1282_, v___x_1320_);
v___x_1322_ = ((size_t)1ULL);
v___x_1323_ = lean_usize_add(v_x_1283_, v___x_1322_);
v___x_1324_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg(v_node_1316_, v___x_1321_, v___x_1323_, v_x_1284_, v_x_1285_);
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 0, v___x_1324_);
v___x_1326_ = v___x_1318_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v___x_1324_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
v___y_1299_ = v___x_1326_;
goto v___jp_1298_;
}
}
}
default: 
{
lean_object* v___x_1329_; 
v___x_1329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1329_, 0, v_x_1284_);
lean_ctor_set(v___x_1329_, 1, v_x_1285_);
v___y_1299_ = v___x_1329_;
goto v___jp_1298_;
}
}
v___jp_1298_:
{
lean_object* v___x_1300_; lean_object* v___x_1302_; 
v___x_1300_ = lean_array_fset(v_xs_x27_1297_, v_j_1289_, v___y_1299_);
lean_dec(v_j_1289_);
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 0, v___x_1300_);
v___x_1302_ = v___x_1293_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v___x_1300_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
}
}
else
{
lean_object* v_ks_1332_; lean_object* v_vs_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1351_; 
v_ks_1332_ = lean_ctor_get(v_x_1281_, 0);
v_vs_1333_ = lean_ctor_get(v_x_1281_, 1);
v_isSharedCheck_1351_ = !lean_is_exclusive(v_x_1281_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1335_ = v_x_1281_;
v_isShared_1336_ = v_isSharedCheck_1351_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_vs_1333_);
lean_inc(v_ks_1332_);
lean_dec(v_x_1281_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1351_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_ks_1332_);
lean_ctor_set(v_reuseFailAlloc_1350_, 1, v_vs_1333_);
v___x_1338_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
lean_object* v_newNode_1339_; size_t v___x_1340_; uint8_t v___x_1341_; 
v_newNode_1339_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12___redArg(v___x_1338_, v_x_1284_, v_x_1285_);
v___x_1340_ = ((size_t)7ULL);
v___x_1341_ = lean_usize_dec_le(v___x_1340_, v_x_1283_);
if (v___x_1341_ == 0)
{
lean_object* v___x_1342_; lean_object* v___x_1343_; uint8_t v___x_1344_; 
v___x_1342_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1339_);
v___x_1343_ = lean_unsigned_to_nat(4u);
v___x_1344_ = lean_nat_dec_lt(v___x_1342_, v___x_1343_);
lean_dec(v___x_1342_);
if (v___x_1344_ == 0)
{
lean_object* v_ks_1345_; lean_object* v_vs_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v_ks_1345_ = lean_ctor_get(v_newNode_1339_, 0);
lean_inc_ref(v_ks_1345_);
v_vs_1346_ = lean_ctor_get(v_newNode_1339_, 1);
lean_inc_ref(v_vs_1346_);
lean_dec_ref(v_newNode_1339_);
v___x_1347_ = lean_unsigned_to_nat(0u);
v___x_1348_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__0);
v___x_1349_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___redArg(v_x_1283_, v_ks_1345_, v_vs_1346_, v___x_1347_, v___x_1348_);
lean_dec_ref(v_vs_1346_);
lean_dec_ref(v_ks_1345_);
return v___x_1349_;
}
else
{
return v_newNode_1339_;
}
}
else
{
return v_newNode_1339_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___redArg(size_t v_depth_1352_, lean_object* v_keys_1353_, lean_object* v_vals_1354_, lean_object* v_i_1355_, lean_object* v_entries_1356_){
_start:
{
lean_object* v___x_1357_; uint8_t v___x_1358_; 
v___x_1357_ = lean_array_get_size(v_keys_1353_);
v___x_1358_ = lean_nat_dec_lt(v_i_1355_, v___x_1357_);
if (v___x_1358_ == 0)
{
lean_dec(v_i_1355_);
return v_entries_1356_;
}
else
{
lean_object* v_k_1359_; lean_object* v_v_1360_; uint64_t v___x_1361_; size_t v_h_1362_; size_t v___x_1363_; lean_object* v___x_1364_; size_t v___x_1365_; size_t v___x_1366_; size_t v___x_1367_; size_t v_h_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; 
v_k_1359_ = lean_array_fget_borrowed(v_keys_1353_, v_i_1355_);
v_v_1360_ = lean_array_fget_borrowed(v_vals_1354_, v_i_1355_);
v___x_1361_ = l_Lean_instHashableMVarId_hash(v_k_1359_);
v_h_1362_ = lean_uint64_to_usize(v___x_1361_);
v___x_1363_ = ((size_t)5ULL);
v___x_1364_ = lean_unsigned_to_nat(1u);
v___x_1365_ = ((size_t)1ULL);
v___x_1366_ = lean_usize_sub(v_depth_1352_, v___x_1365_);
v___x_1367_ = lean_usize_mul(v___x_1363_, v___x_1366_);
v_h_1368_ = lean_usize_shift_right(v_h_1362_, v___x_1367_);
v___x_1369_ = lean_nat_add(v_i_1355_, v___x_1364_);
lean_dec(v_i_1355_);
lean_inc(v_v_1360_);
lean_inc(v_k_1359_);
v___x_1370_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg(v_entries_1356_, v_h_1368_, v_depth_1352_, v_k_1359_, v_v_1360_);
v_i_1355_ = v___x_1369_;
v_entries_1356_ = v___x_1370_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___redArg___boxed(lean_object* v_depth_1372_, lean_object* v_keys_1373_, lean_object* v_vals_1374_, lean_object* v_i_1375_, lean_object* v_entries_1376_){
_start:
{
size_t v_depth_boxed_1377_; lean_object* v_res_1378_; 
v_depth_boxed_1377_ = lean_unbox_usize(v_depth_1372_);
lean_dec(v_depth_1372_);
v_res_1378_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___redArg(v_depth_boxed_1377_, v_keys_1373_, v_vals_1374_, v_i_1375_, v_entries_1376_);
lean_dec_ref(v_vals_1374_);
lean_dec_ref(v_keys_1373_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___boxed(lean_object* v_x_1379_, lean_object* v_x_1380_, lean_object* v_x_1381_, lean_object* v_x_1382_, lean_object* v_x_1383_){
_start:
{
size_t v_x_7412__boxed_1384_; size_t v_x_7413__boxed_1385_; lean_object* v_res_1386_; 
v_x_7412__boxed_1384_ = lean_unbox_usize(v_x_1380_);
lean_dec(v_x_1380_);
v_x_7413__boxed_1385_ = lean_unbox_usize(v_x_1381_);
lean_dec(v_x_1381_);
v_res_1386_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg(v_x_1379_, v_x_7412__boxed_1384_, v_x_7413__boxed_1385_, v_x_1382_, v_x_1383_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4___redArg(lean_object* v_x_1387_, lean_object* v_x_1388_, lean_object* v_x_1389_){
_start:
{
uint64_t v___x_1390_; size_t v___x_1391_; size_t v___x_1392_; lean_object* v___x_1393_; 
v___x_1390_ = l_Lean_instHashableMVarId_hash(v_x_1388_);
v___x_1391_ = lean_uint64_to_usize(v___x_1390_);
v___x_1392_ = ((size_t)1ULL);
v___x_1393_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg(v_x_1387_, v___x_1391_, v___x_1392_, v_x_1388_, v_x_1389_);
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___redArg(lean_object* v_mvarId_1394_, lean_object* v_val_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v___x_1398_; lean_object* v_mctx_1399_; lean_object* v_cache_1400_; lean_object* v_zetaDeltaFVarIds_1401_; lean_object* v_postponed_1402_; lean_object* v_diag_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1433_; 
v___x_1398_ = lean_st_ref_take(v___y_1396_);
v_mctx_1399_ = lean_ctor_get(v___x_1398_, 0);
v_cache_1400_ = lean_ctor_get(v___x_1398_, 1);
v_zetaDeltaFVarIds_1401_ = lean_ctor_get(v___x_1398_, 2);
v_postponed_1402_ = lean_ctor_get(v___x_1398_, 3);
v_diag_1403_ = lean_ctor_get(v___x_1398_, 4);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1405_ = v___x_1398_;
v_isShared_1406_ = v_isSharedCheck_1433_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_diag_1403_);
lean_inc(v_postponed_1402_);
lean_inc(v_zetaDeltaFVarIds_1401_);
lean_inc(v_cache_1400_);
lean_inc(v_mctx_1399_);
lean_dec(v___x_1398_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1433_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v_depth_1407_; lean_object* v_levelAssignDepth_1408_; lean_object* v_lmvarCounter_1409_; lean_object* v_mvarCounter_1410_; lean_object* v_lDecls_1411_; lean_object* v_decls_1412_; lean_object* v_userNames_1413_; lean_object* v_lAssignment_1414_; lean_object* v_eAssignment_1415_; lean_object* v_dAssignment_1416_; lean_object* v_instanceTypedMVars_1417_; lean_object* v_synthNormMemo_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1432_; 
v_depth_1407_ = lean_ctor_get(v_mctx_1399_, 0);
v_levelAssignDepth_1408_ = lean_ctor_get(v_mctx_1399_, 1);
v_lmvarCounter_1409_ = lean_ctor_get(v_mctx_1399_, 2);
v_mvarCounter_1410_ = lean_ctor_get(v_mctx_1399_, 3);
v_lDecls_1411_ = lean_ctor_get(v_mctx_1399_, 4);
v_decls_1412_ = lean_ctor_get(v_mctx_1399_, 5);
v_userNames_1413_ = lean_ctor_get(v_mctx_1399_, 6);
v_lAssignment_1414_ = lean_ctor_get(v_mctx_1399_, 7);
v_eAssignment_1415_ = lean_ctor_get(v_mctx_1399_, 8);
v_dAssignment_1416_ = lean_ctor_get(v_mctx_1399_, 9);
v_instanceTypedMVars_1417_ = lean_ctor_get(v_mctx_1399_, 10);
v_synthNormMemo_1418_ = lean_ctor_get(v_mctx_1399_, 11);
v_isSharedCheck_1432_ = !lean_is_exclusive(v_mctx_1399_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1420_ = v_mctx_1399_;
v_isShared_1421_ = v_isSharedCheck_1432_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_synthNormMemo_1418_);
lean_inc(v_instanceTypedMVars_1417_);
lean_inc(v_dAssignment_1416_);
lean_inc(v_eAssignment_1415_);
lean_inc(v_lAssignment_1414_);
lean_inc(v_userNames_1413_);
lean_inc(v_decls_1412_);
lean_inc(v_lDecls_1411_);
lean_inc(v_mvarCounter_1410_);
lean_inc(v_lmvarCounter_1409_);
lean_inc(v_levelAssignDepth_1408_);
lean_inc(v_depth_1407_);
lean_dec(v_mctx_1399_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1432_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1425_; 
v___x_1422_ = lean_box(0);
v___x_1423_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4___redArg(v_eAssignment_1415_, v_mvarId_1394_, v_val_1395_);
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 8, v___x_1423_);
v___x_1425_ = v___x_1420_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_depth_1407_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v_levelAssignDepth_1408_);
lean_ctor_set(v_reuseFailAlloc_1431_, 2, v_lmvarCounter_1409_);
lean_ctor_set(v_reuseFailAlloc_1431_, 3, v_mvarCounter_1410_);
lean_ctor_set(v_reuseFailAlloc_1431_, 4, v_lDecls_1411_);
lean_ctor_set(v_reuseFailAlloc_1431_, 5, v_decls_1412_);
lean_ctor_set(v_reuseFailAlloc_1431_, 6, v_userNames_1413_);
lean_ctor_set(v_reuseFailAlloc_1431_, 7, v_lAssignment_1414_);
lean_ctor_set(v_reuseFailAlloc_1431_, 8, v___x_1423_);
lean_ctor_set(v_reuseFailAlloc_1431_, 9, v_dAssignment_1416_);
lean_ctor_set(v_reuseFailAlloc_1431_, 10, v_instanceTypedMVars_1417_);
lean_ctor_set(v_reuseFailAlloc_1431_, 11, v_synthNormMemo_1418_);
v___x_1425_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
lean_object* v___x_1427_; 
if (v_isShared_1406_ == 0)
{
lean_ctor_set(v___x_1405_, 0, v___x_1425_);
v___x_1427_ = v___x_1405_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v___x_1425_);
lean_ctor_set(v_reuseFailAlloc_1430_, 1, v_cache_1400_);
lean_ctor_set(v_reuseFailAlloc_1430_, 2, v_zetaDeltaFVarIds_1401_);
lean_ctor_set(v_reuseFailAlloc_1430_, 3, v_postponed_1402_);
lean_ctor_set(v_reuseFailAlloc_1430_, 4, v_diag_1403_);
v___x_1427_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1428_ = lean_st_ref_put(v___y_1396_, v___x_1427_);
v___x_1429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1422_);
return v___x_1429_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___redArg___boxed(lean_object* v_mvarId_1434_, lean_object* v_val_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_){
_start:
{
lean_object* v_res_1438_; 
v_res_1438_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___redArg(v_mvarId_1434_, v_val_1435_, v___y_1436_);
lean_dec(v___y_1436_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___redArg(lean_object* v_a_1439_, lean_object* v_as_1440_, size_t v_sz_1441_, size_t v_i_1442_, lean_object* v_b_1443_){
_start:
{
uint8_t v___x_1445_; 
v___x_1445_ = lean_usize_dec_lt(v_i_1442_, v_sz_1441_);
if (v___x_1445_ == 0)
{
lean_object* v___x_1446_; 
v___x_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1446_, 0, v_b_1443_);
return v___x_1446_;
}
else
{
lean_object* v_snd_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1465_; 
v_snd_1447_ = lean_ctor_get(v_b_1443_, 1);
v_isSharedCheck_1465_ = !lean_is_exclusive(v_b_1443_);
if (v_isSharedCheck_1465_ == 0)
{
lean_object* v_unused_1466_; 
v_unused_1466_ = lean_ctor_get(v_b_1443_, 0);
lean_dec(v_unused_1466_);
v___x_1449_ = v_b_1443_;
v_isShared_1450_ = v_isSharedCheck_1465_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_snd_1447_);
lean_dec(v_b_1443_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1465_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1451_; lean_object* v_a_1453_; lean_object* v_a_1460_; 
v___x_1451_ = lean_box(0);
v_a_1460_ = lean_array_uget_borrowed(v_as_1440_, v_i_1442_);
if (lean_obj_tag(v_a_1460_) == 0)
{
v_a_1453_ = v_snd_1447_;
goto v___jp_1452_;
}
else
{
lean_object* v_val_1461_; lean_object* v___x_1462_; uint8_t v___x_1463_; 
v_val_1461_ = lean_ctor_get(v_a_1460_, 0);
v___x_1462_ = l_Lean_LocalDecl_fvarId(v_val_1461_);
v___x_1463_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_1462_, v_a_1439_);
if (v___x_1463_ == 0)
{
lean_object* v___x_1464_; 
v___x_1464_ = l_Lean_LocalContext_erase(v_snd_1447_, v___x_1462_);
lean_dec(v___x_1462_);
v_a_1453_ = v___x_1464_;
goto v___jp_1452_;
}
else
{
lean_dec(v___x_1462_);
v_a_1453_ = v_snd_1447_;
goto v___jp_1452_;
}
}
v___jp_1452_:
{
lean_object* v___x_1455_; 
if (v_isShared_1450_ == 0)
{
lean_ctor_set(v___x_1449_, 1, v_a_1453_);
lean_ctor_set(v___x_1449_, 0, v___x_1451_);
v___x_1455_ = v___x_1449_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1451_);
lean_ctor_set(v_reuseFailAlloc_1459_, 1, v_a_1453_);
v___x_1455_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
size_t v___x_1456_; size_t v___x_1457_; 
v___x_1456_ = ((size_t)1ULL);
v___x_1457_ = lean_usize_add(v_i_1442_, v___x_1456_);
v_i_1442_ = v___x_1457_;
v_b_1443_ = v___x_1455_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___redArg___boxed(lean_object* v_a_1467_, lean_object* v_as_1468_, lean_object* v_sz_1469_, lean_object* v_i_1470_, lean_object* v_b_1471_, lean_object* v___y_1472_){
_start:
{
size_t v_sz_boxed_1473_; size_t v_i_boxed_1474_; lean_object* v_res_1475_; 
v_sz_boxed_1473_ = lean_unbox_usize(v_sz_1469_);
lean_dec(v_sz_1469_);
v_i_boxed_1474_ = lean_unbox_usize(v_i_1470_);
lean_dec(v_i_1470_);
v_res_1475_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___redArg(v_a_1467_, v_as_1468_, v_sz_boxed_1473_, v_i_boxed_1474_, v_b_1471_);
lean_dec_ref(v_as_1468_);
lean_dec(v_a_1467_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4(lean_object* v_a_1476_, lean_object* v_as_1477_, size_t v_sz_1478_, size_t v_i_1479_, lean_object* v_b_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_){
_start:
{
uint8_t v___x_1486_; 
v___x_1486_ = lean_usize_dec_lt(v_i_1479_, v_sz_1478_);
if (v___x_1486_ == 0)
{
lean_object* v___x_1487_; 
v___x_1487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1487_, 0, v_b_1480_);
return v___x_1487_;
}
else
{
lean_object* v_snd_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1506_; 
v_snd_1488_ = lean_ctor_get(v_b_1480_, 1);
v_isSharedCheck_1506_ = !lean_is_exclusive(v_b_1480_);
if (v_isSharedCheck_1506_ == 0)
{
lean_object* v_unused_1507_; 
v_unused_1507_ = lean_ctor_get(v_b_1480_, 0);
lean_dec(v_unused_1507_);
v___x_1490_ = v_b_1480_;
v_isShared_1491_ = v_isSharedCheck_1506_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_snd_1488_);
lean_dec(v_b_1480_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1506_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1492_; lean_object* v_a_1494_; lean_object* v_a_1501_; 
v___x_1492_ = lean_box(0);
v_a_1501_ = lean_array_uget_borrowed(v_as_1477_, v_i_1479_);
if (lean_obj_tag(v_a_1501_) == 0)
{
v_a_1494_ = v_snd_1488_;
goto v___jp_1493_;
}
else
{
lean_object* v_val_1502_; lean_object* v___x_1503_; uint8_t v___x_1504_; 
v_val_1502_ = lean_ctor_get(v_a_1501_, 0);
v___x_1503_ = l_Lean_LocalDecl_fvarId(v_val_1502_);
v___x_1504_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_1503_, v_a_1476_);
if (v___x_1504_ == 0)
{
lean_object* v___x_1505_; 
v___x_1505_ = l_Lean_LocalContext_erase(v_snd_1488_, v___x_1503_);
lean_dec(v___x_1503_);
v_a_1494_ = v___x_1505_;
goto v___jp_1493_;
}
else
{
lean_dec(v___x_1503_);
v_a_1494_ = v_snd_1488_;
goto v___jp_1493_;
}
}
v___jp_1493_:
{
lean_object* v___x_1496_; 
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 1, v_a_1494_);
lean_ctor_set(v___x_1490_, 0, v___x_1492_);
v___x_1496_ = v___x_1490_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1492_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v_a_1494_);
v___x_1496_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
size_t v___x_1497_; size_t v___x_1498_; lean_object* v___x_1499_; 
v___x_1497_ = ((size_t)1ULL);
v___x_1498_ = lean_usize_add(v_i_1479_, v___x_1497_);
v___x_1499_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___redArg(v_a_1476_, v_as_1477_, v_sz_1478_, v___x_1498_, v___x_1496_);
return v___x_1499_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4___boxed(lean_object* v_a_1508_, lean_object* v_as_1509_, lean_object* v_sz_1510_, lean_object* v_i_1511_, lean_object* v_b_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
size_t v_sz_boxed_1518_; size_t v_i_boxed_1519_; lean_object* v_res_1520_; 
v_sz_boxed_1518_ = lean_unbox_usize(v_sz_1510_);
lean_dec(v_sz_1510_);
v_i_boxed_1519_ = lean_unbox_usize(v_i_1511_);
lean_dec(v_i_1511_);
v_res_1520_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4(v_a_1508_, v_as_1509_, v_sz_boxed_1518_, v_i_boxed_1519_, v_b_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
lean_dec_ref(v_as_1509_);
lean_dec(v_a_1508_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0(lean_object* v_init_1521_, lean_object* v_a_1522_, lean_object* v_n_1523_, lean_object* v_b_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
if (lean_obj_tag(v_n_1523_) == 0)
{
lean_object* v_cs_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; size_t v_sz_1533_; size_t v___x_1534_; lean_object* v___x_1535_; 
v_cs_1530_ = lean_ctor_get(v_n_1523_, 0);
v___x_1531_ = lean_box(0);
v___x_1532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1531_);
lean_ctor_set(v___x_1532_, 1, v_b_1524_);
v_sz_1533_ = lean_array_size(v_cs_1530_);
v___x_1534_ = ((size_t)0ULL);
v___x_1535_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__3(v_init_1521_, v_a_1522_, v_cs_1530_, v_sz_1533_, v___x_1534_, v___x_1532_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v_a_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1550_; 
v_a_1536_ = lean_ctor_get(v___x_1535_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1538_ = v___x_1535_;
v_isShared_1539_ = v_isSharedCheck_1550_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_a_1536_);
lean_dec(v___x_1535_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1550_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v_fst_1540_; 
v_fst_1540_ = lean_ctor_get(v_a_1536_, 0);
if (lean_obj_tag(v_fst_1540_) == 0)
{
lean_object* v_snd_1541_; lean_object* v___x_1542_; lean_object* v___x_1544_; 
v_snd_1541_ = lean_ctor_get(v_a_1536_, 1);
lean_inc(v_snd_1541_);
lean_dec(v_a_1536_);
v___x_1542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1542_, 0, v_snd_1541_);
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 0, v___x_1542_);
v___x_1544_ = v___x_1538_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1542_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
else
{
lean_object* v_val_1546_; lean_object* v___x_1548_; 
lean_inc_ref(v_fst_1540_);
lean_dec(v_a_1536_);
v_val_1546_ = lean_ctor_get(v_fst_1540_, 0);
lean_inc(v_val_1546_);
lean_dec_ref_known(v_fst_1540_, 1);
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 0, v_val_1546_);
v___x_1548_ = v___x_1538_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_val_1546_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
}
else
{
lean_object* v_a_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1558_; 
v_a_1551_ = lean_ctor_get(v___x_1535_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1553_ = v___x_1535_;
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_a_1551_);
lean_dec(v___x_1535_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1556_; 
if (v_isShared_1554_ == 0)
{
v___x_1556_ = v___x_1553_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_a_1551_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
}
else
{
lean_object* v_vs_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; size_t v_sz_1562_; size_t v___x_1563_; lean_object* v___x_1564_; 
v_vs_1559_ = lean_ctor_get(v_n_1523_, 0);
v___x_1560_ = lean_box(0);
v___x_1561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1560_);
lean_ctor_set(v___x_1561_, 1, v_b_1524_);
v_sz_1562_ = lean_array_size(v_vs_1559_);
v___x_1563_ = ((size_t)0ULL);
v___x_1564_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4(v_a_1522_, v_vs_1559_, v_sz_1562_, v___x_1563_, v___x_1561_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1579_; 
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1567_ = v___x_1564_;
v_isShared_1568_ = v_isSharedCheck_1579_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1564_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1579_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v_fst_1569_; 
v_fst_1569_ = lean_ctor_get(v_a_1565_, 0);
if (lean_obj_tag(v_fst_1569_) == 0)
{
lean_object* v_snd_1570_; lean_object* v___x_1571_; lean_object* v___x_1573_; 
v_snd_1570_ = lean_ctor_get(v_a_1565_, 1);
lean_inc(v_snd_1570_);
lean_dec(v_a_1565_);
v___x_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1571_, 0, v_snd_1570_);
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 0, v___x_1571_);
v___x_1573_ = v___x_1567_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___x_1571_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
else
{
lean_object* v_val_1575_; lean_object* v___x_1577_; 
lean_inc_ref(v_fst_1569_);
lean_dec(v_a_1565_);
v_val_1575_ = lean_ctor_get(v_fst_1569_, 0);
lean_inc(v_val_1575_);
lean_dec_ref_known(v_fst_1569_, 1);
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 0, v_val_1575_);
v___x_1577_ = v___x_1567_;
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
v_a_1580_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1582_ = v___x_1564_;
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1564_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__3(lean_object* v_init_1588_, lean_object* v_a_1589_, lean_object* v_as_1590_, size_t v_sz_1591_, size_t v_i_1592_, lean_object* v_b_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
uint8_t v___x_1599_; 
v___x_1599_ = lean_usize_dec_lt(v_i_1592_, v_sz_1591_);
if (v___x_1599_ == 0)
{
lean_object* v___x_1600_; 
v___x_1600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1600_, 0, v_b_1593_);
return v___x_1600_;
}
else
{
lean_object* v_snd_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1635_; 
v_snd_1601_ = lean_ctor_get(v_b_1593_, 1);
v_isSharedCheck_1635_ = !lean_is_exclusive(v_b_1593_);
if (v_isSharedCheck_1635_ == 0)
{
lean_object* v_unused_1636_; 
v_unused_1636_ = lean_ctor_get(v_b_1593_, 0);
lean_dec(v_unused_1636_);
v___x_1603_ = v_b_1593_;
v_isShared_1604_ = v_isSharedCheck_1635_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_snd_1601_);
lean_dec(v_b_1593_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1635_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1605_; lean_object* v_a_1606_; lean_object* v___x_1607_; 
v___x_1605_ = lean_box(0);
v_a_1606_ = lean_array_uget_borrowed(v_as_1590_, v_i_1592_);
lean_inc(v_snd_1601_);
v___x_1607_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0(v_init_1588_, v_a_1589_, v_a_1606_, v_snd_1601_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v_a_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1626_; 
v_a_1608_ = lean_ctor_get(v___x_1607_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1610_ = v___x_1607_;
v_isShared_1611_ = v_isSharedCheck_1626_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_a_1608_);
lean_dec(v___x_1607_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1626_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
if (lean_obj_tag(v_a_1608_) == 0)
{
lean_object* v___x_1612_; lean_object* v___x_1614_; 
v___x_1612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1612_, 0, v_a_1608_);
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 0, v___x_1612_);
v___x_1614_ = v___x_1603_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v___x_1612_);
lean_ctor_set(v_reuseFailAlloc_1618_, 1, v_snd_1601_);
v___x_1614_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
lean_object* v___x_1616_; 
if (v_isShared_1611_ == 0)
{
lean_ctor_set(v___x_1610_, 0, v___x_1614_);
v___x_1616_ = v___x_1610_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v___x_1614_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
else
{
lean_object* v_a_1619_; lean_object* v___x_1621_; 
lean_del_object(v___x_1610_);
lean_dec(v_snd_1601_);
v_a_1619_ = lean_ctor_get(v_a_1608_, 0);
lean_inc(v_a_1619_);
lean_dec_ref_known(v_a_1608_, 1);
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 1, v_a_1619_);
lean_ctor_set(v___x_1603_, 0, v___x_1605_);
v___x_1621_ = v___x_1603_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v___x_1605_);
lean_ctor_set(v_reuseFailAlloc_1625_, 1, v_a_1619_);
v___x_1621_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
size_t v___x_1622_; size_t v___x_1623_; 
v___x_1622_ = ((size_t)1ULL);
v___x_1623_ = lean_usize_add(v_i_1592_, v___x_1622_);
v_i_1592_ = v___x_1623_;
v_b_1593_ = v___x_1621_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1634_; 
lean_del_object(v___x_1603_);
lean_dec(v_snd_1601_);
v_a_1627_ = lean_ctor_get(v___x_1607_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1629_ = v___x_1607_;
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_a_1627_);
lean_dec(v___x_1607_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1632_; 
if (v_isShared_1630_ == 0)
{
v___x_1632_ = v___x_1629_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_a_1627_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__3___boxed(lean_object* v_init_1637_, lean_object* v_a_1638_, lean_object* v_as_1639_, lean_object* v_sz_1640_, lean_object* v_i_1641_, lean_object* v_b_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_){
_start:
{
size_t v_sz_boxed_1648_; size_t v_i_boxed_1649_; lean_object* v_res_1650_; 
v_sz_boxed_1648_ = lean_unbox_usize(v_sz_1640_);
lean_dec(v_sz_1640_);
v_i_boxed_1649_ = lean_unbox_usize(v_i_1641_);
lean_dec(v_i_1641_);
v_res_1650_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__3(v_init_1637_, v_a_1638_, v_as_1639_, v_sz_boxed_1648_, v_i_boxed_1649_, v_b_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec_ref(v_as_1639_);
lean_dec(v_a_1638_);
lean_dec_ref(v_init_1637_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0___boxed(lean_object* v_init_1651_, lean_object* v_a_1652_, lean_object* v_n_1653_, lean_object* v_b_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0(v_init_1651_, v_a_1652_, v_n_1653_, v_b_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1655_);
lean_dec_ref(v_n_1653_);
lean_dec(v_a_1652_);
lean_dec_ref(v_init_1651_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___redArg(lean_object* v_a_1661_, lean_object* v_as_1662_, size_t v_sz_1663_, size_t v_i_1664_, lean_object* v_b_1665_){
_start:
{
uint8_t v___x_1667_; 
v___x_1667_ = lean_usize_dec_lt(v_i_1664_, v_sz_1663_);
if (v___x_1667_ == 0)
{
lean_object* v___x_1668_; 
v___x_1668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1668_, 0, v_b_1665_);
return v___x_1668_;
}
else
{
lean_object* v_snd_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1687_; 
v_snd_1669_ = lean_ctor_get(v_b_1665_, 1);
v_isSharedCheck_1687_ = !lean_is_exclusive(v_b_1665_);
if (v_isSharedCheck_1687_ == 0)
{
lean_object* v_unused_1688_; 
v_unused_1688_ = lean_ctor_get(v_b_1665_, 0);
lean_dec(v_unused_1688_);
v___x_1671_ = v_b_1665_;
v_isShared_1672_ = v_isSharedCheck_1687_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_snd_1669_);
lean_dec(v_b_1665_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1687_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1673_; lean_object* v_a_1675_; lean_object* v_a_1682_; 
v___x_1673_ = lean_box(0);
v_a_1682_ = lean_array_uget_borrowed(v_as_1662_, v_i_1664_);
if (lean_obj_tag(v_a_1682_) == 0)
{
v_a_1675_ = v_snd_1669_;
goto v___jp_1674_;
}
else
{
lean_object* v_val_1683_; lean_object* v___x_1684_; uint8_t v___x_1685_; 
v_val_1683_ = lean_ctor_get(v_a_1682_, 0);
v___x_1684_ = l_Lean_LocalDecl_fvarId(v_val_1683_);
v___x_1685_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_1684_, v_a_1661_);
if (v___x_1685_ == 0)
{
lean_object* v___x_1686_; 
v___x_1686_ = l_Lean_LocalContext_erase(v_snd_1669_, v___x_1684_);
lean_dec(v___x_1684_);
v_a_1675_ = v___x_1686_;
goto v___jp_1674_;
}
else
{
lean_dec(v___x_1684_);
v_a_1675_ = v_snd_1669_;
goto v___jp_1674_;
}
}
v___jp_1674_:
{
lean_object* v___x_1677_; 
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 1, v_a_1675_);
lean_ctor_set(v___x_1671_, 0, v___x_1673_);
v___x_1677_ = v___x_1671_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v___x_1673_);
lean_ctor_set(v_reuseFailAlloc_1681_, 1, v_a_1675_);
v___x_1677_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
size_t v___x_1678_; size_t v___x_1679_; 
v___x_1678_ = ((size_t)1ULL);
v___x_1679_ = lean_usize_add(v_i_1664_, v___x_1678_);
v_i_1664_ = v___x_1679_;
v_b_1665_ = v___x_1677_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___redArg___boxed(lean_object* v_a_1689_, lean_object* v_as_1690_, lean_object* v_sz_1691_, lean_object* v_i_1692_, lean_object* v_b_1693_, lean_object* v___y_1694_){
_start:
{
size_t v_sz_boxed_1695_; size_t v_i_boxed_1696_; lean_object* v_res_1697_; 
v_sz_boxed_1695_ = lean_unbox_usize(v_sz_1691_);
lean_dec(v_sz_1691_);
v_i_boxed_1696_ = lean_unbox_usize(v_i_1692_);
lean_dec(v_i_1692_);
v_res_1697_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___redArg(v_a_1689_, v_as_1690_, v_sz_boxed_1695_, v_i_boxed_1696_, v_b_1693_);
lean_dec_ref(v_as_1690_);
lean_dec(v_a_1689_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1(lean_object* v_a_1698_, lean_object* v_as_1699_, size_t v_sz_1700_, size_t v_i_1701_, lean_object* v_b_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
uint8_t v___x_1708_; 
v___x_1708_ = lean_usize_dec_lt(v_i_1701_, v_sz_1700_);
if (v___x_1708_ == 0)
{
lean_object* v___x_1709_; 
v___x_1709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1709_, 0, v_b_1702_);
return v___x_1709_;
}
else
{
lean_object* v_snd_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1728_; 
v_snd_1710_ = lean_ctor_get(v_b_1702_, 1);
v_isSharedCheck_1728_ = !lean_is_exclusive(v_b_1702_);
if (v_isSharedCheck_1728_ == 0)
{
lean_object* v_unused_1729_; 
v_unused_1729_ = lean_ctor_get(v_b_1702_, 0);
lean_dec(v_unused_1729_);
v___x_1712_ = v_b_1702_;
v_isShared_1713_ = v_isSharedCheck_1728_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_snd_1710_);
lean_dec(v_b_1702_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1728_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1714_; lean_object* v_a_1716_; lean_object* v_a_1723_; 
v___x_1714_ = lean_box(0);
v_a_1723_ = lean_array_uget_borrowed(v_as_1699_, v_i_1701_);
if (lean_obj_tag(v_a_1723_) == 0)
{
v_a_1716_ = v_snd_1710_;
goto v___jp_1715_;
}
else
{
lean_object* v_val_1724_; lean_object* v___x_1725_; uint8_t v___x_1726_; 
v_val_1724_ = lean_ctor_get(v_a_1723_, 0);
v___x_1725_ = l_Lean_LocalDecl_fvarId(v_val_1724_);
v___x_1726_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_1725_, v_a_1698_);
if (v___x_1726_ == 0)
{
lean_object* v___x_1727_; 
v___x_1727_ = l_Lean_LocalContext_erase(v_snd_1710_, v___x_1725_);
lean_dec(v___x_1725_);
v_a_1716_ = v___x_1727_;
goto v___jp_1715_;
}
else
{
lean_dec(v___x_1725_);
v_a_1716_ = v_snd_1710_;
goto v___jp_1715_;
}
}
v___jp_1715_:
{
lean_object* v___x_1718_; 
if (v_isShared_1713_ == 0)
{
lean_ctor_set(v___x_1712_, 1, v_a_1716_);
lean_ctor_set(v___x_1712_, 0, v___x_1714_);
v___x_1718_ = v___x_1712_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v___x_1714_);
lean_ctor_set(v_reuseFailAlloc_1722_, 1, v_a_1716_);
v___x_1718_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
size_t v___x_1719_; size_t v___x_1720_; lean_object* v___x_1721_; 
v___x_1719_ = ((size_t)1ULL);
v___x_1720_ = lean_usize_add(v_i_1701_, v___x_1719_);
v___x_1721_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___redArg(v_a_1698_, v_as_1699_, v_sz_1700_, v___x_1720_, v___x_1718_);
return v___x_1721_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1___boxed(lean_object* v_a_1730_, lean_object* v_as_1731_, lean_object* v_sz_1732_, lean_object* v_i_1733_, lean_object* v_b_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
size_t v_sz_boxed_1740_; size_t v_i_boxed_1741_; lean_object* v_res_1742_; 
v_sz_boxed_1740_ = lean_unbox_usize(v_sz_1732_);
lean_dec(v_sz_1732_);
v_i_boxed_1741_ = lean_unbox_usize(v_i_1733_);
lean_dec(v_i_1733_);
v_res_1742_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1(v_a_1730_, v_as_1731_, v_sz_boxed_1740_, v_i_boxed_1741_, v_b_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
lean_dec_ref(v_as_1731_);
lean_dec(v_a_1730_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0(lean_object* v_a_1743_, lean_object* v_t_1744_, lean_object* v_init_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v_root_1751_; lean_object* v_tail_1752_; lean_object* v___x_1753_; 
v_root_1751_ = lean_ctor_get(v_t_1744_, 0);
v_tail_1752_ = lean_ctor_get(v_t_1744_, 1);
lean_inc_ref(v_init_1745_);
v___x_1753_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0(v_init_1745_, v_a_1743_, v_root_1751_, v_init_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_);
lean_dec_ref(v_init_1745_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1790_; 
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1756_ = v___x_1753_;
v_isShared_1757_ = v_isSharedCheck_1790_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1753_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1790_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
if (lean_obj_tag(v_a_1754_) == 0)
{
lean_object* v_a_1758_; lean_object* v___x_1760_; 
v_a_1758_ = lean_ctor_get(v_a_1754_, 0);
lean_inc(v_a_1758_);
lean_dec_ref_known(v_a_1754_, 1);
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 0, v_a_1758_);
v___x_1760_ = v___x_1756_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_a_1758_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
else
{
lean_object* v_a_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; size_t v_sz_1765_; size_t v___x_1766_; lean_object* v___x_1767_; 
lean_del_object(v___x_1756_);
v_a_1762_ = lean_ctor_get(v_a_1754_, 0);
lean_inc(v_a_1762_);
lean_dec_ref_known(v_a_1754_, 1);
v___x_1763_ = lean_box(0);
v___x_1764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1764_, 0, v___x_1763_);
lean_ctor_set(v___x_1764_, 1, v_a_1762_);
v_sz_1765_ = lean_array_size(v_tail_1752_);
v___x_1766_ = ((size_t)0ULL);
v___x_1767_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1(v_a_1743_, v_tail_1752_, v_sz_1765_, v___x_1766_, v___x_1764_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_);
if (lean_obj_tag(v___x_1767_) == 0)
{
lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1781_; 
v_a_1768_ = lean_ctor_get(v___x_1767_, 0);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1770_ = v___x_1767_;
v_isShared_1771_ = v_isSharedCheck_1781_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v___x_1767_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1781_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v_fst_1772_; 
v_fst_1772_ = lean_ctor_get(v_a_1768_, 0);
if (lean_obj_tag(v_fst_1772_) == 0)
{
lean_object* v_snd_1773_; lean_object* v___x_1775_; 
v_snd_1773_ = lean_ctor_get(v_a_1768_, 1);
lean_inc(v_snd_1773_);
lean_dec(v_a_1768_);
if (v_isShared_1771_ == 0)
{
lean_ctor_set(v___x_1770_, 0, v_snd_1773_);
v___x_1775_ = v___x_1770_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_snd_1773_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
else
{
lean_object* v_val_1777_; lean_object* v___x_1779_; 
lean_inc_ref(v_fst_1772_);
lean_dec(v_a_1768_);
v_val_1777_ = lean_ctor_get(v_fst_1772_, 0);
lean_inc(v_val_1777_);
lean_dec_ref_known(v_fst_1772_, 1);
if (v_isShared_1771_ == 0)
{
lean_ctor_set(v___x_1770_, 0, v_val_1777_);
v___x_1779_ = v___x_1770_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v_val_1777_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
return v___x_1779_;
}
}
}
}
else
{
lean_object* v_a_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1789_; 
v_a_1782_ = lean_ctor_get(v___x_1767_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1784_ = v___x_1767_;
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_a_1782_);
lean_dec(v___x_1767_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1787_; 
if (v_isShared_1785_ == 0)
{
v___x_1787_ = v___x_1784_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_a_1782_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
}
}
}
else
{
lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1798_; 
v_a_1791_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1793_ = v___x_1753_;
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v___x_1753_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1796_; 
if (v_isShared_1794_ == 0)
{
v___x_1796_ = v___x_1793_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_a_1791_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0___boxed(lean_object* v_a_1799_, lean_object* v_t_1800_, lean_object* v_init_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0(v_a_1799_, v_t_1800_, v_init_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec_ref(v_t_1800_);
lean_dec(v_a_1799_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___lam__0(lean_object* v_mvarId_1810_, lean_object* v___x_1811_, lean_object* v___x_1812_, lean_object* v_toPreserve_1813_, uint8_t v_indirectProps_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_){
_start:
{
lean_object* v___x_1820_; 
lean_inc(v_mvarId_1810_);
v___x_1820_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1810_, v___x_1811_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
if (lean_obj_tag(v___x_1820_) == 0)
{
uint8_t v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
lean_dec_ref_known(v___x_1820_, 1);
v___x_1821_ = 0;
v___x_1822_ = lean_box(v___x_1821_);
v___x_1823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1822_);
lean_ctor_set(v___x_1823_, 1, v___x_1812_);
v___x_1824_ = lean_st_mk_ref(v___x_1823_);
lean_inc(v_mvarId_1810_);
v___x_1825_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed(v_mvarId_1810_, v_toPreserve_1813_, v_indirectProps_1814_, v___x_1824_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v_a_1826_; lean_object* v___x_1827_; lean_object* v_lctx_1828_; lean_object* v_localInstances_1829_; lean_object* v_decls_1830_; lean_object* v___x_1831_; 
v_a_1826_ = lean_ctor_get(v___x_1825_, 0);
lean_inc(v_a_1826_);
lean_dec_ref_known(v___x_1825_, 1);
v___x_1827_ = lean_st_ref_get(v___x_1824_);
lean_dec(v___x_1824_);
lean_dec(v___x_1827_);
v_lctx_1828_ = lean_ctor_get(v___y_1815_, 2);
v_localInstances_1829_ = lean_ctor_get(v___y_1815_, 3);
v_decls_1830_ = lean_ctor_get(v_lctx_1828_, 1);
lean_inc_ref(v_lctx_1828_);
v___x_1831_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0(v_a_1826_, v_decls_1830_, v_lctx_1828_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v_a_1832_; lean_object* v___x_1833_; lean_object* v___y_1835_; lean_object* v___x_1879_; lean_object* v___x_1880_; uint8_t v___x_1881_; 
v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
lean_inc(v_a_1832_);
lean_dec_ref_known(v___x_1831_, 1);
v___x_1833_ = lean_unsigned_to_nat(0u);
v___x_1879_ = lean_array_get_size(v_localInstances_1829_);
v___x_1880_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___lam__0___closed__0));
v___x_1881_ = lean_nat_dec_lt(v___x_1833_, v___x_1879_);
if (v___x_1881_ == 0)
{
lean_dec(v_a_1826_);
v___y_1835_ = v___x_1880_;
goto v___jp_1834_;
}
else
{
size_t v___x_1882_; size_t v___x_1883_; lean_object* v___x_1884_; 
v___x_1882_ = ((size_t)0ULL);
v___x_1883_ = lean_usize_of_nat(v___x_1879_);
v___x_1884_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__3(v_a_1826_, v_localInstances_1829_, v___x_1882_, v___x_1883_, v___x_1880_);
lean_dec(v_a_1826_);
v___y_1835_ = v___x_1884_;
goto v___jp_1834_;
}
v___jp_1834_:
{
lean_object* v___x_1836_; 
lean_inc(v_mvarId_1810_);
v___x_1836_ = l_Lean_MVarId_getType(v_mvarId_1810_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v_a_1837_; lean_object* v___x_1838_; lean_object* v_a_1839_; lean_object* v___x_1840_; 
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
lean_inc(v_a_1837_);
lean_dec_ref_known(v___x_1836_, 1);
v___x_1838_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___redArg(v_a_1837_, v___y_1816_);
v_a_1839_ = lean_ctor_get(v___x_1838_, 0);
lean_inc(v_a_1839_);
lean_dec_ref(v___x_1838_);
lean_inc(v_mvarId_1810_);
v___x_1840_ = l_Lean_MVarId_getTag(v_mvarId_1810_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v_a_1841_; uint8_t v___x_1842_; lean_object* v___x_1843_; 
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
lean_inc(v_a_1841_);
lean_dec_ref_known(v___x_1840_, 1);
v___x_1842_ = 2;
v___x_1843_ = l_Lean_Meta_mkFreshExprMVarAt(v_a_1832_, v___y_1835_, v_a_1839_, v___x_1842_, v_a_1841_, v___x_1833_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
lean_dec_ref(v___y_1815_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; lean_object* v___x_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1853_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
lean_inc_n(v_a_1844_, 2);
lean_dec_ref_known(v___x_1843_, 1);
v___x_1845_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___redArg(v_mvarId_1810_, v_a_1844_, v___y_1816_);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1853_ == 0)
{
lean_object* v_unused_1854_; 
v_unused_1854_ = lean_ctor_get(v___x_1845_, 0);
lean_dec(v_unused_1854_);
v___x_1847_ = v___x_1845_;
v_isShared_1848_ = v_isSharedCheck_1853_;
goto v_resetjp_1846_;
}
else
{
lean_dec(v___x_1845_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1853_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___x_1849_; lean_object* v___x_1851_; 
v___x_1849_ = l_Lean_Expr_mvarId_x21(v_a_1844_);
lean_dec(v_a_1844_);
if (v_isShared_1848_ == 0)
{
lean_ctor_set(v___x_1847_, 0, v___x_1849_);
v___x_1851_ = v___x_1847_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v___x_1849_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
}
else
{
lean_object* v_a_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1862_; 
lean_dec(v_mvarId_1810_);
v_a_1855_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1857_ = v___x_1843_;
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_a_1855_);
lean_dec(v___x_1843_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1860_; 
if (v_isShared_1858_ == 0)
{
v___x_1860_ = v___x_1857_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_a_1855_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
}
else
{
lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1870_; 
lean_dec(v_a_1839_);
lean_dec_ref(v___y_1835_);
lean_dec(v_a_1832_);
lean_dec_ref(v___y_1815_);
lean_dec(v_mvarId_1810_);
v_a_1863_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1865_ = v___x_1840_;
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_dec(v___x_1840_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1868_; 
if (v_isShared_1866_ == 0)
{
v___x_1868_ = v___x_1865_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_a_1863_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
}
}
else
{
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1878_; 
lean_dec_ref(v___y_1835_);
lean_dec(v_a_1832_);
lean_dec_ref(v___y_1815_);
lean_dec(v_mvarId_1810_);
v_a_1871_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1873_ = v___x_1836_;
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___x_1836_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1876_; 
if (v_isShared_1874_ == 0)
{
v___x_1876_ = v___x_1873_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_a_1871_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
}
}
}
else
{
lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1892_; 
lean_dec(v_a_1826_);
lean_dec_ref(v___y_1815_);
lean_dec(v_mvarId_1810_);
v_a_1885_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1887_ = v___x_1831_;
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_dec(v___x_1831_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1890_; 
if (v_isShared_1888_ == 0)
{
v___x_1890_ = v___x_1887_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_a_1885_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
}
else
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1900_; 
lean_dec(v___x_1824_);
lean_dec_ref(v___y_1815_);
lean_dec(v_mvarId_1810_);
v_a_1893_ = lean_ctor_get(v___x_1825_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1895_ = v___x_1825_;
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1825_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1898_; 
if (v_isShared_1896_ == 0)
{
v___x_1898_ = v___x_1895_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_a_1893_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
}
else
{
lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1908_; 
lean_dec_ref(v___y_1815_);
lean_dec(v___x_1812_);
lean_dec(v_mvarId_1810_);
v_a_1901_ = lean_ctor_get(v___x_1820_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1903_ = v___x_1820_;
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1820_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1906_; 
if (v_isShared_1904_ == 0)
{
v___x_1906_ = v___x_1903_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_a_1901_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___lam__0___boxed(lean_object* v_mvarId_1909_, lean_object* v___x_1910_, lean_object* v___x_1911_, lean_object* v_toPreserve_1912_, lean_object* v_indirectProps_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_){
_start:
{
uint8_t v_indirectProps_boxed_1919_; lean_object* v_res_1920_; 
v_indirectProps_boxed_1919_ = lean_unbox(v_indirectProps_1913_);
v_res_1920_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___lam__0(v_mvarId_1909_, v___x_1910_, v___x_1911_, v_toPreserve_1912_, v_indirectProps_boxed_1919_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
lean_dec(v___y_1917_);
lean_dec_ref(v___y_1916_);
lean_dec(v___y_1915_);
lean_dec_ref(v_toPreserve_1912_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(lean_object* v_mvarId_1924_, lean_object* v_toPreserve_1925_, uint8_t v_indirectProps_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_){
_start:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___f_1935_; lean_object* v___x_1936_; 
v___x_1932_ = lean_box(1);
v___x_1933_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___closed__1));
v___x_1934_ = lean_box(v_indirectProps_1926_);
lean_inc(v_mvarId_1924_);
v___f_1935_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1935_, 0, v_mvarId_1924_);
lean_closure_set(v___f_1935_, 1, v___x_1933_);
lean_closure_set(v___f_1935_, 2, v___x_1932_);
lean_closure_set(v___f_1935_, 3, v_toPreserve_1925_);
lean_closure_set(v___f_1935_, 4, v___x_1934_);
v___x_1936_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___redArg(v_mvarId_1924_, v___f_1935_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_);
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___boxed(lean_object* v_mvarId_1937_, lean_object* v_toPreserve_1938_, lean_object* v_indirectProps_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_){
_start:
{
uint8_t v_indirectProps_boxed_1945_; lean_object* v_res_1946_; 
v_indirectProps_boxed_1945_ = lean_unbox(v_indirectProps_1939_);
v_res_1946_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(v_mvarId_1937_, v_toPreserve_1938_, v_indirectProps_boxed_1945_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_);
lean_dec(v_a_1943_);
lean_dec_ref(v_a_1942_);
lean_dec(v_a_1941_);
lean_dec_ref(v_a_1940_);
return v_res_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2(lean_object* v_mvarId_1947_, lean_object* v_val_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_){
_start:
{
lean_object* v___x_1954_; 
v___x_1954_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___redArg(v_mvarId_1947_, v_val_1948_, v___y_1950_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___boxed(lean_object* v_mvarId_1955_, lean_object* v_val_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
lean_object* v_res_1962_; 
v_res_1962_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2(v_mvarId_1955_, v_val_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
return v_res_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4(lean_object* v_00_u03b2_1963_, lean_object* v_x_1964_, lean_object* v_x_1965_, lean_object* v_x_1966_){
_start:
{
lean_object* v___x_1967_; 
v___x_1967_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4___redArg(v_x_1964_, v_x_1965_, v_x_1966_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6(lean_object* v_a_1968_, lean_object* v_as_1969_, size_t v_sz_1970_, size_t v_i_1971_, lean_object* v_b_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_){
_start:
{
lean_object* v___x_1978_; 
v___x_1978_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___redArg(v_a_1968_, v_as_1969_, v_sz_1970_, v_i_1971_, v_b_1972_);
return v___x_1978_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___boxed(lean_object* v_a_1979_, lean_object* v_as_1980_, lean_object* v_sz_1981_, lean_object* v_i_1982_, lean_object* v_b_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
size_t v_sz_boxed_1989_; size_t v_i_boxed_1990_; lean_object* v_res_1991_; 
v_sz_boxed_1989_ = lean_unbox_usize(v_sz_1981_);
lean_dec(v_sz_1981_);
v_i_boxed_1990_ = lean_unbox_usize(v_i_1982_);
lean_dec(v_i_1982_);
v_res_1991_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6(v_a_1979_, v_as_1980_, v_sz_boxed_1989_, v_i_boxed_1990_, v_b_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
lean_dec_ref(v_as_1980_);
lean_dec(v_a_1979_);
return v_res_1991_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9(lean_object* v_00_u03b2_1992_, lean_object* v_x_1993_, size_t v_x_1994_, size_t v_x_1995_, lean_object* v_x_1996_, lean_object* v_x_1997_){
_start:
{
lean_object* v___x_1998_; 
v___x_1998_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg(v_x_1993_, v_x_1994_, v_x_1995_, v_x_1996_, v_x_1997_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___boxed(lean_object* v_00_u03b2_1999_, lean_object* v_x_2000_, lean_object* v_x_2001_, lean_object* v_x_2002_, lean_object* v_x_2003_, lean_object* v_x_2004_){
_start:
{
size_t v_x_8417__boxed_2005_; size_t v_x_8418__boxed_2006_; lean_object* v_res_2007_; 
v_x_8417__boxed_2005_ = lean_unbox_usize(v_x_2001_);
lean_dec(v_x_2001_);
v_x_8418__boxed_2006_ = lean_unbox_usize(v_x_2002_);
lean_dec(v_x_2002_);
v_res_2007_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9(v_00_u03b2_1999_, v_x_2000_, v_x_8417__boxed_2005_, v_x_8418__boxed_2006_, v_x_2003_, v_x_2004_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7(lean_object* v_a_2008_, lean_object* v_as_2009_, size_t v_sz_2010_, size_t v_i_2011_, lean_object* v_b_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
lean_object* v___x_2018_; 
v___x_2018_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___redArg(v_a_2008_, v_as_2009_, v_sz_2010_, v_i_2011_, v_b_2012_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___boxed(lean_object* v_a_2019_, lean_object* v_as_2020_, lean_object* v_sz_2021_, lean_object* v_i_2022_, lean_object* v_b_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
size_t v_sz_boxed_2029_; size_t v_i_boxed_2030_; lean_object* v_res_2031_; 
v_sz_boxed_2029_ = lean_unbox_usize(v_sz_2021_);
lean_dec(v_sz_2021_);
v_i_boxed_2030_ = lean_unbox_usize(v_i_2022_);
lean_dec(v_i_2022_);
v_res_2031_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7(v_a_2019_, v_as_2020_, v_sz_boxed_2029_, v_i_boxed_2030_, v_b_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec_ref(v_as_2020_);
lean_dec(v_a_2019_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12(lean_object* v_00_u03b2_2032_, lean_object* v_n_2033_, lean_object* v_k_2034_, lean_object* v_v_2035_){
_start:
{
lean_object* v___x_2036_; 
v___x_2036_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12___redArg(v_n_2033_, v_k_2034_, v_v_2035_);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13(lean_object* v_00_u03b2_2037_, size_t v_depth_2038_, lean_object* v_keys_2039_, lean_object* v_vals_2040_, lean_object* v_heq_2041_, lean_object* v_i_2042_, lean_object* v_entries_2043_){
_start:
{
lean_object* v___x_2044_; 
v___x_2044_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___redArg(v_depth_2038_, v_keys_2039_, v_vals_2040_, v_i_2042_, v_entries_2043_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___boxed(lean_object* v_00_u03b2_2045_, lean_object* v_depth_2046_, lean_object* v_keys_2047_, lean_object* v_vals_2048_, lean_object* v_heq_2049_, lean_object* v_i_2050_, lean_object* v_entries_2051_){
_start:
{
size_t v_depth_boxed_2052_; lean_object* v_res_2053_; 
v_depth_boxed_2052_ = lean_unbox_usize(v_depth_2046_);
lean_dec(v_depth_2046_);
v_res_2053_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13(v_00_u03b2_2045_, v_depth_boxed_2052_, v_keys_2047_, v_vals_2048_, v_heq_2049_, v_i_2050_, v_entries_2051_);
lean_dec_ref(v_vals_2048_);
lean_dec_ref(v_keys_2047_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12_spec__13(lean_object* v_00_u03b2_2054_, lean_object* v_x_2055_, lean_object* v_x_2056_, lean_object* v_x_2057_, lean_object* v_x_2058_){
_start:
{
lean_object* v___x_2059_; 
v___x_2059_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12_spec__13___redArg(v_x_2055_, v_x_2056_, v_x_2057_, v_x_2058_);
return v___x_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_cleanup(lean_object* v_mvarId_2060_, lean_object* v_toPreserve_2061_, uint8_t v_indirectProps_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_){
_start:
{
lean_object* v___x_2068_; 
v___x_2068_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(v_mvarId_2060_, v_toPreserve_2061_, v_indirectProps_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_cleanup___boxed(lean_object* v_mvarId_2069_, lean_object* v_toPreserve_2070_, lean_object* v_indirectProps_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_){
_start:
{
uint8_t v_indirectProps_boxed_2077_; lean_object* v_res_2078_; 
v_indirectProps_boxed_2077_ = lean_unbox(v_indirectProps_2071_);
v_res_2078_ = l_Lean_MVarId_cleanup(v_mvarId_2069_, v_toPreserve_2070_, v_indirectProps_boxed_2077_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_);
lean_dec(v_a_2075_);
lean_dec_ref(v_a_2074_);
lean_dec(v_a_2073_);
lean_dec_ref(v_a_2072_);
return v_res_2078_;
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
