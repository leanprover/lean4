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
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(lean_object* v_k_1_, lean_object* v_t_2_){
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
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1_ = stack[0].m_obj;
lean_object* v_t_2_ = stack[1].m_obj;
uint8_t v_res_11_;
v_res_11_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v_k_1_, v_t_2_);
stack->m_num = v_res_11_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg___boxed(lean_object* v_k_12_, lean_object* v_t_13_){
_start:
{
uint8_t v_res_14_; lean_object* v_r_15_; 
v_res_14_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v_k_12_, v_t_13_);
lean_dec(v_t_13_);
lean_dec(v_k_12_);
v_r_15_ = lean_box(v_res_14_);
return v_r_15_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0___redArg(lean_object* v_e_16_, lean_object* v___y_17_){
_start:
{
uint8_t v___x_19_; 
v___x_19_ = l_Lean_Expr_hasMVar(v_e_16_);
if (v___x_19_ == 0)
{
lean_object* v___x_20_; 
v___x_20_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_20_, 0, v_e_16_);
return v___x_20_;
}
else
{
lean_object* v___x_21_; lean_object* v_mctx_22_; lean_object* v___x_23_; lean_object* v_fst_24_; lean_object* v_snd_25_; lean_object* v___x_26_; lean_object* v_cache_27_; lean_object* v_zetaDeltaFVarIds_28_; lean_object* v_postponed_29_; lean_object* v_diag_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_39_; 
v___x_21_ = lean_st_ref_get(v___y_17_);
v_mctx_22_ = lean_ctor_get(v___x_21_, 0);
lean_inc_ref(v_mctx_22_);
lean_dec(v___x_21_);
v___x_23_ = l_Lean_instantiateMVarsCore(v_mctx_22_, v_e_16_);
v_fst_24_ = lean_ctor_get(v___x_23_, 0);
lean_inc(v_fst_24_);
v_snd_25_ = lean_ctor_get(v___x_23_, 1);
lean_inc(v_snd_25_);
lean_dec_ref(v___x_23_);
v___x_26_ = lean_st_ref_take(v___y_17_);
v_cache_27_ = lean_ctor_get(v___x_26_, 1);
v_zetaDeltaFVarIds_28_ = lean_ctor_get(v___x_26_, 2);
v_postponed_29_ = lean_ctor_get(v___x_26_, 3);
v_diag_30_ = lean_ctor_get(v___x_26_, 4);
v_isSharedCheck_39_ = !lean_is_exclusive(v___x_26_);
if (v_isSharedCheck_39_ == 0)
{
lean_object* v_unused_40_; 
v_unused_40_ = lean_ctor_get(v___x_26_, 0);
lean_dec(v_unused_40_);
v___x_32_ = v___x_26_;
v_isShared_33_ = v_isSharedCheck_39_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_diag_30_);
lean_inc(v_postponed_29_);
lean_inc(v_zetaDeltaFVarIds_28_);
lean_inc(v_cache_27_);
lean_dec(v___x_26_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_39_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
lean_object* v___x_35_; 
if (v_isShared_33_ == 0)
{
lean_ctor_set(v___x_32_, 0, v_snd_25_);
v___x_35_ = v___x_32_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v_snd_25_);
lean_ctor_set(v_reuseFailAlloc_38_, 1, v_cache_27_);
lean_ctor_set(v_reuseFailAlloc_38_, 2, v_zetaDeltaFVarIds_28_);
lean_ctor_set(v_reuseFailAlloc_38_, 3, v_postponed_29_);
lean_ctor_set(v_reuseFailAlloc_38_, 4, v_diag_30_);
v___x_35_ = v_reuseFailAlloc_38_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = lean_st_ref_put(v___y_17_, v___x_35_);
v___x_37_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_37_, 0, v_fst_24_);
return v___x_37_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_16_ = stack[0].m_obj;
lean_object* v___y_17_ = stack[1].m_obj;
lean_object* v_res_41_;
v_res_41_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0___redArg(v_e_16_, v___y_17_);
stack->m_obj
 = v_res_41_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0___redArg___boxed(lean_object* v_e_42_, lean_object* v___y_43_, lean_object* v___y_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0___redArg(v_e_42_, v___y_43_);
lean_dec(v___y_43_);
return v_res_45_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__0(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_48_ = lean_box(0);
v___x_49_ = lean_unsigned_to_nat(16u);
v___x_50_ = lean_mk_array(v___x_49_, v___x_48_);
return v___x_50_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__1(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_51_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__0, &l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__0_once, _init_l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__0);
v___x_52_ = lean_unsigned_to_nat(0u);
v___x_53_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
lean_ctor_set(v___x_53_, 1, v___x_51_);
return v___x_53_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__3(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_54_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__2));
v___x_55_ = lean_box(1);
v___x_56_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__1, &l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__1);
v___x_57_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
lean_ctor_set(v___x_57_, 1, v___x_55_);
lean_ctor_set(v___x_57_, 2, v___x_54_);
return v___x_57_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(lean_object* v_fvarId_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_){
_start:
{
lean_object* v___x_65_; lean_object* v_snd_66_; uint8_t v___x_67_; 
v___x_65_ = lean_st_ref_get(v_a_59_);
v_snd_66_ = lean_ctor_get(v___x_65_, 1);
lean_inc(v_snd_66_);
lean_dec(v___x_65_);
v___x_67_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v_fvarId_58_, v_snd_66_);
lean_dec(v_snd_66_);
if (v___x_67_ == 0)
{
uint8_t v___x_68_; lean_object* v___x_69_; lean_object* v_snd_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_81_; 
v___x_68_ = 1;
v___x_69_ = lean_st_ref_take(v_a_59_);
v_snd_70_ = lean_ctor_get(v___x_69_, 1);
v_isSharedCheck_81_ = !lean_is_exclusive(v___x_69_);
if (v_isSharedCheck_81_ == 0)
{
lean_object* v_unused_82_; 
v_unused_82_ = lean_ctor_get(v___x_69_, 0);
lean_dec(v_unused_82_);
v___x_72_ = v___x_69_;
v_isShared_73_ = v_isSharedCheck_81_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_snd_70_);
lean_dec(v___x_69_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_81_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_77_; 
lean_inc(v_fvarId_58_);
v___x_74_ = l_Lean_FVarIdSet_insert(v_snd_70_, v_fvarId_58_);
v___x_75_ = lean_box(v___x_68_);
if (v_isShared_73_ == 0)
{
lean_ctor_set(v___x_72_, 1, v___x_74_);
lean_ctor_set(v___x_72_, 0, v___x_75_);
v___x_77_ = v___x_72_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_80_; 
v_reuseFailAlloc_80_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_80_, 0, v___x_75_);
lean_ctor_set(v_reuseFailAlloc_80_, 1, v___x_74_);
v___x_77_ = v_reuseFailAlloc_80_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = lean_st_ref_put(v_a_59_, v___x_77_);
v___x_79_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addDeps(v_fvarId_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_);
return v___x_79_;
}
}
}
else
{
lean_object* v___x_83_; lean_object* v___x_84_; 
lean_dec(v_fvarId_58_);
v___x_83_ = lean_box(0);
v___x_84_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
return v___x_84_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_58_ = stack[0].m_obj;
lean_object* v_a_59_ = stack[1].m_obj;
lean_object* v_a_60_ = stack[2].m_obj;
lean_object* v_a_61_ = stack[3].m_obj;
lean_object* v_a_62_ = stack[4].m_obj;
lean_object* v_a_63_ = stack[5].m_obj;
lean_object* v_res_85_;
v_res_85_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v_fvarId_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_);
stack->m_obj
 = v_res_85_;
}
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__1(lean_object* v_init_86_, lean_object* v_x_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_){
_start:
{
if (lean_obj_tag(v_x_87_) == 0)
{
lean_object* v_k_94_; lean_object* v_l_95_; lean_object* v_r_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v_k_94_ = lean_ctor_get(v_x_87_, 1);
lean_inc(v_k_94_);
v_l_95_ = lean_ctor_get(v_x_87_, 3);
lean_inc(v_l_95_);
v_r_96_ = lean_ctor_get(v_x_87_, 4);
lean_inc(v_r_96_);
lean_dec_ref_known(v_x_87_, 5);
v___x_97_ = lean_box(0);
v___x_98_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__1(v_init_86_, v_l_95_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_);
if (lean_obj_tag(v___x_98_) == 0)
{
lean_object* v___x_99_; 
lean_dec_ref_known(v___x_98_, 1);
v___x_99_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v_k_94_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_);
if (lean_obj_tag(v___x_99_) == 0)
{
lean_dec_ref_known(v___x_99_, 1);
v_init_86_ = v___x_97_;
v_x_87_ = v_r_96_;
goto _start;
}
else
{
lean_object* v_a_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_108_; 
lean_dec(v_r_96_);
v_a_101_ = lean_ctor_get(v___x_99_, 0);
v_isSharedCheck_108_ = !lean_is_exclusive(v___x_99_);
if (v_isSharedCheck_108_ == 0)
{
v___x_103_ = v___x_99_;
v_isShared_104_ = v_isSharedCheck_108_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_a_101_);
lean_dec(v___x_99_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_108_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___x_106_; 
if (v_isShared_104_ == 0)
{
v___x_106_ = v___x_103_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_a_101_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
}
else
{
lean_dec(v_r_96_);
lean_dec(v_k_94_);
return v___x_98_;
}
}
else
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_109_, 0, v_init_86_);
v___x_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
return v___x_110_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_86_ = stack[0].m_obj;
lean_object* v_x_87_ = stack[1].m_obj;
lean_object* v___y_88_ = stack[2].m_obj;
lean_object* v___y_89_ = stack[3].m_obj;
lean_object* v___y_90_ = stack[4].m_obj;
lean_object* v___y_91_ = stack[5].m_obj;
lean_object* v___y_92_ = stack[6].m_obj;
lean_object* v_res_111_;
v_res_111_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__1(v_init_86_, v_x_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_);
stack->m_obj
 = v_res_111_;
}
lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars(lean_object* v_e_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0___redArg(v_e_112_, v_a_115_);
if (lean_obj_tag(v___x_119_) == 0)
{
lean_object* v_a_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v_a_120_ = lean_ctor_get(v___x_119_, 0);
lean_inc(v_a_120_);
lean_dec_ref_known(v___x_119_, 1);
v___x_121_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__3, &l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__3);
v___x_122_ = lean_st_mk_ref(v___x_121_);
v___x_123_ = l_Lean_Expr_collectFVars(v_a_120_, v___x_122_, v_a_114_, v_a_115_, v_a_116_, v_a_117_);
if (lean_obj_tag(v___x_123_) == 0)
{
lean_object* v___x_124_; lean_object* v_fvarSet_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
lean_dec_ref_known(v___x_123_, 1);
v___x_124_ = lean_st_ref_get(v___x_122_);
lean_dec(v___x_122_);
v_fvarSet_125_ = lean_ctor_get(v___x_124_, 1);
lean_inc(v_fvarSet_125_);
lean_dec(v___x_124_);
v___x_126_ = lean_box(0);
v___x_127_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__1(v___x_126_, v_fvarSet_125_, v_a_113_, v_a_114_, v_a_115_, v_a_116_, v_a_117_);
if (lean_obj_tag(v___x_127_) == 0)
{
lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_134_; 
v_isSharedCheck_134_ = !lean_is_exclusive(v___x_127_);
if (v_isSharedCheck_134_ == 0)
{
lean_object* v_unused_135_; 
v_unused_135_ = lean_ctor_get(v___x_127_, 0);
lean_dec(v_unused_135_);
v___x_129_ = v___x_127_;
v_isShared_130_ = v_isSharedCheck_134_;
goto v_resetjp_128_;
}
else
{
lean_dec(v___x_127_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_134_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_132_; 
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 0, v___x_126_);
v___x_132_ = v___x_129_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v___x_126_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
}
else
{
lean_object* v_a_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_143_; 
v_a_136_ = lean_ctor_get(v___x_127_, 0);
v_isSharedCheck_143_ = !lean_is_exclusive(v___x_127_);
if (v_isSharedCheck_143_ == 0)
{
v___x_138_ = v___x_127_;
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_a_136_);
lean_dec(v___x_127_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_141_; 
if (v_isShared_139_ == 0)
{
v___x_141_ = v___x_138_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_a_136_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
}
else
{
lean_dec(v___x_122_);
return v___x_123_;
}
}
else
{
lean_object* v_a_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_151_; 
v_a_144_ = lean_ctor_get(v___x_119_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v___x_119_);
if (v_isSharedCheck_151_ == 0)
{
v___x_146_ = v___x_119_;
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_a_144_);
lean_dec(v___x_119_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_149_; 
if (v_isShared_147_ == 0)
{
v___x_149_ = v___x_146_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_a_144_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_112_ = stack[0].m_obj;
lean_object* v_a_113_ = stack[1].m_obj;
lean_object* v_a_114_ = stack[2].m_obj;
lean_object* v_a_115_ = stack[3].m_obj;
lean_object* v_a_116_ = stack[4].m_obj;
lean_object* v_a_117_ = stack[5].m_obj;
lean_object* v_res_152_;
v_res_152_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars(v_e_112_, v_a_113_, v_a_114_, v_a_115_, v_a_116_, v_a_117_);
stack->m_obj
 = v_res_152_;
}
lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addDeps(lean_object* v_fvarId_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_153_, v_a_155_, v_a_157_, v_a_158_);
if (lean_obj_tag(v___x_160_) == 0)
{
lean_object* v_a_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v_a_161_ = lean_ctor_get(v___x_160_, 0);
lean_inc(v_a_161_);
lean_dec_ref_known(v___x_160_, 1);
v___x_162_ = l_Lean_LocalDecl_type(v_a_161_);
v___x_163_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars(v___x_162_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_);
if (lean_obj_tag(v___x_163_) == 0)
{
lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_175_; 
v_isSharedCheck_175_ = !lean_is_exclusive(v___x_163_);
if (v_isSharedCheck_175_ == 0)
{
lean_object* v_unused_176_; 
v_unused_176_ = lean_ctor_get(v___x_163_, 0);
lean_dec(v_unused_176_);
v___x_165_ = v___x_163_;
v_isShared_166_ = v_isSharedCheck_175_;
goto v_resetjp_164_;
}
else
{
lean_dec(v___x_163_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_175_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
uint8_t v___x_167_; lean_object* v___x_168_; 
v___x_167_ = 0;
v___x_168_ = l_Lean_LocalDecl_value_x3f(v_a_161_, v___x_167_);
lean_dec(v_a_161_);
if (lean_obj_tag(v___x_168_) == 1)
{
lean_object* v_val_169_; lean_object* v___x_170_; 
lean_del_object(v___x_165_);
v_val_169_ = lean_ctor_get(v___x_168_, 0);
lean_inc(v_val_169_);
lean_dec_ref_known(v___x_168_, 1);
v___x_170_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars(v_val_169_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_);
return v___x_170_;
}
else
{
lean_object* v___x_171_; lean_object* v___x_173_; 
lean_dec(v___x_168_);
v___x_171_ = lean_box(0);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 0, v___x_171_);
v___x_173_ = v___x_165_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_171_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
else
{
lean_dec(v_a_161_);
return v___x_163_;
}
}
else
{
lean_object* v_a_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_184_; 
v_a_177_ = lean_ctor_get(v___x_160_, 0);
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_184_ == 0)
{
v___x_179_ = v___x_160_;
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_a_177_);
lean_dec(v___x_160_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_182_; 
if (v_isShared_180_ == 0)
{
v___x_182_ = v___x_179_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_a_177_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addDeps_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_153_ = stack[0].m_obj;
lean_object* v_a_154_ = stack[1].m_obj;
lean_object* v_a_155_ = stack[2].m_obj;
lean_object* v_a_156_ = stack[3].m_obj;
lean_object* v_a_157_ = stack[4].m_obj;
lean_object* v_a_158_ = stack[5].m_obj;
lean_object* v_res_185_;
v_res_185_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addDeps(v_fvarId_153_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_);
stack->m_obj
 = v_res_185_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addDeps___boxed(lean_object* v_fvarId_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addDeps(v_fvarId_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_);
lean_dec(v_a_191_);
lean_dec_ref(v_a_190_);
lean_dec(v_a_189_);
lean_dec_ref(v_a_188_);
lean_dec(v_a_187_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__1___boxed(lean_object* v_init_194_, lean_object* v_x_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__1(v_init_194_, v_x_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
lean_dec(v___y_196_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar___boxed(lean_object* v_fvarId_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v_fvarId_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
lean_dec(v_a_208_);
lean_dec_ref(v_a_207_);
lean_dec(v_a_206_);
lean_dec_ref(v_a_205_);
lean_dec(v_a_204_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___boxed(lean_object* v_e_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars(v_e_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
lean_dec(v_a_216_);
lean_dec_ref(v_a_215_);
lean_dec(v_a_214_);
lean_dec_ref(v_a_213_);
lean_dec(v_a_212_);
return v_res_218_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0(lean_object* v_e_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0___redArg(v_e_219_, v___y_222_);
return v___x_226_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_219_ = stack[0].m_obj;
lean_object* v___y_220_ = stack[1].m_obj;
lean_object* v___y_221_ = stack[2].m_obj;
lean_object* v___y_222_ = stack[3].m_obj;
lean_object* v___y_223_ = stack[4].m_obj;
lean_object* v___y_224_ = stack[5].m_obj;
lean_object* v_res_227_;
v_res_227_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0(v_e_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_);
stack->m_obj
 = v_res_227_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0___boxed(lean_object* v_e_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0(v_e_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_);
lean_dec(v___y_233_);
lean_dec_ref(v___y_232_);
lean_dec(v___y_231_);
lean_dec_ref(v___y_230_);
lean_dec(v___y_229_);
return v_res_235_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3(lean_object* v_00_u03b2_236_, lean_object* v_k_237_, lean_object* v_t_238_){
_start:
{
uint8_t v___x_239_; 
v___x_239_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v_k_237_, v_t_238_);
return v___x_239_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_237_ = stack[1].m_obj;
lean_object* v_t_238_ = stack[2].m_obj;
uint8_t v_res_240_;
v_res_240_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3(lean_box(0), v_k_237_, v_t_238_);
stack->m_num = v_res_240_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___boxed(lean_object* v_00_u03b2_241_, lean_object* v_k_242_, lean_object* v_t_243_){
_start:
{
uint8_t v_res_244_; lean_object* v_r_245_; 
v_res_244_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3(v_00_u03b2_241_, v_k_242_, v_t_243_);
lean_dec(v_t_243_);
lean_dec(v_k_242_);
v_r_245_ = lean_box(v_res_244_);
return v_r_245_;
}
}
lean_object* l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(lean_object* v_e_246_, lean_object* v_pf_247_, lean_object* v_pm_248_, lean_object* v___y_249_){
_start:
{
lean_object* v___x_251_; uint8_t v_fst_253_; lean_object* v_mctx_254_; lean_object* v___y_272_; lean_object* v_mctx_277_; lean_object* v___x_278_; lean_object* v___x_279_; uint8_t v___x_280_; 
v___x_251_ = lean_st_ref_get(v___y_249_);
v_mctx_277_ = lean_ctor_get(v___x_251_, 0);
lean_inc_ref_n(v_mctx_277_, 2);
lean_dec(v___x_251_);
v___x_278_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__1, &l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars___closed__1);
v___x_279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
lean_ctor_set(v___x_279_, 1, v_mctx_277_);
v___x_280_ = l_Lean_Expr_hasFVar(v_e_246_);
if (v___x_280_ == 0)
{
uint8_t v___x_281_; 
v___x_281_ = l_Lean_Expr_hasMVar(v_e_246_);
if (v___x_281_ == 0)
{
lean_dec_ref_known(v___x_279_, 2);
lean_dec_ref(v_pm_248_);
lean_dec_ref(v_pf_247_);
lean_dec_ref(v_e_246_);
v_fst_253_ = v___x_281_;
v_mctx_254_ = v_mctx_277_;
goto v___jp_252_;
}
else
{
lean_object* v___x_282_; 
lean_dec_ref(v_mctx_277_);
v___x_282_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v_pf_247_, v_pm_248_, v_e_246_, v___x_279_);
v___y_272_ = v___x_282_;
goto v___jp_271_;
}
}
else
{
lean_object* v___x_283_; 
lean_dec_ref(v_mctx_277_);
v___x_283_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v_pf_247_, v_pm_248_, v_e_246_, v___x_279_);
v___y_272_ = v___x_283_;
goto v___jp_271_;
}
v___jp_252_:
{
lean_object* v___x_255_; lean_object* v_cache_256_; lean_object* v_zetaDeltaFVarIds_257_; lean_object* v_postponed_258_; lean_object* v_diag_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_269_; 
v___x_255_ = lean_st_ref_take(v___y_249_);
v_cache_256_ = lean_ctor_get(v___x_255_, 1);
v_zetaDeltaFVarIds_257_ = lean_ctor_get(v___x_255_, 2);
v_postponed_258_ = lean_ctor_get(v___x_255_, 3);
v_diag_259_ = lean_ctor_get(v___x_255_, 4);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_269_ == 0)
{
lean_object* v_unused_270_; 
v_unused_270_ = lean_ctor_get(v___x_255_, 0);
lean_dec(v_unused_270_);
v___x_261_ = v___x_255_;
v_isShared_262_ = v_isSharedCheck_269_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_diag_259_);
lean_inc(v_postponed_258_);
lean_inc(v_zetaDeltaFVarIds_257_);
lean_inc(v_cache_256_);
lean_dec(v___x_255_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_269_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_264_; 
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 0, v_mctx_254_);
v___x_264_ = v___x_261_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_mctx_254_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v_cache_256_);
lean_ctor_set(v_reuseFailAlloc_268_, 2, v_zetaDeltaFVarIds_257_);
lean_ctor_set(v_reuseFailAlloc_268_, 3, v_postponed_258_);
lean_ctor_set(v_reuseFailAlloc_268_, 4, v_diag_259_);
v___x_264_ = v_reuseFailAlloc_268_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_265_ = lean_st_ref_put(v___y_249_, v___x_264_);
v___x_266_ = lean_box(v_fst_253_);
v___x_267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
return v___x_267_;
}
}
}
v___jp_271_:
{
lean_object* v_snd_273_; lean_object* v_fst_274_; lean_object* v_mctx_275_; uint8_t v___x_276_; 
v_snd_273_ = lean_ctor_get(v___y_272_, 1);
lean_inc(v_snd_273_);
v_fst_274_ = lean_ctor_get(v___y_272_, 0);
lean_inc(v_fst_274_);
lean_dec_ref(v___y_272_);
v_mctx_275_ = lean_ctor_get(v_snd_273_, 1);
lean_inc_ref(v_mctx_275_);
lean_dec(v_snd_273_);
v___x_276_ = lean_unbox(v_fst_274_);
lean_dec(v_fst_274_);
v_fst_253_ = v___x_276_;
v_mctx_254_ = v_mctx_275_;
goto v___jp_252_;
}
}
}
LEAN_EXPORT void l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_246_ = stack[0].m_obj;
lean_object* v_pf_247_ = stack[1].m_obj;
lean_object* v_pm_248_ = stack[2].m_obj;
lean_object* v___y_249_ = stack[3].m_obj;
lean_object* v_res_284_;
v_res_284_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v_e_246_, v_pf_247_, v_pm_248_, v___y_249_);
stack->m_obj
 = v_res_284_;
}
LEAN_EXPORT lean_object* l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg___boxed(lean_object* v_e_285_, lean_object* v_pf_286_, lean_object* v_pm_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v_e_285_, v_pf_286_, v_pm_287_, v___y_288_);
lean_dec(v___y_288_);
return v_res_290_;
}
}
lean_object* l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0(lean_object* v_e_291_, lean_object* v_pf_292_, lean_object* v_pm_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v_e_291_, v_pf_292_, v_pm_293_, v___y_296_);
return v___x_300_;
}
}
LEAN_EXPORT void l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_291_ = stack[0].m_obj;
lean_object* v_pf_292_ = stack[1].m_obj;
lean_object* v_pm_293_ = stack[2].m_obj;
lean_object* v___y_294_ = stack[3].m_obj;
lean_object* v___y_295_ = stack[4].m_obj;
lean_object* v___y_296_ = stack[5].m_obj;
lean_object* v___y_297_ = stack[6].m_obj;
lean_object* v___y_298_ = stack[7].m_obj;
lean_object* v_res_301_;
v_res_301_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0(v_e_291_, v_pf_292_, v_pm_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_);
stack->m_obj
 = v_res_301_;
}
LEAN_EXPORT lean_object* l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___boxed(lean_object* v_e_302_, lean_object* v_pf_303_, lean_object* v_pm_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0(v_e_302_, v_pf_303_, v_pm_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
lean_dec(v___y_309_);
lean_dec_ref(v___y_308_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
lean_dec(v___y_305_);
return v_res_311_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__0(lean_object* v_snd_312_, lean_object* v___y_313_){
_start:
{
uint8_t v___x_314_; 
v___x_314_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___y_313_, v_snd_312_);
return v___x_314_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_312_ = stack[0].m_obj;
lean_object* v___y_313_ = stack[1].m_obj;
uint8_t v_res_315_;
v_res_315_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__0(v_snd_312_, v___y_313_);
stack->m_num = v_res_315_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__0___boxed(lean_object* v_snd_316_, lean_object* v___y_317_){
_start:
{
uint8_t v_res_318_; lean_object* v_r_319_; 
v_res_318_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__0(v_snd_316_, v___y_317_);
lean_dec(v___y_317_);
lean_dec(v_snd_316_);
v_r_319_ = lean_box(v_res_318_);
return v_r_319_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__2(uint8_t v___x_320_, lean_object* v_x_321_){
_start:
{
return v___x_320_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__2_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_320_ = stack[0].m_num;
lean_object* v_x_321_ = stack[1].m_obj;
uint8_t v_res_322_;
v_res_322_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__2(v___x_320_, v_x_321_);
stack->m_num = v_res_322_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__2___boxed(lean_object* v___x_323_, lean_object* v_x_324_){
_start:
{
uint8_t v___x_9019__boxed_325_; uint8_t v_res_326_; lean_object* v_r_327_; 
v___x_9019__boxed_325_ = lean_unbox(v___x_323_);
v_res_326_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__2(v___x_9019__boxed_325_, v_x_324_);
lean_dec(v_x_324_);
v_r_327_ = lean_box(v_res_326_);
return v_r_327_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2_spec__5(lean_object* v_as_328_, size_t v_sz_329_, size_t v_i_330_, lean_object* v_b_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_){
_start:
{
uint8_t v___x_338_; 
v___x_338_ = lean_usize_dec_lt(v_i_330_, v_sz_329_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; 
v___x_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_339_, 0, v_b_331_);
return v___x_339_;
}
else
{
lean_object* v_snd_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_423_; 
v_snd_340_ = lean_ctor_get(v_b_331_, 1);
v_isSharedCheck_423_ = !lean_is_exclusive(v_b_331_);
if (v_isSharedCheck_423_ == 0)
{
lean_object* v_unused_424_; 
v_unused_424_ = lean_ctor_get(v_b_331_, 0);
lean_dec(v_unused_424_);
v___x_342_ = v_b_331_;
v_isShared_343_ = v_isSharedCheck_423_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_snd_340_);
lean_dec(v_b_331_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_423_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_344_; lean_object* v_a_346_; lean_object* v_a_353_; 
v___x_344_ = lean_box(0);
v_a_353_ = lean_array_uget_borrowed(v_as_328_, v_i_330_);
if (lean_obj_tag(v_a_353_) == 0)
{
v_a_346_ = v_snd_340_;
goto v___jp_345_;
}
else
{
lean_object* v_val_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v_snd_357_; lean_object* v___x_358_; uint8_t v___x_359_; 
lean_dec(v_snd_340_);
v_val_354_ = lean_ctor_get(v_a_353_, 0);
v___x_355_ = lean_box(0);
v___x_356_ = lean_st_ref_get(v___y_332_);
v_snd_357_ = lean_ctor_get(v___x_356_, 1);
lean_inc(v_snd_357_);
lean_dec(v___x_356_);
v___x_358_ = l_Lean_LocalDecl_fvarId(v_val_354_);
v___x_359_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_358_, v_snd_357_);
if (v___x_359_ == 0)
{
lean_object* v___f_360_; lean_object* v___x_361_; lean_object* v___f_362_; lean_object* v___y_364_; lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v___y_367_; lean_object* v___y_368_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___f_360_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_360_, 0, v_snd_357_);
v___x_361_ = lean_box(v___x_359_);
v___f_362_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__2___boxed), 2, 1);
lean_closure_set(v___f_362_, 0, v___x_361_);
v___x_391_ = l_Lean_LocalDecl_type(v_val_354_);
lean_inc_ref(v___x_391_);
v___x_392_ = l_Lean_Meta_isProp(v___x_391_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_object* v_a_393_; uint8_t v___x_394_; 
v_a_393_ = lean_ctor_get(v___x_392_, 0);
lean_inc(v_a_393_);
lean_dec_ref_known(v___x_392_, 1);
v___x_394_ = lean_unbox(v_a_393_);
lean_dec(v_a_393_);
if (v___x_394_ == 0)
{
lean_dec_ref(v___x_391_);
v___y_364_ = v___y_332_;
v___y_365_ = v___y_333_;
v___y_366_ = v___y_334_;
v___y_367_ = v___y_335_;
v___y_368_ = v___y_336_;
goto v___jp_363_;
}
else
{
lean_object* v___x_395_; 
lean_inc_ref(v___f_362_);
lean_inc_ref(v___f_360_);
v___x_395_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v___x_391_, v___f_360_, v___f_362_, v___y_334_);
if (lean_obj_tag(v___x_395_) == 0)
{
lean_object* v_a_396_; uint8_t v___x_397_; 
v_a_396_ = lean_ctor_get(v___x_395_, 0);
lean_inc(v_a_396_);
lean_dec_ref_known(v___x_395_, 1);
v___x_397_ = lean_unbox(v_a_396_);
lean_dec(v_a_396_);
if (v___x_397_ == 0)
{
v___y_364_ = v___y_332_;
v___y_365_ = v___y_333_;
v___y_366_ = v___y_334_;
v___y_367_ = v___y_335_;
v___y_368_ = v___y_336_;
goto v___jp_363_;
}
else
{
lean_object* v___x_398_; 
lean_inc(v___x_358_);
v___x_398_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_358_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_dec_ref_known(v___x_398_, 1);
v___y_364_ = v___y_332_;
v___y_365_ = v___y_333_;
v___y_366_ = v___y_334_;
v___y_367_ = v___y_335_;
v___y_368_ = v___y_336_;
goto v___jp_363_;
}
else
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
lean_dec_ref(v___f_362_);
lean_dec_ref(v___f_360_);
lean_dec(v___x_358_);
lean_del_object(v___x_342_);
v_a_399_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_406_ == 0)
{
v___x_401_ = v___x_398_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_398_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_402_ == 0)
{
v___x_404_ = v___x_401_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_a_399_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
}
else
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_414_; 
lean_dec_ref(v___f_362_);
lean_dec_ref(v___f_360_);
lean_dec(v___x_358_);
lean_del_object(v___x_342_);
v_a_407_ = lean_ctor_get(v___x_395_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_414_ == 0)
{
v___x_409_ = v___x_395_;
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_395_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_410_ == 0)
{
v___x_412_ = v___x_409_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_a_407_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
}
}
else
{
lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_422_; 
lean_dec_ref(v___x_391_);
lean_dec_ref(v___f_362_);
lean_dec_ref(v___f_360_);
lean_dec(v___x_358_);
lean_del_object(v___x_342_);
v_a_415_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_422_ == 0)
{
v___x_417_ = v___x_392_;
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v___x_392_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_420_; 
if (v_isShared_418_ == 0)
{
v___x_420_ = v___x_417_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_a_415_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
v___jp_363_:
{
lean_object* v___x_369_; 
v___x_369_ = l_Lean_LocalDecl_value_x3f(v_val_354_, v___x_359_);
if (lean_obj_tag(v___x_369_) == 1)
{
lean_object* v_val_370_; lean_object* v___x_371_; 
v_val_370_ = lean_ctor_get(v___x_369_, 0);
lean_inc(v_val_370_);
lean_dec_ref_known(v___x_369_, 1);
v___x_371_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v_val_370_, v___f_360_, v___f_362_, v___y_366_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v_a_372_; uint8_t v___x_373_; 
v_a_372_ = lean_ctor_get(v___x_371_, 0);
lean_inc(v_a_372_);
lean_dec_ref_known(v___x_371_, 1);
v___x_373_ = lean_unbox(v_a_372_);
lean_dec(v_a_372_);
if (v___x_373_ == 0)
{
lean_dec(v___x_358_);
v_a_346_ = v___x_355_;
goto v___jp_345_;
}
else
{
lean_object* v___x_374_; 
v___x_374_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_358_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_);
if (lean_obj_tag(v___x_374_) == 0)
{
lean_dec_ref_known(v___x_374_, 1);
v_a_346_ = v___x_355_;
goto v___jp_345_;
}
else
{
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_382_; 
lean_del_object(v___x_342_);
v_a_375_ = lean_ctor_get(v___x_374_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_382_ == 0)
{
v___x_377_ = v___x_374_;
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_374_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_380_; 
if (v_isShared_378_ == 0)
{
v___x_380_ = v___x_377_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_a_375_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
}
else
{
lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_390_; 
lean_dec(v___x_358_);
lean_del_object(v___x_342_);
v_a_383_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_390_ == 0)
{
v___x_385_ = v___x_371_;
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v___x_371_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_388_; 
if (v_isShared_386_ == 0)
{
v___x_388_ = v___x_385_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_383_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
else
{
lean_dec(v___x_369_);
lean_dec_ref(v___f_362_);
lean_dec_ref(v___f_360_);
lean_dec(v___x_358_);
v_a_346_ = v___x_355_;
goto v___jp_345_;
}
}
}
else
{
lean_dec(v___x_358_);
lean_dec(v_snd_357_);
v_a_346_ = v___x_355_;
goto v___jp_345_;
}
}
v___jp_345_:
{
lean_object* v___x_348_; 
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 1, v_a_346_);
lean_ctor_set(v___x_342_, 0, v___x_344_);
v___x_348_ = v___x_342_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v___x_344_);
lean_ctor_set(v_reuseFailAlloc_352_, 1, v_a_346_);
v___x_348_ = v_reuseFailAlloc_352_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
size_t v___x_349_; size_t v___x_350_; 
v___x_349_ = ((size_t)1ULL);
v___x_350_ = lean_usize_add(v_i_330_, v___x_349_);
v_i_330_ = v___x_350_;
v_b_331_ = v___x_348_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_328_ = stack[0].m_obj;
size_t v_sz_329_ = stack[1].m_num;
size_t v_i_330_ = stack[2].m_num;
lean_object* v_b_331_ = stack[3].m_obj;
lean_object* v___y_332_ = stack[4].m_obj;
lean_object* v___y_333_ = stack[5].m_obj;
lean_object* v___y_334_ = stack[6].m_obj;
lean_object* v___y_335_ = stack[7].m_obj;
lean_object* v___y_336_ = stack[8].m_obj;
lean_object* v_res_425_;
v_res_425_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2_spec__5(v_as_328_, v_sz_329_, v_i_330_, v_b_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
stack->m_obj
 = v_res_425_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2_spec__5___boxed(lean_object* v_as_426_, lean_object* v_sz_427_, lean_object* v_i_428_, lean_object* v_b_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
size_t v_sz_boxed_436_; size_t v_i_boxed_437_; lean_object* v_res_438_; 
v_sz_boxed_436_ = lean_unbox_usize(v_sz_427_);
lean_dec(v_sz_427_);
v_i_boxed_437_ = lean_unbox_usize(v_i_428_);
lean_dec(v_i_428_);
v_res_438_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2_spec__5(v_as_426_, v_sz_boxed_436_, v_i_boxed_437_, v_b_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec(v___y_430_);
lean_dec_ref(v_as_426_);
return v_res_438_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2(lean_object* v_as_439_, size_t v_sz_440_, size_t v_i_441_, lean_object* v_b_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
uint8_t v___x_449_; 
v___x_449_ = lean_usize_dec_lt(v_i_441_, v_sz_440_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; 
v___x_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_450_, 0, v_b_442_);
return v___x_450_;
}
else
{
lean_object* v_snd_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_534_; 
v_snd_451_ = lean_ctor_get(v_b_442_, 1);
v_isSharedCheck_534_ = !lean_is_exclusive(v_b_442_);
if (v_isSharedCheck_534_ == 0)
{
lean_object* v_unused_535_; 
v_unused_535_ = lean_ctor_get(v_b_442_, 0);
lean_dec(v_unused_535_);
v___x_453_ = v_b_442_;
v_isShared_454_ = v_isSharedCheck_534_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_snd_451_);
lean_dec(v_b_442_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_534_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_455_; lean_object* v_a_457_; lean_object* v_a_464_; 
v___x_455_ = lean_box(0);
v_a_464_ = lean_array_uget_borrowed(v_as_439_, v_i_441_);
if (lean_obj_tag(v_a_464_) == 0)
{
v_a_457_ = v_snd_451_;
goto v___jp_456_;
}
else
{
lean_object* v_val_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v_snd_468_; lean_object* v___x_469_; uint8_t v___x_470_; 
lean_dec(v_snd_451_);
v_val_465_ = lean_ctor_get(v_a_464_, 0);
v___x_466_ = lean_box(0);
v___x_467_ = lean_st_ref_get(v___y_443_);
v_snd_468_ = lean_ctor_get(v___x_467_, 1);
lean_inc(v_snd_468_);
lean_dec(v___x_467_);
v___x_469_ = l_Lean_LocalDecl_fvarId(v_val_465_);
v___x_470_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_469_, v_snd_468_);
if (v___x_470_ == 0)
{
lean_object* v___f_471_; lean_object* v___x_472_; lean_object* v___f_473_; lean_object* v___y_475_; lean_object* v___y_476_; lean_object* v___y_477_; lean_object* v___y_478_; lean_object* v___y_479_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___f_471_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_471_, 0, v_snd_468_);
v___x_472_ = lean_box(v___x_470_);
v___f_473_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__2___boxed), 2, 1);
lean_closure_set(v___f_473_, 0, v___x_472_);
v___x_502_ = l_Lean_LocalDecl_type(v_val_465_);
lean_inc_ref(v___x_502_);
v___x_503_ = l_Lean_Meta_isProp(v___x_502_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_a_504_; uint8_t v___x_505_; 
v_a_504_ = lean_ctor_get(v___x_503_, 0);
lean_inc(v_a_504_);
lean_dec_ref_known(v___x_503_, 1);
v___x_505_ = lean_unbox(v_a_504_);
lean_dec(v_a_504_);
if (v___x_505_ == 0)
{
lean_dec_ref(v___x_502_);
v___y_475_ = v___y_443_;
v___y_476_ = v___y_444_;
v___y_477_ = v___y_445_;
v___y_478_ = v___y_446_;
v___y_479_ = v___y_447_;
goto v___jp_474_;
}
else
{
lean_object* v___x_506_; 
lean_inc_ref(v___f_473_);
lean_inc_ref(v___f_471_);
v___x_506_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v___x_502_, v___f_471_, v___f_473_, v___y_445_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; uint8_t v___x_508_; 
v_a_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_a_507_);
lean_dec_ref_known(v___x_506_, 1);
v___x_508_ = lean_unbox(v_a_507_);
lean_dec(v_a_507_);
if (v___x_508_ == 0)
{
v___y_475_ = v___y_443_;
v___y_476_ = v___y_444_;
v___y_477_ = v___y_445_;
v___y_478_ = v___y_446_;
v___y_479_ = v___y_447_;
goto v___jp_474_;
}
else
{
lean_object* v___x_509_; 
lean_inc(v___x_469_);
v___x_509_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_469_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_dec_ref_known(v___x_509_, 1);
v___y_475_ = v___y_443_;
v___y_476_ = v___y_444_;
v___y_477_ = v___y_445_;
v___y_478_ = v___y_446_;
v___y_479_ = v___y_447_;
goto v___jp_474_;
}
else
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_517_; 
lean_dec_ref(v___f_473_);
lean_dec_ref(v___f_471_);
lean_dec(v___x_469_);
lean_del_object(v___x_453_);
v_a_510_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_517_ == 0)
{
v___x_512_ = v___x_509_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_509_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_513_ == 0)
{
v___x_515_ = v___x_512_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_a_510_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
}
else
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_525_; 
lean_dec_ref(v___f_473_);
lean_dec_ref(v___f_471_);
lean_dec(v___x_469_);
lean_del_object(v___x_453_);
v_a_518_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_525_ == 0)
{
v___x_520_ = v___x_506_;
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_506_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_523_; 
if (v_isShared_521_ == 0)
{
v___x_523_ = v___x_520_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_a_518_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
}
else
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_533_; 
lean_dec_ref(v___x_502_);
lean_dec_ref(v___f_473_);
lean_dec_ref(v___f_471_);
lean_dec(v___x_469_);
lean_del_object(v___x_453_);
v_a_526_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_533_ == 0)
{
v___x_528_ = v___x_503_;
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_503_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_531_; 
if (v_isShared_529_ == 0)
{
v___x_531_ = v___x_528_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_a_526_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
v___jp_474_:
{
lean_object* v___x_480_; 
v___x_480_ = l_Lean_LocalDecl_value_x3f(v_val_465_, v___x_470_);
if (lean_obj_tag(v___x_480_) == 1)
{
lean_object* v_val_481_; lean_object* v___x_482_; 
v_val_481_ = lean_ctor_get(v___x_480_, 0);
lean_inc(v_val_481_);
lean_dec_ref_known(v___x_480_, 1);
v___x_482_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v_val_481_, v___f_471_, v___f_473_, v___y_477_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; uint8_t v___x_484_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
lean_inc(v_a_483_);
lean_dec_ref_known(v___x_482_, 1);
v___x_484_ = lean_unbox(v_a_483_);
lean_dec(v_a_483_);
if (v___x_484_ == 0)
{
lean_dec(v___x_469_);
v_a_457_ = v___x_466_;
goto v___jp_456_;
}
else
{
lean_object* v___x_485_; 
v___x_485_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_469_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
if (lean_obj_tag(v___x_485_) == 0)
{
lean_dec_ref_known(v___x_485_, 1);
v_a_457_ = v___x_466_;
goto v___jp_456_;
}
else
{
lean_object* v_a_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_493_; 
lean_del_object(v___x_453_);
v_a_486_ = lean_ctor_get(v___x_485_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_493_ == 0)
{
v___x_488_ = v___x_485_;
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_a_486_);
lean_dec(v___x_485_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_491_; 
if (v_isShared_489_ == 0)
{
v___x_491_ = v___x_488_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_a_486_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
}
else
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_501_; 
lean_dec(v___x_469_);
lean_del_object(v___x_453_);
v_a_494_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_501_ == 0)
{
v___x_496_ = v___x_482_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_482_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_a_494_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
else
{
lean_dec(v___x_480_);
lean_dec_ref(v___f_473_);
lean_dec_ref(v___f_471_);
lean_dec(v___x_469_);
v_a_457_ = v___x_466_;
goto v___jp_456_;
}
}
}
else
{
lean_dec(v___x_469_);
lean_dec(v_snd_468_);
v_a_457_ = v___x_466_;
goto v___jp_456_;
}
}
v___jp_456_:
{
lean_object* v___x_459_; 
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 1, v_a_457_);
lean_ctor_set(v___x_453_, 0, v___x_455_);
v___x_459_ = v___x_453_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_455_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v_a_457_);
v___x_459_ = v_reuseFailAlloc_463_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
size_t v___x_460_; size_t v___x_461_; lean_object* v___x_462_; 
v___x_460_ = ((size_t)1ULL);
v___x_461_ = lean_usize_add(v_i_441_, v___x_460_);
v___x_462_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2_spec__5(v_as_439_, v_sz_440_, v___x_461_, v___x_459_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
return v___x_462_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_439_ = stack[0].m_obj;
size_t v_sz_440_ = stack[1].m_num;
size_t v_i_441_ = stack[2].m_num;
lean_object* v_b_442_ = stack[3].m_obj;
lean_object* v___y_443_ = stack[4].m_obj;
lean_object* v___y_444_ = stack[5].m_obj;
lean_object* v___y_445_ = stack[6].m_obj;
lean_object* v___y_446_ = stack[7].m_obj;
lean_object* v___y_447_ = stack[8].m_obj;
lean_object* v_res_536_;
v_res_536_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2(v_as_439_, v_sz_440_, v_i_441_, v_b_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
stack->m_obj
 = v_res_536_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___boxed(lean_object* v_as_537_, lean_object* v_sz_538_, lean_object* v_i_539_, lean_object* v_b_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_){
_start:
{
size_t v_sz_boxed_547_; size_t v_i_boxed_548_; lean_object* v_res_549_; 
v_sz_boxed_547_ = lean_unbox_usize(v_sz_538_);
lean_dec(v_sz_538_);
v_i_boxed_548_ = lean_unbox_usize(v_i_539_);
lean_dec(v_i_539_);
v_res_549_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2(v_as_537_, v_sz_boxed_547_, v_i_boxed_548_, v_b_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
lean_dec(v___y_543_);
lean_dec_ref(v___y_542_);
lean_dec(v___y_541_);
lean_dec_ref(v_as_537_);
return v_res_549_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3_spec__4(lean_object* v_as_550_, size_t v_sz_551_, size_t v_i_552_, lean_object* v_b_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
uint8_t v___x_560_; 
v___x_560_ = lean_usize_dec_lt(v_i_552_, v_sz_551_);
if (v___x_560_ == 0)
{
lean_object* v___x_561_; 
v___x_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_561_, 0, v_b_553_);
return v___x_561_;
}
else
{
lean_object* v_snd_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_645_; 
v_snd_562_ = lean_ctor_get(v_b_553_, 1);
v_isSharedCheck_645_ = !lean_is_exclusive(v_b_553_);
if (v_isSharedCheck_645_ == 0)
{
lean_object* v_unused_646_; 
v_unused_646_ = lean_ctor_get(v_b_553_, 0);
lean_dec(v_unused_646_);
v___x_564_ = v_b_553_;
v_isShared_565_ = v_isSharedCheck_645_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_snd_562_);
lean_dec(v_b_553_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_645_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_566_; lean_object* v_a_568_; lean_object* v_a_575_; 
v___x_566_ = lean_box(0);
v_a_575_ = lean_array_uget_borrowed(v_as_550_, v_i_552_);
if (lean_obj_tag(v_a_575_) == 0)
{
v_a_568_ = v_snd_562_;
goto v___jp_567_;
}
else
{
lean_object* v_val_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v_snd_579_; lean_object* v___x_580_; uint8_t v___x_581_; 
lean_dec(v_snd_562_);
v_val_576_ = lean_ctor_get(v_a_575_, 0);
v___x_577_ = lean_box(0);
v___x_578_ = lean_st_ref_get(v___y_554_);
v_snd_579_ = lean_ctor_get(v___x_578_, 1);
lean_inc(v_snd_579_);
lean_dec(v___x_578_);
v___x_580_ = l_Lean_LocalDecl_fvarId(v_val_576_);
v___x_581_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_580_, v_snd_579_);
if (v___x_581_ == 0)
{
lean_object* v___f_582_; lean_object* v___x_583_; lean_object* v___f_584_; lean_object* v___y_586_; lean_object* v___y_587_; lean_object* v___y_588_; lean_object* v___y_589_; lean_object* v___y_590_; lean_object* v___x_613_; lean_object* v___x_614_; 
v___f_582_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_582_, 0, v_snd_579_);
v___x_583_ = lean_box(v___x_581_);
v___f_584_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__2___boxed), 2, 1);
lean_closure_set(v___f_584_, 0, v___x_583_);
v___x_613_ = l_Lean_LocalDecl_type(v_val_576_);
lean_inc_ref(v___x_613_);
v___x_614_ = l_Lean_Meta_isProp(v___x_613_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; uint8_t v___x_616_; 
v_a_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc(v_a_615_);
lean_dec_ref_known(v___x_614_, 1);
v___x_616_ = lean_unbox(v_a_615_);
lean_dec(v_a_615_);
if (v___x_616_ == 0)
{
lean_dec_ref(v___x_613_);
v___y_586_ = v___y_554_;
v___y_587_ = v___y_555_;
v___y_588_ = v___y_556_;
v___y_589_ = v___y_557_;
v___y_590_ = v___y_558_;
goto v___jp_585_;
}
else
{
lean_object* v___x_617_; 
lean_inc_ref(v___f_584_);
lean_inc_ref(v___f_582_);
v___x_617_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v___x_613_, v___f_582_, v___f_584_, v___y_556_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v_a_618_; uint8_t v___x_619_; 
v_a_618_ = lean_ctor_get(v___x_617_, 0);
lean_inc(v_a_618_);
lean_dec_ref_known(v___x_617_, 1);
v___x_619_ = lean_unbox(v_a_618_);
lean_dec(v_a_618_);
if (v___x_619_ == 0)
{
v___y_586_ = v___y_554_;
v___y_587_ = v___y_555_;
v___y_588_ = v___y_556_;
v___y_589_ = v___y_557_;
v___y_590_ = v___y_558_;
goto v___jp_585_;
}
else
{
lean_object* v___x_620_; 
lean_inc(v___x_580_);
v___x_620_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_580_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_dec_ref_known(v___x_620_, 1);
v___y_586_ = v___y_554_;
v___y_587_ = v___y_555_;
v___y_588_ = v___y_556_;
v___y_589_ = v___y_557_;
v___y_590_ = v___y_558_;
goto v___jp_585_;
}
else
{
lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_628_; 
lean_dec_ref(v___f_584_);
lean_dec_ref(v___f_582_);
lean_dec(v___x_580_);
lean_del_object(v___x_564_);
v_a_621_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_628_ == 0)
{
v___x_623_ = v___x_620_;
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_620_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_626_; 
if (v_isShared_624_ == 0)
{
v___x_626_ = v___x_623_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_a_621_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
}
else
{
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_636_; 
lean_dec_ref(v___f_584_);
lean_dec_ref(v___f_582_);
lean_dec(v___x_580_);
lean_del_object(v___x_564_);
v_a_629_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_636_ == 0)
{
v___x_631_ = v___x_617_;
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_617_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_634_; 
if (v_isShared_632_ == 0)
{
v___x_634_ = v___x_631_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_a_629_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
}
}
else
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_644_; 
lean_dec_ref(v___x_613_);
lean_dec_ref(v___f_584_);
lean_dec_ref(v___f_582_);
lean_dec(v___x_580_);
lean_del_object(v___x_564_);
v_a_637_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_644_ == 0)
{
v___x_639_ = v___x_614_;
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_614_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_642_; 
if (v_isShared_640_ == 0)
{
v___x_642_ = v___x_639_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_637_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
v___jp_585_:
{
lean_object* v___x_591_; 
v___x_591_ = l_Lean_LocalDecl_value_x3f(v_val_576_, v___x_581_);
if (lean_obj_tag(v___x_591_) == 1)
{
lean_object* v_val_592_; lean_object* v___x_593_; 
v_val_592_ = lean_ctor_get(v___x_591_, 0);
lean_inc(v_val_592_);
lean_dec_ref_known(v___x_591_, 1);
v___x_593_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v_val_592_, v___f_582_, v___f_584_, v___y_588_);
if (lean_obj_tag(v___x_593_) == 0)
{
lean_object* v_a_594_; uint8_t v___x_595_; 
v_a_594_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_a_594_);
lean_dec_ref_known(v___x_593_, 1);
v___x_595_ = lean_unbox(v_a_594_);
lean_dec(v_a_594_);
if (v___x_595_ == 0)
{
lean_dec(v___x_580_);
v_a_568_ = v___x_577_;
goto v___jp_567_;
}
else
{
lean_object* v___x_596_; 
v___x_596_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_580_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_dec_ref_known(v___x_596_, 1);
v_a_568_ = v___x_577_;
goto v___jp_567_;
}
else
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_604_; 
lean_del_object(v___x_564_);
v_a_597_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_604_ == 0)
{
v___x_599_ = v___x_596_;
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_596_);
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
}
else
{
lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_612_; 
lean_dec(v___x_580_);
lean_del_object(v___x_564_);
v_a_605_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_612_ == 0)
{
v___x_607_ = v___x_593_;
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v___x_593_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_610_; 
if (v_isShared_608_ == 0)
{
v___x_610_ = v___x_607_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_a_605_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
else
{
lean_dec(v___x_591_);
lean_dec_ref(v___f_584_);
lean_dec_ref(v___f_582_);
lean_dec(v___x_580_);
v_a_568_ = v___x_577_;
goto v___jp_567_;
}
}
}
else
{
lean_dec(v___x_580_);
lean_dec(v_snd_579_);
v_a_568_ = v___x_577_;
goto v___jp_567_;
}
}
v___jp_567_:
{
lean_object* v___x_570_; 
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 1, v_a_568_);
lean_ctor_set(v___x_564_, 0, v___x_566_);
v___x_570_ = v___x_564_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_566_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v_a_568_);
v___x_570_ = v_reuseFailAlloc_574_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
size_t v___x_571_; size_t v___x_572_; 
v___x_571_ = ((size_t)1ULL);
v___x_572_ = lean_usize_add(v_i_552_, v___x_571_);
v_i_552_ = v___x_572_;
v_b_553_ = v___x_570_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_550_ = stack[0].m_obj;
size_t v_sz_551_ = stack[1].m_num;
size_t v_i_552_ = stack[2].m_num;
lean_object* v_b_553_ = stack[3].m_obj;
lean_object* v___y_554_ = stack[4].m_obj;
lean_object* v___y_555_ = stack[5].m_obj;
lean_object* v___y_556_ = stack[6].m_obj;
lean_object* v___y_557_ = stack[7].m_obj;
lean_object* v___y_558_ = stack[8].m_obj;
lean_object* v_res_647_;
v_res_647_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3_spec__4(v_as_550_, v_sz_551_, v_i_552_, v_b_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
stack->m_obj
 = v_res_647_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3_spec__4___boxed(lean_object* v_as_648_, lean_object* v_sz_649_, lean_object* v_i_650_, lean_object* v_b_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
size_t v_sz_boxed_658_; size_t v_i_boxed_659_; lean_object* v_res_660_; 
v_sz_boxed_658_ = lean_unbox_usize(v_sz_649_);
lean_dec(v_sz_649_);
v_i_boxed_659_ = lean_unbox_usize(v_i_650_);
lean_dec(v_i_650_);
v_res_660_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3_spec__4(v_as_648_, v_sz_boxed_658_, v_i_boxed_659_, v_b_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
lean_dec(v___y_652_);
lean_dec_ref(v_as_648_);
return v_res_660_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3(lean_object* v_as_661_, size_t v_sz_662_, size_t v_i_663_, lean_object* v_b_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
uint8_t v___x_671_; 
v___x_671_ = lean_usize_dec_lt(v_i_663_, v_sz_662_);
if (v___x_671_ == 0)
{
lean_object* v___x_672_; 
v___x_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_672_, 0, v_b_664_);
return v___x_672_;
}
else
{
lean_object* v_snd_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_756_; 
v_snd_673_ = lean_ctor_get(v_b_664_, 1);
v_isSharedCheck_756_ = !lean_is_exclusive(v_b_664_);
if (v_isSharedCheck_756_ == 0)
{
lean_object* v_unused_757_; 
v_unused_757_ = lean_ctor_get(v_b_664_, 0);
lean_dec(v_unused_757_);
v___x_675_ = v_b_664_;
v_isShared_676_ = v_isSharedCheck_756_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_snd_673_);
lean_dec(v_b_664_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_756_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_677_; lean_object* v_a_679_; lean_object* v_a_686_; 
v___x_677_ = lean_box(0);
v_a_686_ = lean_array_uget_borrowed(v_as_661_, v_i_663_);
if (lean_obj_tag(v_a_686_) == 0)
{
v_a_679_ = v_snd_673_;
goto v___jp_678_;
}
else
{
lean_object* v_val_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v_snd_690_; lean_object* v___x_691_; uint8_t v___x_692_; 
lean_dec(v_snd_673_);
v_val_687_ = lean_ctor_get(v_a_686_, 0);
v___x_688_ = lean_box(0);
v___x_689_ = lean_st_ref_get(v___y_665_);
v_snd_690_ = lean_ctor_get(v___x_689_, 1);
lean_inc(v_snd_690_);
lean_dec(v___x_689_);
v___x_691_ = l_Lean_LocalDecl_fvarId(v_val_687_);
v___x_692_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_691_, v_snd_690_);
if (v___x_692_ == 0)
{
lean_object* v___f_693_; lean_object* v___x_694_; lean_object* v___f_695_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___x_724_; lean_object* v___x_725_; 
v___f_693_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_693_, 0, v_snd_690_);
v___x_694_ = lean_box(v___x_692_);
v___f_695_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2___lam__2___boxed), 2, 1);
lean_closure_set(v___f_695_, 0, v___x_694_);
v___x_724_ = l_Lean_LocalDecl_type(v_val_687_);
lean_inc_ref(v___x_724_);
v___x_725_ = l_Lean_Meta_isProp(v___x_724_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; uint8_t v___x_727_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_a_726_);
lean_dec_ref_known(v___x_725_, 1);
v___x_727_ = lean_unbox(v_a_726_);
lean_dec(v_a_726_);
if (v___x_727_ == 0)
{
lean_dec_ref(v___x_724_);
v___y_697_ = v___y_665_;
v___y_698_ = v___y_666_;
v___y_699_ = v___y_667_;
v___y_700_ = v___y_668_;
v___y_701_ = v___y_669_;
goto v___jp_696_;
}
else
{
lean_object* v___x_728_; 
lean_inc_ref(v___f_695_);
lean_inc_ref(v___f_693_);
v___x_728_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v___x_724_, v___f_693_, v___f_695_, v___y_667_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v_a_729_; uint8_t v___x_730_; 
v_a_729_ = lean_ctor_get(v___x_728_, 0);
lean_inc(v_a_729_);
lean_dec_ref_known(v___x_728_, 1);
v___x_730_ = lean_unbox(v_a_729_);
lean_dec(v_a_729_);
if (v___x_730_ == 0)
{
v___y_697_ = v___y_665_;
v___y_698_ = v___y_666_;
v___y_699_ = v___y_667_;
v___y_700_ = v___y_668_;
v___y_701_ = v___y_669_;
goto v___jp_696_;
}
else
{
lean_object* v___x_731_; 
lean_inc(v___x_691_);
v___x_731_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_691_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_dec_ref_known(v___x_731_, 1);
v___y_697_ = v___y_665_;
v___y_698_ = v___y_666_;
v___y_699_ = v___y_667_;
v___y_700_ = v___y_668_;
v___y_701_ = v___y_669_;
goto v___jp_696_;
}
else
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_739_; 
lean_dec_ref(v___f_695_);
lean_dec_ref(v___f_693_);
lean_dec(v___x_691_);
lean_del_object(v___x_675_);
v_a_732_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_739_ == 0)
{
v___x_734_ = v___x_731_;
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___x_731_);
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
}
}
else
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_747_; 
lean_dec_ref(v___f_695_);
lean_dec_ref(v___f_693_);
lean_dec(v___x_691_);
lean_del_object(v___x_675_);
v_a_740_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_747_ == 0)
{
v___x_742_ = v___x_728_;
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_728_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_745_; 
if (v_isShared_743_ == 0)
{
v___x_745_ = v___x_742_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_a_740_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
}
else
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_755_; 
lean_dec_ref(v___x_724_);
lean_dec_ref(v___f_695_);
lean_dec_ref(v___f_693_);
lean_dec(v___x_691_);
lean_del_object(v___x_675_);
v_a_748_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_755_ == 0)
{
v___x_750_ = v___x_725_;
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_725_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_753_; 
if (v_isShared_751_ == 0)
{
v___x_753_ = v___x_750_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_a_748_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
v___jp_696_:
{
lean_object* v___x_702_; 
v___x_702_ = l_Lean_LocalDecl_value_x3f(v_val_687_, v___x_692_);
if (lean_obj_tag(v___x_702_) == 1)
{
lean_object* v_val_703_; lean_object* v___x_704_; 
v_val_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_val_703_);
lean_dec_ref_known(v___x_702_, 1);
v___x_704_ = l_Lean_dependsOnPred___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__0___redArg(v_val_703_, v___f_693_, v___f_695_, v___y_699_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v_a_705_; uint8_t v___x_706_; 
v_a_705_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_a_705_);
lean_dec_ref_known(v___x_704_, 1);
v___x_706_ = lean_unbox(v_a_705_);
lean_dec(v_a_705_);
if (v___x_706_ == 0)
{
lean_dec(v___x_691_);
v_a_679_ = v___x_688_;
goto v___jp_678_;
}
else
{
lean_object* v___x_707_; 
v___x_707_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_691_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_dec_ref_known(v___x_707_, 1);
v_a_679_ = v___x_688_;
goto v___jp_678_;
}
else
{
lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_715_; 
lean_del_object(v___x_675_);
v_a_708_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_715_ == 0)
{
v___x_710_ = v___x_707_;
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_707_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_711_ == 0)
{
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_a_708_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
}
else
{
lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_723_; 
lean_dec(v___x_691_);
lean_del_object(v___x_675_);
v_a_716_ = lean_ctor_get(v___x_704_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_723_ == 0)
{
v___x_718_ = v___x_704_;
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v___x_704_);
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
else
{
lean_dec(v___x_702_);
lean_dec_ref(v___f_695_);
lean_dec_ref(v___f_693_);
lean_dec(v___x_691_);
v_a_679_ = v___x_688_;
goto v___jp_678_;
}
}
}
else
{
lean_dec(v___x_691_);
lean_dec(v_snd_690_);
v_a_679_ = v___x_688_;
goto v___jp_678_;
}
}
v___jp_678_:
{
lean_object* v___x_681_; 
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 1, v_a_679_);
lean_ctor_set(v___x_675_, 0, v___x_677_);
v___x_681_ = v___x_675_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_677_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v_a_679_);
v___x_681_ = v_reuseFailAlloc_685_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
size_t v___x_682_; size_t v___x_683_; lean_object* v___x_684_; 
v___x_682_ = ((size_t)1ULL);
v___x_683_ = lean_usize_add(v_i_663_, v___x_682_);
v___x_684_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3_spec__4(v_as_661_, v_sz_662_, v___x_683_, v___x_681_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
return v___x_684_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_661_ = stack[0].m_obj;
size_t v_sz_662_ = stack[1].m_num;
size_t v_i_663_ = stack[2].m_num;
lean_object* v_b_664_ = stack[3].m_obj;
lean_object* v___y_665_ = stack[4].m_obj;
lean_object* v___y_666_ = stack[5].m_obj;
lean_object* v___y_667_ = stack[6].m_obj;
lean_object* v___y_668_ = stack[7].m_obj;
lean_object* v___y_669_ = stack[8].m_obj;
lean_object* v_res_758_;
v_res_758_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3(v_as_661_, v_sz_662_, v_i_663_, v_b_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
stack->m_obj
 = v_res_758_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3___boxed(lean_object* v_as_759_, lean_object* v_sz_760_, lean_object* v_i_761_, lean_object* v_b_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
size_t v_sz_boxed_769_; size_t v_i_boxed_770_; lean_object* v_res_771_; 
v_sz_boxed_769_ = lean_unbox_usize(v_sz_760_);
lean_dec(v_sz_760_);
v_i_boxed_770_ = lean_unbox_usize(v_i_761_);
lean_dec(v_i_761_);
v_res_771_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3(v_as_759_, v_sz_boxed_769_, v_i_boxed_770_, v_b_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v_as_759_);
return v_res_771_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1(lean_object* v_init_772_, lean_object* v_n_773_, lean_object* v_b_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
if (lean_obj_tag(v_n_773_) == 0)
{
lean_object* v_cs_781_; lean_object* v___x_782_; lean_object* v___x_783_; size_t v_sz_784_; size_t v___x_785_; lean_object* v___x_786_; 
v_cs_781_ = lean_ctor_get(v_n_773_, 0);
v___x_782_ = lean_box(0);
v___x_783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
lean_ctor_set(v___x_783_, 1, v_b_774_);
v_sz_784_ = lean_array_size(v_cs_781_);
v___x_785_ = ((size_t)0ULL);
v___x_786_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__2(v_init_772_, v_cs_781_, v_sz_784_, v___x_785_, v___x_783_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_801_; 
v_a_787_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_801_ == 0)
{
v___x_789_ = v___x_786_;
v_isShared_790_ = v_isSharedCheck_801_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_786_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_801_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v_fst_791_; 
v_fst_791_ = lean_ctor_get(v_a_787_, 0);
if (lean_obj_tag(v_fst_791_) == 0)
{
lean_object* v_snd_792_; lean_object* v___x_793_; lean_object* v___x_795_; 
v_snd_792_ = lean_ctor_get(v_a_787_, 1);
lean_inc(v_snd_792_);
lean_dec(v_a_787_);
v___x_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_793_, 0, v_snd_792_);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 0, v___x_793_);
v___x_795_ = v___x_789_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_793_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
else
{
lean_object* v_val_797_; lean_object* v___x_799_; 
lean_inc_ref(v_fst_791_);
lean_dec(v_a_787_);
v_val_797_ = lean_ctor_get(v_fst_791_, 0);
lean_inc(v_val_797_);
lean_dec_ref_known(v_fst_791_, 1);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 0, v_val_797_);
v___x_799_ = v___x_789_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_val_797_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
else
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_809_; 
v_a_802_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_809_ == 0)
{
v___x_804_ = v___x_786_;
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_786_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_807_; 
if (v_isShared_805_ == 0)
{
v___x_807_ = v___x_804_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_a_802_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
else
{
lean_object* v_vs_810_; lean_object* v___x_811_; lean_object* v___x_812_; size_t v_sz_813_; size_t v___x_814_; lean_object* v___x_815_; 
v_vs_810_ = lean_ctor_get(v_n_773_, 0);
v___x_811_ = lean_box(0);
v___x_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
lean_ctor_set(v___x_812_, 1, v_b_774_);
v_sz_813_ = lean_array_size(v_vs_810_);
v___x_814_ = ((size_t)0ULL);
v___x_815_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__3(v_vs_810_, v_sz_813_, v___x_814_, v___x_812_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_830_; 
v_a_816_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_830_ == 0)
{
v___x_818_ = v___x_815_;
v_isShared_819_ = v_isSharedCheck_830_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___x_815_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_830_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v_fst_820_; 
v_fst_820_ = lean_ctor_get(v_a_816_, 0);
if (lean_obj_tag(v_fst_820_) == 0)
{
lean_object* v_snd_821_; lean_object* v___x_822_; lean_object* v___x_824_; 
v_snd_821_ = lean_ctor_get(v_a_816_, 1);
lean_inc(v_snd_821_);
lean_dec(v_a_816_);
v___x_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_822_, 0, v_snd_821_);
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 0, v___x_822_);
v___x_824_ = v___x_818_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_822_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
else
{
lean_object* v_val_826_; lean_object* v___x_828_; 
lean_inc_ref(v_fst_820_);
lean_dec(v_a_816_);
v_val_826_ = lean_ctor_get(v_fst_820_, 0);
lean_inc(v_val_826_);
lean_dec_ref_known(v_fst_820_, 1);
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 0, v_val_826_);
v___x_828_ = v___x_818_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_val_826_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
else
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
v_a_831_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_815_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_815_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_a_831_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_772_ = stack[0].m_obj;
lean_object* v_n_773_ = stack[1].m_obj;
lean_object* v_b_774_ = stack[2].m_obj;
lean_object* v___y_775_ = stack[3].m_obj;
lean_object* v___y_776_ = stack[4].m_obj;
lean_object* v___y_777_ = stack[5].m_obj;
lean_object* v___y_778_ = stack[6].m_obj;
lean_object* v___y_779_ = stack[7].m_obj;
lean_object* v_res_839_;
v_res_839_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1(v_init_772_, v_n_773_, v_b_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
stack->m_obj
 = v_res_839_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__2(lean_object* v_init_840_, lean_object* v_as_841_, size_t v_sz_842_, size_t v_i_843_, lean_object* v_b_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
uint8_t v___x_851_; 
v___x_851_ = lean_usize_dec_lt(v_i_843_, v_sz_842_);
if (v___x_851_ == 0)
{
lean_object* v___x_852_; 
v___x_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_852_, 0, v_b_844_);
return v___x_852_;
}
else
{
lean_object* v_snd_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_887_; 
v_snd_853_ = lean_ctor_get(v_b_844_, 1);
v_isSharedCheck_887_ = !lean_is_exclusive(v_b_844_);
if (v_isSharedCheck_887_ == 0)
{
lean_object* v_unused_888_; 
v_unused_888_ = lean_ctor_get(v_b_844_, 0);
lean_dec(v_unused_888_);
v___x_855_ = v_b_844_;
v_isShared_856_ = v_isSharedCheck_887_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_snd_853_);
lean_dec(v_b_844_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_887_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_857_; lean_object* v_a_858_; lean_object* v___x_859_; 
v___x_857_ = lean_box(0);
v_a_858_ = lean_array_uget_borrowed(v_as_841_, v_i_843_);
lean_inc(v_snd_853_);
v___x_859_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1(v_init_840_, v_a_858_, v_snd_853_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_878_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_878_ == 0)
{
v___x_862_ = v___x_859_;
v_isShared_863_ = v_isSharedCheck_878_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_859_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_878_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
if (lean_obj_tag(v_a_860_) == 0)
{
lean_object* v___x_864_; lean_object* v___x_866_; 
v___x_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_864_, 0, v_a_860_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v___x_864_);
v___x_866_ = v___x_855_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_864_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v_snd_853_);
v___x_866_ = v_reuseFailAlloc_870_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
lean_object* v___x_868_; 
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 0, v___x_866_);
v___x_868_ = v___x_862_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v___x_866_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
else
{
lean_object* v_a_871_; lean_object* v___x_873_; 
lean_del_object(v___x_862_);
lean_dec(v_snd_853_);
v_a_871_ = lean_ctor_get(v_a_860_, 0);
lean_inc(v_a_871_);
lean_dec_ref_known(v_a_860_, 1);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 1, v_a_871_);
lean_ctor_set(v___x_855_, 0, v___x_857_);
v___x_873_ = v___x_855_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_857_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v_a_871_);
v___x_873_ = v_reuseFailAlloc_877_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
size_t v___x_874_; size_t v___x_875_; 
v___x_874_ = ((size_t)1ULL);
v___x_875_ = lean_usize_add(v_i_843_, v___x_874_);
v_i_843_ = v___x_875_;
v_b_844_ = v___x_873_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
lean_del_object(v___x_855_);
lean_dec(v_snd_853_);
v_a_879_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_886_ == 0)
{
v___x_881_ = v___x_859_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_859_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_879_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_840_ = stack[0].m_obj;
lean_object* v_as_841_ = stack[1].m_obj;
size_t v_sz_842_ = stack[2].m_num;
size_t v_i_843_ = stack[3].m_num;
lean_object* v_b_844_ = stack[4].m_obj;
lean_object* v___y_845_ = stack[5].m_obj;
lean_object* v___y_846_ = stack[6].m_obj;
lean_object* v___y_847_ = stack[7].m_obj;
lean_object* v___y_848_ = stack[8].m_obj;
lean_object* v___y_849_ = stack[9].m_obj;
lean_object* v_res_889_;
v_res_889_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__2(v_init_840_, v_as_841_, v_sz_842_, v_i_843_, v_b_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
stack->m_obj
 = v_res_889_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__2___boxed(lean_object* v_init_890_, lean_object* v_as_891_, lean_object* v_sz_892_, lean_object* v_i_893_, lean_object* v_b_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
size_t v_sz_boxed_901_; size_t v_i_boxed_902_; lean_object* v_res_903_; 
v_sz_boxed_901_ = lean_unbox_usize(v_sz_892_);
lean_dec(v_sz_892_);
v_i_boxed_902_ = lean_unbox_usize(v_i_893_);
lean_dec(v_i_893_);
v_res_903_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1_spec__2(v_init_890_, v_as_891_, v_sz_boxed_901_, v_i_boxed_902_, v_b_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec_ref(v_as_891_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1___boxed(lean_object* v_init_904_, lean_object* v_n_905_, lean_object* v_b_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1(v_init_904_, v_n_905_, v_b_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec(v___y_907_);
lean_dec_ref(v_n_905_);
return v_res_913_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1(lean_object* v_t_914_, lean_object* v_init_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v_root_922_; lean_object* v_tail_923_; lean_object* v___x_924_; 
v_root_922_ = lean_ctor_get(v_t_914_, 0);
v_tail_923_ = lean_ctor_get(v_t_914_, 1);
v___x_924_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__1(v_init_915_, v_root_922_, v_init_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_961_; 
v_a_925_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_961_ == 0)
{
v___x_927_ = v___x_924_;
v_isShared_928_ = v_isSharedCheck_961_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_924_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_961_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
if (lean_obj_tag(v_a_925_) == 0)
{
lean_object* v_a_929_; lean_object* v___x_931_; 
v_a_929_ = lean_ctor_get(v_a_925_, 0);
lean_inc(v_a_929_);
lean_dec_ref_known(v_a_925_, 1);
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 0, v_a_929_);
v___x_931_ = v___x_927_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_929_);
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
lean_object* v_a_933_; lean_object* v___x_934_; lean_object* v___x_935_; size_t v_sz_936_; size_t v___x_937_; lean_object* v___x_938_; 
lean_del_object(v___x_927_);
v_a_933_ = lean_ctor_get(v_a_925_, 0);
lean_inc(v_a_933_);
lean_dec_ref_known(v_a_925_, 1);
v___x_934_ = lean_box(0);
v___x_935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
lean_ctor_set(v___x_935_, 1, v_a_933_);
v_sz_936_ = lean_array_size(v_tail_923_);
v___x_937_ = ((size_t)0ULL);
v___x_938_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_spec__2(v_tail_923_, v_sz_936_, v___x_937_, v___x_935_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_952_; 
v_a_939_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_952_ == 0)
{
v___x_941_ = v___x_938_;
v_isShared_942_ = v_isSharedCheck_952_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v___x_938_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_952_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v_fst_943_; 
v_fst_943_ = lean_ctor_get(v_a_939_, 0);
if (lean_obj_tag(v_fst_943_) == 0)
{
lean_object* v_snd_944_; lean_object* v___x_946_; 
v_snd_944_ = lean_ctor_get(v_a_939_, 1);
lean_inc(v_snd_944_);
lean_dec(v_a_939_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 0, v_snd_944_);
v___x_946_ = v___x_941_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_snd_944_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
else
{
lean_object* v_val_948_; lean_object* v___x_950_; 
lean_inc_ref(v_fst_943_);
lean_dec(v_a_939_);
v_val_948_ = lean_ctor_get(v_fst_943_, 0);
lean_inc(v_val_948_);
lean_dec_ref_known(v_fst_943_, 1);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 0, v_val_948_);
v___x_950_ = v___x_941_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_val_948_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
else
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_960_; 
v_a_953_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_960_ == 0)
{
v___x_955_ = v___x_938_;
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___x_938_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_958_; 
if (v_isShared_956_ == 0)
{
v___x_958_ = v___x_955_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_a_953_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
}
}
}
else
{
lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_969_; 
v_a_962_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_969_ == 0)
{
v___x_964_ = v___x_924_;
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_924_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_967_; 
if (v_isShared_965_ == 0)
{
v___x_967_ = v___x_964_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_a_962_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_914_ = stack[0].m_obj;
lean_object* v_init_915_ = stack[1].m_obj;
lean_object* v___y_916_ = stack[2].m_obj;
lean_object* v___y_917_ = stack[3].m_obj;
lean_object* v___y_918_ = stack[4].m_obj;
lean_object* v___y_919_ = stack[5].m_obj;
lean_object* v___y_920_ = stack[6].m_obj;
lean_object* v_res_970_;
v_res_970_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1(v_t_914_, v_init_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
stack->m_obj
 = v_res_970_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1___boxed(lean_object* v_t_971_, lean_object* v_init_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1(v_t_971_, v_init_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec(v___y_973_);
lean_dec_ref(v_t_971_);
return v_res_979_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep(lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_){
_start:
{
lean_object* v_lctx_986_; lean_object* v_decls_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v_lctx_986_ = lean_ctor_get(v_a_981_, 2);
v_decls_987_ = lean_ctor_get(v_lctx_986_, 1);
v___x_988_ = lean_box(0);
v___x_989_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_spec__1(v_decls_987_, v___x_988_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_996_; 
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_996_ == 0)
{
lean_object* v_unused_997_; 
v_unused_997_ = lean_ctor_get(v___x_989_, 0);
lean_dec(v_unused_997_);
v___x_991_ = v___x_989_;
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
else
{
lean_dec(v___x_989_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_994_; 
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 0, v___x_988_);
v___x_994_ = v___x_991_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v___x_988_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
}
else
{
return v___x_989_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_980_ = stack[0].m_obj;
lean_object* v_a_981_ = stack[1].m_obj;
lean_object* v_a_982_ = stack[2].m_obj;
lean_object* v_a_983_ = stack[3].m_obj;
lean_object* v_a_984_ = stack[4].m_obj;
lean_object* v_res_998_;
v_res_998_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep(v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_);
stack->m_obj
 = v_res_998_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep___boxed(lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep(v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
lean_dec(v_a_1003_);
lean_dec_ref(v_a_1002_);
lean_dec(v_a_1001_);
lean_dec_ref(v_a_1000_);
lean_dec(v_a_999_);
return v_res_1005_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectProps(lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_){
_start:
{
lean_object* v___x_1012_; lean_object* v_snd_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1037_; 
v___x_1012_ = lean_st_ref_take(v_a_1006_);
v_snd_1013_ = lean_ctor_get(v___x_1012_, 1);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1037_ == 0)
{
lean_object* v_unused_1038_; 
v_unused_1038_ = lean_ctor_get(v___x_1012_, 0);
lean_dec(v_unused_1038_);
v___x_1015_ = v___x_1012_;
v_isShared_1016_ = v_isSharedCheck_1037_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_snd_1013_);
lean_dec(v___x_1012_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1037_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
uint8_t v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1020_; 
v___x_1017_ = 0;
v___x_1018_ = lean_box(v___x_1017_);
if (v_isShared_1016_ == 0)
{
lean_ctor_set(v___x_1015_, 0, v___x_1018_);
v___x_1020_ = v___x_1015_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1018_);
lean_ctor_set(v_reuseFailAlloc_1036_, 1, v_snd_1013_);
v___x_1020_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = lean_st_ref_put(v_a_1006_, v___x_1020_);
v___x_1022_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectPropsStep(v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1034_; 
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1034_ == 0)
{
lean_object* v_unused_1035_; 
v_unused_1035_ = lean_ctor_get(v___x_1022_, 0);
lean_dec(v_unused_1035_);
v___x_1024_ = v___x_1022_;
v_isShared_1025_ = v_isSharedCheck_1034_;
goto v_resetjp_1023_;
}
else
{
lean_dec(v___x_1022_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1034_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1026_; lean_object* v_fst_1027_; uint8_t v___x_1028_; 
v___x_1026_ = lean_st_ref_get(v_a_1006_);
v_fst_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_fst_1027_);
lean_dec(v___x_1026_);
v___x_1028_ = lean_unbox(v_fst_1027_);
lean_dec(v_fst_1027_);
if (v___x_1028_ == 0)
{
lean_object* v___x_1029_; lean_object* v___x_1031_; 
v___x_1029_ = lean_box(0);
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 0, v___x_1029_);
v___x_1031_ = v___x_1024_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1029_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
else
{
lean_del_object(v___x_1024_);
goto _start;
}
}
}
else
{
return v___x_1022_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectProps_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1006_ = stack[0].m_obj;
lean_object* v_a_1007_ = stack[1].m_obj;
lean_object* v_a_1008_ = stack[2].m_obj;
lean_object* v_a_1009_ = stack[3].m_obj;
lean_object* v_a_1010_ = stack[4].m_obj;
lean_object* v_res_1039_;
v_res_1039_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectProps(v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_);
stack->m_obj
 = v_res_1039_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectProps___boxed(lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectProps(v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_);
lean_dec(v_a_1044_);
lean_dec_ref(v_a_1043_);
lean_dec(v_a_1042_);
lean_dec_ref(v_a_1041_);
lean_dec(v_a_1040_);
return v_res_1046_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed_spec__0(lean_object* v_as_1047_, size_t v_i_1048_, size_t v_stop_1049_, lean_object* v_b_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
uint8_t v___x_1057_; 
v___x_1057_ = lean_usize_dec_eq(v_i_1048_, v_stop_1049_);
if (v___x_1057_ == 0)
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1058_ = lean_array_uget_borrowed(v_as_1047_, v_i_1048_);
lean_inc(v___x_1058_);
v___x_1059_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar(v___x_1058_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v_a_1060_; size_t v___x_1061_; size_t v___x_1062_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_a_1060_);
lean_dec_ref_known(v___x_1059_, 1);
v___x_1061_ = ((size_t)1ULL);
v___x_1062_ = lean_usize_add(v_i_1048_, v___x_1061_);
v_i_1048_ = v___x_1062_;
v_b_1050_ = v_a_1060_;
goto _start;
}
else
{
return v___x_1059_;
}
}
else
{
lean_object* v___x_1064_; 
v___x_1064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1064_, 0, v_b_1050_);
return v___x_1064_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1047_ = stack[0].m_obj;
size_t v_i_1048_ = stack[1].m_num;
size_t v_stop_1049_ = stack[2].m_num;
lean_object* v_b_1050_ = stack[3].m_obj;
lean_object* v___y_1051_ = stack[4].m_obj;
lean_object* v___y_1052_ = stack[5].m_obj;
lean_object* v___y_1053_ = stack[6].m_obj;
lean_object* v___y_1054_ = stack[7].m_obj;
lean_object* v___y_1055_ = stack[8].m_obj;
lean_object* v_res_1065_;
v_res_1065_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed_spec__0(v_as_1047_, v_i_1048_, v_stop_1049_, v_b_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
stack->m_obj
 = v_res_1065_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed_spec__0___boxed(lean_object* v_as_1066_, lean_object* v_i_1067_, lean_object* v_stop_1068_, lean_object* v_b_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
size_t v_i_boxed_1076_; size_t v_stop_boxed_1077_; lean_object* v_res_1078_; 
v_i_boxed_1076_ = lean_unbox_usize(v_i_1067_);
lean_dec(v_i_1067_);
v_stop_boxed_1077_ = lean_unbox_usize(v_stop_1068_);
lean_dec(v_stop_1068_);
v_res_1078_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed_spec__0(v_as_1066_, v_i_boxed_1076_, v_stop_boxed_1077_, v_b_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec_ref(v_as_1066_);
return v_res_1078_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed(lean_object* v_mvarId_1079_, lean_object* v_toPreserve_1080_, uint8_t v_indirectProps_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_){
_start:
{
lean_object* v___y_1089_; lean_object* v___y_1104_; lean_object* v___x_1113_; 
v___x_1113_ = l_Lean_MVarId_getType(v_mvarId_1079_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_object* v_a_1114_; lean_object* v___x_1115_; lean_object* v_a_1116_; lean_object* v___x_1117_; 
v_a_1114_ = lean_ctor_get(v___x_1113_, 0);
lean_inc(v_a_1114_);
lean_dec_ref_known(v___x_1113_, 1);
v___x_1115_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars_spec__0___redArg(v_a_1114_, v_a_1084_);
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_a_1116_);
lean_dec_ref(v___x_1115_);
v___x_1117_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVars(v_a_1116_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v___x_1118_; lean_object* v___x_1119_; uint8_t v___x_1120_; 
lean_dec_ref_known(v___x_1117_, 1);
v___x_1118_ = lean_unsigned_to_nat(0u);
v___x_1119_ = lean_array_get_size(v_toPreserve_1080_);
v___x_1120_ = lean_nat_dec_lt(v___x_1118_, v___x_1119_);
if (v___x_1120_ == 0)
{
goto v___jp_1093_;
}
else
{
lean_object* v___x_1121_; uint8_t v___x_1122_; 
v___x_1121_ = lean_box(0);
v___x_1122_ = lean_nat_dec_le(v___x_1119_, v___x_1119_);
if (v___x_1122_ == 0)
{
if (v___x_1120_ == 0)
{
goto v___jp_1093_;
}
else
{
size_t v___x_1123_; size_t v___x_1124_; lean_object* v___x_1125_; 
v___x_1123_ = ((size_t)0ULL);
v___x_1124_ = lean_usize_of_nat(v___x_1119_);
v___x_1125_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed_spec__0(v_toPreserve_1080_, v___x_1123_, v___x_1124_, v___x_1121_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
v___y_1104_ = v___x_1125_;
goto v___jp_1103_;
}
}
else
{
size_t v___x_1126_; size_t v___x_1127_; lean_object* v___x_1128_; 
v___x_1126_ = ((size_t)0ULL);
v___x_1127_ = lean_usize_of_nat(v___x_1119_);
v___x_1128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed_spec__0(v_toPreserve_1080_, v___x_1126_, v___x_1127_, v___x_1121_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
v___y_1104_ = v___x_1128_;
goto v___jp_1103_;
}
}
}
else
{
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1136_; 
v_a_1129_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1131_ = v___x_1117_;
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v___x_1117_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1134_; 
if (v_isShared_1132_ == 0)
{
v___x_1134_ = v___x_1131_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_a_1129_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
}
else
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1144_; 
v_a_1137_ = lean_ctor_get(v___x_1113_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1139_ = v___x_1113_;
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1113_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1142_; 
if (v_isShared_1140_ == 0)
{
v___x_1142_ = v___x_1139_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_a_1137_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
v___jp_1088_:
{
lean_object* v___x_1090_; lean_object* v_snd_1091_; lean_object* v___x_1092_; 
v___x_1090_ = lean_st_ref_get(v___y_1089_);
v_snd_1091_ = lean_ctor_get(v___x_1090_, 1);
lean_inc(v_snd_1091_);
lean_dec(v___x_1090_);
v___x_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1092_, 0, v_snd_1091_);
return v___x_1092_;
}
v___jp_1093_:
{
if (v_indirectProps_1081_ == 0)
{
v___y_1089_ = v_a_1082_;
goto v___jp_1088_;
}
else
{
lean_object* v___x_1094_; 
v___x_1094_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectProps(v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
if (lean_obj_tag(v___x_1094_) == 0)
{
lean_dec_ref_known(v___x_1094_, 1);
v___y_1089_ = v_a_1082_;
goto v___jp_1088_;
}
else
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
v_a_1095_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___x_1094_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1094_);
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
v___jp_1103_:
{
if (lean_obj_tag(v___y_1104_) == 0)
{
lean_dec_ref_known(v___y_1104_, 1);
goto v___jp_1093_;
}
else
{
lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1112_; 
v_a_1105_ = lean_ctor_get(v___y_1104_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___y_1104_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1107_ = v___y_1104_;
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_dec(v___y_1104_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1110_; 
if (v_isShared_1108_ == 0)
{
v___x_1110_ = v___x_1107_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_a_1105_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1079_ = stack[0].m_obj;
lean_object* v_toPreserve_1080_ = stack[1].m_obj;
uint8_t v_indirectProps_1081_ = stack[2].m_num;
lean_object* v_a_1082_ = stack[3].m_obj;
lean_object* v_a_1083_ = stack[4].m_obj;
lean_object* v_a_1084_ = stack[5].m_obj;
lean_object* v_a_1085_ = stack[6].m_obj;
lean_object* v_a_1086_ = stack[7].m_obj;
lean_object* v_res_1145_;
v_res_1145_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed(v_mvarId_1079_, v_toPreserve_1080_, v_indirectProps_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
stack->m_obj
 = v_res_1145_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed___boxed(lean_object* v_mvarId_1146_, lean_object* v_toPreserve_1147_, lean_object* v_indirectProps_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_){
_start:
{
uint8_t v_indirectProps_boxed_1155_; lean_object* v_res_1156_; 
v_indirectProps_boxed_1155_ = lean_unbox(v_indirectProps_1148_);
v_res_1156_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed(v_mvarId_1146_, v_toPreserve_1147_, v_indirectProps_boxed_1155_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_);
lean_dec(v_a_1153_);
lean_dec_ref(v_a_1152_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec_ref(v_toPreserve_1147_);
return v_res_1156_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___redArg(lean_object* v_e_1157_, lean_object* v___y_1158_){
_start:
{
uint8_t v___x_1160_; 
v___x_1160_ = l_Lean_Expr_hasMVar(v_e_1157_);
if (v___x_1160_ == 0)
{
lean_object* v___x_1161_; 
v___x_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1161_, 0, v_e_1157_);
return v___x_1161_;
}
else
{
lean_object* v___x_1162_; lean_object* v_mctx_1163_; lean_object* v___x_1164_; lean_object* v_fst_1165_; lean_object* v_snd_1166_; lean_object* v___x_1167_; lean_object* v_cache_1168_; lean_object* v_zetaDeltaFVarIds_1169_; lean_object* v_postponed_1170_; lean_object* v_diag_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1180_; 
v___x_1162_ = lean_st_ref_get(v___y_1158_);
v_mctx_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc_ref(v_mctx_1163_);
lean_dec(v___x_1162_);
v___x_1164_ = l_Lean_instantiateMVarsCore(v_mctx_1163_, v_e_1157_);
v_fst_1165_ = lean_ctor_get(v___x_1164_, 0);
lean_inc(v_fst_1165_);
v_snd_1166_ = lean_ctor_get(v___x_1164_, 1);
lean_inc(v_snd_1166_);
lean_dec_ref(v___x_1164_);
v___x_1167_ = lean_st_ref_take(v___y_1158_);
v_cache_1168_ = lean_ctor_get(v___x_1167_, 1);
v_zetaDeltaFVarIds_1169_ = lean_ctor_get(v___x_1167_, 2);
v_postponed_1170_ = lean_ctor_get(v___x_1167_, 3);
v_diag_1171_ = lean_ctor_get(v___x_1167_, 4);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1180_ == 0)
{
lean_object* v_unused_1181_; 
v_unused_1181_ = lean_ctor_get(v___x_1167_, 0);
lean_dec(v_unused_1181_);
v___x_1173_ = v___x_1167_;
v_isShared_1174_ = v_isSharedCheck_1180_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_diag_1171_);
lean_inc(v_postponed_1170_);
lean_inc(v_zetaDeltaFVarIds_1169_);
lean_inc(v_cache_1168_);
lean_dec(v___x_1167_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1180_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1176_; 
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 0, v_snd_1166_);
v___x_1176_ = v___x_1173_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_snd_1166_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v_cache_1168_);
lean_ctor_set(v_reuseFailAlloc_1179_, 2, v_zetaDeltaFVarIds_1169_);
lean_ctor_set(v_reuseFailAlloc_1179_, 3, v_postponed_1170_);
lean_ctor_set(v_reuseFailAlloc_1179_, 4, v_diag_1171_);
v___x_1176_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = lean_st_ref_put(v___y_1158_, v___x_1176_);
v___x_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1178_, 0, v_fst_1165_);
return v___x_1178_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1157_ = stack[0].m_obj;
lean_object* v___y_1158_ = stack[1].m_obj;
lean_object* v_res_1182_;
v_res_1182_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___redArg(v_e_1157_, v___y_1158_);
stack->m_obj
 = v_res_1182_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___redArg___boxed(lean_object* v_e_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___redArg(v_e_1183_, v___y_1184_);
lean_dec(v___y_1184_);
return v_res_1186_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1(lean_object* v_e_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v___x_1193_; 
v___x_1193_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___redArg(v_e_1187_, v___y_1189_);
return v___x_1193_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1187_ = stack[0].m_obj;
lean_object* v___y_1188_ = stack[1].m_obj;
lean_object* v___y_1189_ = stack[2].m_obj;
lean_object* v___y_1190_ = stack[3].m_obj;
lean_object* v___y_1191_ = stack[4].m_obj;
lean_object* v_res_1194_;
v_res_1194_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1(v_e_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
stack->m_obj
 = v_res_1194_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___boxed(lean_object* v_e_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1(v_e_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
return v_res_1201_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___redArg(lean_object* v_mvarId_1202_, lean_object* v_x_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
lean_object* v___x_1209_; 
v___x_1209_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1202_, v_x_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1217_; 
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1212_ = v___x_1209_;
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1209_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1215_; 
if (v_isShared_1213_ == 0)
{
v___x_1215_ = v___x_1212_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_a_1210_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
else
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1225_; 
v_a_1218_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1220_ = v___x_1209_;
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1209_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1223_; 
if (v_isShared_1221_ == 0)
{
v___x_1223_ = v___x_1220_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1218_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1202_ = stack[0].m_obj;
lean_object* v_x_1203_ = stack[1].m_obj;
lean_object* v___y_1204_ = stack[2].m_obj;
lean_object* v___y_1205_ = stack[3].m_obj;
lean_object* v___y_1206_ = stack[4].m_obj;
lean_object* v___y_1207_ = stack[5].m_obj;
lean_object* v_res_1226_;
v_res_1226_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___redArg(v_mvarId_1202_, v_x_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
stack->m_obj
 = v_res_1226_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___redArg___boxed(lean_object* v_mvarId_1227_, lean_object* v_x_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___redArg(v_mvarId_1227_, v_x_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
return v_res_1234_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4(lean_object* v_00_u03b1_1235_, lean_object* v_mvarId_1236_, lean_object* v_x_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
lean_object* v___x_1243_; 
v___x_1243_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___redArg(v_mvarId_1236_, v_x_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
return v___x_1243_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1236_ = stack[1].m_obj;
lean_object* v_x_1237_ = stack[2].m_obj;
lean_object* v___y_1238_ = stack[3].m_obj;
lean_object* v___y_1239_ = stack[4].m_obj;
lean_object* v___y_1240_ = stack[5].m_obj;
lean_object* v___y_1241_ = stack[6].m_obj;
lean_object* v_res_1244_;
v_res_1244_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4(lean_box(0), v_mvarId_1236_, v_x_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
stack->m_obj
 = v_res_1244_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___boxed(lean_object* v_00_u03b1_1245_, lean_object* v_mvarId_1246_, lean_object* v_x_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
lean_object* v_res_1253_; 
v_res_1253_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4(v_00_u03b1_1245_, v_mvarId_1246_, v_x_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
return v_res_1253_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__3(lean_object* v_a_1254_, lean_object* v_as_1255_, size_t v_i_1256_, size_t v_stop_1257_, lean_object* v_b_1258_){
_start:
{
lean_object* v___y_1260_; uint8_t v___x_1264_; 
v___x_1264_ = lean_usize_dec_eq(v_i_1256_, v_stop_1257_);
if (v___x_1264_ == 0)
{
lean_object* v___x_1265_; lean_object* v_fvar_1266_; lean_object* v___x_1267_; uint8_t v___x_1268_; 
v___x_1265_ = lean_array_uget_borrowed(v_as_1255_, v_i_1256_);
v_fvar_1266_ = lean_ctor_get(v___x_1265_, 1);
v___x_1267_ = l_Lean_Expr_fvarId_x21(v_fvar_1266_);
v___x_1268_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_1267_, v_a_1254_);
lean_dec(v___x_1267_);
if (v___x_1268_ == 0)
{
v___y_1260_ = v_b_1258_;
goto v___jp_1259_;
}
else
{
lean_object* v___x_1269_; 
lean_inc(v___x_1265_);
v___x_1269_ = lean_array_push(v_b_1258_, v___x_1265_);
v___y_1260_ = v___x_1269_;
goto v___jp_1259_;
}
}
else
{
return v_b_1258_;
}
v___jp_1259_:
{
size_t v___x_1261_; size_t v___x_1262_; 
v___x_1261_ = ((size_t)1ULL);
v___x_1262_ = lean_usize_add(v_i_1256_, v___x_1261_);
v_i_1256_ = v___x_1262_;
v_b_1258_ = v___y_1260_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1254_ = stack[0].m_obj;
lean_object* v_as_1255_ = stack[1].m_obj;
size_t v_i_1256_ = stack[2].m_num;
size_t v_stop_1257_ = stack[3].m_num;
lean_object* v_b_1258_ = stack[4].m_obj;
lean_object* v_res_1270_;
v_res_1270_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__3(v_a_1254_, v_as_1255_, v_i_1256_, v_stop_1257_, v_b_1258_);
stack->m_obj
 = v_res_1270_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__3___boxed(lean_object* v_a_1271_, lean_object* v_as_1272_, lean_object* v_i_1273_, lean_object* v_stop_1274_, lean_object* v_b_1275_){
_start:
{
size_t v_i_boxed_1276_; size_t v_stop_boxed_1277_; lean_object* v_res_1278_; 
v_i_boxed_1276_ = lean_unbox_usize(v_i_1273_);
lean_dec(v_i_1273_);
v_stop_boxed_1277_ = lean_unbox_usize(v_stop_1274_);
lean_dec(v_stop_1274_);
v_res_1278_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__3(v_a_1271_, v_as_1272_, v_i_boxed_1276_, v_stop_boxed_1277_, v_b_1275_);
lean_dec_ref(v_as_1272_);
lean_dec(v_a_1271_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12_spec__13___redArg(lean_object* v_x_1279_, lean_object* v_x_1280_, lean_object* v_x_1281_, lean_object* v_x_1282_){
_start:
{
lean_object* v_ks_1283_; lean_object* v_vs_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1308_; 
v_ks_1283_ = lean_ctor_get(v_x_1279_, 0);
v_vs_1284_ = lean_ctor_get(v_x_1279_, 1);
v_isSharedCheck_1308_ = !lean_is_exclusive(v_x_1279_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1286_ = v_x_1279_;
v_isShared_1287_ = v_isSharedCheck_1308_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_vs_1284_);
lean_inc(v_ks_1283_);
lean_dec(v_x_1279_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1308_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1288_; uint8_t v___x_1289_; 
v___x_1288_ = lean_array_get_size(v_ks_1283_);
v___x_1289_ = lean_nat_dec_lt(v_x_1280_, v___x_1288_);
if (v___x_1289_ == 0)
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1293_; 
lean_dec(v_x_1280_);
v___x_1290_ = lean_array_push(v_ks_1283_, v_x_1281_);
v___x_1291_ = lean_array_push(v_vs_1284_, v_x_1282_);
if (v_isShared_1287_ == 0)
{
lean_ctor_set(v___x_1286_, 1, v___x_1291_);
lean_ctor_set(v___x_1286_, 0, v___x_1290_);
v___x_1293_ = v___x_1286_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1290_);
lean_ctor_set(v_reuseFailAlloc_1294_, 1, v___x_1291_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
else
{
lean_object* v_k_x27_1295_; uint8_t v___x_1296_; 
v_k_x27_1295_ = lean_array_fget_borrowed(v_ks_1283_, v_x_1280_);
v___x_1296_ = l_Lean_instBEqMVarId_beq(v_x_1281_, v_k_x27_1295_);
if (v___x_1296_ == 0)
{
lean_object* v___x_1298_; 
if (v_isShared_1287_ == 0)
{
v___x_1298_ = v___x_1286_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_ks_1283_);
lean_ctor_set(v_reuseFailAlloc_1302_, 1, v_vs_1284_);
v___x_1298_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1299_ = lean_unsigned_to_nat(1u);
v___x_1300_ = lean_nat_add(v_x_1280_, v___x_1299_);
lean_dec(v_x_1280_);
v_x_1279_ = v___x_1298_;
v_x_1280_ = v___x_1300_;
goto _start;
}
}
else
{
lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1306_; 
v___x_1303_ = lean_array_fset(v_ks_1283_, v_x_1280_, v_x_1281_);
v___x_1304_ = lean_array_fset(v_vs_1284_, v_x_1280_, v_x_1282_);
lean_dec(v_x_1280_);
if (v_isShared_1287_ == 0)
{
lean_ctor_set(v___x_1286_, 1, v___x_1304_);
lean_ctor_set(v___x_1286_, 0, v___x_1303_);
v___x_1306_ = v___x_1286_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v___x_1303_);
lean_ctor_set(v_reuseFailAlloc_1307_, 1, v___x_1304_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12___redArg(lean_object* v_n_1309_, lean_object* v_k_1310_, lean_object* v_v_1311_){
_start:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1312_ = lean_unsigned_to_nat(0u);
v___x_1313_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12_spec__13___redArg(v_n_1309_, v___x_1312_, v_k_1310_, v_v_1311_);
return v___x_1313_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1314_; 
v___x_1314_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1314_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg(lean_object* v_x_1315_, size_t v_x_1316_, size_t v_x_1317_, lean_object* v_x_1318_, lean_object* v_x_1319_){
_start:
{
if (lean_obj_tag(v_x_1315_) == 0)
{
lean_object* v_es_1320_; size_t v___x_1321_; size_t v___x_1322_; lean_object* v_j_1323_; lean_object* v___x_1324_; uint8_t v___x_1325_; 
v_es_1320_ = lean_ctor_get(v_x_1315_, 0);
v___x_1321_ = ((size_t)31ULL);
v___x_1322_ = lean_usize_land(v_x_1316_, v___x_1321_);
v_j_1323_ = lean_usize_to_nat(v___x_1322_);
v___x_1324_ = lean_array_get_size(v_es_1320_);
v___x_1325_ = lean_nat_dec_lt(v_j_1323_, v___x_1324_);
if (v___x_1325_ == 0)
{
lean_dec(v_j_1323_);
lean_dec(v_x_1319_);
lean_dec(v_x_1318_);
return v_x_1315_;
}
else
{
lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1364_; 
lean_inc_ref(v_es_1320_);
v_isSharedCheck_1364_ = !lean_is_exclusive(v_x_1315_);
if (v_isSharedCheck_1364_ == 0)
{
lean_object* v_unused_1365_; 
v_unused_1365_ = lean_ctor_get(v_x_1315_, 0);
lean_dec(v_unused_1365_);
v___x_1327_ = v_x_1315_;
v_isShared_1328_ = v_isSharedCheck_1364_;
goto v_resetjp_1326_;
}
else
{
lean_dec(v_x_1315_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1364_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v_v_1329_; lean_object* v___x_1330_; lean_object* v_xs_x27_1331_; lean_object* v___y_1333_; 
v_v_1329_ = lean_array_fget(v_es_1320_, v_j_1323_);
v___x_1330_ = lean_box(0);
v_xs_x27_1331_ = lean_array_fset(v_es_1320_, v_j_1323_, v___x_1330_);
switch(lean_obj_tag(v_v_1329_))
{
case 0:
{
lean_object* v_key_1338_; lean_object* v_val_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1349_; 
v_key_1338_ = lean_ctor_get(v_v_1329_, 0);
v_val_1339_ = lean_ctor_get(v_v_1329_, 1);
v_isSharedCheck_1349_ = !lean_is_exclusive(v_v_1329_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1341_ = v_v_1329_;
v_isShared_1342_ = v_isSharedCheck_1349_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_val_1339_);
lean_inc(v_key_1338_);
lean_dec(v_v_1329_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1349_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
uint8_t v___x_1343_; 
v___x_1343_ = l_Lean_instBEqMVarId_beq(v_x_1318_, v_key_1338_);
if (v___x_1343_ == 0)
{
lean_object* v___x_1344_; lean_object* v___x_1345_; 
lean_del_object(v___x_1341_);
v___x_1344_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1338_, v_val_1339_, v_x_1318_, v_x_1319_);
v___x_1345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1344_);
v___y_1333_ = v___x_1345_;
goto v___jp_1332_;
}
else
{
lean_object* v___x_1347_; 
lean_dec(v_val_1339_);
lean_dec(v_key_1338_);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 1, v_x_1319_);
lean_ctor_set(v___x_1341_, 0, v_x_1318_);
v___x_1347_ = v___x_1341_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_x_1318_);
lean_ctor_set(v_reuseFailAlloc_1348_, 1, v_x_1319_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
v___y_1333_ = v___x_1347_;
goto v___jp_1332_;
}
}
}
}
case 1:
{
lean_object* v_node_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1362_; 
v_node_1350_ = lean_ctor_get(v_v_1329_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v_v_1329_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1352_ = v_v_1329_;
v_isShared_1353_ = v_isSharedCheck_1362_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_node_1350_);
lean_dec(v_v_1329_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1362_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
size_t v___x_1354_; size_t v___x_1355_; size_t v___x_1356_; size_t v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1360_; 
v___x_1354_ = ((size_t)5ULL);
v___x_1355_ = lean_usize_shift_right(v_x_1316_, v___x_1354_);
v___x_1356_ = ((size_t)1ULL);
v___x_1357_ = lean_usize_add(v_x_1317_, v___x_1356_);
v___x_1358_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg(v_node_1350_, v___x_1355_, v___x_1357_, v_x_1318_, v_x_1319_);
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 0, v___x_1358_);
v___x_1360_ = v___x_1352_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1358_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
v___y_1333_ = v___x_1360_;
goto v___jp_1332_;
}
}
}
default: 
{
lean_object* v___x_1363_; 
v___x_1363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1363_, 0, v_x_1318_);
lean_ctor_set(v___x_1363_, 1, v_x_1319_);
v___y_1333_ = v___x_1363_;
goto v___jp_1332_;
}
}
v___jp_1332_:
{
lean_object* v___x_1334_; lean_object* v___x_1336_; 
v___x_1334_ = lean_array_fset(v_xs_x27_1331_, v_j_1323_, v___y_1333_);
lean_dec(v_j_1323_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 0, v___x_1334_);
v___x_1336_ = v___x_1327_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v___x_1334_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
}
}
}
else
{
lean_object* v_ks_1366_; lean_object* v_vs_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1385_; 
v_ks_1366_ = lean_ctor_get(v_x_1315_, 0);
v_vs_1367_ = lean_ctor_get(v_x_1315_, 1);
v_isSharedCheck_1385_ = !lean_is_exclusive(v_x_1315_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1369_ = v_x_1315_;
v_isShared_1370_ = v_isSharedCheck_1385_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_vs_1367_);
lean_inc(v_ks_1366_);
lean_dec(v_x_1315_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1385_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1372_; 
if (v_isShared_1370_ == 0)
{
v___x_1372_ = v___x_1369_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_ks_1366_);
lean_ctor_set(v_reuseFailAlloc_1384_, 1, v_vs_1367_);
v___x_1372_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
lean_object* v_newNode_1373_; size_t v___x_1374_; uint8_t v___x_1375_; 
v_newNode_1373_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12___redArg(v___x_1372_, v_x_1318_, v_x_1319_);
v___x_1374_ = ((size_t)7ULL);
v___x_1375_ = lean_usize_dec_le(v___x_1374_, v_x_1317_);
if (v___x_1375_ == 0)
{
lean_object* v___x_1376_; lean_object* v___x_1377_; uint8_t v___x_1378_; 
v___x_1376_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1373_);
v___x_1377_ = lean_unsigned_to_nat(4u);
v___x_1378_ = lean_nat_dec_lt(v___x_1376_, v___x_1377_);
lean_dec(v___x_1376_);
if (v___x_1378_ == 0)
{
lean_object* v_ks_1379_; lean_object* v_vs_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v_ks_1379_ = lean_ctor_get(v_newNode_1373_, 0);
lean_inc_ref(v_ks_1379_);
v_vs_1380_ = lean_ctor_get(v_newNode_1373_, 1);
lean_inc_ref(v_vs_1380_);
lean_dec_ref(v_newNode_1373_);
v___x_1381_ = lean_unsigned_to_nat(0u);
v___x_1382_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___closed__0);
v___x_1383_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___redArg(v_x_1317_, v_ks_1379_, v_vs_1380_, v___x_1381_, v___x_1382_);
lean_dec_ref(v_vs_1380_);
lean_dec_ref(v_ks_1379_);
return v___x_1383_;
}
else
{
return v_newNode_1373_;
}
}
else
{
return v_newNode_1373_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1315_ = stack[0].m_obj;
size_t v_x_1316_ = stack[1].m_num;
size_t v_x_1317_ = stack[2].m_num;
lean_object* v_x_1318_ = stack[3].m_obj;
lean_object* v_x_1319_ = stack[4].m_obj;
lean_object* v_res_1386_;
v_res_1386_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg(v_x_1315_, v_x_1316_, v_x_1317_, v_x_1318_, v_x_1319_);
stack->m_obj
 = v_res_1386_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___redArg(size_t v_depth_1387_, lean_object* v_keys_1388_, lean_object* v_vals_1389_, lean_object* v_i_1390_, lean_object* v_entries_1391_){
_start:
{
lean_object* v___x_1392_; uint8_t v___x_1393_; 
v___x_1392_ = lean_array_get_size(v_keys_1388_);
v___x_1393_ = lean_nat_dec_lt(v_i_1390_, v___x_1392_);
if (v___x_1393_ == 0)
{
lean_dec(v_i_1390_);
return v_entries_1391_;
}
else
{
lean_object* v_k_1394_; lean_object* v_v_1395_; uint64_t v___x_1396_; size_t v_h_1397_; size_t v___x_1398_; lean_object* v___x_1399_; size_t v___x_1400_; size_t v___x_1401_; size_t v___x_1402_; size_t v_h_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v_k_1394_ = lean_array_fget_borrowed(v_keys_1388_, v_i_1390_);
v_v_1395_ = lean_array_fget_borrowed(v_vals_1389_, v_i_1390_);
v___x_1396_ = l_Lean_instHashableMVarId_hash(v_k_1394_);
v_h_1397_ = lean_uint64_to_usize(v___x_1396_);
v___x_1398_ = ((size_t)5ULL);
v___x_1399_ = lean_unsigned_to_nat(1u);
v___x_1400_ = ((size_t)1ULL);
v___x_1401_ = lean_usize_sub(v_depth_1387_, v___x_1400_);
v___x_1402_ = lean_usize_mul(v___x_1398_, v___x_1401_);
v_h_1403_ = lean_usize_shift_right(v_h_1397_, v___x_1402_);
v___x_1404_ = lean_nat_add(v_i_1390_, v___x_1399_);
lean_dec(v_i_1390_);
lean_inc(v_v_1395_);
lean_inc(v_k_1394_);
v___x_1405_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg(v_entries_1391_, v_h_1403_, v_depth_1387_, v_k_1394_, v_v_1395_);
v_i_1390_ = v___x_1404_;
v_entries_1391_ = v___x_1405_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1387_ = stack[0].m_num;
lean_object* v_keys_1388_ = stack[1].m_obj;
lean_object* v_vals_1389_ = stack[2].m_obj;
lean_object* v_i_1390_ = stack[3].m_obj;
lean_object* v_entries_1391_ = stack[4].m_obj;
lean_object* v_res_1407_;
v_res_1407_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___redArg(v_depth_1387_, v_keys_1388_, v_vals_1389_, v_i_1390_, v_entries_1391_);
stack->m_obj
 = v_res_1407_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___redArg___boxed(lean_object* v_depth_1408_, lean_object* v_keys_1409_, lean_object* v_vals_1410_, lean_object* v_i_1411_, lean_object* v_entries_1412_){
_start:
{
size_t v_depth_boxed_1413_; lean_object* v_res_1414_; 
v_depth_boxed_1413_ = lean_unbox_usize(v_depth_1408_);
lean_dec(v_depth_1408_);
v_res_1414_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___redArg(v_depth_boxed_1413_, v_keys_1409_, v_vals_1410_, v_i_1411_, v_entries_1412_);
lean_dec_ref(v_vals_1410_);
lean_dec_ref(v_keys_1409_);
return v_res_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg___boxed(lean_object* v_x_1415_, lean_object* v_x_1416_, lean_object* v_x_1417_, lean_object* v_x_1418_, lean_object* v_x_1419_){
_start:
{
size_t v_x_7529__boxed_1420_; size_t v_x_7530__boxed_1421_; lean_object* v_res_1422_; 
v_x_7529__boxed_1420_ = lean_unbox_usize(v_x_1416_);
lean_dec(v_x_1416_);
v_x_7530__boxed_1421_ = lean_unbox_usize(v_x_1417_);
lean_dec(v_x_1417_);
v_res_1422_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg(v_x_1415_, v_x_7529__boxed_1420_, v_x_7530__boxed_1421_, v_x_1418_, v_x_1419_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4___redArg(lean_object* v_x_1423_, lean_object* v_x_1424_, lean_object* v_x_1425_){
_start:
{
uint64_t v___x_1426_; size_t v___x_1427_; size_t v___x_1428_; lean_object* v___x_1429_; 
v___x_1426_ = l_Lean_instHashableMVarId_hash(v_x_1424_);
v___x_1427_ = lean_uint64_to_usize(v___x_1426_);
v___x_1428_ = ((size_t)1ULL);
v___x_1429_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg(v_x_1423_, v___x_1427_, v___x_1428_, v_x_1424_, v_x_1425_);
return v___x_1429_;
}
}
lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___redArg(lean_object* v_mvarId_1430_, lean_object* v_val_1431_, lean_object* v___y_1432_){
_start:
{
lean_object* v___x_1434_; lean_object* v_mctx_1435_; lean_object* v_cache_1436_; lean_object* v_zetaDeltaFVarIds_1437_; lean_object* v_postponed_1438_; lean_object* v_diag_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1469_; 
v___x_1434_ = lean_st_ref_take(v___y_1432_);
v_mctx_1435_ = lean_ctor_get(v___x_1434_, 0);
v_cache_1436_ = lean_ctor_get(v___x_1434_, 1);
v_zetaDeltaFVarIds_1437_ = lean_ctor_get(v___x_1434_, 2);
v_postponed_1438_ = lean_ctor_get(v___x_1434_, 3);
v_diag_1439_ = lean_ctor_get(v___x_1434_, 4);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1441_ = v___x_1434_;
v_isShared_1442_ = v_isSharedCheck_1469_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_diag_1439_);
lean_inc(v_postponed_1438_);
lean_inc(v_zetaDeltaFVarIds_1437_);
lean_inc(v_cache_1436_);
lean_inc(v_mctx_1435_);
lean_dec(v___x_1434_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1469_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v_depth_1443_; lean_object* v_levelAssignDepth_1444_; lean_object* v_lmvarCounter_1445_; lean_object* v_mvarCounter_1446_; lean_object* v_lDecls_1447_; lean_object* v_decls_1448_; lean_object* v_userNames_1449_; lean_object* v_lAssignment_1450_; lean_object* v_eAssignment_1451_; lean_object* v_dAssignment_1452_; lean_object* v_instanceTypedMVars_1453_; lean_object* v_synthNormMemo_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1468_; 
v_depth_1443_ = lean_ctor_get(v_mctx_1435_, 0);
v_levelAssignDepth_1444_ = lean_ctor_get(v_mctx_1435_, 1);
v_lmvarCounter_1445_ = lean_ctor_get(v_mctx_1435_, 2);
v_mvarCounter_1446_ = lean_ctor_get(v_mctx_1435_, 3);
v_lDecls_1447_ = lean_ctor_get(v_mctx_1435_, 4);
v_decls_1448_ = lean_ctor_get(v_mctx_1435_, 5);
v_userNames_1449_ = lean_ctor_get(v_mctx_1435_, 6);
v_lAssignment_1450_ = lean_ctor_get(v_mctx_1435_, 7);
v_eAssignment_1451_ = lean_ctor_get(v_mctx_1435_, 8);
v_dAssignment_1452_ = lean_ctor_get(v_mctx_1435_, 9);
v_instanceTypedMVars_1453_ = lean_ctor_get(v_mctx_1435_, 10);
v_synthNormMemo_1454_ = lean_ctor_get(v_mctx_1435_, 11);
v_isSharedCheck_1468_ = !lean_is_exclusive(v_mctx_1435_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1456_ = v_mctx_1435_;
v_isShared_1457_ = v_isSharedCheck_1468_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_synthNormMemo_1454_);
lean_inc(v_instanceTypedMVars_1453_);
lean_inc(v_dAssignment_1452_);
lean_inc(v_eAssignment_1451_);
lean_inc(v_lAssignment_1450_);
lean_inc(v_userNames_1449_);
lean_inc(v_decls_1448_);
lean_inc(v_lDecls_1447_);
lean_inc(v_mvarCounter_1446_);
lean_inc(v_lmvarCounter_1445_);
lean_inc(v_levelAssignDepth_1444_);
lean_inc(v_depth_1443_);
lean_dec(v_mctx_1435_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1468_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1461_; 
v___x_1458_ = lean_box(0);
v___x_1459_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4___redArg(v_eAssignment_1451_, v_mvarId_1430_, v_val_1431_);
if (v_isShared_1457_ == 0)
{
lean_ctor_set(v___x_1456_, 8, v___x_1459_);
v___x_1461_ = v___x_1456_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_depth_1443_);
lean_ctor_set(v_reuseFailAlloc_1467_, 1, v_levelAssignDepth_1444_);
lean_ctor_set(v_reuseFailAlloc_1467_, 2, v_lmvarCounter_1445_);
lean_ctor_set(v_reuseFailAlloc_1467_, 3, v_mvarCounter_1446_);
lean_ctor_set(v_reuseFailAlloc_1467_, 4, v_lDecls_1447_);
lean_ctor_set(v_reuseFailAlloc_1467_, 5, v_decls_1448_);
lean_ctor_set(v_reuseFailAlloc_1467_, 6, v_userNames_1449_);
lean_ctor_set(v_reuseFailAlloc_1467_, 7, v_lAssignment_1450_);
lean_ctor_set(v_reuseFailAlloc_1467_, 8, v___x_1459_);
lean_ctor_set(v_reuseFailAlloc_1467_, 9, v_dAssignment_1452_);
lean_ctor_set(v_reuseFailAlloc_1467_, 10, v_instanceTypedMVars_1453_);
lean_ctor_set(v_reuseFailAlloc_1467_, 11, v_synthNormMemo_1454_);
v___x_1461_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
lean_object* v___x_1463_; 
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 0, v___x_1461_);
v___x_1463_ = v___x_1441_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v___x_1461_);
lean_ctor_set(v_reuseFailAlloc_1466_, 1, v_cache_1436_);
lean_ctor_set(v_reuseFailAlloc_1466_, 2, v_zetaDeltaFVarIds_1437_);
lean_ctor_set(v_reuseFailAlloc_1466_, 3, v_postponed_1438_);
lean_ctor_set(v_reuseFailAlloc_1466_, 4, v_diag_1439_);
v___x_1463_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1464_ = lean_st_ref_put(v___y_1432_, v___x_1463_);
v___x_1465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1458_);
return v___x_1465_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1430_ = stack[0].m_obj;
lean_object* v_val_1431_ = stack[1].m_obj;
lean_object* v___y_1432_ = stack[2].m_obj;
lean_object* v_res_1470_;
v_res_1470_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___redArg(v_mvarId_1430_, v_val_1431_, v___y_1432_);
stack->m_obj
 = v_res_1470_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___redArg___boxed(lean_object* v_mvarId_1471_, lean_object* v_val_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___redArg(v_mvarId_1471_, v_val_1472_, v___y_1473_);
lean_dec(v___y_1473_);
return v_res_1475_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___redArg(lean_object* v_a_1476_, lean_object* v_as_1477_, size_t v_sz_1478_, size_t v_i_1479_, lean_object* v_b_1480_){
_start:
{
uint8_t v___x_1482_; 
v___x_1482_ = lean_usize_dec_lt(v_i_1479_, v_sz_1478_);
if (v___x_1482_ == 0)
{
lean_object* v___x_1483_; 
v___x_1483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1483_, 0, v_b_1480_);
return v___x_1483_;
}
else
{
lean_object* v_snd_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1502_; 
v_snd_1484_ = lean_ctor_get(v_b_1480_, 1);
v_isSharedCheck_1502_ = !lean_is_exclusive(v_b_1480_);
if (v_isSharedCheck_1502_ == 0)
{
lean_object* v_unused_1503_; 
v_unused_1503_ = lean_ctor_get(v_b_1480_, 0);
lean_dec(v_unused_1503_);
v___x_1486_ = v_b_1480_;
v_isShared_1487_ = v_isSharedCheck_1502_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_snd_1484_);
lean_dec(v_b_1480_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1502_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1488_; lean_object* v_a_1490_; lean_object* v_a_1497_; 
v___x_1488_ = lean_box(0);
v_a_1497_ = lean_array_uget_borrowed(v_as_1477_, v_i_1479_);
if (lean_obj_tag(v_a_1497_) == 0)
{
v_a_1490_ = v_snd_1484_;
goto v___jp_1489_;
}
else
{
lean_object* v_val_1498_; lean_object* v___x_1499_; uint8_t v___x_1500_; 
v_val_1498_ = lean_ctor_get(v_a_1497_, 0);
v___x_1499_ = l_Lean_LocalDecl_fvarId(v_val_1498_);
v___x_1500_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_1499_, v_a_1476_);
if (v___x_1500_ == 0)
{
lean_object* v___x_1501_; 
v___x_1501_ = l_Lean_LocalContext_erase(v_snd_1484_, v___x_1499_);
lean_dec(v___x_1499_);
v_a_1490_ = v___x_1501_;
goto v___jp_1489_;
}
else
{
lean_dec(v___x_1499_);
v_a_1490_ = v_snd_1484_;
goto v___jp_1489_;
}
}
v___jp_1489_:
{
lean_object* v___x_1492_; 
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 1, v_a_1490_);
lean_ctor_set(v___x_1486_, 0, v___x_1488_);
v___x_1492_ = v___x_1486_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v___x_1488_);
lean_ctor_set(v_reuseFailAlloc_1496_, 1, v_a_1490_);
v___x_1492_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
size_t v___x_1493_; size_t v___x_1494_; 
v___x_1493_ = ((size_t)1ULL);
v___x_1494_ = lean_usize_add(v_i_1479_, v___x_1493_);
v_i_1479_ = v___x_1494_;
v_b_1480_ = v___x_1492_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1476_ = stack[0].m_obj;
lean_object* v_as_1477_ = stack[1].m_obj;
size_t v_sz_1478_ = stack[2].m_num;
size_t v_i_1479_ = stack[3].m_num;
lean_object* v_b_1480_ = stack[4].m_obj;
lean_object* v_res_1504_;
v_res_1504_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___redArg(v_a_1476_, v_as_1477_, v_sz_1478_, v_i_1479_, v_b_1480_);
stack->m_obj
 = v_res_1504_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___redArg___boxed(lean_object* v_a_1505_, lean_object* v_as_1506_, lean_object* v_sz_1507_, lean_object* v_i_1508_, lean_object* v_b_1509_, lean_object* v___y_1510_){
_start:
{
size_t v_sz_boxed_1511_; size_t v_i_boxed_1512_; lean_object* v_res_1513_; 
v_sz_boxed_1511_ = lean_unbox_usize(v_sz_1507_);
lean_dec(v_sz_1507_);
v_i_boxed_1512_ = lean_unbox_usize(v_i_1508_);
lean_dec(v_i_1508_);
v_res_1513_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___redArg(v_a_1505_, v_as_1506_, v_sz_boxed_1511_, v_i_boxed_1512_, v_b_1509_);
lean_dec_ref(v_as_1506_);
lean_dec(v_a_1505_);
return v_res_1513_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4(lean_object* v_a_1514_, lean_object* v_as_1515_, size_t v_sz_1516_, size_t v_i_1517_, lean_object* v_b_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
uint8_t v___x_1524_; 
v___x_1524_ = lean_usize_dec_lt(v_i_1517_, v_sz_1516_);
if (v___x_1524_ == 0)
{
lean_object* v___x_1525_; 
v___x_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1525_, 0, v_b_1518_);
return v___x_1525_;
}
else
{
lean_object* v_snd_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1544_; 
v_snd_1526_ = lean_ctor_get(v_b_1518_, 1);
v_isSharedCheck_1544_ = !lean_is_exclusive(v_b_1518_);
if (v_isSharedCheck_1544_ == 0)
{
lean_object* v_unused_1545_; 
v_unused_1545_ = lean_ctor_get(v_b_1518_, 0);
lean_dec(v_unused_1545_);
v___x_1528_ = v_b_1518_;
v_isShared_1529_ = v_isSharedCheck_1544_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_snd_1526_);
lean_dec(v_b_1518_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1544_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1530_; lean_object* v_a_1532_; lean_object* v_a_1539_; 
v___x_1530_ = lean_box(0);
v_a_1539_ = lean_array_uget_borrowed(v_as_1515_, v_i_1517_);
if (lean_obj_tag(v_a_1539_) == 0)
{
v_a_1532_ = v_snd_1526_;
goto v___jp_1531_;
}
else
{
lean_object* v_val_1540_; lean_object* v___x_1541_; uint8_t v___x_1542_; 
v_val_1540_ = lean_ctor_get(v_a_1539_, 0);
v___x_1541_ = l_Lean_LocalDecl_fvarId(v_val_1540_);
v___x_1542_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_1541_, v_a_1514_);
if (v___x_1542_ == 0)
{
lean_object* v___x_1543_; 
v___x_1543_ = l_Lean_LocalContext_erase(v_snd_1526_, v___x_1541_);
lean_dec(v___x_1541_);
v_a_1532_ = v___x_1543_;
goto v___jp_1531_;
}
else
{
lean_dec(v___x_1541_);
v_a_1532_ = v_snd_1526_;
goto v___jp_1531_;
}
}
v___jp_1531_:
{
lean_object* v___x_1534_; 
if (v_isShared_1529_ == 0)
{
lean_ctor_set(v___x_1528_, 1, v_a_1532_);
lean_ctor_set(v___x_1528_, 0, v___x_1530_);
v___x_1534_ = v___x_1528_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v___x_1530_);
lean_ctor_set(v_reuseFailAlloc_1538_, 1, v_a_1532_);
v___x_1534_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
size_t v___x_1535_; size_t v___x_1536_; lean_object* v___x_1537_; 
v___x_1535_ = ((size_t)1ULL);
v___x_1536_ = lean_usize_add(v_i_1517_, v___x_1535_);
v___x_1537_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___redArg(v_a_1514_, v_as_1515_, v_sz_1516_, v___x_1536_, v___x_1534_);
return v___x_1537_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1514_ = stack[0].m_obj;
lean_object* v_as_1515_ = stack[1].m_obj;
size_t v_sz_1516_ = stack[2].m_num;
size_t v_i_1517_ = stack[3].m_num;
lean_object* v_b_1518_ = stack[4].m_obj;
lean_object* v___y_1519_ = stack[5].m_obj;
lean_object* v___y_1520_ = stack[6].m_obj;
lean_object* v___y_1521_ = stack[7].m_obj;
lean_object* v___y_1522_ = stack[8].m_obj;
lean_object* v_res_1546_;
v_res_1546_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4(v_a_1514_, v_as_1515_, v_sz_1516_, v_i_1517_, v_b_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
stack->m_obj
 = v_res_1546_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4___boxed(lean_object* v_a_1547_, lean_object* v_as_1548_, lean_object* v_sz_1549_, lean_object* v_i_1550_, lean_object* v_b_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_){
_start:
{
size_t v_sz_boxed_1557_; size_t v_i_boxed_1558_; lean_object* v_res_1559_; 
v_sz_boxed_1557_ = lean_unbox_usize(v_sz_1549_);
lean_dec(v_sz_1549_);
v_i_boxed_1558_ = lean_unbox_usize(v_i_1550_);
lean_dec(v_i_1550_);
v_res_1559_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4(v_a_1547_, v_as_1548_, v_sz_boxed_1557_, v_i_boxed_1558_, v_b_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_);
lean_dec(v___y_1555_);
lean_dec_ref(v___y_1554_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
lean_dec_ref(v_as_1548_);
lean_dec(v_a_1547_);
return v_res_1559_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0(lean_object* v_init_1560_, lean_object* v_a_1561_, lean_object* v_n_1562_, lean_object* v_b_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_){
_start:
{
if (lean_obj_tag(v_n_1562_) == 0)
{
lean_object* v_cs_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; size_t v_sz_1572_; size_t v___x_1573_; lean_object* v___x_1574_; 
v_cs_1569_ = lean_ctor_get(v_n_1562_, 0);
v___x_1570_ = lean_box(0);
v___x_1571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1570_);
lean_ctor_set(v___x_1571_, 1, v_b_1563_);
v_sz_1572_ = lean_array_size(v_cs_1569_);
v___x_1573_ = ((size_t)0ULL);
v___x_1574_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__3(v_init_1560_, v_a_1561_, v_cs_1569_, v_sz_1572_, v___x_1573_, v___x_1571_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_);
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
else
{
lean_object* v_vs_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; size_t v_sz_1601_; size_t v___x_1602_; lean_object* v___x_1603_; 
v_vs_1598_ = lean_ctor_get(v_n_1562_, 0);
v___x_1599_ = lean_box(0);
v___x_1600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1599_);
lean_ctor_set(v___x_1600_, 1, v_b_1563_);
v_sz_1601_ = lean_array_size(v_vs_1598_);
v___x_1602_ = ((size_t)0ULL);
v___x_1603_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4(v_a_1561_, v_vs_1598_, v_sz_1601_, v___x_1602_, v___x_1600_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1618_; 
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1606_ = v___x_1603_;
v_isShared_1607_ = v_isSharedCheck_1618_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1603_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1618_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v_fst_1608_; 
v_fst_1608_ = lean_ctor_get(v_a_1604_, 0);
if (lean_obj_tag(v_fst_1608_) == 0)
{
lean_object* v_snd_1609_; lean_object* v___x_1610_; lean_object* v___x_1612_; 
v_snd_1609_ = lean_ctor_get(v_a_1604_, 1);
lean_inc(v_snd_1609_);
lean_dec(v_a_1604_);
v___x_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1610_, 0, v_snd_1609_);
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 0, v___x_1610_);
v___x_1612_ = v___x_1606_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___x_1610_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
else
{
lean_object* v_val_1614_; lean_object* v___x_1616_; 
lean_inc_ref(v_fst_1608_);
lean_dec(v_a_1604_);
v_val_1614_ = lean_ctor_get(v_fst_1608_, 0);
lean_inc(v_val_1614_);
lean_dec_ref_known(v_fst_1608_, 1);
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 0, v_val_1614_);
v___x_1616_ = v___x_1606_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_val_1614_);
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
else
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1626_; 
v_a_1619_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1621_ = v___x_1603_;
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1603_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1624_; 
if (v_isShared_1622_ == 0)
{
v___x_1624_ = v___x_1621_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1619_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_1560_ = stack[0].m_obj;
lean_object* v_a_1561_ = stack[1].m_obj;
lean_object* v_n_1562_ = stack[2].m_obj;
lean_object* v_b_1563_ = stack[3].m_obj;
lean_object* v___y_1564_ = stack[4].m_obj;
lean_object* v___y_1565_ = stack[5].m_obj;
lean_object* v___y_1566_ = stack[6].m_obj;
lean_object* v___y_1567_ = stack[7].m_obj;
lean_object* v_res_1627_;
v_res_1627_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0(v_init_1560_, v_a_1561_, v_n_1562_, v_b_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_);
stack->m_obj
 = v_res_1627_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__3(lean_object* v_init_1628_, lean_object* v_a_1629_, lean_object* v_as_1630_, size_t v_sz_1631_, size_t v_i_1632_, lean_object* v_b_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
uint8_t v___x_1639_; 
v___x_1639_ = lean_usize_dec_lt(v_i_1632_, v_sz_1631_);
if (v___x_1639_ == 0)
{
lean_object* v___x_1640_; 
v___x_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1640_, 0, v_b_1633_);
return v___x_1640_;
}
else
{
lean_object* v_snd_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1675_; 
v_snd_1641_ = lean_ctor_get(v_b_1633_, 1);
v_isSharedCheck_1675_ = !lean_is_exclusive(v_b_1633_);
if (v_isSharedCheck_1675_ == 0)
{
lean_object* v_unused_1676_; 
v_unused_1676_ = lean_ctor_get(v_b_1633_, 0);
lean_dec(v_unused_1676_);
v___x_1643_ = v_b_1633_;
v_isShared_1644_ = v_isSharedCheck_1675_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_snd_1641_);
lean_dec(v_b_1633_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1675_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1645_; lean_object* v_a_1646_; lean_object* v___x_1647_; 
v___x_1645_ = lean_box(0);
v_a_1646_ = lean_array_uget_borrowed(v_as_1630_, v_i_1632_);
lean_inc(v_snd_1641_);
v___x_1647_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0(v_init_1628_, v_a_1629_, v_a_1646_, v_snd_1641_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1666_; 
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1650_ = v___x_1647_;
v_isShared_1651_ = v_isSharedCheck_1666_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v___x_1647_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1666_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
if (lean_obj_tag(v_a_1648_) == 0)
{
lean_object* v___x_1652_; lean_object* v___x_1654_; 
v___x_1652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1652_, 0, v_a_1648_);
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 0, v___x_1652_);
v___x_1654_ = v___x_1643_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v___x_1652_);
lean_ctor_set(v_reuseFailAlloc_1658_, 1, v_snd_1641_);
v___x_1654_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
lean_object* v___x_1656_; 
if (v_isShared_1651_ == 0)
{
lean_ctor_set(v___x_1650_, 0, v___x_1654_);
v___x_1656_ = v___x_1650_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1654_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
else
{
lean_object* v_a_1659_; lean_object* v___x_1661_; 
lean_del_object(v___x_1650_);
lean_dec(v_snd_1641_);
v_a_1659_ = lean_ctor_get(v_a_1648_, 0);
lean_inc(v_a_1659_);
lean_dec_ref_known(v_a_1648_, 1);
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 1, v_a_1659_);
lean_ctor_set(v___x_1643_, 0, v___x_1645_);
v___x_1661_ = v___x_1643_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v___x_1645_);
lean_ctor_set(v_reuseFailAlloc_1665_, 1, v_a_1659_);
v___x_1661_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
size_t v___x_1662_; size_t v___x_1663_; 
v___x_1662_ = ((size_t)1ULL);
v___x_1663_ = lean_usize_add(v_i_1632_, v___x_1662_);
v_i_1632_ = v___x_1663_;
v_b_1633_ = v___x_1661_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1674_; 
lean_del_object(v___x_1643_);
lean_dec(v_snd_1641_);
v_a_1667_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1669_ = v___x_1647_;
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_a_1667_);
lean_dec(v___x_1647_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1672_; 
if (v_isShared_1670_ == 0)
{
v___x_1672_ = v___x_1669_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_a_1667_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_1628_ = stack[0].m_obj;
lean_object* v_a_1629_ = stack[1].m_obj;
lean_object* v_as_1630_ = stack[2].m_obj;
size_t v_sz_1631_ = stack[3].m_num;
size_t v_i_1632_ = stack[4].m_num;
lean_object* v_b_1633_ = stack[5].m_obj;
lean_object* v___y_1634_ = stack[6].m_obj;
lean_object* v___y_1635_ = stack[7].m_obj;
lean_object* v___y_1636_ = stack[8].m_obj;
lean_object* v___y_1637_ = stack[9].m_obj;
lean_object* v_res_1677_;
v_res_1677_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__3(v_init_1628_, v_a_1629_, v_as_1630_, v_sz_1631_, v_i_1632_, v_b_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
stack->m_obj
 = v_res_1677_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__3___boxed(lean_object* v_init_1678_, lean_object* v_a_1679_, lean_object* v_as_1680_, lean_object* v_sz_1681_, lean_object* v_i_1682_, lean_object* v_b_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_){
_start:
{
size_t v_sz_boxed_1689_; size_t v_i_boxed_1690_; lean_object* v_res_1691_; 
v_sz_boxed_1689_ = lean_unbox_usize(v_sz_1681_);
lean_dec(v_sz_1681_);
v_i_boxed_1690_ = lean_unbox_usize(v_i_1682_);
lean_dec(v_i_1682_);
v_res_1691_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__3(v_init_1678_, v_a_1679_, v_as_1680_, v_sz_boxed_1689_, v_i_boxed_1690_, v_b_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec_ref(v_as_1680_);
lean_dec(v_a_1679_);
lean_dec_ref(v_init_1678_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0___boxed(lean_object* v_init_1692_, lean_object* v_a_1693_, lean_object* v_n_1694_, lean_object* v_b_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0(v_init_1692_, v_a_1693_, v_n_1694_, v_b_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
lean_dec_ref(v_n_1694_);
lean_dec(v_a_1693_);
lean_dec_ref(v_init_1692_);
return v_res_1701_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___redArg(lean_object* v_a_1702_, lean_object* v_as_1703_, size_t v_sz_1704_, size_t v_i_1705_, lean_object* v_b_1706_){
_start:
{
uint8_t v___x_1708_; 
v___x_1708_ = lean_usize_dec_lt(v_i_1705_, v_sz_1704_);
if (v___x_1708_ == 0)
{
lean_object* v___x_1709_; 
v___x_1709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1709_, 0, v_b_1706_);
return v___x_1709_;
}
else
{
lean_object* v_snd_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1728_; 
v_snd_1710_ = lean_ctor_get(v_b_1706_, 1);
v_isSharedCheck_1728_ = !lean_is_exclusive(v_b_1706_);
if (v_isSharedCheck_1728_ == 0)
{
lean_object* v_unused_1729_; 
v_unused_1729_ = lean_ctor_get(v_b_1706_, 0);
lean_dec(v_unused_1729_);
v___x_1712_ = v_b_1706_;
v_isShared_1713_ = v_isSharedCheck_1728_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_snd_1710_);
lean_dec(v_b_1706_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1728_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1714_; lean_object* v_a_1716_; lean_object* v_a_1723_; 
v___x_1714_ = lean_box(0);
v_a_1723_ = lean_array_uget_borrowed(v_as_1703_, v_i_1705_);
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
v___x_1726_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_1725_, v_a_1702_);
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
size_t v___x_1719_; size_t v___x_1720_; 
v___x_1719_ = ((size_t)1ULL);
v___x_1720_ = lean_usize_add(v_i_1705_, v___x_1719_);
v_i_1705_ = v___x_1720_;
v_b_1706_ = v___x_1718_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1702_ = stack[0].m_obj;
lean_object* v_as_1703_ = stack[1].m_obj;
size_t v_sz_1704_ = stack[2].m_num;
size_t v_i_1705_ = stack[3].m_num;
lean_object* v_b_1706_ = stack[4].m_obj;
lean_object* v_res_1730_;
v_res_1730_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___redArg(v_a_1702_, v_as_1703_, v_sz_1704_, v_i_1705_, v_b_1706_);
stack->m_obj
 = v_res_1730_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___redArg___boxed(lean_object* v_a_1731_, lean_object* v_as_1732_, lean_object* v_sz_1733_, lean_object* v_i_1734_, lean_object* v_b_1735_, lean_object* v___y_1736_){
_start:
{
size_t v_sz_boxed_1737_; size_t v_i_boxed_1738_; lean_object* v_res_1739_; 
v_sz_boxed_1737_ = lean_unbox_usize(v_sz_1733_);
lean_dec(v_sz_1733_);
v_i_boxed_1738_ = lean_unbox_usize(v_i_1734_);
lean_dec(v_i_1734_);
v_res_1739_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___redArg(v_a_1731_, v_as_1732_, v_sz_boxed_1737_, v_i_boxed_1738_, v_b_1735_);
lean_dec_ref(v_as_1732_);
lean_dec(v_a_1731_);
return v_res_1739_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1(lean_object* v_a_1740_, lean_object* v_as_1741_, size_t v_sz_1742_, size_t v_i_1743_, lean_object* v_b_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
uint8_t v___x_1750_; 
v___x_1750_ = lean_usize_dec_lt(v_i_1743_, v_sz_1742_);
if (v___x_1750_ == 0)
{
lean_object* v___x_1751_; 
v___x_1751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1751_, 0, v_b_1744_);
return v___x_1751_;
}
else
{
lean_object* v_snd_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1770_; 
v_snd_1752_ = lean_ctor_get(v_b_1744_, 1);
v_isSharedCheck_1770_ = !lean_is_exclusive(v_b_1744_);
if (v_isSharedCheck_1770_ == 0)
{
lean_object* v_unused_1771_; 
v_unused_1771_ = lean_ctor_get(v_b_1744_, 0);
lean_dec(v_unused_1771_);
v___x_1754_ = v_b_1744_;
v_isShared_1755_ = v_isSharedCheck_1770_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_snd_1752_);
lean_dec(v_b_1744_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1770_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1756_; lean_object* v_a_1758_; lean_object* v_a_1765_; 
v___x_1756_ = lean_box(0);
v_a_1765_ = lean_array_uget_borrowed(v_as_1741_, v_i_1743_);
if (lean_obj_tag(v_a_1765_) == 0)
{
v_a_1758_ = v_snd_1752_;
goto v___jp_1757_;
}
else
{
lean_object* v_val_1766_; lean_object* v___x_1767_; uint8_t v___x_1768_; 
v_val_1766_ = lean_ctor_get(v_a_1765_, 0);
v___x_1767_ = l_Lean_LocalDecl_fvarId(v_val_1766_);
v___x_1768_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_addUsedFVar_spec__3___redArg(v___x_1767_, v_a_1740_);
if (v___x_1768_ == 0)
{
lean_object* v___x_1769_; 
v___x_1769_ = l_Lean_LocalContext_erase(v_snd_1752_, v___x_1767_);
lean_dec(v___x_1767_);
v_a_1758_ = v___x_1769_;
goto v___jp_1757_;
}
else
{
lean_dec(v___x_1767_);
v_a_1758_ = v_snd_1752_;
goto v___jp_1757_;
}
}
v___jp_1757_:
{
lean_object* v___x_1760_; 
if (v_isShared_1755_ == 0)
{
lean_ctor_set(v___x_1754_, 1, v_a_1758_);
lean_ctor_set(v___x_1754_, 0, v___x_1756_);
v___x_1760_ = v___x_1754_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v___x_1756_);
lean_ctor_set(v_reuseFailAlloc_1764_, 1, v_a_1758_);
v___x_1760_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
size_t v___x_1761_; size_t v___x_1762_; lean_object* v___x_1763_; 
v___x_1761_ = ((size_t)1ULL);
v___x_1762_ = lean_usize_add(v_i_1743_, v___x_1761_);
v___x_1763_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___redArg(v_a_1740_, v_as_1741_, v_sz_1742_, v___x_1762_, v___x_1760_);
return v___x_1763_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1740_ = stack[0].m_obj;
lean_object* v_as_1741_ = stack[1].m_obj;
size_t v_sz_1742_ = stack[2].m_num;
size_t v_i_1743_ = stack[3].m_num;
lean_object* v_b_1744_ = stack[4].m_obj;
lean_object* v___y_1745_ = stack[5].m_obj;
lean_object* v___y_1746_ = stack[6].m_obj;
lean_object* v___y_1747_ = stack[7].m_obj;
lean_object* v___y_1748_ = stack[8].m_obj;
lean_object* v_res_1772_;
v_res_1772_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1(v_a_1740_, v_as_1741_, v_sz_1742_, v_i_1743_, v_b_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
stack->m_obj
 = v_res_1772_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1___boxed(lean_object* v_a_1773_, lean_object* v_as_1774_, lean_object* v_sz_1775_, lean_object* v_i_1776_, lean_object* v_b_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_){
_start:
{
size_t v_sz_boxed_1783_; size_t v_i_boxed_1784_; lean_object* v_res_1785_; 
v_sz_boxed_1783_ = lean_unbox_usize(v_sz_1775_);
lean_dec(v_sz_1775_);
v_i_boxed_1784_ = lean_unbox_usize(v_i_1776_);
lean_dec(v_i_1776_);
v_res_1785_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1(v_a_1773_, v_as_1774_, v_sz_boxed_1783_, v_i_boxed_1784_, v_b_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec_ref(v_as_1774_);
lean_dec(v_a_1773_);
return v_res_1785_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0(lean_object* v_a_1786_, lean_object* v_t_1787_, lean_object* v_init_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v_root_1794_; lean_object* v_tail_1795_; lean_object* v___x_1796_; 
v_root_1794_ = lean_ctor_get(v_t_1787_, 0);
v_tail_1795_ = lean_ctor_get(v_t_1787_, 1);
lean_inc_ref(v_init_1788_);
v___x_1796_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0(v_init_1788_, v_a_1786_, v_root_1794_, v_init_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
lean_dec_ref(v_init_1788_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1833_; 
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1799_ = v___x_1796_;
v_isShared_1800_ = v_isSharedCheck_1833_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1796_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1833_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
if (lean_obj_tag(v_a_1797_) == 0)
{
lean_object* v_a_1801_; lean_object* v___x_1803_; 
v_a_1801_ = lean_ctor_get(v_a_1797_, 0);
lean_inc(v_a_1801_);
lean_dec_ref_known(v_a_1797_, 1);
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 0, v_a_1801_);
v___x_1803_ = v___x_1799_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_a_1801_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
else
{
lean_object* v_a_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; size_t v_sz_1808_; size_t v___x_1809_; lean_object* v___x_1810_; 
lean_del_object(v___x_1799_);
v_a_1805_ = lean_ctor_get(v_a_1797_, 0);
lean_inc(v_a_1805_);
lean_dec_ref_known(v_a_1797_, 1);
v___x_1806_ = lean_box(0);
v___x_1807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1806_);
lean_ctor_set(v___x_1807_, 1, v_a_1805_);
v_sz_1808_ = lean_array_size(v_tail_1795_);
v___x_1809_ = ((size_t)0ULL);
v___x_1810_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1(v_a_1786_, v_tail_1795_, v_sz_1808_, v___x_1809_, v___x_1807_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1824_; 
v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1813_ = v___x_1810_;
v_isShared_1814_ = v_isSharedCheck_1824_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1810_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1824_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v_fst_1815_; 
v_fst_1815_ = lean_ctor_get(v_a_1811_, 0);
if (lean_obj_tag(v_fst_1815_) == 0)
{
lean_object* v_snd_1816_; lean_object* v___x_1818_; 
v_snd_1816_ = lean_ctor_get(v_a_1811_, 1);
lean_inc(v_snd_1816_);
lean_dec(v_a_1811_);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 0, v_snd_1816_);
v___x_1818_ = v___x_1813_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_snd_1816_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
else
{
lean_object* v_val_1820_; lean_object* v___x_1822_; 
lean_inc_ref(v_fst_1815_);
lean_dec(v_a_1811_);
v_val_1820_ = lean_ctor_get(v_fst_1815_, 0);
lean_inc(v_val_1820_);
lean_dec_ref_known(v_fst_1815_, 1);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 0, v_val_1820_);
v___x_1822_ = v___x_1813_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_val_1820_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
}
else
{
lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1832_; 
v_a_1825_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1827_ = v___x_1810_;
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v___x_1810_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1830_; 
if (v_isShared_1828_ == 0)
{
v___x_1830_ = v___x_1827_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_a_1825_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
}
}
}
}
else
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1841_; 
v_a_1834_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1836_ = v___x_1796_;
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1796_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1839_; 
if (v_isShared_1837_ == 0)
{
v___x_1839_ = v___x_1836_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_a_1834_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1786_ = stack[0].m_obj;
lean_object* v_t_1787_ = stack[1].m_obj;
lean_object* v_init_1788_ = stack[2].m_obj;
lean_object* v___y_1789_ = stack[3].m_obj;
lean_object* v___y_1790_ = stack[4].m_obj;
lean_object* v___y_1791_ = stack[5].m_obj;
lean_object* v___y_1792_ = stack[6].m_obj;
lean_object* v_res_1842_;
v_res_1842_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0(v_a_1786_, v_t_1787_, v_init_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
stack->m_obj
 = v_res_1842_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0___boxed(lean_object* v_a_1843_, lean_object* v_t_1844_, lean_object* v_init_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_){
_start:
{
lean_object* v_res_1851_; 
v_res_1851_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0(v_a_1843_, v_t_1844_, v_init_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec_ref(v_t_1844_);
lean_dec(v_a_1843_);
return v_res_1851_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___lam__0(lean_object* v_mvarId_1854_, lean_object* v___x_1855_, lean_object* v___x_1856_, lean_object* v_toPreserve_1857_, uint8_t v_indirectProps_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
lean_object* v___x_1864_; 
lean_inc(v_mvarId_1854_);
v___x_1864_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1854_, v___x_1855_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
if (lean_obj_tag(v___x_1864_) == 0)
{
uint8_t v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
lean_dec_ref_known(v___x_1864_, 1);
v___x_1865_ = 0;
v___x_1866_ = lean_box(v___x_1865_);
v___x_1867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1866_);
lean_ctor_set(v___x_1867_, 1, v___x_1856_);
v___x_1868_ = lean_st_mk_ref(v___x_1867_);
lean_inc(v_mvarId_1854_);
v___x_1869_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_collectUsed(v_mvarId_1854_, v_toPreserve_1857_, v_indirectProps_1858_, v___x_1868_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_object* v_a_1870_; lean_object* v___x_1871_; lean_object* v_lctx_1872_; lean_object* v_localInstances_1873_; lean_object* v_decls_1874_; lean_object* v___x_1875_; 
v_a_1870_ = lean_ctor_get(v___x_1869_, 0);
lean_inc(v_a_1870_);
lean_dec_ref_known(v___x_1869_, 1);
v___x_1871_ = lean_st_ref_get(v___x_1868_);
lean_dec(v___x_1868_);
lean_dec(v___x_1871_);
v_lctx_1872_ = lean_ctor_get(v___y_1859_, 2);
v_localInstances_1873_ = lean_ctor_get(v___y_1859_, 3);
v_decls_1874_ = lean_ctor_get(v_lctx_1872_, 1);
lean_inc_ref(v_lctx_1872_);
v___x_1875_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0(v_a_1870_, v_decls_1874_, v_lctx_1872_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_object* v_a_1876_; lean_object* v___x_1877_; lean_object* v___y_1879_; lean_object* v___x_1923_; lean_object* v___x_1924_; uint8_t v___x_1925_; 
v_a_1876_ = lean_ctor_get(v___x_1875_, 0);
lean_inc(v_a_1876_);
lean_dec_ref_known(v___x_1875_, 1);
v___x_1877_ = lean_unsigned_to_nat(0u);
v___x_1923_ = lean_array_get_size(v_localInstances_1873_);
v___x_1924_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___lam__0___closed__0));
v___x_1925_ = lean_nat_dec_lt(v___x_1877_, v___x_1923_);
if (v___x_1925_ == 0)
{
lean_dec(v_a_1870_);
v___y_1879_ = v___x_1924_;
goto v___jp_1878_;
}
else
{
uint8_t v___x_1926_; 
v___x_1926_ = lean_nat_dec_le(v___x_1923_, v___x_1923_);
if (v___x_1926_ == 0)
{
if (v___x_1925_ == 0)
{
lean_dec(v_a_1870_);
v___y_1879_ = v___x_1924_;
goto v___jp_1878_;
}
else
{
size_t v___x_1927_; size_t v___x_1928_; lean_object* v___x_1929_; 
v___x_1927_ = ((size_t)0ULL);
v___x_1928_ = lean_usize_of_nat(v___x_1923_);
v___x_1929_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__3(v_a_1870_, v_localInstances_1873_, v___x_1927_, v___x_1928_, v___x_1924_);
lean_dec(v_a_1870_);
v___y_1879_ = v___x_1929_;
goto v___jp_1878_;
}
}
else
{
size_t v___x_1930_; size_t v___x_1931_; lean_object* v___x_1932_; 
v___x_1930_ = ((size_t)0ULL);
v___x_1931_ = lean_usize_of_nat(v___x_1923_);
v___x_1932_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__3(v_a_1870_, v_localInstances_1873_, v___x_1930_, v___x_1931_, v___x_1924_);
lean_dec(v_a_1870_);
v___y_1879_ = v___x_1932_;
goto v___jp_1878_;
}
}
v___jp_1878_:
{
lean_object* v___x_1880_; 
lean_inc(v_mvarId_1854_);
v___x_1880_ = l_Lean_MVarId_getType(v_mvarId_1854_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v_a_1881_; lean_object* v___x_1882_; lean_object* v_a_1883_; lean_object* v___x_1884_; 
v_a_1881_ = lean_ctor_get(v___x_1880_, 0);
lean_inc(v_a_1881_);
lean_dec_ref_known(v___x_1880_, 1);
v___x_1882_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__1___redArg(v_a_1881_, v___y_1860_);
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
lean_inc(v_a_1883_);
lean_dec_ref(v___x_1882_);
lean_inc(v_mvarId_1854_);
v___x_1884_ = l_Lean_MVarId_getTag(v_mvarId_1854_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v_a_1885_; uint8_t v___x_1886_; lean_object* v___x_1887_; 
v_a_1885_ = lean_ctor_get(v___x_1884_, 0);
lean_inc(v_a_1885_);
lean_dec_ref_known(v___x_1884_, 1);
v___x_1886_ = 2;
v___x_1887_ = l_Lean_Meta_mkFreshExprMVarAt(v_a_1876_, v___y_1879_, v_a_1883_, v___x_1886_, v_a_1885_, v___x_1877_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
lean_dec_ref(v___y_1859_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v_a_1888_; lean_object* v___x_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1897_; 
v_a_1888_ = lean_ctor_get(v___x_1887_, 0);
lean_inc_n(v_a_1888_, 2);
lean_dec_ref_known(v___x_1887_, 1);
v___x_1889_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___redArg(v_mvarId_1854_, v_a_1888_, v___y_1860_);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1897_ == 0)
{
lean_object* v_unused_1898_; 
v_unused_1898_ = lean_ctor_get(v___x_1889_, 0);
lean_dec(v_unused_1898_);
v___x_1891_ = v___x_1889_;
v_isShared_1892_ = v_isSharedCheck_1897_;
goto v_resetjp_1890_;
}
else
{
lean_dec(v___x_1889_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1897_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1893_; lean_object* v___x_1895_; 
v___x_1893_ = l_Lean_Expr_mvarId_x21(v_a_1888_);
lean_dec(v_a_1888_);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 0, v___x_1893_);
v___x_1895_ = v___x_1891_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v___x_1893_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
else
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1906_; 
lean_dec(v_mvarId_1854_);
v_a_1899_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1901_ = v___x_1887_;
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1887_);
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
lean_dec(v_a_1883_);
lean_dec_ref(v___y_1879_);
lean_dec(v_a_1876_);
lean_dec_ref(v___y_1859_);
lean_dec(v_mvarId_1854_);
v_a_1907_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1909_ = v___x_1884_;
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1884_);
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
lean_dec_ref(v___y_1879_);
lean_dec(v_a_1876_);
lean_dec_ref(v___y_1859_);
lean_dec(v_mvarId_1854_);
v_a_1915_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1917_ = v___x_1880_;
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1880_);
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
else
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1940_; 
lean_dec(v_a_1870_);
lean_dec_ref(v___y_1859_);
lean_dec(v_mvarId_1854_);
v_a_1933_ = lean_ctor_get(v___x_1875_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1935_ = v___x_1875_;
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1875_);
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
lean_dec(v___x_1868_);
lean_dec_ref(v___y_1859_);
lean_dec(v_mvarId_1854_);
v_a_1941_ = lean_ctor_get(v___x_1869_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1943_ = v___x_1869_;
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1869_);
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
else
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1956_; 
lean_dec_ref(v___y_1859_);
lean_dec(v___x_1856_);
lean_dec(v_mvarId_1854_);
v_a_1949_ = lean_ctor_get(v___x_1864_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1951_ = v___x_1864_;
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1864_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1954_; 
if (v_isShared_1952_ == 0)
{
v___x_1954_ = v___x_1951_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_a_1949_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1854_ = stack[0].m_obj;
lean_object* v___x_1855_ = stack[1].m_obj;
lean_object* v___x_1856_ = stack[2].m_obj;
lean_object* v_toPreserve_1857_ = stack[3].m_obj;
uint8_t v_indirectProps_1858_ = stack[4].m_num;
lean_object* v___y_1859_ = stack[5].m_obj;
lean_object* v___y_1860_ = stack[6].m_obj;
lean_object* v___y_1861_ = stack[7].m_obj;
lean_object* v___y_1862_ = stack[8].m_obj;
lean_object* v_res_1957_;
v_res_1957_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___lam__0(v_mvarId_1854_, v___x_1855_, v___x_1856_, v_toPreserve_1857_, v_indirectProps_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
stack->m_obj
 = v_res_1957_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___lam__0___boxed(lean_object* v_mvarId_1958_, lean_object* v___x_1959_, lean_object* v___x_1960_, lean_object* v_toPreserve_1961_, lean_object* v_indirectProps_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
uint8_t v_indirectProps_boxed_1968_; lean_object* v_res_1969_; 
v_indirectProps_boxed_1968_ = lean_unbox(v_indirectProps_1962_);
v_res_1969_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___lam__0(v_mvarId_1958_, v___x_1959_, v___x_1960_, v_toPreserve_1961_, v_indirectProps_boxed_1968_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec_ref(v_toPreserve_1961_);
return v_res_1969_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(lean_object* v_mvarId_1973_, lean_object* v_toPreserve_1974_, uint8_t v_indirectProps_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_){
_start:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___f_1984_; lean_object* v___x_1985_; 
v___x_1981_ = lean_box(1);
v___x_1982_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___closed__1));
v___x_1983_ = lean_box(v_indirectProps_1975_);
lean_inc(v_mvarId_1973_);
v___f_1984_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1984_, 0, v_mvarId_1973_);
lean_closure_set(v___f_1984_, 1, v___x_1982_);
lean_closure_set(v___f_1984_, 2, v___x_1981_);
lean_closure_set(v___f_1984_, 3, v_toPreserve_1974_);
lean_closure_set(v___f_1984_, 4, v___x_1983_);
v___x_1985_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__4___redArg(v_mvarId_1973_, v___f_1984_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_);
return v___x_1985_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1973_ = stack[0].m_obj;
lean_object* v_toPreserve_1974_ = stack[1].m_obj;
uint8_t v_indirectProps_1975_ = stack[2].m_num;
lean_object* v_a_1976_ = stack[3].m_obj;
lean_object* v_a_1977_ = stack[4].m_obj;
lean_object* v_a_1978_ = stack[5].m_obj;
lean_object* v_a_1979_ = stack[6].m_obj;
lean_object* v_res_1986_;
v_res_1986_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(v_mvarId_1973_, v_toPreserve_1974_, v_indirectProps_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_);
stack->m_obj
 = v_res_1986_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore___boxed(lean_object* v_mvarId_1987_, lean_object* v_toPreserve_1988_, lean_object* v_indirectProps_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_){
_start:
{
uint8_t v_indirectProps_boxed_1995_; lean_object* v_res_1996_; 
v_indirectProps_boxed_1995_ = lean_unbox(v_indirectProps_1989_);
v_res_1996_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(v_mvarId_1987_, v_toPreserve_1988_, v_indirectProps_boxed_1995_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_);
lean_dec(v_a_1993_);
lean_dec_ref(v_a_1992_);
lean_dec(v_a_1991_);
lean_dec_ref(v_a_1990_);
return v_res_1996_;
}
}
lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2(lean_object* v_mvarId_1997_, lean_object* v_val_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
lean_object* v___x_2004_; 
v___x_2004_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___redArg(v_mvarId_1997_, v_val_1998_, v___y_2000_);
return v___x_2004_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1997_ = stack[0].m_obj;
lean_object* v_val_1998_ = stack[1].m_obj;
lean_object* v___y_1999_ = stack[2].m_obj;
lean_object* v___y_2000_ = stack[3].m_obj;
lean_object* v___y_2001_ = stack[4].m_obj;
lean_object* v___y_2002_ = stack[5].m_obj;
lean_object* v_res_2005_;
v_res_2005_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2(v_mvarId_1997_, v_val_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
stack->m_obj
 = v_res_2005_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2___boxed(lean_object* v_mvarId_2006_, lean_object* v_val_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_){
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2(v_mvarId_2006_, v_val_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2008_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4(lean_object* v_00_u03b2_2014_, lean_object* v_x_2015_, lean_object* v_x_2016_, lean_object* v_x_2017_){
_start:
{
lean_object* v___x_2018_; 
v___x_2018_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4___redArg(v_x_2015_, v_x_2016_, v_x_2017_);
return v___x_2018_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6(lean_object* v_a_2019_, lean_object* v_as_2020_, size_t v_sz_2021_, size_t v_i_2022_, lean_object* v_b_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_){
_start:
{
lean_object* v___x_2029_; 
v___x_2029_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___redArg(v_a_2019_, v_as_2020_, v_sz_2021_, v_i_2022_, v_b_2023_);
return v___x_2029_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2019_ = stack[0].m_obj;
lean_object* v_as_2020_ = stack[1].m_obj;
size_t v_sz_2021_ = stack[2].m_num;
size_t v_i_2022_ = stack[3].m_num;
lean_object* v_b_2023_ = stack[4].m_obj;
lean_object* v___y_2024_ = stack[5].m_obj;
lean_object* v___y_2025_ = stack[6].m_obj;
lean_object* v___y_2026_ = stack[7].m_obj;
lean_object* v___y_2027_ = stack[8].m_obj;
lean_object* v_res_2030_;
v_res_2030_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6(v_a_2019_, v_as_2020_, v_sz_2021_, v_i_2022_, v_b_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
stack->m_obj
 = v_res_2030_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6___boxed(lean_object* v_a_2031_, lean_object* v_as_2032_, lean_object* v_sz_2033_, lean_object* v_i_2034_, lean_object* v_b_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_){
_start:
{
size_t v_sz_boxed_2041_; size_t v_i_boxed_2042_; lean_object* v_res_2043_; 
v_sz_boxed_2041_ = lean_unbox_usize(v_sz_2033_);
lean_dec(v_sz_2033_);
v_i_boxed_2042_ = lean_unbox_usize(v_i_2034_);
lean_dec(v_i_2034_);
v_res_2043_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__1_spec__6(v_a_2031_, v_as_2032_, v_sz_boxed_2041_, v_i_boxed_2042_, v_b_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
lean_dec_ref(v_as_2032_);
lean_dec(v_a_2031_);
return v_res_2043_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9(lean_object* v_00_u03b2_2044_, lean_object* v_x_2045_, size_t v_x_2046_, size_t v_x_2047_, lean_object* v_x_2048_, lean_object* v_x_2049_){
_start:
{
lean_object* v___x_2050_; 
v___x_2050_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___redArg(v_x_2045_, v_x_2046_, v_x_2047_, v_x_2048_, v_x_2049_);
return v___x_2050_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2045_ = stack[1].m_obj;
size_t v_x_2046_ = stack[2].m_num;
size_t v_x_2047_ = stack[3].m_num;
lean_object* v_x_2048_ = stack[4].m_obj;
lean_object* v_x_2049_ = stack[5].m_obj;
lean_object* v_res_2051_;
v_res_2051_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9(lean_box(0), v_x_2045_, v_x_2046_, v_x_2047_, v_x_2048_, v_x_2049_);
stack->m_obj
 = v_res_2051_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9___boxed(lean_object* v_00_u03b2_2052_, lean_object* v_x_2053_, lean_object* v_x_2054_, lean_object* v_x_2055_, lean_object* v_x_2056_, lean_object* v_x_2057_){
_start:
{
size_t v_x_9079__boxed_2058_; size_t v_x_9080__boxed_2059_; lean_object* v_res_2060_; 
v_x_9079__boxed_2058_ = lean_unbox_usize(v_x_2054_);
lean_dec(v_x_2054_);
v_x_9080__boxed_2059_ = lean_unbox_usize(v_x_2055_);
lean_dec(v_x_2055_);
v_res_2060_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9(v_00_u03b2_2052_, v_x_2053_, v_x_9079__boxed_2058_, v_x_9080__boxed_2059_, v_x_2056_, v_x_2057_);
return v_res_2060_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7(lean_object* v_a_2061_, lean_object* v_as_2062_, size_t v_sz_2063_, size_t v_i_2064_, lean_object* v_b_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_){
_start:
{
lean_object* v___x_2071_; 
v___x_2071_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___redArg(v_a_2061_, v_as_2062_, v_sz_2063_, v_i_2064_, v_b_2065_);
return v___x_2071_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2061_ = stack[0].m_obj;
lean_object* v_as_2062_ = stack[1].m_obj;
size_t v_sz_2063_ = stack[2].m_num;
size_t v_i_2064_ = stack[3].m_num;
lean_object* v_b_2065_ = stack[4].m_obj;
lean_object* v___y_2066_ = stack[5].m_obj;
lean_object* v___y_2067_ = stack[6].m_obj;
lean_object* v___y_2068_ = stack[7].m_obj;
lean_object* v___y_2069_ = stack[8].m_obj;
lean_object* v_res_2072_;
v_res_2072_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7(v_a_2061_, v_as_2062_, v_sz_2063_, v_i_2064_, v_b_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
stack->m_obj
 = v_res_2072_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7___boxed(lean_object* v_a_2073_, lean_object* v_as_2074_, lean_object* v_sz_2075_, lean_object* v_i_2076_, lean_object* v_b_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
size_t v_sz_boxed_2083_; size_t v_i_boxed_2084_; lean_object* v_res_2085_; 
v_sz_boxed_2083_ = lean_unbox_usize(v_sz_2075_);
lean_dec(v_sz_2075_);
v_i_boxed_2084_ = lean_unbox_usize(v_i_2076_);
lean_dec(v_i_2076_);
v_res_2085_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__0_spec__0_spec__4_spec__7(v_a_2073_, v_as_2074_, v_sz_boxed_2083_, v_i_boxed_2084_, v_b_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
lean_dec(v___y_2079_);
lean_dec_ref(v___y_2078_);
lean_dec_ref(v_as_2074_);
lean_dec(v_a_2073_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12(lean_object* v_00_u03b2_2086_, lean_object* v_n_2087_, lean_object* v_k_2088_, lean_object* v_v_2089_){
_start:
{
lean_object* v___x_2090_; 
v___x_2090_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12___redArg(v_n_2087_, v_k_2088_, v_v_2089_);
return v___x_2090_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13(lean_object* v_00_u03b2_2091_, size_t v_depth_2092_, lean_object* v_keys_2093_, lean_object* v_vals_2094_, lean_object* v_heq_2095_, lean_object* v_i_2096_, lean_object* v_entries_2097_){
_start:
{
lean_object* v___x_2098_; 
v___x_2098_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___redArg(v_depth_2092_, v_keys_2093_, v_vals_2094_, v_i_2096_, v_entries_2097_);
return v___x_2098_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13_0interp(lean_interpreter_value* stack)
{
size_t v_depth_2092_ = stack[1].m_num;
lean_object* v_keys_2093_ = stack[2].m_obj;
lean_object* v_vals_2094_ = stack[3].m_obj;
lean_object* v_i_2096_ = stack[5].m_obj;
lean_object* v_entries_2097_ = stack[6].m_obj;
lean_object* v_res_2099_;
v_res_2099_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13(lean_box(0), v_depth_2092_, v_keys_2093_, v_vals_2094_, lean_box(0), v_i_2096_, v_entries_2097_);
stack->m_obj
 = v_res_2099_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13___boxed(lean_object* v_00_u03b2_2100_, lean_object* v_depth_2101_, lean_object* v_keys_2102_, lean_object* v_vals_2103_, lean_object* v_heq_2104_, lean_object* v_i_2105_, lean_object* v_entries_2106_){
_start:
{
size_t v_depth_boxed_2107_; lean_object* v_res_2108_; 
v_depth_boxed_2107_ = lean_unbox_usize(v_depth_2101_);
lean_dec(v_depth_2101_);
v_res_2108_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__13(v_00_u03b2_2100_, v_depth_boxed_2107_, v_keys_2102_, v_vals_2103_, v_heq_2104_, v_i_2105_, v_entries_2106_);
lean_dec_ref(v_vals_2103_);
lean_dec_ref(v_keys_2102_);
return v_res_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12_spec__13(lean_object* v_00_u03b2_2109_, lean_object* v_x_2110_, lean_object* v_x_2111_, lean_object* v_x_2112_, lean_object* v_x_2113_){
_start:
{
lean_object* v___x_2114_; 
v___x_2114_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore_spec__2_spec__4_spec__9_spec__12_spec__13___redArg(v_x_2110_, v_x_2111_, v_x_2112_, v_x_2113_);
return v___x_2114_;
}
}
lean_object* l_Lean_MVarId_cleanup(lean_object* v_mvarId_2115_, lean_object* v_toPreserve_2116_, uint8_t v_indirectProps_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_){
_start:
{
lean_object* v___x_2123_; 
v___x_2123_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(v_mvarId_2115_, v_toPreserve_2116_, v_indirectProps_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_);
return v___x_2123_;
}
}
LEAN_EXPORT void l_Lean_MVarId_cleanup_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2115_ = stack[0].m_obj;
lean_object* v_toPreserve_2116_ = stack[1].m_obj;
uint8_t v_indirectProps_2117_ = stack[2].m_num;
lean_object* v_a_2118_ = stack[3].m_obj;
lean_object* v_a_2119_ = stack[4].m_obj;
lean_object* v_a_2120_ = stack[5].m_obj;
lean_object* v_a_2121_ = stack[6].m_obj;
lean_object* v_res_2124_;
v_res_2124_ = l_Lean_MVarId_cleanup(v_mvarId_2115_, v_toPreserve_2116_, v_indirectProps_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_);
stack->m_obj
 = v_res_2124_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_cleanup___boxed(lean_object* v_mvarId_2125_, lean_object* v_toPreserve_2126_, lean_object* v_indirectProps_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_){
_start:
{
uint8_t v_indirectProps_boxed_2133_; lean_object* v_res_2134_; 
v_indirectProps_boxed_2133_ = lean_unbox(v_indirectProps_2127_);
v_res_2134_ = l_Lean_MVarId_cleanup(v_mvarId_2125_, v_toPreserve_2126_, v_indirectProps_boxed_2133_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_);
lean_dec(v_a_2131_);
lean_dec_ref(v_a_2130_);
lean_dec(v_a_2129_);
lean_dec_ref(v_a_2128_);
return v_res_2134_;
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
