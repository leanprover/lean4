// Lean compiler output
// Module: Lean.Meta.Tactic.Clear
// Imports: public import Lean.Meta.Tactic.Util import Init.Data.Nat.Order import Init.Data.Order.Lemmas
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
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_erase(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalContext_contains(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_LocalContext_sortFVarsByContextOrder(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT uint8_t l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__1___boxed(lean_object*);
static const lean_closure_object l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__0_value;
static lean_once_cell_t l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2;
static lean_once_cell_t l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_MVarId_clear___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_clear___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "clear"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 138, 223, 238, 58, 192, 25, 14)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "variable '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "' depends on '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_clear___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "target depends on '"};
static const lean_object* l_Lean_MVarId_clear___lam__1___closed__0 = (const lean_object*)&l_Lean_MVarId_clear___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_MVarId_clear___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_clear___lam__1___closed__1;
static const lean_string_object l_Lean_MVarId_clear___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "unknown variable '"};
static const lean_object* l_Lean_MVarId_clear___lam__1___closed__2 = (const lean_object*)&l_Lean_MVarId_clear___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_MVarId_clear___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_clear___lam__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_MVarId_clear___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_clear___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_clear___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClear___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany_x27___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany_x27___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__0(lean_object* v_fvarId_1_, lean_object* v_x_2_){
_start:
{
uint8_t v___x_3_; 
v___x_3_ = l_Lean_instBEqFVarId_beq(v_fvarId_1_, v_x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__0___boxed(lean_object* v_fvarId_4_, lean_object* v_x_5_){
_start:
{
uint8_t v_res_6_; lean_object* v_r_7_; 
v_res_6_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__0(v_fvarId_4_, v_x_5_);
lean_dec(v_x_5_);
lean_dec(v_fvarId_4_);
v_r_7_ = lean_box(v_res_6_);
return v_r_7_;
}
}
LEAN_EXPORT uint8_t l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__1(lean_object* v_x_8_){
_start:
{
uint8_t v___x_9_; 
v___x_9_ = 0;
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__1___boxed(lean_object* v_x_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__1(v_x_10_);
lean_dec(v_x_10_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
static lean_object* _init_l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v_cellCount_14_; lean_object* v___x_15_; 
v_cellCount_14_ = lean_unsigned_to_nat(16u);
v___x_15_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_14_);
return v___x_15_;
}
}
static lean_object* _init_l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v_cellCount_16_; lean_object* v___x_17_; 
v_cellCount_16_ = lean_unsigned_to_nat(16u);
v___x_17_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_16_);
return v___x_17_;
}
}
static lean_object* _init_l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_18_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2);
v___x_19_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__1, &l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__1_once, _init_l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__1);
v___x_20_ = lean_unsigned_to_nat(0u);
v___x_21_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_21_, 0, v___x_20_);
lean_ctor_set(v___x_21_, 1, v___x_19_);
lean_ctor_set(v___x_21_, 2, v___x_18_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg(lean_object* v_localDecl_22_, lean_object* v_fvarId_23_, uint8_t v_generalizeNondepLet_24_, lean_object* v___y_25_){
_start:
{
uint8_t v_fst_28_; lean_object* v_snd_29_; lean_object* v___y_48_; lean_object* v___f_52_; lean_object* v___f_53_; 
v___f_52_ = lean_alloc_closure((void*)(l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_52_, 0, v_fvarId_23_);
v___f_53_ = ((lean_object*)(l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__0));
if (lean_obj_tag(v_localDecl_22_) == 0)
{
lean_object* v_type_54_; lean_object* v___x_55_; uint8_t v_fst_57_; lean_object* v_mctx_58_; lean_object* v___y_76_; lean_object* v_mctx_81_; lean_object* v___x_82_; lean_object* v___x_83_; uint8_t v___x_84_; 
v_type_54_ = lean_ctor_get(v_localDecl_22_, 3);
lean_inc_ref(v_type_54_);
lean_dec_ref_known(v_localDecl_22_, 4);
v___x_55_ = lean_st_ref_get(v___y_25_);
v_mctx_81_ = lean_ctor_get(v___x_55_, 0);
lean_inc_ref_n(v_mctx_81_, 2);
lean_dec(v___x_55_);
v___x_82_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__3, &l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__3_once, _init_l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__3);
v___x_83_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
lean_ctor_set(v___x_83_, 1, v_mctx_81_);
v___x_84_ = l_Lean_Expr_hasFVar(v_type_54_);
if (v___x_84_ == 0)
{
uint8_t v___x_85_; 
v___x_85_ = l_Lean_Expr_hasMVar(v_type_54_);
if (v___x_85_ == 0)
{
lean_dec_ref_known(v___x_83_, 2);
lean_dec_ref(v_type_54_);
lean_dec_ref(v___f_52_);
v_fst_57_ = v___x_85_;
v_mctx_58_ = v_mctx_81_;
goto v___jp_56_;
}
else
{
lean_object* v___x_86_; 
lean_dec_ref(v_mctx_81_);
v___x_86_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_52_, v___f_53_, v_type_54_, v___x_83_);
v___y_76_ = v___x_86_;
goto v___jp_75_;
}
}
else
{
lean_object* v___x_87_; 
lean_dec_ref(v_mctx_81_);
v___x_87_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_52_, v___f_53_, v_type_54_, v___x_83_);
v___y_76_ = v___x_87_;
goto v___jp_75_;
}
v___jp_56_:
{
lean_object* v___x_59_; lean_object* v_cache_60_; lean_object* v_zetaDeltaFVarIds_61_; lean_object* v_postponed_62_; lean_object* v_diag_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_73_; 
v___x_59_ = lean_st_ref_take(v___y_25_);
v_cache_60_ = lean_ctor_get(v___x_59_, 1);
v_zetaDeltaFVarIds_61_ = lean_ctor_get(v___x_59_, 2);
v_postponed_62_ = lean_ctor_get(v___x_59_, 3);
v_diag_63_ = lean_ctor_get(v___x_59_, 4);
v_isSharedCheck_73_ = !lean_is_exclusive(v___x_59_);
if (v_isSharedCheck_73_ == 0)
{
lean_object* v_unused_74_; 
v_unused_74_ = lean_ctor_get(v___x_59_, 0);
lean_dec(v_unused_74_);
v___x_65_ = v___x_59_;
v_isShared_66_ = v_isSharedCheck_73_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_diag_63_);
lean_inc(v_postponed_62_);
lean_inc(v_zetaDeltaFVarIds_61_);
lean_inc(v_cache_60_);
lean_dec(v___x_59_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_73_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___x_68_; 
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 0, v_mctx_58_);
v___x_68_ = v___x_65_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v_mctx_58_);
lean_ctor_set(v_reuseFailAlloc_72_, 1, v_cache_60_);
lean_ctor_set(v_reuseFailAlloc_72_, 2, v_zetaDeltaFVarIds_61_);
lean_ctor_set(v_reuseFailAlloc_72_, 3, v_postponed_62_);
lean_ctor_set(v_reuseFailAlloc_72_, 4, v_diag_63_);
v___x_68_ = v_reuseFailAlloc_72_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_69_ = lean_st_ref_put(v___y_25_, v___x_68_);
v___x_70_ = lean_box(v_fst_57_);
v___x_71_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
return v___x_71_;
}
}
}
v___jp_75_:
{
lean_object* v_snd_77_; lean_object* v_fst_78_; lean_object* v_mctx_79_; uint8_t v___x_80_; 
v_snd_77_ = lean_ctor_get(v___y_76_, 1);
lean_inc(v_snd_77_);
v_fst_78_ = lean_ctor_get(v___y_76_, 0);
lean_inc(v_fst_78_);
lean_dec_ref(v___y_76_);
v_mctx_79_ = lean_ctor_get(v_snd_77_, 1);
lean_inc_ref(v_mctx_79_);
lean_dec(v_snd_77_);
v___x_80_ = lean_unbox(v_fst_78_);
lean_dec(v_fst_78_);
v_fst_57_ = v___x_80_;
v_mctx_58_ = v_mctx_79_;
goto v___jp_56_;
}
}
else
{
lean_object* v_type_88_; lean_object* v_value_89_; uint8_t v_nondep_90_; uint8_t v_fst_92_; lean_object* v_snd_93_; lean_object* v___y_99_; 
v_type_88_ = lean_ctor_get(v_localDecl_22_, 3);
lean_inc_ref(v_type_88_);
v_value_89_ = lean_ctor_get(v_localDecl_22_, 4);
lean_inc_ref(v_value_89_);
v_nondep_90_ = lean_ctor_get_uint8(v_localDecl_22_, sizeof(void*)*5);
lean_dec_ref_known(v_localDecl_22_, 5);
if (v_generalizeNondepLet_24_ == 0)
{
goto v___jp_103_;
}
else
{
if (v_nondep_90_ == 0)
{
goto v___jp_103_;
}
else
{
lean_object* v___x_112_; uint8_t v_fst_114_; lean_object* v_mctx_115_; lean_object* v___y_133_; lean_object* v_mctx_138_; lean_object* v___x_139_; lean_object* v___x_140_; uint8_t v___x_141_; 
lean_dec_ref(v_value_89_);
v___x_112_ = lean_st_ref_get(v___y_25_);
v_mctx_138_ = lean_ctor_get(v___x_112_, 0);
lean_inc_ref_n(v_mctx_138_, 2);
lean_dec(v___x_112_);
v___x_139_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__3, &l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__3_once, _init_l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__3);
v___x_140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
lean_ctor_set(v___x_140_, 1, v_mctx_138_);
v___x_141_ = l_Lean_Expr_hasFVar(v_type_88_);
if (v___x_141_ == 0)
{
uint8_t v___x_142_; 
v___x_142_ = l_Lean_Expr_hasMVar(v_type_88_);
if (v___x_142_ == 0)
{
lean_dec_ref_known(v___x_140_, 2);
lean_dec_ref(v_type_88_);
lean_dec_ref(v___f_52_);
v_fst_114_ = v___x_142_;
v_mctx_115_ = v_mctx_138_;
goto v___jp_113_;
}
else
{
lean_object* v___x_143_; 
lean_dec_ref(v_mctx_138_);
v___x_143_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_52_, v___f_53_, v_type_88_, v___x_140_);
v___y_133_ = v___x_143_;
goto v___jp_132_;
}
}
else
{
lean_object* v___x_144_; 
lean_dec_ref(v_mctx_138_);
v___x_144_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_52_, v___f_53_, v_type_88_, v___x_140_);
v___y_133_ = v___x_144_;
goto v___jp_132_;
}
v___jp_113_:
{
lean_object* v___x_116_; lean_object* v_cache_117_; lean_object* v_zetaDeltaFVarIds_118_; lean_object* v_postponed_119_; lean_object* v_diag_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_130_; 
v___x_116_ = lean_st_ref_take(v___y_25_);
v_cache_117_ = lean_ctor_get(v___x_116_, 1);
v_zetaDeltaFVarIds_118_ = lean_ctor_get(v___x_116_, 2);
v_postponed_119_ = lean_ctor_get(v___x_116_, 3);
v_diag_120_ = lean_ctor_get(v___x_116_, 4);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_130_ == 0)
{
lean_object* v_unused_131_; 
v_unused_131_ = lean_ctor_get(v___x_116_, 0);
lean_dec(v_unused_131_);
v___x_122_ = v___x_116_;
v_isShared_123_ = v_isSharedCheck_130_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_diag_120_);
lean_inc(v_postponed_119_);
lean_inc(v_zetaDeltaFVarIds_118_);
lean_inc(v_cache_117_);
lean_dec(v___x_116_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_130_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_125_; 
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 0, v_mctx_115_);
v___x_125_ = v___x_122_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_mctx_115_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v_cache_117_);
lean_ctor_set(v_reuseFailAlloc_129_, 2, v_zetaDeltaFVarIds_118_);
lean_ctor_set(v_reuseFailAlloc_129_, 3, v_postponed_119_);
lean_ctor_set(v_reuseFailAlloc_129_, 4, v_diag_120_);
v___x_125_ = v_reuseFailAlloc_129_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_126_ = lean_st_ref_put(v___y_25_, v___x_125_);
v___x_127_ = lean_box(v_fst_114_);
v___x_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
return v___x_128_;
}
}
}
v___jp_132_:
{
lean_object* v_snd_134_; lean_object* v_fst_135_; lean_object* v_mctx_136_; uint8_t v___x_137_; 
v_snd_134_ = lean_ctor_get(v___y_133_, 1);
lean_inc(v_snd_134_);
v_fst_135_ = lean_ctor_get(v___y_133_, 0);
lean_inc(v_fst_135_);
lean_dec_ref(v___y_133_);
v_mctx_136_ = lean_ctor_get(v_snd_134_, 1);
lean_inc_ref(v_mctx_136_);
lean_dec(v_snd_134_);
v___x_137_ = lean_unbox(v_fst_135_);
lean_dec(v_fst_135_);
v_fst_114_ = v___x_137_;
v_mctx_115_ = v_mctx_136_;
goto v___jp_113_;
}
}
}
v___jp_91_:
{
if (v_fst_92_ == 0)
{
uint8_t v___x_94_; 
v___x_94_ = l_Lean_Expr_hasFVar(v_value_89_);
if (v___x_94_ == 0)
{
uint8_t v___x_95_; 
v___x_95_ = l_Lean_Expr_hasMVar(v_value_89_);
if (v___x_95_ == 0)
{
lean_dec_ref(v_value_89_);
lean_dec_ref(v___f_52_);
v_fst_28_ = v___x_95_;
v_snd_29_ = v_snd_93_;
goto v___jp_27_;
}
else
{
lean_object* v___x_96_; 
v___x_96_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_52_, v___f_53_, v_value_89_, v_snd_93_);
v___y_48_ = v___x_96_;
goto v___jp_47_;
}
}
else
{
lean_object* v___x_97_; 
v___x_97_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_52_, v___f_53_, v_value_89_, v_snd_93_);
v___y_48_ = v___x_97_;
goto v___jp_47_;
}
}
else
{
lean_dec_ref(v_value_89_);
lean_dec_ref(v___f_52_);
v_fst_28_ = v_fst_92_;
v_snd_29_ = v_snd_93_;
goto v___jp_27_;
}
}
v___jp_98_:
{
lean_object* v_fst_100_; lean_object* v_snd_101_; uint8_t v___x_102_; 
v_fst_100_ = lean_ctor_get(v___y_99_, 0);
lean_inc(v_fst_100_);
v_snd_101_ = lean_ctor_get(v___y_99_, 1);
lean_inc(v_snd_101_);
lean_dec_ref(v___y_99_);
v___x_102_ = lean_unbox(v_fst_100_);
lean_dec(v_fst_100_);
v_fst_92_ = v___x_102_;
v_snd_93_ = v_snd_101_;
goto v___jp_91_;
}
v___jp_103_:
{
lean_object* v___x_104_; lean_object* v_mctx_105_; lean_object* v___x_106_; lean_object* v___x_107_; uint8_t v___x_108_; 
v___x_104_ = lean_st_ref_get(v___y_25_);
v_mctx_105_ = lean_ctor_get(v___x_104_, 0);
lean_inc_ref(v_mctx_105_);
lean_dec(v___x_104_);
v___x_106_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__3, &l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__3_once, _init_l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__3);
v___x_107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
lean_ctor_set(v___x_107_, 1, v_mctx_105_);
v___x_108_ = l_Lean_Expr_hasFVar(v_type_88_);
if (v___x_108_ == 0)
{
uint8_t v___x_109_; 
v___x_109_ = l_Lean_Expr_hasMVar(v_type_88_);
if (v___x_109_ == 0)
{
lean_dec_ref(v_type_88_);
v_fst_92_ = v___x_109_;
v_snd_93_ = v___x_107_;
goto v___jp_91_;
}
else
{
lean_object* v___x_110_; 
lean_inc_ref(v___f_52_);
v___x_110_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_52_, v___f_53_, v_type_88_, v___x_107_);
v___y_99_ = v___x_110_;
goto v___jp_98_;
}
}
else
{
lean_object* v___x_111_; 
lean_inc_ref(v___f_52_);
v___x_111_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_52_, v___f_53_, v_type_88_, v___x_107_);
v___y_99_ = v___x_111_;
goto v___jp_98_;
}
}
}
v___jp_27_:
{
lean_object* v_mctx_30_; lean_object* v___x_31_; lean_object* v_cache_32_; lean_object* v_zetaDeltaFVarIds_33_; lean_object* v_postponed_34_; lean_object* v_diag_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_45_; 
v_mctx_30_ = lean_ctor_get(v_snd_29_, 1);
lean_inc_ref(v_mctx_30_);
lean_dec_ref(v_snd_29_);
v___x_31_ = lean_st_ref_take(v___y_25_);
v_cache_32_ = lean_ctor_get(v___x_31_, 1);
v_zetaDeltaFVarIds_33_ = lean_ctor_get(v___x_31_, 2);
v_postponed_34_ = lean_ctor_get(v___x_31_, 3);
v_diag_35_ = lean_ctor_get(v___x_31_, 4);
v_isSharedCheck_45_ = !lean_is_exclusive(v___x_31_);
if (v_isSharedCheck_45_ == 0)
{
lean_object* v_unused_46_; 
v_unused_46_ = lean_ctor_get(v___x_31_, 0);
lean_dec(v_unused_46_);
v___x_37_ = v___x_31_;
v_isShared_38_ = v_isSharedCheck_45_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_diag_35_);
lean_inc(v_postponed_34_);
lean_inc(v_zetaDeltaFVarIds_33_);
lean_inc(v_cache_32_);
lean_dec(v___x_31_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_45_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v___x_40_; 
if (v_isShared_38_ == 0)
{
lean_ctor_set(v___x_37_, 0, v_mctx_30_);
v___x_40_ = v___x_37_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_mctx_30_);
lean_ctor_set(v_reuseFailAlloc_44_, 1, v_cache_32_);
lean_ctor_set(v_reuseFailAlloc_44_, 2, v_zetaDeltaFVarIds_33_);
lean_ctor_set(v_reuseFailAlloc_44_, 3, v_postponed_34_);
lean_ctor_set(v_reuseFailAlloc_44_, 4, v_diag_35_);
v___x_40_ = v_reuseFailAlloc_44_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_41_ = lean_st_ref_put(v___y_25_, v___x_40_);
v___x_42_ = lean_box(v_fst_28_);
v___x_43_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_43_, 0, v___x_42_);
return v___x_43_;
}
}
}
v___jp_47_:
{
lean_object* v_fst_49_; lean_object* v_snd_50_; uint8_t v___x_51_; 
v_fst_49_ = lean_ctor_get(v___y_48_, 0);
lean_inc(v_fst_49_);
v_snd_50_ = lean_ctor_get(v___y_48_, 1);
lean_inc(v_snd_50_);
lean_dec_ref(v___y_48_);
v___x_51_ = lean_unbox(v_fst_49_);
lean_dec(v_fst_49_);
v_fst_28_ = v___x_51_;
v_snd_29_ = v_snd_50_;
goto v___jp_27_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___boxed(lean_object* v_localDecl_145_, lean_object* v_fvarId_146_, lean_object* v_generalizeNondepLet_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
uint8_t v_generalizeNondepLet_boxed_150_; lean_object* v_res_151_; 
v_generalizeNondepLet_boxed_150_ = lean_unbox(v_generalizeNondepLet_147_);
v_res_151_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg(v_localDecl_145_, v_fvarId_146_, v_generalizeNondepLet_boxed_150_, v___y_148_);
lean_dec(v___y_148_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0(lean_object* v_localDecl_152_, lean_object* v_fvarId_153_, uint8_t v_generalizeNondepLet_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg(v_localDecl_152_, v_fvarId_153_, v_generalizeNondepLet_154_, v___y_156_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___boxed(lean_object* v_localDecl_161_, lean_object* v_fvarId_162_, lean_object* v_generalizeNondepLet_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
uint8_t v_generalizeNondepLet_boxed_169_; lean_object* v_res_170_; 
v_generalizeNondepLet_boxed_169_ = lean_unbox(v_generalizeNondepLet_163_);
v_res_170_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0(v_localDecl_161_, v_fvarId_162_, v_generalizeNondepLet_boxed_169_, v___y_164_, v___y_165_, v___y_166_, v___y_167_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3___redArg(lean_object* v_e_171_, lean_object* v_fvarId_172_, lean_object* v___y_173_){
_start:
{
lean_object* v___x_175_; uint8_t v_fst_177_; lean_object* v_mctx_178_; lean_object* v___y_196_; lean_object* v_mctx_201_; lean_object* v___f_202_; lean_object* v___f_203_; lean_object* v___x_204_; lean_object* v___x_205_; uint8_t v___x_206_; 
v___x_175_ = lean_st_ref_get(v___y_173_);
v_mctx_201_ = lean_ctor_get(v___x_175_, 0);
lean_inc_ref_n(v_mctx_201_, 2);
lean_dec(v___x_175_);
v___f_202_ = ((lean_object*)(l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__0));
v___f_203_ = lean_alloc_closure((void*)(l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_203_, 0, v_fvarId_172_);
v___x_204_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__3, &l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__3_once, _init_l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__3);
v___x_205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
lean_ctor_set(v___x_205_, 1, v_mctx_201_);
v___x_206_ = l_Lean_Expr_hasFVar(v_e_171_);
if (v___x_206_ == 0)
{
uint8_t v___x_207_; 
v___x_207_ = l_Lean_Expr_hasMVar(v_e_171_);
if (v___x_207_ == 0)
{
lean_dec_ref_known(v___x_205_, 2);
lean_dec_ref(v___f_203_);
lean_dec_ref(v_e_171_);
v_fst_177_ = v___x_207_;
v_mctx_178_ = v_mctx_201_;
goto v___jp_176_;
}
else
{
lean_object* v___x_208_; 
lean_dec_ref(v_mctx_201_);
v___x_208_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_203_, v___f_202_, v_e_171_, v___x_205_);
v___y_196_ = v___x_208_;
goto v___jp_195_;
}
}
else
{
lean_object* v___x_209_; 
lean_dec_ref(v_mctx_201_);
v___x_209_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_203_, v___f_202_, v_e_171_, v___x_205_);
v___y_196_ = v___x_209_;
goto v___jp_195_;
}
v___jp_176_:
{
lean_object* v___x_179_; lean_object* v_cache_180_; lean_object* v_zetaDeltaFVarIds_181_; lean_object* v_postponed_182_; lean_object* v_diag_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_193_; 
v___x_179_ = lean_st_ref_take(v___y_173_);
v_cache_180_ = lean_ctor_get(v___x_179_, 1);
v_zetaDeltaFVarIds_181_ = lean_ctor_get(v___x_179_, 2);
v_postponed_182_ = lean_ctor_get(v___x_179_, 3);
v_diag_183_ = lean_ctor_get(v___x_179_, 4);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_193_ == 0)
{
lean_object* v_unused_194_; 
v_unused_194_ = lean_ctor_get(v___x_179_, 0);
lean_dec(v_unused_194_);
v___x_185_ = v___x_179_;
v_isShared_186_ = v_isSharedCheck_193_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_diag_183_);
lean_inc(v_postponed_182_);
lean_inc(v_zetaDeltaFVarIds_181_);
lean_inc(v_cache_180_);
lean_dec(v___x_179_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_193_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_188_; 
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 0, v_mctx_178_);
v___x_188_ = v___x_185_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_mctx_178_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v_cache_180_);
lean_ctor_set(v_reuseFailAlloc_192_, 2, v_zetaDeltaFVarIds_181_);
lean_ctor_set(v_reuseFailAlloc_192_, 3, v_postponed_182_);
lean_ctor_set(v_reuseFailAlloc_192_, 4, v_diag_183_);
v___x_188_ = v_reuseFailAlloc_192_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_189_ = lean_st_ref_put(v___y_173_, v___x_188_);
v___x_190_ = lean_box(v_fst_177_);
v___x_191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
return v___x_191_;
}
}
}
v___jp_195_:
{
lean_object* v_snd_197_; lean_object* v_fst_198_; lean_object* v_mctx_199_; uint8_t v___x_200_; 
v_snd_197_ = lean_ctor_get(v___y_196_, 1);
lean_inc(v_snd_197_);
v_fst_198_ = lean_ctor_get(v___y_196_, 0);
lean_inc(v_fst_198_);
lean_dec_ref(v___y_196_);
v_mctx_199_ = lean_ctor_get(v_snd_197_, 1);
lean_inc_ref(v_mctx_199_);
lean_dec(v_snd_197_);
v___x_200_ = lean_unbox(v_fst_198_);
lean_dec(v_fst_198_);
v_fst_177_ = v___x_200_;
v_mctx_178_ = v_mctx_199_;
goto v___jp_176_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3___redArg___boxed(lean_object* v_e_210_, lean_object* v_fvarId_211_, lean_object* v___y_212_, lean_object* v___y_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3___redArg(v_e_210_, v_fvarId_211_, v___y_212_);
lean_dec(v___y_212_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3(lean_object* v_e_215_, lean_object* v_fvarId_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3___redArg(v_e_215_, v_fvarId_216_, v___y_218_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3___boxed(lean_object* v_e_223_, lean_object* v_fvarId_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3(v_e_223_, v_fvarId_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_);
lean_dec(v___y_228_);
lean_dec_ref(v___y_227_);
lean_dec(v___y_226_);
lean_dec_ref(v___y_225_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg(lean_object* v_mvarId_231_, lean_object* v_x_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_231_, v_x_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_);
if (lean_obj_tag(v___x_238_) == 0)
{
lean_object* v_a_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_246_; 
v_a_239_ = lean_ctor_get(v___x_238_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_246_ == 0)
{
v___x_241_ = v___x_238_;
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_a_239_);
lean_dec(v___x_238_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_244_; 
if (v_isShared_242_ == 0)
{
v___x_244_ = v___x_241_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_a_239_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
else
{
lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_254_; 
v_a_247_ = lean_ctor_get(v___x_238_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_254_ == 0)
{
v___x_249_ = v___x_238_;
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_a_247_);
lean_dec(v___x_238_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_252_; 
if (v_isShared_250_ == 0)
{
v___x_252_ = v___x_249_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_a_247_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg___boxed(lean_object* v_mvarId_255_, lean_object* v_x_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg(v_mvarId_255_, v_x_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4(lean_object* v_00_u03b1_263_, lean_object* v_mvarId_264_, lean_object* v_x_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg(v_mvarId_264_, v_x_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___boxed(lean_object* v_00_u03b1_272_, lean_object* v_mvarId_273_, lean_object* v_x_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4(v_00_u03b1_272_, v_mvarId_273_, v_x_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
return v_res_280_;
}
}
LEAN_EXPORT uint8_t l_Lean_MVarId_clear___lam__0(lean_object* v_fvarId_281_, lean_object* v_localInst_282_){
_start:
{
lean_object* v_fvar_283_; lean_object* v___x_284_; uint8_t v___x_285_; 
v_fvar_283_ = lean_ctor_get(v_localInst_282_, 1);
v___x_284_ = l_Lean_Expr_fvarId_x21(v_fvar_283_);
v___x_285_ = l_Lean_instBEqFVarId_beq(v___x_284_, v_fvarId_281_);
lean_dec(v___x_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clear___lam__0___boxed(lean_object* v_fvarId_286_, lean_object* v_localInst_287_){
_start:
{
uint8_t v_res_288_; lean_object* v_r_289_; 
v_res_288_ = l_Lean_MVarId_clear___lam__0(v_fvarId_286_, v_localInst_287_);
lean_dec_ref(v_localInst_287_);
lean_dec(v_fvarId_286_);
v_r_289_ = lean_box(v_res_288_);
return v_r_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13_spec__14___redArg(lean_object* v_x_290_, lean_object* v_x_291_, lean_object* v_x_292_, lean_object* v_x_293_){
_start:
{
lean_object* v_ks_294_; lean_object* v_vs_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_319_; 
v_ks_294_ = lean_ctor_get(v_x_290_, 0);
v_vs_295_ = lean_ctor_get(v_x_290_, 1);
v_isSharedCheck_319_ = !lean_is_exclusive(v_x_290_);
if (v_isSharedCheck_319_ == 0)
{
v___x_297_ = v_x_290_;
v_isShared_298_ = v_isSharedCheck_319_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_vs_295_);
lean_inc(v_ks_294_);
lean_dec(v_x_290_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_319_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_299_; uint8_t v___x_300_; 
v___x_299_ = lean_array_get_size(v_ks_294_);
v___x_300_ = lean_nat_dec_lt(v_x_291_, v___x_299_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_304_; 
lean_dec(v_x_291_);
v___x_301_ = lean_array_push(v_ks_294_, v_x_292_);
v___x_302_ = lean_array_push(v_vs_295_, v_x_293_);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 1, v___x_302_);
lean_ctor_set(v___x_297_, 0, v___x_301_);
v___x_304_ = v___x_297_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v___x_301_);
lean_ctor_set(v_reuseFailAlloc_305_, 1, v___x_302_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
else
{
lean_object* v_k_x27_306_; uint8_t v___x_307_; 
v_k_x27_306_ = lean_array_fget_borrowed(v_ks_294_, v_x_291_);
v___x_307_ = l_Lean_instBEqMVarId_beq(v_x_292_, v_k_x27_306_);
if (v___x_307_ == 0)
{
lean_object* v___x_309_; 
if (v_isShared_298_ == 0)
{
v___x_309_ = v___x_297_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_ks_294_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v_vs_295_);
v___x_309_ = v_reuseFailAlloc_313_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = lean_unsigned_to_nat(1u);
v___x_311_ = lean_nat_add(v_x_291_, v___x_310_);
lean_dec(v_x_291_);
v_x_290_ = v___x_309_;
v_x_291_ = v___x_311_;
goto _start;
}
}
else
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_317_; 
v___x_314_ = lean_array_fset(v_ks_294_, v_x_291_, v_x_292_);
v___x_315_ = lean_array_fset(v_vs_295_, v_x_291_, v_x_293_);
lean_dec(v_x_291_);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 1, v___x_315_);
lean_ctor_set(v___x_297_, 0, v___x_314_);
v___x_317_ = v___x_297_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v___x_314_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v___x_315_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13___redArg(lean_object* v_n_320_, lean_object* v_k_321_, lean_object* v_v_322_){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = lean_unsigned_to_nat(0u);
v___x_324_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13_spec__14___redArg(v_n_320_, v___x_323_, v_k_321_, v_v_322_);
return v___x_324_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(lean_object* v_x_326_, size_t v_x_327_, size_t v_x_328_, lean_object* v_x_329_, lean_object* v_x_330_){
_start:
{
if (lean_obj_tag(v_x_326_) == 0)
{
lean_object* v_es_331_; size_t v___x_332_; size_t v___x_333_; lean_object* v_j_334_; lean_object* v___x_335_; uint8_t v___x_336_; 
v_es_331_ = lean_ctor_get(v_x_326_, 0);
v___x_332_ = ((size_t)31ULL);
v___x_333_ = lean_usize_land(v_x_327_, v___x_332_);
v_j_334_ = lean_usize_to_nat(v___x_333_);
v___x_335_ = lean_array_get_size(v_es_331_);
v___x_336_ = lean_nat_dec_lt(v_j_334_, v___x_335_);
if (v___x_336_ == 0)
{
lean_dec(v_j_334_);
lean_dec(v_x_330_);
lean_dec(v_x_329_);
return v_x_326_;
}
else
{
lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_375_; 
lean_inc_ref(v_es_331_);
v_isSharedCheck_375_ = !lean_is_exclusive(v_x_326_);
if (v_isSharedCheck_375_ == 0)
{
lean_object* v_unused_376_; 
v_unused_376_ = lean_ctor_get(v_x_326_, 0);
lean_dec(v_unused_376_);
v___x_338_ = v_x_326_;
v_isShared_339_ = v_isSharedCheck_375_;
goto v_resetjp_337_;
}
else
{
lean_dec(v_x_326_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_375_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v_v_340_; lean_object* v___x_341_; lean_object* v_xs_x27_342_; lean_object* v___y_344_; 
v_v_340_ = lean_array_fget(v_es_331_, v_j_334_);
v___x_341_ = lean_box(0);
v_xs_x27_342_ = lean_array_fset(v_es_331_, v_j_334_, v___x_341_);
switch(lean_obj_tag(v_v_340_))
{
case 0:
{
lean_object* v_key_349_; lean_object* v_val_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_360_; 
v_key_349_ = lean_ctor_get(v_v_340_, 0);
v_val_350_ = lean_ctor_get(v_v_340_, 1);
v_isSharedCheck_360_ = !lean_is_exclusive(v_v_340_);
if (v_isSharedCheck_360_ == 0)
{
v___x_352_ = v_v_340_;
v_isShared_353_ = v_isSharedCheck_360_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_val_350_);
lean_inc(v_key_349_);
lean_dec(v_v_340_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_360_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
uint8_t v___x_354_; 
v___x_354_ = l_Lean_instBEqMVarId_beq(v_x_329_, v_key_349_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; lean_object* v___x_356_; 
lean_del_object(v___x_352_);
v___x_355_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_349_, v_val_350_, v_x_329_, v_x_330_);
v___x_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
v___y_344_ = v___x_356_;
goto v___jp_343_;
}
else
{
lean_object* v___x_358_; 
lean_dec(v_val_350_);
lean_dec(v_key_349_);
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 1, v_x_330_);
lean_ctor_set(v___x_352_, 0, v_x_329_);
v___x_358_ = v___x_352_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_x_329_);
lean_ctor_set(v_reuseFailAlloc_359_, 1, v_x_330_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
v___y_344_ = v___x_358_;
goto v___jp_343_;
}
}
}
}
case 1:
{
lean_object* v_node_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_373_; 
v_node_361_ = lean_ctor_get(v_v_340_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v_v_340_);
if (v_isSharedCheck_373_ == 0)
{
v___x_363_ = v_v_340_;
v_isShared_364_ = v_isSharedCheck_373_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_node_361_);
lean_dec(v_v_340_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_373_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
size_t v___x_365_; size_t v___x_366_; size_t v___x_367_; size_t v___x_368_; lean_object* v___x_369_; lean_object* v___x_371_; 
v___x_365_ = ((size_t)5ULL);
v___x_366_ = lean_usize_shift_right(v_x_327_, v___x_365_);
v___x_367_ = ((size_t)1ULL);
v___x_368_ = lean_usize_add(v_x_328_, v___x_367_);
v___x_369_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_node_361_, v___x_366_, v___x_368_, v_x_329_, v_x_330_);
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 0, v___x_369_);
v___x_371_ = v___x_363_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_369_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
v___y_344_ = v___x_371_;
goto v___jp_343_;
}
}
}
default: 
{
lean_object* v___x_374_; 
v___x_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_374_, 0, v_x_329_);
lean_ctor_set(v___x_374_, 1, v_x_330_);
v___y_344_ = v___x_374_;
goto v___jp_343_;
}
}
v___jp_343_:
{
lean_object* v___x_345_; lean_object* v___x_347_; 
v___x_345_ = lean_array_fset(v_xs_x27_342_, v_j_334_, v___y_344_);
lean_dec(v_j_334_);
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 0, v___x_345_);
v___x_347_ = v___x_338_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v___x_345_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
}
}
}
else
{
lean_object* v_ks_377_; lean_object* v_vs_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_398_; 
v_ks_377_ = lean_ctor_get(v_x_326_, 0);
v_vs_378_ = lean_ctor_get(v_x_326_, 1);
v_isSharedCheck_398_ = !lean_is_exclusive(v_x_326_);
if (v_isSharedCheck_398_ == 0)
{
v___x_380_ = v_x_326_;
v_isShared_381_ = v_isSharedCheck_398_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_vs_378_);
lean_inc(v_ks_377_);
lean_dec(v_x_326_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_398_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_383_; 
if (v_isShared_381_ == 0)
{
v___x_383_ = v___x_380_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_ks_377_);
lean_ctor_set(v_reuseFailAlloc_397_, 1, v_vs_378_);
v___x_383_ = v_reuseFailAlloc_397_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
lean_object* v_newNode_384_; uint8_t v___y_386_; size_t v___x_392_; uint8_t v___x_393_; 
v_newNode_384_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13___redArg(v___x_383_, v_x_329_, v_x_330_);
v___x_392_ = ((size_t)7ULL);
v___x_393_ = lean_usize_dec_le(v___x_392_, v_x_328_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; lean_object* v___x_395_; uint8_t v___x_396_; 
v___x_394_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_384_);
v___x_395_ = lean_unsigned_to_nat(4u);
v___x_396_ = lean_nat_dec_lt(v___x_394_, v___x_395_);
lean_dec(v___x_394_);
v___y_386_ = v___x_396_;
goto v___jp_385_;
}
else
{
v___y_386_ = v___x_393_;
goto v___jp_385_;
}
v___jp_385_:
{
if (v___y_386_ == 0)
{
lean_object* v_ks_387_; lean_object* v_vs_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v_ks_387_ = lean_ctor_get(v_newNode_384_, 0);
lean_inc_ref(v_ks_387_);
v_vs_388_ = lean_ctor_get(v_newNode_384_, 1);
lean_inc_ref(v_vs_388_);
lean_dec_ref(v_newNode_384_);
v___x_389_ = lean_unsigned_to_nat(0u);
v___x_390_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__0);
v___x_391_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg(v_x_328_, v_ks_387_, v_vs_388_, v___x_389_, v___x_390_);
lean_dec_ref(v_vs_388_);
lean_dec_ref(v_ks_387_);
return v___x_391_;
}
else
{
return v_newNode_384_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg(size_t v_depth_399_, lean_object* v_keys_400_, lean_object* v_vals_401_, lean_object* v_i_402_, lean_object* v_entries_403_){
_start:
{
lean_object* v___x_404_; uint8_t v___x_405_; 
v___x_404_ = lean_array_get_size(v_keys_400_);
v___x_405_ = lean_nat_dec_lt(v_i_402_, v___x_404_);
if (v___x_405_ == 0)
{
lean_dec(v_i_402_);
return v_entries_403_;
}
else
{
lean_object* v_k_406_; lean_object* v_v_407_; uint64_t v___x_408_; size_t v_h_409_; size_t v___x_410_; lean_object* v___x_411_; size_t v___x_412_; size_t v___x_413_; size_t v___x_414_; size_t v_h_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v_k_406_ = lean_array_fget_borrowed(v_keys_400_, v_i_402_);
v_v_407_ = lean_array_fget_borrowed(v_vals_401_, v_i_402_);
v___x_408_ = l_Lean_instHashableMVarId_hash(v_k_406_);
v_h_409_ = lean_uint64_to_usize(v___x_408_);
v___x_410_ = ((size_t)5ULL);
v___x_411_ = lean_unsigned_to_nat(1u);
v___x_412_ = ((size_t)1ULL);
v___x_413_ = lean_usize_sub(v_depth_399_, v___x_412_);
v___x_414_ = lean_usize_mul(v___x_410_, v___x_413_);
v_h_415_ = lean_usize_shift_right(v_h_409_, v___x_414_);
v___x_416_ = lean_nat_add(v_i_402_, v___x_411_);
lean_dec(v_i_402_);
lean_inc(v_v_407_);
lean_inc(v_k_406_);
v___x_417_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_entries_403_, v_h_415_, v_depth_399_, v_k_406_, v_v_407_);
v_i_402_ = v___x_416_;
v_entries_403_ = v___x_417_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg___boxed(lean_object* v_depth_419_, lean_object* v_keys_420_, lean_object* v_vals_421_, lean_object* v_i_422_, lean_object* v_entries_423_){
_start:
{
size_t v_depth_boxed_424_; lean_object* v_res_425_; 
v_depth_boxed_424_ = lean_unbox_usize(v_depth_419_);
lean_dec(v_depth_419_);
v_res_425_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg(v_depth_boxed_424_, v_keys_420_, v_vals_421_, v_i_422_, v_entries_423_);
lean_dec_ref(v_vals_421_);
lean_dec_ref(v_keys_420_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___boxed(lean_object* v_x_426_, lean_object* v_x_427_, lean_object* v_x_428_, lean_object* v_x_429_, lean_object* v_x_430_){
_start:
{
size_t v_x_8814__boxed_431_; size_t v_x_8815__boxed_432_; lean_object* v_res_433_; 
v_x_8814__boxed_431_ = lean_unbox_usize(v_x_427_);
lean_dec(v_x_427_);
v_x_8815__boxed_432_ = lean_unbox_usize(v_x_428_);
lean_dec(v_x_428_);
v_res_433_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_x_426_, v_x_8814__boxed_431_, v_x_8815__boxed_432_, v_x_429_, v_x_430_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3___redArg(lean_object* v_x_434_, lean_object* v_x_435_, lean_object* v_x_436_){
_start:
{
uint64_t v___x_437_; size_t v___x_438_; size_t v___x_439_; lean_object* v___x_440_; 
v___x_437_ = l_Lean_instHashableMVarId_hash(v_x_435_);
v___x_438_ = lean_uint64_to_usize(v___x_437_);
v___x_439_ = ((size_t)1ULL);
v___x_440_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_x_434_, v___x_438_, v___x_439_, v_x_435_, v_x_436_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg(lean_object* v_mvarId_441_, lean_object* v_val_442_, lean_object* v___y_443_){
_start:
{
lean_object* v___x_445_; lean_object* v_mctx_446_; lean_object* v_cache_447_; lean_object* v_zetaDeltaFVarIds_448_; lean_object* v_postponed_449_; lean_object* v_diag_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_479_; 
v___x_445_ = lean_st_ref_take(v___y_443_);
v_mctx_446_ = lean_ctor_get(v___x_445_, 0);
v_cache_447_ = lean_ctor_get(v___x_445_, 1);
v_zetaDeltaFVarIds_448_ = lean_ctor_get(v___x_445_, 2);
v_postponed_449_ = lean_ctor_get(v___x_445_, 3);
v_diag_450_ = lean_ctor_get(v___x_445_, 4);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_479_ == 0)
{
v___x_452_ = v___x_445_;
v_isShared_453_ = v_isSharedCheck_479_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_diag_450_);
lean_inc(v_postponed_449_);
lean_inc(v_zetaDeltaFVarIds_448_);
lean_inc(v_cache_447_);
lean_inc(v_mctx_446_);
lean_dec(v___x_445_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_479_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v_depth_454_; lean_object* v_levelAssignDepth_455_; lean_object* v_lmvarCounter_456_; lean_object* v_mvarCounter_457_; lean_object* v_lDecls_458_; lean_object* v_decls_459_; lean_object* v_userNames_460_; lean_object* v_lAssignment_461_; lean_object* v_eAssignment_462_; lean_object* v_dAssignment_463_; lean_object* v_instanceTypedMVars_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_478_; 
v_depth_454_ = lean_ctor_get(v_mctx_446_, 0);
v_levelAssignDepth_455_ = lean_ctor_get(v_mctx_446_, 1);
v_lmvarCounter_456_ = lean_ctor_get(v_mctx_446_, 2);
v_mvarCounter_457_ = lean_ctor_get(v_mctx_446_, 3);
v_lDecls_458_ = lean_ctor_get(v_mctx_446_, 4);
v_decls_459_ = lean_ctor_get(v_mctx_446_, 5);
v_userNames_460_ = lean_ctor_get(v_mctx_446_, 6);
v_lAssignment_461_ = lean_ctor_get(v_mctx_446_, 7);
v_eAssignment_462_ = lean_ctor_get(v_mctx_446_, 8);
v_dAssignment_463_ = lean_ctor_get(v_mctx_446_, 9);
v_instanceTypedMVars_464_ = lean_ctor_get(v_mctx_446_, 10);
v_isSharedCheck_478_ = !lean_is_exclusive(v_mctx_446_);
if (v_isSharedCheck_478_ == 0)
{
v___x_466_ = v_mctx_446_;
v_isShared_467_ = v_isSharedCheck_478_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_instanceTypedMVars_464_);
lean_inc(v_dAssignment_463_);
lean_inc(v_eAssignment_462_);
lean_inc(v_lAssignment_461_);
lean_inc(v_userNames_460_);
lean_inc(v_decls_459_);
lean_inc(v_lDecls_458_);
lean_inc(v_mvarCounter_457_);
lean_inc(v_lmvarCounter_456_);
lean_inc(v_levelAssignDepth_455_);
lean_inc(v_depth_454_);
lean_dec(v_mctx_446_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_478_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_468_; lean_object* v___x_470_; 
v___x_468_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3___redArg(v_eAssignment_462_, v_mvarId_441_, v_val_442_);
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 8, v___x_468_);
v___x_470_ = v___x_466_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_depth_454_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v_levelAssignDepth_455_);
lean_ctor_set(v_reuseFailAlloc_477_, 2, v_lmvarCounter_456_);
lean_ctor_set(v_reuseFailAlloc_477_, 3, v_mvarCounter_457_);
lean_ctor_set(v_reuseFailAlloc_477_, 4, v_lDecls_458_);
lean_ctor_set(v_reuseFailAlloc_477_, 5, v_decls_459_);
lean_ctor_set(v_reuseFailAlloc_477_, 6, v_userNames_460_);
lean_ctor_set(v_reuseFailAlloc_477_, 7, v_lAssignment_461_);
lean_ctor_set(v_reuseFailAlloc_477_, 8, v___x_468_);
lean_ctor_set(v_reuseFailAlloc_477_, 9, v_dAssignment_463_);
lean_ctor_set(v_reuseFailAlloc_477_, 10, v_instanceTypedMVars_464_);
v___x_470_ = v_reuseFailAlloc_477_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
lean_object* v___x_472_; 
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 0, v___x_470_);
v___x_472_ = v___x_452_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v___x_470_);
lean_ctor_set(v_reuseFailAlloc_476_, 1, v_cache_447_);
lean_ctor_set(v_reuseFailAlloc_476_, 2, v_zetaDeltaFVarIds_448_);
lean_ctor_set(v_reuseFailAlloc_476_, 3, v_postponed_449_);
lean_ctor_set(v_reuseFailAlloc_476_, 4, v_diag_450_);
v___x_472_ = v_reuseFailAlloc_476_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_473_ = lean_st_ref_put(v___y_443_, v___x_472_);
v___x_474_ = lean_box(0);
v___x_475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_475_, 0, v___x_474_);
return v___x_475_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg___boxed(lean_object* v_mvarId_480_, lean_object* v_val_481_, lean_object* v___y_482_, lean_object* v___y_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg(v_mvarId_480_, v_val_481_, v___y_482_);
lean_dec(v___y_482_);
return v_res_484_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3(void){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__2));
v___x_490_ = l_Lean_stringToMessageData(v___x_489_);
return v___x_490_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5(void){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__4));
v___x_493_ = l_Lean_stringToMessageData(v___x_492_);
return v___x_493_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7(void){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__6));
v___x_496_ = l_Lean_stringToMessageData(v___x_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9(lean_object* v_fvarId_497_, lean_object* v_mvarId_498_, lean_object* v_as_499_, size_t v_i_500_, size_t v_stop_501_, lean_object* v_b_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
lean_object* v_a_509_; uint8_t v___x_513_; 
v___x_513_ = lean_usize_dec_eq(v_i_500_, v_stop_501_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; 
v___x_514_ = lean_array_uget(v_as_499_, v_i_500_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v___x_515_; 
v___x_515_ = lean_box(0);
v_a_509_ = v___x_515_;
goto v___jp_508_;
}
else
{
lean_object* v_val_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_553_; 
v_val_516_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_553_ == 0)
{
v___x_518_ = v___x_514_;
v_isShared_519_ = v_isSharedCheck_553_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_val_516_);
lean_dec(v___x_514_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_553_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_520_; uint8_t v___x_521_; 
v___x_520_ = l_Lean_LocalDecl_fvarId(v_val_516_);
v___x_521_ = l_Lean_instBEqFVarId_beq(v___x_520_, v_fvarId_497_);
lean_dec(v___x_520_);
if (v___x_521_ == 0)
{
uint8_t v___x_522_; lean_object* v___x_523_; 
v___x_522_ = 1;
lean_inc(v_fvarId_497_);
lean_inc(v_val_516_);
v___x_523_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg(v_val_516_, v_fvarId_497_, v___x_522_, v___y_504_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v_a_524_; uint8_t v___x_525_; 
v_a_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_a_524_);
lean_dec_ref_known(v___x_523_, 1);
v___x_525_ = lean_unbox(v_a_524_);
lean_dec(v_a_524_);
if (v___x_525_ == 0)
{
lean_object* v___x_526_; 
lean_del_object(v___x_518_);
lean_dec(v_val_516_);
v___x_526_ = lean_box(0);
v_a_509_ = v___x_526_;
goto v___jp_508_;
}
else
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_540_; 
v___x_527_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__1));
v___x_528_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3);
v___x_529_ = l_Lean_LocalDecl_toExpr(v_val_516_);
v___x_530_ = l_Lean_MessageData_ofExpr(v___x_529_);
v___x_531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_528_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
v___x_532_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5);
v___x_533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_531_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
lean_inc(v_fvarId_497_);
v___x_534_ = l_Lean_mkFVar(v_fvarId_497_);
v___x_535_ = l_Lean_MessageData_ofExpr(v___x_534_);
v___x_536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_533_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
v___x_537_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7);
v___x_538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_536_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 0, v___x_538_);
v___x_540_ = v___x_518_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_538_);
v___x_540_ = v_reuseFailAlloc_543_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
lean_object* v___x_541_; 
lean_inc(v_mvarId_498_);
v___x_541_ = l_Lean_Meta_throwTacticEx___redArg(v___x_527_, v_mvarId_498_, v___x_540_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
if (lean_obj_tag(v___x_541_) == 0)
{
lean_object* v_a_542_; 
v_a_542_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_a_542_);
lean_dec_ref_known(v___x_541_, 1);
v_a_509_ = v_a_542_;
goto v___jp_508_;
}
else
{
lean_dec(v_mvarId_498_);
lean_dec(v_fvarId_497_);
return v___x_541_;
}
}
}
}
else
{
lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_551_; 
lean_del_object(v___x_518_);
lean_dec(v_val_516_);
lean_dec(v_mvarId_498_);
lean_dec(v_fvarId_497_);
v_a_544_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_551_ == 0)
{
v___x_546_ = v___x_523_;
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_dec(v___x_523_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_a_544_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
else
{
lean_object* v___x_552_; 
lean_del_object(v___x_518_);
lean_dec(v_val_516_);
v___x_552_ = lean_box(0);
v_a_509_ = v___x_552_;
goto v___jp_508_;
}
}
}
}
else
{
lean_object* v___x_554_; 
lean_dec(v_mvarId_498_);
lean_dec(v_fvarId_497_);
v___x_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_554_, 0, v_b_502_);
return v___x_554_;
}
v___jp_508_:
{
size_t v___x_510_; size_t v___x_511_; 
v___x_510_ = ((size_t)1ULL);
v___x_511_ = lean_usize_add(v_i_500_, v___x_510_);
v_i_500_ = v___x_511_;
v_b_502_ = v_a_509_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___boxed(lean_object* v_fvarId_555_, lean_object* v_mvarId_556_, lean_object* v_as_557_, lean_object* v_i_558_, lean_object* v_stop_559_, lean_object* v_b_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
size_t v_i_boxed_566_; size_t v_stop_boxed_567_; lean_object* v_res_568_; 
v_i_boxed_566_ = lean_unbox_usize(v_i_558_);
lean_dec(v_i_558_);
v_stop_boxed_567_ = lean_unbox_usize(v_stop_559_);
lean_dec(v_stop_559_);
v_res_568_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9(v_fvarId_555_, v_mvarId_556_, v_as_557_, v_i_boxed_566_, v_stop_boxed_567_, v_b_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec_ref(v_as_557_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(lean_object* v_fvarId_569_, lean_object* v_mvarId_570_, lean_object* v_as_571_, size_t v_i_572_, size_t v_stop_573_, lean_object* v_b_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
lean_object* v_a_581_; uint8_t v___x_585_; 
v___x_585_ = lean_usize_dec_eq(v_i_572_, v_stop_573_);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; 
v___x_586_ = lean_array_uget(v_as_571_, v_i_572_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v___x_587_; 
v___x_587_ = lean_box(0);
v_a_581_ = v___x_587_;
goto v___jp_580_;
}
else
{
lean_object* v_val_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_625_; 
v_val_588_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_625_ == 0)
{
v___x_590_ = v___x_586_;
v_isShared_591_ = v_isSharedCheck_625_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_val_588_);
lean_dec(v___x_586_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_625_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_592_; uint8_t v___x_593_; 
v___x_592_ = l_Lean_LocalDecl_fvarId(v_val_588_);
v___x_593_ = l_Lean_instBEqFVarId_beq(v___x_592_, v_fvarId_569_);
lean_dec(v___x_592_);
if (v___x_593_ == 0)
{
uint8_t v___x_594_; lean_object* v___x_595_; 
v___x_594_ = 1;
lean_inc(v_fvarId_569_);
lean_inc(v_val_588_);
v___x_595_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg(v_val_588_, v_fvarId_569_, v___x_594_, v___y_576_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v_a_596_; uint8_t v___x_597_; 
v_a_596_ = lean_ctor_get(v___x_595_, 0);
lean_inc(v_a_596_);
lean_dec_ref_known(v___x_595_, 1);
v___x_597_ = lean_unbox(v_a_596_);
lean_dec(v_a_596_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; 
lean_del_object(v___x_590_);
lean_dec(v_val_588_);
v___x_598_ = lean_box(0);
v_a_581_ = v___x_598_;
goto v___jp_580_;
}
else
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_612_; 
v___x_599_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__1));
v___x_600_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3);
v___x_601_ = l_Lean_LocalDecl_toExpr(v_val_588_);
v___x_602_ = l_Lean_MessageData_ofExpr(v___x_601_);
v___x_603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_600_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
v___x_604_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5);
v___x_605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_603_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
lean_inc(v_fvarId_569_);
v___x_606_ = l_Lean_mkFVar(v_fvarId_569_);
v___x_607_ = l_Lean_MessageData_ofExpr(v___x_606_);
v___x_608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_605_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
v___x_609_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7);
v___x_610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_608_);
lean_ctor_set(v___x_610_, 1, v___x_609_);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 0, v___x_610_);
v___x_612_ = v___x_590_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_610_);
v___x_612_ = v_reuseFailAlloc_615_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
lean_object* v___x_613_; 
lean_inc(v_mvarId_570_);
v___x_613_ = l_Lean_Meta_throwTacticEx___redArg(v___x_599_, v_mvarId_570_, v___x_612_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
if (lean_obj_tag(v___x_613_) == 0)
{
lean_object* v_a_614_; 
v_a_614_ = lean_ctor_get(v___x_613_, 0);
lean_inc(v_a_614_);
lean_dec_ref_known(v___x_613_, 1);
v_a_581_ = v_a_614_;
goto v___jp_580_;
}
else
{
lean_dec(v_mvarId_570_);
lean_dec(v_fvarId_569_);
return v___x_613_;
}
}
}
}
else
{
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_623_; 
lean_del_object(v___x_590_);
lean_dec(v_val_588_);
lean_dec(v_mvarId_570_);
lean_dec(v_fvarId_569_);
v_a_616_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_623_ == 0)
{
v___x_618_ = v___x_595_;
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_595_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_621_; 
if (v_isShared_619_ == 0)
{
v___x_621_ = v___x_618_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_a_616_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
}
else
{
lean_object* v___x_624_; 
lean_del_object(v___x_590_);
lean_dec(v_val_588_);
v___x_624_ = lean_box(0);
v_a_581_ = v___x_624_;
goto v___jp_580_;
}
}
}
}
else
{
lean_object* v___x_626_; 
lean_dec(v_mvarId_570_);
lean_dec(v_fvarId_569_);
v___x_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_626_, 0, v_b_574_);
return v___x_626_;
}
v___jp_580_:
{
size_t v___x_582_; size_t v___x_583_; lean_object* v___x_584_; 
v___x_582_ = ((size_t)1ULL);
v___x_583_ = lean_usize_add(v_i_572_, v___x_582_);
v___x_584_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9(v_fvarId_569_, v_mvarId_570_, v_as_571_, v___x_583_, v_stop_573_, v_a_581_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
return v___x_584_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5___boxed(lean_object* v_fvarId_627_, lean_object* v_mvarId_628_, lean_object* v_as_629_, lean_object* v_i_630_, lean_object* v_stop_631_, lean_object* v_b_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
size_t v_i_boxed_638_; size_t v_stop_boxed_639_; lean_object* v_res_640_; 
v_i_boxed_638_ = lean_unbox_usize(v_i_630_);
lean_dec(v_i_630_);
v_stop_boxed_639_ = lean_unbox_usize(v_stop_631_);
lean_dec(v_stop_631_);
v_res_640_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_627_, v_mvarId_628_, v_as_629_, v_i_boxed_638_, v_stop_boxed_639_, v_b_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec_ref(v_as_629_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6(lean_object* v_fvarId_641_, lean_object* v_mvarId_642_, lean_object* v_x_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_){
_start:
{
if (lean_obj_tag(v_x_643_) == 0)
{
lean_object* v_cs_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_670_; 
v_cs_649_ = lean_ctor_get(v_x_643_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v_x_643_);
if (v_isSharedCheck_670_ == 0)
{
v___x_651_ = v_x_643_;
v_isShared_652_ = v_isSharedCheck_670_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_cs_649_);
lean_dec(v_x_643_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_670_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; uint8_t v___x_656_; 
v___x_653_ = lean_unsigned_to_nat(0u);
v___x_654_ = lean_array_get_size(v_cs_649_);
v___x_655_ = lean_box(0);
v___x_656_ = lean_nat_dec_lt(v___x_653_, v___x_654_);
if (v___x_656_ == 0)
{
lean_object* v___x_658_; 
lean_dec_ref(v_cs_649_);
lean_dec(v_mvarId_642_);
lean_dec(v_fvarId_641_);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 0, v___x_655_);
v___x_658_ = v___x_651_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_655_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
else
{
uint8_t v___x_660_; 
v___x_660_ = lean_nat_dec_le(v___x_654_, v___x_654_);
if (v___x_660_ == 0)
{
if (v___x_656_ == 0)
{
lean_object* v___x_662_; 
lean_dec_ref(v_cs_649_);
lean_dec(v_mvarId_642_);
lean_dec(v_fvarId_641_);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 0, v___x_655_);
v___x_662_ = v___x_651_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v___x_655_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
else
{
size_t v___x_664_; size_t v___x_665_; lean_object* v___x_666_; 
lean_del_object(v___x_651_);
v___x_664_ = ((size_t)0ULL);
v___x_665_ = lean_usize_of_nat(v___x_654_);
v___x_666_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(v_fvarId_641_, v_mvarId_642_, v_cs_649_, v___x_664_, v___x_665_, v___x_655_, v___y_644_, v___y_645_, v___y_646_, v___y_647_);
lean_dec_ref(v_cs_649_);
return v___x_666_;
}
}
else
{
size_t v___x_667_; size_t v___x_668_; lean_object* v___x_669_; 
lean_del_object(v___x_651_);
v___x_667_ = ((size_t)0ULL);
v___x_668_ = lean_usize_of_nat(v___x_654_);
v___x_669_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(v_fvarId_641_, v_mvarId_642_, v_cs_649_, v___x_667_, v___x_668_, v___x_655_, v___y_644_, v___y_645_, v___y_646_, v___y_647_);
lean_dec_ref(v_cs_649_);
return v___x_669_;
}
}
}
}
else
{
lean_object* v_vs_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_692_; 
v_vs_671_ = lean_ctor_get(v_x_643_, 0);
v_isSharedCheck_692_ = !lean_is_exclusive(v_x_643_);
if (v_isSharedCheck_692_ == 0)
{
v___x_673_ = v_x_643_;
v_isShared_674_ = v_isSharedCheck_692_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_vs_671_);
lean_dec(v_x_643_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_692_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; uint8_t v___x_678_; 
v___x_675_ = lean_unsigned_to_nat(0u);
v___x_676_ = lean_array_get_size(v_vs_671_);
v___x_677_ = lean_box(0);
v___x_678_ = lean_nat_dec_lt(v___x_675_, v___x_676_);
if (v___x_678_ == 0)
{
lean_object* v___x_680_; 
lean_dec_ref(v_vs_671_);
lean_dec(v_mvarId_642_);
lean_dec(v_fvarId_641_);
if (v_isShared_674_ == 0)
{
lean_ctor_set_tag(v___x_673_, 0);
lean_ctor_set(v___x_673_, 0, v___x_677_);
v___x_680_ = v___x_673_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_677_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
else
{
uint8_t v___x_682_; 
v___x_682_ = lean_nat_dec_le(v___x_676_, v___x_676_);
if (v___x_682_ == 0)
{
if (v___x_678_ == 0)
{
lean_object* v___x_684_; 
lean_dec_ref(v_vs_671_);
lean_dec(v_mvarId_642_);
lean_dec(v_fvarId_641_);
if (v_isShared_674_ == 0)
{
lean_ctor_set_tag(v___x_673_, 0);
lean_ctor_set(v___x_673_, 0, v___x_677_);
v___x_684_ = v___x_673_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_677_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
else
{
size_t v___x_686_; size_t v___x_687_; lean_object* v___x_688_; 
lean_del_object(v___x_673_);
v___x_686_ = ((size_t)0ULL);
v___x_687_ = lean_usize_of_nat(v___x_676_);
v___x_688_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_641_, v_mvarId_642_, v_vs_671_, v___x_686_, v___x_687_, v___x_677_, v___y_644_, v___y_645_, v___y_646_, v___y_647_);
lean_dec_ref(v_vs_671_);
return v___x_688_;
}
}
else
{
size_t v___x_689_; size_t v___x_690_; lean_object* v___x_691_; 
lean_del_object(v___x_673_);
v___x_689_ = ((size_t)0ULL);
v___x_690_ = lean_usize_of_nat(v___x_676_);
v___x_691_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_641_, v_mvarId_642_, v_vs_671_, v___x_689_, v___x_690_, v___x_677_, v___y_644_, v___y_645_, v___y_646_, v___y_647_);
lean_dec_ref(v_vs_671_);
return v___x_691_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(lean_object* v_fvarId_693_, lean_object* v_mvarId_694_, lean_object* v_as_695_, size_t v_i_696_, size_t v_stop_697_, lean_object* v_b_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
uint8_t v___x_704_; 
v___x_704_ = lean_usize_dec_eq(v_i_696_, v_stop_697_);
if (v___x_704_ == 0)
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = lean_array_uget_borrowed(v_as_695_, v_i_696_);
lean_inc(v___x_705_);
lean_inc(v_mvarId_694_);
lean_inc(v_fvarId_693_);
v___x_706_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6(v_fvarId_693_, v_mvarId_694_, v___x_705_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_a_707_; size_t v___x_708_; size_t v___x_709_; 
v_a_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_a_707_);
lean_dec_ref_known(v___x_706_, 1);
v___x_708_ = ((size_t)1ULL);
v___x_709_ = lean_usize_add(v_i_696_, v___x_708_);
v_i_696_ = v___x_709_;
v_b_698_ = v_a_707_;
goto _start;
}
else
{
lean_dec(v_mvarId_694_);
lean_dec(v_fvarId_693_);
return v___x_706_;
}
}
else
{
lean_object* v___x_711_; 
lean_dec(v_mvarId_694_);
lean_dec(v_fvarId_693_);
v___x_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_711_, 0, v_b_698_);
return v___x_711_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7___boxed(lean_object* v_fvarId_712_, lean_object* v_mvarId_713_, lean_object* v_as_714_, lean_object* v_i_715_, lean_object* v_stop_716_, lean_object* v_b_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
size_t v_i_boxed_723_; size_t v_stop_boxed_724_; lean_object* v_res_725_; 
v_i_boxed_723_ = lean_unbox_usize(v_i_715_);
lean_dec(v_i_715_);
v_stop_boxed_724_ = lean_unbox_usize(v_stop_716_);
lean_dec(v_stop_716_);
v_res_725_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(v_fvarId_712_, v_mvarId_713_, v_as_714_, v_i_boxed_723_, v_stop_boxed_724_, v_b_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec_ref(v_as_714_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6___boxed(lean_object* v_fvarId_726_, lean_object* v_mvarId_727_, lean_object* v_x_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6(v_fvarId_726_, v_mvarId_727_, v_x_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6(lean_object* v_fvarId_735_, lean_object* v_mvarId_736_, lean_object* v_t_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
lean_object* v_root_743_; lean_object* v_tail_744_; lean_object* v___x_745_; 
v_root_743_ = lean_ctor_get(v_t_737_, 0);
lean_inc_ref(v_root_743_);
v_tail_744_ = lean_ctor_get(v_t_737_, 1);
lean_inc_ref(v_tail_744_);
lean_dec_ref(v_t_737_);
lean_inc(v_mvarId_736_);
lean_inc(v_fvarId_735_);
v___x_745_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6(v_fvarId_735_, v_mvarId_736_, v_root_743_, v___y_738_, v___y_739_, v___y_740_, v___y_741_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_766_; 
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_766_ == 0)
{
lean_object* v_unused_767_; 
v_unused_767_ = lean_ctor_get(v___x_745_, 0);
lean_dec(v_unused_767_);
v___x_747_ = v___x_745_;
v_isShared_748_ = v_isSharedCheck_766_;
goto v_resetjp_746_;
}
else
{
lean_dec(v___x_745_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_766_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; uint8_t v___x_752_; 
v___x_749_ = lean_unsigned_to_nat(0u);
v___x_750_ = lean_array_get_size(v_tail_744_);
v___x_751_ = lean_box(0);
v___x_752_ = lean_nat_dec_lt(v___x_749_, v___x_750_);
if (v___x_752_ == 0)
{
lean_object* v___x_754_; 
lean_dec_ref(v_tail_744_);
lean_dec(v_mvarId_736_);
lean_dec(v_fvarId_735_);
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 0, v___x_751_);
v___x_754_ = v___x_747_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_751_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
else
{
uint8_t v___x_756_; 
v___x_756_ = lean_nat_dec_le(v___x_750_, v___x_750_);
if (v___x_756_ == 0)
{
if (v___x_752_ == 0)
{
lean_object* v___x_758_; 
lean_dec_ref(v_tail_744_);
lean_dec(v_mvarId_736_);
lean_dec(v_fvarId_735_);
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 0, v___x_751_);
v___x_758_ = v___x_747_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_751_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
else
{
size_t v___x_760_; size_t v___x_761_; lean_object* v___x_762_; 
lean_del_object(v___x_747_);
v___x_760_ = ((size_t)0ULL);
v___x_761_ = lean_usize_of_nat(v___x_750_);
v___x_762_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_735_, v_mvarId_736_, v_tail_744_, v___x_760_, v___x_761_, v___x_751_, v___y_738_, v___y_739_, v___y_740_, v___y_741_);
lean_dec_ref(v_tail_744_);
return v___x_762_;
}
}
else
{
size_t v___x_763_; size_t v___x_764_; lean_object* v___x_765_; 
lean_del_object(v___x_747_);
v___x_763_ = ((size_t)0ULL);
v___x_764_ = lean_usize_of_nat(v___x_750_);
v___x_765_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_735_, v_mvarId_736_, v_tail_744_, v___x_763_, v___x_764_, v___x_751_, v___y_738_, v___y_739_, v___y_740_, v___y_741_);
lean_dec_ref(v_tail_744_);
return v___x_765_;
}
}
}
}
else
{
lean_dec_ref(v_tail_744_);
lean_dec(v_mvarId_736_);
lean_dec(v_fvarId_735_);
return v___x_745_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6___boxed(lean_object* v_fvarId_768_, lean_object* v_mvarId_769_, lean_object* v_t_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6(v_fvarId_768_, v_mvarId_769_, v_t_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
return v_res_776_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4(lean_object* v_fvarId_778_, lean_object* v_mvarId_779_, lean_object* v_x_780_, size_t v_x_781_, size_t v_x_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
if (lean_obj_tag(v_x_780_) == 0)
{
lean_object* v_cs_788_; lean_object* v___x_789_; size_t v___x_790_; lean_object* v_j_791_; lean_object* v___x_792_; size_t v___x_793_; size_t v___x_794_; size_t v___x_795_; size_t v___x_796_; size_t v___x_797_; size_t v___x_798_; lean_object* v___x_799_; 
v_cs_788_ = lean_ctor_get(v_x_780_, 0);
lean_inc_ref(v_cs_788_);
lean_dec_ref_known(v_x_780_, 1);
v___x_789_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0);
v___x_790_ = lean_usize_shift_right(v_x_781_, v_x_782_);
v_j_791_ = lean_usize_to_nat(v___x_790_);
v___x_792_ = lean_array_get_borrowed(v___x_789_, v_cs_788_, v_j_791_);
v___x_793_ = ((size_t)1ULL);
v___x_794_ = lean_usize_shift_left(v___x_793_, v_x_782_);
v___x_795_ = lean_usize_sub(v___x_794_, v___x_793_);
v___x_796_ = lean_usize_land(v_x_781_, v___x_795_);
v___x_797_ = ((size_t)5ULL);
v___x_798_ = lean_usize_sub(v_x_782_, v___x_797_);
lean_inc(v___x_792_);
lean_inc(v_mvarId_779_);
lean_inc(v_fvarId_778_);
v___x_799_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4(v_fvarId_778_, v_mvarId_779_, v___x_792_, v___x_796_, v___x_798_, v___y_783_, v___y_784_, v___y_785_, v___y_786_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_821_; 
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_821_ == 0)
{
lean_object* v_unused_822_; 
v_unused_822_ = lean_ctor_get(v___x_799_, 0);
lean_dec(v_unused_822_);
v___x_801_ = v___x_799_;
v_isShared_802_ = v_isSharedCheck_821_;
goto v_resetjp_800_;
}
else
{
lean_dec(v___x_799_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_821_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; uint8_t v___x_807_; 
v___x_803_ = lean_unsigned_to_nat(1u);
v___x_804_ = lean_nat_add(v_j_791_, v___x_803_);
lean_dec(v_j_791_);
v___x_805_ = lean_array_get_size(v_cs_788_);
v___x_806_ = lean_box(0);
v___x_807_ = lean_nat_dec_lt(v___x_804_, v___x_805_);
if (v___x_807_ == 0)
{
lean_object* v___x_809_; 
lean_dec(v___x_804_);
lean_dec_ref(v_cs_788_);
lean_dec(v_mvarId_779_);
lean_dec(v_fvarId_778_);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 0, v___x_806_);
v___x_809_ = v___x_801_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v___x_806_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
else
{
uint8_t v___x_811_; 
v___x_811_ = lean_nat_dec_le(v___x_805_, v___x_805_);
if (v___x_811_ == 0)
{
if (v___x_807_ == 0)
{
lean_object* v___x_813_; 
lean_dec(v___x_804_);
lean_dec_ref(v_cs_788_);
lean_dec(v_mvarId_779_);
lean_dec(v_fvarId_778_);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 0, v___x_806_);
v___x_813_ = v___x_801_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_806_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
else
{
size_t v___x_815_; size_t v___x_816_; lean_object* v___x_817_; 
lean_del_object(v___x_801_);
v___x_815_ = lean_usize_of_nat(v___x_804_);
lean_dec(v___x_804_);
v___x_816_ = lean_usize_of_nat(v___x_805_);
v___x_817_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(v_fvarId_778_, v_mvarId_779_, v_cs_788_, v___x_815_, v___x_816_, v___x_806_, v___y_783_, v___y_784_, v___y_785_, v___y_786_);
lean_dec_ref(v_cs_788_);
return v___x_817_;
}
}
else
{
size_t v___x_818_; size_t v___x_819_; lean_object* v___x_820_; 
lean_del_object(v___x_801_);
v___x_818_ = lean_usize_of_nat(v___x_804_);
lean_dec(v___x_804_);
v___x_819_ = lean_usize_of_nat(v___x_805_);
v___x_820_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(v_fvarId_778_, v_mvarId_779_, v_cs_788_, v___x_818_, v___x_819_, v___x_806_, v___y_783_, v___y_784_, v___y_785_, v___y_786_);
lean_dec_ref(v_cs_788_);
return v___x_820_;
}
}
}
}
else
{
lean_dec(v_j_791_);
lean_dec_ref(v_cs_788_);
lean_dec(v_mvarId_779_);
lean_dec(v_fvarId_778_);
return v___x_799_;
}
}
else
{
lean_object* v_vs_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_844_; 
v_vs_823_ = lean_ctor_get(v_x_780_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v_x_780_);
if (v_isSharedCheck_844_ == 0)
{
v___x_825_ = v_x_780_;
v_isShared_826_ = v_isSharedCheck_844_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_vs_823_);
lean_dec(v_x_780_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_844_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; uint8_t v___x_830_; 
v___x_827_ = lean_usize_to_nat(v_x_781_);
v___x_828_ = lean_array_get_size(v_vs_823_);
v___x_829_ = lean_box(0);
v___x_830_ = lean_nat_dec_lt(v___x_827_, v___x_828_);
if (v___x_830_ == 0)
{
lean_object* v___x_832_; 
lean_dec(v___x_827_);
lean_dec_ref(v_vs_823_);
lean_dec(v_mvarId_779_);
lean_dec(v_fvarId_778_);
if (v_isShared_826_ == 0)
{
lean_ctor_set_tag(v___x_825_, 0);
lean_ctor_set(v___x_825_, 0, v___x_829_);
v___x_832_ = v___x_825_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v___x_829_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
else
{
uint8_t v___x_834_; 
v___x_834_ = lean_nat_dec_le(v___x_828_, v___x_828_);
if (v___x_834_ == 0)
{
if (v___x_830_ == 0)
{
lean_object* v___x_836_; 
lean_dec(v___x_827_);
lean_dec_ref(v_vs_823_);
lean_dec(v_mvarId_779_);
lean_dec(v_fvarId_778_);
if (v_isShared_826_ == 0)
{
lean_ctor_set_tag(v___x_825_, 0);
lean_ctor_set(v___x_825_, 0, v___x_829_);
v___x_836_ = v___x_825_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v___x_829_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
else
{
size_t v___x_838_; size_t v___x_839_; lean_object* v___x_840_; 
lean_del_object(v___x_825_);
v___x_838_ = lean_usize_of_nat(v___x_827_);
lean_dec(v___x_827_);
v___x_839_ = lean_usize_of_nat(v___x_828_);
v___x_840_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_778_, v_mvarId_779_, v_vs_823_, v___x_838_, v___x_839_, v___x_829_, v___y_783_, v___y_784_, v___y_785_, v___y_786_);
lean_dec_ref(v_vs_823_);
return v___x_840_;
}
}
else
{
size_t v___x_841_; size_t v___x_842_; lean_object* v___x_843_; 
lean_del_object(v___x_825_);
v___x_841_ = lean_usize_of_nat(v___x_827_);
lean_dec(v___x_827_);
v___x_842_ = lean_usize_of_nat(v___x_828_);
v___x_843_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_778_, v_mvarId_779_, v_vs_823_, v___x_841_, v___x_842_, v___x_829_, v___y_783_, v___y_784_, v___y_785_, v___y_786_);
lean_dec_ref(v_vs_823_);
return v___x_843_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___boxed(lean_object* v_fvarId_845_, lean_object* v_mvarId_846_, lean_object* v_x_847_, lean_object* v_x_848_, lean_object* v_x_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
size_t v_x_9503__boxed_855_; size_t v_x_9504__boxed_856_; lean_object* v_res_857_; 
v_x_9503__boxed_855_ = lean_unbox_usize(v_x_848_);
lean_dec(v_x_848_);
v_x_9504__boxed_856_ = lean_unbox_usize(v_x_849_);
lean_dec(v_x_849_);
v_res_857_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4(v_fvarId_845_, v_mvarId_846_, v_x_847_, v_x_9503__boxed_855_, v_x_9504__boxed_856_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1(lean_object* v_fvarId_858_, lean_object* v_mvarId_859_, lean_object* v_t_860_, lean_object* v_start_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v___x_867_; uint8_t v___x_868_; 
v___x_867_ = lean_unsigned_to_nat(0u);
v___x_868_ = lean_nat_dec_eq(v_start_861_, v___x_867_);
if (v___x_868_ == 0)
{
lean_object* v_root_869_; lean_object* v_tail_870_; size_t v_shift_871_; lean_object* v_tailOff_872_; uint8_t v___x_873_; 
v_root_869_ = lean_ctor_get(v_t_860_, 0);
lean_inc_ref(v_root_869_);
v_tail_870_ = lean_ctor_get(v_t_860_, 1);
lean_inc_ref(v_tail_870_);
v_shift_871_ = lean_ctor_get_usize(v_t_860_, 4);
v_tailOff_872_ = lean_ctor_get(v_t_860_, 3);
lean_inc(v_tailOff_872_);
lean_dec_ref(v_t_860_);
v___x_873_ = lean_nat_dec_le(v_tailOff_872_, v_start_861_);
if (v___x_873_ == 0)
{
size_t v___x_874_; lean_object* v___x_875_; 
lean_dec(v_tailOff_872_);
v___x_874_ = lean_usize_of_nat(v_start_861_);
lean_inc(v_mvarId_859_);
lean_inc(v_fvarId_858_);
v___x_875_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4(v_fvarId_858_, v_mvarId_859_, v_root_869_, v___x_874_, v_shift_871_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
if (lean_obj_tag(v___x_875_) == 0)
{
lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_895_; 
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_895_ == 0)
{
lean_object* v_unused_896_; 
v_unused_896_ = lean_ctor_get(v___x_875_, 0);
lean_dec(v_unused_896_);
v___x_877_ = v___x_875_;
v_isShared_878_ = v_isSharedCheck_895_;
goto v_resetjp_876_;
}
else
{
lean_dec(v___x_875_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_895_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_879_; lean_object* v___x_880_; uint8_t v___x_881_; 
v___x_879_ = lean_array_get_size(v_tail_870_);
v___x_880_ = lean_box(0);
v___x_881_ = lean_nat_dec_lt(v___x_867_, v___x_879_);
if (v___x_881_ == 0)
{
lean_object* v___x_883_; 
lean_dec_ref(v_tail_870_);
lean_dec(v_mvarId_859_);
lean_dec(v_fvarId_858_);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 0, v___x_880_);
v___x_883_ = v___x_877_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_880_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
else
{
uint8_t v___x_885_; 
v___x_885_ = lean_nat_dec_le(v___x_879_, v___x_879_);
if (v___x_885_ == 0)
{
if (v___x_881_ == 0)
{
lean_object* v___x_887_; 
lean_dec_ref(v_tail_870_);
lean_dec(v_mvarId_859_);
lean_dec(v_fvarId_858_);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 0, v___x_880_);
v___x_887_ = v___x_877_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_880_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
else
{
size_t v___x_889_; size_t v___x_890_; lean_object* v___x_891_; 
lean_del_object(v___x_877_);
v___x_889_ = ((size_t)0ULL);
v___x_890_ = lean_usize_of_nat(v___x_879_);
v___x_891_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_858_, v_mvarId_859_, v_tail_870_, v___x_889_, v___x_890_, v___x_880_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
lean_dec_ref(v_tail_870_);
return v___x_891_;
}
}
else
{
size_t v___x_892_; size_t v___x_893_; lean_object* v___x_894_; 
lean_del_object(v___x_877_);
v___x_892_ = ((size_t)0ULL);
v___x_893_ = lean_usize_of_nat(v___x_879_);
v___x_894_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_858_, v_mvarId_859_, v_tail_870_, v___x_892_, v___x_893_, v___x_880_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
lean_dec_ref(v_tail_870_);
return v___x_894_;
}
}
}
}
else
{
lean_dec_ref(v_tail_870_);
lean_dec(v_mvarId_859_);
lean_dec(v_fvarId_858_);
return v___x_875_;
}
}
else
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; uint8_t v___x_900_; 
lean_dec_ref(v_root_869_);
v___x_897_ = lean_nat_sub(v_start_861_, v_tailOff_872_);
lean_dec(v_tailOff_872_);
v___x_898_ = lean_array_get_size(v_tail_870_);
v___x_899_ = lean_box(0);
v___x_900_ = lean_nat_dec_lt(v___x_897_, v___x_898_);
if (v___x_900_ == 0)
{
lean_object* v___x_901_; 
lean_dec(v___x_897_);
lean_dec_ref(v_tail_870_);
lean_dec(v_mvarId_859_);
lean_dec(v_fvarId_858_);
v___x_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_901_, 0, v___x_899_);
return v___x_901_;
}
else
{
uint8_t v___x_902_; 
v___x_902_ = lean_nat_dec_le(v___x_898_, v___x_898_);
if (v___x_902_ == 0)
{
if (v___x_900_ == 0)
{
lean_object* v___x_903_; 
lean_dec(v___x_897_);
lean_dec_ref(v_tail_870_);
lean_dec(v_mvarId_859_);
lean_dec(v_fvarId_858_);
v___x_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_903_, 0, v___x_899_);
return v___x_903_;
}
else
{
size_t v___x_904_; size_t v___x_905_; lean_object* v___x_906_; 
v___x_904_ = lean_usize_of_nat(v___x_897_);
lean_dec(v___x_897_);
v___x_905_ = lean_usize_of_nat(v___x_898_);
v___x_906_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_858_, v_mvarId_859_, v_tail_870_, v___x_904_, v___x_905_, v___x_899_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
lean_dec_ref(v_tail_870_);
return v___x_906_;
}
}
else
{
size_t v___x_907_; size_t v___x_908_; lean_object* v___x_909_; 
v___x_907_ = lean_usize_of_nat(v___x_897_);
lean_dec(v___x_897_);
v___x_908_ = lean_usize_of_nat(v___x_898_);
v___x_909_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_858_, v_mvarId_859_, v_tail_870_, v___x_907_, v___x_908_, v___x_899_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
lean_dec_ref(v_tail_870_);
return v___x_909_;
}
}
}
}
else
{
lean_object* v___x_910_; 
v___x_910_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6(v_fvarId_858_, v_mvarId_859_, v_t_860_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
return v___x_910_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1___boxed(lean_object* v_fvarId_911_, lean_object* v_mvarId_912_, lean_object* v_t_913_, lean_object* v_start_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1(v_fvarId_911_, v_mvarId_912_, v_t_913_, v_start_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v_start_914_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1(lean_object* v_fvarId_921_, lean_object* v_mvarId_922_, lean_object* v_lctx_923_, lean_object* v_start_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
lean_object* v_decls_930_; lean_object* v___x_931_; 
v_decls_930_ = lean_ctor_get(v_lctx_923_, 1);
lean_inc_ref(v_decls_930_);
lean_dec_ref(v_lctx_923_);
v___x_931_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1(v_fvarId_921_, v_mvarId_922_, v_decls_930_, v_start_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1___boxed(lean_object* v_fvarId_932_, lean_object* v_mvarId_933_, lean_object* v_lctx_934_, lean_object* v_start_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1(v_fvarId_932_, v_mvarId_933_, v_lctx_934_, v_start_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v_start_935_);
return v_res_941_;
}
}
static lean_object* _init_l_Lean_MVarId_clear___lam__1___closed__1(void){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_943_ = ((lean_object*)(l_Lean_MVarId_clear___lam__1___closed__0));
v___x_944_ = l_Lean_stringToMessageData(v___x_943_);
return v___x_944_;
}
}
static lean_object* _init_l_Lean_MVarId_clear___lam__1___closed__3(void){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_946_ = ((lean_object*)(l_Lean_MVarId_clear___lam__1___closed__2));
v___x_947_ = l_Lean_stringToMessageData(v___x_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clear___lam__1(lean_object* v_mvarId_948_, lean_object* v___x_949_, lean_object* v_fvarId_950_, lean_object* v___f_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v___y_958_; lean_object* v___y_959_; lean_object* v___y_960_; lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v___x_988_; 
lean_inc(v___x_949_);
lean_inc(v_mvarId_948_);
v___x_988_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_948_, v___x_949_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v_lctx_989_; lean_object* v___y_991_; lean_object* v___y_992_; lean_object* v___y_993_; lean_object* v___y_994_; lean_object* v___y_995_; lean_object* v___y_996_; lean_object* v___y_997_; lean_object* v___y_1004_; lean_object* v___y_1005_; lean_object* v___y_1006_; lean_object* v___y_1007_; uint8_t v___x_1064_; 
lean_dec_ref_known(v___x_988_, 1);
v_lctx_989_ = lean_ctor_get(v___y_952_, 2);
lean_inc_ref(v_lctx_989_);
v___x_1064_ = l_Lean_LocalContext_contains(v_lctx_989_, v_fvarId_950_);
if (v___x_1064_ == 0)
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1065_ = lean_obj_once(&l_Lean_MVarId_clear___lam__1___closed__3, &l_Lean_MVarId_clear___lam__1___closed__3_once, _init_l_Lean_MVarId_clear___lam__1___closed__3);
lean_inc(v_fvarId_950_);
v___x_1066_ = l_Lean_mkFVar(v_fvarId_950_);
v___x_1067_ = l_Lean_MessageData_ofExpr(v___x_1066_);
v___x_1068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1065_);
lean_ctor_set(v___x_1068_, 1, v___x_1067_);
v___x_1069_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7);
v___x_1070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1068_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
v___x_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
lean_inc(v_mvarId_948_);
lean_inc(v___x_949_);
v___x_1072_ = l_Lean_Meta_throwTacticEx___redArg(v___x_949_, v_mvarId_948_, v___x_1071_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_dec_ref_known(v___x_1072_, 1);
v___y_1004_ = v___y_952_;
v___y_1005_ = v___y_953_;
v___y_1006_ = v___y_954_;
v___y_1007_ = v___y_955_;
goto v___jp_1003_;
}
else
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1080_; 
lean_dec_ref(v_lctx_989_);
lean_dec_ref(v___y_952_);
lean_dec_ref(v___f_951_);
lean_dec(v_fvarId_950_);
lean_dec(v___x_949_);
lean_dec(v_mvarId_948_);
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
else
{
v___y_1004_ = v___y_952_;
v___y_1005_ = v___y_953_;
v___y_1006_ = v___y_954_;
v___y_1007_ = v___y_955_;
goto v___jp_1003_;
}
v___jp_990_:
{
lean_object* v_localInstances_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v_localInstances_998_ = lean_ctor_get(v___y_994_, 3);
v___x_999_ = lean_local_ctx_erase(v_lctx_989_, v_fvarId_950_);
lean_inc(v___y_991_);
v___x_1000_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_951_, v_localInstances_998_, v___y_991_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_inc_ref(v_localInstances_998_);
v___y_958_ = v___y_995_;
v___y_959_ = v___y_994_;
v___y_960_ = v___y_991_;
v___y_961_ = v___y_992_;
v___y_962_ = v___x_999_;
v___y_963_ = v___y_993_;
v___y_964_ = v___y_996_;
v___y_965_ = v___y_997_;
v___y_966_ = v_localInstances_998_;
goto v___jp_957_;
}
else
{
lean_object* v_val_1001_; lean_object* v___x_1002_; 
v_val_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_val_1001_);
lean_dec_ref_known(v___x_1000_, 1);
lean_inc_ref(v_localInstances_998_);
v___x_1002_ = l_Array_eraseIdx___redArg(v_localInstances_998_, v_val_1001_);
v___y_958_ = v___y_995_;
v___y_959_ = v___y_994_;
v___y_960_ = v___y_991_;
v___y_961_ = v___y_992_;
v___y_962_ = v___x_999_;
v___y_963_ = v___y_993_;
v___y_964_ = v___y_996_;
v___y_965_ = v___y_997_;
v___y_966_ = v___x_1002_;
goto v___jp_957_;
}
}
v___jp_1003_:
{
lean_object* v___x_1008_; 
lean_inc(v_mvarId_948_);
v___x_1008_ = l_Lean_MVarId_getTag(v_mvarId_948_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc(v_a_1009_);
lean_dec_ref_known(v___x_1008_, 1);
v___x_1010_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_lctx_989_);
lean_inc(v_mvarId_948_);
lean_inc(v_fvarId_950_);
v___x_1011_ = l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1(v_fvarId_950_, v_mvarId_948_, v_lctx_989_, v___x_1010_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v___x_1012_; 
lean_dec_ref_known(v___x_1011_, 1);
lean_inc(v_mvarId_948_);
v___x_1012_ = l_Lean_MVarId_getDecl(v_mvarId_948_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v_a_1013_; lean_object* v_type_1014_; lean_object* v___x_1015_; lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1039_; 
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_a_1013_);
lean_dec_ref_known(v___x_1012_, 1);
v_type_1014_ = lean_ctor_get(v_a_1013_, 2);
lean_inc_ref_n(v_type_1014_, 2);
lean_dec(v_a_1013_);
lean_inc(v_fvarId_950_);
v___x_1015_ = l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3___redArg(v_type_1014_, v_fvarId_950_, v___y_1005_);
v_a_1016_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1018_ = v___x_1015_;
v_isShared_1019_ = v_isSharedCheck_1039_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___x_1015_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1039_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
uint8_t v___x_1020_; 
v___x_1020_ = lean_unbox(v_a_1016_);
lean_dec(v_a_1016_);
if (v___x_1020_ == 0)
{
lean_del_object(v___x_1018_);
lean_dec(v___x_949_);
v___y_991_ = v___x_1010_;
v___y_992_ = v_a_1009_;
v___y_993_ = v_type_1014_;
v___y_994_ = v___y_1004_;
v___y_995_ = v___y_1005_;
v___y_996_ = v___y_1006_;
v___y_997_ = v___y_1007_;
goto v___jp_990_;
}
else
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1028_; 
v___x_1021_ = lean_obj_once(&l_Lean_MVarId_clear___lam__1___closed__1, &l_Lean_MVarId_clear___lam__1___closed__1_once, _init_l_Lean_MVarId_clear___lam__1___closed__1);
lean_inc(v_fvarId_950_);
v___x_1022_ = l_Lean_mkFVar(v_fvarId_950_);
v___x_1023_ = l_Lean_MessageData_ofExpr(v___x_1022_);
v___x_1024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1021_);
lean_ctor_set(v___x_1024_, 1, v___x_1023_);
v___x_1025_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7);
v___x_1026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1024_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
if (v_isShared_1019_ == 0)
{
lean_ctor_set_tag(v___x_1018_, 1);
lean_ctor_set(v___x_1018_, 0, v___x_1026_);
v___x_1028_ = v___x_1018_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1026_);
v___x_1028_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
lean_object* v___x_1029_; 
lean_inc(v_mvarId_948_);
v___x_1029_ = l_Lean_Meta_throwTacticEx___redArg(v___x_949_, v_mvarId_948_, v___x_1028_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_dec_ref_known(v___x_1029_, 1);
v___y_991_ = v___x_1010_;
v___y_992_ = v_a_1009_;
v___y_993_ = v_type_1014_;
v___y_994_ = v___y_1004_;
v___y_995_ = v___y_1005_;
v___y_996_ = v___y_1006_;
v___y_997_ = v___y_1007_;
goto v___jp_990_;
}
else
{
lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1037_; 
lean_dec_ref(v_type_1014_);
lean_dec(v_a_1009_);
lean_dec_ref(v___y_1004_);
lean_dec_ref(v_lctx_989_);
lean_dec_ref(v___f_951_);
lean_dec(v_fvarId_950_);
lean_dec(v_mvarId_948_);
v_a_1030_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1032_ = v___x_1029_;
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v___x_1029_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1035_; 
if (v_isShared_1033_ == 0)
{
v___x_1035_ = v___x_1032_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_a_1030_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1047_; 
lean_dec(v_a_1009_);
lean_dec_ref(v___y_1004_);
lean_dec_ref(v_lctx_989_);
lean_dec_ref(v___f_951_);
lean_dec(v_fvarId_950_);
lean_dec(v___x_949_);
lean_dec(v_mvarId_948_);
v_a_1040_ = lean_ctor_get(v___x_1012_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1042_ = v___x_1012_;
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___x_1012_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1045_; 
if (v_isShared_1043_ == 0)
{
v___x_1045_ = v___x_1042_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_a_1040_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
}
}
else
{
lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1055_; 
lean_dec(v_a_1009_);
lean_dec_ref(v___y_1004_);
lean_dec_ref(v_lctx_989_);
lean_dec_ref(v___f_951_);
lean_dec(v_fvarId_950_);
lean_dec(v___x_949_);
lean_dec(v_mvarId_948_);
v_a_1048_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1050_ = v___x_1011_;
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_dec(v___x_1011_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1053_; 
if (v_isShared_1051_ == 0)
{
v___x_1053_ = v___x_1050_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_a_1048_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
else
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
lean_dec_ref(v___y_1004_);
lean_dec_ref(v_lctx_989_);
lean_dec_ref(v___f_951_);
lean_dec(v_fvarId_950_);
lean_dec(v___x_949_);
lean_dec(v_mvarId_948_);
v_a_1056_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1008_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1008_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
}
else
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1088_; 
lean_dec_ref(v___y_952_);
lean_dec_ref(v___f_951_);
lean_dec(v_fvarId_950_);
lean_dec(v___x_949_);
lean_dec(v_mvarId_948_);
v_a_1081_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1083_ = v___x_988_;
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_988_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1086_; 
if (v_isShared_1084_ == 0)
{
v___x_1086_ = v___x_1083_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1081_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
v___jp_957_:
{
uint8_t v___x_967_; lean_object* v___x_968_; 
v___x_967_ = 2;
v___x_968_ = l_Lean_Meta_mkFreshExprMVarAt(v___y_962_, v___y_966_, v___y_963_, v___x_967_, v___y_961_, v___y_960_, v___y_959_, v___y_958_, v___y_964_, v___y_965_);
lean_dec_ref(v___y_959_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_a_969_; lean_object* v___x_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_978_; 
v_a_969_ = lean_ctor_get(v___x_968_, 0);
lean_inc_n(v_a_969_, 2);
lean_dec_ref_known(v___x_968_, 1);
v___x_970_ = l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg(v_mvarId_948_, v_a_969_, v___y_958_);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_978_ == 0)
{
lean_object* v_unused_979_; 
v_unused_979_ = lean_ctor_get(v___x_970_, 0);
lean_dec(v_unused_979_);
v___x_972_ = v___x_970_;
v_isShared_973_ = v_isSharedCheck_978_;
goto v_resetjp_971_;
}
else
{
lean_dec(v___x_970_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_978_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_974_; lean_object* v___x_976_; 
v___x_974_ = l_Lean_Expr_mvarId_x21(v_a_969_);
lean_dec(v_a_969_);
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 0, v___x_974_);
v___x_976_ = v___x_972_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_974_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
else
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_987_; 
lean_dec(v_mvarId_948_);
v_a_980_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_987_ == 0)
{
v___x_982_ = v___x_968_;
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_968_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_983_ == 0)
{
v___x_985_ = v___x_982_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_a_980_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clear___lam__1___boxed(lean_object* v_mvarId_1089_, lean_object* v___x_1090_, lean_object* v_fvarId_1091_, lean_object* v___f_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l_Lean_MVarId_clear___lam__1(v_mvarId_1089_, v___x_1090_, v_fvarId_1091_, v___f_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec(v___y_1094_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clear(lean_object* v_mvarId_1099_, lean_object* v_fvarId_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_){
_start:
{
lean_object* v___f_1106_; lean_object* v___x_1107_; lean_object* v___f_1108_; lean_object* v___x_1109_; 
lean_inc(v_fvarId_1100_);
v___f_1106_ = lean_alloc_closure((void*)(l_Lean_MVarId_clear___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1106_, 0, v_fvarId_1100_);
v___x_1107_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__1));
lean_inc(v_mvarId_1099_);
v___f_1108_ = lean_alloc_closure((void*)(l_Lean_MVarId_clear___lam__1___boxed), 9, 4);
lean_closure_set(v___f_1108_, 0, v_mvarId_1099_);
lean_closure_set(v___f_1108_, 1, v___x_1107_);
lean_closure_set(v___f_1108_, 2, v_fvarId_1100_);
lean_closure_set(v___f_1108_, 3, v___f_1106_);
v___x_1109_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg(v_mvarId_1099_, v___f_1108_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clear___boxed(lean_object* v_mvarId_1110_, lean_object* v_fvarId_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Lean_MVarId_clear(v_mvarId_1110_, v_fvarId_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_);
lean_dec(v_a_1115_);
lean_dec_ref(v_a_1114_);
lean_dec(v_a_1113_);
lean_dec_ref(v_a_1112_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2(lean_object* v_mvarId_1118_, lean_object* v_val_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v___x_1125_; 
v___x_1125_ = l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg(v_mvarId_1118_, v_val_1119_, v___y_1121_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___boxed(lean_object* v_mvarId_1126_, lean_object* v_val_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2(v_mvarId_1126_, v_val_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3(lean_object* v_00_u03b2_1134_, lean_object* v_x_1135_, lean_object* v_x_1136_, lean_object* v_x_1137_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3___redArg(v_x_1135_, v_x_1136_, v_x_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9(lean_object* v_00_u03b2_1139_, lean_object* v_x_1140_, size_t v_x_1141_, size_t v_x_1142_, lean_object* v_x_1143_, lean_object* v_x_1144_){
_start:
{
lean_object* v___x_1145_; 
v___x_1145_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_x_1140_, v_x_1141_, v_x_1142_, v_x_1143_, v_x_1144_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___boxed(lean_object* v_00_u03b2_1146_, lean_object* v_x_1147_, lean_object* v_x_1148_, lean_object* v_x_1149_, lean_object* v_x_1150_, lean_object* v_x_1151_){
_start:
{
size_t v_x_10105__boxed_1152_; size_t v_x_10106__boxed_1153_; lean_object* v_res_1154_; 
v_x_10105__boxed_1152_ = lean_unbox_usize(v_x_1148_);
lean_dec(v_x_1148_);
v_x_10106__boxed_1153_ = lean_unbox_usize(v_x_1149_);
lean_dec(v_x_1149_);
v_res_1154_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9(v_00_u03b2_1146_, v_x_1147_, v_x_10105__boxed_1152_, v_x_10106__boxed_1153_, v_x_1150_, v_x_1151_);
return v_res_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13(lean_object* v_00_u03b2_1155_, lean_object* v_n_1156_, lean_object* v_k_1157_, lean_object* v_v_1158_){
_start:
{
lean_object* v___x_1159_; 
v___x_1159_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13___redArg(v_n_1156_, v_k_1157_, v_v_1158_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14(lean_object* v_00_u03b2_1160_, size_t v_depth_1161_, lean_object* v_keys_1162_, lean_object* v_vals_1163_, lean_object* v_heq_1164_, lean_object* v_i_1165_, lean_object* v_entries_1166_){
_start:
{
lean_object* v___x_1167_; 
v___x_1167_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg(v_depth_1161_, v_keys_1162_, v_vals_1163_, v_i_1165_, v_entries_1166_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___boxed(lean_object* v_00_u03b2_1168_, lean_object* v_depth_1169_, lean_object* v_keys_1170_, lean_object* v_vals_1171_, lean_object* v_heq_1172_, lean_object* v_i_1173_, lean_object* v_entries_1174_){
_start:
{
size_t v_depth_boxed_1175_; lean_object* v_res_1176_; 
v_depth_boxed_1175_ = lean_unbox_usize(v_depth_1169_);
lean_dec(v_depth_1169_);
v_res_1176_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14(v_00_u03b2_1168_, v_depth_boxed_1175_, v_keys_1170_, v_vals_1171_, v_heq_1172_, v_i_1173_, v_entries_1174_);
lean_dec_ref(v_vals_1171_);
lean_dec_ref(v_keys_1170_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13_spec__14(lean_object* v_00_u03b2_1177_, lean_object* v_x_1178_, lean_object* v_x_1179_, lean_object* v_x_1180_, lean_object* v_x_1181_){
_start:
{
lean_object* v___x_1182_; 
v___x_1182_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13_spec__14___redArg(v_x_1178_, v_x_1179_, v_x_1180_, v_x_1181_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClear(lean_object* v_mvarId_1183_, lean_object* v_fvarId_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_){
_start:
{
lean_object* v___x_1190_; 
v___x_1190_ = l_Lean_Meta_saveState___redArg(v_a_1186_, v_a_1188_);
if (lean_obj_tag(v___x_1190_) == 0)
{
lean_object* v_a_1191_; lean_object* v___x_1192_; 
v_a_1191_ = lean_ctor_get(v___x_1190_, 0);
lean_inc(v_a_1191_);
lean_dec_ref_known(v___x_1190_, 1);
lean_inc(v_mvarId_1183_);
v___x_1192_ = l_Lean_MVarId_clear(v_mvarId_1183_, v_fvarId_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_dec(v_a_1191_);
lean_dec(v_mvarId_1183_);
return v___x_1192_;
}
else
{
lean_object* v_a_1193_; uint8_t v___y_1195_; uint8_t v___x_1213_; 
v_a_1193_ = lean_ctor_get(v___x_1192_, 0);
lean_inc(v_a_1193_);
v___x_1213_ = l_Lean_Exception_isInterrupt(v_a_1193_);
if (v___x_1213_ == 0)
{
uint8_t v___x_1214_; 
v___x_1214_ = l_Lean_Exception_isRuntime(v_a_1193_);
v___y_1195_ = v___x_1214_;
goto v___jp_1194_;
}
else
{
lean_dec(v_a_1193_);
v___y_1195_ = v___x_1213_;
goto v___jp_1194_;
}
v___jp_1194_:
{
if (v___y_1195_ == 0)
{
lean_object* v___x_1196_; 
lean_dec_ref_known(v___x_1192_, 1);
v___x_1196_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1191_, v_a_1186_, v_a_1188_);
lean_dec(v_a_1191_);
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1203_ == 0)
{
lean_object* v_unused_1204_; 
v_unused_1204_ = lean_ctor_get(v___x_1196_, 0);
lean_dec(v_unused_1204_);
v___x_1198_ = v___x_1196_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_dec(v___x_1196_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1201_; 
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 0, v_mvarId_1183_);
v___x_1201_ = v___x_1198_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_mvarId_1183_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
else
{
lean_object* v_a_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1212_; 
lean_dec(v_mvarId_1183_);
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
else
{
lean_dec(v_a_1191_);
lean_dec(v_mvarId_1183_);
return v___x_1192_;
}
}
}
}
else
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1222_; 
lean_dec(v_fvarId_1184_);
lean_dec(v_mvarId_1183_);
v_a_1215_ = lean_ctor_get(v___x_1190_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1217_ = v___x_1190_;
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_1190_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1218_ == 0)
{
v___x_1220_ = v___x_1217_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_a_1215_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClear___boxed(lean_object* v_mvarId_1223_, lean_object* v_fvarId_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Lean_MVarId_tryClear(v_mvarId_1223_, v_fvarId_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_);
lean_dec(v_a_1228_);
lean_dec_ref(v_a_1227_);
lean_dec(v_a_1226_);
lean_dec_ref(v_a_1225_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0(lean_object* v_as_1231_, size_t v_i_1232_, size_t v_stop_1233_, lean_object* v_b_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
uint8_t v___x_1240_; 
v___x_1240_ = lean_usize_dec_eq(v_i_1232_, v_stop_1233_);
if (v___x_1240_ == 0)
{
size_t v___x_1241_; size_t v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1241_ = ((size_t)1ULL);
v___x_1242_ = lean_usize_sub(v_i_1232_, v___x_1241_);
v___x_1243_ = lean_array_uget_borrowed(v_as_1231_, v___x_1242_);
lean_inc(v___x_1243_);
v___x_1244_ = l_Lean_MVarId_tryClear(v_b_1234_, v___x_1243_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v_a_1245_; 
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_a_1245_);
lean_dec_ref_known(v___x_1244_, 1);
v_i_1232_ = v___x_1242_;
v_b_1234_ = v_a_1245_;
goto _start;
}
else
{
return v___x_1244_;
}
}
else
{
lean_object* v___x_1247_; 
v___x_1247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1247_, 0, v_b_1234_);
return v___x_1247_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0___boxed(lean_object* v_as_1248_, lean_object* v_i_1249_, lean_object* v_stop_1250_, lean_object* v_b_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
size_t v_i_boxed_1257_; size_t v_stop_boxed_1258_; lean_object* v_res_1259_; 
v_i_boxed_1257_ = lean_unbox_usize(v_i_1249_);
lean_dec(v_i_1249_);
v_stop_boxed_1258_ = lean_unbox_usize(v_stop_1250_);
lean_dec(v_stop_1250_);
v_res_1259_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0(v_as_1248_, v_i_boxed_1257_, v_stop_boxed_1258_, v_b_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec_ref(v_as_1248_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany(lean_object* v_mvarId_1260_, lean_object* v_fvarIds_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_){
_start:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; uint8_t v___x_1269_; 
v___x_1267_ = lean_array_get_size(v_fvarIds_1261_);
v___x_1268_ = lean_unsigned_to_nat(0u);
v___x_1269_ = lean_nat_dec_lt(v___x_1268_, v___x_1267_);
if (v___x_1269_ == 0)
{
lean_object* v___x_1270_; 
v___x_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1270_, 0, v_mvarId_1260_);
return v___x_1270_;
}
else
{
size_t v___x_1271_; size_t v___x_1272_; lean_object* v___x_1273_; 
v___x_1271_ = lean_usize_of_nat(v___x_1267_);
v___x_1272_ = ((size_t)0ULL);
v___x_1273_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0(v_fvarIds_1261_, v___x_1271_, v___x_1272_, v_mvarId_1260_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_);
return v___x_1273_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany___boxed(lean_object* v_mvarId_1274_, lean_object* v_fvarIds_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Lean_MVarId_tryClearMany(v_mvarId_1274_, v_fvarIds_1275_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_);
lean_dec(v_a_1279_);
lean_dec_ref(v_a_1278_);
lean_dec(v_a_1277_);
lean_dec_ref(v_a_1276_);
lean_dec_ref(v_fvarIds_1275_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0(lean_object* v_as_1282_, size_t v_i_1283_, size_t v_stop_1284_, lean_object* v_b_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
uint8_t v___x_1291_; 
v___x_1291_ = lean_usize_dec_eq(v_i_1283_, v_stop_1284_);
if (v___x_1291_ == 0)
{
lean_object* v_fst_1292_; lean_object* v_snd_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1318_; 
v_fst_1292_ = lean_ctor_get(v_b_1285_, 0);
v_snd_1293_ = lean_ctor_get(v_b_1285_, 1);
v_isSharedCheck_1318_ = !lean_is_exclusive(v_b_1285_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1295_ = v_b_1285_;
v_isShared_1296_ = v_isSharedCheck_1318_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_snd_1293_);
lean_inc(v_fst_1292_);
lean_dec(v_b_1285_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1318_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
size_t v___x_1297_; size_t v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1297_ = ((size_t)1ULL);
v___x_1298_ = lean_usize_sub(v_i_1283_, v___x_1297_);
v___x_1299_ = lean_array_uget_borrowed(v_as_1282_, v___x_1298_);
lean_inc(v___x_1299_);
lean_inc(v_fst_1292_);
v___x_1300_ = l_Lean_MVarId_tryClear(v_fst_1292_, v___x_1299_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
if (lean_obj_tag(v___x_1300_) == 0)
{
lean_object* v_a_1301_; lean_object* v___y_1303_; uint8_t v___x_1308_; 
v_a_1301_ = lean_ctor_get(v___x_1300_, 0);
lean_inc(v_a_1301_);
lean_dec_ref_known(v___x_1300_, 1);
v___x_1308_ = l_Lean_instBEqMVarId_beq(v_fst_1292_, v_a_1301_);
lean_dec(v_fst_1292_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; 
lean_inc(v___x_1299_);
v___x_1309_ = lean_array_push(v_snd_1293_, v___x_1299_);
v___y_1303_ = v___x_1309_;
goto v___jp_1302_;
}
else
{
v___y_1303_ = v_snd_1293_;
goto v___jp_1302_;
}
v___jp_1302_:
{
lean_object* v___x_1305_; 
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 1, v___y_1303_);
lean_ctor_set(v___x_1295_, 0, v_a_1301_);
v___x_1305_ = v___x_1295_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_a_1301_);
lean_ctor_set(v_reuseFailAlloc_1307_, 1, v___y_1303_);
v___x_1305_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
v_i_1283_ = v___x_1298_;
v_b_1285_ = v___x_1305_;
goto _start;
}
}
}
else
{
lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1317_; 
lean_del_object(v___x_1295_);
lean_dec(v_snd_1293_);
lean_dec(v_fst_1292_);
v_a_1310_ = lean_ctor_get(v___x_1300_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1312_ = v___x_1300_;
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_dec(v___x_1300_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1315_; 
if (v_isShared_1313_ == 0)
{
v___x_1315_ = v___x_1312_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_a_1310_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
}
}
else
{
lean_object* v___x_1319_; 
v___x_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1319_, 0, v_b_1285_);
return v___x_1319_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0___boxed(lean_object* v_as_1320_, lean_object* v_i_1321_, lean_object* v_stop_1322_, lean_object* v_b_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
size_t v_i_boxed_1329_; size_t v_stop_boxed_1330_; lean_object* v_res_1331_; 
v_i_boxed_1329_ = lean_unbox_usize(v_i_1321_);
lean_dec(v_i_1321_);
v_stop_boxed_1330_ = lean_unbox_usize(v_stop_1322_);
lean_dec(v_stop_1322_);
v_res_1331_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0(v_as_1320_, v_i_boxed_1329_, v_stop_boxed_1330_, v_b_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec_ref(v_as_1320_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany_x27___lam__0(lean_object* v_fvarIds_1332_, lean_object* v_goal_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_){
_start:
{
lean_object* v_lctx_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; uint8_t v___x_1345_; 
v_lctx_1339_ = lean_ctor_get(v___y_1334_, 2);
v___x_1340_ = l_Lean_LocalContext_sortFVarsByContextOrder(v_lctx_1339_, v_fvarIds_1332_);
v___x_1341_ = lean_array_get_size(v___x_1340_);
v___x_1342_ = lean_mk_empty_array_with_capacity(v___x_1341_);
v___x_1343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1343_, 0, v_goal_1333_);
lean_ctor_set(v___x_1343_, 1, v___x_1342_);
v___x_1344_ = lean_unsigned_to_nat(0u);
v___x_1345_ = lean_nat_dec_lt(v___x_1344_, v___x_1341_);
if (v___x_1345_ == 0)
{
lean_object* v___x_1346_; 
lean_dec_ref(v___x_1340_);
v___x_1346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1343_);
return v___x_1346_;
}
else
{
size_t v___x_1347_; size_t v___x_1348_; lean_object* v___x_1349_; 
v___x_1347_ = lean_usize_of_nat(v___x_1341_);
v___x_1348_ = ((size_t)0ULL);
v___x_1349_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0(v___x_1340_, v___x_1347_, v___x_1348_, v___x_1343_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
lean_dec_ref(v___x_1340_);
return v___x_1349_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany_x27___lam__0___boxed(lean_object* v_fvarIds_1350_, lean_object* v_goal_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l_Lean_MVarId_tryClearMany_x27___lam__0(v_fvarIds_1350_, v_goal_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany_x27(lean_object* v_goal_1358_, lean_object* v_fvarIds_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_){
_start:
{
lean_object* v___f_1365_; lean_object* v___x_1366_; 
lean_inc(v_goal_1358_);
v___f_1365_ = lean_alloc_closure((void*)(l_Lean_MVarId_tryClearMany_x27___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1365_, 0, v_fvarIds_1359_);
lean_closure_set(v___f_1365_, 1, v_goal_1358_);
v___x_1366_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg(v_goal_1358_, v___f_1365_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany_x27___boxed(lean_object* v_goal_1367_, lean_object* v_fvarIds_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l_Lean_MVarId_tryClearMany_x27(v_goal_1367_, v_fvarIds_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_);
lean_dec(v_a_1372_);
lean_dec_ref(v_a_1371_);
lean_dec(v_a_1370_);
lean_dec_ref(v_a_1369_);
return v_res_1374_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Util(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Lemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Clear(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Clear(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Order(uint8_t builtin);
lean_object* initialize_Init_Data_Order_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Clear(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Clear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Clear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Clear(builtin);
}
#ifdef __cplusplus
}
#endif
