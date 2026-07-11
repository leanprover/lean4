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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t lean_bool_not(uint8_t);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__0_value;
static lean_once_cell_t l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2;
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
LEAN_EXPORT uint8_t l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__0(lean_object* v_x_1_){
_start:
{
uint8_t v___x_2_; 
v___x_2_ = 0;
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__0___boxed(lean_object* v_x_3_){
_start:
{
uint8_t v_res_4_; lean_object* v_r_5_; 
v_res_4_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__0(v_x_3_);
lean_dec(v_x_3_);
v_r_5_ = lean_box(v_res_4_);
return v_r_5_;
}
}
LEAN_EXPORT uint8_t l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__1(lean_object* v_fvarId_6_, lean_object* v_x_7_){
_start:
{
uint8_t v___x_8_; 
v___x_8_ = l_Lean_instBEqFVarId_beq(v_fvarId_6_, v_x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__1___boxed(lean_object* v_fvarId_9_, lean_object* v_x_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__1(v_fvarId_9_, v_x_10_);
lean_dec(v_x_10_);
lean_dec(v_fvarId_9_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
static lean_object* _init_l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_14_ = lean_box(0);
v___x_15_ = lean_unsigned_to_nat(16u);
v___x_16_ = lean_mk_array(v___x_15_, v___x_14_);
return v___x_16_;
}
}
static lean_object* _init_l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_17_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__1, &l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__1_once, _init_l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__1);
v___x_18_ = lean_unsigned_to_nat(0u);
v___x_19_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_19_, 0, v___x_18_);
lean_ctor_set(v___x_19_, 1, v___x_17_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg(lean_object* v_localDecl_20_, lean_object* v_fvarId_21_, uint8_t v_generalizeNondepLet_22_, lean_object* v___y_23_){
_start:
{
uint8_t v_fst_26_; lean_object* v_snd_27_; lean_object* v___f_45_; lean_object* v___f_46_; 
v___f_45_ = ((lean_object*)(l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__0));
v___f_46_ = lean_alloc_closure((void*)(l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_46_, 0, v_fvarId_21_);
if (lean_obj_tag(v_localDecl_20_) == 0)
{
lean_object* v_type_47_; lean_object* v___x_48_; uint8_t v_fst_50_; lean_object* v_mctx_51_; lean_object* v_mctx_68_; lean_object* v___x_69_; lean_object* v___x_70_; uint8_t v___y_72_; uint8_t v___x_79_; uint8_t v___x_80_; 
v_type_47_ = lean_ctor_get(v_localDecl_20_, 3);
lean_inc_ref(v_type_47_);
lean_dec_ref_known(v_localDecl_20_, 4);
v___x_48_ = lean_st_ref_get(v___y_23_);
v_mctx_68_ = lean_ctor_get(v___x_48_, 0);
lean_inc_ref_n(v_mctx_68_, 2);
lean_dec(v___x_48_);
v___x_69_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2);
v___x_70_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
lean_ctor_set(v___x_70_, 1, v_mctx_68_);
v___x_79_ = l_Lean_Expr_hasFVar(v_type_47_);
v___x_80_ = lean_bool_not(v___x_79_);
if (v___x_80_ == 0)
{
v___y_72_ = v___x_80_;
goto v___jp_71_;
}
else
{
uint8_t v___x_81_; uint8_t v___x_82_; 
v___x_81_ = l_Lean_Expr_hasMVar(v_type_47_);
v___x_82_ = lean_bool_not(v___x_81_);
v___y_72_ = v___x_82_;
goto v___jp_71_;
}
v___jp_49_:
{
lean_object* v___x_52_; lean_object* v_cache_53_; lean_object* v_zetaDeltaFVarIds_54_; lean_object* v_postponed_55_; lean_object* v_diag_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_66_; 
v___x_52_ = lean_st_ref_take(v___y_23_);
v_cache_53_ = lean_ctor_get(v___x_52_, 1);
v_zetaDeltaFVarIds_54_ = lean_ctor_get(v___x_52_, 2);
v_postponed_55_ = lean_ctor_get(v___x_52_, 3);
v_diag_56_ = lean_ctor_get(v___x_52_, 4);
v_isSharedCheck_66_ = !lean_is_exclusive(v___x_52_);
if (v_isSharedCheck_66_ == 0)
{
lean_object* v_unused_67_; 
v_unused_67_ = lean_ctor_get(v___x_52_, 0);
lean_dec(v_unused_67_);
v___x_58_ = v___x_52_;
v_isShared_59_ = v_isSharedCheck_66_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_diag_56_);
lean_inc(v_postponed_55_);
lean_inc(v_zetaDeltaFVarIds_54_);
lean_inc(v_cache_53_);
lean_dec(v___x_52_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_66_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v___x_61_; 
if (v_isShared_59_ == 0)
{
lean_ctor_set(v___x_58_, 0, v_mctx_51_);
v___x_61_ = v___x_58_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v_mctx_51_);
lean_ctor_set(v_reuseFailAlloc_65_, 1, v_cache_53_);
lean_ctor_set(v_reuseFailAlloc_65_, 2, v_zetaDeltaFVarIds_54_);
lean_ctor_set(v_reuseFailAlloc_65_, 3, v_postponed_55_);
lean_ctor_set(v_reuseFailAlloc_65_, 4, v_diag_56_);
v___x_61_ = v_reuseFailAlloc_65_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_62_ = lean_st_ref_set(v___y_23_, v___x_61_);
v___x_63_ = lean_box(v_fst_50_);
v___x_64_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
return v___x_64_;
}
}
}
v___jp_71_:
{
if (v___y_72_ == 0)
{
lean_object* v___x_73_; lean_object* v_snd_74_; lean_object* v_fst_75_; lean_object* v_mctx_76_; uint8_t v___x_77_; 
lean_dec_ref(v_mctx_68_);
v___x_73_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_46_, v___f_45_, v_type_47_, v___x_70_);
v_snd_74_ = lean_ctor_get(v___x_73_, 1);
lean_inc(v_snd_74_);
v_fst_75_ = lean_ctor_get(v___x_73_, 0);
lean_inc(v_fst_75_);
lean_dec_ref(v___x_73_);
v_mctx_76_ = lean_ctor_get(v_snd_74_, 1);
lean_inc_ref(v_mctx_76_);
lean_dec(v_snd_74_);
v___x_77_ = lean_unbox(v_fst_75_);
lean_dec(v_fst_75_);
v_fst_50_ = v___x_77_;
v_mctx_51_ = v_mctx_76_;
goto v___jp_49_;
}
else
{
uint8_t v___x_78_; 
lean_dec_ref_known(v___x_70_, 2);
lean_dec_ref(v_type_47_);
lean_dec_ref(v___f_46_);
v___x_78_ = 0;
v_fst_50_ = v___x_78_;
v_mctx_51_ = v_mctx_68_;
goto v___jp_49_;
}
}
}
else
{
lean_object* v_type_83_; lean_object* v_value_84_; uint8_t v_nondep_85_; uint8_t v___y_87_; lean_object* v___y_88_; uint8_t v___y_89_; uint8_t v_fst_95_; lean_object* v_snd_96_; lean_object* v___y_102_; uint8_t v___y_103_; uint8_t v___y_104_; uint8_t v___y_113_; 
v_type_83_ = lean_ctor_get(v_localDecl_20_, 3);
lean_inc_ref(v_type_83_);
v_value_84_ = lean_ctor_get(v_localDecl_20_, 4);
lean_inc_ref(v_value_84_);
v_nondep_85_ = lean_ctor_get_uint8(v_localDecl_20_, sizeof(void*)*5);
lean_dec_ref_known(v_localDecl_20_, 5);
if (v_generalizeNondepLet_22_ == 0)
{
v___y_113_ = v_generalizeNondepLet_22_;
goto v___jp_112_;
}
else
{
if (v_nondep_85_ == 0)
{
v___y_113_ = v_nondep_85_;
goto v___jp_112_;
}
else
{
lean_object* v___x_122_; uint8_t v_fst_124_; lean_object* v_mctx_125_; lean_object* v_mctx_142_; lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v___y_146_; uint8_t v___x_153_; uint8_t v___x_154_; 
lean_dec_ref(v_value_84_);
v___x_122_ = lean_st_ref_get(v___y_23_);
v_mctx_142_ = lean_ctor_get(v___x_122_, 0);
lean_inc_ref_n(v_mctx_142_, 2);
lean_dec(v___x_122_);
v___x_143_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2);
v___x_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
lean_ctor_set(v___x_144_, 1, v_mctx_142_);
v___x_153_ = l_Lean_Expr_hasFVar(v_type_83_);
v___x_154_ = lean_bool_not(v___x_153_);
if (v___x_154_ == 0)
{
v___y_146_ = v___x_154_;
goto v___jp_145_;
}
else
{
uint8_t v___x_155_; uint8_t v___x_156_; 
v___x_155_ = l_Lean_Expr_hasMVar(v_type_83_);
v___x_156_ = lean_bool_not(v___x_155_);
v___y_146_ = v___x_156_;
goto v___jp_145_;
}
v___jp_123_:
{
lean_object* v___x_126_; lean_object* v_cache_127_; lean_object* v_zetaDeltaFVarIds_128_; lean_object* v_postponed_129_; lean_object* v_diag_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_140_; 
v___x_126_ = lean_st_ref_take(v___y_23_);
v_cache_127_ = lean_ctor_get(v___x_126_, 1);
v_zetaDeltaFVarIds_128_ = lean_ctor_get(v___x_126_, 2);
v_postponed_129_ = lean_ctor_get(v___x_126_, 3);
v_diag_130_ = lean_ctor_get(v___x_126_, 4);
v_isSharedCheck_140_ = !lean_is_exclusive(v___x_126_);
if (v_isSharedCheck_140_ == 0)
{
lean_object* v_unused_141_; 
v_unused_141_ = lean_ctor_get(v___x_126_, 0);
lean_dec(v_unused_141_);
v___x_132_ = v___x_126_;
v_isShared_133_ = v_isSharedCheck_140_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_diag_130_);
lean_inc(v_postponed_129_);
lean_inc(v_zetaDeltaFVarIds_128_);
lean_inc(v_cache_127_);
lean_dec(v___x_126_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_140_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_135_; 
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 0, v_mctx_125_);
v___x_135_ = v___x_132_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_mctx_125_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v_cache_127_);
lean_ctor_set(v_reuseFailAlloc_139_, 2, v_zetaDeltaFVarIds_128_);
lean_ctor_set(v_reuseFailAlloc_139_, 3, v_postponed_129_);
lean_ctor_set(v_reuseFailAlloc_139_, 4, v_diag_130_);
v___x_135_ = v_reuseFailAlloc_139_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_136_ = lean_st_ref_set(v___y_23_, v___x_135_);
v___x_137_ = lean_box(v_fst_124_);
v___x_138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
return v___x_138_;
}
}
}
v___jp_145_:
{
if (v___y_146_ == 0)
{
lean_object* v___x_147_; lean_object* v_snd_148_; lean_object* v_fst_149_; lean_object* v_mctx_150_; uint8_t v___x_151_; 
lean_dec_ref(v_mctx_142_);
v___x_147_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_46_, v___f_45_, v_type_83_, v___x_144_);
v_snd_148_ = lean_ctor_get(v___x_147_, 1);
lean_inc(v_snd_148_);
v_fst_149_ = lean_ctor_get(v___x_147_, 0);
lean_inc(v_fst_149_);
lean_dec_ref(v___x_147_);
v_mctx_150_ = lean_ctor_get(v_snd_148_, 1);
lean_inc_ref(v_mctx_150_);
lean_dec(v_snd_148_);
v___x_151_ = lean_unbox(v_fst_149_);
lean_dec(v_fst_149_);
v_fst_124_ = v___x_151_;
v_mctx_125_ = v_mctx_150_;
goto v___jp_123_;
}
else
{
uint8_t v___x_152_; 
lean_dec_ref_known(v___x_144_, 2);
lean_dec_ref(v_type_83_);
lean_dec_ref(v___f_46_);
v___x_152_ = 0;
v_fst_124_ = v___x_152_;
v_mctx_125_ = v_mctx_142_;
goto v___jp_123_;
}
}
}
}
v___jp_86_:
{
if (v___y_89_ == 0)
{
lean_object* v___x_90_; lean_object* v_fst_91_; lean_object* v_snd_92_; uint8_t v___x_93_; 
v___x_90_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_46_, v___f_45_, v_value_84_, v___y_88_);
v_fst_91_ = lean_ctor_get(v___x_90_, 0);
lean_inc(v_fst_91_);
v_snd_92_ = lean_ctor_get(v___x_90_, 1);
lean_inc(v_snd_92_);
lean_dec_ref(v___x_90_);
v___x_93_ = lean_unbox(v_fst_91_);
lean_dec(v_fst_91_);
v_fst_26_ = v___x_93_;
v_snd_27_ = v_snd_92_;
goto v___jp_25_;
}
else
{
lean_dec_ref(v_value_84_);
lean_dec_ref(v___f_46_);
v_fst_26_ = v___y_87_;
v_snd_27_ = v___y_88_;
goto v___jp_25_;
}
}
v___jp_94_:
{
uint8_t v___x_97_; uint8_t v___x_98_; 
v___x_97_ = l_Lean_Expr_hasFVar(v_value_84_);
v___x_98_ = lean_bool_not(v___x_97_);
if (v___x_98_ == 0)
{
v___y_87_ = v_fst_95_;
v___y_88_ = v_snd_96_;
v___y_89_ = v___x_98_;
goto v___jp_86_;
}
else
{
uint8_t v___x_99_; uint8_t v___x_100_; 
v___x_99_ = l_Lean_Expr_hasMVar(v_value_84_);
v___x_100_ = lean_bool_not(v___x_99_);
v___y_87_ = v_fst_95_;
v___y_88_ = v_snd_96_;
v___y_89_ = v___x_100_;
goto v___jp_86_;
}
}
v___jp_101_:
{
if (v___y_104_ == 0)
{
lean_object* v___x_105_; lean_object* v_fst_106_; uint8_t v___x_107_; 
lean_inc_ref(v___f_46_);
v___x_105_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_46_, v___f_45_, v_type_83_, v___y_102_);
v_fst_106_ = lean_ctor_get(v___x_105_, 0);
lean_inc(v_fst_106_);
v___x_107_ = lean_unbox(v_fst_106_);
if (v___x_107_ == 0)
{
lean_object* v_snd_108_; uint8_t v___x_109_; 
v_snd_108_ = lean_ctor_get(v___x_105_, 1);
lean_inc(v_snd_108_);
lean_dec_ref(v___x_105_);
v___x_109_ = lean_unbox(v_fst_106_);
lean_dec(v_fst_106_);
v_fst_95_ = v___x_109_;
v_snd_96_ = v_snd_108_;
goto v___jp_94_;
}
else
{
lean_object* v_snd_110_; uint8_t v___x_111_; 
lean_dec_ref(v_value_84_);
lean_dec_ref(v___f_46_);
v_snd_110_ = lean_ctor_get(v___x_105_, 1);
lean_inc(v_snd_110_);
lean_dec_ref(v___x_105_);
v___x_111_ = lean_unbox(v_fst_106_);
lean_dec(v_fst_106_);
v_fst_26_ = v___x_111_;
v_snd_27_ = v_snd_110_;
goto v___jp_25_;
}
}
else
{
lean_dec_ref(v_type_83_);
v_fst_95_ = v___y_103_;
v_snd_96_ = v___y_102_;
goto v___jp_94_;
}
}
v___jp_112_:
{
lean_object* v___x_114_; lean_object* v_mctx_115_; lean_object* v___x_116_; lean_object* v___x_117_; uint8_t v___x_118_; uint8_t v___x_119_; 
v___x_114_ = lean_st_ref_get(v___y_23_);
v_mctx_115_ = lean_ctor_get(v___x_114_, 0);
lean_inc_ref(v_mctx_115_);
lean_dec(v___x_114_);
v___x_116_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2);
v___x_117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
lean_ctor_set(v___x_117_, 1, v_mctx_115_);
v___x_118_ = l_Lean_Expr_hasFVar(v_type_83_);
v___x_119_ = lean_bool_not(v___x_118_);
if (v___x_119_ == 0)
{
v___y_102_ = v___x_117_;
v___y_103_ = v___y_113_;
v___y_104_ = v___x_119_;
goto v___jp_101_;
}
else
{
uint8_t v___x_120_; uint8_t v___x_121_; 
v___x_120_ = l_Lean_Expr_hasMVar(v_type_83_);
v___x_121_ = lean_bool_not(v___x_120_);
v___y_102_ = v___x_117_;
v___y_103_ = v___y_113_;
v___y_104_ = v___x_121_;
goto v___jp_101_;
}
}
}
v___jp_25_:
{
lean_object* v_mctx_28_; lean_object* v___x_29_; lean_object* v_cache_30_; lean_object* v_zetaDeltaFVarIds_31_; lean_object* v_postponed_32_; lean_object* v_diag_33_; lean_object* v___x_35_; uint8_t v_isShared_36_; uint8_t v_isSharedCheck_43_; 
v_mctx_28_ = lean_ctor_get(v_snd_27_, 1);
lean_inc_ref(v_mctx_28_);
lean_dec_ref(v_snd_27_);
v___x_29_ = lean_st_ref_take(v___y_23_);
v_cache_30_ = lean_ctor_get(v___x_29_, 1);
v_zetaDeltaFVarIds_31_ = lean_ctor_get(v___x_29_, 2);
v_postponed_32_ = lean_ctor_get(v___x_29_, 3);
v_diag_33_ = lean_ctor_get(v___x_29_, 4);
v_isSharedCheck_43_ = !lean_is_exclusive(v___x_29_);
if (v_isSharedCheck_43_ == 0)
{
lean_object* v_unused_44_; 
v_unused_44_ = lean_ctor_get(v___x_29_, 0);
lean_dec(v_unused_44_);
v___x_35_ = v___x_29_;
v_isShared_36_ = v_isSharedCheck_43_;
goto v_resetjp_34_;
}
else
{
lean_inc(v_diag_33_);
lean_inc(v_postponed_32_);
lean_inc(v_zetaDeltaFVarIds_31_);
lean_inc(v_cache_30_);
lean_dec(v___x_29_);
v___x_35_ = lean_box(0);
v_isShared_36_ = v_isSharedCheck_43_;
goto v_resetjp_34_;
}
v_resetjp_34_:
{
lean_object* v___x_38_; 
if (v_isShared_36_ == 0)
{
lean_ctor_set(v___x_35_, 0, v_mctx_28_);
v___x_38_ = v___x_35_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v_mctx_28_);
lean_ctor_set(v_reuseFailAlloc_42_, 1, v_cache_30_);
lean_ctor_set(v_reuseFailAlloc_42_, 2, v_zetaDeltaFVarIds_31_);
lean_ctor_set(v_reuseFailAlloc_42_, 3, v_postponed_32_);
lean_ctor_set(v_reuseFailAlloc_42_, 4, v_diag_33_);
v___x_38_ = v_reuseFailAlloc_42_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_39_ = lean_st_ref_set(v___y_23_, v___x_38_);
v___x_40_ = lean_box(v_fst_26_);
v___x_41_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_41_, 0, v___x_40_);
return v___x_41_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___boxed(lean_object* v_localDecl_157_, lean_object* v_fvarId_158_, lean_object* v_generalizeNondepLet_159_, lean_object* v___y_160_, lean_object* v___y_161_){
_start:
{
uint8_t v_generalizeNondepLet_boxed_162_; lean_object* v_res_163_; 
v_generalizeNondepLet_boxed_162_ = lean_unbox(v_generalizeNondepLet_159_);
v_res_163_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg(v_localDecl_157_, v_fvarId_158_, v_generalizeNondepLet_boxed_162_, v___y_160_);
lean_dec(v___y_160_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0(lean_object* v_localDecl_164_, lean_object* v_fvarId_165_, uint8_t v_generalizeNondepLet_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg(v_localDecl_164_, v_fvarId_165_, v_generalizeNondepLet_166_, v___y_168_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___boxed(lean_object* v_localDecl_173_, lean_object* v_fvarId_174_, lean_object* v_generalizeNondepLet_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_){
_start:
{
uint8_t v_generalizeNondepLet_boxed_181_; lean_object* v_res_182_; 
v_generalizeNondepLet_boxed_181_ = lean_unbox(v_generalizeNondepLet_175_);
v_res_182_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0(v_localDecl_173_, v_fvarId_174_, v_generalizeNondepLet_boxed_181_, v___y_176_, v___y_177_, v___y_178_, v___y_179_);
lean_dec(v___y_179_);
lean_dec_ref(v___y_178_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3___redArg(lean_object* v_e_183_, lean_object* v_fvarId_184_, lean_object* v___y_185_){
_start:
{
lean_object* v___x_187_; uint8_t v_fst_189_; lean_object* v_mctx_190_; lean_object* v_mctx_207_; lean_object* v___f_208_; lean_object* v___f_209_; lean_object* v___x_210_; lean_object* v___x_211_; uint8_t v___y_213_; uint8_t v___x_220_; uint8_t v___x_221_; 
v___x_187_ = lean_st_ref_get(v___y_185_);
v_mctx_207_ = lean_ctor_get(v___x_187_, 0);
lean_inc_ref_n(v_mctx_207_, 2);
lean_dec(v___x_187_);
v___f_208_ = ((lean_object*)(l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__0));
v___f_209_ = lean_alloc_closure((void*)(l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_209_, 0, v_fvarId_184_);
v___x_210_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2);
v___x_211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
lean_ctor_set(v___x_211_, 1, v_mctx_207_);
v___x_220_ = l_Lean_Expr_hasFVar(v_e_183_);
v___x_221_ = lean_bool_not(v___x_220_);
if (v___x_221_ == 0)
{
v___y_213_ = v___x_221_;
goto v___jp_212_;
}
else
{
uint8_t v___x_222_; uint8_t v___x_223_; 
v___x_222_ = l_Lean_Expr_hasMVar(v_e_183_);
v___x_223_ = lean_bool_not(v___x_222_);
v___y_213_ = v___x_223_;
goto v___jp_212_;
}
v___jp_188_:
{
lean_object* v___x_191_; lean_object* v_cache_192_; lean_object* v_zetaDeltaFVarIds_193_; lean_object* v_postponed_194_; lean_object* v_diag_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_205_; 
v___x_191_ = lean_st_ref_take(v___y_185_);
v_cache_192_ = lean_ctor_get(v___x_191_, 1);
v_zetaDeltaFVarIds_193_ = lean_ctor_get(v___x_191_, 2);
v_postponed_194_ = lean_ctor_get(v___x_191_, 3);
v_diag_195_ = lean_ctor_get(v___x_191_, 4);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_191_);
if (v_isSharedCheck_205_ == 0)
{
lean_object* v_unused_206_; 
v_unused_206_ = lean_ctor_get(v___x_191_, 0);
lean_dec(v_unused_206_);
v___x_197_ = v___x_191_;
v_isShared_198_ = v_isSharedCheck_205_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_diag_195_);
lean_inc(v_postponed_194_);
lean_inc(v_zetaDeltaFVarIds_193_);
lean_inc(v_cache_192_);
lean_dec(v___x_191_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_205_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_200_; 
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 0, v_mctx_190_);
v___x_200_ = v___x_197_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_mctx_190_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v_cache_192_);
lean_ctor_set(v_reuseFailAlloc_204_, 2, v_zetaDeltaFVarIds_193_);
lean_ctor_set(v_reuseFailAlloc_204_, 3, v_postponed_194_);
lean_ctor_set(v_reuseFailAlloc_204_, 4, v_diag_195_);
v___x_200_ = v_reuseFailAlloc_204_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_201_ = lean_st_ref_set(v___y_185_, v___x_200_);
v___x_202_ = lean_box(v_fst_189_);
v___x_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
return v___x_203_;
}
}
}
v___jp_212_:
{
if (v___y_213_ == 0)
{
lean_object* v___x_214_; lean_object* v_snd_215_; lean_object* v_fst_216_; lean_object* v_mctx_217_; uint8_t v___x_218_; 
lean_dec_ref(v_mctx_207_);
v___x_214_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_209_, v___f_208_, v_e_183_, v___x_211_);
v_snd_215_ = lean_ctor_get(v___x_214_, 1);
lean_inc(v_snd_215_);
v_fst_216_ = lean_ctor_get(v___x_214_, 0);
lean_inc(v_fst_216_);
lean_dec_ref(v___x_214_);
v_mctx_217_ = lean_ctor_get(v_snd_215_, 1);
lean_inc_ref(v_mctx_217_);
lean_dec(v_snd_215_);
v___x_218_ = lean_unbox(v_fst_216_);
lean_dec(v_fst_216_);
v_fst_189_ = v___x_218_;
v_mctx_190_ = v_mctx_217_;
goto v___jp_188_;
}
else
{
uint8_t v___x_219_; 
lean_dec_ref_known(v___x_211_, 2);
lean_dec_ref(v___f_209_);
lean_dec_ref(v_e_183_);
v___x_219_ = 0;
v_fst_189_ = v___x_219_;
v_mctx_190_ = v_mctx_207_;
goto v___jp_188_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3___redArg___boxed(lean_object* v_e_224_, lean_object* v_fvarId_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3___redArg(v_e_224_, v_fvarId_225_, v___y_226_);
lean_dec(v___y_226_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3(lean_object* v_e_229_, lean_object* v_fvarId_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3___redArg(v_e_229_, v_fvarId_230_, v___y_232_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3___boxed(lean_object* v_e_237_, lean_object* v_fvarId_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3(v_e_237_, v_fvarId_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
lean_dec(v___y_240_);
lean_dec_ref(v___y_239_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg(lean_object* v_mvarId_245_, lean_object* v_x_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_245_, v_x_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_a_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_260_; 
v_a_253_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_260_ == 0)
{
v___x_255_ = v___x_252_;
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_a_253_);
lean_dec(v___x_252_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_258_; 
if (v_isShared_256_ == 0)
{
v___x_258_ = v___x_255_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_a_253_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
else
{
lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_268_; 
v_a_261_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_268_ == 0)
{
v___x_263_ = v___x_252_;
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v___x_252_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_266_; 
if (v_isShared_264_ == 0)
{
v___x_266_ = v___x_263_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_a_261_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg___boxed(lean_object* v_mvarId_269_, lean_object* v_x_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg(v_mvarId_269_, v_x_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4(lean_object* v_00_u03b1_277_, lean_object* v_mvarId_278_, lean_object* v_x_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg(v_mvarId_278_, v_x_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___boxed(lean_object* v_00_u03b1_286_, lean_object* v_mvarId_287_, lean_object* v_x_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4(v_00_u03b1_286_, v_mvarId_287_, v_x_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
return v_res_294_;
}
}
LEAN_EXPORT uint8_t l_Lean_MVarId_clear___lam__0(lean_object* v_fvarId_295_, lean_object* v_localInst_296_){
_start:
{
lean_object* v_fvar_297_; lean_object* v___x_298_; uint8_t v___x_299_; 
v_fvar_297_ = lean_ctor_get(v_localInst_296_, 1);
v___x_298_ = l_Lean_Expr_fvarId_x21(v_fvar_297_);
v___x_299_ = l_Lean_instBEqFVarId_beq(v___x_298_, v_fvarId_295_);
lean_dec(v___x_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clear___lam__0___boxed(lean_object* v_fvarId_300_, lean_object* v_localInst_301_){
_start:
{
uint8_t v_res_302_; lean_object* v_r_303_; 
v_res_302_ = l_Lean_MVarId_clear___lam__0(v_fvarId_300_, v_localInst_301_);
lean_dec_ref(v_localInst_301_);
lean_dec(v_fvarId_300_);
v_r_303_ = lean_box(v_res_302_);
return v_r_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13_spec__14___redArg(lean_object* v_x_304_, lean_object* v_x_305_, lean_object* v_x_306_, lean_object* v_x_307_){
_start:
{
lean_object* v_ks_308_; lean_object* v_vs_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_333_; 
v_ks_308_ = lean_ctor_get(v_x_304_, 0);
v_vs_309_ = lean_ctor_get(v_x_304_, 1);
v_isSharedCheck_333_ = !lean_is_exclusive(v_x_304_);
if (v_isSharedCheck_333_ == 0)
{
v___x_311_ = v_x_304_;
v_isShared_312_ = v_isSharedCheck_333_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_vs_309_);
lean_inc(v_ks_308_);
lean_dec(v_x_304_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_333_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_313_; uint8_t v___x_314_; 
v___x_313_ = lean_array_get_size(v_ks_308_);
v___x_314_ = lean_nat_dec_lt(v_x_305_, v___x_313_);
if (v___x_314_ == 0)
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_318_; 
lean_dec(v_x_305_);
v___x_315_ = lean_array_push(v_ks_308_, v_x_306_);
v___x_316_ = lean_array_push(v_vs_309_, v_x_307_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 1, v___x_316_);
lean_ctor_set(v___x_311_, 0, v___x_315_);
v___x_318_ = v___x_311_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v___x_315_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v___x_316_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
else
{
lean_object* v_k_x27_320_; uint8_t v___x_321_; 
v_k_x27_320_ = lean_array_fget_borrowed(v_ks_308_, v_x_305_);
v___x_321_ = l_Lean_instBEqMVarId_beq(v_x_306_, v_k_x27_320_);
if (v___x_321_ == 0)
{
lean_object* v___x_323_; 
if (v_isShared_312_ == 0)
{
v___x_323_ = v___x_311_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_ks_308_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_vs_309_);
v___x_323_ = v_reuseFailAlloc_327_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = lean_unsigned_to_nat(1u);
v___x_325_ = lean_nat_add(v_x_305_, v___x_324_);
lean_dec(v_x_305_);
v_x_304_ = v___x_323_;
v_x_305_ = v___x_325_;
goto _start;
}
}
else
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_331_; 
v___x_328_ = lean_array_fset(v_ks_308_, v_x_305_, v_x_306_);
v___x_329_ = lean_array_fset(v_vs_309_, v_x_305_, v_x_307_);
lean_dec(v_x_305_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 1, v___x_329_);
lean_ctor_set(v___x_311_, 0, v___x_328_);
v___x_331_ = v___x_311_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_328_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v___x_329_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13___redArg(lean_object* v_n_334_, lean_object* v_k_335_, lean_object* v_v_336_){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = lean_unsigned_to_nat(0u);
v___x_338_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13_spec__14___redArg(v_n_334_, v___x_337_, v_k_335_, v_v_336_);
return v___x_338_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(lean_object* v_x_340_, size_t v_x_341_, size_t v_x_342_, lean_object* v_x_343_, lean_object* v_x_344_){
_start:
{
if (lean_obj_tag(v_x_340_) == 0)
{
lean_object* v_es_345_; size_t v___x_346_; size_t v___x_347_; lean_object* v_j_348_; lean_object* v___x_349_; uint8_t v___x_350_; 
v_es_345_ = lean_ctor_get(v_x_340_, 0);
v___x_346_ = ((size_t)31ULL);
v___x_347_ = lean_usize_land(v_x_341_, v___x_346_);
v_j_348_ = lean_usize_to_nat(v___x_347_);
v___x_349_ = lean_array_get_size(v_es_345_);
v___x_350_ = lean_nat_dec_lt(v_j_348_, v___x_349_);
if (v___x_350_ == 0)
{
lean_dec(v_j_348_);
lean_dec(v_x_344_);
lean_dec(v_x_343_);
return v_x_340_;
}
else
{
lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_389_; 
lean_inc_ref(v_es_345_);
v_isSharedCheck_389_ = !lean_is_exclusive(v_x_340_);
if (v_isSharedCheck_389_ == 0)
{
lean_object* v_unused_390_; 
v_unused_390_ = lean_ctor_get(v_x_340_, 0);
lean_dec(v_unused_390_);
v___x_352_ = v_x_340_;
v_isShared_353_ = v_isSharedCheck_389_;
goto v_resetjp_351_;
}
else
{
lean_dec(v_x_340_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_389_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v_v_354_; lean_object* v___x_355_; lean_object* v_xs_x27_356_; lean_object* v___y_358_; 
v_v_354_ = lean_array_fget(v_es_345_, v_j_348_);
v___x_355_ = lean_box(0);
v_xs_x27_356_ = lean_array_fset(v_es_345_, v_j_348_, v___x_355_);
switch(lean_obj_tag(v_v_354_))
{
case 0:
{
lean_object* v_key_363_; lean_object* v_val_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_374_; 
v_key_363_ = lean_ctor_get(v_v_354_, 0);
v_val_364_ = lean_ctor_get(v_v_354_, 1);
v_isSharedCheck_374_ = !lean_is_exclusive(v_v_354_);
if (v_isSharedCheck_374_ == 0)
{
v___x_366_ = v_v_354_;
v_isShared_367_ = v_isSharedCheck_374_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_val_364_);
lean_inc(v_key_363_);
lean_dec(v_v_354_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_374_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
uint8_t v___x_368_; 
v___x_368_ = l_Lean_instBEqMVarId_beq(v_x_343_, v_key_363_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; lean_object* v___x_370_; 
lean_del_object(v___x_366_);
v___x_369_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_363_, v_val_364_, v_x_343_, v_x_344_);
v___x_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
v___y_358_ = v___x_370_;
goto v___jp_357_;
}
else
{
lean_object* v___x_372_; 
lean_dec(v_val_364_);
lean_dec(v_key_363_);
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 1, v_x_344_);
lean_ctor_set(v___x_366_, 0, v_x_343_);
v___x_372_ = v___x_366_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_x_343_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v_x_344_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
v___y_358_ = v___x_372_;
goto v___jp_357_;
}
}
}
}
case 1:
{
lean_object* v_node_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_387_; 
v_node_375_ = lean_ctor_get(v_v_354_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v_v_354_);
if (v_isSharedCheck_387_ == 0)
{
v___x_377_ = v_v_354_;
v_isShared_378_ = v_isSharedCheck_387_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_node_375_);
lean_dec(v_v_354_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_387_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
size_t v___x_379_; size_t v___x_380_; size_t v___x_381_; size_t v___x_382_; lean_object* v___x_383_; lean_object* v___x_385_; 
v___x_379_ = ((size_t)5ULL);
v___x_380_ = lean_usize_shift_right(v_x_341_, v___x_379_);
v___x_381_ = ((size_t)1ULL);
v___x_382_ = lean_usize_add(v_x_342_, v___x_381_);
v___x_383_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_node_375_, v___x_380_, v___x_382_, v_x_343_, v_x_344_);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 0, v___x_383_);
v___x_385_ = v___x_377_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___x_383_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
v___y_358_ = v___x_385_;
goto v___jp_357_;
}
}
}
default: 
{
lean_object* v___x_388_; 
v___x_388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_388_, 0, v_x_343_);
lean_ctor_set(v___x_388_, 1, v_x_344_);
v___y_358_ = v___x_388_;
goto v___jp_357_;
}
}
v___jp_357_:
{
lean_object* v___x_359_; lean_object* v___x_361_; 
v___x_359_ = lean_array_fset(v_xs_x27_356_, v_j_348_, v___y_358_);
lean_dec(v_j_348_);
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 0, v___x_359_);
v___x_361_ = v___x_352_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_359_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
}
}
}
else
{
lean_object* v_ks_391_; lean_object* v_vs_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_412_; 
v_ks_391_ = lean_ctor_get(v_x_340_, 0);
v_vs_392_ = lean_ctor_get(v_x_340_, 1);
v_isSharedCheck_412_ = !lean_is_exclusive(v_x_340_);
if (v_isSharedCheck_412_ == 0)
{
v___x_394_ = v_x_340_;
v_isShared_395_ = v_isSharedCheck_412_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_vs_392_);
lean_inc(v_ks_391_);
lean_dec(v_x_340_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_412_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_397_; 
if (v_isShared_395_ == 0)
{
v___x_397_ = v___x_394_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_ks_391_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v_vs_392_);
v___x_397_ = v_reuseFailAlloc_411_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
lean_object* v_newNode_398_; uint8_t v___y_400_; size_t v___x_406_; uint8_t v___x_407_; 
v_newNode_398_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13___redArg(v___x_397_, v_x_343_, v_x_344_);
v___x_406_ = ((size_t)7ULL);
v___x_407_ = lean_usize_dec_le(v___x_406_, v_x_342_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; lean_object* v___x_409_; uint8_t v___x_410_; 
v___x_408_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_398_);
v___x_409_ = lean_unsigned_to_nat(4u);
v___x_410_ = lean_nat_dec_lt(v___x_408_, v___x_409_);
lean_dec(v___x_408_);
v___y_400_ = v___x_410_;
goto v___jp_399_;
}
else
{
v___y_400_ = v___x_407_;
goto v___jp_399_;
}
v___jp_399_:
{
if (v___y_400_ == 0)
{
lean_object* v_ks_401_; lean_object* v_vs_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v_ks_401_ = lean_ctor_get(v_newNode_398_, 0);
lean_inc_ref(v_ks_401_);
v_vs_402_ = lean_ctor_get(v_newNode_398_, 1);
lean_inc_ref(v_vs_402_);
lean_dec_ref(v_newNode_398_);
v___x_403_ = lean_unsigned_to_nat(0u);
v___x_404_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__0);
v___x_405_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg(v_x_342_, v_ks_401_, v_vs_402_, v___x_403_, v___x_404_);
lean_dec_ref(v_vs_402_);
lean_dec_ref(v_ks_401_);
return v___x_405_;
}
else
{
return v_newNode_398_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg(size_t v_depth_413_, lean_object* v_keys_414_, lean_object* v_vals_415_, lean_object* v_i_416_, lean_object* v_entries_417_){
_start:
{
lean_object* v___x_418_; uint8_t v___x_419_; 
v___x_418_ = lean_array_get_size(v_keys_414_);
v___x_419_ = lean_nat_dec_lt(v_i_416_, v___x_418_);
if (v___x_419_ == 0)
{
lean_dec(v_i_416_);
return v_entries_417_;
}
else
{
lean_object* v_k_420_; lean_object* v_v_421_; uint64_t v___x_422_; size_t v_h_423_; size_t v___x_424_; lean_object* v___x_425_; size_t v___x_426_; size_t v___x_427_; size_t v___x_428_; size_t v_h_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v_k_420_ = lean_array_fget_borrowed(v_keys_414_, v_i_416_);
v_v_421_ = lean_array_fget_borrowed(v_vals_415_, v_i_416_);
v___x_422_ = l_Lean_instHashableMVarId_hash(v_k_420_);
v_h_423_ = lean_uint64_to_usize(v___x_422_);
v___x_424_ = ((size_t)5ULL);
v___x_425_ = lean_unsigned_to_nat(1u);
v___x_426_ = ((size_t)1ULL);
v___x_427_ = lean_usize_sub(v_depth_413_, v___x_426_);
v___x_428_ = lean_usize_mul(v___x_424_, v___x_427_);
v_h_429_ = lean_usize_shift_right(v_h_423_, v___x_428_);
v___x_430_ = lean_nat_add(v_i_416_, v___x_425_);
lean_dec(v_i_416_);
lean_inc(v_v_421_);
lean_inc(v_k_420_);
v___x_431_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_entries_417_, v_h_429_, v_depth_413_, v_k_420_, v_v_421_);
v_i_416_ = v___x_430_;
v_entries_417_ = v___x_431_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg___boxed(lean_object* v_depth_433_, lean_object* v_keys_434_, lean_object* v_vals_435_, lean_object* v_i_436_, lean_object* v_entries_437_){
_start:
{
size_t v_depth_boxed_438_; lean_object* v_res_439_; 
v_depth_boxed_438_ = lean_unbox_usize(v_depth_433_);
lean_dec(v_depth_433_);
v_res_439_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg(v_depth_boxed_438_, v_keys_434_, v_vals_435_, v_i_436_, v_entries_437_);
lean_dec_ref(v_vals_435_);
lean_dec_ref(v_keys_434_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___boxed(lean_object* v_x_440_, lean_object* v_x_441_, lean_object* v_x_442_, lean_object* v_x_443_, lean_object* v_x_444_){
_start:
{
size_t v_x_8897__boxed_445_; size_t v_x_8898__boxed_446_; lean_object* v_res_447_; 
v_x_8897__boxed_445_ = lean_unbox_usize(v_x_441_);
lean_dec(v_x_441_);
v_x_8898__boxed_446_ = lean_unbox_usize(v_x_442_);
lean_dec(v_x_442_);
v_res_447_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_x_440_, v_x_8897__boxed_445_, v_x_8898__boxed_446_, v_x_443_, v_x_444_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3___redArg(lean_object* v_x_448_, lean_object* v_x_449_, lean_object* v_x_450_){
_start:
{
uint64_t v___x_451_; size_t v___x_452_; size_t v___x_453_; lean_object* v___x_454_; 
v___x_451_ = l_Lean_instHashableMVarId_hash(v_x_449_);
v___x_452_ = lean_uint64_to_usize(v___x_451_);
v___x_453_ = ((size_t)1ULL);
v___x_454_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_x_448_, v___x_452_, v___x_453_, v_x_449_, v_x_450_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg(lean_object* v_mvarId_455_, lean_object* v_val_456_, lean_object* v___y_457_){
_start:
{
lean_object* v___x_459_; lean_object* v_mctx_460_; lean_object* v_cache_461_; lean_object* v_zetaDeltaFVarIds_462_; lean_object* v_postponed_463_; lean_object* v_diag_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_492_; 
v___x_459_ = lean_st_ref_take(v___y_457_);
v_mctx_460_ = lean_ctor_get(v___x_459_, 0);
v_cache_461_ = lean_ctor_get(v___x_459_, 1);
v_zetaDeltaFVarIds_462_ = lean_ctor_get(v___x_459_, 2);
v_postponed_463_ = lean_ctor_get(v___x_459_, 3);
v_diag_464_ = lean_ctor_get(v___x_459_, 4);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_492_ == 0)
{
v___x_466_ = v___x_459_;
v_isShared_467_ = v_isSharedCheck_492_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_diag_464_);
lean_inc(v_postponed_463_);
lean_inc(v_zetaDeltaFVarIds_462_);
lean_inc(v_cache_461_);
lean_inc(v_mctx_460_);
lean_dec(v___x_459_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_492_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v_depth_468_; lean_object* v_levelAssignDepth_469_; lean_object* v_lmvarCounter_470_; lean_object* v_mvarCounter_471_; lean_object* v_lDecls_472_; lean_object* v_decls_473_; lean_object* v_userNames_474_; lean_object* v_lAssignment_475_; lean_object* v_eAssignment_476_; lean_object* v_dAssignment_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_491_; 
v_depth_468_ = lean_ctor_get(v_mctx_460_, 0);
v_levelAssignDepth_469_ = lean_ctor_get(v_mctx_460_, 1);
v_lmvarCounter_470_ = lean_ctor_get(v_mctx_460_, 2);
v_mvarCounter_471_ = lean_ctor_get(v_mctx_460_, 3);
v_lDecls_472_ = lean_ctor_get(v_mctx_460_, 4);
v_decls_473_ = lean_ctor_get(v_mctx_460_, 5);
v_userNames_474_ = lean_ctor_get(v_mctx_460_, 6);
v_lAssignment_475_ = lean_ctor_get(v_mctx_460_, 7);
v_eAssignment_476_ = lean_ctor_get(v_mctx_460_, 8);
v_dAssignment_477_ = lean_ctor_get(v_mctx_460_, 9);
v_isSharedCheck_491_ = !lean_is_exclusive(v_mctx_460_);
if (v_isSharedCheck_491_ == 0)
{
v___x_479_ = v_mctx_460_;
v_isShared_480_ = v_isSharedCheck_491_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_dAssignment_477_);
lean_inc(v_eAssignment_476_);
lean_inc(v_lAssignment_475_);
lean_inc(v_userNames_474_);
lean_inc(v_decls_473_);
lean_inc(v_lDecls_472_);
lean_inc(v_mvarCounter_471_);
lean_inc(v_lmvarCounter_470_);
lean_inc(v_levelAssignDepth_469_);
lean_inc(v_depth_468_);
lean_dec(v_mctx_460_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_491_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_481_; lean_object* v___x_483_; 
v___x_481_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3___redArg(v_eAssignment_476_, v_mvarId_455_, v_val_456_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 8, v___x_481_);
v___x_483_ = v___x_479_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_depth_468_);
lean_ctor_set(v_reuseFailAlloc_490_, 1, v_levelAssignDepth_469_);
lean_ctor_set(v_reuseFailAlloc_490_, 2, v_lmvarCounter_470_);
lean_ctor_set(v_reuseFailAlloc_490_, 3, v_mvarCounter_471_);
lean_ctor_set(v_reuseFailAlloc_490_, 4, v_lDecls_472_);
lean_ctor_set(v_reuseFailAlloc_490_, 5, v_decls_473_);
lean_ctor_set(v_reuseFailAlloc_490_, 6, v_userNames_474_);
lean_ctor_set(v_reuseFailAlloc_490_, 7, v_lAssignment_475_);
lean_ctor_set(v_reuseFailAlloc_490_, 8, v___x_481_);
lean_ctor_set(v_reuseFailAlloc_490_, 9, v_dAssignment_477_);
v___x_483_ = v_reuseFailAlloc_490_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
lean_object* v___x_485_; 
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 0, v___x_483_);
v___x_485_ = v___x_466_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v___x_483_);
lean_ctor_set(v_reuseFailAlloc_489_, 1, v_cache_461_);
lean_ctor_set(v_reuseFailAlloc_489_, 2, v_zetaDeltaFVarIds_462_);
lean_ctor_set(v_reuseFailAlloc_489_, 3, v_postponed_463_);
lean_ctor_set(v_reuseFailAlloc_489_, 4, v_diag_464_);
v___x_485_ = v_reuseFailAlloc_489_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_486_ = lean_st_ref_set(v___y_457_, v___x_485_);
v___x_487_ = lean_box(0);
v___x_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
return v___x_488_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg___boxed(lean_object* v_mvarId_493_, lean_object* v_val_494_, lean_object* v___y_495_, lean_object* v___y_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg(v_mvarId_493_, v_val_494_, v___y_495_);
lean_dec(v___y_495_);
return v_res_497_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__2));
v___x_503_ = l_Lean_stringToMessageData(v___x_502_);
return v___x_503_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5(void){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__4));
v___x_506_ = l_Lean_stringToMessageData(v___x_505_);
return v___x_506_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7(void){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_508_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__6));
v___x_509_ = l_Lean_stringToMessageData(v___x_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9(lean_object* v_fvarId_510_, lean_object* v_mvarId_511_, lean_object* v_as_512_, size_t v_i_513_, size_t v_stop_514_, lean_object* v_b_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
lean_object* v_a_522_; uint8_t v___x_526_; 
v___x_526_ = lean_usize_dec_eq(v_i_513_, v_stop_514_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; 
v___x_527_ = lean_array_uget(v_as_512_, v_i_513_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v___x_528_; 
v___x_528_ = lean_box(0);
v_a_522_ = v___x_528_;
goto v___jp_521_;
}
else
{
lean_object* v_val_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_566_; 
v_val_529_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_566_ == 0)
{
v___x_531_ = v___x_527_;
v_isShared_532_ = v_isSharedCheck_566_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_val_529_);
lean_dec(v___x_527_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_566_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_533_; uint8_t v___x_534_; 
v___x_533_ = l_Lean_LocalDecl_fvarId(v_val_529_);
v___x_534_ = l_Lean_instBEqFVarId_beq(v___x_533_, v_fvarId_510_);
lean_dec(v___x_533_);
if (v___x_534_ == 0)
{
uint8_t v___x_535_; lean_object* v___x_536_; 
v___x_535_ = 1;
lean_inc(v_fvarId_510_);
lean_inc(v_val_529_);
v___x_536_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg(v_val_529_, v_fvarId_510_, v___x_535_, v___y_517_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v_a_537_; uint8_t v___x_538_; 
v_a_537_ = lean_ctor_get(v___x_536_, 0);
lean_inc(v_a_537_);
lean_dec_ref_known(v___x_536_, 1);
v___x_538_ = lean_unbox(v_a_537_);
lean_dec(v_a_537_);
if (v___x_538_ == 0)
{
lean_object* v___x_539_; 
lean_del_object(v___x_531_);
lean_dec(v_val_529_);
v___x_539_ = lean_box(0);
v_a_522_ = v___x_539_;
goto v___jp_521_;
}
else
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_553_; 
v___x_540_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__1));
v___x_541_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3);
v___x_542_ = l_Lean_LocalDecl_toExpr(v_val_529_);
v___x_543_ = l_Lean_MessageData_ofExpr(v___x_542_);
v___x_544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_541_);
lean_ctor_set(v___x_544_, 1, v___x_543_);
v___x_545_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5);
v___x_546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_546_, 0, v___x_544_);
lean_ctor_set(v___x_546_, 1, v___x_545_);
lean_inc(v_fvarId_510_);
v___x_547_ = l_Lean_mkFVar(v_fvarId_510_);
v___x_548_ = l_Lean_MessageData_ofExpr(v___x_547_);
v___x_549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_549_, 0, v___x_546_);
lean_ctor_set(v___x_549_, 1, v___x_548_);
v___x_550_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7);
v___x_551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_551_, 0, v___x_549_);
lean_ctor_set(v___x_551_, 1, v___x_550_);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 0, v___x_551_);
v___x_553_ = v___x_531_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v___x_551_);
v___x_553_ = v_reuseFailAlloc_556_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
lean_object* v___x_554_; 
lean_inc(v_mvarId_511_);
v___x_554_ = l_Lean_Meta_throwTacticEx___redArg(v___x_540_, v_mvarId_511_, v___x_553_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v_a_555_; 
v_a_555_ = lean_ctor_get(v___x_554_, 0);
lean_inc(v_a_555_);
lean_dec_ref_known(v___x_554_, 1);
v_a_522_ = v_a_555_;
goto v___jp_521_;
}
else
{
lean_dec(v_mvarId_511_);
lean_dec(v_fvarId_510_);
return v___x_554_;
}
}
}
}
else
{
lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_564_; 
lean_del_object(v___x_531_);
lean_dec(v_val_529_);
lean_dec(v_mvarId_511_);
lean_dec(v_fvarId_510_);
v_a_557_ = lean_ctor_get(v___x_536_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_564_ == 0)
{
v___x_559_ = v___x_536_;
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v___x_536_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_562_; 
if (v_isShared_560_ == 0)
{
v___x_562_ = v___x_559_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_a_557_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
}
else
{
lean_object* v___x_565_; 
lean_del_object(v___x_531_);
lean_dec(v_val_529_);
v___x_565_ = lean_box(0);
v_a_522_ = v___x_565_;
goto v___jp_521_;
}
}
}
}
else
{
lean_object* v___x_567_; 
lean_dec(v_mvarId_511_);
lean_dec(v_fvarId_510_);
v___x_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_567_, 0, v_b_515_);
return v___x_567_;
}
v___jp_521_:
{
size_t v___x_523_; size_t v___x_524_; 
v___x_523_ = ((size_t)1ULL);
v___x_524_ = lean_usize_add(v_i_513_, v___x_523_);
v_i_513_ = v___x_524_;
v_b_515_ = v_a_522_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___boxed(lean_object* v_fvarId_568_, lean_object* v_mvarId_569_, lean_object* v_as_570_, lean_object* v_i_571_, lean_object* v_stop_572_, lean_object* v_b_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
size_t v_i_boxed_579_; size_t v_stop_boxed_580_; lean_object* v_res_581_; 
v_i_boxed_579_ = lean_unbox_usize(v_i_571_);
lean_dec(v_i_571_);
v_stop_boxed_580_ = lean_unbox_usize(v_stop_572_);
lean_dec(v_stop_572_);
v_res_581_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9(v_fvarId_568_, v_mvarId_569_, v_as_570_, v_i_boxed_579_, v_stop_boxed_580_, v_b_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec_ref(v_as_570_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(lean_object* v_fvarId_582_, lean_object* v_mvarId_583_, lean_object* v_as_584_, size_t v_i_585_, size_t v_stop_586_, lean_object* v_b_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_){
_start:
{
lean_object* v_a_594_; uint8_t v___x_598_; 
v___x_598_ = lean_usize_dec_eq(v_i_585_, v_stop_586_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; 
v___x_599_ = lean_array_uget(v_as_584_, v_i_585_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v___x_600_; 
v___x_600_ = lean_box(0);
v_a_594_ = v___x_600_;
goto v___jp_593_;
}
else
{
lean_object* v_val_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_638_; 
v_val_601_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_638_ == 0)
{
v___x_603_ = v___x_599_;
v_isShared_604_ = v_isSharedCheck_638_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_val_601_);
lean_dec(v___x_599_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_638_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_605_; uint8_t v___x_606_; 
v___x_605_ = l_Lean_LocalDecl_fvarId(v_val_601_);
v___x_606_ = l_Lean_instBEqFVarId_beq(v___x_605_, v_fvarId_582_);
lean_dec(v___x_605_);
if (v___x_606_ == 0)
{
uint8_t v___x_607_; lean_object* v___x_608_; 
v___x_607_ = 1;
lean_inc(v_fvarId_582_);
lean_inc(v_val_601_);
v___x_608_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg(v_val_601_, v_fvarId_582_, v___x_607_, v___y_589_);
if (lean_obj_tag(v___x_608_) == 0)
{
lean_object* v_a_609_; uint8_t v___x_610_; 
v_a_609_ = lean_ctor_get(v___x_608_, 0);
lean_inc(v_a_609_);
lean_dec_ref_known(v___x_608_, 1);
v___x_610_ = lean_unbox(v_a_609_);
lean_dec(v_a_609_);
if (v___x_610_ == 0)
{
lean_object* v___x_611_; 
lean_del_object(v___x_603_);
lean_dec(v_val_601_);
v___x_611_ = lean_box(0);
v_a_594_ = v___x_611_;
goto v___jp_593_;
}
else
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_625_; 
v___x_612_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__1));
v___x_613_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3);
v___x_614_ = l_Lean_LocalDecl_toExpr(v_val_601_);
v___x_615_ = l_Lean_MessageData_ofExpr(v___x_614_);
v___x_616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_613_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
v___x_617_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5);
v___x_618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_618_, 0, v___x_616_);
lean_ctor_set(v___x_618_, 1, v___x_617_);
lean_inc(v_fvarId_582_);
v___x_619_ = l_Lean_mkFVar(v_fvarId_582_);
v___x_620_ = l_Lean_MessageData_ofExpr(v___x_619_);
v___x_621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_621_, 0, v___x_618_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
v___x_622_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7);
v___x_623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_621_);
lean_ctor_set(v___x_623_, 1, v___x_622_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v___x_623_);
v___x_625_ = v___x_603_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_623_);
v___x_625_ = v_reuseFailAlloc_628_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
lean_object* v___x_626_; 
lean_inc(v_mvarId_583_);
v___x_626_ = l_Lean_Meta_throwTacticEx___redArg(v___x_612_, v_mvarId_583_, v___x_625_, v___y_588_, v___y_589_, v___y_590_, v___y_591_);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_object* v_a_627_; 
v_a_627_ = lean_ctor_get(v___x_626_, 0);
lean_inc(v_a_627_);
lean_dec_ref_known(v___x_626_, 1);
v_a_594_ = v_a_627_;
goto v___jp_593_;
}
else
{
lean_dec(v_mvarId_583_);
lean_dec(v_fvarId_582_);
return v___x_626_;
}
}
}
}
else
{
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_636_; 
lean_del_object(v___x_603_);
lean_dec(v_val_601_);
lean_dec(v_mvarId_583_);
lean_dec(v_fvarId_582_);
v_a_629_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_636_ == 0)
{
v___x_631_ = v___x_608_;
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_608_);
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
else
{
lean_object* v___x_637_; 
lean_del_object(v___x_603_);
lean_dec(v_val_601_);
v___x_637_ = lean_box(0);
v_a_594_ = v___x_637_;
goto v___jp_593_;
}
}
}
}
else
{
lean_object* v___x_639_; 
lean_dec(v_mvarId_583_);
lean_dec(v_fvarId_582_);
v___x_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_639_, 0, v_b_587_);
return v___x_639_;
}
v___jp_593_:
{
size_t v___x_595_; size_t v___x_596_; lean_object* v___x_597_; 
v___x_595_ = ((size_t)1ULL);
v___x_596_ = lean_usize_add(v_i_585_, v___x_595_);
v___x_597_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9(v_fvarId_582_, v_mvarId_583_, v_as_584_, v___x_596_, v_stop_586_, v_a_594_, v___y_588_, v___y_589_, v___y_590_, v___y_591_);
return v___x_597_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5___boxed(lean_object* v_fvarId_640_, lean_object* v_mvarId_641_, lean_object* v_as_642_, lean_object* v_i_643_, lean_object* v_stop_644_, lean_object* v_b_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
size_t v_i_boxed_651_; size_t v_stop_boxed_652_; lean_object* v_res_653_; 
v_i_boxed_651_ = lean_unbox_usize(v_i_643_);
lean_dec(v_i_643_);
v_stop_boxed_652_ = lean_unbox_usize(v_stop_644_);
lean_dec(v_stop_644_);
v_res_653_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_640_, v_mvarId_641_, v_as_642_, v_i_boxed_651_, v_stop_boxed_652_, v_b_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec_ref(v_as_642_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6(lean_object* v_fvarId_654_, lean_object* v_mvarId_655_, lean_object* v_x_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
if (lean_obj_tag(v_x_656_) == 0)
{
lean_object* v_cs_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_683_; 
v_cs_662_ = lean_ctor_get(v_x_656_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v_x_656_);
if (v_isSharedCheck_683_ == 0)
{
v___x_664_ = v_x_656_;
v_isShared_665_ = v_isSharedCheck_683_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_cs_662_);
lean_dec(v_x_656_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_683_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_666_ = lean_unsigned_to_nat(0u);
v___x_667_ = lean_array_get_size(v_cs_662_);
v___x_668_ = lean_box(0);
v___x_669_ = lean_nat_dec_lt(v___x_666_, v___x_667_);
if (v___x_669_ == 0)
{
lean_object* v___x_671_; 
lean_dec_ref(v_cs_662_);
lean_dec(v_mvarId_655_);
lean_dec(v_fvarId_654_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 0, v___x_668_);
v___x_671_ = v___x_664_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v___x_668_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
else
{
uint8_t v___x_673_; 
v___x_673_ = lean_nat_dec_le(v___x_667_, v___x_667_);
if (v___x_673_ == 0)
{
if (v___x_669_ == 0)
{
lean_object* v___x_675_; 
lean_dec_ref(v_cs_662_);
lean_dec(v_mvarId_655_);
lean_dec(v_fvarId_654_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 0, v___x_668_);
v___x_675_ = v___x_664_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_668_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
else
{
size_t v___x_677_; size_t v___x_678_; lean_object* v___x_679_; 
lean_del_object(v___x_664_);
v___x_677_ = ((size_t)0ULL);
v___x_678_ = lean_usize_of_nat(v___x_667_);
v___x_679_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(v_fvarId_654_, v_mvarId_655_, v_cs_662_, v___x_677_, v___x_678_, v___x_668_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
lean_dec_ref(v_cs_662_);
return v___x_679_;
}
}
else
{
size_t v___x_680_; size_t v___x_681_; lean_object* v___x_682_; 
lean_del_object(v___x_664_);
v___x_680_ = ((size_t)0ULL);
v___x_681_ = lean_usize_of_nat(v___x_667_);
v___x_682_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(v_fvarId_654_, v_mvarId_655_, v_cs_662_, v___x_680_, v___x_681_, v___x_668_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
lean_dec_ref(v_cs_662_);
return v___x_682_;
}
}
}
}
else
{
lean_object* v_vs_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_705_; 
v_vs_684_ = lean_ctor_get(v_x_656_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v_x_656_);
if (v_isSharedCheck_705_ == 0)
{
v___x_686_ = v_x_656_;
v_isShared_687_ = v_isSharedCheck_705_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_vs_684_);
lean_dec(v_x_656_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_705_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; uint8_t v___x_691_; 
v___x_688_ = lean_unsigned_to_nat(0u);
v___x_689_ = lean_array_get_size(v_vs_684_);
v___x_690_ = lean_box(0);
v___x_691_ = lean_nat_dec_lt(v___x_688_, v___x_689_);
if (v___x_691_ == 0)
{
lean_object* v___x_693_; 
lean_dec_ref(v_vs_684_);
lean_dec(v_mvarId_655_);
lean_dec(v_fvarId_654_);
if (v_isShared_687_ == 0)
{
lean_ctor_set_tag(v___x_686_, 0);
lean_ctor_set(v___x_686_, 0, v___x_690_);
v___x_693_ = v___x_686_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_690_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
else
{
uint8_t v___x_695_; 
v___x_695_ = lean_nat_dec_le(v___x_689_, v___x_689_);
if (v___x_695_ == 0)
{
if (v___x_691_ == 0)
{
lean_object* v___x_697_; 
lean_dec_ref(v_vs_684_);
lean_dec(v_mvarId_655_);
lean_dec(v_fvarId_654_);
if (v_isShared_687_ == 0)
{
lean_ctor_set_tag(v___x_686_, 0);
lean_ctor_set(v___x_686_, 0, v___x_690_);
v___x_697_ = v___x_686_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_690_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
else
{
size_t v___x_699_; size_t v___x_700_; lean_object* v___x_701_; 
lean_del_object(v___x_686_);
v___x_699_ = ((size_t)0ULL);
v___x_700_ = lean_usize_of_nat(v___x_689_);
v___x_701_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_654_, v_mvarId_655_, v_vs_684_, v___x_699_, v___x_700_, v___x_690_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
lean_dec_ref(v_vs_684_);
return v___x_701_;
}
}
else
{
size_t v___x_702_; size_t v___x_703_; lean_object* v___x_704_; 
lean_del_object(v___x_686_);
v___x_702_ = ((size_t)0ULL);
v___x_703_ = lean_usize_of_nat(v___x_689_);
v___x_704_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_654_, v_mvarId_655_, v_vs_684_, v___x_702_, v___x_703_, v___x_690_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
lean_dec_ref(v_vs_684_);
return v___x_704_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(lean_object* v_fvarId_706_, lean_object* v_mvarId_707_, lean_object* v_as_708_, size_t v_i_709_, size_t v_stop_710_, lean_object* v_b_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_){
_start:
{
uint8_t v___x_717_; 
v___x_717_ = lean_usize_dec_eq(v_i_709_, v_stop_710_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = lean_array_uget_borrowed(v_as_708_, v_i_709_);
lean_inc(v___x_718_);
lean_inc(v_mvarId_707_);
lean_inc(v_fvarId_706_);
v___x_719_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6(v_fvarId_706_, v_mvarId_707_, v___x_718_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v_a_720_; size_t v___x_721_; size_t v___x_722_; 
v_a_720_ = lean_ctor_get(v___x_719_, 0);
lean_inc(v_a_720_);
lean_dec_ref_known(v___x_719_, 1);
v___x_721_ = ((size_t)1ULL);
v___x_722_ = lean_usize_add(v_i_709_, v___x_721_);
v_i_709_ = v___x_722_;
v_b_711_ = v_a_720_;
goto _start;
}
else
{
lean_dec(v_mvarId_707_);
lean_dec(v_fvarId_706_);
return v___x_719_;
}
}
else
{
lean_object* v___x_724_; 
lean_dec(v_mvarId_707_);
lean_dec(v_fvarId_706_);
v___x_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_724_, 0, v_b_711_);
return v___x_724_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7___boxed(lean_object* v_fvarId_725_, lean_object* v_mvarId_726_, lean_object* v_as_727_, lean_object* v_i_728_, lean_object* v_stop_729_, lean_object* v_b_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
size_t v_i_boxed_736_; size_t v_stop_boxed_737_; lean_object* v_res_738_; 
v_i_boxed_736_ = lean_unbox_usize(v_i_728_);
lean_dec(v_i_728_);
v_stop_boxed_737_ = lean_unbox_usize(v_stop_729_);
lean_dec(v_stop_729_);
v_res_738_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(v_fvarId_725_, v_mvarId_726_, v_as_727_, v_i_boxed_736_, v_stop_boxed_737_, v_b_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec_ref(v_as_727_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6___boxed(lean_object* v_fvarId_739_, lean_object* v_mvarId_740_, lean_object* v_x_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6(v_fvarId_739_, v_mvarId_740_, v_x_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6(lean_object* v_fvarId_748_, lean_object* v_mvarId_749_, lean_object* v_t_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v_root_756_; lean_object* v_tail_757_; lean_object* v___x_758_; 
v_root_756_ = lean_ctor_get(v_t_750_, 0);
lean_inc_ref(v_root_756_);
v_tail_757_ = lean_ctor_get(v_t_750_, 1);
lean_inc_ref(v_tail_757_);
lean_dec_ref(v_t_750_);
lean_inc(v_mvarId_749_);
lean_inc(v_fvarId_748_);
v___x_758_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6(v_fvarId_748_, v_mvarId_749_, v_root_756_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_779_; 
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_779_ == 0)
{
lean_object* v_unused_780_; 
v_unused_780_ = lean_ctor_get(v___x_758_, 0);
lean_dec(v_unused_780_);
v___x_760_ = v___x_758_;
v_isShared_761_ = v_isSharedCheck_779_;
goto v_resetjp_759_;
}
else
{
lean_dec(v___x_758_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_779_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; uint8_t v___x_765_; 
v___x_762_ = lean_unsigned_to_nat(0u);
v___x_763_ = lean_array_get_size(v_tail_757_);
v___x_764_ = lean_box(0);
v___x_765_ = lean_nat_dec_lt(v___x_762_, v___x_763_);
if (v___x_765_ == 0)
{
lean_object* v___x_767_; 
lean_dec_ref(v_tail_757_);
lean_dec(v_mvarId_749_);
lean_dec(v_fvarId_748_);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 0, v___x_764_);
v___x_767_ = v___x_760_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v___x_764_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
else
{
uint8_t v___x_769_; 
v___x_769_ = lean_nat_dec_le(v___x_763_, v___x_763_);
if (v___x_769_ == 0)
{
if (v___x_765_ == 0)
{
lean_object* v___x_771_; 
lean_dec_ref(v_tail_757_);
lean_dec(v_mvarId_749_);
lean_dec(v_fvarId_748_);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 0, v___x_764_);
v___x_771_ = v___x_760_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_764_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
else
{
size_t v___x_773_; size_t v___x_774_; lean_object* v___x_775_; 
lean_del_object(v___x_760_);
v___x_773_ = ((size_t)0ULL);
v___x_774_ = lean_usize_of_nat(v___x_763_);
v___x_775_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_748_, v_mvarId_749_, v_tail_757_, v___x_773_, v___x_774_, v___x_764_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
lean_dec_ref(v_tail_757_);
return v___x_775_;
}
}
else
{
size_t v___x_776_; size_t v___x_777_; lean_object* v___x_778_; 
lean_del_object(v___x_760_);
v___x_776_ = ((size_t)0ULL);
v___x_777_ = lean_usize_of_nat(v___x_763_);
v___x_778_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_748_, v_mvarId_749_, v_tail_757_, v___x_776_, v___x_777_, v___x_764_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
lean_dec_ref(v_tail_757_);
return v___x_778_;
}
}
}
}
else
{
lean_dec_ref(v_tail_757_);
lean_dec(v_mvarId_749_);
lean_dec(v_fvarId_748_);
return v___x_758_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6___boxed(lean_object* v_fvarId_781_, lean_object* v_mvarId_782_, lean_object* v_t_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6(v_fvarId_781_, v_mvarId_782_, v_t_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
return v_res_789_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4(lean_object* v_fvarId_791_, lean_object* v_mvarId_792_, lean_object* v_x_793_, size_t v_x_794_, size_t v_x_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_){
_start:
{
if (lean_obj_tag(v_x_793_) == 0)
{
lean_object* v_cs_801_; lean_object* v___x_802_; size_t v___x_803_; lean_object* v_j_804_; lean_object* v___x_805_; size_t v___x_806_; size_t v___x_807_; size_t v___x_808_; size_t v___x_809_; size_t v___x_810_; size_t v___x_811_; lean_object* v___x_812_; 
v_cs_801_ = lean_ctor_get(v_x_793_, 0);
lean_inc_ref(v_cs_801_);
lean_dec_ref_known(v_x_793_, 1);
v___x_802_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0);
v___x_803_ = lean_usize_shift_right(v_x_794_, v_x_795_);
v_j_804_ = lean_usize_to_nat(v___x_803_);
v___x_805_ = lean_array_get_borrowed(v___x_802_, v_cs_801_, v_j_804_);
v___x_806_ = ((size_t)1ULL);
v___x_807_ = lean_usize_shift_left(v___x_806_, v_x_795_);
v___x_808_ = lean_usize_sub(v___x_807_, v___x_806_);
v___x_809_ = lean_usize_land(v_x_794_, v___x_808_);
v___x_810_ = ((size_t)5ULL);
v___x_811_ = lean_usize_sub(v_x_795_, v___x_810_);
lean_inc(v___x_805_);
lean_inc(v_mvarId_792_);
lean_inc(v_fvarId_791_);
v___x_812_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4(v_fvarId_791_, v_mvarId_792_, v___x_805_, v___x_809_, v___x_811_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_834_; 
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_834_ == 0)
{
lean_object* v_unused_835_; 
v_unused_835_ = lean_ctor_get(v___x_812_, 0);
lean_dec(v_unused_835_);
v___x_814_ = v___x_812_;
v_isShared_815_ = v_isSharedCheck_834_;
goto v_resetjp_813_;
}
else
{
lean_dec(v___x_812_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_834_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; uint8_t v___x_820_; 
v___x_816_ = lean_unsigned_to_nat(1u);
v___x_817_ = lean_nat_add(v_j_804_, v___x_816_);
lean_dec(v_j_804_);
v___x_818_ = lean_array_get_size(v_cs_801_);
v___x_819_ = lean_box(0);
v___x_820_ = lean_nat_dec_lt(v___x_817_, v___x_818_);
if (v___x_820_ == 0)
{
lean_object* v___x_822_; 
lean_dec(v___x_817_);
lean_dec_ref(v_cs_801_);
lean_dec(v_mvarId_792_);
lean_dec(v_fvarId_791_);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 0, v___x_819_);
v___x_822_ = v___x_814_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_819_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
else
{
uint8_t v___x_824_; 
v___x_824_ = lean_nat_dec_le(v___x_818_, v___x_818_);
if (v___x_824_ == 0)
{
if (v___x_820_ == 0)
{
lean_object* v___x_826_; 
lean_dec(v___x_817_);
lean_dec_ref(v_cs_801_);
lean_dec(v_mvarId_792_);
lean_dec(v_fvarId_791_);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 0, v___x_819_);
v___x_826_ = v___x_814_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_819_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
else
{
size_t v___x_828_; size_t v___x_829_; lean_object* v___x_830_; 
lean_del_object(v___x_814_);
v___x_828_ = lean_usize_of_nat(v___x_817_);
lean_dec(v___x_817_);
v___x_829_ = lean_usize_of_nat(v___x_818_);
v___x_830_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(v_fvarId_791_, v_mvarId_792_, v_cs_801_, v___x_828_, v___x_829_, v___x_819_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
lean_dec_ref(v_cs_801_);
return v___x_830_;
}
}
else
{
size_t v___x_831_; size_t v___x_832_; lean_object* v___x_833_; 
lean_del_object(v___x_814_);
v___x_831_ = lean_usize_of_nat(v___x_817_);
lean_dec(v___x_817_);
v___x_832_ = lean_usize_of_nat(v___x_818_);
v___x_833_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(v_fvarId_791_, v_mvarId_792_, v_cs_801_, v___x_831_, v___x_832_, v___x_819_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
lean_dec_ref(v_cs_801_);
return v___x_833_;
}
}
}
}
else
{
lean_dec(v_j_804_);
lean_dec_ref(v_cs_801_);
lean_dec(v_mvarId_792_);
lean_dec(v_fvarId_791_);
return v___x_812_;
}
}
else
{
lean_object* v_vs_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_857_; 
v_vs_836_ = lean_ctor_get(v_x_793_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v_x_793_);
if (v_isSharedCheck_857_ == 0)
{
v___x_838_ = v_x_793_;
v_isShared_839_ = v_isSharedCheck_857_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_vs_836_);
lean_dec(v_x_793_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_857_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; uint8_t v___x_843_; 
v___x_840_ = lean_usize_to_nat(v_x_794_);
v___x_841_ = lean_array_get_size(v_vs_836_);
v___x_842_ = lean_box(0);
v___x_843_ = lean_nat_dec_lt(v___x_840_, v___x_841_);
if (v___x_843_ == 0)
{
lean_object* v___x_845_; 
lean_dec(v___x_840_);
lean_dec_ref(v_vs_836_);
lean_dec(v_mvarId_792_);
lean_dec(v_fvarId_791_);
if (v_isShared_839_ == 0)
{
lean_ctor_set_tag(v___x_838_, 0);
lean_ctor_set(v___x_838_, 0, v___x_842_);
v___x_845_ = v___x_838_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_842_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
else
{
uint8_t v___x_847_; 
v___x_847_ = lean_nat_dec_le(v___x_841_, v___x_841_);
if (v___x_847_ == 0)
{
if (v___x_843_ == 0)
{
lean_object* v___x_849_; 
lean_dec(v___x_840_);
lean_dec_ref(v_vs_836_);
lean_dec(v_mvarId_792_);
lean_dec(v_fvarId_791_);
if (v_isShared_839_ == 0)
{
lean_ctor_set_tag(v___x_838_, 0);
lean_ctor_set(v___x_838_, 0, v___x_842_);
v___x_849_ = v___x_838_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_842_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
else
{
size_t v___x_851_; size_t v___x_852_; lean_object* v___x_853_; 
lean_del_object(v___x_838_);
v___x_851_ = lean_usize_of_nat(v___x_840_);
lean_dec(v___x_840_);
v___x_852_ = lean_usize_of_nat(v___x_841_);
v___x_853_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_791_, v_mvarId_792_, v_vs_836_, v___x_851_, v___x_852_, v___x_842_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
lean_dec_ref(v_vs_836_);
return v___x_853_;
}
}
else
{
size_t v___x_854_; size_t v___x_855_; lean_object* v___x_856_; 
lean_del_object(v___x_838_);
v___x_854_ = lean_usize_of_nat(v___x_840_);
lean_dec(v___x_840_);
v___x_855_ = lean_usize_of_nat(v___x_841_);
v___x_856_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_791_, v_mvarId_792_, v_vs_836_, v___x_854_, v___x_855_, v___x_842_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
lean_dec_ref(v_vs_836_);
return v___x_856_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___boxed(lean_object* v_fvarId_858_, lean_object* v_mvarId_859_, lean_object* v_x_860_, lean_object* v_x_861_, lean_object* v_x_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
size_t v_x_9586__boxed_868_; size_t v_x_9587__boxed_869_; lean_object* v_res_870_; 
v_x_9586__boxed_868_ = lean_unbox_usize(v_x_861_);
lean_dec(v_x_861_);
v_x_9587__boxed_869_ = lean_unbox_usize(v_x_862_);
lean_dec(v_x_862_);
v_res_870_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4(v_fvarId_858_, v_mvarId_859_, v_x_860_, v_x_9586__boxed_868_, v_x_9587__boxed_869_, v___y_863_, v___y_864_, v___y_865_, v___y_866_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1(lean_object* v_fvarId_871_, lean_object* v_mvarId_872_, lean_object* v_t_873_, lean_object* v_start_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
lean_object* v___x_880_; uint8_t v___x_881_; 
v___x_880_ = lean_unsigned_to_nat(0u);
v___x_881_ = lean_nat_dec_eq(v_start_874_, v___x_880_);
if (v___x_881_ == 0)
{
lean_object* v_root_882_; lean_object* v_tail_883_; size_t v_shift_884_; lean_object* v_tailOff_885_; uint8_t v___x_886_; 
v_root_882_ = lean_ctor_get(v_t_873_, 0);
lean_inc_ref(v_root_882_);
v_tail_883_ = lean_ctor_get(v_t_873_, 1);
lean_inc_ref(v_tail_883_);
v_shift_884_ = lean_ctor_get_usize(v_t_873_, 4);
v_tailOff_885_ = lean_ctor_get(v_t_873_, 3);
lean_inc(v_tailOff_885_);
lean_dec_ref(v_t_873_);
v___x_886_ = lean_nat_dec_le(v_tailOff_885_, v_start_874_);
if (v___x_886_ == 0)
{
size_t v___x_887_; lean_object* v___x_888_; 
lean_dec(v_tailOff_885_);
v___x_887_ = lean_usize_of_nat(v_start_874_);
lean_inc(v_mvarId_872_);
lean_inc(v_fvarId_871_);
v___x_888_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4(v_fvarId_871_, v_mvarId_872_, v_root_882_, v___x_887_, v_shift_884_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_908_; 
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_908_ == 0)
{
lean_object* v_unused_909_; 
v_unused_909_ = lean_ctor_get(v___x_888_, 0);
lean_dec(v_unused_909_);
v___x_890_ = v___x_888_;
v_isShared_891_ = v_isSharedCheck_908_;
goto v_resetjp_889_;
}
else
{
lean_dec(v___x_888_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_908_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_892_; lean_object* v___x_893_; uint8_t v___x_894_; 
v___x_892_ = lean_array_get_size(v_tail_883_);
v___x_893_ = lean_box(0);
v___x_894_ = lean_nat_dec_lt(v___x_880_, v___x_892_);
if (v___x_894_ == 0)
{
lean_object* v___x_896_; 
lean_dec_ref(v_tail_883_);
lean_dec(v_mvarId_872_);
lean_dec(v_fvarId_871_);
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 0, v___x_893_);
v___x_896_ = v___x_890_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_893_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
else
{
uint8_t v___x_898_; 
v___x_898_ = lean_nat_dec_le(v___x_892_, v___x_892_);
if (v___x_898_ == 0)
{
if (v___x_894_ == 0)
{
lean_object* v___x_900_; 
lean_dec_ref(v_tail_883_);
lean_dec(v_mvarId_872_);
lean_dec(v_fvarId_871_);
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 0, v___x_893_);
v___x_900_ = v___x_890_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v___x_893_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
else
{
size_t v___x_902_; size_t v___x_903_; lean_object* v___x_904_; 
lean_del_object(v___x_890_);
v___x_902_ = ((size_t)0ULL);
v___x_903_ = lean_usize_of_nat(v___x_892_);
v___x_904_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_871_, v_mvarId_872_, v_tail_883_, v___x_902_, v___x_903_, v___x_893_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
lean_dec_ref(v_tail_883_);
return v___x_904_;
}
}
else
{
size_t v___x_905_; size_t v___x_906_; lean_object* v___x_907_; 
lean_del_object(v___x_890_);
v___x_905_ = ((size_t)0ULL);
v___x_906_ = lean_usize_of_nat(v___x_892_);
v___x_907_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_871_, v_mvarId_872_, v_tail_883_, v___x_905_, v___x_906_, v___x_893_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
lean_dec_ref(v_tail_883_);
return v___x_907_;
}
}
}
}
else
{
lean_dec_ref(v_tail_883_);
lean_dec(v_mvarId_872_);
lean_dec(v_fvarId_871_);
return v___x_888_;
}
}
else
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; uint8_t v___x_913_; 
lean_dec_ref(v_root_882_);
v___x_910_ = lean_nat_sub(v_start_874_, v_tailOff_885_);
lean_dec(v_tailOff_885_);
v___x_911_ = lean_array_get_size(v_tail_883_);
v___x_912_ = lean_box(0);
v___x_913_ = lean_nat_dec_lt(v___x_910_, v___x_911_);
if (v___x_913_ == 0)
{
lean_object* v___x_914_; 
lean_dec(v___x_910_);
lean_dec_ref(v_tail_883_);
lean_dec(v_mvarId_872_);
lean_dec(v_fvarId_871_);
v___x_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_914_, 0, v___x_912_);
return v___x_914_;
}
else
{
uint8_t v___x_915_; 
v___x_915_ = lean_nat_dec_le(v___x_911_, v___x_911_);
if (v___x_915_ == 0)
{
if (v___x_913_ == 0)
{
lean_object* v___x_916_; 
lean_dec(v___x_910_);
lean_dec_ref(v_tail_883_);
lean_dec(v_mvarId_872_);
lean_dec(v_fvarId_871_);
v___x_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_916_, 0, v___x_912_);
return v___x_916_;
}
else
{
size_t v___x_917_; size_t v___x_918_; lean_object* v___x_919_; 
v___x_917_ = lean_usize_of_nat(v___x_910_);
lean_dec(v___x_910_);
v___x_918_ = lean_usize_of_nat(v___x_911_);
v___x_919_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_871_, v_mvarId_872_, v_tail_883_, v___x_917_, v___x_918_, v___x_912_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
lean_dec_ref(v_tail_883_);
return v___x_919_;
}
}
else
{
size_t v___x_920_; size_t v___x_921_; lean_object* v___x_922_; 
v___x_920_ = lean_usize_of_nat(v___x_910_);
lean_dec(v___x_910_);
v___x_921_ = lean_usize_of_nat(v___x_911_);
v___x_922_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_871_, v_mvarId_872_, v_tail_883_, v___x_920_, v___x_921_, v___x_912_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
lean_dec_ref(v_tail_883_);
return v___x_922_;
}
}
}
}
else
{
lean_object* v___x_923_; 
v___x_923_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6(v_fvarId_871_, v_mvarId_872_, v_t_873_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
return v___x_923_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1___boxed(lean_object* v_fvarId_924_, lean_object* v_mvarId_925_, lean_object* v_t_926_, lean_object* v_start_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1(v_fvarId_924_, v_mvarId_925_, v_t_926_, v_start_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec(v_start_927_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1(lean_object* v_fvarId_934_, lean_object* v_mvarId_935_, lean_object* v_lctx_936_, lean_object* v_start_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
lean_object* v_decls_943_; lean_object* v___x_944_; 
v_decls_943_ = lean_ctor_get(v_lctx_936_, 1);
lean_inc_ref(v_decls_943_);
lean_dec_ref(v_lctx_936_);
v___x_944_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1(v_fvarId_934_, v_mvarId_935_, v_decls_943_, v_start_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1___boxed(lean_object* v_fvarId_945_, lean_object* v_mvarId_946_, lean_object* v_lctx_947_, lean_object* v_start_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1(v_fvarId_945_, v_mvarId_946_, v_lctx_947_, v_start_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
lean_dec(v_start_948_);
return v_res_954_;
}
}
static lean_object* _init_l_Lean_MVarId_clear___lam__1___closed__1(void){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = ((lean_object*)(l_Lean_MVarId_clear___lam__1___closed__0));
v___x_957_ = l_Lean_stringToMessageData(v___x_956_);
return v___x_957_;
}
}
static lean_object* _init_l_Lean_MVarId_clear___lam__1___closed__3(void){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = ((lean_object*)(l_Lean_MVarId_clear___lam__1___closed__2));
v___x_960_ = l_Lean_stringToMessageData(v___x_959_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clear___lam__1(lean_object* v_mvarId_961_, lean_object* v___x_962_, lean_object* v_fvarId_963_, lean_object* v___f_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v___x_1001_; 
lean_inc(v___x_962_);
lean_inc(v_mvarId_961_);
v___x_1001_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_961_, v___x_962_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_lctx_1002_; lean_object* v___y_1004_; lean_object* v___y_1005_; lean_object* v___y_1006_; lean_object* v___y_1007_; lean_object* v___y_1008_; lean_object* v___y_1009_; lean_object* v___y_1010_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1020_; uint8_t v___x_1077_; 
lean_dec_ref_known(v___x_1001_, 1);
v_lctx_1002_ = lean_ctor_get(v___y_965_, 2);
lean_inc_ref(v_lctx_1002_);
v___x_1077_ = l_Lean_LocalContext_contains(v_lctx_1002_, v_fvarId_963_);
if (v___x_1077_ == 0)
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1078_ = lean_obj_once(&l_Lean_MVarId_clear___lam__1___closed__3, &l_Lean_MVarId_clear___lam__1___closed__3_once, _init_l_Lean_MVarId_clear___lam__1___closed__3);
lean_inc(v_fvarId_963_);
v___x_1079_ = l_Lean_mkFVar(v_fvarId_963_);
v___x_1080_ = l_Lean_MessageData_ofExpr(v___x_1079_);
v___x_1081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1078_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
v___x_1082_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7);
v___x_1083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1081_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
v___x_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
lean_inc(v_mvarId_961_);
lean_inc(v___x_962_);
v___x_1085_ = l_Lean_Meta_throwTacticEx___redArg(v___x_962_, v_mvarId_961_, v___x_1084_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_dec_ref_known(v___x_1085_, 1);
v___y_1017_ = v___y_965_;
v___y_1018_ = v___y_966_;
v___y_1019_ = v___y_967_;
v___y_1020_ = v___y_968_;
goto v___jp_1016_;
}
else
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1093_; 
lean_dec_ref(v_lctx_1002_);
lean_dec_ref(v___y_965_);
lean_dec_ref(v___f_964_);
lean_dec(v_fvarId_963_);
lean_dec(v___x_962_);
lean_dec(v_mvarId_961_);
v_a_1086_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1088_ = v___x_1085_;
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1085_);
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
else
{
v___y_1017_ = v___y_965_;
v___y_1018_ = v___y_966_;
v___y_1019_ = v___y_967_;
v___y_1020_ = v___y_968_;
goto v___jp_1016_;
}
v___jp_1003_:
{
lean_object* v_localInstances_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v_localInstances_1011_ = lean_ctor_get(v___y_1007_, 3);
v___x_1012_ = lean_local_ctx_erase(v_lctx_1002_, v_fvarId_963_);
lean_inc(v___y_1004_);
v___x_1013_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_964_, v_localInstances_1011_, v___y_1004_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_inc_ref(v_localInstances_1011_);
v___y_971_ = v___y_1007_;
v___y_972_ = v___y_1008_;
v___y_973_ = v___x_1012_;
v___y_974_ = v___y_1004_;
v___y_975_ = v___y_1005_;
v___y_976_ = v___y_1006_;
v___y_977_ = v___y_1010_;
v___y_978_ = v___y_1009_;
v___y_979_ = v_localInstances_1011_;
goto v___jp_970_;
}
else
{
lean_object* v_val_1014_; lean_object* v___x_1015_; 
v_val_1014_ = lean_ctor_get(v___x_1013_, 0);
lean_inc(v_val_1014_);
lean_dec_ref_known(v___x_1013_, 1);
lean_inc_ref(v_localInstances_1011_);
v___x_1015_ = l_Array_eraseIdx___redArg(v_localInstances_1011_, v_val_1014_);
v___y_971_ = v___y_1007_;
v___y_972_ = v___y_1008_;
v___y_973_ = v___x_1012_;
v___y_974_ = v___y_1004_;
v___y_975_ = v___y_1005_;
v___y_976_ = v___y_1006_;
v___y_977_ = v___y_1010_;
v___y_978_ = v___y_1009_;
v___y_979_ = v___x_1015_;
goto v___jp_970_;
}
}
v___jp_1016_:
{
lean_object* v___x_1021_; 
lean_inc(v_mvarId_961_);
v___x_1021_ = l_Lean_MVarId_getTag(v_mvarId_961_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v_a_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_a_1022_);
lean_dec_ref_known(v___x_1021_, 1);
v___x_1023_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_lctx_1002_);
lean_inc(v_mvarId_961_);
lean_inc(v_fvarId_963_);
v___x_1024_ = l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1(v_fvarId_963_, v_mvarId_961_, v_lctx_1002_, v___x_1023_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v___x_1025_; 
lean_dec_ref_known(v___x_1024_, 1);
lean_inc(v_mvarId_961_);
v___x_1025_ = l_Lean_MVarId_getDecl(v_mvarId_961_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v_type_1027_; lean_object* v___x_1028_; lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1052_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_a_1026_);
lean_dec_ref_known(v___x_1025_, 1);
v_type_1027_ = lean_ctor_get(v_a_1026_, 2);
lean_inc_ref_n(v_type_1027_, 2);
lean_dec(v_a_1026_);
lean_inc(v_fvarId_963_);
v___x_1028_ = l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3___redArg(v_type_1027_, v_fvarId_963_, v___y_1018_);
v_a_1029_ = lean_ctor_get(v___x_1028_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1031_ = v___x_1028_;
v_isShared_1032_ = v_isSharedCheck_1052_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v___x_1028_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1052_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
uint8_t v___x_1033_; 
v___x_1033_ = lean_unbox(v_a_1029_);
lean_dec(v_a_1029_);
if (v___x_1033_ == 0)
{
lean_del_object(v___x_1031_);
lean_dec(v___x_962_);
v___y_1004_ = v___x_1023_;
v___y_1005_ = v_a_1022_;
v___y_1006_ = v_type_1027_;
v___y_1007_ = v___y_1017_;
v___y_1008_ = v___y_1018_;
v___y_1009_ = v___y_1019_;
v___y_1010_ = v___y_1020_;
goto v___jp_1003_;
}
else
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1041_; 
v___x_1034_ = lean_obj_once(&l_Lean_MVarId_clear___lam__1___closed__1, &l_Lean_MVarId_clear___lam__1___closed__1_once, _init_l_Lean_MVarId_clear___lam__1___closed__1);
lean_inc(v_fvarId_963_);
v___x_1035_ = l_Lean_mkFVar(v_fvarId_963_);
v___x_1036_ = l_Lean_MessageData_ofExpr(v___x_1035_);
v___x_1037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1034_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
v___x_1038_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7);
v___x_1039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1037_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
if (v_isShared_1032_ == 0)
{
lean_ctor_set_tag(v___x_1031_, 1);
lean_ctor_set(v___x_1031_, 0, v___x_1039_);
v___x_1041_ = v___x_1031_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1039_);
v___x_1041_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
lean_object* v___x_1042_; 
lean_inc(v_mvarId_961_);
v___x_1042_ = l_Lean_Meta_throwTacticEx___redArg(v___x_962_, v_mvarId_961_, v___x_1041_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_dec_ref_known(v___x_1042_, 1);
v___y_1004_ = v___x_1023_;
v___y_1005_ = v_a_1022_;
v___y_1006_ = v_type_1027_;
v___y_1007_ = v___y_1017_;
v___y_1008_ = v___y_1018_;
v___y_1009_ = v___y_1019_;
v___y_1010_ = v___y_1020_;
goto v___jp_1003_;
}
else
{
lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1050_; 
lean_dec_ref(v_type_1027_);
lean_dec(v_a_1022_);
lean_dec_ref(v___y_1017_);
lean_dec_ref(v_lctx_1002_);
lean_dec_ref(v___f_964_);
lean_dec(v_fvarId_963_);
lean_dec(v_mvarId_961_);
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1045_ = v___x_1042_;
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___x_1042_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1048_; 
if (v_isShared_1046_ == 0)
{
v___x_1048_ = v___x_1045_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_a_1043_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
lean_dec(v_a_1022_);
lean_dec_ref(v___y_1017_);
lean_dec_ref(v_lctx_1002_);
lean_dec_ref(v___f_964_);
lean_dec(v_fvarId_963_);
lean_dec(v___x_962_);
lean_dec(v_mvarId_961_);
v_a_1053_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1055_ = v___x_1025_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1025_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1053_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
}
else
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1068_; 
lean_dec(v_a_1022_);
lean_dec_ref(v___y_1017_);
lean_dec_ref(v_lctx_1002_);
lean_dec_ref(v___f_964_);
lean_dec(v_fvarId_963_);
lean_dec(v___x_962_);
lean_dec(v_mvarId_961_);
v_a_1061_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1063_ = v___x_1024_;
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1024_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1066_; 
if (v_isShared_1064_ == 0)
{
v___x_1066_ = v___x_1063_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1061_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
}
else
{
lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1076_; 
lean_dec_ref(v___y_1017_);
lean_dec_ref(v_lctx_1002_);
lean_dec_ref(v___f_964_);
lean_dec(v_fvarId_963_);
lean_dec(v___x_962_);
lean_dec(v_mvarId_961_);
v_a_1069_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1071_ = v___x_1021_;
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_dec(v___x_1021_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1074_; 
if (v_isShared_1072_ == 0)
{
v___x_1074_ = v___x_1071_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_a_1069_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
}
}
else
{
lean_object* v_a_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1101_; 
lean_dec_ref(v___y_965_);
lean_dec_ref(v___f_964_);
lean_dec(v_fvarId_963_);
lean_dec(v___x_962_);
lean_dec(v_mvarId_961_);
v_a_1094_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1096_ = v___x_1001_;
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_a_1094_);
lean_dec(v___x_1001_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1099_; 
if (v_isShared_1097_ == 0)
{
v___x_1099_ = v___x_1096_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_a_1094_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
v___jp_970_:
{
uint8_t v___x_980_; lean_object* v___x_981_; 
v___x_980_ = 2;
v___x_981_ = l_Lean_Meta_mkFreshExprMVarAt(v___y_973_, v___y_979_, v___y_976_, v___x_980_, v___y_975_, v___y_974_, v___y_971_, v___y_972_, v___y_978_, v___y_977_);
lean_dec_ref(v___y_971_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v_a_982_; lean_object* v___x_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_991_; 
v_a_982_ = lean_ctor_get(v___x_981_, 0);
lean_inc_n(v_a_982_, 2);
lean_dec_ref_known(v___x_981_, 1);
v___x_983_ = l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg(v_mvarId_961_, v_a_982_, v___y_972_);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_991_ == 0)
{
lean_object* v_unused_992_; 
v_unused_992_ = lean_ctor_get(v___x_983_, 0);
lean_dec(v_unused_992_);
v___x_985_ = v___x_983_;
v_isShared_986_ = v_isSharedCheck_991_;
goto v_resetjp_984_;
}
else
{
lean_dec(v___x_983_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_991_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_987_; lean_object* v___x_989_; 
v___x_987_ = l_Lean_Expr_mvarId_x21(v_a_982_);
lean_dec(v_a_982_);
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 0, v___x_987_);
v___x_989_ = v___x_985_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v___x_987_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
else
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
lean_dec(v_mvarId_961_);
v_a_993_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_995_ = v___x_981_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_981_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_993_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clear___lam__1___boxed(lean_object* v_mvarId_1102_, lean_object* v___x_1103_, lean_object* v_fvarId_1104_, lean_object* v___f_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Lean_MVarId_clear___lam__1(v_mvarId_1102_, v___x_1103_, v_fvarId_1104_, v___f_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
lean_dec(v___y_1107_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clear(lean_object* v_mvarId_1112_, lean_object* v_fvarId_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_){
_start:
{
lean_object* v___f_1119_; lean_object* v___x_1120_; lean_object* v___f_1121_; lean_object* v___x_1122_; 
lean_inc(v_fvarId_1113_);
v___f_1119_ = lean_alloc_closure((void*)(l_Lean_MVarId_clear___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1119_, 0, v_fvarId_1113_);
v___x_1120_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__1));
lean_inc(v_mvarId_1112_);
v___f_1121_ = lean_alloc_closure((void*)(l_Lean_MVarId_clear___lam__1___boxed), 9, 4);
lean_closure_set(v___f_1121_, 0, v_mvarId_1112_);
lean_closure_set(v___f_1121_, 1, v___x_1120_);
lean_closure_set(v___f_1121_, 2, v_fvarId_1113_);
lean_closure_set(v___f_1121_, 3, v___f_1119_);
v___x_1122_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg(v_mvarId_1112_, v___f_1121_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clear___boxed(lean_object* v_mvarId_1123_, lean_object* v_fvarId_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l_Lean_MVarId_clear(v_mvarId_1123_, v_fvarId_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_);
lean_dec(v_a_1128_);
lean_dec_ref(v_a_1127_);
lean_dec(v_a_1126_);
lean_dec_ref(v_a_1125_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2(lean_object* v_mvarId_1131_, lean_object* v_val_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg(v_mvarId_1131_, v_val_1132_, v___y_1134_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___boxed(lean_object* v_mvarId_1139_, lean_object* v_val_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2(v_mvarId_1139_, v_val_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3(lean_object* v_00_u03b2_1147_, lean_object* v_x_1148_, lean_object* v_x_1149_, lean_object* v_x_1150_){
_start:
{
lean_object* v___x_1151_; 
v___x_1151_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3___redArg(v_x_1148_, v_x_1149_, v_x_1150_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9(lean_object* v_00_u03b2_1152_, lean_object* v_x_1153_, size_t v_x_1154_, size_t v_x_1155_, lean_object* v_x_1156_, lean_object* v_x_1157_){
_start:
{
lean_object* v___x_1158_; 
v___x_1158_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_x_1153_, v_x_1154_, v_x_1155_, v_x_1156_, v_x_1157_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___boxed(lean_object* v_00_u03b2_1159_, lean_object* v_x_1160_, lean_object* v_x_1161_, lean_object* v_x_1162_, lean_object* v_x_1163_, lean_object* v_x_1164_){
_start:
{
size_t v_x_10188__boxed_1165_; size_t v_x_10189__boxed_1166_; lean_object* v_res_1167_; 
v_x_10188__boxed_1165_ = lean_unbox_usize(v_x_1161_);
lean_dec(v_x_1161_);
v_x_10189__boxed_1166_ = lean_unbox_usize(v_x_1162_);
lean_dec(v_x_1162_);
v_res_1167_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9(v_00_u03b2_1159_, v_x_1160_, v_x_10188__boxed_1165_, v_x_10189__boxed_1166_, v_x_1163_, v_x_1164_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13(lean_object* v_00_u03b2_1168_, lean_object* v_n_1169_, lean_object* v_k_1170_, lean_object* v_v_1171_){
_start:
{
lean_object* v___x_1172_; 
v___x_1172_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13___redArg(v_n_1169_, v_k_1170_, v_v_1171_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14(lean_object* v_00_u03b2_1173_, size_t v_depth_1174_, lean_object* v_keys_1175_, lean_object* v_vals_1176_, lean_object* v_heq_1177_, lean_object* v_i_1178_, lean_object* v_entries_1179_){
_start:
{
lean_object* v___x_1180_; 
v___x_1180_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg(v_depth_1174_, v_keys_1175_, v_vals_1176_, v_i_1178_, v_entries_1179_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___boxed(lean_object* v_00_u03b2_1181_, lean_object* v_depth_1182_, lean_object* v_keys_1183_, lean_object* v_vals_1184_, lean_object* v_heq_1185_, lean_object* v_i_1186_, lean_object* v_entries_1187_){
_start:
{
size_t v_depth_boxed_1188_; lean_object* v_res_1189_; 
v_depth_boxed_1188_ = lean_unbox_usize(v_depth_1182_);
lean_dec(v_depth_1182_);
v_res_1189_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14(v_00_u03b2_1181_, v_depth_boxed_1188_, v_keys_1183_, v_vals_1184_, v_heq_1185_, v_i_1186_, v_entries_1187_);
lean_dec_ref(v_vals_1184_);
lean_dec_ref(v_keys_1183_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13_spec__14(lean_object* v_00_u03b2_1190_, lean_object* v_x_1191_, lean_object* v_x_1192_, lean_object* v_x_1193_, lean_object* v_x_1194_){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13_spec__14___redArg(v_x_1191_, v_x_1192_, v_x_1193_, v_x_1194_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClear(lean_object* v_mvarId_1196_, lean_object* v_fvarId_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = l_Lean_Meta_saveState___redArg(v_a_1199_, v_a_1201_);
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_object* v_a_1204_; lean_object* v___x_1205_; 
v_a_1204_ = lean_ctor_get(v___x_1203_, 0);
lean_inc(v_a_1204_);
lean_dec_ref_known(v___x_1203_, 1);
lean_inc(v_mvarId_1196_);
v___x_1205_ = l_Lean_MVarId_clear(v_mvarId_1196_, v_fvarId_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_dec(v_a_1204_);
lean_dec(v_mvarId_1196_);
return v___x_1205_;
}
else
{
lean_object* v_a_1206_; uint8_t v___y_1208_; uint8_t v___x_1226_; 
v_a_1206_ = lean_ctor_get(v___x_1205_, 0);
lean_inc(v_a_1206_);
v___x_1226_ = l_Lean_Exception_isInterrupt(v_a_1206_);
if (v___x_1226_ == 0)
{
uint8_t v___x_1227_; 
v___x_1227_ = l_Lean_Exception_isRuntime(v_a_1206_);
v___y_1208_ = v___x_1227_;
goto v___jp_1207_;
}
else
{
lean_dec(v_a_1206_);
v___y_1208_ = v___x_1226_;
goto v___jp_1207_;
}
v___jp_1207_:
{
if (v___y_1208_ == 0)
{
lean_object* v___x_1209_; 
lean_dec_ref_known(v___x_1205_, 1);
v___x_1209_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1204_, v_a_1199_, v_a_1201_);
lean_dec(v_a_1204_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1216_ == 0)
{
lean_object* v_unused_1217_; 
v_unused_1217_ = lean_ctor_get(v___x_1209_, 0);
lean_dec(v_unused_1217_);
v___x_1211_ = v___x_1209_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_dec(v___x_1209_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
lean_ctor_set(v___x_1211_, 0, v_mvarId_1196_);
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_mvarId_1196_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
else
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1225_; 
lean_dec(v_mvarId_1196_);
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
else
{
lean_dec(v_a_1204_);
lean_dec(v_mvarId_1196_);
return v___x_1205_;
}
}
}
}
else
{
lean_object* v_a_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1235_; 
lean_dec(v_fvarId_1197_);
lean_dec(v_mvarId_1196_);
v_a_1228_ = lean_ctor_get(v___x_1203_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1230_ = v___x_1203_;
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_a_1228_);
lean_dec(v___x_1203_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1233_; 
if (v_isShared_1231_ == 0)
{
v___x_1233_ = v___x_1230_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_a_1228_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClear___boxed(lean_object* v_mvarId_1236_, lean_object* v_fvarId_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l_Lean_MVarId_tryClear(v_mvarId_1236_, v_fvarId_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_);
lean_dec(v_a_1241_);
lean_dec_ref(v_a_1240_);
lean_dec(v_a_1239_);
lean_dec_ref(v_a_1238_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0(lean_object* v_as_1244_, size_t v_i_1245_, size_t v_stop_1246_, lean_object* v_b_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
uint8_t v___x_1253_; 
v___x_1253_ = lean_usize_dec_eq(v_i_1245_, v_stop_1246_);
if (v___x_1253_ == 0)
{
size_t v___x_1254_; size_t v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1254_ = ((size_t)1ULL);
v___x_1255_ = lean_usize_sub(v_i_1245_, v___x_1254_);
v___x_1256_ = lean_array_uget_borrowed(v_as_1244_, v___x_1255_);
lean_inc(v___x_1256_);
v___x_1257_ = l_Lean_MVarId_tryClear(v_b_1247_, v___x_1256_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v_a_1258_; 
v_a_1258_ = lean_ctor_get(v___x_1257_, 0);
lean_inc(v_a_1258_);
lean_dec_ref_known(v___x_1257_, 1);
v_i_1245_ = v___x_1255_;
v_b_1247_ = v_a_1258_;
goto _start;
}
else
{
return v___x_1257_;
}
}
else
{
lean_object* v___x_1260_; 
v___x_1260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1260_, 0, v_b_1247_);
return v___x_1260_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0___boxed(lean_object* v_as_1261_, lean_object* v_i_1262_, lean_object* v_stop_1263_, lean_object* v_b_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
size_t v_i_boxed_1270_; size_t v_stop_boxed_1271_; lean_object* v_res_1272_; 
v_i_boxed_1270_ = lean_unbox_usize(v_i_1262_);
lean_dec(v_i_1262_);
v_stop_boxed_1271_ = lean_unbox_usize(v_stop_1263_);
lean_dec(v_stop_1263_);
v_res_1272_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0(v_as_1261_, v_i_boxed_1270_, v_stop_boxed_1271_, v_b_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec_ref(v_as_1261_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany(lean_object* v_mvarId_1273_, lean_object* v_fvarIds_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_){
_start:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; uint8_t v___x_1282_; 
v___x_1280_ = lean_array_get_size(v_fvarIds_1274_);
v___x_1281_ = lean_unsigned_to_nat(0u);
v___x_1282_ = lean_nat_dec_lt(v___x_1281_, v___x_1280_);
if (v___x_1282_ == 0)
{
lean_object* v___x_1283_; 
v___x_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1283_, 0, v_mvarId_1273_);
return v___x_1283_;
}
else
{
size_t v___x_1284_; size_t v___x_1285_; lean_object* v___x_1286_; 
v___x_1284_ = lean_usize_of_nat(v___x_1280_);
v___x_1285_ = ((size_t)0ULL);
v___x_1286_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0(v_fvarIds_1274_, v___x_1284_, v___x_1285_, v_mvarId_1273_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_);
return v___x_1286_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany___boxed(lean_object* v_mvarId_1287_, lean_object* v_fvarIds_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l_Lean_MVarId_tryClearMany(v_mvarId_1287_, v_fvarIds_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_);
lean_dec(v_a_1292_);
lean_dec_ref(v_a_1291_);
lean_dec(v_a_1290_);
lean_dec_ref(v_a_1289_);
lean_dec_ref(v_fvarIds_1288_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0(lean_object* v_as_1295_, size_t v_i_1296_, size_t v_stop_1297_, lean_object* v_b_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
uint8_t v___x_1304_; 
v___x_1304_ = lean_usize_dec_eq(v_i_1296_, v_stop_1297_);
if (v___x_1304_ == 0)
{
lean_object* v_fst_1305_; lean_object* v_snd_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1331_; 
v_fst_1305_ = lean_ctor_get(v_b_1298_, 0);
v_snd_1306_ = lean_ctor_get(v_b_1298_, 1);
v_isSharedCheck_1331_ = !lean_is_exclusive(v_b_1298_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1308_ = v_b_1298_;
v_isShared_1309_ = v_isSharedCheck_1331_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_snd_1306_);
lean_inc(v_fst_1305_);
lean_dec(v_b_1298_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1331_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
size_t v___x_1310_; size_t v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1310_ = ((size_t)1ULL);
v___x_1311_ = lean_usize_sub(v_i_1296_, v___x_1310_);
v___x_1312_ = lean_array_uget_borrowed(v_as_1295_, v___x_1311_);
lean_inc(v___x_1312_);
lean_inc(v_fst_1305_);
v___x_1313_ = l_Lean_MVarId_tryClear(v_fst_1305_, v___x_1312_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_object* v_a_1314_; lean_object* v___y_1316_; uint8_t v___x_1321_; 
v_a_1314_ = lean_ctor_get(v___x_1313_, 0);
lean_inc(v_a_1314_);
lean_dec_ref_known(v___x_1313_, 1);
v___x_1321_ = l_Lean_instBEqMVarId_beq(v_fst_1305_, v_a_1314_);
lean_dec(v_fst_1305_);
if (v___x_1321_ == 0)
{
lean_object* v___x_1322_; 
lean_inc(v___x_1312_);
v___x_1322_ = lean_array_push(v_snd_1306_, v___x_1312_);
v___y_1316_ = v___x_1322_;
goto v___jp_1315_;
}
else
{
v___y_1316_ = v_snd_1306_;
goto v___jp_1315_;
}
v___jp_1315_:
{
lean_object* v___x_1318_; 
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 1, v___y_1316_);
lean_ctor_set(v___x_1308_, 0, v_a_1314_);
v___x_1318_ = v___x_1308_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_a_1314_);
lean_ctor_set(v_reuseFailAlloc_1320_, 1, v___y_1316_);
v___x_1318_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
v_i_1296_ = v___x_1311_;
v_b_1298_ = v___x_1318_;
goto _start;
}
}
}
else
{
lean_object* v_a_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1330_; 
lean_del_object(v___x_1308_);
lean_dec(v_snd_1306_);
lean_dec(v_fst_1305_);
v_a_1323_ = lean_ctor_get(v___x_1313_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1325_ = v___x_1313_;
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_a_1323_);
lean_dec(v___x_1313_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1328_; 
if (v_isShared_1326_ == 0)
{
v___x_1328_ = v___x_1325_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_a_1323_);
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
lean_object* v___x_1332_; 
v___x_1332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1332_, 0, v_b_1298_);
return v___x_1332_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0___boxed(lean_object* v_as_1333_, lean_object* v_i_1334_, lean_object* v_stop_1335_, lean_object* v_b_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
size_t v_i_boxed_1342_; size_t v_stop_boxed_1343_; lean_object* v_res_1344_; 
v_i_boxed_1342_ = lean_unbox_usize(v_i_1334_);
lean_dec(v_i_1334_);
v_stop_boxed_1343_ = lean_unbox_usize(v_stop_1335_);
lean_dec(v_stop_1335_);
v_res_1344_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0(v_as_1333_, v_i_boxed_1342_, v_stop_boxed_1343_, v_b_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec_ref(v_as_1333_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany_x27___lam__0(lean_object* v_fvarIds_1345_, lean_object* v_goal_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v_lctx_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; uint8_t v___x_1358_; 
v_lctx_1352_ = lean_ctor_get(v___y_1347_, 2);
v___x_1353_ = l_Lean_LocalContext_sortFVarsByContextOrder(v_lctx_1352_, v_fvarIds_1345_);
v___x_1354_ = lean_array_get_size(v___x_1353_);
v___x_1355_ = lean_mk_empty_array_with_capacity(v___x_1354_);
v___x_1356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1356_, 0, v_goal_1346_);
lean_ctor_set(v___x_1356_, 1, v___x_1355_);
v___x_1357_ = lean_unsigned_to_nat(0u);
v___x_1358_ = lean_nat_dec_lt(v___x_1357_, v___x_1354_);
if (v___x_1358_ == 0)
{
lean_object* v___x_1359_; 
lean_dec_ref(v___x_1353_);
v___x_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1356_);
return v___x_1359_;
}
else
{
size_t v___x_1360_; size_t v___x_1361_; lean_object* v___x_1362_; 
v___x_1360_ = lean_usize_of_nat(v___x_1354_);
v___x_1361_ = ((size_t)0ULL);
v___x_1362_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0(v___x_1353_, v___x_1360_, v___x_1361_, v___x_1356_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
lean_dec_ref(v___x_1353_);
return v___x_1362_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany_x27___lam__0___boxed(lean_object* v_fvarIds_1363_, lean_object* v_goal_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
lean_object* v_res_1370_; 
v_res_1370_ = l_Lean_MVarId_tryClearMany_x27___lam__0(v_fvarIds_1363_, v_goal_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany_x27(lean_object* v_goal_1371_, lean_object* v_fvarIds_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_){
_start:
{
lean_object* v___f_1378_; lean_object* v___x_1379_; 
lean_inc(v_goal_1371_);
v___f_1378_ = lean_alloc_closure((void*)(l_Lean_MVarId_tryClearMany_x27___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1378_, 0, v_fvarIds_1372_);
lean_closure_set(v___f_1378_, 1, v_goal_1371_);
v___x_1379_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg(v_goal_1371_, v___f_1378_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany_x27___boxed(lean_object* v_goal_1380_, lean_object* v_fvarIds_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_Lean_MVarId_tryClearMany_x27(v_goal_1380_, v_fvarIds_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_);
lean_dec(v_a_1385_);
lean_dec_ref(v_a_1384_);
lean_dec(v_a_1383_);
lean_dec_ref(v_a_1382_);
return v_res_1387_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Util(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Clear(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
