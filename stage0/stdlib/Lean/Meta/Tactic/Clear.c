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
size_t lean_usize_shift_left(size_t, size_t);
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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
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
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__2;
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
uint8_t v_fst_26_; lean_object* v_snd_27_; lean_object* v___y_46_; lean_object* v___f_50_; lean_object* v___f_51_; 
v___f_50_ = lean_alloc_closure((void*)(l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_50_, 0, v_fvarId_21_);
v___f_51_ = ((lean_object*)(l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__0));
if (lean_obj_tag(v_localDecl_20_) == 0)
{
lean_object* v_type_52_; lean_object* v___x_53_; uint8_t v_fst_55_; lean_object* v_mctx_56_; lean_object* v___y_74_; lean_object* v_mctx_79_; lean_object* v___x_80_; lean_object* v___x_81_; uint8_t v___x_82_; 
v_type_52_ = lean_ctor_get(v_localDecl_20_, 3);
lean_inc_ref(v_type_52_);
lean_dec_ref(v_localDecl_20_);
v___x_53_ = lean_st_ref_get(v___y_23_);
v_mctx_79_ = lean_ctor_get(v___x_53_, 0);
lean_inc_ref_n(v_mctx_79_, 2);
lean_dec(v___x_53_);
v___x_80_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2);
v___x_81_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
lean_ctor_set(v___x_81_, 1, v_mctx_79_);
v___x_82_ = l_Lean_Expr_hasFVar(v_type_52_);
if (v___x_82_ == 0)
{
uint8_t v___x_83_; 
v___x_83_ = l_Lean_Expr_hasMVar(v_type_52_);
if (v___x_83_ == 0)
{
lean_dec_ref(v___x_81_);
lean_dec_ref(v_type_52_);
lean_dec_ref(v___f_50_);
v_fst_55_ = v___x_83_;
v_mctx_56_ = v_mctx_79_;
goto v___jp_54_;
}
else
{
lean_object* v___x_84_; 
lean_dec_ref(v_mctx_79_);
v___x_84_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_50_, v___f_51_, v_type_52_, v___x_81_);
v___y_74_ = v___x_84_;
goto v___jp_73_;
}
}
else
{
lean_object* v___x_85_; 
lean_dec_ref(v_mctx_79_);
v___x_85_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_50_, v___f_51_, v_type_52_, v___x_81_);
v___y_74_ = v___x_85_;
goto v___jp_73_;
}
v___jp_54_:
{
lean_object* v___x_57_; lean_object* v_cache_58_; lean_object* v_zetaDeltaFVarIds_59_; lean_object* v_postponed_60_; lean_object* v_diag_61_; lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_71_; 
v___x_57_ = lean_st_ref_take(v___y_23_);
v_cache_58_ = lean_ctor_get(v___x_57_, 1);
v_zetaDeltaFVarIds_59_ = lean_ctor_get(v___x_57_, 2);
v_postponed_60_ = lean_ctor_get(v___x_57_, 3);
v_diag_61_ = lean_ctor_get(v___x_57_, 4);
v_isSharedCheck_71_ = !lean_is_exclusive(v___x_57_);
if (v_isSharedCheck_71_ == 0)
{
lean_object* v_unused_72_; 
v_unused_72_ = lean_ctor_get(v___x_57_, 0);
lean_dec(v_unused_72_);
v___x_63_ = v___x_57_;
v_isShared_64_ = v_isSharedCheck_71_;
goto v_resetjp_62_;
}
else
{
lean_inc(v_diag_61_);
lean_inc(v_postponed_60_);
lean_inc(v_zetaDeltaFVarIds_59_);
lean_inc(v_cache_58_);
lean_dec(v___x_57_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_71_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
lean_object* v___x_66_; 
if (v_isShared_64_ == 0)
{
lean_ctor_set(v___x_63_, 0, v_mctx_56_);
v___x_66_ = v___x_63_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v_mctx_56_);
lean_ctor_set(v_reuseFailAlloc_70_, 1, v_cache_58_);
lean_ctor_set(v_reuseFailAlloc_70_, 2, v_zetaDeltaFVarIds_59_);
lean_ctor_set(v_reuseFailAlloc_70_, 3, v_postponed_60_);
lean_ctor_set(v_reuseFailAlloc_70_, 4, v_diag_61_);
v___x_66_ = v_reuseFailAlloc_70_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_67_ = lean_st_ref_set(v___y_23_, v___x_66_);
v___x_68_ = lean_box(v_fst_55_);
v___x_69_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
return v___x_69_;
}
}
}
v___jp_73_:
{
lean_object* v_snd_75_; lean_object* v_fst_76_; lean_object* v_mctx_77_; uint8_t v___x_78_; 
v_snd_75_ = lean_ctor_get(v___y_74_, 1);
lean_inc(v_snd_75_);
v_fst_76_ = lean_ctor_get(v___y_74_, 0);
lean_inc(v_fst_76_);
lean_dec_ref(v___y_74_);
v_mctx_77_ = lean_ctor_get(v_snd_75_, 1);
lean_inc_ref(v_mctx_77_);
lean_dec(v_snd_75_);
v___x_78_ = lean_unbox(v_fst_76_);
lean_dec(v_fst_76_);
v_fst_55_ = v___x_78_;
v_mctx_56_ = v_mctx_77_;
goto v___jp_54_;
}
}
else
{
lean_object* v_type_86_; lean_object* v_value_87_; uint8_t v_nondep_88_; uint8_t v_fst_90_; lean_object* v_snd_91_; lean_object* v___y_97_; 
v_type_86_ = lean_ctor_get(v_localDecl_20_, 3);
lean_inc_ref(v_type_86_);
v_value_87_ = lean_ctor_get(v_localDecl_20_, 4);
lean_inc_ref(v_value_87_);
v_nondep_88_ = lean_ctor_get_uint8(v_localDecl_20_, sizeof(void*)*5);
lean_dec_ref(v_localDecl_20_);
if (v_generalizeNondepLet_22_ == 0)
{
goto v___jp_101_;
}
else
{
if (v_nondep_88_ == 0)
{
goto v___jp_101_;
}
else
{
lean_object* v___x_110_; uint8_t v_fst_112_; lean_object* v_mctx_113_; lean_object* v___y_131_; lean_object* v_mctx_136_; lean_object* v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; 
lean_dec_ref(v_value_87_);
v___x_110_ = lean_st_ref_get(v___y_23_);
v_mctx_136_ = lean_ctor_get(v___x_110_, 0);
lean_inc_ref_n(v_mctx_136_, 2);
lean_dec(v___x_110_);
v___x_137_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2);
v___x_138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
lean_ctor_set(v___x_138_, 1, v_mctx_136_);
v___x_139_ = l_Lean_Expr_hasFVar(v_type_86_);
if (v___x_139_ == 0)
{
uint8_t v___x_140_; 
v___x_140_ = l_Lean_Expr_hasMVar(v_type_86_);
if (v___x_140_ == 0)
{
lean_dec_ref(v___x_138_);
lean_dec_ref(v_type_86_);
lean_dec_ref(v___f_50_);
v_fst_112_ = v___x_140_;
v_mctx_113_ = v_mctx_136_;
goto v___jp_111_;
}
else
{
lean_object* v___x_141_; 
lean_dec_ref(v_mctx_136_);
v___x_141_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_50_, v___f_51_, v_type_86_, v___x_138_);
v___y_131_ = v___x_141_;
goto v___jp_130_;
}
}
else
{
lean_object* v___x_142_; 
lean_dec_ref(v_mctx_136_);
v___x_142_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_50_, v___f_51_, v_type_86_, v___x_138_);
v___y_131_ = v___x_142_;
goto v___jp_130_;
}
v___jp_111_:
{
lean_object* v___x_114_; lean_object* v_cache_115_; lean_object* v_zetaDeltaFVarIds_116_; lean_object* v_postponed_117_; lean_object* v_diag_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_128_; 
v___x_114_ = lean_st_ref_take(v___y_23_);
v_cache_115_ = lean_ctor_get(v___x_114_, 1);
v_zetaDeltaFVarIds_116_ = lean_ctor_get(v___x_114_, 2);
v_postponed_117_ = lean_ctor_get(v___x_114_, 3);
v_diag_118_ = lean_ctor_get(v___x_114_, 4);
v_isSharedCheck_128_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_128_ == 0)
{
lean_object* v_unused_129_; 
v_unused_129_ = lean_ctor_get(v___x_114_, 0);
lean_dec(v_unused_129_);
v___x_120_ = v___x_114_;
v_isShared_121_ = v_isSharedCheck_128_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_diag_118_);
lean_inc(v_postponed_117_);
lean_inc(v_zetaDeltaFVarIds_116_);
lean_inc(v_cache_115_);
lean_dec(v___x_114_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_128_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_123_; 
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 0, v_mctx_113_);
v___x_123_ = v___x_120_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_mctx_113_);
lean_ctor_set(v_reuseFailAlloc_127_, 1, v_cache_115_);
lean_ctor_set(v_reuseFailAlloc_127_, 2, v_zetaDeltaFVarIds_116_);
lean_ctor_set(v_reuseFailAlloc_127_, 3, v_postponed_117_);
lean_ctor_set(v_reuseFailAlloc_127_, 4, v_diag_118_);
v___x_123_ = v_reuseFailAlloc_127_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_124_ = lean_st_ref_set(v___y_23_, v___x_123_);
v___x_125_ = lean_box(v_fst_112_);
v___x_126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
return v___x_126_;
}
}
}
v___jp_130_:
{
lean_object* v_snd_132_; lean_object* v_fst_133_; lean_object* v_mctx_134_; uint8_t v___x_135_; 
v_snd_132_ = lean_ctor_get(v___y_131_, 1);
lean_inc(v_snd_132_);
v_fst_133_ = lean_ctor_get(v___y_131_, 0);
lean_inc(v_fst_133_);
lean_dec_ref(v___y_131_);
v_mctx_134_ = lean_ctor_get(v_snd_132_, 1);
lean_inc_ref(v_mctx_134_);
lean_dec(v_snd_132_);
v___x_135_ = lean_unbox(v_fst_133_);
lean_dec(v_fst_133_);
v_fst_112_ = v___x_135_;
v_mctx_113_ = v_mctx_134_;
goto v___jp_111_;
}
}
}
v___jp_89_:
{
if (v_fst_90_ == 0)
{
uint8_t v___x_92_; 
v___x_92_ = l_Lean_Expr_hasFVar(v_value_87_);
if (v___x_92_ == 0)
{
uint8_t v___x_93_; 
v___x_93_ = l_Lean_Expr_hasMVar(v_value_87_);
if (v___x_93_ == 0)
{
lean_dec_ref(v_value_87_);
lean_dec_ref(v___f_50_);
v_fst_26_ = v___x_93_;
v_snd_27_ = v_snd_91_;
goto v___jp_25_;
}
else
{
lean_object* v___x_94_; 
v___x_94_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_50_, v___f_51_, v_value_87_, v_snd_91_);
v___y_46_ = v___x_94_;
goto v___jp_45_;
}
}
else
{
lean_object* v___x_95_; 
v___x_95_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_50_, v___f_51_, v_value_87_, v_snd_91_);
v___y_46_ = v___x_95_;
goto v___jp_45_;
}
}
else
{
lean_dec_ref(v_value_87_);
lean_dec_ref(v___f_50_);
v_fst_26_ = v_fst_90_;
v_snd_27_ = v_snd_91_;
goto v___jp_25_;
}
}
v___jp_96_:
{
lean_object* v_fst_98_; lean_object* v_snd_99_; uint8_t v___x_100_; 
v_fst_98_ = lean_ctor_get(v___y_97_, 0);
lean_inc(v_fst_98_);
v_snd_99_ = lean_ctor_get(v___y_97_, 1);
lean_inc(v_snd_99_);
lean_dec_ref(v___y_97_);
v___x_100_ = lean_unbox(v_fst_98_);
lean_dec(v_fst_98_);
v_fst_90_ = v___x_100_;
v_snd_91_ = v_snd_99_;
goto v___jp_89_;
}
v___jp_101_:
{
lean_object* v___x_102_; lean_object* v_mctx_103_; lean_object* v___x_104_; lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_102_ = lean_st_ref_get(v___y_23_);
v_mctx_103_ = lean_ctor_get(v___x_102_, 0);
lean_inc_ref(v_mctx_103_);
lean_dec(v___x_102_);
v___x_104_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2);
v___x_105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
lean_ctor_set(v___x_105_, 1, v_mctx_103_);
v___x_106_ = l_Lean_Expr_hasFVar(v_type_86_);
if (v___x_106_ == 0)
{
uint8_t v___x_107_; 
v___x_107_ = l_Lean_Expr_hasMVar(v_type_86_);
if (v___x_107_ == 0)
{
lean_dec_ref(v_type_86_);
v_fst_90_ = v___x_107_;
v_snd_91_ = v___x_105_;
goto v___jp_89_;
}
else
{
lean_object* v___x_108_; 
lean_inc_ref(v___f_50_);
v___x_108_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_50_, v___f_51_, v_type_86_, v___x_105_);
v___y_97_ = v___x_108_;
goto v___jp_96_;
}
}
else
{
lean_object* v___x_109_; 
lean_inc_ref(v___f_50_);
v___x_109_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_50_, v___f_51_, v_type_86_, v___x_105_);
v___y_97_ = v___x_109_;
goto v___jp_96_;
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
v___jp_45_:
{
lean_object* v_fst_47_; lean_object* v_snd_48_; uint8_t v___x_49_; 
v_fst_47_ = lean_ctor_get(v___y_46_, 0);
lean_inc(v_fst_47_);
v_snd_48_ = lean_ctor_get(v___y_46_, 1);
lean_inc(v_snd_48_);
lean_dec_ref(v___y_46_);
v___x_49_ = lean_unbox(v_fst_47_);
lean_dec(v_fst_47_);
v_fst_26_ = v___x_49_;
v_snd_27_ = v_snd_48_;
goto v___jp_25_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___boxed(lean_object* v_localDecl_143_, lean_object* v_fvarId_144_, lean_object* v_generalizeNondepLet_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
uint8_t v_generalizeNondepLet_boxed_148_; lean_object* v_res_149_; 
v_generalizeNondepLet_boxed_148_ = lean_unbox(v_generalizeNondepLet_145_);
v_res_149_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg(v_localDecl_143_, v_fvarId_144_, v_generalizeNondepLet_boxed_148_, v___y_146_);
lean_dec(v___y_146_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0(lean_object* v_localDecl_150_, lean_object* v_fvarId_151_, uint8_t v_generalizeNondepLet_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg(v_localDecl_150_, v_fvarId_151_, v_generalizeNondepLet_152_, v___y_154_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___boxed(lean_object* v_localDecl_159_, lean_object* v_fvarId_160_, lean_object* v_generalizeNondepLet_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_){
_start:
{
uint8_t v_generalizeNondepLet_boxed_167_; lean_object* v_res_168_; 
v_generalizeNondepLet_boxed_167_ = lean_unbox(v_generalizeNondepLet_161_);
v_res_168_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0(v_localDecl_159_, v_fvarId_160_, v_generalizeNondepLet_boxed_167_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3___redArg(lean_object* v_e_169_, lean_object* v_fvarId_170_, lean_object* v___y_171_){
_start:
{
lean_object* v___x_173_; uint8_t v_fst_175_; lean_object* v_mctx_176_; lean_object* v___y_194_; lean_object* v_mctx_199_; lean_object* v___f_200_; lean_object* v___f_201_; lean_object* v___x_202_; lean_object* v___x_203_; uint8_t v___x_204_; 
v___x_173_ = lean_st_ref_get(v___y_171_);
v_mctx_199_ = lean_ctor_get(v___x_173_, 0);
lean_inc_ref_n(v_mctx_199_, 2);
lean_dec(v___x_173_);
v___f_200_ = ((lean_object*)(l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__0));
v___f_201_ = lean_alloc_closure((void*)(l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_201_, 0, v_fvarId_170_);
v___x_202_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2);
v___x_203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
lean_ctor_set(v___x_203_, 1, v_mctx_199_);
v___x_204_ = l_Lean_Expr_hasFVar(v_e_169_);
if (v___x_204_ == 0)
{
uint8_t v___x_205_; 
v___x_205_ = l_Lean_Expr_hasMVar(v_e_169_);
if (v___x_205_ == 0)
{
lean_dec_ref(v___x_203_);
lean_dec_ref(v___f_201_);
lean_dec_ref(v_e_169_);
v_fst_175_ = v___x_205_;
v_mctx_176_ = v_mctx_199_;
goto v___jp_174_;
}
else
{
lean_object* v___x_206_; 
lean_dec_ref(v_mctx_199_);
v___x_206_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_201_, v___f_200_, v_e_169_, v___x_203_);
v___y_194_ = v___x_206_;
goto v___jp_193_;
}
}
else
{
lean_object* v___x_207_; 
lean_dec_ref(v_mctx_199_);
v___x_207_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_201_, v___f_200_, v_e_169_, v___x_203_);
v___y_194_ = v___x_207_;
goto v___jp_193_;
}
v___jp_174_:
{
lean_object* v___x_177_; lean_object* v_cache_178_; lean_object* v_zetaDeltaFVarIds_179_; lean_object* v_postponed_180_; lean_object* v_diag_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_191_; 
v___x_177_ = lean_st_ref_take(v___y_171_);
v_cache_178_ = lean_ctor_get(v___x_177_, 1);
v_zetaDeltaFVarIds_179_ = lean_ctor_get(v___x_177_, 2);
v_postponed_180_ = lean_ctor_get(v___x_177_, 3);
v_diag_181_ = lean_ctor_get(v___x_177_, 4);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_191_ == 0)
{
lean_object* v_unused_192_; 
v_unused_192_ = lean_ctor_get(v___x_177_, 0);
lean_dec(v_unused_192_);
v___x_183_ = v___x_177_;
v_isShared_184_ = v_isSharedCheck_191_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_diag_181_);
lean_inc(v_postponed_180_);
lean_inc(v_zetaDeltaFVarIds_179_);
lean_inc(v_cache_178_);
lean_dec(v___x_177_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_191_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_186_; 
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 0, v_mctx_176_);
v___x_186_ = v___x_183_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_mctx_176_);
lean_ctor_set(v_reuseFailAlloc_190_, 1, v_cache_178_);
lean_ctor_set(v_reuseFailAlloc_190_, 2, v_zetaDeltaFVarIds_179_);
lean_ctor_set(v_reuseFailAlloc_190_, 3, v_postponed_180_);
lean_ctor_set(v_reuseFailAlloc_190_, 4, v_diag_181_);
v___x_186_ = v_reuseFailAlloc_190_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_187_ = lean_st_ref_set(v___y_171_, v___x_186_);
v___x_188_ = lean_box(v_fst_175_);
v___x_189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
return v___x_189_;
}
}
}
v___jp_193_:
{
lean_object* v_snd_195_; lean_object* v_fst_196_; lean_object* v_mctx_197_; uint8_t v___x_198_; 
v_snd_195_ = lean_ctor_get(v___y_194_, 1);
lean_inc(v_snd_195_);
v_fst_196_ = lean_ctor_get(v___y_194_, 0);
lean_inc(v_fst_196_);
lean_dec_ref(v___y_194_);
v_mctx_197_ = lean_ctor_get(v_snd_195_, 1);
lean_inc_ref(v_mctx_197_);
lean_dec(v_snd_195_);
v___x_198_ = lean_unbox(v_fst_196_);
lean_dec(v_fst_196_);
v_fst_175_ = v___x_198_;
v_mctx_176_ = v_mctx_197_;
goto v___jp_174_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3___redArg___boxed(lean_object* v_e_208_, lean_object* v_fvarId_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3___redArg(v_e_208_, v_fvarId_209_, v___y_210_);
lean_dec(v___y_210_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3(lean_object* v_e_213_, lean_object* v_fvarId_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3___redArg(v_e_213_, v_fvarId_214_, v___y_216_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3___boxed(lean_object* v_e_221_, lean_object* v_fvarId_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3(v_e_221_, v_fvarId_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_);
lean_dec(v___y_226_);
lean_dec_ref(v___y_225_);
lean_dec(v___y_224_);
lean_dec_ref(v___y_223_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg(lean_object* v_mvarId_229_, lean_object* v_x_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_229_, v_x_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_object* v_a_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_244_; 
v_a_237_ = lean_ctor_get(v___x_236_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_244_ == 0)
{
v___x_239_ = v___x_236_;
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_a_237_);
lean_dec(v___x_236_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_242_; 
if (v_isShared_240_ == 0)
{
v___x_242_ = v___x_239_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_a_237_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
else
{
lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_252_; 
v_a_245_ = lean_ctor_get(v___x_236_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_252_ == 0)
{
v___x_247_ = v___x_236_;
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_dec(v___x_236_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_250_; 
if (v_isShared_248_ == 0)
{
v___x_250_ = v___x_247_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_a_245_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg___boxed(lean_object* v_mvarId_253_, lean_object* v_x_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg(v_mvarId_253_, v_x_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4(lean_object* v_00_u03b1_261_, lean_object* v_mvarId_262_, lean_object* v_x_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg(v_mvarId_262_, v_x_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___boxed(lean_object* v_00_u03b1_270_, lean_object* v_mvarId_271_, lean_object* v_x_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4(v_00_u03b1_270_, v_mvarId_271_, v_x_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
return v_res_278_;
}
}
LEAN_EXPORT uint8_t l_Lean_MVarId_clear___lam__0(lean_object* v_fvarId_279_, lean_object* v_localInst_280_){
_start:
{
lean_object* v_fvar_281_; lean_object* v___x_282_; uint8_t v___x_283_; 
v_fvar_281_ = lean_ctor_get(v_localInst_280_, 1);
v___x_282_ = l_Lean_Expr_fvarId_x21(v_fvar_281_);
v___x_283_ = l_Lean_instBEqFVarId_beq(v___x_282_, v_fvarId_279_);
lean_dec(v___x_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clear___lam__0___boxed(lean_object* v_fvarId_284_, lean_object* v_localInst_285_){
_start:
{
uint8_t v_res_286_; lean_object* v_r_287_; 
v_res_286_ = l_Lean_MVarId_clear___lam__0(v_fvarId_284_, v_localInst_285_);
lean_dec_ref(v_localInst_285_);
lean_dec(v_fvarId_284_);
v_r_287_ = lean_box(v_res_286_);
return v_r_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13_spec__14___redArg(lean_object* v_x_288_, lean_object* v_x_289_, lean_object* v_x_290_, lean_object* v_x_291_){
_start:
{
lean_object* v_ks_292_; lean_object* v_vs_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_317_; 
v_ks_292_ = lean_ctor_get(v_x_288_, 0);
v_vs_293_ = lean_ctor_get(v_x_288_, 1);
v_isSharedCheck_317_ = !lean_is_exclusive(v_x_288_);
if (v_isSharedCheck_317_ == 0)
{
v___x_295_ = v_x_288_;
v_isShared_296_ = v_isSharedCheck_317_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_vs_293_);
lean_inc(v_ks_292_);
lean_dec(v_x_288_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_317_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_297_ = lean_array_get_size(v_ks_292_);
v___x_298_ = lean_nat_dec_lt(v_x_289_, v___x_297_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_302_; 
lean_dec(v_x_289_);
v___x_299_ = lean_array_push(v_ks_292_, v_x_290_);
v___x_300_ = lean_array_push(v_vs_293_, v_x_291_);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 1, v___x_300_);
lean_ctor_set(v___x_295_, 0, v___x_299_);
v___x_302_ = v___x_295_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v___x_299_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v___x_300_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
else
{
lean_object* v_k_x27_304_; uint8_t v___x_305_; 
v_k_x27_304_ = lean_array_fget_borrowed(v_ks_292_, v_x_289_);
v___x_305_ = l_Lean_instBEqMVarId_beq(v_x_290_, v_k_x27_304_);
if (v___x_305_ == 0)
{
lean_object* v___x_307_; 
if (v_isShared_296_ == 0)
{
v___x_307_ = v___x_295_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_ks_292_);
lean_ctor_set(v_reuseFailAlloc_311_, 1, v_vs_293_);
v___x_307_ = v_reuseFailAlloc_311_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = lean_unsigned_to_nat(1u);
v___x_309_ = lean_nat_add(v_x_289_, v___x_308_);
lean_dec(v_x_289_);
v_x_288_ = v___x_307_;
v_x_289_ = v___x_309_;
goto _start;
}
}
else
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_315_; 
v___x_312_ = lean_array_fset(v_ks_292_, v_x_289_, v_x_290_);
v___x_313_ = lean_array_fset(v_vs_293_, v_x_289_, v_x_291_);
lean_dec(v_x_289_);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 1, v___x_313_);
lean_ctor_set(v___x_295_, 0, v___x_312_);
v___x_315_ = v___x_295_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v___x_312_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v___x_313_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13___redArg(lean_object* v_n_318_, lean_object* v_k_319_, lean_object* v_v_320_){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = lean_unsigned_to_nat(0u);
v___x_322_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13_spec__14___redArg(v_n_318_, v___x_321_, v_k_319_, v_v_320_);
return v___x_322_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__0(void){
_start:
{
size_t v___x_323_; size_t v___x_324_; size_t v___x_325_; 
v___x_323_ = ((size_t)5ULL);
v___x_324_ = ((size_t)1ULL);
v___x_325_ = lean_usize_shift_left(v___x_324_, v___x_323_);
return v___x_325_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__1(void){
_start:
{
size_t v___x_326_; size_t v___x_327_; size_t v___x_328_; 
v___x_326_ = ((size_t)1ULL);
v___x_327_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__0);
v___x_328_ = lean_usize_sub(v___x_327_, v___x_326_);
return v___x_328_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(lean_object* v_x_330_, size_t v_x_331_, size_t v_x_332_, lean_object* v_x_333_, lean_object* v_x_334_){
_start:
{
if (lean_obj_tag(v_x_330_) == 0)
{
lean_object* v_es_335_; size_t v___x_336_; size_t v___x_337_; size_t v___x_338_; size_t v___x_339_; lean_object* v_j_340_; lean_object* v___x_341_; uint8_t v___x_342_; 
v_es_335_ = lean_ctor_get(v_x_330_, 0);
v___x_336_ = ((size_t)5ULL);
v___x_337_ = ((size_t)1ULL);
v___x_338_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__1);
v___x_339_ = lean_usize_land(v_x_331_, v___x_338_);
v_j_340_ = lean_usize_to_nat(v___x_339_);
v___x_341_ = lean_array_get_size(v_es_335_);
v___x_342_ = lean_nat_dec_lt(v_j_340_, v___x_341_);
if (v___x_342_ == 0)
{
lean_dec(v_j_340_);
lean_dec(v_x_334_);
lean_dec(v_x_333_);
return v_x_330_;
}
else
{
lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_379_; 
lean_inc_ref(v_es_335_);
v_isSharedCheck_379_ = !lean_is_exclusive(v_x_330_);
if (v_isSharedCheck_379_ == 0)
{
lean_object* v_unused_380_; 
v_unused_380_ = lean_ctor_get(v_x_330_, 0);
lean_dec(v_unused_380_);
v___x_344_ = v_x_330_;
v_isShared_345_ = v_isSharedCheck_379_;
goto v_resetjp_343_;
}
else
{
lean_dec(v_x_330_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_379_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v_v_346_; lean_object* v___x_347_; lean_object* v_xs_x27_348_; lean_object* v___y_350_; 
v_v_346_ = lean_array_fget(v_es_335_, v_j_340_);
v___x_347_ = lean_box(0);
v_xs_x27_348_ = lean_array_fset(v_es_335_, v_j_340_, v___x_347_);
switch(lean_obj_tag(v_v_346_))
{
case 0:
{
lean_object* v_key_355_; lean_object* v_val_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_366_; 
v_key_355_ = lean_ctor_get(v_v_346_, 0);
v_val_356_ = lean_ctor_get(v_v_346_, 1);
v_isSharedCheck_366_ = !lean_is_exclusive(v_v_346_);
if (v_isSharedCheck_366_ == 0)
{
v___x_358_ = v_v_346_;
v_isShared_359_ = v_isSharedCheck_366_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_val_356_);
lean_inc(v_key_355_);
lean_dec(v_v_346_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_366_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
uint8_t v___x_360_; 
v___x_360_ = l_Lean_instBEqMVarId_beq(v_x_333_, v_key_355_);
if (v___x_360_ == 0)
{
lean_object* v___x_361_; lean_object* v___x_362_; 
lean_del_object(v___x_358_);
v___x_361_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_355_, v_val_356_, v_x_333_, v_x_334_);
v___x_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_362_, 0, v___x_361_);
v___y_350_ = v___x_362_;
goto v___jp_349_;
}
else
{
lean_object* v___x_364_; 
lean_dec(v_val_356_);
lean_dec(v_key_355_);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 1, v_x_334_);
lean_ctor_set(v___x_358_, 0, v_x_333_);
v___x_364_ = v___x_358_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_x_333_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_x_334_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
v___y_350_ = v___x_364_;
goto v___jp_349_;
}
}
}
}
case 1:
{
lean_object* v_node_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_377_; 
v_node_367_ = lean_ctor_get(v_v_346_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v_v_346_);
if (v_isSharedCheck_377_ == 0)
{
v___x_369_ = v_v_346_;
v_isShared_370_ = v_isSharedCheck_377_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_node_367_);
lean_dec(v_v_346_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_377_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
size_t v___x_371_; size_t v___x_372_; lean_object* v___x_373_; lean_object* v___x_375_; 
v___x_371_ = lean_usize_shift_right(v_x_331_, v___x_336_);
v___x_372_ = lean_usize_add(v_x_332_, v___x_337_);
v___x_373_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_node_367_, v___x_371_, v___x_372_, v_x_333_, v_x_334_);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 0, v___x_373_);
v___x_375_ = v___x_369_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v___x_373_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
v___y_350_ = v___x_375_;
goto v___jp_349_;
}
}
}
default: 
{
lean_object* v___x_378_; 
v___x_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_378_, 0, v_x_333_);
lean_ctor_set(v___x_378_, 1, v_x_334_);
v___y_350_ = v___x_378_;
goto v___jp_349_;
}
}
v___jp_349_:
{
lean_object* v___x_351_; lean_object* v___x_353_; 
v___x_351_ = lean_array_fset(v_xs_x27_348_, v_j_340_, v___y_350_);
lean_dec(v_j_340_);
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 0, v___x_351_);
v___x_353_ = v___x_344_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v___x_351_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
}
else
{
lean_object* v_ks_381_; lean_object* v_vs_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_402_; 
v_ks_381_ = lean_ctor_get(v_x_330_, 0);
v_vs_382_ = lean_ctor_get(v_x_330_, 1);
v_isSharedCheck_402_ = !lean_is_exclusive(v_x_330_);
if (v_isSharedCheck_402_ == 0)
{
v___x_384_ = v_x_330_;
v_isShared_385_ = v_isSharedCheck_402_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_vs_382_);
lean_inc(v_ks_381_);
lean_dec(v_x_330_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_402_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_387_; 
if (v_isShared_385_ == 0)
{
v___x_387_ = v___x_384_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_ks_381_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v_vs_382_);
v___x_387_ = v_reuseFailAlloc_401_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
lean_object* v_newNode_388_; uint8_t v___y_390_; size_t v___x_396_; uint8_t v___x_397_; 
v_newNode_388_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13___redArg(v___x_387_, v_x_333_, v_x_334_);
v___x_396_ = ((size_t)7ULL);
v___x_397_ = lean_usize_dec_le(v___x_396_, v_x_332_);
if (v___x_397_ == 0)
{
lean_object* v___x_398_; lean_object* v___x_399_; uint8_t v___x_400_; 
v___x_398_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_388_);
v___x_399_ = lean_unsigned_to_nat(4u);
v___x_400_ = lean_nat_dec_lt(v___x_398_, v___x_399_);
lean_dec(v___x_398_);
v___y_390_ = v___x_400_;
goto v___jp_389_;
}
else
{
v___y_390_ = v___x_397_;
goto v___jp_389_;
}
v___jp_389_:
{
if (v___y_390_ == 0)
{
lean_object* v_ks_391_; lean_object* v_vs_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v_ks_391_ = lean_ctor_get(v_newNode_388_, 0);
lean_inc_ref(v_ks_391_);
v_vs_392_ = lean_ctor_get(v_newNode_388_, 1);
lean_inc_ref(v_vs_392_);
lean_dec_ref(v_newNode_388_);
v___x_393_ = lean_unsigned_to_nat(0u);
v___x_394_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__2);
v___x_395_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg(v_x_332_, v_ks_391_, v_vs_392_, v___x_393_, v___x_394_);
lean_dec_ref(v_vs_392_);
lean_dec_ref(v_ks_391_);
return v___x_395_;
}
else
{
return v_newNode_388_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg(size_t v_depth_403_, lean_object* v_keys_404_, lean_object* v_vals_405_, lean_object* v_i_406_, lean_object* v_entries_407_){
_start:
{
lean_object* v___x_408_; uint8_t v___x_409_; 
v___x_408_ = lean_array_get_size(v_keys_404_);
v___x_409_ = lean_nat_dec_lt(v_i_406_, v___x_408_);
if (v___x_409_ == 0)
{
lean_dec(v_i_406_);
return v_entries_407_;
}
else
{
lean_object* v_k_410_; lean_object* v_v_411_; uint64_t v___x_412_; size_t v_h_413_; size_t v___x_414_; lean_object* v___x_415_; size_t v___x_416_; size_t v___x_417_; size_t v___x_418_; size_t v_h_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v_k_410_ = lean_array_fget_borrowed(v_keys_404_, v_i_406_);
v_v_411_ = lean_array_fget_borrowed(v_vals_405_, v_i_406_);
v___x_412_ = l_Lean_instHashableMVarId_hash(v_k_410_);
v_h_413_ = lean_uint64_to_usize(v___x_412_);
v___x_414_ = ((size_t)5ULL);
v___x_415_ = lean_unsigned_to_nat(1u);
v___x_416_ = ((size_t)1ULL);
v___x_417_ = lean_usize_sub(v_depth_403_, v___x_416_);
v___x_418_ = lean_usize_mul(v___x_414_, v___x_417_);
v_h_419_ = lean_usize_shift_right(v_h_413_, v___x_418_);
v___x_420_ = lean_nat_add(v_i_406_, v___x_415_);
lean_dec(v_i_406_);
lean_inc(v_v_411_);
lean_inc(v_k_410_);
v___x_421_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_entries_407_, v_h_419_, v_depth_403_, v_k_410_, v_v_411_);
v_i_406_ = v___x_420_;
v_entries_407_ = v___x_421_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg___boxed(lean_object* v_depth_423_, lean_object* v_keys_424_, lean_object* v_vals_425_, lean_object* v_i_426_, lean_object* v_entries_427_){
_start:
{
size_t v_depth_boxed_428_; lean_object* v_res_429_; 
v_depth_boxed_428_ = lean_unbox_usize(v_depth_423_);
lean_dec(v_depth_423_);
v_res_429_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg(v_depth_boxed_428_, v_keys_424_, v_vals_425_, v_i_426_, v_entries_427_);
lean_dec_ref(v_vals_425_);
lean_dec_ref(v_keys_424_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___boxed(lean_object* v_x_430_, lean_object* v_x_431_, lean_object* v_x_432_, lean_object* v_x_433_, lean_object* v_x_434_){
_start:
{
size_t v_x_8837__boxed_435_; size_t v_x_8838__boxed_436_; lean_object* v_res_437_; 
v_x_8837__boxed_435_ = lean_unbox_usize(v_x_431_);
lean_dec(v_x_431_);
v_x_8838__boxed_436_ = lean_unbox_usize(v_x_432_);
lean_dec(v_x_432_);
v_res_437_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_x_430_, v_x_8837__boxed_435_, v_x_8838__boxed_436_, v_x_433_, v_x_434_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3___redArg(lean_object* v_x_438_, lean_object* v_x_439_, lean_object* v_x_440_){
_start:
{
uint64_t v___x_441_; size_t v___x_442_; size_t v___x_443_; lean_object* v___x_444_; 
v___x_441_ = l_Lean_instHashableMVarId_hash(v_x_439_);
v___x_442_ = lean_uint64_to_usize(v___x_441_);
v___x_443_ = ((size_t)1ULL);
v___x_444_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_x_438_, v___x_442_, v___x_443_, v_x_439_, v_x_440_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg(lean_object* v_mvarId_445_, lean_object* v_val_446_, lean_object* v___y_447_){
_start:
{
lean_object* v___x_449_; lean_object* v_mctx_450_; lean_object* v_cache_451_; lean_object* v_zetaDeltaFVarIds_452_; lean_object* v_postponed_453_; lean_object* v_diag_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_482_; 
v___x_449_ = lean_st_ref_take(v___y_447_);
v_mctx_450_ = lean_ctor_get(v___x_449_, 0);
v_cache_451_ = lean_ctor_get(v___x_449_, 1);
v_zetaDeltaFVarIds_452_ = lean_ctor_get(v___x_449_, 2);
v_postponed_453_ = lean_ctor_get(v___x_449_, 3);
v_diag_454_ = lean_ctor_get(v___x_449_, 4);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_482_ == 0)
{
v___x_456_ = v___x_449_;
v_isShared_457_ = v_isSharedCheck_482_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_diag_454_);
lean_inc(v_postponed_453_);
lean_inc(v_zetaDeltaFVarIds_452_);
lean_inc(v_cache_451_);
lean_inc(v_mctx_450_);
lean_dec(v___x_449_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_482_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v_depth_458_; lean_object* v_levelAssignDepth_459_; lean_object* v_lmvarCounter_460_; lean_object* v_mvarCounter_461_; lean_object* v_lDecls_462_; lean_object* v_decls_463_; lean_object* v_userNames_464_; lean_object* v_lAssignment_465_; lean_object* v_eAssignment_466_; lean_object* v_dAssignment_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_481_; 
v_depth_458_ = lean_ctor_get(v_mctx_450_, 0);
v_levelAssignDepth_459_ = lean_ctor_get(v_mctx_450_, 1);
v_lmvarCounter_460_ = lean_ctor_get(v_mctx_450_, 2);
v_mvarCounter_461_ = lean_ctor_get(v_mctx_450_, 3);
v_lDecls_462_ = lean_ctor_get(v_mctx_450_, 4);
v_decls_463_ = lean_ctor_get(v_mctx_450_, 5);
v_userNames_464_ = lean_ctor_get(v_mctx_450_, 6);
v_lAssignment_465_ = lean_ctor_get(v_mctx_450_, 7);
v_eAssignment_466_ = lean_ctor_get(v_mctx_450_, 8);
v_dAssignment_467_ = lean_ctor_get(v_mctx_450_, 9);
v_isSharedCheck_481_ = !lean_is_exclusive(v_mctx_450_);
if (v_isSharedCheck_481_ == 0)
{
v___x_469_ = v_mctx_450_;
v_isShared_470_ = v_isSharedCheck_481_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_dAssignment_467_);
lean_inc(v_eAssignment_466_);
lean_inc(v_lAssignment_465_);
lean_inc(v_userNames_464_);
lean_inc(v_decls_463_);
lean_inc(v_lDecls_462_);
lean_inc(v_mvarCounter_461_);
lean_inc(v_lmvarCounter_460_);
lean_inc(v_levelAssignDepth_459_);
lean_inc(v_depth_458_);
lean_dec(v_mctx_450_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_481_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_471_; lean_object* v___x_473_; 
v___x_471_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3___redArg(v_eAssignment_466_, v_mvarId_445_, v_val_446_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 8, v___x_471_);
v___x_473_ = v___x_469_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_depth_458_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v_levelAssignDepth_459_);
lean_ctor_set(v_reuseFailAlloc_480_, 2, v_lmvarCounter_460_);
lean_ctor_set(v_reuseFailAlloc_480_, 3, v_mvarCounter_461_);
lean_ctor_set(v_reuseFailAlloc_480_, 4, v_lDecls_462_);
lean_ctor_set(v_reuseFailAlloc_480_, 5, v_decls_463_);
lean_ctor_set(v_reuseFailAlloc_480_, 6, v_userNames_464_);
lean_ctor_set(v_reuseFailAlloc_480_, 7, v_lAssignment_465_);
lean_ctor_set(v_reuseFailAlloc_480_, 8, v___x_471_);
lean_ctor_set(v_reuseFailAlloc_480_, 9, v_dAssignment_467_);
v___x_473_ = v_reuseFailAlloc_480_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
lean_object* v___x_475_; 
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 0, v___x_473_);
v___x_475_ = v___x_456_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_473_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v_cache_451_);
lean_ctor_set(v_reuseFailAlloc_479_, 2, v_zetaDeltaFVarIds_452_);
lean_ctor_set(v_reuseFailAlloc_479_, 3, v_postponed_453_);
lean_ctor_set(v_reuseFailAlloc_479_, 4, v_diag_454_);
v___x_475_ = v_reuseFailAlloc_479_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_476_ = lean_st_ref_set(v___y_447_, v___x_475_);
v___x_477_ = lean_box(0);
v___x_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
return v___x_478_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg___boxed(lean_object* v_mvarId_483_, lean_object* v_val_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg(v_mvarId_483_, v_val_484_, v___y_485_);
lean_dec(v___y_485_);
return v_res_487_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3(void){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__2));
v___x_493_ = l_Lean_stringToMessageData(v___x_492_);
return v___x_493_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5(void){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__4));
v___x_496_ = l_Lean_stringToMessageData(v___x_495_);
return v___x_496_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__6));
v___x_499_ = l_Lean_stringToMessageData(v___x_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9(lean_object* v_fvarId_500_, lean_object* v_mvarId_501_, lean_object* v_as_502_, size_t v_i_503_, size_t v_stop_504_, lean_object* v_b_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_){
_start:
{
lean_object* v_a_512_; uint8_t v___x_516_; 
v___x_516_ = lean_usize_dec_eq(v_i_503_, v_stop_504_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; 
v___x_517_ = lean_array_uget(v_as_502_, v_i_503_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v___x_518_; 
v___x_518_ = lean_box(0);
v_a_512_ = v___x_518_;
goto v___jp_511_;
}
else
{
lean_object* v_val_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_556_; 
v_val_519_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_556_ == 0)
{
v___x_521_ = v___x_517_;
v_isShared_522_ = v_isSharedCheck_556_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_val_519_);
lean_dec(v___x_517_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_556_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_523_ = l_Lean_LocalDecl_fvarId(v_val_519_);
v___x_524_ = l_Lean_instBEqFVarId_beq(v___x_523_, v_fvarId_500_);
lean_dec(v___x_523_);
if (v___x_524_ == 0)
{
uint8_t v___x_525_; lean_object* v___x_526_; 
v___x_525_ = 1;
lean_inc(v_fvarId_500_);
lean_inc(v_val_519_);
v___x_526_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg(v_val_519_, v_fvarId_500_, v___x_525_, v___y_507_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v_a_527_; uint8_t v___x_528_; 
v_a_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_a_527_);
lean_dec_ref(v___x_526_);
v___x_528_ = lean_unbox(v_a_527_);
lean_dec(v_a_527_);
if (v___x_528_ == 0)
{
lean_object* v___x_529_; 
lean_del_object(v___x_521_);
lean_dec(v_val_519_);
v___x_529_ = lean_box(0);
v_a_512_ = v___x_529_;
goto v___jp_511_;
}
else
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_543_; 
v___x_530_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__1));
v___x_531_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3);
v___x_532_ = l_Lean_LocalDecl_toExpr(v_val_519_);
v___x_533_ = l_Lean_MessageData_ofExpr(v___x_532_);
v___x_534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_531_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
v___x_535_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5);
v___x_536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_534_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
lean_inc(v_fvarId_500_);
v___x_537_ = l_Lean_mkFVar(v_fvarId_500_);
v___x_538_ = l_Lean_MessageData_ofExpr(v___x_537_);
v___x_539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_536_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
v___x_540_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7);
v___x_541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_541_, 0, v___x_539_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_541_);
v___x_543_ = v___x_521_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_541_);
v___x_543_ = v_reuseFailAlloc_546_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_object* v___x_544_; 
lean_inc(v_mvarId_501_);
v___x_544_ = l_Lean_Meta_throwTacticEx___redArg(v___x_530_, v_mvarId_501_, v___x_543_, v___y_506_, v___y_507_, v___y_508_, v___y_509_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v_a_545_; 
v_a_545_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_a_545_);
lean_dec_ref(v___x_544_);
v_a_512_ = v_a_545_;
goto v___jp_511_;
}
else
{
lean_dec(v_mvarId_501_);
lean_dec(v_fvarId_500_);
return v___x_544_;
}
}
}
}
else
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
lean_del_object(v___x_521_);
lean_dec(v_val_519_);
lean_dec(v_mvarId_501_);
lean_dec(v_fvarId_500_);
v_a_547_ = lean_ctor_get(v___x_526_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v___x_526_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_526_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_547_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
else
{
lean_object* v___x_555_; 
lean_del_object(v___x_521_);
lean_dec(v_val_519_);
v___x_555_ = lean_box(0);
v_a_512_ = v___x_555_;
goto v___jp_511_;
}
}
}
}
else
{
lean_object* v___x_557_; 
lean_dec(v_mvarId_501_);
lean_dec(v_fvarId_500_);
v___x_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_557_, 0, v_b_505_);
return v___x_557_;
}
v___jp_511_:
{
size_t v___x_513_; size_t v___x_514_; 
v___x_513_ = ((size_t)1ULL);
v___x_514_ = lean_usize_add(v_i_503_, v___x_513_);
v_i_503_ = v___x_514_;
v_b_505_ = v_a_512_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___boxed(lean_object* v_fvarId_558_, lean_object* v_mvarId_559_, lean_object* v_as_560_, lean_object* v_i_561_, lean_object* v_stop_562_, lean_object* v_b_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
size_t v_i_boxed_569_; size_t v_stop_boxed_570_; lean_object* v_res_571_; 
v_i_boxed_569_ = lean_unbox_usize(v_i_561_);
lean_dec(v_i_561_);
v_stop_boxed_570_ = lean_unbox_usize(v_stop_562_);
lean_dec(v_stop_562_);
v_res_571_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9(v_fvarId_558_, v_mvarId_559_, v_as_560_, v_i_boxed_569_, v_stop_boxed_570_, v_b_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec_ref(v_as_560_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(lean_object* v_fvarId_572_, lean_object* v_mvarId_573_, lean_object* v_as_574_, size_t v_i_575_, size_t v_stop_576_, lean_object* v_b_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
lean_object* v_a_584_; uint8_t v___x_588_; 
v___x_588_ = lean_usize_dec_eq(v_i_575_, v_stop_576_);
if (v___x_588_ == 0)
{
lean_object* v___x_589_; 
v___x_589_ = lean_array_uget(v_as_574_, v_i_575_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v___x_590_; 
v___x_590_ = lean_box(0);
v_a_584_ = v___x_590_;
goto v___jp_583_;
}
else
{
lean_object* v_val_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_628_; 
v_val_591_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_628_ == 0)
{
v___x_593_ = v___x_589_;
v_isShared_594_ = v_isSharedCheck_628_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_val_591_);
lean_dec(v___x_589_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_628_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_595_; uint8_t v___x_596_; 
v___x_595_ = l_Lean_LocalDecl_fvarId(v_val_591_);
v___x_596_ = l_Lean_instBEqFVarId_beq(v___x_595_, v_fvarId_572_);
lean_dec(v___x_595_);
if (v___x_596_ == 0)
{
uint8_t v___x_597_; lean_object* v___x_598_; 
v___x_597_ = 1;
lean_inc(v_fvarId_572_);
lean_inc(v_val_591_);
v___x_598_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg(v_val_591_, v_fvarId_572_, v___x_597_, v___y_579_);
if (lean_obj_tag(v___x_598_) == 0)
{
lean_object* v_a_599_; uint8_t v___x_600_; 
v_a_599_ = lean_ctor_get(v___x_598_, 0);
lean_inc(v_a_599_);
lean_dec_ref(v___x_598_);
v___x_600_ = lean_unbox(v_a_599_);
lean_dec(v_a_599_);
if (v___x_600_ == 0)
{
lean_object* v___x_601_; 
lean_del_object(v___x_593_);
lean_dec(v_val_591_);
v___x_601_ = lean_box(0);
v_a_584_ = v___x_601_;
goto v___jp_583_;
}
else
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_615_; 
v___x_602_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__1));
v___x_603_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3);
v___x_604_ = l_Lean_LocalDecl_toExpr(v_val_591_);
v___x_605_ = l_Lean_MessageData_ofExpr(v___x_604_);
v___x_606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_603_);
lean_ctor_set(v___x_606_, 1, v___x_605_);
v___x_607_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5);
v___x_608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_606_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
lean_inc(v_fvarId_572_);
v___x_609_ = l_Lean_mkFVar(v_fvarId_572_);
v___x_610_ = l_Lean_MessageData_ofExpr(v___x_609_);
v___x_611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_611_, 0, v___x_608_);
lean_ctor_set(v___x_611_, 1, v___x_610_);
v___x_612_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7);
v___x_613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_611_);
lean_ctor_set(v___x_613_, 1, v___x_612_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_613_);
v___x_615_ = v___x_593_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_613_);
v___x_615_ = v_reuseFailAlloc_618_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
lean_object* v___x_616_; 
lean_inc(v_mvarId_573_);
v___x_616_ = l_Lean_Meta_throwTacticEx___redArg(v___x_602_, v_mvarId_573_, v___x_615_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
if (lean_obj_tag(v___x_616_) == 0)
{
lean_object* v_a_617_; 
v_a_617_ = lean_ctor_get(v___x_616_, 0);
lean_inc(v_a_617_);
lean_dec_ref(v___x_616_);
v_a_584_ = v_a_617_;
goto v___jp_583_;
}
else
{
lean_dec(v_mvarId_573_);
lean_dec(v_fvarId_572_);
return v___x_616_;
}
}
}
}
else
{
lean_object* v_a_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_626_; 
lean_del_object(v___x_593_);
lean_dec(v_val_591_);
lean_dec(v_mvarId_573_);
lean_dec(v_fvarId_572_);
v_a_619_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_626_ == 0)
{
v___x_621_ = v___x_598_;
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_a_619_);
lean_dec(v___x_598_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_624_; 
if (v_isShared_622_ == 0)
{
v___x_624_ = v___x_621_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_a_619_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
}
else
{
lean_object* v___x_627_; 
lean_del_object(v___x_593_);
lean_dec(v_val_591_);
v___x_627_ = lean_box(0);
v_a_584_ = v___x_627_;
goto v___jp_583_;
}
}
}
}
else
{
lean_object* v___x_629_; 
lean_dec(v_mvarId_573_);
lean_dec(v_fvarId_572_);
v___x_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_629_, 0, v_b_577_);
return v___x_629_;
}
v___jp_583_:
{
size_t v___x_585_; size_t v___x_586_; lean_object* v___x_587_; 
v___x_585_ = ((size_t)1ULL);
v___x_586_ = lean_usize_add(v_i_575_, v___x_585_);
v___x_587_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9(v_fvarId_572_, v_mvarId_573_, v_as_574_, v___x_586_, v_stop_576_, v_a_584_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
return v___x_587_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5___boxed(lean_object* v_fvarId_630_, lean_object* v_mvarId_631_, lean_object* v_as_632_, lean_object* v_i_633_, lean_object* v_stop_634_, lean_object* v_b_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_){
_start:
{
size_t v_i_boxed_641_; size_t v_stop_boxed_642_; lean_object* v_res_643_; 
v_i_boxed_641_ = lean_unbox_usize(v_i_633_);
lean_dec(v_i_633_);
v_stop_boxed_642_ = lean_unbox_usize(v_stop_634_);
lean_dec(v_stop_634_);
v_res_643_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_630_, v_mvarId_631_, v_as_632_, v_i_boxed_641_, v_stop_boxed_642_, v_b_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec_ref(v_as_632_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6(lean_object* v_fvarId_644_, lean_object* v_mvarId_645_, lean_object* v_x_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
if (lean_obj_tag(v_x_646_) == 0)
{
lean_object* v_cs_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_673_; 
v_cs_652_ = lean_ctor_get(v_x_646_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v_x_646_);
if (v_isSharedCheck_673_ == 0)
{
v___x_654_ = v_x_646_;
v_isShared_655_ = v_isSharedCheck_673_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_cs_652_);
lean_dec(v_x_646_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_673_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_656_ = lean_unsigned_to_nat(0u);
v___x_657_ = lean_array_get_size(v_cs_652_);
v___x_658_ = lean_box(0);
v___x_659_ = lean_nat_dec_lt(v___x_656_, v___x_657_);
if (v___x_659_ == 0)
{
lean_object* v___x_661_; 
lean_dec_ref(v_cs_652_);
lean_dec(v_mvarId_645_);
lean_dec(v_fvarId_644_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 0, v___x_658_);
v___x_661_ = v___x_654_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_658_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
else
{
uint8_t v___x_663_; 
v___x_663_ = lean_nat_dec_le(v___x_657_, v___x_657_);
if (v___x_663_ == 0)
{
if (v___x_659_ == 0)
{
lean_object* v___x_665_; 
lean_dec_ref(v_cs_652_);
lean_dec(v_mvarId_645_);
lean_dec(v_fvarId_644_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 0, v___x_658_);
v___x_665_ = v___x_654_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v___x_658_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
else
{
size_t v___x_667_; size_t v___x_668_; lean_object* v___x_669_; 
lean_del_object(v___x_654_);
v___x_667_ = ((size_t)0ULL);
v___x_668_ = lean_usize_of_nat(v___x_657_);
v___x_669_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(v_fvarId_644_, v_mvarId_645_, v_cs_652_, v___x_667_, v___x_668_, v___x_658_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
lean_dec_ref(v_cs_652_);
return v___x_669_;
}
}
else
{
size_t v___x_670_; size_t v___x_671_; lean_object* v___x_672_; 
lean_del_object(v___x_654_);
v___x_670_ = ((size_t)0ULL);
v___x_671_ = lean_usize_of_nat(v___x_657_);
v___x_672_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(v_fvarId_644_, v_mvarId_645_, v_cs_652_, v___x_670_, v___x_671_, v___x_658_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
lean_dec_ref(v_cs_652_);
return v___x_672_;
}
}
}
}
else
{
lean_object* v_vs_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_695_; 
v_vs_674_ = lean_ctor_get(v_x_646_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v_x_646_);
if (v_isSharedCheck_695_ == 0)
{
v___x_676_ = v_x_646_;
v_isShared_677_ = v_isSharedCheck_695_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_vs_674_);
lean_dec(v_x_646_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_695_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; uint8_t v___x_681_; 
v___x_678_ = lean_unsigned_to_nat(0u);
v___x_679_ = lean_array_get_size(v_vs_674_);
v___x_680_ = lean_box(0);
v___x_681_ = lean_nat_dec_lt(v___x_678_, v___x_679_);
if (v___x_681_ == 0)
{
lean_object* v___x_683_; 
lean_dec_ref(v_vs_674_);
lean_dec(v_mvarId_645_);
lean_dec(v_fvarId_644_);
if (v_isShared_677_ == 0)
{
lean_ctor_set_tag(v___x_676_, 0);
lean_ctor_set(v___x_676_, 0, v___x_680_);
v___x_683_ = v___x_676_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_680_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
else
{
uint8_t v___x_685_; 
v___x_685_ = lean_nat_dec_le(v___x_679_, v___x_679_);
if (v___x_685_ == 0)
{
if (v___x_681_ == 0)
{
lean_object* v___x_687_; 
lean_dec_ref(v_vs_674_);
lean_dec(v_mvarId_645_);
lean_dec(v_fvarId_644_);
if (v_isShared_677_ == 0)
{
lean_ctor_set_tag(v___x_676_, 0);
lean_ctor_set(v___x_676_, 0, v___x_680_);
v___x_687_ = v___x_676_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_680_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
else
{
size_t v___x_689_; size_t v___x_690_; lean_object* v___x_691_; 
lean_del_object(v___x_676_);
v___x_689_ = ((size_t)0ULL);
v___x_690_ = lean_usize_of_nat(v___x_679_);
v___x_691_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_644_, v_mvarId_645_, v_vs_674_, v___x_689_, v___x_690_, v___x_680_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
lean_dec_ref(v_vs_674_);
return v___x_691_;
}
}
else
{
size_t v___x_692_; size_t v___x_693_; lean_object* v___x_694_; 
lean_del_object(v___x_676_);
v___x_692_ = ((size_t)0ULL);
v___x_693_ = lean_usize_of_nat(v___x_679_);
v___x_694_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_644_, v_mvarId_645_, v_vs_674_, v___x_692_, v___x_693_, v___x_680_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
lean_dec_ref(v_vs_674_);
return v___x_694_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(lean_object* v_fvarId_696_, lean_object* v_mvarId_697_, lean_object* v_as_698_, size_t v_i_699_, size_t v_stop_700_, lean_object* v_b_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
uint8_t v___x_707_; 
v___x_707_ = lean_usize_dec_eq(v_i_699_, v_stop_700_);
if (v___x_707_ == 0)
{
lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_708_ = lean_array_uget_borrowed(v_as_698_, v_i_699_);
lean_inc(v___x_708_);
lean_inc(v_mvarId_697_);
lean_inc(v_fvarId_696_);
v___x_709_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6(v_fvarId_696_, v_mvarId_697_, v___x_708_, v___y_702_, v___y_703_, v___y_704_, v___y_705_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; size_t v___x_711_; size_t v___x_712_; 
v_a_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_a_710_);
lean_dec_ref(v___x_709_);
v___x_711_ = ((size_t)1ULL);
v___x_712_ = lean_usize_add(v_i_699_, v___x_711_);
v_i_699_ = v___x_712_;
v_b_701_ = v_a_710_;
goto _start;
}
else
{
lean_dec(v_mvarId_697_);
lean_dec(v_fvarId_696_);
return v___x_709_;
}
}
else
{
lean_object* v___x_714_; 
lean_dec(v_mvarId_697_);
lean_dec(v_fvarId_696_);
v___x_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_714_, 0, v_b_701_);
return v___x_714_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7___boxed(lean_object* v_fvarId_715_, lean_object* v_mvarId_716_, lean_object* v_as_717_, lean_object* v_i_718_, lean_object* v_stop_719_, lean_object* v_b_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
size_t v_i_boxed_726_; size_t v_stop_boxed_727_; lean_object* v_res_728_; 
v_i_boxed_726_ = lean_unbox_usize(v_i_718_);
lean_dec(v_i_718_);
v_stop_boxed_727_ = lean_unbox_usize(v_stop_719_);
lean_dec(v_stop_719_);
v_res_728_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(v_fvarId_715_, v_mvarId_716_, v_as_717_, v_i_boxed_726_, v_stop_boxed_727_, v_b_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec_ref(v_as_717_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6___boxed(lean_object* v_fvarId_729_, lean_object* v_mvarId_730_, lean_object* v_x_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6(v_fvarId_729_, v_mvarId_730_, v_x_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_732_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6(lean_object* v_fvarId_738_, lean_object* v_mvarId_739_, lean_object* v_t_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v_root_746_; lean_object* v_tail_747_; lean_object* v___x_748_; 
v_root_746_ = lean_ctor_get(v_t_740_, 0);
lean_inc_ref(v_root_746_);
v_tail_747_ = lean_ctor_get(v_t_740_, 1);
lean_inc_ref(v_tail_747_);
lean_dec_ref(v_t_740_);
lean_inc(v_mvarId_739_);
lean_inc(v_fvarId_738_);
v___x_748_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6(v_fvarId_738_, v_mvarId_739_, v_root_746_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_769_; 
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_769_ == 0)
{
lean_object* v_unused_770_; 
v_unused_770_ = lean_ctor_get(v___x_748_, 0);
lean_dec(v_unused_770_);
v___x_750_ = v___x_748_;
v_isShared_751_ = v_isSharedCheck_769_;
goto v_resetjp_749_;
}
else
{
lean_dec(v___x_748_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_769_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; uint8_t v___x_755_; 
v___x_752_ = lean_unsigned_to_nat(0u);
v___x_753_ = lean_array_get_size(v_tail_747_);
v___x_754_ = lean_box(0);
v___x_755_ = lean_nat_dec_lt(v___x_752_, v___x_753_);
if (v___x_755_ == 0)
{
lean_object* v___x_757_; 
lean_dec_ref(v_tail_747_);
lean_dec(v_mvarId_739_);
lean_dec(v_fvarId_738_);
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 0, v___x_754_);
v___x_757_ = v___x_750_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_754_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
else
{
uint8_t v___x_759_; 
v___x_759_ = lean_nat_dec_le(v___x_753_, v___x_753_);
if (v___x_759_ == 0)
{
if (v___x_755_ == 0)
{
lean_object* v___x_761_; 
lean_dec_ref(v_tail_747_);
lean_dec(v_mvarId_739_);
lean_dec(v_fvarId_738_);
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 0, v___x_754_);
v___x_761_ = v___x_750_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_754_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
else
{
size_t v___x_763_; size_t v___x_764_; lean_object* v___x_765_; 
lean_del_object(v___x_750_);
v___x_763_ = ((size_t)0ULL);
v___x_764_ = lean_usize_of_nat(v___x_753_);
v___x_765_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_738_, v_mvarId_739_, v_tail_747_, v___x_763_, v___x_764_, v___x_754_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
lean_dec_ref(v_tail_747_);
return v___x_765_;
}
}
else
{
size_t v___x_766_; size_t v___x_767_; lean_object* v___x_768_; 
lean_del_object(v___x_750_);
v___x_766_ = ((size_t)0ULL);
v___x_767_ = lean_usize_of_nat(v___x_753_);
v___x_768_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_738_, v_mvarId_739_, v_tail_747_, v___x_766_, v___x_767_, v___x_754_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
lean_dec_ref(v_tail_747_);
return v___x_768_;
}
}
}
}
else
{
lean_dec_ref(v_tail_747_);
lean_dec(v_mvarId_739_);
lean_dec(v_fvarId_738_);
return v___x_748_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6___boxed(lean_object* v_fvarId_771_, lean_object* v_mvarId_772_, lean_object* v_t_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6(v_fvarId_771_, v_mvarId_772_, v_t_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_);
lean_dec(v___y_777_);
lean_dec_ref(v___y_776_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
return v_res_779_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4(lean_object* v_fvarId_781_, lean_object* v_mvarId_782_, lean_object* v_x_783_, size_t v_x_784_, size_t v_x_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
if (lean_obj_tag(v_x_783_) == 0)
{
lean_object* v_cs_791_; lean_object* v___x_792_; size_t v___x_793_; lean_object* v_j_794_; lean_object* v___x_795_; size_t v___x_796_; size_t v___x_797_; size_t v___x_798_; size_t v___x_799_; size_t v___x_800_; size_t v___x_801_; lean_object* v___x_802_; 
v_cs_791_ = lean_ctor_get(v_x_783_, 0);
lean_inc_ref(v_cs_791_);
lean_dec_ref(v_x_783_);
v___x_792_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0);
v___x_793_ = lean_usize_shift_right(v_x_784_, v_x_785_);
v_j_794_ = lean_usize_to_nat(v___x_793_);
v___x_795_ = lean_array_get_borrowed(v___x_792_, v_cs_791_, v_j_794_);
v___x_796_ = ((size_t)1ULL);
v___x_797_ = lean_usize_shift_left(v___x_796_, v_x_785_);
v___x_798_ = lean_usize_sub(v___x_797_, v___x_796_);
v___x_799_ = lean_usize_land(v_x_784_, v___x_798_);
v___x_800_ = ((size_t)5ULL);
v___x_801_ = lean_usize_sub(v_x_785_, v___x_800_);
lean_inc(v___x_795_);
lean_inc(v_mvarId_782_);
lean_inc(v_fvarId_781_);
v___x_802_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4(v_fvarId_781_, v_mvarId_782_, v___x_795_, v___x_799_, v___x_801_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_824_; 
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_824_ == 0)
{
lean_object* v_unused_825_; 
v_unused_825_ = lean_ctor_get(v___x_802_, 0);
lean_dec(v_unused_825_);
v___x_804_ = v___x_802_;
v_isShared_805_ = v_isSharedCheck_824_;
goto v_resetjp_803_;
}
else
{
lean_dec(v___x_802_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_824_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; uint8_t v___x_810_; 
v___x_806_ = lean_unsigned_to_nat(1u);
v___x_807_ = lean_nat_add(v_j_794_, v___x_806_);
lean_dec(v_j_794_);
v___x_808_ = lean_array_get_size(v_cs_791_);
v___x_809_ = lean_box(0);
v___x_810_ = lean_nat_dec_lt(v___x_807_, v___x_808_);
if (v___x_810_ == 0)
{
lean_object* v___x_812_; 
lean_dec(v___x_807_);
lean_dec_ref(v_cs_791_);
lean_dec(v_mvarId_782_);
lean_dec(v_fvarId_781_);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 0, v___x_809_);
v___x_812_ = v___x_804_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_809_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
else
{
uint8_t v___x_814_; 
v___x_814_ = lean_nat_dec_le(v___x_808_, v___x_808_);
if (v___x_814_ == 0)
{
if (v___x_810_ == 0)
{
lean_object* v___x_816_; 
lean_dec(v___x_807_);
lean_dec_ref(v_cs_791_);
lean_dec(v_mvarId_782_);
lean_dec(v_fvarId_781_);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 0, v___x_809_);
v___x_816_ = v___x_804_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_809_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
else
{
size_t v___x_818_; size_t v___x_819_; lean_object* v___x_820_; 
lean_del_object(v___x_804_);
v___x_818_ = lean_usize_of_nat(v___x_807_);
lean_dec(v___x_807_);
v___x_819_ = lean_usize_of_nat(v___x_808_);
v___x_820_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(v_fvarId_781_, v_mvarId_782_, v_cs_791_, v___x_818_, v___x_819_, v___x_809_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
lean_dec_ref(v_cs_791_);
return v___x_820_;
}
}
else
{
size_t v___x_821_; size_t v___x_822_; lean_object* v___x_823_; 
lean_del_object(v___x_804_);
v___x_821_ = lean_usize_of_nat(v___x_807_);
lean_dec(v___x_807_);
v___x_822_ = lean_usize_of_nat(v___x_808_);
v___x_823_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(v_fvarId_781_, v_mvarId_782_, v_cs_791_, v___x_821_, v___x_822_, v___x_809_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
lean_dec_ref(v_cs_791_);
return v___x_823_;
}
}
}
}
else
{
lean_dec(v_j_794_);
lean_dec_ref(v_cs_791_);
lean_dec(v_mvarId_782_);
lean_dec(v_fvarId_781_);
return v___x_802_;
}
}
else
{
lean_object* v_vs_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_847_; 
v_vs_826_ = lean_ctor_get(v_x_783_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v_x_783_);
if (v_isSharedCheck_847_ == 0)
{
v___x_828_ = v_x_783_;
v_isShared_829_ = v_isSharedCheck_847_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_vs_826_);
lean_dec(v_x_783_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_847_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; uint8_t v___x_833_; 
v___x_830_ = lean_usize_to_nat(v_x_784_);
v___x_831_ = lean_array_get_size(v_vs_826_);
v___x_832_ = lean_box(0);
v___x_833_ = lean_nat_dec_lt(v___x_830_, v___x_831_);
if (v___x_833_ == 0)
{
lean_object* v___x_835_; 
lean_dec(v___x_830_);
lean_dec_ref(v_vs_826_);
lean_dec(v_mvarId_782_);
lean_dec(v_fvarId_781_);
if (v_isShared_829_ == 0)
{
lean_ctor_set_tag(v___x_828_, 0);
lean_ctor_set(v___x_828_, 0, v___x_832_);
v___x_835_ = v___x_828_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_832_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
else
{
uint8_t v___x_837_; 
v___x_837_ = lean_nat_dec_le(v___x_831_, v___x_831_);
if (v___x_837_ == 0)
{
if (v___x_833_ == 0)
{
lean_object* v___x_839_; 
lean_dec(v___x_830_);
lean_dec_ref(v_vs_826_);
lean_dec(v_mvarId_782_);
lean_dec(v_fvarId_781_);
if (v_isShared_829_ == 0)
{
lean_ctor_set_tag(v___x_828_, 0);
lean_ctor_set(v___x_828_, 0, v___x_832_);
v___x_839_ = v___x_828_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_832_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
else
{
size_t v___x_841_; size_t v___x_842_; lean_object* v___x_843_; 
lean_del_object(v___x_828_);
v___x_841_ = lean_usize_of_nat(v___x_830_);
lean_dec(v___x_830_);
v___x_842_ = lean_usize_of_nat(v___x_831_);
v___x_843_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_781_, v_mvarId_782_, v_vs_826_, v___x_841_, v___x_842_, v___x_832_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
lean_dec_ref(v_vs_826_);
return v___x_843_;
}
}
else
{
size_t v___x_844_; size_t v___x_845_; lean_object* v___x_846_; 
lean_del_object(v___x_828_);
v___x_844_ = lean_usize_of_nat(v___x_830_);
lean_dec(v___x_830_);
v___x_845_ = lean_usize_of_nat(v___x_831_);
v___x_846_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_781_, v_mvarId_782_, v_vs_826_, v___x_844_, v___x_845_, v___x_832_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
lean_dec_ref(v_vs_826_);
return v___x_846_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___boxed(lean_object* v_fvarId_848_, lean_object* v_mvarId_849_, lean_object* v_x_850_, lean_object* v_x_851_, lean_object* v_x_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
size_t v_x_9532__boxed_858_; size_t v_x_9533__boxed_859_; lean_object* v_res_860_; 
v_x_9532__boxed_858_ = lean_unbox_usize(v_x_851_);
lean_dec(v_x_851_);
v_x_9533__boxed_859_ = lean_unbox_usize(v_x_852_);
lean_dec(v_x_852_);
v_res_860_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4(v_fvarId_848_, v_mvarId_849_, v_x_850_, v_x_9532__boxed_858_, v_x_9533__boxed_859_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1(lean_object* v_fvarId_861_, lean_object* v_mvarId_862_, lean_object* v_t_863_, lean_object* v_start_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
lean_object* v___x_870_; uint8_t v___x_871_; 
v___x_870_ = lean_unsigned_to_nat(0u);
v___x_871_ = lean_nat_dec_eq(v_start_864_, v___x_870_);
if (v___x_871_ == 0)
{
lean_object* v_root_872_; lean_object* v_tail_873_; size_t v_shift_874_; lean_object* v_tailOff_875_; uint8_t v___x_876_; 
v_root_872_ = lean_ctor_get(v_t_863_, 0);
lean_inc_ref(v_root_872_);
v_tail_873_ = lean_ctor_get(v_t_863_, 1);
lean_inc_ref(v_tail_873_);
v_shift_874_ = lean_ctor_get_usize(v_t_863_, 4);
v_tailOff_875_ = lean_ctor_get(v_t_863_, 3);
lean_inc(v_tailOff_875_);
lean_dec_ref(v_t_863_);
v___x_876_ = lean_nat_dec_le(v_tailOff_875_, v_start_864_);
if (v___x_876_ == 0)
{
size_t v___x_877_; lean_object* v___x_878_; 
lean_dec(v_tailOff_875_);
v___x_877_ = lean_usize_of_nat(v_start_864_);
lean_inc(v_mvarId_862_);
lean_inc(v_fvarId_861_);
v___x_878_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4(v_fvarId_861_, v_mvarId_862_, v_root_872_, v___x_877_, v_shift_874_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_898_; 
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_898_ == 0)
{
lean_object* v_unused_899_; 
v_unused_899_ = lean_ctor_get(v___x_878_, 0);
lean_dec(v_unused_899_);
v___x_880_ = v___x_878_;
v_isShared_881_ = v_isSharedCheck_898_;
goto v_resetjp_879_;
}
else
{
lean_dec(v___x_878_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_898_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_882_; lean_object* v___x_883_; uint8_t v___x_884_; 
v___x_882_ = lean_array_get_size(v_tail_873_);
v___x_883_ = lean_box(0);
v___x_884_ = lean_nat_dec_lt(v___x_870_, v___x_882_);
if (v___x_884_ == 0)
{
lean_object* v___x_886_; 
lean_dec_ref(v_tail_873_);
lean_dec(v_mvarId_862_);
lean_dec(v_fvarId_861_);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 0, v___x_883_);
v___x_886_ = v___x_880_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_883_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
else
{
uint8_t v___x_888_; 
v___x_888_ = lean_nat_dec_le(v___x_882_, v___x_882_);
if (v___x_888_ == 0)
{
if (v___x_884_ == 0)
{
lean_object* v___x_890_; 
lean_dec_ref(v_tail_873_);
lean_dec(v_mvarId_862_);
lean_dec(v_fvarId_861_);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 0, v___x_883_);
v___x_890_ = v___x_880_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_883_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
else
{
size_t v___x_892_; size_t v___x_893_; lean_object* v___x_894_; 
lean_del_object(v___x_880_);
v___x_892_ = ((size_t)0ULL);
v___x_893_ = lean_usize_of_nat(v___x_882_);
v___x_894_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_861_, v_mvarId_862_, v_tail_873_, v___x_892_, v___x_893_, v___x_883_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
lean_dec_ref(v_tail_873_);
return v___x_894_;
}
}
else
{
size_t v___x_895_; size_t v___x_896_; lean_object* v___x_897_; 
lean_del_object(v___x_880_);
v___x_895_ = ((size_t)0ULL);
v___x_896_ = lean_usize_of_nat(v___x_882_);
v___x_897_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_861_, v_mvarId_862_, v_tail_873_, v___x_895_, v___x_896_, v___x_883_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
lean_dec_ref(v_tail_873_);
return v___x_897_;
}
}
}
}
else
{
lean_dec_ref(v_tail_873_);
lean_dec(v_mvarId_862_);
lean_dec(v_fvarId_861_);
return v___x_878_;
}
}
else
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; uint8_t v___x_903_; 
lean_dec_ref(v_root_872_);
v___x_900_ = lean_nat_sub(v_start_864_, v_tailOff_875_);
lean_dec(v_tailOff_875_);
v___x_901_ = lean_array_get_size(v_tail_873_);
v___x_902_ = lean_box(0);
v___x_903_ = lean_nat_dec_lt(v___x_900_, v___x_901_);
if (v___x_903_ == 0)
{
lean_object* v___x_904_; 
lean_dec(v___x_900_);
lean_dec_ref(v_tail_873_);
lean_dec(v_mvarId_862_);
lean_dec(v_fvarId_861_);
v___x_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_904_, 0, v___x_902_);
return v___x_904_;
}
else
{
uint8_t v___x_905_; 
v___x_905_ = lean_nat_dec_le(v___x_901_, v___x_901_);
if (v___x_905_ == 0)
{
if (v___x_903_ == 0)
{
lean_object* v___x_906_; 
lean_dec(v___x_900_);
lean_dec_ref(v_tail_873_);
lean_dec(v_mvarId_862_);
lean_dec(v_fvarId_861_);
v___x_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_906_, 0, v___x_902_);
return v___x_906_;
}
else
{
size_t v___x_907_; size_t v___x_908_; lean_object* v___x_909_; 
v___x_907_ = lean_usize_of_nat(v___x_900_);
lean_dec(v___x_900_);
v___x_908_ = lean_usize_of_nat(v___x_901_);
v___x_909_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_861_, v_mvarId_862_, v_tail_873_, v___x_907_, v___x_908_, v___x_902_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
lean_dec_ref(v_tail_873_);
return v___x_909_;
}
}
else
{
size_t v___x_910_; size_t v___x_911_; lean_object* v___x_912_; 
v___x_910_ = lean_usize_of_nat(v___x_900_);
lean_dec(v___x_900_);
v___x_911_ = lean_usize_of_nat(v___x_901_);
v___x_912_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_861_, v_mvarId_862_, v_tail_873_, v___x_910_, v___x_911_, v___x_902_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
lean_dec_ref(v_tail_873_);
return v___x_912_;
}
}
}
}
else
{
lean_object* v___x_913_; 
v___x_913_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6(v_fvarId_861_, v_mvarId_862_, v_t_863_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
return v___x_913_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1___boxed(lean_object* v_fvarId_914_, lean_object* v_mvarId_915_, lean_object* v_t_916_, lean_object* v_start_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1(v_fvarId_914_, v_mvarId_915_, v_t_916_, v_start_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v_start_917_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1(lean_object* v_fvarId_924_, lean_object* v_mvarId_925_, lean_object* v_lctx_926_, lean_object* v_start_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v_decls_933_; lean_object* v___x_934_; 
v_decls_933_ = lean_ctor_get(v_lctx_926_, 1);
lean_inc_ref(v_decls_933_);
lean_dec_ref(v_lctx_926_);
v___x_934_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1(v_fvarId_924_, v_mvarId_925_, v_decls_933_, v_start_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1___boxed(lean_object* v_fvarId_935_, lean_object* v_mvarId_936_, lean_object* v_lctx_937_, lean_object* v_start_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1(v_fvarId_935_, v_mvarId_936_, v_lctx_937_, v_start_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v_start_938_);
return v_res_944_;
}
}
static lean_object* _init_l_Lean_MVarId_clear___lam__1___closed__1(void){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_946_ = ((lean_object*)(l_Lean_MVarId_clear___lam__1___closed__0));
v___x_947_ = l_Lean_stringToMessageData(v___x_946_);
return v___x_947_;
}
}
static lean_object* _init_l_Lean_MVarId_clear___lam__1___closed__3(void){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_949_ = ((lean_object*)(l_Lean_MVarId_clear___lam__1___closed__2));
v___x_950_ = l_Lean_stringToMessageData(v___x_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clear___lam__1(lean_object* v_mvarId_951_, lean_object* v___x_952_, lean_object* v_fvarId_953_, lean_object* v___f_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v___y_967_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___x_991_; 
lean_inc(v___x_952_);
lean_inc(v_mvarId_951_);
v___x_991_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_951_, v___x_952_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v_lctx_992_; lean_object* v___y_994_; lean_object* v___y_995_; lean_object* v___y_996_; lean_object* v___y_997_; lean_object* v___y_998_; lean_object* v___y_999_; lean_object* v___y_1000_; lean_object* v___y_1007_; lean_object* v___y_1008_; lean_object* v___y_1009_; lean_object* v___y_1010_; uint8_t v___x_1067_; 
lean_dec_ref(v___x_991_);
v_lctx_992_ = lean_ctor_get(v___y_955_, 2);
lean_inc_ref(v_lctx_992_);
v___x_1067_ = l_Lean_LocalContext_contains(v_lctx_992_, v_fvarId_953_);
if (v___x_1067_ == 0)
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1068_ = lean_obj_once(&l_Lean_MVarId_clear___lam__1___closed__3, &l_Lean_MVarId_clear___lam__1___closed__3_once, _init_l_Lean_MVarId_clear___lam__1___closed__3);
lean_inc(v_fvarId_953_);
v___x_1069_ = l_Lean_mkFVar(v_fvarId_953_);
v___x_1070_ = l_Lean_MessageData_ofExpr(v___x_1069_);
v___x_1071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1068_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
v___x_1072_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7);
v___x_1073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1071_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
v___x_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1073_);
lean_inc(v_mvarId_951_);
lean_inc(v___x_952_);
v___x_1075_ = l_Lean_Meta_throwTacticEx___redArg(v___x_952_, v_mvarId_951_, v___x_1074_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_dec_ref(v___x_1075_);
v___y_1007_ = v___y_955_;
v___y_1008_ = v___y_956_;
v___y_1009_ = v___y_957_;
v___y_1010_ = v___y_958_;
goto v___jp_1006_;
}
else
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1083_; 
lean_dec_ref(v_lctx_992_);
lean_dec_ref(v___y_955_);
lean_dec_ref(v___f_954_);
lean_dec(v_fvarId_953_);
lean_dec(v___x_952_);
lean_dec(v_mvarId_951_);
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
else
{
v___y_1007_ = v___y_955_;
v___y_1008_ = v___y_956_;
v___y_1009_ = v___y_957_;
v___y_1010_ = v___y_958_;
goto v___jp_1006_;
}
v___jp_993_:
{
lean_object* v_localInstances_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v_localInstances_1001_ = lean_ctor_get(v___y_997_, 3);
v___x_1002_ = lean_local_ctx_erase(v_lctx_992_, v_fvarId_953_);
lean_inc(v___y_995_);
v___x_1003_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_954_, v_localInstances_1001_, v___y_995_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_inc_ref(v_localInstances_1001_);
v___y_961_ = v___y_999_;
v___y_962_ = v___y_1000_;
v___y_963_ = v___y_994_;
v___y_964_ = v___y_998_;
v___y_965_ = v___y_995_;
v___y_966_ = v___y_996_;
v___y_967_ = v___y_997_;
v___y_968_ = v___x_1002_;
v___y_969_ = v_localInstances_1001_;
goto v___jp_960_;
}
else
{
lean_object* v_val_1004_; lean_object* v___x_1005_; 
v_val_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_val_1004_);
lean_dec_ref(v___x_1003_);
lean_inc_ref(v_localInstances_1001_);
v___x_1005_ = l_Array_eraseIdx___redArg(v_localInstances_1001_, v_val_1004_);
v___y_961_ = v___y_999_;
v___y_962_ = v___y_1000_;
v___y_963_ = v___y_994_;
v___y_964_ = v___y_998_;
v___y_965_ = v___y_995_;
v___y_966_ = v___y_996_;
v___y_967_ = v___y_997_;
v___y_968_ = v___x_1002_;
v___y_969_ = v___x_1005_;
goto v___jp_960_;
}
}
v___jp_1006_:
{
lean_object* v___x_1011_; 
lean_inc(v_mvarId_951_);
v___x_1011_ = l_Lean_MVarId_getTag(v_mvarId_951_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_a_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_a_1012_);
lean_dec_ref(v___x_1011_);
v___x_1013_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_lctx_992_);
lean_inc(v_mvarId_951_);
lean_inc(v_fvarId_953_);
v___x_1014_ = l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1(v_fvarId_953_, v_mvarId_951_, v_lctx_992_, v___x_1013_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v___x_1015_; 
lean_dec_ref(v___x_1014_);
lean_inc(v_mvarId_951_);
v___x_1015_ = l_Lean_MVarId_getDecl(v_mvarId_951_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v_a_1016_; lean_object* v_type_1017_; lean_object* v___x_1018_; lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1042_; 
v_a_1016_ = lean_ctor_get(v___x_1015_, 0);
lean_inc(v_a_1016_);
lean_dec_ref(v___x_1015_);
v_type_1017_ = lean_ctor_get(v_a_1016_, 2);
lean_inc_ref_n(v_type_1017_, 2);
lean_dec(v_a_1016_);
lean_inc(v_fvarId_953_);
v___x_1018_ = l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3___redArg(v_type_1017_, v_fvarId_953_, v___y_1008_);
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1021_ = v___x_1018_;
v_isShared_1022_ = v_isSharedCheck_1042_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_1018_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1042_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
uint8_t v___x_1023_; 
v___x_1023_ = lean_unbox(v_a_1019_);
lean_dec(v_a_1019_);
if (v___x_1023_ == 0)
{
lean_del_object(v___x_1021_);
lean_dec(v___x_952_);
v___y_994_ = v_type_1017_;
v___y_995_ = v___x_1013_;
v___y_996_ = v_a_1012_;
v___y_997_ = v___y_1007_;
v___y_998_ = v___y_1008_;
v___y_999_ = v___y_1009_;
v___y_1000_ = v___y_1010_;
goto v___jp_993_;
}
else
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1031_; 
v___x_1024_ = lean_obj_once(&l_Lean_MVarId_clear___lam__1___closed__1, &l_Lean_MVarId_clear___lam__1___closed__1_once, _init_l_Lean_MVarId_clear___lam__1___closed__1);
lean_inc(v_fvarId_953_);
v___x_1025_ = l_Lean_mkFVar(v_fvarId_953_);
v___x_1026_ = l_Lean_MessageData_ofExpr(v___x_1025_);
v___x_1027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1024_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
v___x_1028_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7);
v___x_1029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1027_);
lean_ctor_set(v___x_1029_, 1, v___x_1028_);
if (v_isShared_1022_ == 0)
{
lean_ctor_set_tag(v___x_1021_, 1);
lean_ctor_set(v___x_1021_, 0, v___x_1029_);
v___x_1031_ = v___x_1021_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v___x_1029_);
v___x_1031_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
lean_object* v___x_1032_; 
lean_inc(v_mvarId_951_);
v___x_1032_ = l_Lean_Meta_throwTacticEx___redArg(v___x_952_, v_mvarId_951_, v___x_1031_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_dec_ref(v___x_1032_);
v___y_994_ = v_type_1017_;
v___y_995_ = v___x_1013_;
v___y_996_ = v_a_1012_;
v___y_997_ = v___y_1007_;
v___y_998_ = v___y_1008_;
v___y_999_ = v___y_1009_;
v___y_1000_ = v___y_1010_;
goto v___jp_993_;
}
else
{
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1040_; 
lean_dec_ref(v_type_1017_);
lean_dec(v_a_1012_);
lean_dec_ref(v___y_1007_);
lean_dec_ref(v_lctx_992_);
lean_dec_ref(v___f_954_);
lean_dec(v_fvarId_953_);
lean_dec(v_mvarId_951_);
v_a_1033_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1035_ = v___x_1032_;
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v___x_1032_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1038_; 
if (v_isShared_1036_ == 0)
{
v___x_1038_ = v___x_1035_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_a_1033_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1050_; 
lean_dec(v_a_1012_);
lean_dec_ref(v___y_1007_);
lean_dec_ref(v_lctx_992_);
lean_dec_ref(v___f_954_);
lean_dec(v_fvarId_953_);
lean_dec(v___x_952_);
lean_dec(v_mvarId_951_);
v_a_1043_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1045_ = v___x_1015_;
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___x_1015_);
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
else
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1058_; 
lean_dec(v_a_1012_);
lean_dec_ref(v___y_1007_);
lean_dec_ref(v_lctx_992_);
lean_dec_ref(v___f_954_);
lean_dec(v_fvarId_953_);
lean_dec(v___x_952_);
lean_dec(v_mvarId_951_);
v_a_1051_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1053_ = v___x_1014_;
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_1014_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1056_; 
if (v_isShared_1054_ == 0)
{
v___x_1056_ = v___x_1053_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_a_1051_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
else
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1066_; 
lean_dec_ref(v___y_1007_);
lean_dec_ref(v_lctx_992_);
lean_dec_ref(v___f_954_);
lean_dec(v_fvarId_953_);
lean_dec(v___x_952_);
lean_dec(v_mvarId_951_);
v_a_1059_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1061_ = v___x_1011_;
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_1011_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1064_; 
if (v_isShared_1062_ == 0)
{
v___x_1064_ = v___x_1061_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_a_1059_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
}
}
else
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1091_; 
lean_dec_ref(v___y_955_);
lean_dec_ref(v___f_954_);
lean_dec(v_fvarId_953_);
lean_dec(v___x_952_);
lean_dec(v_mvarId_951_);
v_a_1084_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1086_ = v___x_991_;
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_991_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1089_; 
if (v_isShared_1087_ == 0)
{
v___x_1089_ = v___x_1086_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_a_1084_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
v___jp_960_:
{
uint8_t v___x_970_; lean_object* v___x_971_; 
v___x_970_ = 2;
v___x_971_ = l_Lean_Meta_mkFreshExprMVarAt(v___y_968_, v___y_969_, v___y_963_, v___x_970_, v___y_966_, v___y_965_, v___y_967_, v___y_964_, v___y_961_, v___y_962_);
lean_dec_ref(v___y_967_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v_a_972_; lean_object* v___x_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_981_; 
v_a_972_ = lean_ctor_get(v___x_971_, 0);
lean_inc_n(v_a_972_, 2);
lean_dec_ref(v___x_971_);
v___x_973_ = l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg(v_mvarId_951_, v_a_972_, v___y_964_);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_981_ == 0)
{
lean_object* v_unused_982_; 
v_unused_982_ = lean_ctor_get(v___x_973_, 0);
lean_dec(v_unused_982_);
v___x_975_ = v___x_973_;
v_isShared_976_ = v_isSharedCheck_981_;
goto v_resetjp_974_;
}
else
{
lean_dec(v___x_973_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_981_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_977_; lean_object* v___x_979_; 
v___x_977_ = l_Lean_Expr_mvarId_x21(v_a_972_);
lean_dec(v_a_972_);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v___x_977_);
v___x_979_ = v___x_975_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v___x_977_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
else
{
lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_990_; 
lean_dec(v_mvarId_951_);
v_a_983_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_990_ == 0)
{
v___x_985_ = v___x_971_;
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_971_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_988_; 
if (v_isShared_986_ == 0)
{
v___x_988_ = v___x_985_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_a_983_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clear___lam__1___boxed(lean_object* v_mvarId_1092_, lean_object* v___x_1093_, lean_object* v_fvarId_1094_, lean_object* v___f_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Lean_MVarId_clear___lam__1(v_mvarId_1092_, v___x_1093_, v_fvarId_1094_, v___f_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v___y_1097_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clear(lean_object* v_mvarId_1102_, lean_object* v_fvarId_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_){
_start:
{
lean_object* v___f_1109_; lean_object* v___x_1110_; lean_object* v___f_1111_; lean_object* v___x_1112_; 
lean_inc(v_fvarId_1103_);
v___f_1109_ = lean_alloc_closure((void*)(l_Lean_MVarId_clear___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1109_, 0, v_fvarId_1103_);
v___x_1110_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__1));
lean_inc(v_mvarId_1102_);
v___f_1111_ = lean_alloc_closure((void*)(l_Lean_MVarId_clear___lam__1___boxed), 9, 4);
lean_closure_set(v___f_1111_, 0, v_mvarId_1102_);
lean_closure_set(v___f_1111_, 1, v___x_1110_);
lean_closure_set(v___f_1111_, 2, v_fvarId_1103_);
lean_closure_set(v___f_1111_, 3, v___f_1109_);
v___x_1112_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg(v_mvarId_1102_, v___f_1111_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clear___boxed(lean_object* v_mvarId_1113_, lean_object* v_fvarId_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Lean_MVarId_clear(v_mvarId_1113_, v_fvarId_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_);
lean_dec(v_a_1118_);
lean_dec_ref(v_a_1117_);
lean_dec(v_a_1116_);
lean_dec_ref(v_a_1115_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2(lean_object* v_mvarId_1121_, lean_object* v_val_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v___x_1128_; 
v___x_1128_ = l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg(v_mvarId_1121_, v_val_1122_, v___y_1124_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___boxed(lean_object* v_mvarId_1129_, lean_object* v_val_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2(v_mvarId_1129_, v_val_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3(lean_object* v_00_u03b2_1137_, lean_object* v_x_1138_, lean_object* v_x_1139_, lean_object* v_x_1140_){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3___redArg(v_x_1138_, v_x_1139_, v_x_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9(lean_object* v_00_u03b2_1142_, lean_object* v_x_1143_, size_t v_x_1144_, size_t v_x_1145_, lean_object* v_x_1146_, lean_object* v_x_1147_){
_start:
{
lean_object* v___x_1148_; 
v___x_1148_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_x_1143_, v_x_1144_, v_x_1145_, v_x_1146_, v_x_1147_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___boxed(lean_object* v_00_u03b2_1149_, lean_object* v_x_1150_, lean_object* v_x_1151_, lean_object* v_x_1152_, lean_object* v_x_1153_, lean_object* v_x_1154_){
_start:
{
size_t v_x_10134__boxed_1155_; size_t v_x_10135__boxed_1156_; lean_object* v_res_1157_; 
v_x_10134__boxed_1155_ = lean_unbox_usize(v_x_1151_);
lean_dec(v_x_1151_);
v_x_10135__boxed_1156_ = lean_unbox_usize(v_x_1152_);
lean_dec(v_x_1152_);
v_res_1157_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9(v_00_u03b2_1149_, v_x_1150_, v_x_10134__boxed_1155_, v_x_10135__boxed_1156_, v_x_1153_, v_x_1154_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13(lean_object* v_00_u03b2_1158_, lean_object* v_n_1159_, lean_object* v_k_1160_, lean_object* v_v_1161_){
_start:
{
lean_object* v___x_1162_; 
v___x_1162_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13___redArg(v_n_1159_, v_k_1160_, v_v_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14(lean_object* v_00_u03b2_1163_, size_t v_depth_1164_, lean_object* v_keys_1165_, lean_object* v_vals_1166_, lean_object* v_heq_1167_, lean_object* v_i_1168_, lean_object* v_entries_1169_){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg(v_depth_1164_, v_keys_1165_, v_vals_1166_, v_i_1168_, v_entries_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___boxed(lean_object* v_00_u03b2_1171_, lean_object* v_depth_1172_, lean_object* v_keys_1173_, lean_object* v_vals_1174_, lean_object* v_heq_1175_, lean_object* v_i_1176_, lean_object* v_entries_1177_){
_start:
{
size_t v_depth_boxed_1178_; lean_object* v_res_1179_; 
v_depth_boxed_1178_ = lean_unbox_usize(v_depth_1172_);
lean_dec(v_depth_1172_);
v_res_1179_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14(v_00_u03b2_1171_, v_depth_boxed_1178_, v_keys_1173_, v_vals_1174_, v_heq_1175_, v_i_1176_, v_entries_1177_);
lean_dec_ref(v_vals_1174_);
lean_dec_ref(v_keys_1173_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13_spec__14(lean_object* v_00_u03b2_1180_, lean_object* v_x_1181_, lean_object* v_x_1182_, lean_object* v_x_1183_, lean_object* v_x_1184_){
_start:
{
lean_object* v___x_1185_; 
v___x_1185_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13_spec__14___redArg(v_x_1181_, v_x_1182_, v_x_1183_, v_x_1184_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClear(lean_object* v_mvarId_1186_, lean_object* v_fvarId_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_){
_start:
{
lean_object* v___x_1193_; 
v___x_1193_ = l_Lean_Meta_saveState___redArg(v_a_1189_, v_a_1191_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_object* v_a_1194_; lean_object* v___x_1195_; 
v_a_1194_ = lean_ctor_get(v___x_1193_, 0);
lean_inc(v_a_1194_);
lean_dec_ref(v___x_1193_);
lean_inc(v_mvarId_1186_);
v___x_1195_ = l_Lean_MVarId_clear(v_mvarId_1186_, v_fvarId_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_);
if (lean_obj_tag(v___x_1195_) == 0)
{
lean_dec(v_a_1194_);
lean_dec(v_mvarId_1186_);
return v___x_1195_;
}
else
{
lean_object* v_a_1196_; uint8_t v___y_1198_; uint8_t v___x_1216_; 
v_a_1196_ = lean_ctor_get(v___x_1195_, 0);
lean_inc(v_a_1196_);
v___x_1216_ = l_Lean_Exception_isInterrupt(v_a_1196_);
if (v___x_1216_ == 0)
{
uint8_t v___x_1217_; 
v___x_1217_ = l_Lean_Exception_isRuntime(v_a_1196_);
v___y_1198_ = v___x_1217_;
goto v___jp_1197_;
}
else
{
lean_dec(v_a_1196_);
v___y_1198_ = v___x_1216_;
goto v___jp_1197_;
}
v___jp_1197_:
{
if (v___y_1198_ == 0)
{
lean_object* v___x_1199_; 
lean_dec_ref(v___x_1195_);
v___x_1199_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1194_, v_a_1189_, v_a_1191_);
lean_dec(v_a_1194_);
if (lean_obj_tag(v___x_1199_) == 0)
{
lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1206_; 
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1199_);
if (v_isSharedCheck_1206_ == 0)
{
lean_object* v_unused_1207_; 
v_unused_1207_ = lean_ctor_get(v___x_1199_, 0);
lean_dec(v_unused_1207_);
v___x_1201_ = v___x_1199_;
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
else
{
lean_dec(v___x_1199_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1204_; 
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 0, v_mvarId_1186_);
v___x_1204_ = v___x_1201_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_mvarId_1186_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
else
{
lean_object* v_a_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1215_; 
lean_dec(v_mvarId_1186_);
v_a_1208_ = lean_ctor_get(v___x_1199_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1199_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1210_ = v___x_1199_;
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_a_1208_);
lean_dec(v___x_1199_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1213_; 
if (v_isShared_1211_ == 0)
{
v___x_1213_ = v___x_1210_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_a_1208_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
}
else
{
lean_dec(v_a_1194_);
lean_dec(v_mvarId_1186_);
return v___x_1195_;
}
}
}
}
else
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1225_; 
lean_dec(v_fvarId_1187_);
lean_dec(v_mvarId_1186_);
v_a_1218_ = lean_ctor_get(v___x_1193_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1220_ = v___x_1193_;
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1193_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClear___boxed(lean_object* v_mvarId_1226_, lean_object* v_fvarId_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_Lean_MVarId_tryClear(v_mvarId_1226_, v_fvarId_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_);
lean_dec(v_a_1231_);
lean_dec_ref(v_a_1230_);
lean_dec(v_a_1229_);
lean_dec_ref(v_a_1228_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0(lean_object* v_as_1234_, size_t v_i_1235_, size_t v_stop_1236_, lean_object* v_b_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
uint8_t v___x_1243_; 
v___x_1243_ = lean_usize_dec_eq(v_i_1235_, v_stop_1236_);
if (v___x_1243_ == 0)
{
size_t v___x_1244_; size_t v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1244_ = ((size_t)1ULL);
v___x_1245_ = lean_usize_sub(v_i_1235_, v___x_1244_);
v___x_1246_ = lean_array_uget_borrowed(v_as_1234_, v___x_1245_);
lean_inc(v___x_1246_);
v___x_1247_ = l_Lean_MVarId_tryClear(v_b_1237_, v___x_1246_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v_a_1248_; 
v_a_1248_ = lean_ctor_get(v___x_1247_, 0);
lean_inc(v_a_1248_);
lean_dec_ref(v___x_1247_);
v_i_1235_ = v___x_1245_;
v_b_1237_ = v_a_1248_;
goto _start;
}
else
{
return v___x_1247_;
}
}
else
{
lean_object* v___x_1250_; 
v___x_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1250_, 0, v_b_1237_);
return v___x_1250_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0___boxed(lean_object* v_as_1251_, lean_object* v_i_1252_, lean_object* v_stop_1253_, lean_object* v_b_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
size_t v_i_boxed_1260_; size_t v_stop_boxed_1261_; lean_object* v_res_1262_; 
v_i_boxed_1260_ = lean_unbox_usize(v_i_1252_);
lean_dec(v_i_1252_);
v_stop_boxed_1261_ = lean_unbox_usize(v_stop_1253_);
lean_dec(v_stop_1253_);
v_res_1262_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0(v_as_1251_, v_i_boxed_1260_, v_stop_boxed_1261_, v_b_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec_ref(v_as_1251_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany(lean_object* v_mvarId_1263_, lean_object* v_fvarIds_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_){
_start:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; uint8_t v___x_1272_; 
v___x_1270_ = lean_array_get_size(v_fvarIds_1264_);
v___x_1271_ = lean_unsigned_to_nat(0u);
v___x_1272_ = lean_nat_dec_lt(v___x_1271_, v___x_1270_);
if (v___x_1272_ == 0)
{
lean_object* v___x_1273_; 
v___x_1273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1273_, 0, v_mvarId_1263_);
return v___x_1273_;
}
else
{
size_t v___x_1274_; size_t v___x_1275_; lean_object* v___x_1276_; 
v___x_1274_ = lean_usize_of_nat(v___x_1270_);
v___x_1275_ = ((size_t)0ULL);
v___x_1276_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0(v_fvarIds_1264_, v___x_1274_, v___x_1275_, v_mvarId_1263_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
return v___x_1276_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany___boxed(lean_object* v_mvarId_1277_, lean_object* v_fvarIds_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Lean_MVarId_tryClearMany(v_mvarId_1277_, v_fvarIds_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
lean_dec(v_a_1282_);
lean_dec_ref(v_a_1281_);
lean_dec(v_a_1280_);
lean_dec_ref(v_a_1279_);
lean_dec_ref(v_fvarIds_1278_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0(lean_object* v_as_1285_, size_t v_i_1286_, size_t v_stop_1287_, lean_object* v_b_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_){
_start:
{
uint8_t v___x_1294_; 
v___x_1294_ = lean_usize_dec_eq(v_i_1286_, v_stop_1287_);
if (v___x_1294_ == 0)
{
lean_object* v_fst_1295_; lean_object* v_snd_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1321_; 
v_fst_1295_ = lean_ctor_get(v_b_1288_, 0);
v_snd_1296_ = lean_ctor_get(v_b_1288_, 1);
v_isSharedCheck_1321_ = !lean_is_exclusive(v_b_1288_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1298_ = v_b_1288_;
v_isShared_1299_ = v_isSharedCheck_1321_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_snd_1296_);
lean_inc(v_fst_1295_);
lean_dec(v_b_1288_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1321_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
size_t v___x_1300_; size_t v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1300_ = ((size_t)1ULL);
v___x_1301_ = lean_usize_sub(v_i_1286_, v___x_1300_);
v___x_1302_ = lean_array_uget_borrowed(v_as_1285_, v___x_1301_);
lean_inc(v___x_1302_);
lean_inc(v_fst_1295_);
v___x_1303_ = l_Lean_MVarId_tryClear(v_fst_1295_, v___x_1302_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_object* v_a_1304_; lean_object* v___y_1306_; uint8_t v___x_1311_; 
v_a_1304_ = lean_ctor_get(v___x_1303_, 0);
lean_inc(v_a_1304_);
lean_dec_ref(v___x_1303_);
v___x_1311_ = l_Lean_instBEqMVarId_beq(v_fst_1295_, v_a_1304_);
lean_dec(v_fst_1295_);
if (v___x_1311_ == 0)
{
lean_object* v___x_1312_; 
lean_inc(v___x_1302_);
v___x_1312_ = lean_array_push(v_snd_1296_, v___x_1302_);
v___y_1306_ = v___x_1312_;
goto v___jp_1305_;
}
else
{
v___y_1306_ = v_snd_1296_;
goto v___jp_1305_;
}
v___jp_1305_:
{
lean_object* v___x_1308_; 
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 1, v___y_1306_);
lean_ctor_set(v___x_1298_, 0, v_a_1304_);
v___x_1308_ = v___x_1298_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v___y_1306_);
v___x_1308_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
v_i_1286_ = v___x_1301_;
v_b_1288_ = v___x_1308_;
goto _start;
}
}
}
else
{
lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1320_; 
lean_del_object(v___x_1298_);
lean_dec(v_snd_1296_);
lean_dec(v_fst_1295_);
v_a_1313_ = lean_ctor_get(v___x_1303_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1315_ = v___x_1303_;
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v___x_1303_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1318_; 
if (v_isShared_1316_ == 0)
{
v___x_1318_ = v___x_1315_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_a_1313_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
}
}
else
{
lean_object* v___x_1322_; 
v___x_1322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1322_, 0, v_b_1288_);
return v___x_1322_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0___boxed(lean_object* v_as_1323_, lean_object* v_i_1324_, lean_object* v_stop_1325_, lean_object* v_b_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
size_t v_i_boxed_1332_; size_t v_stop_boxed_1333_; lean_object* v_res_1334_; 
v_i_boxed_1332_ = lean_unbox_usize(v_i_1324_);
lean_dec(v_i_1324_);
v_stop_boxed_1333_ = lean_unbox_usize(v_stop_1325_);
lean_dec(v_stop_1325_);
v_res_1334_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0(v_as_1323_, v_i_boxed_1332_, v_stop_boxed_1333_, v_b_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
lean_dec_ref(v_as_1323_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany_x27___lam__0(lean_object* v_fvarIds_1335_, lean_object* v_goal_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v_lctx_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; uint8_t v___x_1348_; 
v_lctx_1342_ = lean_ctor_get(v___y_1337_, 2);
lean_inc_ref(v_lctx_1342_);
v___x_1343_ = l_Lean_LocalContext_sortFVarsByContextOrder(v_lctx_1342_, v_fvarIds_1335_);
v___x_1344_ = lean_array_get_size(v___x_1343_);
v___x_1345_ = lean_mk_empty_array_with_capacity(v___x_1344_);
v___x_1346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1346_, 0, v_goal_1336_);
lean_ctor_set(v___x_1346_, 1, v___x_1345_);
v___x_1347_ = lean_unsigned_to_nat(0u);
v___x_1348_ = lean_nat_dec_lt(v___x_1347_, v___x_1344_);
if (v___x_1348_ == 0)
{
lean_object* v___x_1349_; 
lean_dec_ref(v___x_1343_);
lean_dec_ref(v___y_1337_);
v___x_1349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1346_);
return v___x_1349_;
}
else
{
size_t v___x_1350_; size_t v___x_1351_; lean_object* v___x_1352_; 
v___x_1350_ = lean_usize_of_nat(v___x_1344_);
v___x_1351_ = ((size_t)0ULL);
v___x_1352_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0(v___x_1343_, v___x_1350_, v___x_1351_, v___x_1346_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
lean_dec_ref(v___y_1337_);
lean_dec_ref(v___x_1343_);
return v___x_1352_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany_x27___lam__0___boxed(lean_object* v_fvarIds_1353_, lean_object* v_goal_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l_Lean_MVarId_tryClearMany_x27___lam__0(v_fvarIds_1353_, v_goal_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec(v___y_1356_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany_x27(lean_object* v_goal_1361_, lean_object* v_fvarIds_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_){
_start:
{
lean_object* v___f_1368_; lean_object* v___x_1369_; 
lean_inc(v_goal_1361_);
v___f_1368_ = lean_alloc_closure((void*)(l_Lean_MVarId_tryClearMany_x27___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1368_, 0, v_fvarIds_1362_);
lean_closure_set(v___f_1368_, 1, v_goal_1361_);
v___x_1369_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg(v_goal_1361_, v___f_1368_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany_x27___boxed(lean_object* v_goal_1370_, lean_object* v_fvarIds_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l_Lean_MVarId_tryClearMany_x27(v_goal_1370_, v_fvarIds_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_);
lean_dec(v_a_1375_);
lean_dec_ref(v_a_1374_);
lean_dec(v_a_1373_);
lean_dec_ref(v_a_1372_);
return v_res_1377_;
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
