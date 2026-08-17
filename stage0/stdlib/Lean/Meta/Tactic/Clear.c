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
lean_dec_ref_known(v_localDecl_20_, 4);
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
lean_dec_ref_known(v___x_81_, 2);
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
v___x_67_ = lean_st_ref_put(v___y_23_, v___x_66_);
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
lean_dec_ref_known(v_localDecl_20_, 5);
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
lean_dec_ref_known(v___x_138_, 2);
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
v___x_124_ = lean_st_ref_put(v___y_23_, v___x_123_);
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
v___x_39_ = lean_st_ref_put(v___y_23_, v___x_38_);
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
lean_dec_ref_known(v___x_203_, 2);
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
v___x_187_ = lean_st_ref_put(v___y_171_, v___x_186_);
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
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(lean_object* v_x_324_, size_t v_x_325_, size_t v_x_326_, lean_object* v_x_327_, lean_object* v_x_328_){
_start:
{
if (lean_obj_tag(v_x_324_) == 0)
{
lean_object* v_es_329_; size_t v___x_330_; size_t v___x_331_; lean_object* v_j_332_; lean_object* v___x_333_; uint8_t v___x_334_; 
v_es_329_ = lean_ctor_get(v_x_324_, 0);
v___x_330_ = ((size_t)31ULL);
v___x_331_ = lean_usize_land(v_x_325_, v___x_330_);
v_j_332_ = lean_usize_to_nat(v___x_331_);
v___x_333_ = lean_array_get_size(v_es_329_);
v___x_334_ = lean_nat_dec_lt(v_j_332_, v___x_333_);
if (v___x_334_ == 0)
{
lean_dec(v_j_332_);
lean_dec(v_x_328_);
lean_dec(v_x_327_);
return v_x_324_;
}
else
{
lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_373_; 
lean_inc_ref(v_es_329_);
v_isSharedCheck_373_ = !lean_is_exclusive(v_x_324_);
if (v_isSharedCheck_373_ == 0)
{
lean_object* v_unused_374_; 
v_unused_374_ = lean_ctor_get(v_x_324_, 0);
lean_dec(v_unused_374_);
v___x_336_ = v_x_324_;
v_isShared_337_ = v_isSharedCheck_373_;
goto v_resetjp_335_;
}
else
{
lean_dec(v_x_324_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_373_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v_v_338_; lean_object* v___x_339_; lean_object* v_xs_x27_340_; lean_object* v___y_342_; 
v_v_338_ = lean_array_fget(v_es_329_, v_j_332_);
v___x_339_ = lean_box(0);
v_xs_x27_340_ = lean_array_fset(v_es_329_, v_j_332_, v___x_339_);
switch(lean_obj_tag(v_v_338_))
{
case 0:
{
lean_object* v_key_347_; lean_object* v_val_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_358_; 
v_key_347_ = lean_ctor_get(v_v_338_, 0);
v_val_348_ = lean_ctor_get(v_v_338_, 1);
v_isSharedCheck_358_ = !lean_is_exclusive(v_v_338_);
if (v_isSharedCheck_358_ == 0)
{
v___x_350_ = v_v_338_;
v_isShared_351_ = v_isSharedCheck_358_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_val_348_);
lean_inc(v_key_347_);
lean_dec(v_v_338_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_358_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
uint8_t v___x_352_; 
v___x_352_ = l_Lean_instBEqMVarId_beq(v_x_327_, v_key_347_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; lean_object* v___x_354_; 
lean_del_object(v___x_350_);
v___x_353_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_347_, v_val_348_, v_x_327_, v_x_328_);
v___x_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
v___y_342_ = v___x_354_;
goto v___jp_341_;
}
else
{
lean_object* v___x_356_; 
lean_dec(v_val_348_);
lean_dec(v_key_347_);
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 1, v_x_328_);
lean_ctor_set(v___x_350_, 0, v_x_327_);
v___x_356_ = v___x_350_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_x_327_);
lean_ctor_set(v_reuseFailAlloc_357_, 1, v_x_328_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
v___y_342_ = v___x_356_;
goto v___jp_341_;
}
}
}
}
case 1:
{
lean_object* v_node_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_371_; 
v_node_359_ = lean_ctor_get(v_v_338_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v_v_338_);
if (v_isSharedCheck_371_ == 0)
{
v___x_361_ = v_v_338_;
v_isShared_362_ = v_isSharedCheck_371_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_node_359_);
lean_dec(v_v_338_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_371_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
size_t v___x_363_; size_t v___x_364_; size_t v___x_365_; size_t v___x_366_; lean_object* v___x_367_; lean_object* v___x_369_; 
v___x_363_ = ((size_t)5ULL);
v___x_364_ = lean_usize_shift_right(v_x_325_, v___x_363_);
v___x_365_ = ((size_t)1ULL);
v___x_366_ = lean_usize_add(v_x_326_, v___x_365_);
v___x_367_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_node_359_, v___x_364_, v___x_366_, v_x_327_, v_x_328_);
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 0, v___x_367_);
v___x_369_ = v___x_361_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v___x_367_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
v___y_342_ = v___x_369_;
goto v___jp_341_;
}
}
}
default: 
{
lean_object* v___x_372_; 
v___x_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_372_, 0, v_x_327_);
lean_ctor_set(v___x_372_, 1, v_x_328_);
v___y_342_ = v___x_372_;
goto v___jp_341_;
}
}
v___jp_341_:
{
lean_object* v___x_343_; lean_object* v___x_345_; 
v___x_343_ = lean_array_fset(v_xs_x27_340_, v_j_332_, v___y_342_);
lean_dec(v_j_332_);
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 0, v___x_343_);
v___x_345_ = v___x_336_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_343_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
}
else
{
lean_object* v_ks_375_; lean_object* v_vs_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_396_; 
v_ks_375_ = lean_ctor_get(v_x_324_, 0);
v_vs_376_ = lean_ctor_get(v_x_324_, 1);
v_isSharedCheck_396_ = !lean_is_exclusive(v_x_324_);
if (v_isSharedCheck_396_ == 0)
{
v___x_378_ = v_x_324_;
v_isShared_379_ = v_isSharedCheck_396_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_vs_376_);
lean_inc(v_ks_375_);
lean_dec(v_x_324_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_396_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_381_; 
if (v_isShared_379_ == 0)
{
v___x_381_ = v___x_378_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_ks_375_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v_vs_376_);
v___x_381_ = v_reuseFailAlloc_395_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
lean_object* v_newNode_382_; uint8_t v___y_384_; size_t v___x_390_; uint8_t v___x_391_; 
v_newNode_382_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13___redArg(v___x_381_, v_x_327_, v_x_328_);
v___x_390_ = ((size_t)7ULL);
v___x_391_ = lean_usize_dec_le(v___x_390_, v_x_326_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; lean_object* v___x_393_; uint8_t v___x_394_; 
v___x_392_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_382_);
v___x_393_ = lean_unsigned_to_nat(4u);
v___x_394_ = lean_nat_dec_lt(v___x_392_, v___x_393_);
lean_dec(v___x_392_);
v___y_384_ = v___x_394_;
goto v___jp_383_;
}
else
{
v___y_384_ = v___x_391_;
goto v___jp_383_;
}
v___jp_383_:
{
if (v___y_384_ == 0)
{
lean_object* v_ks_385_; lean_object* v_vs_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v_ks_385_ = lean_ctor_get(v_newNode_382_, 0);
lean_inc_ref(v_ks_385_);
v_vs_386_ = lean_ctor_get(v_newNode_382_, 1);
lean_inc_ref(v_vs_386_);
lean_dec_ref(v_newNode_382_);
v___x_387_ = lean_unsigned_to_nat(0u);
v___x_388_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__0);
v___x_389_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg(v_x_326_, v_ks_385_, v_vs_386_, v___x_387_, v___x_388_);
lean_dec_ref(v_vs_386_);
lean_dec_ref(v_ks_385_);
return v___x_389_;
}
else
{
return v_newNode_382_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg(size_t v_depth_397_, lean_object* v_keys_398_, lean_object* v_vals_399_, lean_object* v_i_400_, lean_object* v_entries_401_){
_start:
{
lean_object* v___x_402_; uint8_t v___x_403_; 
v___x_402_ = lean_array_get_size(v_keys_398_);
v___x_403_ = lean_nat_dec_lt(v_i_400_, v___x_402_);
if (v___x_403_ == 0)
{
lean_dec(v_i_400_);
return v_entries_401_;
}
else
{
lean_object* v_k_404_; lean_object* v_v_405_; uint64_t v___x_406_; size_t v_h_407_; size_t v___x_408_; lean_object* v___x_409_; size_t v___x_410_; size_t v___x_411_; size_t v___x_412_; size_t v_h_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v_k_404_ = lean_array_fget_borrowed(v_keys_398_, v_i_400_);
v_v_405_ = lean_array_fget_borrowed(v_vals_399_, v_i_400_);
v___x_406_ = l_Lean_instHashableMVarId_hash(v_k_404_);
v_h_407_ = lean_uint64_to_usize(v___x_406_);
v___x_408_ = ((size_t)5ULL);
v___x_409_ = lean_unsigned_to_nat(1u);
v___x_410_ = ((size_t)1ULL);
v___x_411_ = lean_usize_sub(v_depth_397_, v___x_410_);
v___x_412_ = lean_usize_mul(v___x_408_, v___x_411_);
v_h_413_ = lean_usize_shift_right(v_h_407_, v___x_412_);
v___x_414_ = lean_nat_add(v_i_400_, v___x_409_);
lean_dec(v_i_400_);
lean_inc(v_v_405_);
lean_inc(v_k_404_);
v___x_415_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_entries_401_, v_h_413_, v_depth_397_, v_k_404_, v_v_405_);
v_i_400_ = v___x_414_;
v_entries_401_ = v___x_415_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg___boxed(lean_object* v_depth_417_, lean_object* v_keys_418_, lean_object* v_vals_419_, lean_object* v_i_420_, lean_object* v_entries_421_){
_start:
{
size_t v_depth_boxed_422_; lean_object* v_res_423_; 
v_depth_boxed_422_ = lean_unbox_usize(v_depth_417_);
lean_dec(v_depth_417_);
v_res_423_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg(v_depth_boxed_422_, v_keys_418_, v_vals_419_, v_i_420_, v_entries_421_);
lean_dec_ref(v_vals_419_);
lean_dec_ref(v_keys_418_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___boxed(lean_object* v_x_424_, lean_object* v_x_425_, lean_object* v_x_426_, lean_object* v_x_427_, lean_object* v_x_428_){
_start:
{
size_t v_x_8831__boxed_429_; size_t v_x_8832__boxed_430_; lean_object* v_res_431_; 
v_x_8831__boxed_429_ = lean_unbox_usize(v_x_425_);
lean_dec(v_x_425_);
v_x_8832__boxed_430_ = lean_unbox_usize(v_x_426_);
lean_dec(v_x_426_);
v_res_431_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_x_424_, v_x_8831__boxed_429_, v_x_8832__boxed_430_, v_x_427_, v_x_428_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3___redArg(lean_object* v_x_432_, lean_object* v_x_433_, lean_object* v_x_434_){
_start:
{
uint64_t v___x_435_; size_t v___x_436_; size_t v___x_437_; lean_object* v___x_438_; 
v___x_435_ = l_Lean_instHashableMVarId_hash(v_x_433_);
v___x_436_ = lean_uint64_to_usize(v___x_435_);
v___x_437_ = ((size_t)1ULL);
v___x_438_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_x_432_, v___x_436_, v___x_437_, v_x_433_, v_x_434_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg(lean_object* v_mvarId_439_, lean_object* v_val_440_, lean_object* v___y_441_){
_start:
{
lean_object* v___x_443_; lean_object* v_mctx_444_; lean_object* v_cache_445_; lean_object* v_zetaDeltaFVarIds_446_; lean_object* v_postponed_447_; lean_object* v_diag_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_477_; 
v___x_443_ = lean_st_ref_take(v___y_441_);
v_mctx_444_ = lean_ctor_get(v___x_443_, 0);
v_cache_445_ = lean_ctor_get(v___x_443_, 1);
v_zetaDeltaFVarIds_446_ = lean_ctor_get(v___x_443_, 2);
v_postponed_447_ = lean_ctor_get(v___x_443_, 3);
v_diag_448_ = lean_ctor_get(v___x_443_, 4);
v_isSharedCheck_477_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_477_ == 0)
{
v___x_450_ = v___x_443_;
v_isShared_451_ = v_isSharedCheck_477_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_diag_448_);
lean_inc(v_postponed_447_);
lean_inc(v_zetaDeltaFVarIds_446_);
lean_inc(v_cache_445_);
lean_inc(v_mctx_444_);
lean_dec(v___x_443_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_477_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v_depth_452_; lean_object* v_levelAssignDepth_453_; lean_object* v_lmvarCounter_454_; lean_object* v_mvarCounter_455_; lean_object* v_lDecls_456_; lean_object* v_decls_457_; lean_object* v_userNames_458_; lean_object* v_lAssignment_459_; lean_object* v_eAssignment_460_; lean_object* v_dAssignment_461_; lean_object* v_instanceTypedMVars_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_476_; 
v_depth_452_ = lean_ctor_get(v_mctx_444_, 0);
v_levelAssignDepth_453_ = lean_ctor_get(v_mctx_444_, 1);
v_lmvarCounter_454_ = lean_ctor_get(v_mctx_444_, 2);
v_mvarCounter_455_ = lean_ctor_get(v_mctx_444_, 3);
v_lDecls_456_ = lean_ctor_get(v_mctx_444_, 4);
v_decls_457_ = lean_ctor_get(v_mctx_444_, 5);
v_userNames_458_ = lean_ctor_get(v_mctx_444_, 6);
v_lAssignment_459_ = lean_ctor_get(v_mctx_444_, 7);
v_eAssignment_460_ = lean_ctor_get(v_mctx_444_, 8);
v_dAssignment_461_ = lean_ctor_get(v_mctx_444_, 9);
v_instanceTypedMVars_462_ = lean_ctor_get(v_mctx_444_, 10);
v_isSharedCheck_476_ = !lean_is_exclusive(v_mctx_444_);
if (v_isSharedCheck_476_ == 0)
{
v___x_464_ = v_mctx_444_;
v_isShared_465_ = v_isSharedCheck_476_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_instanceTypedMVars_462_);
lean_inc(v_dAssignment_461_);
lean_inc(v_eAssignment_460_);
lean_inc(v_lAssignment_459_);
lean_inc(v_userNames_458_);
lean_inc(v_decls_457_);
lean_inc(v_lDecls_456_);
lean_inc(v_mvarCounter_455_);
lean_inc(v_lmvarCounter_454_);
lean_inc(v_levelAssignDepth_453_);
lean_inc(v_depth_452_);
lean_dec(v_mctx_444_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_476_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_466_; lean_object* v___x_468_; 
v___x_466_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3___redArg(v_eAssignment_460_, v_mvarId_439_, v_val_440_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 8, v___x_466_);
v___x_468_ = v___x_464_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_depth_452_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v_levelAssignDepth_453_);
lean_ctor_set(v_reuseFailAlloc_475_, 2, v_lmvarCounter_454_);
lean_ctor_set(v_reuseFailAlloc_475_, 3, v_mvarCounter_455_);
lean_ctor_set(v_reuseFailAlloc_475_, 4, v_lDecls_456_);
lean_ctor_set(v_reuseFailAlloc_475_, 5, v_decls_457_);
lean_ctor_set(v_reuseFailAlloc_475_, 6, v_userNames_458_);
lean_ctor_set(v_reuseFailAlloc_475_, 7, v_lAssignment_459_);
lean_ctor_set(v_reuseFailAlloc_475_, 8, v___x_466_);
lean_ctor_set(v_reuseFailAlloc_475_, 9, v_dAssignment_461_);
lean_ctor_set(v_reuseFailAlloc_475_, 10, v_instanceTypedMVars_462_);
v___x_468_ = v_reuseFailAlloc_475_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
lean_object* v___x_470_; 
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 0, v___x_468_);
v___x_470_ = v___x_450_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v___x_468_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v_cache_445_);
lean_ctor_set(v_reuseFailAlloc_474_, 2, v_zetaDeltaFVarIds_446_);
lean_ctor_set(v_reuseFailAlloc_474_, 3, v_postponed_447_);
lean_ctor_set(v_reuseFailAlloc_474_, 4, v_diag_448_);
v___x_470_ = v_reuseFailAlloc_474_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_471_ = lean_st_ref_put(v___y_441_, v___x_470_);
v___x_472_ = lean_box(0);
v___x_473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_473_, 0, v___x_472_);
return v___x_473_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg___boxed(lean_object* v_mvarId_478_, lean_object* v_val_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg(v_mvarId_478_, v_val_479_, v___y_480_);
lean_dec(v___y_480_);
return v_res_482_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__2));
v___x_488_ = l_Lean_stringToMessageData(v___x_487_);
return v___x_488_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5(void){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__4));
v___x_491_ = l_Lean_stringToMessageData(v___x_490_);
return v___x_491_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7(void){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__6));
v___x_494_ = l_Lean_stringToMessageData(v___x_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9(lean_object* v_fvarId_495_, lean_object* v_mvarId_496_, lean_object* v_as_497_, size_t v_i_498_, size_t v_stop_499_, lean_object* v_b_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v_a_507_; uint8_t v___x_511_; 
v___x_511_ = lean_usize_dec_eq(v_i_498_, v_stop_499_);
if (v___x_511_ == 0)
{
lean_object* v___x_512_; 
v___x_512_ = lean_array_uget(v_as_497_, v_i_498_);
if (lean_obj_tag(v___x_512_) == 0)
{
lean_object* v___x_513_; 
v___x_513_ = lean_box(0);
v_a_507_ = v___x_513_;
goto v___jp_506_;
}
else
{
lean_object* v_val_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_551_; 
v_val_514_ = lean_ctor_get(v___x_512_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_512_);
if (v_isSharedCheck_551_ == 0)
{
v___x_516_ = v___x_512_;
v_isShared_517_ = v_isSharedCheck_551_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_val_514_);
lean_dec(v___x_512_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_551_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_518_; uint8_t v___x_519_; 
v___x_518_ = l_Lean_LocalDecl_fvarId(v_val_514_);
v___x_519_ = l_Lean_instBEqFVarId_beq(v___x_518_, v_fvarId_495_);
lean_dec(v___x_518_);
if (v___x_519_ == 0)
{
uint8_t v___x_520_; lean_object* v___x_521_; 
v___x_520_ = 1;
lean_inc(v_fvarId_495_);
lean_inc(v_val_514_);
v___x_521_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg(v_val_514_, v_fvarId_495_, v___x_520_, v___y_502_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_522_; uint8_t v___x_523_; 
v_a_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc(v_a_522_);
lean_dec_ref_known(v___x_521_, 1);
v___x_523_ = lean_unbox(v_a_522_);
lean_dec(v_a_522_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; 
lean_del_object(v___x_516_);
lean_dec(v_val_514_);
v___x_524_ = lean_box(0);
v_a_507_ = v___x_524_;
goto v___jp_506_;
}
else
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_538_; 
v___x_525_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__1));
v___x_526_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3);
v___x_527_ = l_Lean_LocalDecl_toExpr(v_val_514_);
v___x_528_ = l_Lean_MessageData_ofExpr(v___x_527_);
v___x_529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_529_, 0, v___x_526_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
v___x_530_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5);
v___x_531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_529_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
lean_inc(v_fvarId_495_);
v___x_532_ = l_Lean_mkFVar(v_fvarId_495_);
v___x_533_ = l_Lean_MessageData_ofExpr(v___x_532_);
v___x_534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_531_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
v___x_535_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7);
v___x_536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_534_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 0, v___x_536_);
v___x_538_ = v___x_516_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v___x_536_);
v___x_538_ = v_reuseFailAlloc_541_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
lean_object* v___x_539_; 
lean_inc(v_mvarId_496_);
v___x_539_ = l_Lean_Meta_throwTacticEx___redArg(v___x_525_, v_mvarId_496_, v___x_538_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
if (lean_obj_tag(v___x_539_) == 0)
{
lean_object* v_a_540_; 
v_a_540_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_a_540_);
lean_dec_ref_known(v___x_539_, 1);
v_a_507_ = v_a_540_;
goto v___jp_506_;
}
else
{
lean_dec(v_mvarId_496_);
lean_dec(v_fvarId_495_);
return v___x_539_;
}
}
}
}
else
{
lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_549_; 
lean_del_object(v___x_516_);
lean_dec(v_val_514_);
lean_dec(v_mvarId_496_);
lean_dec(v_fvarId_495_);
v_a_542_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_549_ == 0)
{
v___x_544_ = v___x_521_;
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v___x_521_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_547_; 
if (v_isShared_545_ == 0)
{
v___x_547_ = v___x_544_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_a_542_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
else
{
lean_object* v___x_550_; 
lean_del_object(v___x_516_);
lean_dec(v_val_514_);
v___x_550_ = lean_box(0);
v_a_507_ = v___x_550_;
goto v___jp_506_;
}
}
}
}
else
{
lean_object* v___x_552_; 
lean_dec(v_mvarId_496_);
lean_dec(v_fvarId_495_);
v___x_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_552_, 0, v_b_500_);
return v___x_552_;
}
v___jp_506_:
{
size_t v___x_508_; size_t v___x_509_; 
v___x_508_ = ((size_t)1ULL);
v___x_509_ = lean_usize_add(v_i_498_, v___x_508_);
v_i_498_ = v___x_509_;
v_b_500_ = v_a_507_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___boxed(lean_object* v_fvarId_553_, lean_object* v_mvarId_554_, lean_object* v_as_555_, lean_object* v_i_556_, lean_object* v_stop_557_, lean_object* v_b_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
size_t v_i_boxed_564_; size_t v_stop_boxed_565_; lean_object* v_res_566_; 
v_i_boxed_564_ = lean_unbox_usize(v_i_556_);
lean_dec(v_i_556_);
v_stop_boxed_565_ = lean_unbox_usize(v_stop_557_);
lean_dec(v_stop_557_);
v_res_566_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9(v_fvarId_553_, v_mvarId_554_, v_as_555_, v_i_boxed_564_, v_stop_boxed_565_, v_b_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec_ref(v_as_555_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(lean_object* v_fvarId_567_, lean_object* v_mvarId_568_, lean_object* v_as_569_, size_t v_i_570_, size_t v_stop_571_, lean_object* v_b_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
lean_object* v_a_579_; uint8_t v___x_583_; 
v___x_583_ = lean_usize_dec_eq(v_i_570_, v_stop_571_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; 
v___x_584_ = lean_array_uget(v_as_569_, v_i_570_);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v___x_585_; 
v___x_585_ = lean_box(0);
v_a_579_ = v___x_585_;
goto v___jp_578_;
}
else
{
lean_object* v_val_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_623_; 
v_val_586_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_623_ == 0)
{
v___x_588_ = v___x_584_;
v_isShared_589_ = v_isSharedCheck_623_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_val_586_);
lean_dec(v___x_584_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_623_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_590_; uint8_t v___x_591_; 
v___x_590_ = l_Lean_LocalDecl_fvarId(v_val_586_);
v___x_591_ = l_Lean_instBEqFVarId_beq(v___x_590_, v_fvarId_567_);
lean_dec(v___x_590_);
if (v___x_591_ == 0)
{
uint8_t v___x_592_; lean_object* v___x_593_; 
v___x_592_ = 1;
lean_inc(v_fvarId_567_);
lean_inc(v_val_586_);
v___x_593_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg(v_val_586_, v_fvarId_567_, v___x_592_, v___y_574_);
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
lean_object* v___x_596_; 
lean_del_object(v___x_588_);
lean_dec(v_val_586_);
v___x_596_ = lean_box(0);
v_a_579_ = v___x_596_;
goto v___jp_578_;
}
else
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_610_; 
v___x_597_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__1));
v___x_598_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3);
v___x_599_ = l_Lean_LocalDecl_toExpr(v_val_586_);
v___x_600_ = l_Lean_MessageData_ofExpr(v___x_599_);
v___x_601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_598_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
v___x_602_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5);
v___x_603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_601_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
lean_inc(v_fvarId_567_);
v___x_604_ = l_Lean_mkFVar(v_fvarId_567_);
v___x_605_ = l_Lean_MessageData_ofExpr(v___x_604_);
v___x_606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_603_);
lean_ctor_set(v___x_606_, 1, v___x_605_);
v___x_607_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7);
v___x_608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_606_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 0, v___x_608_);
v___x_610_ = v___x_588_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_608_);
v___x_610_ = v_reuseFailAlloc_613_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
lean_object* v___x_611_; 
lean_inc(v_mvarId_568_);
v___x_611_ = l_Lean_Meta_throwTacticEx___redArg(v___x_597_, v_mvarId_568_, v___x_610_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
if (lean_obj_tag(v___x_611_) == 0)
{
lean_object* v_a_612_; 
v_a_612_ = lean_ctor_get(v___x_611_, 0);
lean_inc(v_a_612_);
lean_dec_ref_known(v___x_611_, 1);
v_a_579_ = v_a_612_;
goto v___jp_578_;
}
else
{
lean_dec(v_mvarId_568_);
lean_dec(v_fvarId_567_);
return v___x_611_;
}
}
}
}
else
{
lean_object* v_a_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_621_; 
lean_del_object(v___x_588_);
lean_dec(v_val_586_);
lean_dec(v_mvarId_568_);
lean_dec(v_fvarId_567_);
v_a_614_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_621_ == 0)
{
v___x_616_ = v___x_593_;
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_a_614_);
lean_dec(v___x_593_);
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
else
{
lean_object* v___x_622_; 
lean_del_object(v___x_588_);
lean_dec(v_val_586_);
v___x_622_ = lean_box(0);
v_a_579_ = v___x_622_;
goto v___jp_578_;
}
}
}
}
else
{
lean_object* v___x_624_; 
lean_dec(v_mvarId_568_);
lean_dec(v_fvarId_567_);
v___x_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_624_, 0, v_b_572_);
return v___x_624_;
}
v___jp_578_:
{
size_t v___x_580_; size_t v___x_581_; lean_object* v___x_582_; 
v___x_580_ = ((size_t)1ULL);
v___x_581_ = lean_usize_add(v_i_570_, v___x_580_);
v___x_582_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9(v_fvarId_567_, v_mvarId_568_, v_as_569_, v___x_581_, v_stop_571_, v_a_579_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
return v___x_582_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5___boxed(lean_object* v_fvarId_625_, lean_object* v_mvarId_626_, lean_object* v_as_627_, lean_object* v_i_628_, lean_object* v_stop_629_, lean_object* v_b_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
size_t v_i_boxed_636_; size_t v_stop_boxed_637_; lean_object* v_res_638_; 
v_i_boxed_636_ = lean_unbox_usize(v_i_628_);
lean_dec(v_i_628_);
v_stop_boxed_637_ = lean_unbox_usize(v_stop_629_);
lean_dec(v_stop_629_);
v_res_638_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_625_, v_mvarId_626_, v_as_627_, v_i_boxed_636_, v_stop_boxed_637_, v_b_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
lean_dec_ref(v_as_627_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6(lean_object* v_fvarId_639_, lean_object* v_mvarId_640_, lean_object* v_x_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
if (lean_obj_tag(v_x_641_) == 0)
{
lean_object* v_cs_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_668_; 
v_cs_647_ = lean_ctor_get(v_x_641_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v_x_641_);
if (v_isSharedCheck_668_ == 0)
{
v___x_649_ = v_x_641_;
v_isShared_650_ = v_isSharedCheck_668_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_cs_647_);
lean_dec(v_x_641_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_668_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; uint8_t v___x_654_; 
v___x_651_ = lean_unsigned_to_nat(0u);
v___x_652_ = lean_array_get_size(v_cs_647_);
v___x_653_ = lean_box(0);
v___x_654_ = lean_nat_dec_lt(v___x_651_, v___x_652_);
if (v___x_654_ == 0)
{
lean_object* v___x_656_; 
lean_dec_ref(v_cs_647_);
lean_dec(v_mvarId_640_);
lean_dec(v_fvarId_639_);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 0, v___x_653_);
v___x_656_ = v___x_649_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v___x_653_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
else
{
uint8_t v___x_658_; 
v___x_658_ = lean_nat_dec_le(v___x_652_, v___x_652_);
if (v___x_658_ == 0)
{
if (v___x_654_ == 0)
{
lean_object* v___x_660_; 
lean_dec_ref(v_cs_647_);
lean_dec(v_mvarId_640_);
lean_dec(v_fvarId_639_);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 0, v___x_653_);
v___x_660_ = v___x_649_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v___x_653_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
else
{
size_t v___x_662_; size_t v___x_663_; lean_object* v___x_664_; 
lean_del_object(v___x_649_);
v___x_662_ = ((size_t)0ULL);
v___x_663_ = lean_usize_of_nat(v___x_652_);
v___x_664_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(v_fvarId_639_, v_mvarId_640_, v_cs_647_, v___x_662_, v___x_663_, v___x_653_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
lean_dec_ref(v_cs_647_);
return v___x_664_;
}
}
else
{
size_t v___x_665_; size_t v___x_666_; lean_object* v___x_667_; 
lean_del_object(v___x_649_);
v___x_665_ = ((size_t)0ULL);
v___x_666_ = lean_usize_of_nat(v___x_652_);
v___x_667_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(v_fvarId_639_, v_mvarId_640_, v_cs_647_, v___x_665_, v___x_666_, v___x_653_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
lean_dec_ref(v_cs_647_);
return v___x_667_;
}
}
}
}
else
{
lean_object* v_vs_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_690_; 
v_vs_669_ = lean_ctor_get(v_x_641_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v_x_641_);
if (v_isSharedCheck_690_ == 0)
{
v___x_671_ = v_x_641_;
v_isShared_672_ = v_isSharedCheck_690_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_vs_669_);
lean_dec(v_x_641_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_690_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_673_ = lean_unsigned_to_nat(0u);
v___x_674_ = lean_array_get_size(v_vs_669_);
v___x_675_ = lean_box(0);
v___x_676_ = lean_nat_dec_lt(v___x_673_, v___x_674_);
if (v___x_676_ == 0)
{
lean_object* v___x_678_; 
lean_dec_ref(v_vs_669_);
lean_dec(v_mvarId_640_);
lean_dec(v_fvarId_639_);
if (v_isShared_672_ == 0)
{
lean_ctor_set_tag(v___x_671_, 0);
lean_ctor_set(v___x_671_, 0, v___x_675_);
v___x_678_ = v___x_671_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_675_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
else
{
uint8_t v___x_680_; 
v___x_680_ = lean_nat_dec_le(v___x_674_, v___x_674_);
if (v___x_680_ == 0)
{
if (v___x_676_ == 0)
{
lean_object* v___x_682_; 
lean_dec_ref(v_vs_669_);
lean_dec(v_mvarId_640_);
lean_dec(v_fvarId_639_);
if (v_isShared_672_ == 0)
{
lean_ctor_set_tag(v___x_671_, 0);
lean_ctor_set(v___x_671_, 0, v___x_675_);
v___x_682_ = v___x_671_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_675_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
else
{
size_t v___x_684_; size_t v___x_685_; lean_object* v___x_686_; 
lean_del_object(v___x_671_);
v___x_684_ = ((size_t)0ULL);
v___x_685_ = lean_usize_of_nat(v___x_674_);
v___x_686_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_639_, v_mvarId_640_, v_vs_669_, v___x_684_, v___x_685_, v___x_675_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
lean_dec_ref(v_vs_669_);
return v___x_686_;
}
}
else
{
size_t v___x_687_; size_t v___x_688_; lean_object* v___x_689_; 
lean_del_object(v___x_671_);
v___x_687_ = ((size_t)0ULL);
v___x_688_ = lean_usize_of_nat(v___x_674_);
v___x_689_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_639_, v_mvarId_640_, v_vs_669_, v___x_687_, v___x_688_, v___x_675_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
lean_dec_ref(v_vs_669_);
return v___x_689_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(lean_object* v_fvarId_691_, lean_object* v_mvarId_692_, lean_object* v_as_693_, size_t v_i_694_, size_t v_stop_695_, lean_object* v_b_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
uint8_t v___x_702_; 
v___x_702_ = lean_usize_dec_eq(v_i_694_, v_stop_695_);
if (v___x_702_ == 0)
{
lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_703_ = lean_array_uget_borrowed(v_as_693_, v_i_694_);
lean_inc(v___x_703_);
lean_inc(v_mvarId_692_);
lean_inc(v_fvarId_691_);
v___x_704_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6(v_fvarId_691_, v_mvarId_692_, v___x_703_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v_a_705_; size_t v___x_706_; size_t v___x_707_; 
v_a_705_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_a_705_);
lean_dec_ref_known(v___x_704_, 1);
v___x_706_ = ((size_t)1ULL);
v___x_707_ = lean_usize_add(v_i_694_, v___x_706_);
v_i_694_ = v___x_707_;
v_b_696_ = v_a_705_;
goto _start;
}
else
{
lean_dec(v_mvarId_692_);
lean_dec(v_fvarId_691_);
return v___x_704_;
}
}
else
{
lean_object* v___x_709_; 
lean_dec(v_mvarId_692_);
lean_dec(v_fvarId_691_);
v___x_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_709_, 0, v_b_696_);
return v___x_709_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7___boxed(lean_object* v_fvarId_710_, lean_object* v_mvarId_711_, lean_object* v_as_712_, lean_object* v_i_713_, lean_object* v_stop_714_, lean_object* v_b_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
size_t v_i_boxed_721_; size_t v_stop_boxed_722_; lean_object* v_res_723_; 
v_i_boxed_721_ = lean_unbox_usize(v_i_713_);
lean_dec(v_i_713_);
v_stop_boxed_722_ = lean_unbox_usize(v_stop_714_);
lean_dec(v_stop_714_);
v_res_723_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(v_fvarId_710_, v_mvarId_711_, v_as_712_, v_i_boxed_721_, v_stop_boxed_722_, v_b_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec_ref(v_as_712_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6___boxed(lean_object* v_fvarId_724_, lean_object* v_mvarId_725_, lean_object* v_x_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6(v_fvarId_724_, v_mvarId_725_, v_x_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6(lean_object* v_fvarId_733_, lean_object* v_mvarId_734_, lean_object* v_t_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
lean_object* v_root_741_; lean_object* v_tail_742_; lean_object* v___x_743_; 
v_root_741_ = lean_ctor_get(v_t_735_, 0);
lean_inc_ref(v_root_741_);
v_tail_742_ = lean_ctor_get(v_t_735_, 1);
lean_inc_ref(v_tail_742_);
lean_dec_ref(v_t_735_);
lean_inc(v_mvarId_734_);
lean_inc(v_fvarId_733_);
v___x_743_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6(v_fvarId_733_, v_mvarId_734_, v_root_741_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_764_; 
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_764_ == 0)
{
lean_object* v_unused_765_; 
v_unused_765_ = lean_ctor_get(v___x_743_, 0);
lean_dec(v_unused_765_);
v___x_745_ = v___x_743_;
v_isShared_746_ = v_isSharedCheck_764_;
goto v_resetjp_744_;
}
else
{
lean_dec(v___x_743_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_764_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; uint8_t v___x_750_; 
v___x_747_ = lean_unsigned_to_nat(0u);
v___x_748_ = lean_array_get_size(v_tail_742_);
v___x_749_ = lean_box(0);
v___x_750_ = lean_nat_dec_lt(v___x_747_, v___x_748_);
if (v___x_750_ == 0)
{
lean_object* v___x_752_; 
lean_dec_ref(v_tail_742_);
lean_dec(v_mvarId_734_);
lean_dec(v_fvarId_733_);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 0, v___x_749_);
v___x_752_ = v___x_745_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_749_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
else
{
uint8_t v___x_754_; 
v___x_754_ = lean_nat_dec_le(v___x_748_, v___x_748_);
if (v___x_754_ == 0)
{
if (v___x_750_ == 0)
{
lean_object* v___x_756_; 
lean_dec_ref(v_tail_742_);
lean_dec(v_mvarId_734_);
lean_dec(v_fvarId_733_);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 0, v___x_749_);
v___x_756_ = v___x_745_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_749_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
else
{
size_t v___x_758_; size_t v___x_759_; lean_object* v___x_760_; 
lean_del_object(v___x_745_);
v___x_758_ = ((size_t)0ULL);
v___x_759_ = lean_usize_of_nat(v___x_748_);
v___x_760_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_733_, v_mvarId_734_, v_tail_742_, v___x_758_, v___x_759_, v___x_749_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
lean_dec_ref(v_tail_742_);
return v___x_760_;
}
}
else
{
size_t v___x_761_; size_t v___x_762_; lean_object* v___x_763_; 
lean_del_object(v___x_745_);
v___x_761_ = ((size_t)0ULL);
v___x_762_ = lean_usize_of_nat(v___x_748_);
v___x_763_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_733_, v_mvarId_734_, v_tail_742_, v___x_761_, v___x_762_, v___x_749_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
lean_dec_ref(v_tail_742_);
return v___x_763_;
}
}
}
}
else
{
lean_dec_ref(v_tail_742_);
lean_dec(v_mvarId_734_);
lean_dec(v_fvarId_733_);
return v___x_743_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6___boxed(lean_object* v_fvarId_766_, lean_object* v_mvarId_767_, lean_object* v_t_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6(v_fvarId_766_, v_mvarId_767_, v_t_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
return v_res_774_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_775_; 
v___x_775_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4(lean_object* v_fvarId_776_, lean_object* v_mvarId_777_, lean_object* v_x_778_, size_t v_x_779_, size_t v_x_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
if (lean_obj_tag(v_x_778_) == 0)
{
lean_object* v_cs_786_; lean_object* v___x_787_; size_t v___x_788_; lean_object* v_j_789_; lean_object* v___x_790_; size_t v___x_791_; size_t v___x_792_; size_t v___x_793_; size_t v___x_794_; size_t v___x_795_; size_t v___x_796_; lean_object* v___x_797_; 
v_cs_786_ = lean_ctor_get(v_x_778_, 0);
lean_inc_ref(v_cs_786_);
lean_dec_ref_known(v_x_778_, 1);
v___x_787_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0);
v___x_788_ = lean_usize_shift_right(v_x_779_, v_x_780_);
v_j_789_ = lean_usize_to_nat(v___x_788_);
v___x_790_ = lean_array_get_borrowed(v___x_787_, v_cs_786_, v_j_789_);
v___x_791_ = ((size_t)1ULL);
v___x_792_ = lean_usize_shift_left(v___x_791_, v_x_780_);
v___x_793_ = lean_usize_sub(v___x_792_, v___x_791_);
v___x_794_ = lean_usize_land(v_x_779_, v___x_793_);
v___x_795_ = ((size_t)5ULL);
v___x_796_ = lean_usize_sub(v_x_780_, v___x_795_);
lean_inc(v___x_790_);
lean_inc(v_mvarId_777_);
lean_inc(v_fvarId_776_);
v___x_797_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4(v_fvarId_776_, v_mvarId_777_, v___x_790_, v___x_794_, v___x_796_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_819_; 
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_819_ == 0)
{
lean_object* v_unused_820_; 
v_unused_820_ = lean_ctor_get(v___x_797_, 0);
lean_dec(v_unused_820_);
v___x_799_ = v___x_797_;
v_isShared_800_ = v_isSharedCheck_819_;
goto v_resetjp_798_;
}
else
{
lean_dec(v___x_797_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_819_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; uint8_t v___x_805_; 
v___x_801_ = lean_unsigned_to_nat(1u);
v___x_802_ = lean_nat_add(v_j_789_, v___x_801_);
lean_dec(v_j_789_);
v___x_803_ = lean_array_get_size(v_cs_786_);
v___x_804_ = lean_box(0);
v___x_805_ = lean_nat_dec_lt(v___x_802_, v___x_803_);
if (v___x_805_ == 0)
{
lean_object* v___x_807_; 
lean_dec(v___x_802_);
lean_dec_ref(v_cs_786_);
lean_dec(v_mvarId_777_);
lean_dec(v_fvarId_776_);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 0, v___x_804_);
v___x_807_ = v___x_799_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_804_);
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
uint8_t v___x_809_; 
v___x_809_ = lean_nat_dec_le(v___x_803_, v___x_803_);
if (v___x_809_ == 0)
{
if (v___x_805_ == 0)
{
lean_object* v___x_811_; 
lean_dec(v___x_802_);
lean_dec_ref(v_cs_786_);
lean_dec(v_mvarId_777_);
lean_dec(v_fvarId_776_);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 0, v___x_804_);
v___x_811_ = v___x_799_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_804_);
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
size_t v___x_813_; size_t v___x_814_; lean_object* v___x_815_; 
lean_del_object(v___x_799_);
v___x_813_ = lean_usize_of_nat(v___x_802_);
lean_dec(v___x_802_);
v___x_814_ = lean_usize_of_nat(v___x_803_);
v___x_815_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(v_fvarId_776_, v_mvarId_777_, v_cs_786_, v___x_813_, v___x_814_, v___x_804_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
lean_dec_ref(v_cs_786_);
return v___x_815_;
}
}
else
{
size_t v___x_816_; size_t v___x_817_; lean_object* v___x_818_; 
lean_del_object(v___x_799_);
v___x_816_ = lean_usize_of_nat(v___x_802_);
lean_dec(v___x_802_);
v___x_817_ = lean_usize_of_nat(v___x_803_);
v___x_818_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(v_fvarId_776_, v_mvarId_777_, v_cs_786_, v___x_816_, v___x_817_, v___x_804_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
lean_dec_ref(v_cs_786_);
return v___x_818_;
}
}
}
}
else
{
lean_dec(v_j_789_);
lean_dec_ref(v_cs_786_);
lean_dec(v_mvarId_777_);
lean_dec(v_fvarId_776_);
return v___x_797_;
}
}
else
{
lean_object* v_vs_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_842_; 
v_vs_821_ = lean_ctor_get(v_x_778_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v_x_778_);
if (v_isSharedCheck_842_ == 0)
{
v___x_823_ = v_x_778_;
v_isShared_824_ = v_isSharedCheck_842_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_vs_821_);
lean_dec(v_x_778_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_842_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; uint8_t v___x_828_; 
v___x_825_ = lean_usize_to_nat(v_x_779_);
v___x_826_ = lean_array_get_size(v_vs_821_);
v___x_827_ = lean_box(0);
v___x_828_ = lean_nat_dec_lt(v___x_825_, v___x_826_);
if (v___x_828_ == 0)
{
lean_object* v___x_830_; 
lean_dec(v___x_825_);
lean_dec_ref(v_vs_821_);
lean_dec(v_mvarId_777_);
lean_dec(v_fvarId_776_);
if (v_isShared_824_ == 0)
{
lean_ctor_set_tag(v___x_823_, 0);
lean_ctor_set(v___x_823_, 0, v___x_827_);
v___x_830_ = v___x_823_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_827_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
else
{
uint8_t v___x_832_; 
v___x_832_ = lean_nat_dec_le(v___x_826_, v___x_826_);
if (v___x_832_ == 0)
{
if (v___x_828_ == 0)
{
lean_object* v___x_834_; 
lean_dec(v___x_825_);
lean_dec_ref(v_vs_821_);
lean_dec(v_mvarId_777_);
lean_dec(v_fvarId_776_);
if (v_isShared_824_ == 0)
{
lean_ctor_set_tag(v___x_823_, 0);
lean_ctor_set(v___x_823_, 0, v___x_827_);
v___x_834_ = v___x_823_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_827_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
else
{
size_t v___x_836_; size_t v___x_837_; lean_object* v___x_838_; 
lean_del_object(v___x_823_);
v___x_836_ = lean_usize_of_nat(v___x_825_);
lean_dec(v___x_825_);
v___x_837_ = lean_usize_of_nat(v___x_826_);
v___x_838_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_776_, v_mvarId_777_, v_vs_821_, v___x_836_, v___x_837_, v___x_827_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
lean_dec_ref(v_vs_821_);
return v___x_838_;
}
}
else
{
size_t v___x_839_; size_t v___x_840_; lean_object* v___x_841_; 
lean_del_object(v___x_823_);
v___x_839_ = lean_usize_of_nat(v___x_825_);
lean_dec(v___x_825_);
v___x_840_ = lean_usize_of_nat(v___x_826_);
v___x_841_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_776_, v_mvarId_777_, v_vs_821_, v___x_839_, v___x_840_, v___x_827_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
lean_dec_ref(v_vs_821_);
return v___x_841_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___boxed(lean_object* v_fvarId_843_, lean_object* v_mvarId_844_, lean_object* v_x_845_, lean_object* v_x_846_, lean_object* v_x_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
size_t v_x_9520__boxed_853_; size_t v_x_9521__boxed_854_; lean_object* v_res_855_; 
v_x_9520__boxed_853_ = lean_unbox_usize(v_x_846_);
lean_dec(v_x_846_);
v_x_9521__boxed_854_ = lean_unbox_usize(v_x_847_);
lean_dec(v_x_847_);
v_res_855_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4(v_fvarId_843_, v_mvarId_844_, v_x_845_, v_x_9520__boxed_853_, v_x_9521__boxed_854_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1(lean_object* v_fvarId_856_, lean_object* v_mvarId_857_, lean_object* v_t_858_, lean_object* v_start_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_){
_start:
{
lean_object* v___x_865_; uint8_t v___x_866_; 
v___x_865_ = lean_unsigned_to_nat(0u);
v___x_866_ = lean_nat_dec_eq(v_start_859_, v___x_865_);
if (v___x_866_ == 0)
{
lean_object* v_root_867_; lean_object* v_tail_868_; size_t v_shift_869_; lean_object* v_tailOff_870_; uint8_t v___x_871_; 
v_root_867_ = lean_ctor_get(v_t_858_, 0);
lean_inc_ref(v_root_867_);
v_tail_868_ = lean_ctor_get(v_t_858_, 1);
lean_inc_ref(v_tail_868_);
v_shift_869_ = lean_ctor_get_usize(v_t_858_, 4);
v_tailOff_870_ = lean_ctor_get(v_t_858_, 3);
lean_inc(v_tailOff_870_);
lean_dec_ref(v_t_858_);
v___x_871_ = lean_nat_dec_le(v_tailOff_870_, v_start_859_);
if (v___x_871_ == 0)
{
size_t v___x_872_; lean_object* v___x_873_; 
lean_dec(v_tailOff_870_);
v___x_872_ = lean_usize_of_nat(v_start_859_);
lean_inc(v_mvarId_857_);
lean_inc(v_fvarId_856_);
v___x_873_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4(v_fvarId_856_, v_mvarId_857_, v_root_867_, v___x_872_, v_shift_869_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
if (lean_obj_tag(v___x_873_) == 0)
{
lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_893_; 
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_893_ == 0)
{
lean_object* v_unused_894_; 
v_unused_894_ = lean_ctor_get(v___x_873_, 0);
lean_dec(v_unused_894_);
v___x_875_ = v___x_873_;
v_isShared_876_ = v_isSharedCheck_893_;
goto v_resetjp_874_;
}
else
{
lean_dec(v___x_873_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_893_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_877_; lean_object* v___x_878_; uint8_t v___x_879_; 
v___x_877_ = lean_array_get_size(v_tail_868_);
v___x_878_ = lean_box(0);
v___x_879_ = lean_nat_dec_lt(v___x_865_, v___x_877_);
if (v___x_879_ == 0)
{
lean_object* v___x_881_; 
lean_dec_ref(v_tail_868_);
lean_dec(v_mvarId_857_);
lean_dec(v_fvarId_856_);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 0, v___x_878_);
v___x_881_ = v___x_875_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_878_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
else
{
uint8_t v___x_883_; 
v___x_883_ = lean_nat_dec_le(v___x_877_, v___x_877_);
if (v___x_883_ == 0)
{
if (v___x_879_ == 0)
{
lean_object* v___x_885_; 
lean_dec_ref(v_tail_868_);
lean_dec(v_mvarId_857_);
lean_dec(v_fvarId_856_);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 0, v___x_878_);
v___x_885_ = v___x_875_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_878_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
else
{
size_t v___x_887_; size_t v___x_888_; lean_object* v___x_889_; 
lean_del_object(v___x_875_);
v___x_887_ = ((size_t)0ULL);
v___x_888_ = lean_usize_of_nat(v___x_877_);
v___x_889_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_856_, v_mvarId_857_, v_tail_868_, v___x_887_, v___x_888_, v___x_878_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
lean_dec_ref(v_tail_868_);
return v___x_889_;
}
}
else
{
size_t v___x_890_; size_t v___x_891_; lean_object* v___x_892_; 
lean_del_object(v___x_875_);
v___x_890_ = ((size_t)0ULL);
v___x_891_ = lean_usize_of_nat(v___x_877_);
v___x_892_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_856_, v_mvarId_857_, v_tail_868_, v___x_890_, v___x_891_, v___x_878_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
lean_dec_ref(v_tail_868_);
return v___x_892_;
}
}
}
}
else
{
lean_dec_ref(v_tail_868_);
lean_dec(v_mvarId_857_);
lean_dec(v_fvarId_856_);
return v___x_873_;
}
}
else
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; uint8_t v___x_898_; 
lean_dec_ref(v_root_867_);
v___x_895_ = lean_nat_sub(v_start_859_, v_tailOff_870_);
lean_dec(v_tailOff_870_);
v___x_896_ = lean_array_get_size(v_tail_868_);
v___x_897_ = lean_box(0);
v___x_898_ = lean_nat_dec_lt(v___x_895_, v___x_896_);
if (v___x_898_ == 0)
{
lean_object* v___x_899_; 
lean_dec(v___x_895_);
lean_dec_ref(v_tail_868_);
lean_dec(v_mvarId_857_);
lean_dec(v_fvarId_856_);
v___x_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_899_, 0, v___x_897_);
return v___x_899_;
}
else
{
uint8_t v___x_900_; 
v___x_900_ = lean_nat_dec_le(v___x_896_, v___x_896_);
if (v___x_900_ == 0)
{
if (v___x_898_ == 0)
{
lean_object* v___x_901_; 
lean_dec(v___x_895_);
lean_dec_ref(v_tail_868_);
lean_dec(v_mvarId_857_);
lean_dec(v_fvarId_856_);
v___x_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_901_, 0, v___x_897_);
return v___x_901_;
}
else
{
size_t v___x_902_; size_t v___x_903_; lean_object* v___x_904_; 
v___x_902_ = lean_usize_of_nat(v___x_895_);
lean_dec(v___x_895_);
v___x_903_ = lean_usize_of_nat(v___x_896_);
v___x_904_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_856_, v_mvarId_857_, v_tail_868_, v___x_902_, v___x_903_, v___x_897_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
lean_dec_ref(v_tail_868_);
return v___x_904_;
}
}
else
{
size_t v___x_905_; size_t v___x_906_; lean_object* v___x_907_; 
v___x_905_ = lean_usize_of_nat(v___x_895_);
lean_dec(v___x_895_);
v___x_906_ = lean_usize_of_nat(v___x_896_);
v___x_907_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_856_, v_mvarId_857_, v_tail_868_, v___x_905_, v___x_906_, v___x_897_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
lean_dec_ref(v_tail_868_);
return v___x_907_;
}
}
}
}
else
{
lean_object* v___x_908_; 
v___x_908_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6(v_fvarId_856_, v_mvarId_857_, v_t_858_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
return v___x_908_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1___boxed(lean_object* v_fvarId_909_, lean_object* v_mvarId_910_, lean_object* v_t_911_, lean_object* v_start_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1(v_fvarId_909_, v_mvarId_910_, v_t_911_, v_start_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec(v_start_912_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1(lean_object* v_fvarId_919_, lean_object* v_mvarId_920_, lean_object* v_lctx_921_, lean_object* v_start_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v_decls_928_; lean_object* v___x_929_; 
v_decls_928_ = lean_ctor_get(v_lctx_921_, 1);
lean_inc_ref(v_decls_928_);
lean_dec_ref(v_lctx_921_);
v___x_929_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1(v_fvarId_919_, v_mvarId_920_, v_decls_928_, v_start_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1___boxed(lean_object* v_fvarId_930_, lean_object* v_mvarId_931_, lean_object* v_lctx_932_, lean_object* v_start_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1(v_fvarId_930_, v_mvarId_931_, v_lctx_932_, v_start_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v_start_933_);
return v_res_939_;
}
}
static lean_object* _init_l_Lean_MVarId_clear___lam__1___closed__1(void){
_start:
{
lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_941_ = ((lean_object*)(l_Lean_MVarId_clear___lam__1___closed__0));
v___x_942_ = l_Lean_stringToMessageData(v___x_941_);
return v___x_942_;
}
}
static lean_object* _init_l_Lean_MVarId_clear___lam__1___closed__3(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_944_ = ((lean_object*)(l_Lean_MVarId_clear___lam__1___closed__2));
v___x_945_ = l_Lean_stringToMessageData(v___x_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clear___lam__1(lean_object* v_mvarId_946_, lean_object* v___x_947_, lean_object* v_fvarId_948_, lean_object* v___f_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v___y_956_; lean_object* v___y_957_; lean_object* v___y_958_; lean_object* v___y_959_; lean_object* v___y_960_; lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___x_986_; 
lean_inc(v___x_947_);
lean_inc(v_mvarId_946_);
v___x_986_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_946_, v___x_947_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v_lctx_987_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v___y_992_; lean_object* v___y_993_; lean_object* v___y_994_; lean_object* v___y_995_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___y_1005_; uint8_t v___x_1062_; 
lean_dec_ref_known(v___x_986_, 1);
v_lctx_987_ = lean_ctor_get(v___y_950_, 2);
lean_inc_ref(v_lctx_987_);
v___x_1062_ = l_Lean_LocalContext_contains(v_lctx_987_, v_fvarId_948_);
if (v___x_1062_ == 0)
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1063_ = lean_obj_once(&l_Lean_MVarId_clear___lam__1___closed__3, &l_Lean_MVarId_clear___lam__1___closed__3_once, _init_l_Lean_MVarId_clear___lam__1___closed__3);
lean_inc(v_fvarId_948_);
v___x_1064_ = l_Lean_mkFVar(v_fvarId_948_);
v___x_1065_ = l_Lean_MessageData_ofExpr(v___x_1064_);
v___x_1066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1063_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
v___x_1067_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7);
v___x_1068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1066_);
lean_ctor_set(v___x_1068_, 1, v___x_1067_);
v___x_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
lean_inc(v_mvarId_946_);
lean_inc(v___x_947_);
v___x_1070_ = l_Lean_Meta_throwTacticEx___redArg(v___x_947_, v_mvarId_946_, v___x_1069_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_dec_ref_known(v___x_1070_, 1);
v___y_1002_ = v___y_950_;
v___y_1003_ = v___y_951_;
v___y_1004_ = v___y_952_;
v___y_1005_ = v___y_953_;
goto v___jp_1001_;
}
else
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1078_; 
lean_dec_ref(v_lctx_987_);
lean_dec_ref(v___y_950_);
lean_dec_ref(v___f_949_);
lean_dec(v_fvarId_948_);
lean_dec(v___x_947_);
lean_dec(v_mvarId_946_);
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1073_ = v___x_1070_;
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1070_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1076_; 
if (v_isShared_1074_ == 0)
{
v___x_1076_ = v___x_1073_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_a_1071_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
}
else
{
v___y_1002_ = v___y_950_;
v___y_1003_ = v___y_951_;
v___y_1004_ = v___y_952_;
v___y_1005_ = v___y_953_;
goto v___jp_1001_;
}
v___jp_988_:
{
lean_object* v_localInstances_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v_localInstances_996_ = lean_ctor_get(v___y_992_, 3);
v___x_997_ = lean_local_ctx_erase(v_lctx_987_, v_fvarId_948_);
lean_inc(v___y_989_);
v___x_998_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_949_, v_localInstances_996_, v___y_989_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_inc_ref(v_localInstances_996_);
v___y_956_ = v___y_994_;
v___y_957_ = v___x_997_;
v___y_958_ = v___y_993_;
v___y_959_ = v___y_992_;
v___y_960_ = v___y_989_;
v___y_961_ = v___y_995_;
v___y_962_ = v___y_990_;
v___y_963_ = v___y_991_;
v___y_964_ = v_localInstances_996_;
goto v___jp_955_;
}
else
{
lean_object* v_val_999_; lean_object* v___x_1000_; 
v_val_999_ = lean_ctor_get(v___x_998_, 0);
lean_inc(v_val_999_);
lean_dec_ref_known(v___x_998_, 1);
lean_inc_ref(v_localInstances_996_);
v___x_1000_ = l_Array_eraseIdx___redArg(v_localInstances_996_, v_val_999_);
v___y_956_ = v___y_994_;
v___y_957_ = v___x_997_;
v___y_958_ = v___y_993_;
v___y_959_ = v___y_992_;
v___y_960_ = v___y_989_;
v___y_961_ = v___y_995_;
v___y_962_ = v___y_990_;
v___y_963_ = v___y_991_;
v___y_964_ = v___x_1000_;
goto v___jp_955_;
}
}
v___jp_1001_:
{
lean_object* v___x_1006_; 
lean_inc(v_mvarId_946_);
v___x_1006_ = l_Lean_MVarId_getTag(v_mvarId_946_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v_a_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
lean_inc(v_a_1007_);
lean_dec_ref_known(v___x_1006_, 1);
v___x_1008_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_lctx_987_);
lean_inc(v_mvarId_946_);
lean_inc(v_fvarId_948_);
v___x_1009_ = l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1(v_fvarId_948_, v_mvarId_946_, v_lctx_987_, v___x_1008_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v___x_1010_; 
lean_dec_ref_known(v___x_1009_, 1);
lean_inc(v_mvarId_946_);
v___x_1010_ = l_Lean_MVarId_getDecl(v_mvarId_946_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v_a_1011_; lean_object* v_type_1012_; lean_object* v___x_1013_; lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1037_; 
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
lean_inc(v_a_1011_);
lean_dec_ref_known(v___x_1010_, 1);
v_type_1012_ = lean_ctor_get(v_a_1011_, 2);
lean_inc_ref_n(v_type_1012_, 2);
lean_dec(v_a_1011_);
lean_inc(v_fvarId_948_);
v___x_1013_ = l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3___redArg(v_type_1012_, v_fvarId_948_, v___y_1003_);
v_a_1014_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1016_ = v___x_1013_;
v_isShared_1017_ = v_isSharedCheck_1037_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_1013_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1037_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
uint8_t v___x_1018_; 
v___x_1018_ = lean_unbox(v_a_1014_);
lean_dec(v_a_1014_);
if (v___x_1018_ == 0)
{
lean_del_object(v___x_1016_);
lean_dec(v___x_947_);
v___y_989_ = v___x_1008_;
v___y_990_ = v_type_1012_;
v___y_991_ = v_a_1007_;
v___y_992_ = v___y_1002_;
v___y_993_ = v___y_1003_;
v___y_994_ = v___y_1004_;
v___y_995_ = v___y_1005_;
goto v___jp_988_;
}
else
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1026_; 
v___x_1019_ = lean_obj_once(&l_Lean_MVarId_clear___lam__1___closed__1, &l_Lean_MVarId_clear___lam__1___closed__1_once, _init_l_Lean_MVarId_clear___lam__1___closed__1);
lean_inc(v_fvarId_948_);
v___x_1020_ = l_Lean_mkFVar(v_fvarId_948_);
v___x_1021_ = l_Lean_MessageData_ofExpr(v___x_1020_);
v___x_1022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1019_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
v___x_1023_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7);
v___x_1024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1022_);
lean_ctor_set(v___x_1024_, 1, v___x_1023_);
if (v_isShared_1017_ == 0)
{
lean_ctor_set_tag(v___x_1016_, 1);
lean_ctor_set(v___x_1016_, 0, v___x_1024_);
v___x_1026_ = v___x_1016_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1024_);
v___x_1026_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
lean_object* v___x_1027_; 
lean_inc(v_mvarId_946_);
v___x_1027_ = l_Lean_Meta_throwTacticEx___redArg(v___x_947_, v_mvarId_946_, v___x_1026_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_dec_ref_known(v___x_1027_, 1);
v___y_989_ = v___x_1008_;
v___y_990_ = v_type_1012_;
v___y_991_ = v_a_1007_;
v___y_992_ = v___y_1002_;
v___y_993_ = v___y_1003_;
v___y_994_ = v___y_1004_;
v___y_995_ = v___y_1005_;
goto v___jp_988_;
}
else
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1035_; 
lean_dec_ref(v_type_1012_);
lean_dec(v_a_1007_);
lean_dec_ref(v___y_1002_);
lean_dec_ref(v_lctx_987_);
lean_dec_ref(v___f_949_);
lean_dec(v_fvarId_948_);
lean_dec(v_mvarId_946_);
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1030_ = v___x_1027_;
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_1027_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1033_; 
if (v_isShared_1031_ == 0)
{
v___x_1033_ = v___x_1030_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_a_1028_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1045_; 
lean_dec(v_a_1007_);
lean_dec_ref(v___y_1002_);
lean_dec_ref(v_lctx_987_);
lean_dec_ref(v___f_949_);
lean_dec(v_fvarId_948_);
lean_dec(v___x_947_);
lean_dec(v_mvarId_946_);
v_a_1038_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1040_ = v___x_1010_;
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1010_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1043_; 
if (v_isShared_1041_ == 0)
{
v___x_1043_ = v___x_1040_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_a_1038_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
else
{
lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1053_; 
lean_dec(v_a_1007_);
lean_dec_ref(v___y_1002_);
lean_dec_ref(v_lctx_987_);
lean_dec_ref(v___f_949_);
lean_dec(v_fvarId_948_);
lean_dec(v___x_947_);
lean_dec(v_mvarId_946_);
v_a_1046_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1048_ = v___x_1009_;
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v___x_1009_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1051_; 
if (v_isShared_1049_ == 0)
{
v___x_1051_ = v___x_1048_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_a_1046_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
}
else
{
lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1061_; 
lean_dec_ref(v___y_1002_);
lean_dec_ref(v_lctx_987_);
lean_dec_ref(v___f_949_);
lean_dec(v_fvarId_948_);
lean_dec(v___x_947_);
lean_dec(v_mvarId_946_);
v_a_1054_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1056_ = v___x_1006_;
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v___x_1006_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1059_; 
if (v_isShared_1057_ == 0)
{
v___x_1059_ = v___x_1056_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_a_1054_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
}
else
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1086_; 
lean_dec_ref(v___y_950_);
lean_dec_ref(v___f_949_);
lean_dec(v_fvarId_948_);
lean_dec(v___x_947_);
lean_dec(v_mvarId_946_);
v_a_1079_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1081_ = v___x_986_;
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_986_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
if (v_isShared_1082_ == 0)
{
v___x_1084_ = v___x_1081_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1079_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
v___jp_955_:
{
uint8_t v___x_965_; lean_object* v___x_966_; 
v___x_965_ = 2;
v___x_966_ = l_Lean_Meta_mkFreshExprMVarAt(v___y_957_, v___y_964_, v___y_962_, v___x_965_, v___y_963_, v___y_960_, v___y_959_, v___y_958_, v___y_956_, v___y_961_);
lean_dec_ref(v___y_959_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v_a_967_; lean_object* v___x_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_976_; 
v_a_967_ = lean_ctor_get(v___x_966_, 0);
lean_inc_n(v_a_967_, 2);
lean_dec_ref_known(v___x_966_, 1);
v___x_968_ = l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg(v_mvarId_946_, v_a_967_, v___y_958_);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_976_ == 0)
{
lean_object* v_unused_977_; 
v_unused_977_ = lean_ctor_get(v___x_968_, 0);
lean_dec(v_unused_977_);
v___x_970_ = v___x_968_;
v_isShared_971_ = v_isSharedCheck_976_;
goto v_resetjp_969_;
}
else
{
lean_dec(v___x_968_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_976_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_972_; lean_object* v___x_974_; 
v___x_972_ = l_Lean_Expr_mvarId_x21(v_a_967_);
lean_dec(v_a_967_);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 0, v___x_972_);
v___x_974_ = v___x_970_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v___x_972_);
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
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_985_; 
lean_dec(v_mvarId_946_);
v_a_978_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_985_ == 0)
{
v___x_980_ = v___x_966_;
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_966_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_983_; 
if (v_isShared_981_ == 0)
{
v___x_983_ = v___x_980_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_a_978_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clear___lam__1___boxed(lean_object* v_mvarId_1087_, lean_object* v___x_1088_, lean_object* v_fvarId_1089_, lean_object* v___f_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_Lean_MVarId_clear___lam__1(v_mvarId_1087_, v___x_1088_, v_fvarId_1089_, v___f_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec(v___y_1092_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clear(lean_object* v_mvarId_1097_, lean_object* v_fvarId_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_){
_start:
{
lean_object* v___f_1104_; lean_object* v___x_1105_; lean_object* v___f_1106_; lean_object* v___x_1107_; 
lean_inc(v_fvarId_1098_);
v___f_1104_ = lean_alloc_closure((void*)(l_Lean_MVarId_clear___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1104_, 0, v_fvarId_1098_);
v___x_1105_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__1));
lean_inc(v_mvarId_1097_);
v___f_1106_ = lean_alloc_closure((void*)(l_Lean_MVarId_clear___lam__1___boxed), 9, 4);
lean_closure_set(v___f_1106_, 0, v_mvarId_1097_);
lean_closure_set(v___f_1106_, 1, v___x_1105_);
lean_closure_set(v___f_1106_, 2, v_fvarId_1098_);
lean_closure_set(v___f_1106_, 3, v___f_1104_);
v___x_1107_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg(v_mvarId_1097_, v___f_1106_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clear___boxed(lean_object* v_mvarId_1108_, lean_object* v_fvarId_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l_Lean_MVarId_clear(v_mvarId_1108_, v_fvarId_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_);
lean_dec(v_a_1113_);
lean_dec_ref(v_a_1112_);
lean_dec(v_a_1111_);
lean_dec_ref(v_a_1110_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2(lean_object* v_mvarId_1116_, lean_object* v_val_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_){
_start:
{
lean_object* v___x_1123_; 
v___x_1123_ = l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg(v_mvarId_1116_, v_val_1117_, v___y_1119_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___boxed(lean_object* v_mvarId_1124_, lean_object* v_val_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2(v_mvarId_1124_, v_val_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3(lean_object* v_00_u03b2_1132_, lean_object* v_x_1133_, lean_object* v_x_1134_, lean_object* v_x_1135_){
_start:
{
lean_object* v___x_1136_; 
v___x_1136_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3___redArg(v_x_1133_, v_x_1134_, v_x_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9(lean_object* v_00_u03b2_1137_, lean_object* v_x_1138_, size_t v_x_1139_, size_t v_x_1140_, lean_object* v_x_1141_, lean_object* v_x_1142_){
_start:
{
lean_object* v___x_1143_; 
v___x_1143_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_x_1138_, v_x_1139_, v_x_1140_, v_x_1141_, v_x_1142_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___boxed(lean_object* v_00_u03b2_1144_, lean_object* v_x_1145_, lean_object* v_x_1146_, lean_object* v_x_1147_, lean_object* v_x_1148_, lean_object* v_x_1149_){
_start:
{
size_t v_x_10122__boxed_1150_; size_t v_x_10123__boxed_1151_; lean_object* v_res_1152_; 
v_x_10122__boxed_1150_ = lean_unbox_usize(v_x_1146_);
lean_dec(v_x_1146_);
v_x_10123__boxed_1151_ = lean_unbox_usize(v_x_1147_);
lean_dec(v_x_1147_);
v_res_1152_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9(v_00_u03b2_1144_, v_x_1145_, v_x_10122__boxed_1150_, v_x_10123__boxed_1151_, v_x_1148_, v_x_1149_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13(lean_object* v_00_u03b2_1153_, lean_object* v_n_1154_, lean_object* v_k_1155_, lean_object* v_v_1156_){
_start:
{
lean_object* v___x_1157_; 
v___x_1157_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13___redArg(v_n_1154_, v_k_1155_, v_v_1156_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14(lean_object* v_00_u03b2_1158_, size_t v_depth_1159_, lean_object* v_keys_1160_, lean_object* v_vals_1161_, lean_object* v_heq_1162_, lean_object* v_i_1163_, lean_object* v_entries_1164_){
_start:
{
lean_object* v___x_1165_; 
v___x_1165_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg(v_depth_1159_, v_keys_1160_, v_vals_1161_, v_i_1163_, v_entries_1164_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___boxed(lean_object* v_00_u03b2_1166_, lean_object* v_depth_1167_, lean_object* v_keys_1168_, lean_object* v_vals_1169_, lean_object* v_heq_1170_, lean_object* v_i_1171_, lean_object* v_entries_1172_){
_start:
{
size_t v_depth_boxed_1173_; lean_object* v_res_1174_; 
v_depth_boxed_1173_ = lean_unbox_usize(v_depth_1167_);
lean_dec(v_depth_1167_);
v_res_1174_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14(v_00_u03b2_1166_, v_depth_boxed_1173_, v_keys_1168_, v_vals_1169_, v_heq_1170_, v_i_1171_, v_entries_1172_);
lean_dec_ref(v_vals_1169_);
lean_dec_ref(v_keys_1168_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13_spec__14(lean_object* v_00_u03b2_1175_, lean_object* v_x_1176_, lean_object* v_x_1177_, lean_object* v_x_1178_, lean_object* v_x_1179_){
_start:
{
lean_object* v___x_1180_; 
v___x_1180_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13_spec__14___redArg(v_x_1176_, v_x_1177_, v_x_1178_, v_x_1179_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClear(lean_object* v_mvarId_1181_, lean_object* v_fvarId_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_){
_start:
{
lean_object* v___x_1188_; 
v___x_1188_ = l_Lean_Meta_saveState___redArg(v_a_1184_, v_a_1186_);
if (lean_obj_tag(v___x_1188_) == 0)
{
lean_object* v_a_1189_; lean_object* v___x_1190_; 
v_a_1189_ = lean_ctor_get(v___x_1188_, 0);
lean_inc(v_a_1189_);
lean_dec_ref_known(v___x_1188_, 1);
lean_inc(v_mvarId_1181_);
v___x_1190_ = l_Lean_MVarId_clear(v_mvarId_1181_, v_fvarId_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_);
if (lean_obj_tag(v___x_1190_) == 0)
{
lean_dec(v_a_1189_);
lean_dec(v_mvarId_1181_);
return v___x_1190_;
}
else
{
lean_object* v_a_1191_; uint8_t v___y_1193_; uint8_t v___x_1211_; 
v_a_1191_ = lean_ctor_get(v___x_1190_, 0);
lean_inc(v_a_1191_);
v___x_1211_ = l_Lean_Exception_isInterrupt(v_a_1191_);
if (v___x_1211_ == 0)
{
uint8_t v___x_1212_; 
v___x_1212_ = l_Lean_Exception_isRuntime(v_a_1191_);
v___y_1193_ = v___x_1212_;
goto v___jp_1192_;
}
else
{
lean_dec(v_a_1191_);
v___y_1193_ = v___x_1211_;
goto v___jp_1192_;
}
v___jp_1192_:
{
if (v___y_1193_ == 0)
{
lean_object* v___x_1194_; 
lean_dec_ref_known(v___x_1190_, 1);
v___x_1194_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1189_, v_a_1184_, v_a_1186_);
lean_dec(v_a_1189_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1201_; 
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1201_ == 0)
{
lean_object* v_unused_1202_; 
v_unused_1202_ = lean_ctor_get(v___x_1194_, 0);
lean_dec(v_unused_1202_);
v___x_1196_ = v___x_1194_;
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
else
{
lean_dec(v___x_1194_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1199_; 
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 0, v_mvarId_1181_);
v___x_1199_ = v___x_1196_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_mvarId_1181_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
else
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1210_; 
lean_dec(v_mvarId_1181_);
v_a_1203_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1205_ = v___x_1194_;
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1194_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1208_; 
if (v_isShared_1206_ == 0)
{
v___x_1208_ = v___x_1205_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_a_1203_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
else
{
lean_dec(v_a_1189_);
lean_dec(v_mvarId_1181_);
return v___x_1190_;
}
}
}
}
else
{
lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1220_; 
lean_dec(v_fvarId_1182_);
lean_dec(v_mvarId_1181_);
v_a_1213_ = lean_ctor_get(v___x_1188_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1215_ = v___x_1188_;
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v___x_1188_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1218_; 
if (v_isShared_1216_ == 0)
{
v___x_1218_ = v___x_1215_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_a_1213_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClear___boxed(lean_object* v_mvarId_1221_, lean_object* v_fvarId_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Lean_MVarId_tryClear(v_mvarId_1221_, v_fvarId_1222_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_);
lean_dec(v_a_1226_);
lean_dec_ref(v_a_1225_);
lean_dec(v_a_1224_);
lean_dec_ref(v_a_1223_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0(lean_object* v_as_1229_, size_t v_i_1230_, size_t v_stop_1231_, lean_object* v_b_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
uint8_t v___x_1238_; 
v___x_1238_ = lean_usize_dec_eq(v_i_1230_, v_stop_1231_);
if (v___x_1238_ == 0)
{
size_t v___x_1239_; size_t v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1239_ = ((size_t)1ULL);
v___x_1240_ = lean_usize_sub(v_i_1230_, v___x_1239_);
v___x_1241_ = lean_array_uget_borrowed(v_as_1229_, v___x_1240_);
lean_inc(v___x_1241_);
v___x_1242_ = l_Lean_MVarId_tryClear(v_b_1232_, v___x_1241_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v_a_1243_; 
v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
lean_inc(v_a_1243_);
lean_dec_ref_known(v___x_1242_, 1);
v_i_1230_ = v___x_1240_;
v_b_1232_ = v_a_1243_;
goto _start;
}
else
{
return v___x_1242_;
}
}
else
{
lean_object* v___x_1245_; 
v___x_1245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1245_, 0, v_b_1232_);
return v___x_1245_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0___boxed(lean_object* v_as_1246_, lean_object* v_i_1247_, lean_object* v_stop_1248_, lean_object* v_b_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
size_t v_i_boxed_1255_; size_t v_stop_boxed_1256_; lean_object* v_res_1257_; 
v_i_boxed_1255_ = lean_unbox_usize(v_i_1247_);
lean_dec(v_i_1247_);
v_stop_boxed_1256_ = lean_unbox_usize(v_stop_1248_);
lean_dec(v_stop_1248_);
v_res_1257_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0(v_as_1246_, v_i_boxed_1255_, v_stop_boxed_1256_, v_b_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec_ref(v_as_1246_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany(lean_object* v_mvarId_1258_, lean_object* v_fvarIds_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_){
_start:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; uint8_t v___x_1267_; 
v___x_1265_ = lean_array_get_size(v_fvarIds_1259_);
v___x_1266_ = lean_unsigned_to_nat(0u);
v___x_1267_ = lean_nat_dec_lt(v___x_1266_, v___x_1265_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1268_; 
v___x_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1268_, 0, v_mvarId_1258_);
return v___x_1268_;
}
else
{
size_t v___x_1269_; size_t v___x_1270_; lean_object* v___x_1271_; 
v___x_1269_ = lean_usize_of_nat(v___x_1265_);
v___x_1270_ = ((size_t)0ULL);
v___x_1271_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0(v_fvarIds_1259_, v___x_1269_, v___x_1270_, v_mvarId_1258_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_);
return v___x_1271_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany___boxed(lean_object* v_mvarId_1272_, lean_object* v_fvarIds_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l_Lean_MVarId_tryClearMany(v_mvarId_1272_, v_fvarIds_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_);
lean_dec(v_a_1277_);
lean_dec_ref(v_a_1276_);
lean_dec(v_a_1275_);
lean_dec_ref(v_a_1274_);
lean_dec_ref(v_fvarIds_1273_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0(lean_object* v_as_1280_, size_t v_i_1281_, size_t v_stop_1282_, lean_object* v_b_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
uint8_t v___x_1289_; 
v___x_1289_ = lean_usize_dec_eq(v_i_1281_, v_stop_1282_);
if (v___x_1289_ == 0)
{
lean_object* v_fst_1290_; lean_object* v_snd_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1316_; 
v_fst_1290_ = lean_ctor_get(v_b_1283_, 0);
v_snd_1291_ = lean_ctor_get(v_b_1283_, 1);
v_isSharedCheck_1316_ = !lean_is_exclusive(v_b_1283_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1293_ = v_b_1283_;
v_isShared_1294_ = v_isSharedCheck_1316_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_snd_1291_);
lean_inc(v_fst_1290_);
lean_dec(v_b_1283_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1316_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
size_t v___x_1295_; size_t v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1295_ = ((size_t)1ULL);
v___x_1296_ = lean_usize_sub(v_i_1281_, v___x_1295_);
v___x_1297_ = lean_array_uget_borrowed(v_as_1280_, v___x_1296_);
lean_inc(v___x_1297_);
lean_inc(v_fst_1290_);
v___x_1298_ = l_Lean_MVarId_tryClear(v_fst_1290_, v___x_1297_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_object* v_a_1299_; lean_object* v___y_1301_; uint8_t v___x_1306_; 
v_a_1299_ = lean_ctor_get(v___x_1298_, 0);
lean_inc(v_a_1299_);
lean_dec_ref_known(v___x_1298_, 1);
v___x_1306_ = l_Lean_instBEqMVarId_beq(v_fst_1290_, v_a_1299_);
lean_dec(v_fst_1290_);
if (v___x_1306_ == 0)
{
lean_object* v___x_1307_; 
lean_inc(v___x_1297_);
v___x_1307_ = lean_array_push(v_snd_1291_, v___x_1297_);
v___y_1301_ = v___x_1307_;
goto v___jp_1300_;
}
else
{
v___y_1301_ = v_snd_1291_;
goto v___jp_1300_;
}
v___jp_1300_:
{
lean_object* v___x_1303_; 
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 1, v___y_1301_);
lean_ctor_set(v___x_1293_, 0, v_a_1299_);
v___x_1303_ = v___x_1293_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_a_1299_);
lean_ctor_set(v_reuseFailAlloc_1305_, 1, v___y_1301_);
v___x_1303_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
v_i_1281_ = v___x_1296_;
v_b_1283_ = v___x_1303_;
goto _start;
}
}
}
else
{
lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1315_; 
lean_del_object(v___x_1293_);
lean_dec(v_snd_1291_);
lean_dec(v_fst_1290_);
v_a_1308_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1310_ = v___x_1298_;
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_dec(v___x_1298_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1313_; 
if (v_isShared_1311_ == 0)
{
v___x_1313_ = v___x_1310_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v_a_1308_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
}
}
}
}
}
else
{
lean_object* v___x_1317_; 
v___x_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1317_, 0, v_b_1283_);
return v___x_1317_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0___boxed(lean_object* v_as_1318_, lean_object* v_i_1319_, lean_object* v_stop_1320_, lean_object* v_b_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
size_t v_i_boxed_1327_; size_t v_stop_boxed_1328_; lean_object* v_res_1329_; 
v_i_boxed_1327_ = lean_unbox_usize(v_i_1319_);
lean_dec(v_i_1319_);
v_stop_boxed_1328_ = lean_unbox_usize(v_stop_1320_);
lean_dec(v_stop_1320_);
v_res_1329_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0(v_as_1318_, v_i_boxed_1327_, v_stop_boxed_1328_, v_b_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec_ref(v_as_1318_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany_x27___lam__0(lean_object* v_fvarIds_1330_, lean_object* v_goal_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_){
_start:
{
lean_object* v_lctx_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; uint8_t v___x_1343_; 
v_lctx_1337_ = lean_ctor_get(v___y_1332_, 2);
v___x_1338_ = l_Lean_LocalContext_sortFVarsByContextOrder(v_lctx_1337_, v_fvarIds_1330_);
v___x_1339_ = lean_array_get_size(v___x_1338_);
v___x_1340_ = lean_mk_empty_array_with_capacity(v___x_1339_);
v___x_1341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1341_, 0, v_goal_1331_);
lean_ctor_set(v___x_1341_, 1, v___x_1340_);
v___x_1342_ = lean_unsigned_to_nat(0u);
v___x_1343_ = lean_nat_dec_lt(v___x_1342_, v___x_1339_);
if (v___x_1343_ == 0)
{
lean_object* v___x_1344_; 
lean_dec_ref(v___x_1338_);
v___x_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1341_);
return v___x_1344_;
}
else
{
size_t v___x_1345_; size_t v___x_1346_; lean_object* v___x_1347_; 
v___x_1345_ = lean_usize_of_nat(v___x_1339_);
v___x_1346_ = ((size_t)0ULL);
v___x_1347_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0(v___x_1338_, v___x_1345_, v___x_1346_, v___x_1341_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
lean_dec_ref(v___x_1338_);
return v___x_1347_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany_x27___lam__0___boxed(lean_object* v_fvarIds_1348_, lean_object* v_goal_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l_Lean_MVarId_tryClearMany_x27___lam__0(v_fvarIds_1348_, v_goal_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany_x27(lean_object* v_goal_1356_, lean_object* v_fvarIds_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_){
_start:
{
lean_object* v___f_1363_; lean_object* v___x_1364_; 
lean_inc(v_goal_1356_);
v___f_1363_ = lean_alloc_closure((void*)(l_Lean_MVarId_tryClearMany_x27___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1363_, 0, v_fvarIds_1357_);
lean_closure_set(v___f_1363_, 1, v_goal_1356_);
v___x_1364_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg(v_goal_1356_, v___f_1363_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany_x27___boxed(lean_object* v_goal_1365_, lean_object* v_fvarIds_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_Lean_MVarId_tryClearMany_x27(v_goal_1365_, v_fvarIds_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_);
lean_dec(v_a_1370_);
lean_dec_ref(v_a_1369_);
lean_dec(v_a_1368_);
lean_dec_ref(v_a_1367_);
return v_res_1372_;
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
