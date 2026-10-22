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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_erase(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default___redArg();
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
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
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
lean_object* v_type_86_; lean_object* v_value_87_; uint8_t v_nondep_88_; lean_object* v_snd_90_; lean_object* v___y_96_; 
v_type_86_ = lean_ctor_get(v_localDecl_20_, 3);
lean_inc_ref(v_type_86_);
v_value_87_ = lean_ctor_get(v_localDecl_20_, 4);
lean_inc_ref(v_value_87_);
v_nondep_88_ = lean_ctor_get_uint8(v_localDecl_20_, sizeof(void*)*5);
lean_dec_ref_known(v_localDecl_20_, 5);
if (v_generalizeNondepLet_22_ == 0)
{
goto v___jp_102_;
}
else
{
if (v_nondep_88_ == 0)
{
goto v___jp_102_;
}
else
{
lean_object* v___x_111_; uint8_t v_fst_113_; lean_object* v_mctx_114_; lean_object* v___y_132_; lean_object* v_mctx_137_; lean_object* v___x_138_; lean_object* v___x_139_; uint8_t v___x_140_; 
lean_dec_ref(v_value_87_);
v___x_111_ = lean_st_ref_get(v___y_23_);
v_mctx_137_ = lean_ctor_get(v___x_111_, 0);
lean_inc_ref_n(v_mctx_137_, 2);
lean_dec(v___x_111_);
v___x_138_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2);
v___x_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
lean_ctor_set(v___x_139_, 1, v_mctx_137_);
v___x_140_ = l_Lean_Expr_hasFVar(v_type_86_);
if (v___x_140_ == 0)
{
uint8_t v___x_141_; 
v___x_141_ = l_Lean_Expr_hasMVar(v_type_86_);
if (v___x_141_ == 0)
{
lean_dec_ref_known(v___x_139_, 2);
lean_dec_ref(v_type_86_);
lean_dec_ref(v___f_50_);
v_fst_113_ = v___x_141_;
v_mctx_114_ = v_mctx_137_;
goto v___jp_112_;
}
else
{
lean_object* v___x_142_; 
lean_dec_ref(v_mctx_137_);
v___x_142_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_50_, v___f_51_, v_type_86_, v___x_139_);
v___y_132_ = v___x_142_;
goto v___jp_131_;
}
}
else
{
lean_object* v___x_143_; 
lean_dec_ref(v_mctx_137_);
v___x_143_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_50_, v___f_51_, v_type_86_, v___x_139_);
v___y_132_ = v___x_143_;
goto v___jp_131_;
}
v___jp_112_:
{
lean_object* v___x_115_; lean_object* v_cache_116_; lean_object* v_zetaDeltaFVarIds_117_; lean_object* v_postponed_118_; lean_object* v_diag_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_129_; 
v___x_115_ = lean_st_ref_take(v___y_23_);
v_cache_116_ = lean_ctor_get(v___x_115_, 1);
v_zetaDeltaFVarIds_117_ = lean_ctor_get(v___x_115_, 2);
v_postponed_118_ = lean_ctor_get(v___x_115_, 3);
v_diag_119_ = lean_ctor_get(v___x_115_, 4);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_129_ == 0)
{
lean_object* v_unused_130_; 
v_unused_130_ = lean_ctor_get(v___x_115_, 0);
lean_dec(v_unused_130_);
v___x_121_ = v___x_115_;
v_isShared_122_ = v_isSharedCheck_129_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_diag_119_);
lean_inc(v_postponed_118_);
lean_inc(v_zetaDeltaFVarIds_117_);
lean_inc(v_cache_116_);
lean_dec(v___x_115_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_129_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_124_; 
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 0, v_mctx_114_);
v___x_124_ = v___x_121_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_mctx_114_);
lean_ctor_set(v_reuseFailAlloc_128_, 1, v_cache_116_);
lean_ctor_set(v_reuseFailAlloc_128_, 2, v_zetaDeltaFVarIds_117_);
lean_ctor_set(v_reuseFailAlloc_128_, 3, v_postponed_118_);
lean_ctor_set(v_reuseFailAlloc_128_, 4, v_diag_119_);
v___x_124_ = v_reuseFailAlloc_128_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_125_ = lean_st_ref_put(v___y_23_, v___x_124_);
v___x_126_ = lean_box(v_fst_113_);
v___x_127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
return v___x_127_;
}
}
}
v___jp_131_:
{
lean_object* v_snd_133_; lean_object* v_fst_134_; lean_object* v_mctx_135_; uint8_t v___x_136_; 
v_snd_133_ = lean_ctor_get(v___y_132_, 1);
lean_inc(v_snd_133_);
v_fst_134_ = lean_ctor_get(v___y_132_, 0);
lean_inc(v_fst_134_);
lean_dec_ref(v___y_132_);
v_mctx_135_ = lean_ctor_get(v_snd_133_, 1);
lean_inc_ref(v_mctx_135_);
lean_dec(v_snd_133_);
v___x_136_ = lean_unbox(v_fst_134_);
lean_dec(v_fst_134_);
v_fst_113_ = v___x_136_;
v_mctx_114_ = v_mctx_135_;
goto v___jp_112_;
}
}
}
v___jp_89_:
{
uint8_t v___x_91_; 
v___x_91_ = l_Lean_Expr_hasFVar(v_value_87_);
if (v___x_91_ == 0)
{
uint8_t v___x_92_; 
v___x_92_ = l_Lean_Expr_hasMVar(v_value_87_);
if (v___x_92_ == 0)
{
lean_dec_ref(v_value_87_);
lean_dec_ref(v___f_50_);
v_fst_26_ = v___x_92_;
v_snd_27_ = v_snd_90_;
goto v___jp_25_;
}
else
{
lean_object* v___x_93_; 
v___x_93_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_50_, v___f_51_, v_value_87_, v_snd_90_);
v___y_46_ = v___x_93_;
goto v___jp_45_;
}
}
else
{
lean_object* v___x_94_; 
v___x_94_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_50_, v___f_51_, v_value_87_, v_snd_90_);
v___y_46_ = v___x_94_;
goto v___jp_45_;
}
}
v___jp_95_:
{
lean_object* v_fst_97_; uint8_t v___x_98_; 
v_fst_97_ = lean_ctor_get(v___y_96_, 0);
v___x_98_ = lean_unbox(v_fst_97_);
if (v___x_98_ == 0)
{
lean_object* v_snd_99_; 
v_snd_99_ = lean_ctor_get(v___y_96_, 1);
lean_inc(v_snd_99_);
lean_dec_ref(v___y_96_);
v_snd_90_ = v_snd_99_;
goto v___jp_89_;
}
else
{
lean_object* v_snd_100_; uint8_t v___x_101_; 
lean_inc(v_fst_97_);
lean_dec_ref(v_value_87_);
lean_dec_ref(v___f_50_);
v_snd_100_ = lean_ctor_get(v___y_96_, 1);
lean_inc(v_snd_100_);
lean_dec_ref(v___y_96_);
v___x_101_ = lean_unbox(v_fst_97_);
lean_dec(v_fst_97_);
v_fst_26_ = v___x_101_;
v_snd_27_ = v_snd_100_;
goto v___jp_25_;
}
}
v___jp_102_:
{
lean_object* v___x_103_; lean_object* v_mctx_104_; lean_object* v___x_105_; lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_103_ = lean_st_ref_get(v___y_23_);
v_mctx_104_ = lean_ctor_get(v___x_103_, 0);
lean_inc_ref(v_mctx_104_);
lean_dec(v___x_103_);
v___x_105_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2);
v___x_106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
lean_ctor_set(v___x_106_, 1, v_mctx_104_);
v___x_107_ = l_Lean_Expr_hasFVar(v_type_86_);
if (v___x_107_ == 0)
{
uint8_t v___x_108_; 
v___x_108_ = l_Lean_Expr_hasMVar(v_type_86_);
if (v___x_108_ == 0)
{
lean_dec_ref(v_type_86_);
v_snd_90_ = v___x_106_;
goto v___jp_89_;
}
else
{
lean_object* v___x_109_; 
lean_inc_ref(v___f_50_);
v___x_109_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_50_, v___f_51_, v_type_86_, v___x_106_);
v___y_96_ = v___x_109_;
goto v___jp_95_;
}
}
else
{
lean_object* v___x_110_; 
lean_inc_ref(v___f_50_);
v___x_110_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_50_, v___f_51_, v_type_86_, v___x_106_);
v___y_96_ = v___x_110_;
goto v___jp_95_;
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
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___boxed(lean_object* v_localDecl_144_, lean_object* v_fvarId_145_, lean_object* v_generalizeNondepLet_146_, lean_object* v___y_147_, lean_object* v___y_148_){
_start:
{
uint8_t v_generalizeNondepLet_boxed_149_; lean_object* v_res_150_; 
v_generalizeNondepLet_boxed_149_ = lean_unbox(v_generalizeNondepLet_146_);
v_res_150_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg(v_localDecl_144_, v_fvarId_145_, v_generalizeNondepLet_boxed_149_, v___y_147_);
lean_dec(v___y_147_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0(lean_object* v_localDecl_151_, lean_object* v_fvarId_152_, uint8_t v_generalizeNondepLet_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg(v_localDecl_151_, v_fvarId_152_, v_generalizeNondepLet_153_, v___y_155_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___boxed(lean_object* v_localDecl_160_, lean_object* v_fvarId_161_, lean_object* v_generalizeNondepLet_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
uint8_t v_generalizeNondepLet_boxed_168_; lean_object* v_res_169_; 
v_generalizeNondepLet_boxed_168_ = lean_unbox(v_generalizeNondepLet_162_);
v_res_169_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0(v_localDecl_160_, v_fvarId_161_, v_generalizeNondepLet_boxed_168_, v___y_163_, v___y_164_, v___y_165_, v___y_166_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3___redArg(lean_object* v_e_170_, lean_object* v_fvarId_171_, lean_object* v___y_172_){
_start:
{
lean_object* v___f_174_; lean_object* v___f_175_; lean_object* v___x_176_; uint8_t v_fst_178_; lean_object* v_mctx_179_; lean_object* v___y_197_; lean_object* v_mctx_202_; lean_object* v___x_203_; lean_object* v___x_204_; uint8_t v___x_205_; 
v___f_174_ = ((lean_object*)(l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__0));
v___f_175_ = lean_alloc_closure((void*)(l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_175_, 0, v_fvarId_171_);
v___x_176_ = lean_st_ref_get(v___y_172_);
v_mctx_202_ = lean_ctor_get(v___x_176_, 0);
lean_inc_ref_n(v_mctx_202_, 2);
lean_dec(v___x_176_);
v___x_203_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2);
v___x_204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
lean_ctor_set(v___x_204_, 1, v_mctx_202_);
v___x_205_ = l_Lean_Expr_hasFVar(v_e_170_);
if (v___x_205_ == 0)
{
uint8_t v___x_206_; 
v___x_206_ = l_Lean_Expr_hasMVar(v_e_170_);
if (v___x_206_ == 0)
{
lean_dec_ref_known(v___x_204_, 2);
lean_dec_ref(v___f_175_);
lean_dec_ref(v_e_170_);
v_fst_178_ = v___x_206_;
v_mctx_179_ = v_mctx_202_;
goto v___jp_177_;
}
else
{
lean_object* v___x_207_; 
lean_dec_ref(v_mctx_202_);
v___x_207_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_175_, v___f_174_, v_e_170_, v___x_204_);
v___y_197_ = v___x_207_;
goto v___jp_196_;
}
}
else
{
lean_object* v___x_208_; 
lean_dec_ref(v_mctx_202_);
v___x_208_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_175_, v___f_174_, v_e_170_, v___x_204_);
v___y_197_ = v___x_208_;
goto v___jp_196_;
}
v___jp_177_:
{
lean_object* v___x_180_; lean_object* v_cache_181_; lean_object* v_zetaDeltaFVarIds_182_; lean_object* v_postponed_183_; lean_object* v_diag_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_194_; 
v___x_180_ = lean_st_ref_take(v___y_172_);
v_cache_181_ = lean_ctor_get(v___x_180_, 1);
v_zetaDeltaFVarIds_182_ = lean_ctor_get(v___x_180_, 2);
v_postponed_183_ = lean_ctor_get(v___x_180_, 3);
v_diag_184_ = lean_ctor_get(v___x_180_, 4);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_194_ == 0)
{
lean_object* v_unused_195_; 
v_unused_195_ = lean_ctor_get(v___x_180_, 0);
lean_dec(v_unused_195_);
v___x_186_ = v___x_180_;
v_isShared_187_ = v_isSharedCheck_194_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_diag_184_);
lean_inc(v_postponed_183_);
lean_inc(v_zetaDeltaFVarIds_182_);
lean_inc(v_cache_181_);
lean_dec(v___x_180_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_194_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_189_; 
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 0, v_mctx_179_);
v___x_189_ = v___x_186_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_mctx_179_);
lean_ctor_set(v_reuseFailAlloc_193_, 1, v_cache_181_);
lean_ctor_set(v_reuseFailAlloc_193_, 2, v_zetaDeltaFVarIds_182_);
lean_ctor_set(v_reuseFailAlloc_193_, 3, v_postponed_183_);
lean_ctor_set(v_reuseFailAlloc_193_, 4, v_diag_184_);
v___x_189_ = v_reuseFailAlloc_193_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_190_ = lean_st_ref_put(v___y_172_, v___x_189_);
v___x_191_ = lean_box(v_fst_178_);
v___x_192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
return v___x_192_;
}
}
}
v___jp_196_:
{
lean_object* v_snd_198_; lean_object* v_fst_199_; lean_object* v_mctx_200_; uint8_t v___x_201_; 
v_snd_198_ = lean_ctor_get(v___y_197_, 1);
lean_inc(v_snd_198_);
v_fst_199_ = lean_ctor_get(v___y_197_, 0);
lean_inc(v_fst_199_);
lean_dec_ref(v___y_197_);
v_mctx_200_ = lean_ctor_get(v_snd_198_, 1);
lean_inc_ref(v_mctx_200_);
lean_dec(v_snd_198_);
v___x_201_ = lean_unbox(v_fst_199_);
lean_dec(v_fst_199_);
v_fst_178_ = v___x_201_;
v_mctx_179_ = v_mctx_200_;
goto v___jp_177_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3___redArg___boxed(lean_object* v_e_209_, lean_object* v_fvarId_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3___redArg(v_e_209_, v_fvarId_210_, v___y_211_);
lean_dec(v___y_211_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3(lean_object* v_e_214_, lean_object* v_fvarId_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3___redArg(v_e_214_, v_fvarId_215_, v___y_217_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3___boxed(lean_object* v_e_222_, lean_object* v_fvarId_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3(v_e_222_, v_fvarId_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
lean_dec(v___y_225_);
lean_dec_ref(v___y_224_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg(lean_object* v_mvarId_230_, lean_object* v_x_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_230_, v_x_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_245_; 
v_a_238_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_245_ == 0)
{
v___x_240_ = v___x_237_;
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v___x_237_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_243_; 
if (v_isShared_241_ == 0)
{
v___x_243_ = v___x_240_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_a_238_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
else
{
lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_253_; 
v_a_246_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_253_ == 0)
{
v___x_248_ = v___x_237_;
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_dec(v___x_237_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_251_; 
if (v_isShared_249_ == 0)
{
v___x_251_ = v___x_248_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_a_246_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg___boxed(lean_object* v_mvarId_254_, lean_object* v_x_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg(v_mvarId_254_, v_x_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4(lean_object* v_00_u03b1_262_, lean_object* v_mvarId_263_, lean_object* v_x_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg(v_mvarId_263_, v_x_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___boxed(lean_object* v_00_u03b1_271_, lean_object* v_mvarId_272_, lean_object* v_x_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4(v_00_u03b1_271_, v_mvarId_272_, v_x_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
return v_res_279_;
}
}
LEAN_EXPORT uint8_t l_Lean_MVarId_clear___lam__0(lean_object* v_fvarId_280_, lean_object* v_localInst_281_){
_start:
{
lean_object* v_fvar_282_; lean_object* v___x_283_; uint8_t v___x_284_; 
v_fvar_282_ = lean_ctor_get(v_localInst_281_, 1);
v___x_283_ = l_Lean_Expr_fvarId_x21(v_fvar_282_);
v___x_284_ = l_Lean_instBEqFVarId_beq(v___x_283_, v_fvarId_280_);
lean_dec(v___x_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clear___lam__0___boxed(lean_object* v_fvarId_285_, lean_object* v_localInst_286_){
_start:
{
uint8_t v_res_287_; lean_object* v_r_288_; 
v_res_287_ = l_Lean_MVarId_clear___lam__0(v_fvarId_285_, v_localInst_286_);
lean_dec_ref(v_localInst_286_);
lean_dec(v_fvarId_285_);
v_r_288_ = lean_box(v_res_287_);
return v_r_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13_spec__14___redArg(lean_object* v_x_289_, lean_object* v_x_290_, lean_object* v_x_291_, lean_object* v_x_292_){
_start:
{
lean_object* v_ks_293_; lean_object* v_vs_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_318_; 
v_ks_293_ = lean_ctor_get(v_x_289_, 0);
v_vs_294_ = lean_ctor_get(v_x_289_, 1);
v_isSharedCheck_318_ = !lean_is_exclusive(v_x_289_);
if (v_isSharedCheck_318_ == 0)
{
v___x_296_ = v_x_289_;
v_isShared_297_ = v_isSharedCheck_318_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_vs_294_);
lean_inc(v_ks_293_);
lean_dec(v_x_289_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_318_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_298_; uint8_t v___x_299_; 
v___x_298_ = lean_array_get_size(v_ks_293_);
v___x_299_ = lean_nat_dec_lt(v_x_290_, v___x_298_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_303_; 
lean_dec(v_x_290_);
v___x_300_ = lean_array_push(v_ks_293_, v_x_291_);
v___x_301_ = lean_array_push(v_vs_294_, v_x_292_);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 1, v___x_301_);
lean_ctor_set(v___x_296_, 0, v___x_300_);
v___x_303_ = v___x_296_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v___x_300_);
lean_ctor_set(v_reuseFailAlloc_304_, 1, v___x_301_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
else
{
lean_object* v_k_x27_305_; uint8_t v___x_306_; 
v_k_x27_305_ = lean_array_fget_borrowed(v_ks_293_, v_x_290_);
v___x_306_ = l_Lean_instBEqMVarId_beq(v_x_291_, v_k_x27_305_);
if (v___x_306_ == 0)
{
lean_object* v___x_308_; 
if (v_isShared_297_ == 0)
{
v___x_308_ = v___x_296_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_ks_293_);
lean_ctor_set(v_reuseFailAlloc_312_, 1, v_vs_294_);
v___x_308_ = v_reuseFailAlloc_312_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_309_ = lean_unsigned_to_nat(1u);
v___x_310_ = lean_nat_add(v_x_290_, v___x_309_);
lean_dec(v_x_290_);
v_x_289_ = v___x_308_;
v_x_290_ = v___x_310_;
goto _start;
}
}
else
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_316_; 
v___x_313_ = lean_array_fset(v_ks_293_, v_x_290_, v_x_291_);
v___x_314_ = lean_array_fset(v_vs_294_, v_x_290_, v_x_292_);
lean_dec(v_x_290_);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 1, v___x_314_);
lean_ctor_set(v___x_296_, 0, v___x_313_);
v___x_316_ = v___x_296_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v___x_313_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v___x_314_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13___redArg(lean_object* v_n_319_, lean_object* v_k_320_, lean_object* v_v_321_){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_322_ = lean_unsigned_to_nat(0u);
v___x_323_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13_spec__14___redArg(v_n_319_, v___x_322_, v_k_320_, v_v_321_);
return v___x_323_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(lean_object* v_x_325_, size_t v_x_326_, size_t v_x_327_, lean_object* v_x_328_, lean_object* v_x_329_){
_start:
{
if (lean_obj_tag(v_x_325_) == 0)
{
lean_object* v_es_330_; size_t v___x_331_; size_t v___x_332_; lean_object* v_j_333_; lean_object* v___x_334_; uint8_t v___x_335_; 
v_es_330_ = lean_ctor_get(v_x_325_, 0);
v___x_331_ = ((size_t)31ULL);
v___x_332_ = lean_usize_land(v_x_326_, v___x_331_);
v_j_333_ = lean_usize_to_nat(v___x_332_);
v___x_334_ = lean_array_get_size(v_es_330_);
v___x_335_ = lean_nat_dec_lt(v_j_333_, v___x_334_);
if (v___x_335_ == 0)
{
lean_dec(v_j_333_);
lean_dec(v_x_329_);
lean_dec(v_x_328_);
return v_x_325_;
}
else
{
lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_374_; 
lean_inc_ref(v_es_330_);
v_isSharedCheck_374_ = !lean_is_exclusive(v_x_325_);
if (v_isSharedCheck_374_ == 0)
{
lean_object* v_unused_375_; 
v_unused_375_ = lean_ctor_get(v_x_325_, 0);
lean_dec(v_unused_375_);
v___x_337_ = v_x_325_;
v_isShared_338_ = v_isSharedCheck_374_;
goto v_resetjp_336_;
}
else
{
lean_dec(v_x_325_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_374_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v_v_339_; lean_object* v___x_340_; lean_object* v_xs_x27_341_; lean_object* v___y_343_; 
v_v_339_ = lean_array_fget(v_es_330_, v_j_333_);
v___x_340_ = lean_box(0);
v_xs_x27_341_ = lean_array_fset(v_es_330_, v_j_333_, v___x_340_);
switch(lean_obj_tag(v_v_339_))
{
case 0:
{
lean_object* v_key_348_; lean_object* v_val_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_359_; 
v_key_348_ = lean_ctor_get(v_v_339_, 0);
v_val_349_ = lean_ctor_get(v_v_339_, 1);
v_isSharedCheck_359_ = !lean_is_exclusive(v_v_339_);
if (v_isSharedCheck_359_ == 0)
{
v___x_351_ = v_v_339_;
v_isShared_352_ = v_isSharedCheck_359_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_val_349_);
lean_inc(v_key_348_);
lean_dec(v_v_339_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_359_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
uint8_t v___x_353_; 
v___x_353_ = l_Lean_instBEqMVarId_beq(v_x_328_, v_key_348_);
if (v___x_353_ == 0)
{
lean_object* v___x_354_; lean_object* v___x_355_; 
lean_del_object(v___x_351_);
v___x_354_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_348_, v_val_349_, v_x_328_, v_x_329_);
v___x_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
v___y_343_ = v___x_355_;
goto v___jp_342_;
}
else
{
lean_object* v___x_357_; 
lean_dec(v_val_349_);
lean_dec(v_key_348_);
if (v_isShared_352_ == 0)
{
lean_ctor_set(v___x_351_, 1, v_x_329_);
lean_ctor_set(v___x_351_, 0, v_x_328_);
v___x_357_ = v___x_351_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_x_328_);
lean_ctor_set(v_reuseFailAlloc_358_, 1, v_x_329_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
v___y_343_ = v___x_357_;
goto v___jp_342_;
}
}
}
}
case 1:
{
lean_object* v_node_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_372_; 
v_node_360_ = lean_ctor_get(v_v_339_, 0);
v_isSharedCheck_372_ = !lean_is_exclusive(v_v_339_);
if (v_isSharedCheck_372_ == 0)
{
v___x_362_ = v_v_339_;
v_isShared_363_ = v_isSharedCheck_372_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_node_360_);
lean_dec(v_v_339_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_372_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
size_t v___x_364_; size_t v___x_365_; size_t v___x_366_; size_t v___x_367_; lean_object* v___x_368_; lean_object* v___x_370_; 
v___x_364_ = ((size_t)5ULL);
v___x_365_ = lean_usize_shift_right(v_x_326_, v___x_364_);
v___x_366_ = ((size_t)1ULL);
v___x_367_ = lean_usize_add(v_x_327_, v___x_366_);
v___x_368_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_node_360_, v___x_365_, v___x_367_, v_x_328_, v_x_329_);
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 0, v___x_368_);
v___x_370_ = v___x_362_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v___x_368_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
v___y_343_ = v___x_370_;
goto v___jp_342_;
}
}
}
default: 
{
lean_object* v___x_373_; 
v___x_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_373_, 0, v_x_328_);
lean_ctor_set(v___x_373_, 1, v_x_329_);
v___y_343_ = v___x_373_;
goto v___jp_342_;
}
}
v___jp_342_:
{
lean_object* v___x_344_; lean_object* v___x_346_; 
v___x_344_ = lean_array_fset(v_xs_x27_341_, v_j_333_, v___y_343_);
lean_dec(v_j_333_);
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 0, v___x_344_);
v___x_346_ = v___x_337_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v___x_344_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
}
else
{
lean_object* v_ks_376_; lean_object* v_vs_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_395_; 
v_ks_376_ = lean_ctor_get(v_x_325_, 0);
v_vs_377_ = lean_ctor_get(v_x_325_, 1);
v_isSharedCheck_395_ = !lean_is_exclusive(v_x_325_);
if (v_isSharedCheck_395_ == 0)
{
v___x_379_ = v_x_325_;
v_isShared_380_ = v_isSharedCheck_395_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_vs_377_);
lean_inc(v_ks_376_);
lean_dec(v_x_325_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_395_;
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
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_ks_376_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v_vs_377_);
v___x_382_ = v_reuseFailAlloc_394_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
lean_object* v_newNode_383_; size_t v___x_384_; uint8_t v___x_385_; 
v_newNode_383_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13___redArg(v___x_382_, v_x_328_, v_x_329_);
v___x_384_ = ((size_t)7ULL);
v___x_385_ = lean_usize_dec_le(v___x_384_, v_x_327_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; lean_object* v___x_387_; uint8_t v___x_388_; 
v___x_386_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_383_);
v___x_387_ = lean_unsigned_to_nat(4u);
v___x_388_ = lean_nat_dec_lt(v___x_386_, v___x_387_);
lean_dec(v___x_386_);
if (v___x_388_ == 0)
{
lean_object* v_ks_389_; lean_object* v_vs_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v_ks_389_ = lean_ctor_get(v_newNode_383_, 0);
lean_inc_ref(v_ks_389_);
v_vs_390_ = lean_ctor_get(v_newNode_383_, 1);
lean_inc_ref(v_vs_390_);
lean_dec_ref(v_newNode_383_);
v___x_391_ = lean_unsigned_to_nat(0u);
v___x_392_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__0);
v___x_393_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg(v_x_327_, v_ks_389_, v_vs_390_, v___x_391_, v___x_392_);
lean_dec_ref(v_vs_390_);
lean_dec_ref(v_ks_389_);
return v___x_393_;
}
else
{
return v_newNode_383_;
}
}
else
{
return v_newNode_383_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg(size_t v_depth_396_, lean_object* v_keys_397_, lean_object* v_vals_398_, lean_object* v_i_399_, lean_object* v_entries_400_){
_start:
{
lean_object* v___x_401_; uint8_t v___x_402_; 
v___x_401_ = lean_array_get_size(v_keys_397_);
v___x_402_ = lean_nat_dec_lt(v_i_399_, v___x_401_);
if (v___x_402_ == 0)
{
lean_dec(v_i_399_);
return v_entries_400_;
}
else
{
lean_object* v_k_403_; lean_object* v_v_404_; uint64_t v___x_405_; size_t v_h_406_; size_t v___x_407_; lean_object* v___x_408_; size_t v___x_409_; size_t v___x_410_; size_t v___x_411_; size_t v_h_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v_k_403_ = lean_array_fget_borrowed(v_keys_397_, v_i_399_);
v_v_404_ = lean_array_fget_borrowed(v_vals_398_, v_i_399_);
v___x_405_ = l_Lean_instHashableMVarId_hash(v_k_403_);
v_h_406_ = lean_uint64_to_usize(v___x_405_);
v___x_407_ = ((size_t)5ULL);
v___x_408_ = lean_unsigned_to_nat(1u);
v___x_409_ = ((size_t)1ULL);
v___x_410_ = lean_usize_sub(v_depth_396_, v___x_409_);
v___x_411_ = lean_usize_mul(v___x_407_, v___x_410_);
v_h_412_ = lean_usize_shift_right(v_h_406_, v___x_411_);
v___x_413_ = lean_nat_add(v_i_399_, v___x_408_);
lean_dec(v_i_399_);
lean_inc(v_v_404_);
lean_inc(v_k_403_);
v___x_414_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_entries_400_, v_h_412_, v_depth_396_, v_k_403_, v_v_404_);
v_i_399_ = v___x_413_;
v_entries_400_ = v___x_414_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg___boxed(lean_object* v_depth_416_, lean_object* v_keys_417_, lean_object* v_vals_418_, lean_object* v_i_419_, lean_object* v_entries_420_){
_start:
{
size_t v_depth_boxed_421_; lean_object* v_res_422_; 
v_depth_boxed_421_ = lean_unbox_usize(v_depth_416_);
lean_dec(v_depth_416_);
v_res_422_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg(v_depth_boxed_421_, v_keys_417_, v_vals_418_, v_i_419_, v_entries_420_);
lean_dec_ref(v_vals_418_);
lean_dec_ref(v_keys_417_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___boxed(lean_object* v_x_423_, lean_object* v_x_424_, lean_object* v_x_425_, lean_object* v_x_426_, lean_object* v_x_427_){
_start:
{
size_t v_x_7912__boxed_428_; size_t v_x_7913__boxed_429_; lean_object* v_res_430_; 
v_x_7912__boxed_428_ = lean_unbox_usize(v_x_424_);
lean_dec(v_x_424_);
v_x_7913__boxed_429_ = lean_unbox_usize(v_x_425_);
lean_dec(v_x_425_);
v_res_430_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_x_423_, v_x_7912__boxed_428_, v_x_7913__boxed_429_, v_x_426_, v_x_427_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3___redArg(lean_object* v_x_431_, lean_object* v_x_432_, lean_object* v_x_433_){
_start:
{
uint64_t v___x_434_; size_t v___x_435_; size_t v___x_436_; lean_object* v___x_437_; 
v___x_434_ = l_Lean_instHashableMVarId_hash(v_x_432_);
v___x_435_ = lean_uint64_to_usize(v___x_434_);
v___x_436_ = ((size_t)1ULL);
v___x_437_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_x_431_, v___x_435_, v___x_436_, v_x_432_, v_x_433_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg(lean_object* v_mvarId_438_, lean_object* v_val_439_, lean_object* v___y_440_){
_start:
{
lean_object* v___x_442_; lean_object* v_mctx_443_; lean_object* v_cache_444_; lean_object* v_zetaDeltaFVarIds_445_; lean_object* v_postponed_446_; lean_object* v_diag_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_476_; 
v___x_442_ = lean_st_ref_take(v___y_440_);
v_mctx_443_ = lean_ctor_get(v___x_442_, 0);
v_cache_444_ = lean_ctor_get(v___x_442_, 1);
v_zetaDeltaFVarIds_445_ = lean_ctor_get(v___x_442_, 2);
v_postponed_446_ = lean_ctor_get(v___x_442_, 3);
v_diag_447_ = lean_ctor_get(v___x_442_, 4);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_476_ == 0)
{
v___x_449_ = v___x_442_;
v_isShared_450_ = v_isSharedCheck_476_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_diag_447_);
lean_inc(v_postponed_446_);
lean_inc(v_zetaDeltaFVarIds_445_);
lean_inc(v_cache_444_);
lean_inc(v_mctx_443_);
lean_dec(v___x_442_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_476_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v_depth_451_; lean_object* v_levelAssignDepth_452_; lean_object* v_lmvarCounter_453_; lean_object* v_mvarCounter_454_; lean_object* v_lDecls_455_; lean_object* v_decls_456_; lean_object* v_userNames_457_; lean_object* v_lAssignment_458_; lean_object* v_eAssignment_459_; lean_object* v_dAssignment_460_; lean_object* v_synthNormMemo_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_475_; 
v_depth_451_ = lean_ctor_get(v_mctx_443_, 0);
v_levelAssignDepth_452_ = lean_ctor_get(v_mctx_443_, 1);
v_lmvarCounter_453_ = lean_ctor_get(v_mctx_443_, 2);
v_mvarCounter_454_ = lean_ctor_get(v_mctx_443_, 3);
v_lDecls_455_ = lean_ctor_get(v_mctx_443_, 4);
v_decls_456_ = lean_ctor_get(v_mctx_443_, 5);
v_userNames_457_ = lean_ctor_get(v_mctx_443_, 6);
v_lAssignment_458_ = lean_ctor_get(v_mctx_443_, 7);
v_eAssignment_459_ = lean_ctor_get(v_mctx_443_, 8);
v_dAssignment_460_ = lean_ctor_get(v_mctx_443_, 9);
v_synthNormMemo_461_ = lean_ctor_get(v_mctx_443_, 10);
v_isSharedCheck_475_ = !lean_is_exclusive(v_mctx_443_);
if (v_isSharedCheck_475_ == 0)
{
v___x_463_ = v_mctx_443_;
v_isShared_464_ = v_isSharedCheck_475_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_synthNormMemo_461_);
lean_inc(v_dAssignment_460_);
lean_inc(v_eAssignment_459_);
lean_inc(v_lAssignment_458_);
lean_inc(v_userNames_457_);
lean_inc(v_decls_456_);
lean_inc(v_lDecls_455_);
lean_inc(v_mvarCounter_454_);
lean_inc(v_lmvarCounter_453_);
lean_inc(v_levelAssignDepth_452_);
lean_inc(v_depth_451_);
lean_dec(v_mctx_443_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_475_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_468_; 
v___x_465_ = lean_box(0);
v___x_466_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3___redArg(v_eAssignment_459_, v_mvarId_438_, v_val_439_);
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 8, v___x_466_);
v___x_468_ = v___x_463_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_depth_451_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v_levelAssignDepth_452_);
lean_ctor_set(v_reuseFailAlloc_474_, 2, v_lmvarCounter_453_);
lean_ctor_set(v_reuseFailAlloc_474_, 3, v_mvarCounter_454_);
lean_ctor_set(v_reuseFailAlloc_474_, 4, v_lDecls_455_);
lean_ctor_set(v_reuseFailAlloc_474_, 5, v_decls_456_);
lean_ctor_set(v_reuseFailAlloc_474_, 6, v_userNames_457_);
lean_ctor_set(v_reuseFailAlloc_474_, 7, v_lAssignment_458_);
lean_ctor_set(v_reuseFailAlloc_474_, 8, v___x_466_);
lean_ctor_set(v_reuseFailAlloc_474_, 9, v_dAssignment_460_);
lean_ctor_set(v_reuseFailAlloc_474_, 10, v_synthNormMemo_461_);
v___x_468_ = v_reuseFailAlloc_474_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
lean_object* v___x_470_; 
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 0, v___x_468_);
v___x_470_ = v___x_449_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_468_);
lean_ctor_set(v_reuseFailAlloc_473_, 1, v_cache_444_);
lean_ctor_set(v_reuseFailAlloc_473_, 2, v_zetaDeltaFVarIds_445_);
lean_ctor_set(v_reuseFailAlloc_473_, 3, v_postponed_446_);
lean_ctor_set(v_reuseFailAlloc_473_, 4, v_diag_447_);
v___x_470_ = v_reuseFailAlloc_473_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = lean_st_ref_put(v___y_440_, v___x_470_);
v___x_472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_472_, 0, v___x_465_);
return v___x_472_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg___boxed(lean_object* v_mvarId_477_, lean_object* v_val_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg(v_mvarId_477_, v_val_478_, v___y_479_);
lean_dec(v___y_479_);
return v_res_481_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3(void){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__2));
v___x_487_ = l_Lean_stringToMessageData(v___x_486_);
return v___x_487_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5(void){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__4));
v___x_490_ = l_Lean_stringToMessageData(v___x_489_);
return v___x_490_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7(void){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__6));
v___x_493_ = l_Lean_stringToMessageData(v___x_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9(lean_object* v_fvarId_494_, lean_object* v_mvarId_495_, lean_object* v_as_496_, size_t v_i_497_, size_t v_stop_498_, lean_object* v_b_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
lean_object* v_a_506_; uint8_t v___x_510_; 
v___x_510_ = lean_usize_dec_eq(v_i_497_, v_stop_498_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; 
v___x_511_ = lean_array_uget(v_as_496_, v_i_497_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v___x_512_; 
v___x_512_ = lean_box(0);
v_a_506_ = v___x_512_;
goto v___jp_505_;
}
else
{
lean_object* v_val_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_550_; 
v_val_513_ = lean_ctor_get(v___x_511_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_550_ == 0)
{
v___x_515_ = v___x_511_;
v_isShared_516_ = v_isSharedCheck_550_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_val_513_);
lean_dec(v___x_511_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_550_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_517_; uint8_t v___x_518_; 
v___x_517_ = l_Lean_LocalDecl_fvarId(v_val_513_);
v___x_518_ = l_Lean_instBEqFVarId_beq(v___x_517_, v_fvarId_494_);
lean_dec(v___x_517_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; uint8_t v___x_520_; lean_object* v___x_521_; 
v___x_519_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__1));
v___x_520_ = 1;
lean_inc(v_fvarId_494_);
lean_inc(v_val_513_);
v___x_521_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg(v_val_513_, v_fvarId_494_, v___x_520_, v___y_501_);
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
lean_del_object(v___x_515_);
lean_dec(v_val_513_);
v___x_524_ = lean_box(0);
v_a_506_ = v___x_524_;
goto v___jp_505_;
}
else
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_537_; 
v___x_525_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3);
v___x_526_ = l_Lean_LocalDecl_toExpr(v_val_513_);
v___x_527_ = l_Lean_MessageData_ofExpr(v___x_526_);
v___x_528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_525_);
lean_ctor_set(v___x_528_, 1, v___x_527_);
v___x_529_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5);
v___x_530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_528_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
lean_inc(v_fvarId_494_);
v___x_531_ = l_Lean_mkFVar(v_fvarId_494_);
v___x_532_ = l_Lean_MessageData_ofExpr(v___x_531_);
v___x_533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_530_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
v___x_534_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7);
v___x_535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_533_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 0, v___x_535_);
v___x_537_ = v___x_515_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v___x_535_);
v___x_537_ = v_reuseFailAlloc_540_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
lean_object* v___x_538_; 
lean_inc(v_mvarId_495_);
v___x_538_ = l_Lean_Meta_throwTacticEx___redArg(v___x_519_, v_mvarId_495_, v___x_537_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v_a_539_; 
v_a_539_ = lean_ctor_get(v___x_538_, 0);
lean_inc(v_a_539_);
lean_dec_ref_known(v___x_538_, 1);
v_a_506_ = v_a_539_;
goto v___jp_505_;
}
else
{
lean_dec(v_mvarId_495_);
lean_dec(v_fvarId_494_);
return v___x_538_;
}
}
}
}
else
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
lean_del_object(v___x_515_);
lean_dec(v_val_513_);
lean_dec(v_mvarId_495_);
lean_dec(v_fvarId_494_);
v_a_541_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v___x_521_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_521_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_a_541_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
else
{
lean_object* v___x_549_; 
lean_del_object(v___x_515_);
lean_dec(v_val_513_);
v___x_549_ = lean_box(0);
v_a_506_ = v___x_549_;
goto v___jp_505_;
}
}
}
}
else
{
lean_object* v___x_551_; 
lean_dec(v_mvarId_495_);
lean_dec(v_fvarId_494_);
v___x_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_551_, 0, v_b_499_);
return v___x_551_;
}
v___jp_505_:
{
size_t v___x_507_; size_t v___x_508_; 
v___x_507_ = ((size_t)1ULL);
v___x_508_ = lean_usize_add(v_i_497_, v___x_507_);
v_i_497_ = v___x_508_;
v_b_499_ = v_a_506_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___boxed(lean_object* v_fvarId_552_, lean_object* v_mvarId_553_, lean_object* v_as_554_, lean_object* v_i_555_, lean_object* v_stop_556_, lean_object* v_b_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
size_t v_i_boxed_563_; size_t v_stop_boxed_564_; lean_object* v_res_565_; 
v_i_boxed_563_ = lean_unbox_usize(v_i_555_);
lean_dec(v_i_555_);
v_stop_boxed_564_ = lean_unbox_usize(v_stop_556_);
lean_dec(v_stop_556_);
v_res_565_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9(v_fvarId_552_, v_mvarId_553_, v_as_554_, v_i_boxed_563_, v_stop_boxed_564_, v_b_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
lean_dec_ref(v_as_554_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(lean_object* v_fvarId_566_, lean_object* v_mvarId_567_, lean_object* v_as_568_, size_t v_i_569_, size_t v_stop_570_, lean_object* v_b_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
lean_object* v_a_578_; uint8_t v___x_582_; 
v___x_582_ = lean_usize_dec_eq(v_i_569_, v_stop_570_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; 
v___x_583_ = lean_array_uget(v_as_568_, v_i_569_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v___x_584_; 
v___x_584_ = lean_box(0);
v_a_578_ = v___x_584_;
goto v___jp_577_;
}
else
{
lean_object* v_val_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_622_; 
v_val_585_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_622_ == 0)
{
v___x_587_ = v___x_583_;
v_isShared_588_ = v_isSharedCheck_622_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_val_585_);
lean_dec(v___x_583_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_622_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_589_ = l_Lean_LocalDecl_fvarId(v_val_585_);
v___x_590_ = l_Lean_instBEqFVarId_beq(v___x_589_, v_fvarId_566_);
lean_dec(v___x_589_);
if (v___x_590_ == 0)
{
lean_object* v___x_591_; uint8_t v___x_592_; lean_object* v___x_593_; 
v___x_591_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__1));
v___x_592_ = 1;
lean_inc(v_fvarId_566_);
lean_inc(v_val_585_);
v___x_593_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg(v_val_585_, v_fvarId_566_, v___x_592_, v___y_573_);
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
lean_del_object(v___x_587_);
lean_dec(v_val_585_);
v___x_596_ = lean_box(0);
v_a_578_ = v___x_596_;
goto v___jp_577_;
}
else
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_609_; 
v___x_597_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3);
v___x_598_ = l_Lean_LocalDecl_toExpr(v_val_585_);
v___x_599_ = l_Lean_MessageData_ofExpr(v___x_598_);
v___x_600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_597_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
v___x_601_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5);
v___x_602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_600_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
lean_inc(v_fvarId_566_);
v___x_603_ = l_Lean_mkFVar(v_fvarId_566_);
v___x_604_ = l_Lean_MessageData_ofExpr(v___x_603_);
v___x_605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_602_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
v___x_606_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7);
v___x_607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_605_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 0, v___x_607_);
v___x_609_ = v___x_587_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_607_);
v___x_609_ = v_reuseFailAlloc_612_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
lean_object* v___x_610_; 
lean_inc(v_mvarId_567_);
v___x_610_ = l_Lean_Meta_throwTacticEx___redArg(v___x_591_, v_mvarId_567_, v___x_609_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v_a_611_; 
v_a_611_ = lean_ctor_get(v___x_610_, 0);
lean_inc(v_a_611_);
lean_dec_ref_known(v___x_610_, 1);
v_a_578_ = v_a_611_;
goto v___jp_577_;
}
else
{
lean_dec(v_mvarId_567_);
lean_dec(v_fvarId_566_);
return v___x_610_;
}
}
}
}
else
{
lean_object* v_a_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_620_; 
lean_del_object(v___x_587_);
lean_dec(v_val_585_);
lean_dec(v_mvarId_567_);
lean_dec(v_fvarId_566_);
v_a_613_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_620_ == 0)
{
v___x_615_ = v___x_593_;
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_a_613_);
lean_dec(v___x_593_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_618_; 
if (v_isShared_616_ == 0)
{
v___x_618_ = v___x_615_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_a_613_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
}
else
{
lean_object* v___x_621_; 
lean_del_object(v___x_587_);
lean_dec(v_val_585_);
v___x_621_ = lean_box(0);
v_a_578_ = v___x_621_;
goto v___jp_577_;
}
}
}
}
else
{
lean_object* v___x_623_; 
lean_dec(v_mvarId_567_);
lean_dec(v_fvarId_566_);
v___x_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_623_, 0, v_b_571_);
return v___x_623_;
}
v___jp_577_:
{
size_t v___x_579_; size_t v___x_580_; lean_object* v___x_581_; 
v___x_579_ = ((size_t)1ULL);
v___x_580_ = lean_usize_add(v_i_569_, v___x_579_);
v___x_581_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9(v_fvarId_566_, v_mvarId_567_, v_as_568_, v___x_580_, v_stop_570_, v_a_578_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
return v___x_581_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5___boxed(lean_object* v_fvarId_624_, lean_object* v_mvarId_625_, lean_object* v_as_626_, lean_object* v_i_627_, lean_object* v_stop_628_, lean_object* v_b_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_){
_start:
{
size_t v_i_boxed_635_; size_t v_stop_boxed_636_; lean_object* v_res_637_; 
v_i_boxed_635_ = lean_unbox_usize(v_i_627_);
lean_dec(v_i_627_);
v_stop_boxed_636_ = lean_unbox_usize(v_stop_628_);
lean_dec(v_stop_628_);
v_res_637_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_624_, v_mvarId_625_, v_as_626_, v_i_boxed_635_, v_stop_boxed_636_, v_b_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec_ref(v_as_626_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6(lean_object* v_fvarId_638_, lean_object* v_mvarId_639_, lean_object* v_x_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
if (lean_obj_tag(v_x_640_) == 0)
{
lean_object* v_cs_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_660_; 
v_cs_646_ = lean_ctor_get(v_x_640_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v_x_640_);
if (v_isSharedCheck_660_ == 0)
{
v___x_648_ = v_x_640_;
v_isShared_649_ = v_isSharedCheck_660_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_cs_646_);
lean_dec(v_x_640_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_660_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; uint8_t v___x_653_; 
v___x_650_ = lean_unsigned_to_nat(0u);
v___x_651_ = lean_array_get_size(v_cs_646_);
v___x_652_ = lean_box(0);
v___x_653_ = lean_nat_dec_lt(v___x_650_, v___x_651_);
if (v___x_653_ == 0)
{
lean_object* v___x_655_; 
lean_dec_ref(v_cs_646_);
lean_dec(v_mvarId_639_);
lean_dec(v_fvarId_638_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 0, v___x_652_);
v___x_655_ = v___x_648_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v___x_652_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
else
{
size_t v___x_657_; size_t v___x_658_; lean_object* v___x_659_; 
lean_del_object(v___x_648_);
v___x_657_ = ((size_t)0ULL);
v___x_658_ = lean_usize_of_nat(v___x_651_);
v___x_659_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(v_fvarId_638_, v_mvarId_639_, v_cs_646_, v___x_657_, v___x_658_, v___x_652_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
lean_dec_ref(v_cs_646_);
return v___x_659_;
}
}
}
else
{
lean_object* v_vs_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_675_; 
v_vs_661_ = lean_ctor_get(v_x_640_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v_x_640_);
if (v_isSharedCheck_675_ == 0)
{
v___x_663_ = v_x_640_;
v_isShared_664_ = v_isSharedCheck_675_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_vs_661_);
lean_dec(v_x_640_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_675_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; uint8_t v___x_668_; 
v___x_665_ = lean_unsigned_to_nat(0u);
v___x_666_ = lean_array_get_size(v_vs_661_);
v___x_667_ = lean_box(0);
v___x_668_ = lean_nat_dec_lt(v___x_665_, v___x_666_);
if (v___x_668_ == 0)
{
lean_object* v___x_670_; 
lean_dec_ref(v_vs_661_);
lean_dec(v_mvarId_639_);
lean_dec(v_fvarId_638_);
if (v_isShared_664_ == 0)
{
lean_ctor_set_tag(v___x_663_, 0);
lean_ctor_set(v___x_663_, 0, v___x_667_);
v___x_670_ = v___x_663_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v___x_667_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
else
{
size_t v___x_672_; size_t v___x_673_; lean_object* v___x_674_; 
lean_del_object(v___x_663_);
v___x_672_ = ((size_t)0ULL);
v___x_673_ = lean_usize_of_nat(v___x_666_);
v___x_674_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_638_, v_mvarId_639_, v_vs_661_, v___x_672_, v___x_673_, v___x_667_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
lean_dec_ref(v_vs_661_);
return v___x_674_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(lean_object* v_fvarId_676_, lean_object* v_mvarId_677_, lean_object* v_as_678_, size_t v_i_679_, size_t v_stop_680_, lean_object* v_b_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
uint8_t v___x_687_; 
v___x_687_ = lean_usize_dec_eq(v_i_679_, v_stop_680_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = lean_array_uget_borrowed(v_as_678_, v_i_679_);
lean_inc(v___x_688_);
lean_inc(v_mvarId_677_);
lean_inc(v_fvarId_676_);
v___x_689_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6(v_fvarId_676_, v_mvarId_677_, v___x_688_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v_a_690_; size_t v___x_691_; size_t v___x_692_; 
v_a_690_ = lean_ctor_get(v___x_689_, 0);
lean_inc(v_a_690_);
lean_dec_ref_known(v___x_689_, 1);
v___x_691_ = ((size_t)1ULL);
v___x_692_ = lean_usize_add(v_i_679_, v___x_691_);
v_i_679_ = v___x_692_;
v_b_681_ = v_a_690_;
goto _start;
}
else
{
lean_dec(v_mvarId_677_);
lean_dec(v_fvarId_676_);
return v___x_689_;
}
}
else
{
lean_object* v___x_694_; 
lean_dec(v_mvarId_677_);
lean_dec(v_fvarId_676_);
v___x_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_694_, 0, v_b_681_);
return v___x_694_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7___boxed(lean_object* v_fvarId_695_, lean_object* v_mvarId_696_, lean_object* v_as_697_, lean_object* v_i_698_, lean_object* v_stop_699_, lean_object* v_b_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
size_t v_i_boxed_706_; size_t v_stop_boxed_707_; lean_object* v_res_708_; 
v_i_boxed_706_ = lean_unbox_usize(v_i_698_);
lean_dec(v_i_698_);
v_stop_boxed_707_ = lean_unbox_usize(v_stop_699_);
lean_dec(v_stop_699_);
v_res_708_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(v_fvarId_695_, v_mvarId_696_, v_as_697_, v_i_boxed_706_, v_stop_boxed_707_, v_b_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec_ref(v_as_697_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6___boxed(lean_object* v_fvarId_709_, lean_object* v_mvarId_710_, lean_object* v_x_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6(v_fvarId_709_, v_mvarId_710_, v_x_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6(lean_object* v_fvarId_718_, lean_object* v_mvarId_719_, lean_object* v_t_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
lean_object* v_root_726_; lean_object* v_tail_727_; lean_object* v___x_728_; 
v_root_726_ = lean_ctor_get(v_t_720_, 0);
lean_inc_ref(v_root_726_);
v_tail_727_ = lean_ctor_get(v_t_720_, 1);
lean_inc_ref(v_tail_727_);
lean_dec_ref(v_t_720_);
lean_inc(v_mvarId_719_);
lean_inc(v_fvarId_718_);
v___x_728_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6(v_fvarId_718_, v_mvarId_719_, v_root_726_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_742_; 
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_742_ == 0)
{
lean_object* v_unused_743_; 
v_unused_743_ = lean_ctor_get(v___x_728_, 0);
lean_dec(v_unused_743_);
v___x_730_ = v___x_728_;
v_isShared_731_ = v_isSharedCheck_742_;
goto v_resetjp_729_;
}
else
{
lean_dec(v___x_728_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_742_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; uint8_t v___x_735_; 
v___x_732_ = lean_unsigned_to_nat(0u);
v___x_733_ = lean_array_get_size(v_tail_727_);
v___x_734_ = lean_box(0);
v___x_735_ = lean_nat_dec_lt(v___x_732_, v___x_733_);
if (v___x_735_ == 0)
{
lean_object* v___x_737_; 
lean_dec_ref(v_tail_727_);
lean_dec(v_mvarId_719_);
lean_dec(v_fvarId_718_);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 0, v___x_734_);
v___x_737_ = v___x_730_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_734_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
else
{
size_t v___x_739_; size_t v___x_740_; lean_object* v___x_741_; 
lean_del_object(v___x_730_);
v___x_739_ = ((size_t)0ULL);
v___x_740_ = lean_usize_of_nat(v___x_733_);
v___x_741_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_718_, v_mvarId_719_, v_tail_727_, v___x_739_, v___x_740_, v___x_734_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
lean_dec_ref(v_tail_727_);
return v___x_741_;
}
}
}
else
{
lean_dec_ref(v_tail_727_);
lean_dec(v_mvarId_719_);
lean_dec(v_fvarId_718_);
return v___x_728_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6___boxed(lean_object* v_fvarId_744_, lean_object* v_mvarId_745_, lean_object* v_t_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6(v_fvarId_744_, v_mvarId_745_, v_t_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
return v_res_752_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4(lean_object* v_fvarId_754_, lean_object* v_mvarId_755_, lean_object* v_x_756_, size_t v_x_757_, size_t v_x_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
if (lean_obj_tag(v_x_756_) == 0)
{
lean_object* v_cs_764_; lean_object* v___x_765_; size_t v___x_766_; lean_object* v_j_767_; lean_object* v___x_768_; size_t v___x_769_; size_t v___x_770_; size_t v___x_771_; size_t v___x_772_; size_t v___x_773_; size_t v___x_774_; lean_object* v___x_775_; 
v_cs_764_ = lean_ctor_get(v_x_756_, 0);
lean_inc_ref(v_cs_764_);
lean_dec_ref_known(v_x_756_, 1);
v___x_765_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0);
v___x_766_ = lean_usize_shift_right(v_x_757_, v_x_758_);
v_j_767_ = lean_usize_to_nat(v___x_766_);
v___x_768_ = lean_array_get_borrowed(v___x_765_, v_cs_764_, v_j_767_);
v___x_769_ = ((size_t)1ULL);
v___x_770_ = lean_usize_shift_left(v___x_769_, v_x_758_);
v___x_771_ = lean_usize_sub(v___x_770_, v___x_769_);
v___x_772_ = lean_usize_land(v_x_757_, v___x_771_);
v___x_773_ = ((size_t)5ULL);
v___x_774_ = lean_usize_sub(v_x_758_, v___x_773_);
lean_inc(v___x_768_);
lean_inc(v_mvarId_755_);
lean_inc(v_fvarId_754_);
v___x_775_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4(v_fvarId_754_, v_mvarId_755_, v___x_768_, v___x_772_, v___x_774_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_790_; 
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_790_ == 0)
{
lean_object* v_unused_791_; 
v_unused_791_ = lean_ctor_get(v___x_775_, 0);
lean_dec(v_unused_791_);
v___x_777_ = v___x_775_;
v_isShared_778_ = v_isSharedCheck_790_;
goto v_resetjp_776_;
}
else
{
lean_dec(v___x_775_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_790_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; uint8_t v___x_783_; 
v___x_779_ = lean_unsigned_to_nat(1u);
v___x_780_ = lean_nat_add(v_j_767_, v___x_779_);
lean_dec(v_j_767_);
v___x_781_ = lean_array_get_size(v_cs_764_);
v___x_782_ = lean_box(0);
v___x_783_ = lean_nat_dec_lt(v___x_780_, v___x_781_);
if (v___x_783_ == 0)
{
lean_object* v___x_785_; 
lean_dec(v___x_780_);
lean_dec_ref(v_cs_764_);
lean_dec(v_mvarId_755_);
lean_dec(v_fvarId_754_);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 0, v___x_782_);
v___x_785_ = v___x_777_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v___x_782_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
else
{
size_t v___x_787_; size_t v___x_788_; lean_object* v___x_789_; 
lean_del_object(v___x_777_);
v___x_787_ = lean_usize_of_nat(v___x_780_);
lean_dec(v___x_780_);
v___x_788_ = lean_usize_of_nat(v___x_781_);
v___x_789_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(v_fvarId_754_, v_mvarId_755_, v_cs_764_, v___x_787_, v___x_788_, v___x_782_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
lean_dec_ref(v_cs_764_);
return v___x_789_;
}
}
}
else
{
lean_dec(v_j_767_);
lean_dec_ref(v_cs_764_);
lean_dec(v_mvarId_755_);
lean_dec(v_fvarId_754_);
return v___x_775_;
}
}
else
{
lean_object* v_vs_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_806_; 
v_vs_792_ = lean_ctor_get(v_x_756_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v_x_756_);
if (v_isSharedCheck_806_ == 0)
{
v___x_794_ = v_x_756_;
v_isShared_795_ = v_isSharedCheck_806_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_vs_792_);
lean_dec(v_x_756_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_806_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; uint8_t v___x_799_; 
v___x_796_ = lean_usize_to_nat(v_x_757_);
v___x_797_ = lean_array_get_size(v_vs_792_);
v___x_798_ = lean_box(0);
v___x_799_ = lean_nat_dec_lt(v___x_796_, v___x_797_);
if (v___x_799_ == 0)
{
lean_object* v___x_801_; 
lean_dec(v___x_796_);
lean_dec_ref(v_vs_792_);
lean_dec(v_mvarId_755_);
lean_dec(v_fvarId_754_);
if (v_isShared_795_ == 0)
{
lean_ctor_set_tag(v___x_794_, 0);
lean_ctor_set(v___x_794_, 0, v___x_798_);
v___x_801_ = v___x_794_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v___x_798_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
else
{
size_t v___x_803_; size_t v___x_804_; lean_object* v___x_805_; 
lean_del_object(v___x_794_);
v___x_803_ = lean_usize_of_nat(v___x_796_);
lean_dec(v___x_796_);
v___x_804_ = lean_usize_of_nat(v___x_797_);
v___x_805_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_754_, v_mvarId_755_, v_vs_792_, v___x_803_, v___x_804_, v___x_798_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
lean_dec_ref(v_vs_792_);
return v___x_805_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___boxed(lean_object* v_fvarId_807_, lean_object* v_mvarId_808_, lean_object* v_x_809_, lean_object* v_x_810_, lean_object* v_x_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
size_t v_x_8555__boxed_817_; size_t v_x_8556__boxed_818_; lean_object* v_res_819_; 
v_x_8555__boxed_817_ = lean_unbox_usize(v_x_810_);
lean_dec(v_x_810_);
v_x_8556__boxed_818_ = lean_unbox_usize(v_x_811_);
lean_dec(v_x_811_);
v_res_819_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4(v_fvarId_807_, v_mvarId_808_, v_x_809_, v_x_8555__boxed_817_, v_x_8556__boxed_818_, v___y_812_, v___y_813_, v___y_814_, v___y_815_);
lean_dec(v___y_815_);
lean_dec_ref(v___y_814_);
lean_dec(v___y_813_);
lean_dec_ref(v___y_812_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1(lean_object* v_fvarId_820_, lean_object* v_mvarId_821_, lean_object* v_t_822_, lean_object* v_start_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
lean_object* v___x_829_; uint8_t v___x_830_; 
v___x_829_ = lean_unsigned_to_nat(0u);
v___x_830_ = lean_nat_dec_eq(v_start_823_, v___x_829_);
if (v___x_830_ == 0)
{
lean_object* v_root_831_; lean_object* v_tail_832_; size_t v_shift_833_; lean_object* v_tailOff_834_; uint8_t v___x_835_; 
v_root_831_ = lean_ctor_get(v_t_822_, 0);
lean_inc_ref(v_root_831_);
v_tail_832_ = lean_ctor_get(v_t_822_, 1);
lean_inc_ref(v_tail_832_);
v_shift_833_ = lean_ctor_get_usize(v_t_822_, 4);
v_tailOff_834_ = lean_ctor_get(v_t_822_, 3);
lean_inc(v_tailOff_834_);
lean_dec_ref(v_t_822_);
v___x_835_ = lean_nat_dec_le(v_tailOff_834_, v_start_823_);
if (v___x_835_ == 0)
{
size_t v___x_836_; lean_object* v___x_837_; 
lean_dec(v_tailOff_834_);
v___x_836_ = lean_usize_of_nat(v_start_823_);
lean_inc(v_mvarId_821_);
lean_inc(v_fvarId_820_);
v___x_837_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4(v_fvarId_820_, v_mvarId_821_, v_root_831_, v___x_836_, v_shift_833_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_850_; 
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_850_ == 0)
{
lean_object* v_unused_851_; 
v_unused_851_ = lean_ctor_get(v___x_837_, 0);
lean_dec(v_unused_851_);
v___x_839_ = v___x_837_;
v_isShared_840_ = v_isSharedCheck_850_;
goto v_resetjp_838_;
}
else
{
lean_dec(v___x_837_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_850_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_841_; lean_object* v___x_842_; uint8_t v___x_843_; 
v___x_841_ = lean_array_get_size(v_tail_832_);
v___x_842_ = lean_box(0);
v___x_843_ = lean_nat_dec_lt(v___x_829_, v___x_841_);
if (v___x_843_ == 0)
{
lean_object* v___x_845_; 
lean_dec_ref(v_tail_832_);
lean_dec(v_mvarId_821_);
lean_dec(v_fvarId_820_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 0, v___x_842_);
v___x_845_ = v___x_839_;
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
size_t v___x_847_; size_t v___x_848_; lean_object* v___x_849_; 
lean_del_object(v___x_839_);
v___x_847_ = ((size_t)0ULL);
v___x_848_ = lean_usize_of_nat(v___x_841_);
v___x_849_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_820_, v_mvarId_821_, v_tail_832_, v___x_847_, v___x_848_, v___x_842_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
lean_dec_ref(v_tail_832_);
return v___x_849_;
}
}
}
else
{
lean_dec_ref(v_tail_832_);
lean_dec(v_mvarId_821_);
lean_dec(v_fvarId_820_);
return v___x_837_;
}
}
else
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; uint8_t v___x_855_; 
lean_dec_ref(v_root_831_);
v___x_852_ = lean_nat_sub(v_start_823_, v_tailOff_834_);
lean_dec(v_tailOff_834_);
v___x_853_ = lean_array_get_size(v_tail_832_);
v___x_854_ = lean_box(0);
v___x_855_ = lean_nat_dec_lt(v___x_852_, v___x_853_);
if (v___x_855_ == 0)
{
lean_object* v___x_856_; 
lean_dec(v___x_852_);
lean_dec_ref(v_tail_832_);
lean_dec(v_mvarId_821_);
lean_dec(v_fvarId_820_);
v___x_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_856_, 0, v___x_854_);
return v___x_856_;
}
else
{
size_t v___x_857_; size_t v___x_858_; lean_object* v___x_859_; 
v___x_857_ = lean_usize_of_nat(v___x_852_);
lean_dec(v___x_852_);
v___x_858_ = lean_usize_of_nat(v___x_853_);
v___x_859_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_820_, v_mvarId_821_, v_tail_832_, v___x_857_, v___x_858_, v___x_854_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
lean_dec_ref(v_tail_832_);
return v___x_859_;
}
}
}
else
{
lean_object* v___x_860_; 
v___x_860_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6(v_fvarId_820_, v_mvarId_821_, v_t_822_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
return v___x_860_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1___boxed(lean_object* v_fvarId_861_, lean_object* v_mvarId_862_, lean_object* v_t_863_, lean_object* v_start_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1(v_fvarId_861_, v_mvarId_862_, v_t_863_, v_start_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
lean_dec(v_start_864_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1(lean_object* v_fvarId_871_, lean_object* v_mvarId_872_, lean_object* v_lctx_873_, lean_object* v_start_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
lean_object* v_decls_880_; lean_object* v___x_881_; 
v_decls_880_ = lean_ctor_get(v_lctx_873_, 1);
lean_inc_ref(v_decls_880_);
lean_dec_ref(v_lctx_873_);
v___x_881_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1(v_fvarId_871_, v_mvarId_872_, v_decls_880_, v_start_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1___boxed(lean_object* v_fvarId_882_, lean_object* v_mvarId_883_, lean_object* v_lctx_884_, lean_object* v_start_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1(v_fvarId_882_, v_mvarId_883_, v_lctx_884_, v_start_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v_start_885_);
return v_res_891_;
}
}
static lean_object* _init_l_Lean_MVarId_clear___lam__1___closed__1(void){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_893_ = ((lean_object*)(l_Lean_MVarId_clear___lam__1___closed__0));
v___x_894_ = l_Lean_stringToMessageData(v___x_893_);
return v___x_894_;
}
}
static lean_object* _init_l_Lean_MVarId_clear___lam__1___closed__3(void){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_896_ = ((lean_object*)(l_Lean_MVarId_clear___lam__1___closed__2));
v___x_897_ = l_Lean_stringToMessageData(v___x_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clear___lam__1(lean_object* v_mvarId_898_, lean_object* v___x_899_, lean_object* v_fvarId_900_, lean_object* v___f_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v___y_908_; lean_object* v___y_909_; lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v___y_912_; lean_object* v___y_913_; lean_object* v___y_914_; lean_object* v___y_915_; lean_object* v___y_916_; lean_object* v___x_938_; 
lean_inc(v___x_899_);
lean_inc(v_mvarId_898_);
v___x_938_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_898_, v___x_899_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v_lctx_939_; lean_object* v___y_941_; lean_object* v___y_942_; lean_object* v___y_943_; lean_object* v___y_944_; lean_object* v___y_945_; lean_object* v___y_946_; lean_object* v___y_947_; lean_object* v___y_954_; lean_object* v___y_955_; lean_object* v___y_956_; lean_object* v___y_957_; uint8_t v___x_1014_; 
lean_dec_ref_known(v___x_938_, 1);
v_lctx_939_ = lean_ctor_get(v___y_902_, 2);
lean_inc_ref(v_lctx_939_);
v___x_1014_ = l_Lean_LocalContext_contains(v_lctx_939_, v_fvarId_900_);
if (v___x_1014_ == 0)
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1015_ = lean_obj_once(&l_Lean_MVarId_clear___lam__1___closed__3, &l_Lean_MVarId_clear___lam__1___closed__3_once, _init_l_Lean_MVarId_clear___lam__1___closed__3);
lean_inc(v_fvarId_900_);
v___x_1016_ = l_Lean_mkFVar(v_fvarId_900_);
v___x_1017_ = l_Lean_MessageData_ofExpr(v___x_1016_);
v___x_1018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1015_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
v___x_1019_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7);
v___x_1020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1018_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v___x_1021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1020_);
lean_inc(v_mvarId_898_);
lean_inc(v___x_899_);
v___x_1022_ = l_Lean_Meta_throwTacticEx___redArg(v___x_899_, v_mvarId_898_, v___x_1021_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_dec_ref_known(v___x_1022_, 1);
v___y_954_ = v___y_902_;
v___y_955_ = v___y_903_;
v___y_956_ = v___y_904_;
v___y_957_ = v___y_905_;
goto v___jp_953_;
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
lean_dec_ref(v_lctx_939_);
lean_dec_ref(v___y_902_);
lean_dec_ref(v___f_901_);
lean_dec(v_fvarId_900_);
lean_dec(v___x_899_);
lean_dec(v_mvarId_898_);
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_1022_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1022_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1023_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
else
{
v___y_954_ = v___y_902_;
v___y_955_ = v___y_903_;
v___y_956_ = v___y_904_;
v___y_957_ = v___y_905_;
goto v___jp_953_;
}
v___jp_940_:
{
lean_object* v_localInstances_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v_localInstances_948_ = lean_ctor_get(v___y_944_, 3);
v___x_949_ = l_Lean_LocalContext_erase(v_lctx_939_, v_fvarId_900_);
lean_dec(v_fvarId_900_);
lean_inc(v___y_943_);
v___x_950_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_901_, v_localInstances_948_, v___y_943_);
if (lean_obj_tag(v___x_950_) == 0)
{
lean_inc_ref(v_localInstances_948_);
v___y_908_ = v___y_941_;
v___y_909_ = v___y_942_;
v___y_910_ = v___y_947_;
v___y_911_ = v___y_945_;
v___y_912_ = v___y_944_;
v___y_913_ = v___x_949_;
v___y_914_ = v___y_946_;
v___y_915_ = v___y_943_;
v___y_916_ = v_localInstances_948_;
goto v___jp_907_;
}
else
{
lean_object* v_val_951_; lean_object* v___x_952_; 
v_val_951_ = lean_ctor_get(v___x_950_, 0);
lean_inc(v_val_951_);
lean_dec_ref_known(v___x_950_, 1);
lean_inc_ref(v_localInstances_948_);
v___x_952_ = l_Array_eraseIdx___redArg(v_localInstances_948_, v_val_951_);
v___y_908_ = v___y_941_;
v___y_909_ = v___y_942_;
v___y_910_ = v___y_947_;
v___y_911_ = v___y_945_;
v___y_912_ = v___y_944_;
v___y_913_ = v___x_949_;
v___y_914_ = v___y_946_;
v___y_915_ = v___y_943_;
v___y_916_ = v___x_952_;
goto v___jp_907_;
}
}
v___jp_953_:
{
lean_object* v___x_958_; 
lean_inc(v_mvarId_898_);
v___x_958_ = l_Lean_MVarId_getTag(v_mvarId_898_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v_a_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v_a_959_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_a_959_);
lean_dec_ref_known(v___x_958_, 1);
v___x_960_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_lctx_939_);
lean_inc(v_mvarId_898_);
lean_inc(v_fvarId_900_);
v___x_961_ = l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1(v_fvarId_900_, v_mvarId_898_, v_lctx_939_, v___x_960_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v___x_962_; 
lean_dec_ref_known(v___x_961_, 1);
lean_inc(v_mvarId_898_);
v___x_962_ = l_Lean_MVarId_getDecl(v_mvarId_898_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v_a_963_; lean_object* v_type_964_; lean_object* v___x_965_; lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_989_; 
v_a_963_ = lean_ctor_get(v___x_962_, 0);
lean_inc(v_a_963_);
lean_dec_ref_known(v___x_962_, 1);
v_type_964_ = lean_ctor_get(v_a_963_, 2);
lean_inc_ref_n(v_type_964_, 2);
lean_dec(v_a_963_);
lean_inc(v_fvarId_900_);
v___x_965_ = l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3___redArg(v_type_964_, v_fvarId_900_, v___y_955_);
v_a_966_ = lean_ctor_get(v___x_965_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_989_ == 0)
{
v___x_968_ = v___x_965_;
v_isShared_969_ = v_isSharedCheck_989_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_965_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_989_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
uint8_t v___x_970_; 
v___x_970_ = lean_unbox(v_a_966_);
lean_dec(v_a_966_);
if (v___x_970_ == 0)
{
lean_del_object(v___x_968_);
lean_dec(v___x_899_);
v___y_941_ = v_a_959_;
v___y_942_ = v_type_964_;
v___y_943_ = v___x_960_;
v___y_944_ = v___y_954_;
v___y_945_ = v___y_955_;
v___y_946_ = v___y_956_;
v___y_947_ = v___y_957_;
goto v___jp_940_;
}
else
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_978_; 
v___x_971_ = lean_obj_once(&l_Lean_MVarId_clear___lam__1___closed__1, &l_Lean_MVarId_clear___lam__1___closed__1_once, _init_l_Lean_MVarId_clear___lam__1___closed__1);
lean_inc(v_fvarId_900_);
v___x_972_ = l_Lean_mkFVar(v_fvarId_900_);
v___x_973_ = l_Lean_MessageData_ofExpr(v___x_972_);
v___x_974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_971_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7);
v___x_976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_974_);
lean_ctor_set(v___x_976_, 1, v___x_975_);
if (v_isShared_969_ == 0)
{
lean_ctor_set_tag(v___x_968_, 1);
lean_ctor_set(v___x_968_, 0, v___x_976_);
v___x_978_ = v___x_968_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v___x_976_);
v___x_978_ = v_reuseFailAlloc_988_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
lean_object* v___x_979_; 
lean_inc(v_mvarId_898_);
v___x_979_ = l_Lean_Meta_throwTacticEx___redArg(v___x_899_, v_mvarId_898_, v___x_978_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_dec_ref_known(v___x_979_, 1);
v___y_941_ = v_a_959_;
v___y_942_ = v_type_964_;
v___y_943_ = v___x_960_;
v___y_944_ = v___y_954_;
v___y_945_ = v___y_955_;
v___y_946_ = v___y_956_;
v___y_947_ = v___y_957_;
goto v___jp_940_;
}
else
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_987_; 
lean_dec_ref(v_type_964_);
lean_dec(v_a_959_);
lean_dec_ref(v___y_954_);
lean_dec_ref(v_lctx_939_);
lean_dec_ref(v___f_901_);
lean_dec(v_fvarId_900_);
lean_dec(v_mvarId_898_);
v_a_980_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_987_ == 0)
{
v___x_982_ = v___x_979_;
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_979_);
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
}
else
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_997_; 
lean_dec(v_a_959_);
lean_dec_ref(v___y_954_);
lean_dec_ref(v_lctx_939_);
lean_dec_ref(v___f_901_);
lean_dec(v_fvarId_900_);
lean_dec(v___x_899_);
lean_dec(v_mvarId_898_);
v_a_990_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_997_ == 0)
{
v___x_992_ = v___x_962_;
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_962_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_995_; 
if (v_isShared_993_ == 0)
{
v___x_995_ = v___x_992_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_a_990_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
}
else
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1005_; 
lean_dec(v_a_959_);
lean_dec_ref(v___y_954_);
lean_dec_ref(v_lctx_939_);
lean_dec_ref(v___f_901_);
lean_dec(v_fvarId_900_);
lean_dec(v___x_899_);
lean_dec(v_mvarId_898_);
v_a_998_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_1000_ = v___x_961_;
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_961_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1003_; 
if (v_isShared_1001_ == 0)
{
v___x_1003_ = v___x_1000_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_a_998_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
}
else
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1013_; 
lean_dec_ref(v___y_954_);
lean_dec_ref(v_lctx_939_);
lean_dec_ref(v___f_901_);
lean_dec(v_fvarId_900_);
lean_dec(v___x_899_);
lean_dec(v_mvarId_898_);
v_a_1006_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1008_ = v___x_958_;
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_958_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1011_; 
if (v_isShared_1009_ == 0)
{
v___x_1011_ = v___x_1008_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_a_1006_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
}
}
else
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1038_; 
lean_dec_ref(v___y_902_);
lean_dec_ref(v___f_901_);
lean_dec(v_fvarId_900_);
lean_dec(v___x_899_);
lean_dec(v_mvarId_898_);
v_a_1031_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1033_ = v___x_938_;
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_938_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1036_; 
if (v_isShared_1034_ == 0)
{
v___x_1036_ = v___x_1033_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1031_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
v___jp_907_:
{
uint8_t v___x_917_; lean_object* v___x_918_; 
v___x_917_ = 2;
v___x_918_ = l_Lean_Meta_mkFreshExprMVarAt(v___y_913_, v___y_916_, v___y_909_, v___x_917_, v___y_908_, v___y_915_, v___y_912_, v___y_911_, v___y_914_, v___y_910_);
lean_dec_ref(v___y_912_);
if (lean_obj_tag(v___x_918_) == 0)
{
lean_object* v_a_919_; lean_object* v___x_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_928_; 
v_a_919_ = lean_ctor_get(v___x_918_, 0);
lean_inc_n(v_a_919_, 2);
lean_dec_ref_known(v___x_918_, 1);
v___x_920_ = l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg(v_mvarId_898_, v_a_919_, v___y_911_);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_928_ == 0)
{
lean_object* v_unused_929_; 
v_unused_929_ = lean_ctor_get(v___x_920_, 0);
lean_dec(v_unused_929_);
v___x_922_ = v___x_920_;
v_isShared_923_ = v_isSharedCheck_928_;
goto v_resetjp_921_;
}
else
{
lean_dec(v___x_920_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_928_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_924_; lean_object* v___x_926_; 
v___x_924_ = l_Lean_Expr_mvarId_x21(v_a_919_);
lean_dec(v_a_919_);
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 0, v___x_924_);
v___x_926_ = v___x_922_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v___x_924_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
else
{
lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_937_; 
lean_dec(v_mvarId_898_);
v_a_930_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_937_ == 0)
{
v___x_932_ = v___x_918_;
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v___x_918_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_935_; 
if (v_isShared_933_ == 0)
{
v___x_935_ = v___x_932_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_a_930_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clear___lam__1___boxed(lean_object* v_mvarId_1039_, lean_object* v___x_1040_, lean_object* v_fvarId_1041_, lean_object* v___f_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Lean_MVarId_clear___lam__1(v_mvarId_1039_, v___x_1040_, v_fvarId_1041_, v___f_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
lean_dec(v___y_1044_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clear(lean_object* v_mvarId_1049_, lean_object* v_fvarId_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_){
_start:
{
lean_object* v___f_1056_; lean_object* v___x_1057_; lean_object* v___f_1058_; lean_object* v___x_1059_; 
lean_inc(v_fvarId_1050_);
v___f_1056_ = lean_alloc_closure((void*)(l_Lean_MVarId_clear___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1056_, 0, v_fvarId_1050_);
v___x_1057_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__1));
lean_inc(v_mvarId_1049_);
v___f_1058_ = lean_alloc_closure((void*)(l_Lean_MVarId_clear___lam__1___boxed), 9, 4);
lean_closure_set(v___f_1058_, 0, v_mvarId_1049_);
lean_closure_set(v___f_1058_, 1, v___x_1057_);
lean_closure_set(v___f_1058_, 2, v_fvarId_1050_);
lean_closure_set(v___f_1058_, 3, v___f_1056_);
v___x_1059_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg(v_mvarId_1049_, v___f_1058_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clear___boxed(lean_object* v_mvarId_1060_, lean_object* v_fvarId_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Lean_MVarId_clear(v_mvarId_1060_, v_fvarId_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_);
lean_dec(v_a_1065_);
lean_dec_ref(v_a_1064_);
lean_dec(v_a_1063_);
lean_dec_ref(v_a_1062_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2(lean_object* v_mvarId_1068_, lean_object* v_val_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v___x_1075_; 
v___x_1075_ = l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg(v_mvarId_1068_, v_val_1069_, v___y_1071_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___boxed(lean_object* v_mvarId_1076_, lean_object* v_val_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2(v_mvarId_1076_, v_val_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3(lean_object* v_00_u03b2_1084_, lean_object* v_x_1085_, lean_object* v_x_1086_, lean_object* v_x_1087_){
_start:
{
lean_object* v___x_1088_; 
v___x_1088_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3___redArg(v_x_1085_, v_x_1086_, v_x_1087_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9(lean_object* v_00_u03b2_1089_, lean_object* v_x_1090_, size_t v_x_1091_, size_t v_x_1092_, lean_object* v_x_1093_, lean_object* v_x_1094_){
_start:
{
lean_object* v___x_1095_; 
v___x_1095_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_x_1090_, v_x_1091_, v_x_1092_, v_x_1093_, v_x_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___boxed(lean_object* v_00_u03b2_1096_, lean_object* v_x_1097_, lean_object* v_x_1098_, lean_object* v_x_1099_, lean_object* v_x_1100_, lean_object* v_x_1101_){
_start:
{
size_t v_x_9105__boxed_1102_; size_t v_x_9106__boxed_1103_; lean_object* v_res_1104_; 
v_x_9105__boxed_1102_ = lean_unbox_usize(v_x_1098_);
lean_dec(v_x_1098_);
v_x_9106__boxed_1103_ = lean_unbox_usize(v_x_1099_);
lean_dec(v_x_1099_);
v_res_1104_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9(v_00_u03b2_1096_, v_x_1097_, v_x_9105__boxed_1102_, v_x_9106__boxed_1103_, v_x_1100_, v_x_1101_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13(lean_object* v_00_u03b2_1105_, lean_object* v_n_1106_, lean_object* v_k_1107_, lean_object* v_v_1108_){
_start:
{
lean_object* v___x_1109_; 
v___x_1109_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13___redArg(v_n_1106_, v_k_1107_, v_v_1108_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14(lean_object* v_00_u03b2_1110_, size_t v_depth_1111_, lean_object* v_keys_1112_, lean_object* v_vals_1113_, lean_object* v_heq_1114_, lean_object* v_i_1115_, lean_object* v_entries_1116_){
_start:
{
lean_object* v___x_1117_; 
v___x_1117_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg(v_depth_1111_, v_keys_1112_, v_vals_1113_, v_i_1115_, v_entries_1116_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___boxed(lean_object* v_00_u03b2_1118_, lean_object* v_depth_1119_, lean_object* v_keys_1120_, lean_object* v_vals_1121_, lean_object* v_heq_1122_, lean_object* v_i_1123_, lean_object* v_entries_1124_){
_start:
{
size_t v_depth_boxed_1125_; lean_object* v_res_1126_; 
v_depth_boxed_1125_ = lean_unbox_usize(v_depth_1119_);
lean_dec(v_depth_1119_);
v_res_1126_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14(v_00_u03b2_1118_, v_depth_boxed_1125_, v_keys_1120_, v_vals_1121_, v_heq_1122_, v_i_1123_, v_entries_1124_);
lean_dec_ref(v_vals_1121_);
lean_dec_ref(v_keys_1120_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13_spec__14(lean_object* v_00_u03b2_1127_, lean_object* v_x_1128_, lean_object* v_x_1129_, lean_object* v_x_1130_, lean_object* v_x_1131_){
_start:
{
lean_object* v___x_1132_; 
v___x_1132_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13_spec__14___redArg(v_x_1128_, v_x_1129_, v_x_1130_, v_x_1131_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClear(lean_object* v_mvarId_1133_, lean_object* v_fvarId_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_){
_start:
{
lean_object* v___x_1140_; 
v___x_1140_ = l_Lean_Meta_saveState___redArg(v_a_1136_, v_a_1138_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v_a_1141_; lean_object* v___x_1142_; 
v_a_1141_ = lean_ctor_get(v___x_1140_, 0);
lean_inc(v_a_1141_);
lean_dec_ref_known(v___x_1140_, 1);
lean_inc(v_mvarId_1133_);
v___x_1142_ = l_Lean_MVarId_clear(v_mvarId_1133_, v_fvarId_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_dec(v_a_1141_);
lean_dec(v_mvarId_1133_);
return v___x_1142_;
}
else
{
lean_object* v_a_1143_; uint8_t v___x_1144_; 
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
v___x_1144_ = l_Lean_Exception_isInterrupt(v_a_1143_);
if (v___x_1144_ == 0)
{
uint8_t v___x_1145_; 
lean_inc(v_a_1143_);
v___x_1145_ = l_Lean_Exception_isRuntime(v_a_1143_);
if (v___x_1145_ == 0)
{
lean_object* v___x_1146_; 
lean_dec_ref_known(v___x_1142_, 1);
v___x_1146_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1141_, v_a_1136_, v_a_1138_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1153_; 
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1153_ == 0)
{
lean_object* v_unused_1154_; 
v_unused_1154_ = lean_ctor_get(v___x_1146_, 0);
lean_dec(v_unused_1154_);
v___x_1148_ = v___x_1146_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_dec(v___x_1146_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v_mvarId_1133_);
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_mvarId_1133_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
else
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1162_; 
lean_dec(v_mvarId_1133_);
v_a_1155_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1157_ = v___x_1146_;
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1146_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1160_; 
if (v_isShared_1158_ == 0)
{
v___x_1160_ = v___x_1157_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_a_1155_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
}
else
{
lean_dec(v_a_1141_);
lean_dec(v_mvarId_1133_);
return v___x_1142_;
}
}
else
{
lean_dec(v_a_1141_);
lean_dec(v_mvarId_1133_);
return v___x_1142_;
}
}
}
else
{
lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1170_; 
lean_dec(v_fvarId_1134_);
lean_dec(v_mvarId_1133_);
v_a_1163_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1165_ = v___x_1140_;
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v___x_1140_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1168_; 
if (v_isShared_1166_ == 0)
{
v___x_1168_ = v___x_1165_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_a_1163_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClear___boxed(lean_object* v_mvarId_1171_, lean_object* v_fvarId_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l_Lean_MVarId_tryClear(v_mvarId_1171_, v_fvarId_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
lean_dec(v_a_1176_);
lean_dec_ref(v_a_1175_);
lean_dec(v_a_1174_);
lean_dec_ref(v_a_1173_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0(lean_object* v_as_1179_, size_t v_i_1180_, size_t v_stop_1181_, lean_object* v_b_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_){
_start:
{
uint8_t v___x_1188_; 
v___x_1188_ = lean_usize_dec_eq(v_i_1180_, v_stop_1181_);
if (v___x_1188_ == 0)
{
size_t v___x_1189_; size_t v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1189_ = ((size_t)1ULL);
v___x_1190_ = lean_usize_sub(v_i_1180_, v___x_1189_);
v___x_1191_ = lean_array_uget_borrowed(v_as_1179_, v___x_1190_);
lean_inc(v___x_1191_);
v___x_1192_ = l_Lean_MVarId_tryClear(v_b_1182_, v___x_1191_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_object* v_a_1193_; 
v_a_1193_ = lean_ctor_get(v___x_1192_, 0);
lean_inc(v_a_1193_);
lean_dec_ref_known(v___x_1192_, 1);
v_i_1180_ = v___x_1190_;
v_b_1182_ = v_a_1193_;
goto _start;
}
else
{
return v___x_1192_;
}
}
else
{
lean_object* v___x_1195_; 
v___x_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1195_, 0, v_b_1182_);
return v___x_1195_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0___boxed(lean_object* v_as_1196_, lean_object* v_i_1197_, lean_object* v_stop_1198_, lean_object* v_b_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_){
_start:
{
size_t v_i_boxed_1205_; size_t v_stop_boxed_1206_; lean_object* v_res_1207_; 
v_i_boxed_1205_ = lean_unbox_usize(v_i_1197_);
lean_dec(v_i_1197_);
v_stop_boxed_1206_ = lean_unbox_usize(v_stop_1198_);
lean_dec(v_stop_1198_);
v_res_1207_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0(v_as_1196_, v_i_boxed_1205_, v_stop_boxed_1206_, v_b_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec_ref(v_as_1196_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany(lean_object* v_mvarId_1208_, lean_object* v_fvarIds_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; uint8_t v___x_1217_; 
v___x_1215_ = lean_array_get_size(v_fvarIds_1209_);
v___x_1216_ = lean_unsigned_to_nat(0u);
v___x_1217_ = lean_nat_dec_lt(v___x_1216_, v___x_1215_);
if (v___x_1217_ == 0)
{
lean_object* v___x_1218_; 
v___x_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1218_, 0, v_mvarId_1208_);
return v___x_1218_;
}
else
{
size_t v___x_1219_; size_t v___x_1220_; lean_object* v___x_1221_; 
v___x_1219_ = lean_usize_of_nat(v___x_1215_);
v___x_1220_ = ((size_t)0ULL);
v___x_1221_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0(v_fvarIds_1209_, v___x_1219_, v___x_1220_, v_mvarId_1208_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
return v___x_1221_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany___boxed(lean_object* v_mvarId_1222_, lean_object* v_fvarIds_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l_Lean_MVarId_tryClearMany(v_mvarId_1222_, v_fvarIds_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
lean_dec(v_a_1225_);
lean_dec_ref(v_a_1224_);
lean_dec_ref(v_fvarIds_1223_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0(lean_object* v_as_1230_, size_t v_i_1231_, size_t v_stop_1232_, lean_object* v_b_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
uint8_t v___x_1239_; 
v___x_1239_ = lean_usize_dec_eq(v_i_1231_, v_stop_1232_);
if (v___x_1239_ == 0)
{
lean_object* v_fst_1240_; lean_object* v_snd_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1266_; 
v_fst_1240_ = lean_ctor_get(v_b_1233_, 0);
v_snd_1241_ = lean_ctor_get(v_b_1233_, 1);
v_isSharedCheck_1266_ = !lean_is_exclusive(v_b_1233_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1243_ = v_b_1233_;
v_isShared_1244_ = v_isSharedCheck_1266_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_snd_1241_);
lean_inc(v_fst_1240_);
lean_dec(v_b_1233_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1266_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
size_t v___x_1245_; size_t v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1245_ = ((size_t)1ULL);
v___x_1246_ = lean_usize_sub(v_i_1231_, v___x_1245_);
v___x_1247_ = lean_array_uget_borrowed(v_as_1230_, v___x_1246_);
lean_inc(v___x_1247_);
lean_inc(v_fst_1240_);
v___x_1248_ = l_Lean_MVarId_tryClear(v_fst_1240_, v___x_1247_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v_a_1249_; lean_object* v___y_1251_; uint8_t v___x_1256_; 
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
lean_inc(v_a_1249_);
lean_dec_ref_known(v___x_1248_, 1);
v___x_1256_ = l_Lean_instBEqMVarId_beq(v_fst_1240_, v_a_1249_);
lean_dec(v_fst_1240_);
if (v___x_1256_ == 0)
{
lean_object* v___x_1257_; 
lean_inc(v___x_1247_);
v___x_1257_ = lean_array_push(v_snd_1241_, v___x_1247_);
v___y_1251_ = v___x_1257_;
goto v___jp_1250_;
}
else
{
v___y_1251_ = v_snd_1241_;
goto v___jp_1250_;
}
v___jp_1250_:
{
lean_object* v___x_1253_; 
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 1, v___y_1251_);
lean_ctor_set(v___x_1243_, 0, v_a_1249_);
v___x_1253_ = v___x_1243_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_a_1249_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v___y_1251_);
v___x_1253_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
v_i_1231_ = v___x_1246_;
v_b_1233_ = v___x_1253_;
goto _start;
}
}
}
else
{
lean_object* v_a_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1265_; 
lean_del_object(v___x_1243_);
lean_dec(v_snd_1241_);
lean_dec(v_fst_1240_);
v_a_1258_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1260_ = v___x_1248_;
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_a_1258_);
lean_dec(v___x_1248_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1263_; 
if (v_isShared_1261_ == 0)
{
v___x_1263_ = v___x_1260_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_a_1258_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
}
}
else
{
lean_object* v___x_1267_; 
v___x_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1267_, 0, v_b_1233_);
return v___x_1267_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0___boxed(lean_object* v_as_1268_, lean_object* v_i_1269_, lean_object* v_stop_1270_, lean_object* v_b_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
size_t v_i_boxed_1277_; size_t v_stop_boxed_1278_; lean_object* v_res_1279_; 
v_i_boxed_1277_ = lean_unbox_usize(v_i_1269_);
lean_dec(v_i_1269_);
v_stop_boxed_1278_ = lean_unbox_usize(v_stop_1270_);
lean_dec(v_stop_1270_);
v_res_1279_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0(v_as_1268_, v_i_boxed_1277_, v_stop_boxed_1278_, v_b_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec_ref(v_as_1268_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany_x27___lam__0(lean_object* v_fvarIds_1280_, lean_object* v_goal_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_){
_start:
{
lean_object* v_lctx_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; uint8_t v___x_1293_; 
v_lctx_1287_ = lean_ctor_get(v___y_1282_, 2);
v___x_1288_ = l_Lean_LocalContext_sortFVarsByContextOrder(v_lctx_1287_, v_fvarIds_1280_);
v___x_1289_ = lean_array_get_size(v___x_1288_);
v___x_1290_ = lean_mk_empty_array_with_capacity(v___x_1289_);
v___x_1291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1291_, 0, v_goal_1281_);
lean_ctor_set(v___x_1291_, 1, v___x_1290_);
v___x_1292_ = lean_unsigned_to_nat(0u);
v___x_1293_ = lean_nat_dec_lt(v___x_1292_, v___x_1289_);
if (v___x_1293_ == 0)
{
lean_object* v___x_1294_; 
lean_dec_ref(v___x_1288_);
v___x_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1291_);
return v___x_1294_;
}
else
{
size_t v___x_1295_; size_t v___x_1296_; lean_object* v___x_1297_; 
v___x_1295_ = lean_usize_of_nat(v___x_1289_);
v___x_1296_ = ((size_t)0ULL);
v___x_1297_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0(v___x_1288_, v___x_1295_, v___x_1296_, v___x_1291_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
lean_dec_ref(v___x_1288_);
return v___x_1297_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany_x27___lam__0___boxed(lean_object* v_fvarIds_1298_, lean_object* v_goal_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l_Lean_MVarId_tryClearMany_x27___lam__0(v_fvarIds_1298_, v_goal_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany_x27(lean_object* v_goal_1306_, lean_object* v_fvarIds_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_){
_start:
{
lean_object* v___f_1313_; lean_object* v___x_1314_; 
lean_inc(v_goal_1306_);
v___f_1313_ = lean_alloc_closure((void*)(l_Lean_MVarId_tryClearMany_x27___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1313_, 0, v_fvarIds_1307_);
lean_closure_set(v___f_1313_, 1, v_goal_1306_);
v___x_1314_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg(v_goal_1306_, v___f_1313_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany_x27___boxed(lean_object* v_goal_1315_, lean_object* v_fvarIds_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_){
_start:
{
lean_object* v_res_1322_; 
v_res_1322_ = l_Lean_MVarId_tryClearMany_x27(v_goal_1315_, v_fvarIds_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_);
lean_dec(v_a_1320_);
lean_dec_ref(v_a_1319_);
lean_dec(v_a_1318_);
lean_dec_ref(v_a_1317_);
return v_res_1322_;
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
