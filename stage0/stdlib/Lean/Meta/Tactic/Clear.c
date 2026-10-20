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
size_t v_x_7916__boxed_428_; size_t v_x_7917__boxed_429_; lean_object* v_res_430_; 
v_x_7916__boxed_428_ = lean_unbox_usize(v_x_424_);
lean_dec(v_x_424_);
v_x_7917__boxed_429_ = lean_unbox_usize(v_x_425_);
lean_dec(v_x_425_);
v_res_430_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_x_423_, v_x_7916__boxed_428_, v_x_7917__boxed_429_, v_x_426_, v_x_427_);
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
lean_object* v___x_442_; lean_object* v_mctx_443_; lean_object* v_cache_444_; lean_object* v_zetaDeltaFVarIds_445_; lean_object* v_postponed_446_; lean_object* v_diag_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_477_; 
v___x_442_ = lean_st_ref_take(v___y_440_);
v_mctx_443_ = lean_ctor_get(v___x_442_, 0);
v_cache_444_ = lean_ctor_get(v___x_442_, 1);
v_zetaDeltaFVarIds_445_ = lean_ctor_get(v___x_442_, 2);
v_postponed_446_ = lean_ctor_get(v___x_442_, 3);
v_diag_447_ = lean_ctor_get(v___x_442_, 4);
v_isSharedCheck_477_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_477_ == 0)
{
v___x_449_ = v___x_442_;
v_isShared_450_ = v_isSharedCheck_477_;
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
v_isShared_450_ = v_isSharedCheck_477_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v_depth_451_; lean_object* v_levelAssignDepth_452_; lean_object* v_lmvarCounter_453_; lean_object* v_mvarCounter_454_; lean_object* v_lDecls_455_; lean_object* v_decls_456_; lean_object* v_userNames_457_; lean_object* v_lAssignment_458_; lean_object* v_eAssignment_459_; lean_object* v_dAssignment_460_; lean_object* v_instanceTypedMVars_461_; lean_object* v_synthNormMemo_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_476_; 
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
v_instanceTypedMVars_461_ = lean_ctor_get(v_mctx_443_, 10);
v_synthNormMemo_462_ = lean_ctor_get(v_mctx_443_, 11);
v_isSharedCheck_476_ = !lean_is_exclusive(v_mctx_443_);
if (v_isSharedCheck_476_ == 0)
{
v___x_464_ = v_mctx_443_;
v_isShared_465_ = v_isSharedCheck_476_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_synthNormMemo_462_);
lean_inc(v_instanceTypedMVars_461_);
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
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_476_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_469_; 
v___x_466_ = lean_box(0);
v___x_467_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3___redArg(v_eAssignment_459_, v_mvarId_438_, v_val_439_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 8, v___x_467_);
v___x_469_ = v___x_464_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_depth_451_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v_levelAssignDepth_452_);
lean_ctor_set(v_reuseFailAlloc_475_, 2, v_lmvarCounter_453_);
lean_ctor_set(v_reuseFailAlloc_475_, 3, v_mvarCounter_454_);
lean_ctor_set(v_reuseFailAlloc_475_, 4, v_lDecls_455_);
lean_ctor_set(v_reuseFailAlloc_475_, 5, v_decls_456_);
lean_ctor_set(v_reuseFailAlloc_475_, 6, v_userNames_457_);
lean_ctor_set(v_reuseFailAlloc_475_, 7, v_lAssignment_458_);
lean_ctor_set(v_reuseFailAlloc_475_, 8, v___x_467_);
lean_ctor_set(v_reuseFailAlloc_475_, 9, v_dAssignment_460_);
lean_ctor_set(v_reuseFailAlloc_475_, 10, v_instanceTypedMVars_461_);
lean_ctor_set(v_reuseFailAlloc_475_, 11, v_synthNormMemo_462_);
v___x_469_ = v_reuseFailAlloc_475_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
lean_object* v___x_471_; 
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 0, v___x_469_);
v___x_471_ = v___x_449_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v___x_469_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v_cache_444_);
lean_ctor_set(v_reuseFailAlloc_474_, 2, v_zetaDeltaFVarIds_445_);
lean_ctor_set(v_reuseFailAlloc_474_, 3, v_postponed_446_);
lean_ctor_set(v_reuseFailAlloc_474_, 4, v_diag_447_);
v___x_471_ = v_reuseFailAlloc_474_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = lean_st_ref_put(v___y_440_, v___x_471_);
v___x_473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_473_, 0, v___x_466_);
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
lean_object* v___x_520_; uint8_t v___x_521_; lean_object* v___x_522_; 
v___x_520_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__1));
v___x_521_ = 1;
lean_inc(v_fvarId_495_);
lean_inc(v_val_514_);
v___x_522_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg(v_val_514_, v_fvarId_495_, v___x_521_, v___y_502_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; uint8_t v___x_524_; 
v_a_523_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_a_523_);
lean_dec_ref_known(v___x_522_, 1);
v___x_524_ = lean_unbox(v_a_523_);
lean_dec(v_a_523_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; 
lean_del_object(v___x_516_);
lean_dec(v_val_514_);
v___x_525_ = lean_box(0);
v_a_507_ = v___x_525_;
goto v___jp_506_;
}
else
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_538_; 
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
v___x_539_ = l_Lean_Meta_throwTacticEx___redArg(v___x_520_, v_mvarId_496_, v___x_538_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
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
v_a_542_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_549_ == 0)
{
v___x_544_ = v___x_522_;
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v___x_522_);
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
lean_object* v___x_592_; uint8_t v___x_593_; lean_object* v___x_594_; 
v___x_592_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__1));
v___x_593_ = 1;
lean_inc(v_fvarId_567_);
lean_inc(v_val_586_);
v___x_594_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg(v_val_586_, v_fvarId_567_, v___x_593_, v___y_574_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v_a_595_; uint8_t v___x_596_; 
v_a_595_ = lean_ctor_get(v___x_594_, 0);
lean_inc(v_a_595_);
lean_dec_ref_known(v___x_594_, 1);
v___x_596_ = lean_unbox(v_a_595_);
lean_dec(v_a_595_);
if (v___x_596_ == 0)
{
lean_object* v___x_597_; 
lean_del_object(v___x_588_);
lean_dec(v_val_586_);
v___x_597_ = lean_box(0);
v_a_579_ = v___x_597_;
goto v___jp_578_;
}
else
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_610_; 
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
v___x_611_ = l_Lean_Meta_throwTacticEx___redArg(v___x_592_, v_mvarId_568_, v___x_610_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
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
v_a_614_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_621_ == 0)
{
v___x_616_ = v___x_594_;
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_a_614_);
lean_dec(v___x_594_);
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
lean_object* v_cs_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_661_; 
v_cs_647_ = lean_ctor_get(v_x_641_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v_x_641_);
if (v_isSharedCheck_661_ == 0)
{
v___x_649_ = v_x_641_;
v_isShared_650_ = v_isSharedCheck_661_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_cs_647_);
lean_dec(v_x_641_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_661_;
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
size_t v___x_658_; size_t v___x_659_; lean_object* v___x_660_; 
lean_del_object(v___x_649_);
v___x_658_ = ((size_t)0ULL);
v___x_659_ = lean_usize_of_nat(v___x_652_);
v___x_660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(v_fvarId_639_, v_mvarId_640_, v_cs_647_, v___x_658_, v___x_659_, v___x_653_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
lean_dec_ref(v_cs_647_);
return v___x_660_;
}
}
}
else
{
lean_object* v_vs_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_676_; 
v_vs_662_ = lean_ctor_get(v_x_641_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v_x_641_);
if (v_isSharedCheck_676_ == 0)
{
v___x_664_ = v_x_641_;
v_isShared_665_ = v_isSharedCheck_676_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_vs_662_);
lean_dec(v_x_641_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_676_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_666_ = lean_unsigned_to_nat(0u);
v___x_667_ = lean_array_get_size(v_vs_662_);
v___x_668_ = lean_box(0);
v___x_669_ = lean_nat_dec_lt(v___x_666_, v___x_667_);
if (v___x_669_ == 0)
{
lean_object* v___x_671_; 
lean_dec_ref(v_vs_662_);
lean_dec(v_mvarId_640_);
lean_dec(v_fvarId_639_);
if (v_isShared_665_ == 0)
{
lean_ctor_set_tag(v___x_664_, 0);
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
size_t v___x_673_; size_t v___x_674_; lean_object* v___x_675_; 
lean_del_object(v___x_664_);
v___x_673_ = ((size_t)0ULL);
v___x_674_ = lean_usize_of_nat(v___x_667_);
v___x_675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_639_, v_mvarId_640_, v_vs_662_, v___x_673_, v___x_674_, v___x_668_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
lean_dec_ref(v_vs_662_);
return v___x_675_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(lean_object* v_fvarId_677_, lean_object* v_mvarId_678_, lean_object* v_as_679_, size_t v_i_680_, size_t v_stop_681_, lean_object* v_b_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
uint8_t v___x_688_; 
v___x_688_ = lean_usize_dec_eq(v_i_680_, v_stop_681_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = lean_array_uget_borrowed(v_as_679_, v_i_680_);
lean_inc(v___x_689_);
lean_inc(v_mvarId_678_);
lean_inc(v_fvarId_677_);
v___x_690_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6(v_fvarId_677_, v_mvarId_678_, v___x_689_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_a_691_; size_t v___x_692_; size_t v___x_693_; 
v_a_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc(v_a_691_);
lean_dec_ref_known(v___x_690_, 1);
v___x_692_ = ((size_t)1ULL);
v___x_693_ = lean_usize_add(v_i_680_, v___x_692_);
v_i_680_ = v___x_693_;
v_b_682_ = v_a_691_;
goto _start;
}
else
{
lean_dec(v_mvarId_678_);
lean_dec(v_fvarId_677_);
return v___x_690_;
}
}
else
{
lean_object* v___x_695_; 
lean_dec(v_mvarId_678_);
lean_dec(v_fvarId_677_);
v___x_695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_695_, 0, v_b_682_);
return v___x_695_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7___boxed(lean_object* v_fvarId_696_, lean_object* v_mvarId_697_, lean_object* v_as_698_, lean_object* v_i_699_, lean_object* v_stop_700_, lean_object* v_b_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
size_t v_i_boxed_707_; size_t v_stop_boxed_708_; lean_object* v_res_709_; 
v_i_boxed_707_ = lean_unbox_usize(v_i_699_);
lean_dec(v_i_699_);
v_stop_boxed_708_ = lean_unbox_usize(v_stop_700_);
lean_dec(v_stop_700_);
v_res_709_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(v_fvarId_696_, v_mvarId_697_, v_as_698_, v_i_boxed_707_, v_stop_boxed_708_, v_b_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec_ref(v_as_698_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6___boxed(lean_object* v_fvarId_710_, lean_object* v_mvarId_711_, lean_object* v_x_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6(v_fvarId_710_, v_mvarId_711_, v_x_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6(lean_object* v_fvarId_719_, lean_object* v_mvarId_720_, lean_object* v_t_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v_root_727_; lean_object* v_tail_728_; lean_object* v___x_729_; 
v_root_727_ = lean_ctor_get(v_t_721_, 0);
lean_inc_ref(v_root_727_);
v_tail_728_ = lean_ctor_get(v_t_721_, 1);
lean_inc_ref(v_tail_728_);
lean_dec_ref(v_t_721_);
lean_inc(v_mvarId_720_);
lean_inc(v_fvarId_719_);
v___x_729_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6(v_fvarId_719_, v_mvarId_720_, v_root_727_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_743_; 
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_743_ == 0)
{
lean_object* v_unused_744_; 
v_unused_744_ = lean_ctor_get(v___x_729_, 0);
lean_dec(v_unused_744_);
v___x_731_ = v___x_729_;
v_isShared_732_ = v_isSharedCheck_743_;
goto v_resetjp_730_;
}
else
{
lean_dec(v___x_729_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_743_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; uint8_t v___x_736_; 
v___x_733_ = lean_unsigned_to_nat(0u);
v___x_734_ = lean_array_get_size(v_tail_728_);
v___x_735_ = lean_box(0);
v___x_736_ = lean_nat_dec_lt(v___x_733_, v___x_734_);
if (v___x_736_ == 0)
{
lean_object* v___x_738_; 
lean_dec_ref(v_tail_728_);
lean_dec(v_mvarId_720_);
lean_dec(v_fvarId_719_);
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 0, v___x_735_);
v___x_738_ = v___x_731_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v___x_735_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
else
{
size_t v___x_740_; size_t v___x_741_; lean_object* v___x_742_; 
lean_del_object(v___x_731_);
v___x_740_ = ((size_t)0ULL);
v___x_741_ = lean_usize_of_nat(v___x_734_);
v___x_742_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_719_, v_mvarId_720_, v_tail_728_, v___x_740_, v___x_741_, v___x_735_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
lean_dec_ref(v_tail_728_);
return v___x_742_;
}
}
}
else
{
lean_dec_ref(v_tail_728_);
lean_dec(v_mvarId_720_);
lean_dec(v_fvarId_719_);
return v___x_729_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6___boxed(lean_object* v_fvarId_745_, lean_object* v_mvarId_746_, lean_object* v_t_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6(v_fvarId_745_, v_mvarId_746_, v_t_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
return v_res_753_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4(lean_object* v_fvarId_755_, lean_object* v_mvarId_756_, lean_object* v_x_757_, size_t v_x_758_, size_t v_x_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
if (lean_obj_tag(v_x_757_) == 0)
{
lean_object* v_cs_765_; lean_object* v___x_766_; size_t v___x_767_; lean_object* v_j_768_; lean_object* v___x_769_; size_t v___x_770_; size_t v___x_771_; size_t v___x_772_; size_t v___x_773_; size_t v___x_774_; size_t v___x_775_; lean_object* v___x_776_; 
v_cs_765_ = lean_ctor_get(v_x_757_, 0);
lean_inc_ref(v_cs_765_);
lean_dec_ref_known(v_x_757_, 1);
v___x_766_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0);
v___x_767_ = lean_usize_shift_right(v_x_758_, v_x_759_);
v_j_768_ = lean_usize_to_nat(v___x_767_);
v___x_769_ = lean_array_get_borrowed(v___x_766_, v_cs_765_, v_j_768_);
v___x_770_ = ((size_t)1ULL);
v___x_771_ = lean_usize_shift_left(v___x_770_, v_x_759_);
v___x_772_ = lean_usize_sub(v___x_771_, v___x_770_);
v___x_773_ = lean_usize_land(v_x_758_, v___x_772_);
v___x_774_ = ((size_t)5ULL);
v___x_775_ = lean_usize_sub(v_x_759_, v___x_774_);
lean_inc(v___x_769_);
lean_inc(v_mvarId_756_);
lean_inc(v_fvarId_755_);
v___x_776_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4(v_fvarId_755_, v_mvarId_756_, v___x_769_, v___x_773_, v___x_775_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_791_; 
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_791_ == 0)
{
lean_object* v_unused_792_; 
v_unused_792_ = lean_ctor_get(v___x_776_, 0);
lean_dec(v_unused_792_);
v___x_778_ = v___x_776_;
v_isShared_779_ = v_isSharedCheck_791_;
goto v_resetjp_777_;
}
else
{
lean_dec(v___x_776_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_791_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; uint8_t v___x_784_; 
v___x_780_ = lean_unsigned_to_nat(1u);
v___x_781_ = lean_nat_add(v_j_768_, v___x_780_);
lean_dec(v_j_768_);
v___x_782_ = lean_array_get_size(v_cs_765_);
v___x_783_ = lean_box(0);
v___x_784_ = lean_nat_dec_lt(v___x_781_, v___x_782_);
if (v___x_784_ == 0)
{
lean_object* v___x_786_; 
lean_dec(v___x_781_);
lean_dec_ref(v_cs_765_);
lean_dec(v_mvarId_756_);
lean_dec(v_fvarId_755_);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 0, v___x_783_);
v___x_786_ = v___x_778_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_783_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
else
{
size_t v___x_788_; size_t v___x_789_; lean_object* v___x_790_; 
lean_del_object(v___x_778_);
v___x_788_ = lean_usize_of_nat(v___x_781_);
lean_dec(v___x_781_);
v___x_789_ = lean_usize_of_nat(v___x_782_);
v___x_790_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(v_fvarId_755_, v_mvarId_756_, v_cs_765_, v___x_788_, v___x_789_, v___x_783_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
lean_dec_ref(v_cs_765_);
return v___x_790_;
}
}
}
else
{
lean_dec(v_j_768_);
lean_dec_ref(v_cs_765_);
lean_dec(v_mvarId_756_);
lean_dec(v_fvarId_755_);
return v___x_776_;
}
}
else
{
lean_object* v_vs_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_807_; 
v_vs_793_ = lean_ctor_get(v_x_757_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v_x_757_);
if (v_isSharedCheck_807_ == 0)
{
v___x_795_ = v_x_757_;
v_isShared_796_ = v_isSharedCheck_807_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_vs_793_);
lean_dec(v_x_757_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_807_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; uint8_t v___x_800_; 
v___x_797_ = lean_usize_to_nat(v_x_758_);
v___x_798_ = lean_array_get_size(v_vs_793_);
v___x_799_ = lean_box(0);
v___x_800_ = lean_nat_dec_lt(v___x_797_, v___x_798_);
if (v___x_800_ == 0)
{
lean_object* v___x_802_; 
lean_dec(v___x_797_);
lean_dec_ref(v_vs_793_);
lean_dec(v_mvarId_756_);
lean_dec(v_fvarId_755_);
if (v_isShared_796_ == 0)
{
lean_ctor_set_tag(v___x_795_, 0);
lean_ctor_set(v___x_795_, 0, v___x_799_);
v___x_802_ = v___x_795_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v___x_799_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
else
{
size_t v___x_804_; size_t v___x_805_; lean_object* v___x_806_; 
lean_del_object(v___x_795_);
v___x_804_ = lean_usize_of_nat(v___x_797_);
lean_dec(v___x_797_);
v___x_805_ = lean_usize_of_nat(v___x_798_);
v___x_806_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_755_, v_mvarId_756_, v_vs_793_, v___x_804_, v___x_805_, v___x_799_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
lean_dec_ref(v_vs_793_);
return v___x_806_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___boxed(lean_object* v_fvarId_808_, lean_object* v_mvarId_809_, lean_object* v_x_810_, lean_object* v_x_811_, lean_object* v_x_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
size_t v_x_8559__boxed_818_; size_t v_x_8560__boxed_819_; lean_object* v_res_820_; 
v_x_8559__boxed_818_ = lean_unbox_usize(v_x_811_);
lean_dec(v_x_811_);
v_x_8560__boxed_819_ = lean_unbox_usize(v_x_812_);
lean_dec(v_x_812_);
v_res_820_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4(v_fvarId_808_, v_mvarId_809_, v_x_810_, v_x_8559__boxed_818_, v_x_8560__boxed_819_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
lean_dec(v___y_814_);
lean_dec_ref(v___y_813_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1(lean_object* v_fvarId_821_, lean_object* v_mvarId_822_, lean_object* v_t_823_, lean_object* v_start_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v___x_830_; uint8_t v___x_831_; 
v___x_830_ = lean_unsigned_to_nat(0u);
v___x_831_ = lean_nat_dec_eq(v_start_824_, v___x_830_);
if (v___x_831_ == 0)
{
lean_object* v_root_832_; lean_object* v_tail_833_; size_t v_shift_834_; lean_object* v_tailOff_835_; uint8_t v___x_836_; 
v_root_832_ = lean_ctor_get(v_t_823_, 0);
lean_inc_ref(v_root_832_);
v_tail_833_ = lean_ctor_get(v_t_823_, 1);
lean_inc_ref(v_tail_833_);
v_shift_834_ = lean_ctor_get_usize(v_t_823_, 4);
v_tailOff_835_ = lean_ctor_get(v_t_823_, 3);
lean_inc(v_tailOff_835_);
lean_dec_ref(v_t_823_);
v___x_836_ = lean_nat_dec_le(v_tailOff_835_, v_start_824_);
if (v___x_836_ == 0)
{
size_t v___x_837_; lean_object* v___x_838_; 
lean_dec(v_tailOff_835_);
v___x_837_ = lean_usize_of_nat(v_start_824_);
lean_inc(v_mvarId_822_);
lean_inc(v_fvarId_821_);
v___x_838_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4(v_fvarId_821_, v_mvarId_822_, v_root_832_, v___x_837_, v_shift_834_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_851_; 
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_851_ == 0)
{
lean_object* v_unused_852_; 
v_unused_852_ = lean_ctor_get(v___x_838_, 0);
lean_dec(v_unused_852_);
v___x_840_ = v___x_838_;
v_isShared_841_ = v_isSharedCheck_851_;
goto v_resetjp_839_;
}
else
{
lean_dec(v___x_838_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_851_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_842_; lean_object* v___x_843_; uint8_t v___x_844_; 
v___x_842_ = lean_array_get_size(v_tail_833_);
v___x_843_ = lean_box(0);
v___x_844_ = lean_nat_dec_lt(v___x_830_, v___x_842_);
if (v___x_844_ == 0)
{
lean_object* v___x_846_; 
lean_dec_ref(v_tail_833_);
lean_dec(v_mvarId_822_);
lean_dec(v_fvarId_821_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 0, v___x_843_);
v___x_846_ = v___x_840_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_843_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
else
{
size_t v___x_848_; size_t v___x_849_; lean_object* v___x_850_; 
lean_del_object(v___x_840_);
v___x_848_ = ((size_t)0ULL);
v___x_849_ = lean_usize_of_nat(v___x_842_);
v___x_850_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_821_, v_mvarId_822_, v_tail_833_, v___x_848_, v___x_849_, v___x_843_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
lean_dec_ref(v_tail_833_);
return v___x_850_;
}
}
}
else
{
lean_dec_ref(v_tail_833_);
lean_dec(v_mvarId_822_);
lean_dec(v_fvarId_821_);
return v___x_838_;
}
}
else
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; uint8_t v___x_856_; 
lean_dec_ref(v_root_832_);
v___x_853_ = lean_nat_sub(v_start_824_, v_tailOff_835_);
lean_dec(v_tailOff_835_);
v___x_854_ = lean_array_get_size(v_tail_833_);
v___x_855_ = lean_box(0);
v___x_856_ = lean_nat_dec_lt(v___x_853_, v___x_854_);
if (v___x_856_ == 0)
{
lean_object* v___x_857_; 
lean_dec(v___x_853_);
lean_dec_ref(v_tail_833_);
lean_dec(v_mvarId_822_);
lean_dec(v_fvarId_821_);
v___x_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_857_, 0, v___x_855_);
return v___x_857_;
}
else
{
size_t v___x_858_; size_t v___x_859_; lean_object* v___x_860_; 
v___x_858_ = lean_usize_of_nat(v___x_853_);
lean_dec(v___x_853_);
v___x_859_ = lean_usize_of_nat(v___x_854_);
v___x_860_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_821_, v_mvarId_822_, v_tail_833_, v___x_858_, v___x_859_, v___x_855_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
lean_dec_ref(v_tail_833_);
return v___x_860_;
}
}
}
else
{
lean_object* v___x_861_; 
v___x_861_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6(v_fvarId_821_, v_mvarId_822_, v_t_823_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
return v___x_861_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1___boxed(lean_object* v_fvarId_862_, lean_object* v_mvarId_863_, lean_object* v_t_864_, lean_object* v_start_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1(v_fvarId_862_, v_mvarId_863_, v_t_864_, v_start_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v_start_865_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1(lean_object* v_fvarId_872_, lean_object* v_mvarId_873_, lean_object* v_lctx_874_, lean_object* v_start_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_){
_start:
{
lean_object* v_decls_881_; lean_object* v___x_882_; 
v_decls_881_ = lean_ctor_get(v_lctx_874_, 1);
lean_inc_ref(v_decls_881_);
lean_dec_ref(v_lctx_874_);
v___x_882_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1(v_fvarId_872_, v_mvarId_873_, v_decls_881_, v_start_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1___boxed(lean_object* v_fvarId_883_, lean_object* v_mvarId_884_, lean_object* v_lctx_885_, lean_object* v_start_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1(v_fvarId_883_, v_mvarId_884_, v_lctx_885_, v_start_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
lean_dec(v_start_886_);
return v_res_892_;
}
}
static lean_object* _init_l_Lean_MVarId_clear___lam__1___closed__1(void){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_894_ = ((lean_object*)(l_Lean_MVarId_clear___lam__1___closed__0));
v___x_895_ = l_Lean_stringToMessageData(v___x_894_);
return v___x_895_;
}
}
static lean_object* _init_l_Lean_MVarId_clear___lam__1___closed__3(void){
_start:
{
lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_897_ = ((lean_object*)(l_Lean_MVarId_clear___lam__1___closed__2));
v___x_898_ = l_Lean_stringToMessageData(v___x_897_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clear___lam__1(lean_object* v_mvarId_899_, lean_object* v___x_900_, lean_object* v_fvarId_901_, lean_object* v___f_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v___y_909_; lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v___y_912_; lean_object* v___y_913_; lean_object* v___y_914_; lean_object* v___y_915_; lean_object* v___y_916_; lean_object* v___y_917_; lean_object* v___x_939_; 
lean_inc(v___x_900_);
lean_inc(v_mvarId_899_);
v___x_939_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_899_, v___x_900_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
if (lean_obj_tag(v___x_939_) == 0)
{
lean_object* v_lctx_940_; lean_object* v___y_942_; lean_object* v___y_943_; lean_object* v___y_944_; lean_object* v___y_945_; lean_object* v___y_946_; lean_object* v___y_947_; lean_object* v___y_948_; lean_object* v___y_955_; lean_object* v___y_956_; lean_object* v___y_957_; lean_object* v___y_958_; uint8_t v___x_1015_; 
lean_dec_ref_known(v___x_939_, 1);
v_lctx_940_ = lean_ctor_get(v___y_903_, 2);
lean_inc_ref(v_lctx_940_);
v___x_1015_ = l_Lean_LocalContext_contains(v_lctx_940_, v_fvarId_901_);
if (v___x_1015_ == 0)
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1016_ = lean_obj_once(&l_Lean_MVarId_clear___lam__1___closed__3, &l_Lean_MVarId_clear___lam__1___closed__3_once, _init_l_Lean_MVarId_clear___lam__1___closed__3);
lean_inc(v_fvarId_901_);
v___x_1017_ = l_Lean_mkFVar(v_fvarId_901_);
v___x_1018_ = l_Lean_MessageData_ofExpr(v___x_1017_);
v___x_1019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1016_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
v___x_1020_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7);
v___x_1021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1019_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
v___x_1022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1021_);
lean_inc(v_mvarId_899_);
lean_inc(v___x_900_);
v___x_1023_ = l_Lean_Meta_throwTacticEx___redArg(v___x_900_, v_mvarId_899_, v___x_1022_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_dec_ref_known(v___x_1023_, 1);
v___y_955_ = v___y_903_;
v___y_956_ = v___y_904_;
v___y_957_ = v___y_905_;
v___y_958_ = v___y_906_;
goto v___jp_954_;
}
else
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
lean_dec_ref(v_lctx_940_);
lean_dec_ref(v___y_903_);
lean_dec_ref(v___f_902_);
lean_dec(v_fvarId_901_);
lean_dec(v___x_900_);
lean_dec(v_mvarId_899_);
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_1023_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1023_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
if (v_isShared_1027_ == 0)
{
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1024_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
else
{
v___y_955_ = v___y_903_;
v___y_956_ = v___y_904_;
v___y_957_ = v___y_905_;
v___y_958_ = v___y_906_;
goto v___jp_954_;
}
v___jp_941_:
{
lean_object* v_localInstances_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v_localInstances_949_ = lean_ctor_get(v___y_945_, 3);
v___x_950_ = l_Lean_LocalContext_erase(v_lctx_940_, v_fvarId_901_);
lean_dec(v_fvarId_901_);
lean_inc(v___y_944_);
v___x_951_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_902_, v_localInstances_949_, v___y_944_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_inc_ref(v_localInstances_949_);
v___y_909_ = v___y_942_;
v___y_910_ = v___y_948_;
v___y_911_ = v___y_946_;
v___y_912_ = v___y_945_;
v___y_913_ = v___y_943_;
v___y_914_ = v___x_950_;
v___y_915_ = v___y_947_;
v___y_916_ = v___y_944_;
v___y_917_ = v_localInstances_949_;
goto v___jp_908_;
}
else
{
lean_object* v_val_952_; lean_object* v___x_953_; 
v_val_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_val_952_);
lean_dec_ref_known(v___x_951_, 1);
lean_inc_ref(v_localInstances_949_);
v___x_953_ = l_Array_eraseIdx___redArg(v_localInstances_949_, v_val_952_);
v___y_909_ = v___y_942_;
v___y_910_ = v___y_948_;
v___y_911_ = v___y_946_;
v___y_912_ = v___y_945_;
v___y_913_ = v___y_943_;
v___y_914_ = v___x_950_;
v___y_915_ = v___y_947_;
v___y_916_ = v___y_944_;
v___y_917_ = v___x_953_;
goto v___jp_908_;
}
}
v___jp_954_:
{
lean_object* v___x_959_; 
lean_inc(v_mvarId_899_);
v___x_959_ = l_Lean_MVarId_getTag(v_mvarId_899_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v_a_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v_a_960_ = lean_ctor_get(v___x_959_, 0);
lean_inc(v_a_960_);
lean_dec_ref_known(v___x_959_, 1);
v___x_961_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_lctx_940_);
lean_inc(v_mvarId_899_);
lean_inc(v_fvarId_901_);
v___x_962_ = l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1(v_fvarId_901_, v_mvarId_899_, v_lctx_940_, v___x_961_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v___x_963_; 
lean_dec_ref_known(v___x_962_, 1);
lean_inc(v_mvarId_899_);
v___x_963_ = l_Lean_MVarId_getDecl(v_mvarId_899_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
if (lean_obj_tag(v___x_963_) == 0)
{
lean_object* v_a_964_; lean_object* v_type_965_; lean_object* v___x_966_; lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_990_; 
v_a_964_ = lean_ctor_get(v___x_963_, 0);
lean_inc(v_a_964_);
lean_dec_ref_known(v___x_963_, 1);
v_type_965_ = lean_ctor_get(v_a_964_, 2);
lean_inc_ref_n(v_type_965_, 2);
lean_dec(v_a_964_);
lean_inc(v_fvarId_901_);
v___x_966_ = l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3___redArg(v_type_965_, v_fvarId_901_, v___y_956_);
v_a_967_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_990_ == 0)
{
v___x_969_ = v___x_966_;
v_isShared_970_ = v_isSharedCheck_990_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_966_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_990_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
uint8_t v___x_971_; 
v___x_971_ = lean_unbox(v_a_967_);
lean_dec(v_a_967_);
if (v___x_971_ == 0)
{
lean_del_object(v___x_969_);
lean_dec(v___x_900_);
v___y_942_ = v_a_960_;
v___y_943_ = v_type_965_;
v___y_944_ = v___x_961_;
v___y_945_ = v___y_955_;
v___y_946_ = v___y_956_;
v___y_947_ = v___y_957_;
v___y_948_ = v___y_958_;
goto v___jp_941_;
}
else
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_979_; 
v___x_972_ = lean_obj_once(&l_Lean_MVarId_clear___lam__1___closed__1, &l_Lean_MVarId_clear___lam__1___closed__1_once, _init_l_Lean_MVarId_clear___lam__1___closed__1);
lean_inc(v_fvarId_901_);
v___x_973_ = l_Lean_mkFVar(v_fvarId_901_);
v___x_974_ = l_Lean_MessageData_ofExpr(v___x_973_);
v___x_975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_972_);
lean_ctor_set(v___x_975_, 1, v___x_974_);
v___x_976_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7);
v___x_977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_975_);
lean_ctor_set(v___x_977_, 1, v___x_976_);
if (v_isShared_970_ == 0)
{
lean_ctor_set_tag(v___x_969_, 1);
lean_ctor_set(v___x_969_, 0, v___x_977_);
v___x_979_ = v___x_969_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v___x_977_);
v___x_979_ = v_reuseFailAlloc_989_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
lean_object* v___x_980_; 
lean_inc(v_mvarId_899_);
v___x_980_ = l_Lean_Meta_throwTacticEx___redArg(v___x_900_, v_mvarId_899_, v___x_979_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_dec_ref_known(v___x_980_, 1);
v___y_942_ = v_a_960_;
v___y_943_ = v_type_965_;
v___y_944_ = v___x_961_;
v___y_945_ = v___y_955_;
v___y_946_ = v___y_956_;
v___y_947_ = v___y_957_;
v___y_948_ = v___y_958_;
goto v___jp_941_;
}
else
{
lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_988_; 
lean_dec_ref(v_type_965_);
lean_dec(v_a_960_);
lean_dec_ref(v___y_955_);
lean_dec_ref(v_lctx_940_);
lean_dec_ref(v___f_902_);
lean_dec(v_fvarId_901_);
lean_dec(v_mvarId_899_);
v_a_981_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_988_ == 0)
{
v___x_983_ = v___x_980_;
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v___x_980_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_986_; 
if (v_isShared_984_ == 0)
{
v___x_986_ = v___x_983_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_a_981_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
lean_dec(v_a_960_);
lean_dec_ref(v___y_955_);
lean_dec_ref(v_lctx_940_);
lean_dec_ref(v___f_902_);
lean_dec(v_fvarId_901_);
lean_dec(v___x_900_);
lean_dec(v_mvarId_899_);
v_a_991_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_963_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_963_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
else
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1006_; 
lean_dec(v_a_960_);
lean_dec_ref(v___y_955_);
lean_dec_ref(v_lctx_940_);
lean_dec_ref(v___f_902_);
lean_dec(v_fvarId_901_);
lean_dec(v___x_900_);
lean_dec(v_mvarId_899_);
v_a_999_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_1001_ = v___x_962_;
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_962_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1004_; 
if (v_isShared_1002_ == 0)
{
v___x_1004_ = v___x_1001_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_a_999_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
}
}
else
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1014_; 
lean_dec_ref(v___y_955_);
lean_dec_ref(v_lctx_940_);
lean_dec_ref(v___f_902_);
lean_dec(v_fvarId_901_);
lean_dec(v___x_900_);
lean_dec(v_mvarId_899_);
v_a_1007_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1009_ = v___x_959_;
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_959_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1012_; 
if (v_isShared_1010_ == 0)
{
v___x_1012_ = v___x_1009_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_a_1007_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
}
}
else
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
lean_dec_ref(v___y_903_);
lean_dec_ref(v___f_902_);
lean_dec(v_fvarId_901_);
lean_dec(v___x_900_);
lean_dec(v_mvarId_899_);
v_a_1032_ = lean_ctor_get(v___x_939_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_939_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_939_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1037_; 
if (v_isShared_1035_ == 0)
{
v___x_1037_ = v___x_1034_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1032_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
v___jp_908_:
{
uint8_t v___x_918_; lean_object* v___x_919_; 
v___x_918_ = 2;
v___x_919_ = l_Lean_Meta_mkFreshExprMVarAt(v___y_914_, v___y_917_, v___y_913_, v___x_918_, v___y_909_, v___y_916_, v___y_912_, v___y_911_, v___y_915_, v___y_910_);
lean_dec_ref(v___y_912_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_object* v_a_920_; lean_object* v___x_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_929_; 
v_a_920_ = lean_ctor_get(v___x_919_, 0);
lean_inc_n(v_a_920_, 2);
lean_dec_ref_known(v___x_919_, 1);
v___x_921_ = l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg(v_mvarId_899_, v_a_920_, v___y_911_);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_929_ == 0)
{
lean_object* v_unused_930_; 
v_unused_930_ = lean_ctor_get(v___x_921_, 0);
lean_dec(v_unused_930_);
v___x_923_ = v___x_921_;
v_isShared_924_ = v_isSharedCheck_929_;
goto v_resetjp_922_;
}
else
{
lean_dec(v___x_921_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_929_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_925_; lean_object* v___x_927_; 
v___x_925_ = l_Lean_Expr_mvarId_x21(v_a_920_);
lean_dec(v_a_920_);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 0, v___x_925_);
v___x_927_ = v___x_923_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v___x_925_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
else
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_938_; 
lean_dec(v_mvarId_899_);
v_a_931_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_938_ == 0)
{
v___x_933_ = v___x_919_;
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_919_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_936_; 
if (v_isShared_934_ == 0)
{
v___x_936_ = v___x_933_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_a_931_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clear___lam__1___boxed(lean_object* v_mvarId_1040_, lean_object* v___x_1041_, lean_object* v_fvarId_1042_, lean_object* v___f_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Lean_MVarId_clear___lam__1(v_mvarId_1040_, v___x_1041_, v_fvarId_1042_, v___f_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v___y_1045_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clear(lean_object* v_mvarId_1050_, lean_object* v_fvarId_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_){
_start:
{
lean_object* v___f_1057_; lean_object* v___x_1058_; lean_object* v___f_1059_; lean_object* v___x_1060_; 
lean_inc(v_fvarId_1051_);
v___f_1057_ = lean_alloc_closure((void*)(l_Lean_MVarId_clear___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1057_, 0, v_fvarId_1051_);
v___x_1058_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__1));
lean_inc(v_mvarId_1050_);
v___f_1059_ = lean_alloc_closure((void*)(l_Lean_MVarId_clear___lam__1___boxed), 9, 4);
lean_closure_set(v___f_1059_, 0, v_mvarId_1050_);
lean_closure_set(v___f_1059_, 1, v___x_1058_);
lean_closure_set(v___f_1059_, 2, v_fvarId_1051_);
lean_closure_set(v___f_1059_, 3, v___f_1057_);
v___x_1060_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg(v_mvarId_1050_, v___f_1059_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clear___boxed(lean_object* v_mvarId_1061_, lean_object* v_fvarId_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_Lean_MVarId_clear(v_mvarId_1061_, v_fvarId_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
lean_dec(v_a_1066_);
lean_dec_ref(v_a_1065_);
lean_dec(v_a_1064_);
lean_dec_ref(v_a_1063_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2(lean_object* v_mvarId_1069_, lean_object* v_val_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v___x_1076_; 
v___x_1076_ = l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg(v_mvarId_1069_, v_val_1070_, v___y_1072_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___boxed(lean_object* v_mvarId_1077_, lean_object* v_val_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2(v_mvarId_1077_, v_val_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3(lean_object* v_00_u03b2_1085_, lean_object* v_x_1086_, lean_object* v_x_1087_, lean_object* v_x_1088_){
_start:
{
lean_object* v___x_1089_; 
v___x_1089_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3___redArg(v_x_1086_, v_x_1087_, v_x_1088_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9(lean_object* v_00_u03b2_1090_, lean_object* v_x_1091_, size_t v_x_1092_, size_t v_x_1093_, lean_object* v_x_1094_, lean_object* v_x_1095_){
_start:
{
lean_object* v___x_1096_; 
v___x_1096_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_x_1091_, v_x_1092_, v_x_1093_, v_x_1094_, v_x_1095_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___boxed(lean_object* v_00_u03b2_1097_, lean_object* v_x_1098_, lean_object* v_x_1099_, lean_object* v_x_1100_, lean_object* v_x_1101_, lean_object* v_x_1102_){
_start:
{
size_t v_x_9109__boxed_1103_; size_t v_x_9110__boxed_1104_; lean_object* v_res_1105_; 
v_x_9109__boxed_1103_ = lean_unbox_usize(v_x_1099_);
lean_dec(v_x_1099_);
v_x_9110__boxed_1104_ = lean_unbox_usize(v_x_1100_);
lean_dec(v_x_1100_);
v_res_1105_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9(v_00_u03b2_1097_, v_x_1098_, v_x_9109__boxed_1103_, v_x_9110__boxed_1104_, v_x_1101_, v_x_1102_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13(lean_object* v_00_u03b2_1106_, lean_object* v_n_1107_, lean_object* v_k_1108_, lean_object* v_v_1109_){
_start:
{
lean_object* v___x_1110_; 
v___x_1110_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13___redArg(v_n_1107_, v_k_1108_, v_v_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14(lean_object* v_00_u03b2_1111_, size_t v_depth_1112_, lean_object* v_keys_1113_, lean_object* v_vals_1114_, lean_object* v_heq_1115_, lean_object* v_i_1116_, lean_object* v_entries_1117_){
_start:
{
lean_object* v___x_1118_; 
v___x_1118_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg(v_depth_1112_, v_keys_1113_, v_vals_1114_, v_i_1116_, v_entries_1117_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___boxed(lean_object* v_00_u03b2_1119_, lean_object* v_depth_1120_, lean_object* v_keys_1121_, lean_object* v_vals_1122_, lean_object* v_heq_1123_, lean_object* v_i_1124_, lean_object* v_entries_1125_){
_start:
{
size_t v_depth_boxed_1126_; lean_object* v_res_1127_; 
v_depth_boxed_1126_ = lean_unbox_usize(v_depth_1120_);
lean_dec(v_depth_1120_);
v_res_1127_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14(v_00_u03b2_1119_, v_depth_boxed_1126_, v_keys_1121_, v_vals_1122_, v_heq_1123_, v_i_1124_, v_entries_1125_);
lean_dec_ref(v_vals_1122_);
lean_dec_ref(v_keys_1121_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13_spec__14(lean_object* v_00_u03b2_1128_, lean_object* v_x_1129_, lean_object* v_x_1130_, lean_object* v_x_1131_, lean_object* v_x_1132_){
_start:
{
lean_object* v___x_1133_; 
v___x_1133_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13_spec__14___redArg(v_x_1129_, v_x_1130_, v_x_1131_, v_x_1132_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClear(lean_object* v_mvarId_1134_, lean_object* v_fvarId_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = l_Lean_Meta_saveState___redArg(v_a_1137_, v_a_1139_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v_a_1142_; lean_object* v___x_1143_; 
v_a_1142_ = lean_ctor_get(v___x_1141_, 0);
lean_inc(v_a_1142_);
lean_dec_ref_known(v___x_1141_, 1);
lean_inc(v_mvarId_1134_);
v___x_1143_ = l_Lean_MVarId_clear(v_mvarId_1134_, v_fvarId_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_dec(v_a_1142_);
lean_dec(v_mvarId_1134_);
return v___x_1143_;
}
else
{
lean_object* v_a_1144_; uint8_t v___x_1145_; 
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
v___x_1145_ = l_Lean_Exception_isInterrupt(v_a_1144_);
if (v___x_1145_ == 0)
{
uint8_t v___x_1146_; 
lean_inc(v_a_1144_);
v___x_1146_ = l_Lean_Exception_isRuntime(v_a_1144_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1147_; 
lean_dec_ref_known(v___x_1143_, 1);
v___x_1147_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1142_, v_a_1137_, v_a_1139_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1154_; 
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1154_ == 0)
{
lean_object* v_unused_1155_; 
v_unused_1155_ = lean_ctor_get(v___x_1147_, 0);
lean_dec(v_unused_1155_);
v___x_1149_ = v___x_1147_;
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
else
{
lean_dec(v___x_1147_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1152_; 
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 0, v_mvarId_1134_);
v___x_1152_ = v___x_1149_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_mvarId_1134_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
else
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1163_; 
lean_dec(v_mvarId_1134_);
v_a_1156_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1158_ = v___x_1147_;
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_1147_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
if (v_isShared_1159_ == 0)
{
v___x_1161_ = v___x_1158_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1156_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
else
{
lean_dec(v_a_1142_);
lean_dec(v_mvarId_1134_);
return v___x_1143_;
}
}
else
{
lean_dec(v_a_1142_);
lean_dec(v_mvarId_1134_);
return v___x_1143_;
}
}
}
else
{
lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1171_; 
lean_dec(v_fvarId_1135_);
lean_dec(v_mvarId_1134_);
v_a_1164_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1166_ = v___x_1141_;
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v___x_1141_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1169_; 
if (v_isShared_1167_ == 0)
{
v___x_1169_ = v___x_1166_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_a_1164_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClear___boxed(lean_object* v_mvarId_1172_, lean_object* v_fvarId_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_Lean_MVarId_tryClear(v_mvarId_1172_, v_fvarId_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
lean_dec(v_a_1177_);
lean_dec_ref(v_a_1176_);
lean_dec(v_a_1175_);
lean_dec_ref(v_a_1174_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0(lean_object* v_as_1180_, size_t v_i_1181_, size_t v_stop_1182_, lean_object* v_b_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
uint8_t v___x_1189_; 
v___x_1189_ = lean_usize_dec_eq(v_i_1181_, v_stop_1182_);
if (v___x_1189_ == 0)
{
size_t v___x_1190_; size_t v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1190_ = ((size_t)1ULL);
v___x_1191_ = lean_usize_sub(v_i_1181_, v___x_1190_);
v___x_1192_ = lean_array_uget_borrowed(v_as_1180_, v___x_1191_);
lean_inc(v___x_1192_);
v___x_1193_ = l_Lean_MVarId_tryClear(v_b_1183_, v___x_1192_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_object* v_a_1194_; 
v_a_1194_ = lean_ctor_get(v___x_1193_, 0);
lean_inc(v_a_1194_);
lean_dec_ref_known(v___x_1193_, 1);
v_i_1181_ = v___x_1191_;
v_b_1183_ = v_a_1194_;
goto _start;
}
else
{
return v___x_1193_;
}
}
else
{
lean_object* v___x_1196_; 
v___x_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1196_, 0, v_b_1183_);
return v___x_1196_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0___boxed(lean_object* v_as_1197_, lean_object* v_i_1198_, lean_object* v_stop_1199_, lean_object* v_b_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
size_t v_i_boxed_1206_; size_t v_stop_boxed_1207_; lean_object* v_res_1208_; 
v_i_boxed_1206_ = lean_unbox_usize(v_i_1198_);
lean_dec(v_i_1198_);
v_stop_boxed_1207_ = lean_unbox_usize(v_stop_1199_);
lean_dec(v_stop_1199_);
v_res_1208_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0(v_as_1197_, v_i_boxed_1206_, v_stop_boxed_1207_, v_b_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec_ref(v_as_1197_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany(lean_object* v_mvarId_1209_, lean_object* v_fvarIds_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_){
_start:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; uint8_t v___x_1218_; 
v___x_1216_ = lean_array_get_size(v_fvarIds_1210_);
v___x_1217_ = lean_unsigned_to_nat(0u);
v___x_1218_ = lean_nat_dec_lt(v___x_1217_, v___x_1216_);
if (v___x_1218_ == 0)
{
lean_object* v___x_1219_; 
v___x_1219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1219_, 0, v_mvarId_1209_);
return v___x_1219_;
}
else
{
size_t v___x_1220_; size_t v___x_1221_; lean_object* v___x_1222_; 
v___x_1220_ = lean_usize_of_nat(v___x_1216_);
v___x_1221_ = ((size_t)0ULL);
v___x_1222_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0(v_fvarIds_1210_, v___x_1220_, v___x_1221_, v_mvarId_1209_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_);
return v___x_1222_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany___boxed(lean_object* v_mvarId_1223_, lean_object* v_fvarIds_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Lean_MVarId_tryClearMany(v_mvarId_1223_, v_fvarIds_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_);
lean_dec(v_a_1228_);
lean_dec_ref(v_a_1227_);
lean_dec(v_a_1226_);
lean_dec_ref(v_a_1225_);
lean_dec_ref(v_fvarIds_1224_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0(lean_object* v_as_1231_, size_t v_i_1232_, size_t v_stop_1233_, lean_object* v_b_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
uint8_t v___x_1240_; 
v___x_1240_ = lean_usize_dec_eq(v_i_1232_, v_stop_1233_);
if (v___x_1240_ == 0)
{
lean_object* v_fst_1241_; lean_object* v_snd_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1267_; 
v_fst_1241_ = lean_ctor_get(v_b_1234_, 0);
v_snd_1242_ = lean_ctor_get(v_b_1234_, 1);
v_isSharedCheck_1267_ = !lean_is_exclusive(v_b_1234_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1244_ = v_b_1234_;
v_isShared_1245_ = v_isSharedCheck_1267_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_snd_1242_);
lean_inc(v_fst_1241_);
lean_dec(v_b_1234_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1267_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
size_t v___x_1246_; size_t v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1246_ = ((size_t)1ULL);
v___x_1247_ = lean_usize_sub(v_i_1232_, v___x_1246_);
v___x_1248_ = lean_array_uget_borrowed(v_as_1231_, v___x_1247_);
lean_inc(v___x_1248_);
lean_inc(v_fst_1241_);
v___x_1249_ = l_Lean_MVarId_tryClear(v_fst_1241_, v___x_1248_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v_a_1250_; lean_object* v___y_1252_; uint8_t v___x_1257_; 
v_a_1250_ = lean_ctor_get(v___x_1249_, 0);
lean_inc(v_a_1250_);
lean_dec_ref_known(v___x_1249_, 1);
v___x_1257_ = l_Lean_instBEqMVarId_beq(v_fst_1241_, v_a_1250_);
lean_dec(v_fst_1241_);
if (v___x_1257_ == 0)
{
lean_object* v___x_1258_; 
lean_inc(v___x_1248_);
v___x_1258_ = lean_array_push(v_snd_1242_, v___x_1248_);
v___y_1252_ = v___x_1258_;
goto v___jp_1251_;
}
else
{
v___y_1252_ = v_snd_1242_;
goto v___jp_1251_;
}
v___jp_1251_:
{
lean_object* v___x_1254_; 
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 1, v___y_1252_);
lean_ctor_set(v___x_1244_, 0, v_a_1250_);
v___x_1254_ = v___x_1244_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1250_);
lean_ctor_set(v_reuseFailAlloc_1256_, 1, v___y_1252_);
v___x_1254_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
v_i_1232_ = v___x_1247_;
v_b_1234_ = v___x_1254_;
goto _start;
}
}
}
else
{
lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1266_; 
lean_del_object(v___x_1244_);
lean_dec(v_snd_1242_);
lean_dec(v_fst_1241_);
v_a_1259_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1261_ = v___x_1249_;
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_dec(v___x_1249_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1262_ == 0)
{
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_a_1259_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
}
}
else
{
lean_object* v___x_1268_; 
v___x_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1268_, 0, v_b_1234_);
return v___x_1268_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0___boxed(lean_object* v_as_1269_, lean_object* v_i_1270_, lean_object* v_stop_1271_, lean_object* v_b_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
size_t v_i_boxed_1278_; size_t v_stop_boxed_1279_; lean_object* v_res_1280_; 
v_i_boxed_1278_ = lean_unbox_usize(v_i_1270_);
lean_dec(v_i_1270_);
v_stop_boxed_1279_ = lean_unbox_usize(v_stop_1271_);
lean_dec(v_stop_1271_);
v_res_1280_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0(v_as_1269_, v_i_boxed_1278_, v_stop_boxed_1279_, v_b_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
lean_dec_ref(v_as_1269_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany_x27___lam__0(lean_object* v_fvarIds_1281_, lean_object* v_goal_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v_lctx_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; uint8_t v___x_1294_; 
v_lctx_1288_ = lean_ctor_get(v___y_1283_, 2);
v___x_1289_ = l_Lean_LocalContext_sortFVarsByContextOrder(v_lctx_1288_, v_fvarIds_1281_);
v___x_1290_ = lean_array_get_size(v___x_1289_);
v___x_1291_ = lean_mk_empty_array_with_capacity(v___x_1290_);
v___x_1292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1292_, 0, v_goal_1282_);
lean_ctor_set(v___x_1292_, 1, v___x_1291_);
v___x_1293_ = lean_unsigned_to_nat(0u);
v___x_1294_ = lean_nat_dec_lt(v___x_1293_, v___x_1290_);
if (v___x_1294_ == 0)
{
lean_object* v___x_1295_; 
lean_dec_ref(v___x_1289_);
v___x_1295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1292_);
return v___x_1295_;
}
else
{
size_t v___x_1296_; size_t v___x_1297_; lean_object* v___x_1298_; 
v___x_1296_ = lean_usize_of_nat(v___x_1290_);
v___x_1297_ = ((size_t)0ULL);
v___x_1298_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0(v___x_1289_, v___x_1296_, v___x_1297_, v___x_1292_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
lean_dec_ref(v___x_1289_);
return v___x_1298_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany_x27___lam__0___boxed(lean_object* v_fvarIds_1299_, lean_object* v_goal_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l_Lean_MVarId_tryClearMany_x27___lam__0(v_fvarIds_1299_, v_goal_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany_x27(lean_object* v_goal_1307_, lean_object* v_fvarIds_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_){
_start:
{
lean_object* v___f_1314_; lean_object* v___x_1315_; 
lean_inc(v_goal_1307_);
v___f_1314_ = lean_alloc_closure((void*)(l_Lean_MVarId_tryClearMany_x27___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1314_, 0, v_fvarIds_1308_);
lean_closure_set(v___f_1314_, 1, v_goal_1307_);
v___x_1315_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg(v_goal_1307_, v___f_1314_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany_x27___boxed(lean_object* v_goal_1316_, lean_object* v_fvarIds_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_Lean_MVarId_tryClearMany_x27(v_goal_1316_, v_fvarIds_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_);
lean_dec(v_a_1321_);
lean_dec_ref(v_a_1320_);
lean_dec(v_a_1319_);
lean_dec_ref(v_a_1318_);
return v_res_1323_;
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
