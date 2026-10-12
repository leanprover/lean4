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
uint8_t l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__0(lean_object* v_fvarId_1_, lean_object* v_x_2_){
_start:
{
uint8_t v___x_3_; 
v___x_3_ = l_Lean_instBEqFVarId_beq(v_fvarId_1_, v_x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_1_ = stack[0].m_obj;
lean_object* v_x_2_ = stack[1].m_obj;
uint8_t v_res_4_;
v_res_4_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__0(v_fvarId_1_, v_x_2_);
stack->m_num = v_res_4_;
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__0___boxed(lean_object* v_fvarId_5_, lean_object* v_x_6_){
_start:
{
uint8_t v_res_7_; lean_object* v_r_8_; 
v_res_7_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__0(v_fvarId_5_, v_x_6_);
lean_dec(v_x_6_);
lean_dec(v_fvarId_5_);
v_r_8_ = lean_box(v_res_7_);
return v_r_8_;
}
}
uint8_t l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__1(lean_object* v_x_9_){
_start:
{
uint8_t v___x_10_; 
v___x_10_ = 0;
return v___x_10_;
}
}
LEAN_EXPORT void l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_9_ = stack[0].m_obj;
uint8_t v_res_11_;
v_res_11_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__1(v_x_9_);
stack->m_num = v_res_11_;
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__1___boxed(lean_object* v_x_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__1(v_x_12_);
lean_dec(v_x_12_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
static lean_object* _init_l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_16_ = lean_box(0);
v___x_17_ = lean_unsigned_to_nat(16u);
v___x_18_ = lean_mk_array(v___x_17_, v___x_16_);
return v___x_18_;
}
}
static lean_object* _init_l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_19_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__1, &l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__1_once, _init_l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__1);
v___x_20_ = lean_unsigned_to_nat(0u);
v___x_21_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_21_, 0, v___x_20_);
lean_ctor_set(v___x_21_, 1, v___x_19_);
return v___x_21_;
}
}
lean_object* l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg(lean_object* v_localDecl_22_, lean_object* v_fvarId_23_, uint8_t v_generalizeNondepLet_24_, lean_object* v___y_25_){
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
v___x_82_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2);
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
v___x_139_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2);
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
v___x_106_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2);
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
LEAN_EXPORT void l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_localDecl_22_ = stack[0].m_obj;
lean_object* v_fvarId_23_ = stack[1].m_obj;
uint8_t v_generalizeNondepLet_24_ = stack[2].m_num;
lean_object* v___y_25_ = stack[3].m_obj;
lean_object* v_res_145_;
v_res_145_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg(v_localDecl_22_, v_fvarId_23_, v_generalizeNondepLet_24_, v___y_25_);
stack->m_obj
 = v_res_145_;
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___boxed(lean_object* v_localDecl_146_, lean_object* v_fvarId_147_, lean_object* v_generalizeNondepLet_148_, lean_object* v___y_149_, lean_object* v___y_150_){
_start:
{
uint8_t v_generalizeNondepLet_boxed_151_; lean_object* v_res_152_; 
v_generalizeNondepLet_boxed_151_ = lean_unbox(v_generalizeNondepLet_148_);
v_res_152_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg(v_localDecl_146_, v_fvarId_147_, v_generalizeNondepLet_boxed_151_, v___y_149_);
lean_dec(v___y_149_);
return v_res_152_;
}
}
lean_object* l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0(lean_object* v_localDecl_153_, lean_object* v_fvarId_154_, uint8_t v_generalizeNondepLet_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg(v_localDecl_153_, v_fvarId_154_, v_generalizeNondepLet_155_, v___y_157_);
return v___x_161_;
}
}
LEAN_EXPORT void l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_localDecl_153_ = stack[0].m_obj;
lean_object* v_fvarId_154_ = stack[1].m_obj;
uint8_t v_generalizeNondepLet_155_ = stack[2].m_num;
lean_object* v___y_156_ = stack[3].m_obj;
lean_object* v___y_157_ = stack[4].m_obj;
lean_object* v___y_158_ = stack[5].m_obj;
lean_object* v___y_159_ = stack[6].m_obj;
lean_object* v_res_162_;
v_res_162_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0(v_localDecl_153_, v_fvarId_154_, v_generalizeNondepLet_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_);
stack->m_obj
 = v_res_162_;
}
LEAN_EXPORT lean_object* l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___boxed(lean_object* v_localDecl_163_, lean_object* v_fvarId_164_, lean_object* v_generalizeNondepLet_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_){
_start:
{
uint8_t v_generalizeNondepLet_boxed_171_; lean_object* v_res_172_; 
v_generalizeNondepLet_boxed_171_ = lean_unbox(v_generalizeNondepLet_165_);
v_res_172_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0(v_localDecl_163_, v_fvarId_164_, v_generalizeNondepLet_boxed_171_, v___y_166_, v___y_167_, v___y_168_, v___y_169_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
return v_res_172_;
}
}
lean_object* l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3___redArg(lean_object* v_e_173_, lean_object* v_fvarId_174_, lean_object* v___y_175_){
_start:
{
lean_object* v___f_177_; lean_object* v___f_178_; lean_object* v___x_179_; uint8_t v_fst_181_; lean_object* v_mctx_182_; lean_object* v___y_200_; lean_object* v_mctx_205_; lean_object* v___x_206_; lean_object* v___x_207_; uint8_t v___x_208_; 
v___f_177_ = ((lean_object*)(l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__0));
v___f_178_ = lean_alloc_closure((void*)(l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_178_, 0, v_fvarId_174_);
v___x_179_ = lean_st_ref_get(v___y_175_);
v_mctx_205_ = lean_ctor_get(v___x_179_, 0);
lean_inc_ref_n(v_mctx_205_, 2);
lean_dec(v___x_179_);
v___x_206_ = lean_obj_once(&l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2, &l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2_once, _init_l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg___closed__2);
v___x_207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
lean_ctor_set(v___x_207_, 1, v_mctx_205_);
v___x_208_ = l_Lean_Expr_hasFVar(v_e_173_);
if (v___x_208_ == 0)
{
uint8_t v___x_209_; 
v___x_209_ = l_Lean_Expr_hasMVar(v_e_173_);
if (v___x_209_ == 0)
{
lean_dec_ref_known(v___x_207_, 2);
lean_dec_ref(v___f_178_);
lean_dec_ref(v_e_173_);
v_fst_181_ = v___x_209_;
v_mctx_182_ = v_mctx_205_;
goto v___jp_180_;
}
else
{
lean_object* v___x_210_; 
lean_dec_ref(v_mctx_205_);
v___x_210_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_178_, v___f_177_, v_e_173_, v___x_207_);
v___y_200_ = v___x_210_;
goto v___jp_199_;
}
}
else
{
lean_object* v___x_211_; 
lean_dec_ref(v_mctx_205_);
v___x_211_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_178_, v___f_177_, v_e_173_, v___x_207_);
v___y_200_ = v___x_211_;
goto v___jp_199_;
}
v___jp_180_:
{
lean_object* v___x_183_; lean_object* v_cache_184_; lean_object* v_zetaDeltaFVarIds_185_; lean_object* v_postponed_186_; lean_object* v_diag_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_197_; 
v___x_183_ = lean_st_ref_take(v___y_175_);
v_cache_184_ = lean_ctor_get(v___x_183_, 1);
v_zetaDeltaFVarIds_185_ = lean_ctor_get(v___x_183_, 2);
v_postponed_186_ = lean_ctor_get(v___x_183_, 3);
v_diag_187_ = lean_ctor_get(v___x_183_, 4);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_197_ == 0)
{
lean_object* v_unused_198_; 
v_unused_198_ = lean_ctor_get(v___x_183_, 0);
lean_dec(v_unused_198_);
v___x_189_ = v___x_183_;
v_isShared_190_ = v_isSharedCheck_197_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_diag_187_);
lean_inc(v_postponed_186_);
lean_inc(v_zetaDeltaFVarIds_185_);
lean_inc(v_cache_184_);
lean_dec(v___x_183_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_197_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_192_; 
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 0, v_mctx_182_);
v___x_192_ = v___x_189_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_mctx_182_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v_cache_184_);
lean_ctor_set(v_reuseFailAlloc_196_, 2, v_zetaDeltaFVarIds_185_);
lean_ctor_set(v_reuseFailAlloc_196_, 3, v_postponed_186_);
lean_ctor_set(v_reuseFailAlloc_196_, 4, v_diag_187_);
v___x_192_ = v_reuseFailAlloc_196_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_193_ = lean_st_ref_put(v___y_175_, v___x_192_);
v___x_194_ = lean_box(v_fst_181_);
v___x_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
return v___x_195_;
}
}
}
v___jp_199_:
{
lean_object* v_snd_201_; lean_object* v_fst_202_; lean_object* v_mctx_203_; uint8_t v___x_204_; 
v_snd_201_ = lean_ctor_get(v___y_200_, 1);
lean_inc(v_snd_201_);
v_fst_202_ = lean_ctor_get(v___y_200_, 0);
lean_inc(v_fst_202_);
lean_dec_ref(v___y_200_);
v_mctx_203_ = lean_ctor_get(v_snd_201_, 1);
lean_inc_ref(v_mctx_203_);
lean_dec(v_snd_201_);
v___x_204_ = lean_unbox(v_fst_202_);
lean_dec(v_fst_202_);
v_fst_181_ = v___x_204_;
v_mctx_182_ = v_mctx_203_;
goto v___jp_180_;
}
}
}
LEAN_EXPORT void l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_173_ = stack[0].m_obj;
lean_object* v_fvarId_174_ = stack[1].m_obj;
lean_object* v___y_175_ = stack[2].m_obj;
lean_object* v_res_212_;
v_res_212_ = l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3___redArg(v_e_173_, v_fvarId_174_, v___y_175_);
stack->m_obj
 = v_res_212_;
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3___redArg___boxed(lean_object* v_e_213_, lean_object* v_fvarId_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3___redArg(v_e_213_, v_fvarId_214_, v___y_215_);
lean_dec(v___y_215_);
return v_res_217_;
}
}
lean_object* l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3(lean_object* v_e_218_, lean_object* v_fvarId_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3___redArg(v_e_218_, v_fvarId_219_, v___y_221_);
return v___x_225_;
}
}
LEAN_EXPORT void l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_218_ = stack[0].m_obj;
lean_object* v_fvarId_219_ = stack[1].m_obj;
lean_object* v___y_220_ = stack[2].m_obj;
lean_object* v___y_221_ = stack[3].m_obj;
lean_object* v___y_222_ = stack[4].m_obj;
lean_object* v___y_223_ = stack[5].m_obj;
lean_object* v_res_226_;
v_res_226_ = l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3(v_e_218_, v_fvarId_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
stack->m_obj
 = v_res_226_;
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3___boxed(lean_object* v_e_227_, lean_object* v_fvarId_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3(v_e_227_, v_fvarId_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
lean_dec(v___y_230_);
lean_dec_ref(v___y_229_);
return v_res_234_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg(lean_object* v_mvarId_235_, lean_object* v_x_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_235_, v_x_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_250_; 
v_a_243_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_250_ == 0)
{
v___x_245_ = v___x_242_;
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_242_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_248_; 
if (v_isShared_246_ == 0)
{
v___x_248_ = v___x_245_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_a_243_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
}
else
{
lean_object* v_a_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_258_; 
v_a_251_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_258_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_258_ == 0)
{
v___x_253_ = v___x_242_;
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_a_251_);
lean_dec(v___x_242_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_256_; 
if (v_isShared_254_ == 0)
{
v___x_256_ = v___x_253_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_a_251_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_235_ = stack[0].m_obj;
lean_object* v_x_236_ = stack[1].m_obj;
lean_object* v___y_237_ = stack[2].m_obj;
lean_object* v___y_238_ = stack[3].m_obj;
lean_object* v___y_239_ = stack[4].m_obj;
lean_object* v___y_240_ = stack[5].m_obj;
lean_object* v_res_259_;
v_res_259_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg(v_mvarId_235_, v_x_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_);
stack->m_obj
 = v_res_259_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg___boxed(lean_object* v_mvarId_260_, lean_object* v_x_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg(v_mvarId_260_, v_x_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
return v_res_267_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4(lean_object* v_00_u03b1_268_, lean_object* v_mvarId_269_, lean_object* v_x_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg(v_mvarId_269_, v_x_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_);
return v___x_276_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_269_ = stack[1].m_obj;
lean_object* v_x_270_ = stack[2].m_obj;
lean_object* v___y_271_ = stack[3].m_obj;
lean_object* v___y_272_ = stack[4].m_obj;
lean_object* v___y_273_ = stack[5].m_obj;
lean_object* v___y_274_ = stack[6].m_obj;
lean_object* v_res_277_;
v_res_277_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4(lean_box(0), v_mvarId_269_, v_x_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_);
stack->m_obj
 = v_res_277_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___boxed(lean_object* v_00_u03b1_278_, lean_object* v_mvarId_279_, lean_object* v_x_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4(v_00_u03b1_278_, v_mvarId_279_, v_x_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_);
lean_dec(v___y_284_);
lean_dec_ref(v___y_283_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
return v_res_286_;
}
}
uint8_t l_Lean_MVarId_clear___lam__0(lean_object* v_fvarId_287_, lean_object* v_localInst_288_){
_start:
{
lean_object* v_fvar_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
v_fvar_289_ = lean_ctor_get(v_localInst_288_, 1);
v___x_290_ = l_Lean_Expr_fvarId_x21(v_fvar_289_);
v___x_291_ = l_Lean_instBEqFVarId_beq(v___x_290_, v_fvarId_287_);
lean_dec(v___x_290_);
return v___x_291_;
}
}
LEAN_EXPORT void l_Lean_MVarId_clear___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_287_ = stack[0].m_obj;
lean_object* v_localInst_288_ = stack[1].m_obj;
uint8_t v_res_292_;
v_res_292_ = l_Lean_MVarId_clear___lam__0(v_fvarId_287_, v_localInst_288_);
stack->m_num = v_res_292_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clear___lam__0___boxed(lean_object* v_fvarId_293_, lean_object* v_localInst_294_){
_start:
{
uint8_t v_res_295_; lean_object* v_r_296_; 
v_res_295_ = l_Lean_MVarId_clear___lam__0(v_fvarId_293_, v_localInst_294_);
lean_dec_ref(v_localInst_294_);
lean_dec(v_fvarId_293_);
v_r_296_ = lean_box(v_res_295_);
return v_r_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13_spec__14___redArg(lean_object* v_x_297_, lean_object* v_x_298_, lean_object* v_x_299_, lean_object* v_x_300_){
_start:
{
lean_object* v_ks_301_; lean_object* v_vs_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_326_; 
v_ks_301_ = lean_ctor_get(v_x_297_, 0);
v_vs_302_ = lean_ctor_get(v_x_297_, 1);
v_isSharedCheck_326_ = !lean_is_exclusive(v_x_297_);
if (v_isSharedCheck_326_ == 0)
{
v___x_304_ = v_x_297_;
v_isShared_305_ = v_isSharedCheck_326_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_vs_302_);
lean_inc(v_ks_301_);
lean_dec(v_x_297_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_326_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_306_; uint8_t v___x_307_; 
v___x_306_ = lean_array_get_size(v_ks_301_);
v___x_307_ = lean_nat_dec_lt(v_x_298_, v___x_306_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_311_; 
lean_dec(v_x_298_);
v___x_308_ = lean_array_push(v_ks_301_, v_x_299_);
v___x_309_ = lean_array_push(v_vs_302_, v_x_300_);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 1, v___x_309_);
lean_ctor_set(v___x_304_, 0, v___x_308_);
v___x_311_ = v___x_304_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_308_);
lean_ctor_set(v_reuseFailAlloc_312_, 1, v___x_309_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
else
{
lean_object* v_k_x27_313_; uint8_t v___x_314_; 
v_k_x27_313_ = lean_array_fget_borrowed(v_ks_301_, v_x_298_);
v___x_314_ = l_Lean_instBEqMVarId_beq(v_x_299_, v_k_x27_313_);
if (v___x_314_ == 0)
{
lean_object* v___x_316_; 
if (v_isShared_305_ == 0)
{
v___x_316_ = v___x_304_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_ks_301_);
lean_ctor_set(v_reuseFailAlloc_320_, 1, v_vs_302_);
v___x_316_ = v_reuseFailAlloc_320_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = lean_unsigned_to_nat(1u);
v___x_318_ = lean_nat_add(v_x_298_, v___x_317_);
lean_dec(v_x_298_);
v_x_297_ = v___x_316_;
v_x_298_ = v___x_318_;
goto _start;
}
}
else
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_324_; 
v___x_321_ = lean_array_fset(v_ks_301_, v_x_298_, v_x_299_);
v___x_322_ = lean_array_fset(v_vs_302_, v_x_298_, v_x_300_);
lean_dec(v_x_298_);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 1, v___x_322_);
lean_ctor_set(v___x_304_, 0, v___x_321_);
v___x_324_ = v___x_304_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v___x_321_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v___x_322_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13___redArg(lean_object* v_n_327_, lean_object* v_k_328_, lean_object* v_v_329_){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = lean_unsigned_to_nat(0u);
v___x_331_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13_spec__14___redArg(v_n_327_, v___x_330_, v_k_328_, v_v_329_);
return v___x_331_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_332_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(lean_object* v_x_333_, size_t v_x_334_, size_t v_x_335_, lean_object* v_x_336_, lean_object* v_x_337_){
_start:
{
if (lean_obj_tag(v_x_333_) == 0)
{
lean_object* v_es_338_; size_t v___x_339_; size_t v___x_340_; lean_object* v_j_341_; lean_object* v___x_342_; uint8_t v___x_343_; 
v_es_338_ = lean_ctor_get(v_x_333_, 0);
v___x_339_ = ((size_t)31ULL);
v___x_340_ = lean_usize_land(v_x_334_, v___x_339_);
v_j_341_ = lean_usize_to_nat(v___x_340_);
v___x_342_ = lean_array_get_size(v_es_338_);
v___x_343_ = lean_nat_dec_lt(v_j_341_, v___x_342_);
if (v___x_343_ == 0)
{
lean_dec(v_j_341_);
lean_dec(v_x_337_);
lean_dec(v_x_336_);
return v_x_333_;
}
else
{
lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_382_; 
lean_inc_ref(v_es_338_);
v_isSharedCheck_382_ = !lean_is_exclusive(v_x_333_);
if (v_isSharedCheck_382_ == 0)
{
lean_object* v_unused_383_; 
v_unused_383_ = lean_ctor_get(v_x_333_, 0);
lean_dec(v_unused_383_);
v___x_345_ = v_x_333_;
v_isShared_346_ = v_isSharedCheck_382_;
goto v_resetjp_344_;
}
else
{
lean_dec(v_x_333_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_382_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v_v_347_; lean_object* v___x_348_; lean_object* v_xs_x27_349_; lean_object* v___y_351_; 
v_v_347_ = lean_array_fget(v_es_338_, v_j_341_);
v___x_348_ = lean_box(0);
v_xs_x27_349_ = lean_array_fset(v_es_338_, v_j_341_, v___x_348_);
switch(lean_obj_tag(v_v_347_))
{
case 0:
{
lean_object* v_key_356_; lean_object* v_val_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_367_; 
v_key_356_ = lean_ctor_get(v_v_347_, 0);
v_val_357_ = lean_ctor_get(v_v_347_, 1);
v_isSharedCheck_367_ = !lean_is_exclusive(v_v_347_);
if (v_isSharedCheck_367_ == 0)
{
v___x_359_ = v_v_347_;
v_isShared_360_ = v_isSharedCheck_367_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_val_357_);
lean_inc(v_key_356_);
lean_dec(v_v_347_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_367_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
uint8_t v___x_361_; 
v___x_361_ = l_Lean_instBEqMVarId_beq(v_x_336_, v_key_356_);
if (v___x_361_ == 0)
{
lean_object* v___x_362_; lean_object* v___x_363_; 
lean_del_object(v___x_359_);
v___x_362_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_356_, v_val_357_, v_x_336_, v_x_337_);
v___x_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
v___y_351_ = v___x_363_;
goto v___jp_350_;
}
else
{
lean_object* v___x_365_; 
lean_dec(v_val_357_);
lean_dec(v_key_356_);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 1, v_x_337_);
lean_ctor_set(v___x_359_, 0, v_x_336_);
v___x_365_ = v___x_359_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_x_336_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v_x_337_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
v___y_351_ = v___x_365_;
goto v___jp_350_;
}
}
}
}
case 1:
{
lean_object* v_node_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_380_; 
v_node_368_ = lean_ctor_get(v_v_347_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v_v_347_);
if (v_isSharedCheck_380_ == 0)
{
v___x_370_ = v_v_347_;
v_isShared_371_ = v_isSharedCheck_380_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_node_368_);
lean_dec(v_v_347_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_380_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
size_t v___x_372_; size_t v___x_373_; size_t v___x_374_; size_t v___x_375_; lean_object* v___x_376_; lean_object* v___x_378_; 
v___x_372_ = ((size_t)5ULL);
v___x_373_ = lean_usize_shift_right(v_x_334_, v___x_372_);
v___x_374_ = ((size_t)1ULL);
v___x_375_ = lean_usize_add(v_x_335_, v___x_374_);
v___x_376_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_node_368_, v___x_373_, v___x_375_, v_x_336_, v_x_337_);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 0, v___x_376_);
v___x_378_ = v___x_370_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v___x_376_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
v___y_351_ = v___x_378_;
goto v___jp_350_;
}
}
}
default: 
{
lean_object* v___x_381_; 
v___x_381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_381_, 0, v_x_336_);
lean_ctor_set(v___x_381_, 1, v_x_337_);
v___y_351_ = v___x_381_;
goto v___jp_350_;
}
}
v___jp_350_:
{
lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_352_ = lean_array_fset(v_xs_x27_349_, v_j_341_, v___y_351_);
lean_dec(v_j_341_);
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 0, v___x_352_);
v___x_354_ = v___x_345_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v___x_352_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
}
}
else
{
lean_object* v_ks_384_; lean_object* v_vs_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_403_; 
v_ks_384_ = lean_ctor_get(v_x_333_, 0);
v_vs_385_ = lean_ctor_get(v_x_333_, 1);
v_isSharedCheck_403_ = !lean_is_exclusive(v_x_333_);
if (v_isSharedCheck_403_ == 0)
{
v___x_387_ = v_x_333_;
v_isShared_388_ = v_isSharedCheck_403_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_vs_385_);
lean_inc(v_ks_384_);
lean_dec(v_x_333_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_403_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_ks_384_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v_vs_385_);
v___x_390_ = v_reuseFailAlloc_402_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
lean_object* v_newNode_391_; size_t v___x_392_; uint8_t v___x_393_; 
v_newNode_391_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13___redArg(v___x_390_, v_x_336_, v_x_337_);
v___x_392_ = ((size_t)7ULL);
v___x_393_ = lean_usize_dec_le(v___x_392_, v_x_335_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; lean_object* v___x_395_; uint8_t v___x_396_; 
v___x_394_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_391_);
v___x_395_ = lean_unsigned_to_nat(4u);
v___x_396_ = lean_nat_dec_lt(v___x_394_, v___x_395_);
lean_dec(v___x_394_);
if (v___x_396_ == 0)
{
lean_object* v_ks_397_; lean_object* v_vs_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v_ks_397_ = lean_ctor_get(v_newNode_391_, 0);
lean_inc_ref(v_ks_397_);
v_vs_398_ = lean_ctor_get(v_newNode_391_, 1);
lean_inc_ref(v_vs_398_);
lean_dec_ref(v_newNode_391_);
v___x_399_ = lean_unsigned_to_nat(0u);
v___x_400_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__0);
v___x_401_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg(v_x_335_, v_ks_397_, v_vs_398_, v___x_399_, v___x_400_);
lean_dec_ref(v_vs_398_);
lean_dec_ref(v_ks_397_);
return v___x_401_;
}
else
{
return v_newNode_391_;
}
}
else
{
return v_newNode_391_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_333_ = stack[0].m_obj;
size_t v_x_334_ = stack[1].m_num;
size_t v_x_335_ = stack[2].m_num;
lean_object* v_x_336_ = stack[3].m_obj;
lean_object* v_x_337_ = stack[4].m_obj;
lean_object* v_res_404_;
v_res_404_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_x_333_, v_x_334_, v_x_335_, v_x_336_, v_x_337_);
stack->m_obj
 = v_res_404_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg(size_t v_depth_405_, lean_object* v_keys_406_, lean_object* v_vals_407_, lean_object* v_i_408_, lean_object* v_entries_409_){
_start:
{
lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_410_ = lean_array_get_size(v_keys_406_);
v___x_411_ = lean_nat_dec_lt(v_i_408_, v___x_410_);
if (v___x_411_ == 0)
{
lean_dec(v_i_408_);
return v_entries_409_;
}
else
{
lean_object* v_k_412_; lean_object* v_v_413_; uint64_t v___x_414_; size_t v_h_415_; size_t v___x_416_; lean_object* v___x_417_; size_t v___x_418_; size_t v___x_419_; size_t v___x_420_; size_t v_h_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v_k_412_ = lean_array_fget_borrowed(v_keys_406_, v_i_408_);
v_v_413_ = lean_array_fget_borrowed(v_vals_407_, v_i_408_);
v___x_414_ = l_Lean_instHashableMVarId_hash(v_k_412_);
v_h_415_ = lean_uint64_to_usize(v___x_414_);
v___x_416_ = ((size_t)5ULL);
v___x_417_ = lean_unsigned_to_nat(1u);
v___x_418_ = ((size_t)1ULL);
v___x_419_ = lean_usize_sub(v_depth_405_, v___x_418_);
v___x_420_ = lean_usize_mul(v___x_416_, v___x_419_);
v_h_421_ = lean_usize_shift_right(v_h_415_, v___x_420_);
v___x_422_ = lean_nat_add(v_i_408_, v___x_417_);
lean_dec(v_i_408_);
lean_inc(v_v_413_);
lean_inc(v_k_412_);
v___x_423_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_entries_409_, v_h_421_, v_depth_405_, v_k_412_, v_v_413_);
v_i_408_ = v___x_422_;
v_entries_409_ = v___x_423_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_405_ = stack[0].m_num;
lean_object* v_keys_406_ = stack[1].m_obj;
lean_object* v_vals_407_ = stack[2].m_obj;
lean_object* v_i_408_ = stack[3].m_obj;
lean_object* v_entries_409_ = stack[4].m_obj;
lean_object* v_res_425_;
v_res_425_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg(v_depth_405_, v_keys_406_, v_vals_407_, v_i_408_, v_entries_409_);
stack->m_obj
 = v_res_425_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg___boxed(lean_object* v_depth_426_, lean_object* v_keys_427_, lean_object* v_vals_428_, lean_object* v_i_429_, lean_object* v_entries_430_){
_start:
{
size_t v_depth_boxed_431_; lean_object* v_res_432_; 
v_depth_boxed_431_ = lean_unbox_usize(v_depth_426_);
lean_dec(v_depth_426_);
v_res_432_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg(v_depth_boxed_431_, v_keys_427_, v_vals_428_, v_i_429_, v_entries_430_);
lean_dec_ref(v_vals_428_);
lean_dec_ref(v_keys_427_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___boxed(lean_object* v_x_433_, lean_object* v_x_434_, lean_object* v_x_435_, lean_object* v_x_436_, lean_object* v_x_437_){
_start:
{
size_t v_x_8165__boxed_438_; size_t v_x_8166__boxed_439_; lean_object* v_res_440_; 
v_x_8165__boxed_438_ = lean_unbox_usize(v_x_434_);
lean_dec(v_x_434_);
v_x_8166__boxed_439_ = lean_unbox_usize(v_x_435_);
lean_dec(v_x_435_);
v_res_440_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_x_433_, v_x_8165__boxed_438_, v_x_8166__boxed_439_, v_x_436_, v_x_437_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3___redArg(lean_object* v_x_441_, lean_object* v_x_442_, lean_object* v_x_443_){
_start:
{
uint64_t v___x_444_; size_t v___x_445_; size_t v___x_446_; lean_object* v___x_447_; 
v___x_444_ = l_Lean_instHashableMVarId_hash(v_x_442_);
v___x_445_ = lean_uint64_to_usize(v___x_444_);
v___x_446_ = ((size_t)1ULL);
v___x_447_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_x_441_, v___x_445_, v___x_446_, v_x_442_, v_x_443_);
return v___x_447_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg(lean_object* v_mvarId_448_, lean_object* v_val_449_, lean_object* v___y_450_){
_start:
{
lean_object* v___x_452_; lean_object* v_mctx_453_; lean_object* v_cache_454_; lean_object* v_zetaDeltaFVarIds_455_; lean_object* v_postponed_456_; lean_object* v_diag_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_487_; 
v___x_452_ = lean_st_ref_take(v___y_450_);
v_mctx_453_ = lean_ctor_get(v___x_452_, 0);
v_cache_454_ = lean_ctor_get(v___x_452_, 1);
v_zetaDeltaFVarIds_455_ = lean_ctor_get(v___x_452_, 2);
v_postponed_456_ = lean_ctor_get(v___x_452_, 3);
v_diag_457_ = lean_ctor_get(v___x_452_, 4);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_487_ == 0)
{
v___x_459_ = v___x_452_;
v_isShared_460_ = v_isSharedCheck_487_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_diag_457_);
lean_inc(v_postponed_456_);
lean_inc(v_zetaDeltaFVarIds_455_);
lean_inc(v_cache_454_);
lean_inc(v_mctx_453_);
lean_dec(v___x_452_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_487_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v_depth_461_; lean_object* v_levelAssignDepth_462_; lean_object* v_lmvarCounter_463_; lean_object* v_mvarCounter_464_; lean_object* v_lDecls_465_; lean_object* v_decls_466_; lean_object* v_userNames_467_; lean_object* v_lAssignment_468_; lean_object* v_eAssignment_469_; lean_object* v_dAssignment_470_; lean_object* v_instanceTypedMVars_471_; lean_object* v_synthNormMemo_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_486_; 
v_depth_461_ = lean_ctor_get(v_mctx_453_, 0);
v_levelAssignDepth_462_ = lean_ctor_get(v_mctx_453_, 1);
v_lmvarCounter_463_ = lean_ctor_get(v_mctx_453_, 2);
v_mvarCounter_464_ = lean_ctor_get(v_mctx_453_, 3);
v_lDecls_465_ = lean_ctor_get(v_mctx_453_, 4);
v_decls_466_ = lean_ctor_get(v_mctx_453_, 5);
v_userNames_467_ = lean_ctor_get(v_mctx_453_, 6);
v_lAssignment_468_ = lean_ctor_get(v_mctx_453_, 7);
v_eAssignment_469_ = lean_ctor_get(v_mctx_453_, 8);
v_dAssignment_470_ = lean_ctor_get(v_mctx_453_, 9);
v_instanceTypedMVars_471_ = lean_ctor_get(v_mctx_453_, 10);
v_synthNormMemo_472_ = lean_ctor_get(v_mctx_453_, 11);
v_isSharedCheck_486_ = !lean_is_exclusive(v_mctx_453_);
if (v_isSharedCheck_486_ == 0)
{
v___x_474_ = v_mctx_453_;
v_isShared_475_ = v_isSharedCheck_486_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_synthNormMemo_472_);
lean_inc(v_instanceTypedMVars_471_);
lean_inc(v_dAssignment_470_);
lean_inc(v_eAssignment_469_);
lean_inc(v_lAssignment_468_);
lean_inc(v_userNames_467_);
lean_inc(v_decls_466_);
lean_inc(v_lDecls_465_);
lean_inc(v_mvarCounter_464_);
lean_inc(v_lmvarCounter_463_);
lean_inc(v_levelAssignDepth_462_);
lean_inc(v_depth_461_);
lean_dec(v_mctx_453_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_486_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_479_; 
v___x_476_ = lean_box(0);
v___x_477_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3___redArg(v_eAssignment_469_, v_mvarId_448_, v_val_449_);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 8, v___x_477_);
v___x_479_ = v___x_474_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_depth_461_);
lean_ctor_set(v_reuseFailAlloc_485_, 1, v_levelAssignDepth_462_);
lean_ctor_set(v_reuseFailAlloc_485_, 2, v_lmvarCounter_463_);
lean_ctor_set(v_reuseFailAlloc_485_, 3, v_mvarCounter_464_);
lean_ctor_set(v_reuseFailAlloc_485_, 4, v_lDecls_465_);
lean_ctor_set(v_reuseFailAlloc_485_, 5, v_decls_466_);
lean_ctor_set(v_reuseFailAlloc_485_, 6, v_userNames_467_);
lean_ctor_set(v_reuseFailAlloc_485_, 7, v_lAssignment_468_);
lean_ctor_set(v_reuseFailAlloc_485_, 8, v___x_477_);
lean_ctor_set(v_reuseFailAlloc_485_, 9, v_dAssignment_470_);
lean_ctor_set(v_reuseFailAlloc_485_, 10, v_instanceTypedMVars_471_);
lean_ctor_set(v_reuseFailAlloc_485_, 11, v_synthNormMemo_472_);
v___x_479_ = v_reuseFailAlloc_485_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
lean_object* v___x_481_; 
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 0, v___x_479_);
v___x_481_ = v___x_459_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_479_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v_cache_454_);
lean_ctor_set(v_reuseFailAlloc_484_, 2, v_zetaDeltaFVarIds_455_);
lean_ctor_set(v_reuseFailAlloc_484_, 3, v_postponed_456_);
lean_ctor_set(v_reuseFailAlloc_484_, 4, v_diag_457_);
v___x_481_ = v_reuseFailAlloc_484_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = lean_st_ref_put(v___y_450_, v___x_481_);
v___x_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_483_, 0, v___x_476_);
return v___x_483_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_448_ = stack[0].m_obj;
lean_object* v_val_449_ = stack[1].m_obj;
lean_object* v___y_450_ = stack[2].m_obj;
lean_object* v_res_488_;
v_res_488_ = l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg(v_mvarId_448_, v_val_449_, v___y_450_);
stack->m_obj
 = v_res_488_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg___boxed(lean_object* v_mvarId_489_, lean_object* v_val_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg(v_mvarId_489_, v_val_490_, v___y_491_);
lean_dec(v___y_491_);
return v_res_493_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__2));
v___x_499_ = l_Lean_stringToMessageData(v___x_498_);
return v___x_499_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5(void){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__4));
v___x_502_ = l_Lean_stringToMessageData(v___x_501_);
return v___x_502_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__6));
v___x_505_ = l_Lean_stringToMessageData(v___x_504_);
return v___x_505_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9(lean_object* v_fvarId_506_, lean_object* v_mvarId_507_, lean_object* v_as_508_, size_t v_i_509_, size_t v_stop_510_, lean_object* v_b_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
lean_object* v_a_518_; uint8_t v___x_522_; 
v___x_522_ = lean_usize_dec_eq(v_i_509_, v_stop_510_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; 
v___x_523_ = lean_array_uget(v_as_508_, v_i_509_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v___x_524_; 
v___x_524_ = lean_box(0);
v_a_518_ = v___x_524_;
goto v___jp_517_;
}
else
{
lean_object* v_val_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_562_; 
v_val_525_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_562_ == 0)
{
v___x_527_ = v___x_523_;
v_isShared_528_ = v_isSharedCheck_562_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_val_525_);
lean_dec(v___x_523_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_562_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_529_; uint8_t v___x_530_; 
v___x_529_ = l_Lean_LocalDecl_fvarId(v_val_525_);
v___x_530_ = l_Lean_instBEqFVarId_beq(v___x_529_, v_fvarId_506_);
lean_dec(v___x_529_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; uint8_t v___x_532_; lean_object* v___x_533_; 
v___x_531_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__1));
v___x_532_ = 1;
lean_inc(v_fvarId_506_);
lean_inc(v_val_525_);
v___x_533_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg(v_val_525_, v_fvarId_506_, v___x_532_, v___y_513_);
if (lean_obj_tag(v___x_533_) == 0)
{
lean_object* v_a_534_; uint8_t v___x_535_; 
v_a_534_ = lean_ctor_get(v___x_533_, 0);
lean_inc(v_a_534_);
lean_dec_ref_known(v___x_533_, 1);
v___x_535_ = lean_unbox(v_a_534_);
lean_dec(v_a_534_);
if (v___x_535_ == 0)
{
lean_object* v___x_536_; 
lean_del_object(v___x_527_);
lean_dec(v_val_525_);
v___x_536_ = lean_box(0);
v_a_518_ = v___x_536_;
goto v___jp_517_;
}
else
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_549_; 
v___x_537_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3);
v___x_538_ = l_Lean_LocalDecl_toExpr(v_val_525_);
v___x_539_ = l_Lean_MessageData_ofExpr(v___x_538_);
v___x_540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_540_, 0, v___x_537_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
v___x_541_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5);
v___x_542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_540_);
lean_ctor_set(v___x_542_, 1, v___x_541_);
lean_inc(v_fvarId_506_);
v___x_543_ = l_Lean_mkFVar(v_fvarId_506_);
v___x_544_ = l_Lean_MessageData_ofExpr(v___x_543_);
v___x_545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_542_);
lean_ctor_set(v___x_545_, 1, v___x_544_);
v___x_546_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7);
v___x_547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_547_, 0, v___x_545_);
lean_ctor_set(v___x_547_, 1, v___x_546_);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 0, v___x_547_);
v___x_549_ = v___x_527_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_547_);
v___x_549_ = v_reuseFailAlloc_552_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
lean_object* v___x_550_; 
lean_inc(v_mvarId_507_);
v___x_550_ = l_Lean_Meta_throwTacticEx___redArg(v___x_531_, v_mvarId_507_, v___x_549_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
if (lean_obj_tag(v___x_550_) == 0)
{
lean_object* v_a_551_; 
v_a_551_ = lean_ctor_get(v___x_550_, 0);
lean_inc(v_a_551_);
lean_dec_ref_known(v___x_550_, 1);
v_a_518_ = v_a_551_;
goto v___jp_517_;
}
else
{
lean_dec(v_mvarId_507_);
lean_dec(v_fvarId_506_);
return v___x_550_;
}
}
}
}
else
{
lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_560_; 
lean_del_object(v___x_527_);
lean_dec(v_val_525_);
lean_dec(v_mvarId_507_);
lean_dec(v_fvarId_506_);
v_a_553_ = lean_ctor_get(v___x_533_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_560_ == 0)
{
v___x_555_ = v___x_533_;
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_533_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_558_; 
if (v_isShared_556_ == 0)
{
v___x_558_ = v___x_555_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_a_553_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
else
{
lean_object* v___x_561_; 
lean_del_object(v___x_527_);
lean_dec(v_val_525_);
v___x_561_ = lean_box(0);
v_a_518_ = v___x_561_;
goto v___jp_517_;
}
}
}
}
else
{
lean_object* v___x_563_; 
lean_dec(v_mvarId_507_);
lean_dec(v_fvarId_506_);
v___x_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_563_, 0, v_b_511_);
return v___x_563_;
}
v___jp_517_:
{
size_t v___x_519_; size_t v___x_520_; 
v___x_519_ = ((size_t)1ULL);
v___x_520_ = lean_usize_add(v_i_509_, v___x_519_);
v_i_509_ = v___x_520_;
v_b_511_ = v_a_518_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_506_ = stack[0].m_obj;
lean_object* v_mvarId_507_ = stack[1].m_obj;
lean_object* v_as_508_ = stack[2].m_obj;
size_t v_i_509_ = stack[3].m_num;
size_t v_stop_510_ = stack[4].m_num;
lean_object* v_b_511_ = stack[5].m_obj;
lean_object* v___y_512_ = stack[6].m_obj;
lean_object* v___y_513_ = stack[7].m_obj;
lean_object* v___y_514_ = stack[8].m_obj;
lean_object* v___y_515_ = stack[9].m_obj;
lean_object* v_res_564_;
v_res_564_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9(v_fvarId_506_, v_mvarId_507_, v_as_508_, v_i_509_, v_stop_510_, v_b_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
stack->m_obj
 = v_res_564_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___boxed(lean_object* v_fvarId_565_, lean_object* v_mvarId_566_, lean_object* v_as_567_, lean_object* v_i_568_, lean_object* v_stop_569_, lean_object* v_b_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
size_t v_i_boxed_576_; size_t v_stop_boxed_577_; lean_object* v_res_578_; 
v_i_boxed_576_ = lean_unbox_usize(v_i_568_);
lean_dec(v_i_568_);
v_stop_boxed_577_ = lean_unbox_usize(v_stop_569_);
lean_dec(v_stop_569_);
v_res_578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9(v_fvarId_565_, v_mvarId_566_, v_as_567_, v_i_boxed_576_, v_stop_boxed_577_, v_b_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec_ref(v_as_567_);
return v_res_578_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(lean_object* v_fvarId_579_, lean_object* v_mvarId_580_, lean_object* v_as_581_, size_t v_i_582_, size_t v_stop_583_, lean_object* v_b_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_){
_start:
{
lean_object* v_a_591_; uint8_t v___x_595_; 
v___x_595_ = lean_usize_dec_eq(v_i_582_, v_stop_583_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; 
v___x_596_ = lean_array_uget(v_as_581_, v_i_582_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v___x_597_; 
v___x_597_ = lean_box(0);
v_a_591_ = v___x_597_;
goto v___jp_590_;
}
else
{
lean_object* v_val_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_635_; 
v_val_598_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_635_ == 0)
{
v___x_600_ = v___x_596_;
v_isShared_601_ = v_isSharedCheck_635_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_val_598_);
lean_dec(v___x_596_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_635_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_602_; uint8_t v___x_603_; 
v___x_602_ = l_Lean_LocalDecl_fvarId(v_val_598_);
v___x_603_ = l_Lean_instBEqFVarId_beq(v___x_602_, v_fvarId_579_);
lean_dec(v___x_602_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; uint8_t v___x_605_; lean_object* v___x_606_; 
v___x_604_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__1));
v___x_605_ = 1;
lean_inc(v_fvarId_579_);
lean_inc(v_val_598_);
v___x_606_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg(v_val_598_, v_fvarId_579_, v___x_605_, v___y_586_);
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
lean_object* v___x_609_; 
lean_del_object(v___x_600_);
lean_dec(v_val_598_);
v___x_609_ = lean_box(0);
v_a_591_ = v___x_609_;
goto v___jp_590_;
}
else
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_622_; 
v___x_610_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3);
v___x_611_ = l_Lean_LocalDecl_toExpr(v_val_598_);
v___x_612_ = l_Lean_MessageData_ofExpr(v___x_611_);
v___x_613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_610_);
lean_ctor_set(v___x_613_, 1, v___x_612_);
v___x_614_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5);
v___x_615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_613_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
lean_inc(v_fvarId_579_);
v___x_616_ = l_Lean_mkFVar(v_fvarId_579_);
v___x_617_ = l_Lean_MessageData_ofExpr(v___x_616_);
v___x_618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_618_, 0, v___x_615_);
lean_ctor_set(v___x_618_, 1, v___x_617_);
v___x_619_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7);
v___x_620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_618_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 0, v___x_620_);
v___x_622_ = v___x_600_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_620_);
v___x_622_ = v_reuseFailAlloc_625_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
lean_object* v___x_623_; 
lean_inc(v_mvarId_580_);
v___x_623_ = l_Lean_Meta_throwTacticEx___redArg(v___x_604_, v_mvarId_580_, v___x_622_, v___y_585_, v___y_586_, v___y_587_, v___y_588_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v_a_624_; 
v_a_624_ = lean_ctor_get(v___x_623_, 0);
lean_inc(v_a_624_);
lean_dec_ref_known(v___x_623_, 1);
v_a_591_ = v_a_624_;
goto v___jp_590_;
}
else
{
lean_dec(v_mvarId_580_);
lean_dec(v_fvarId_579_);
return v___x_623_;
}
}
}
}
else
{
lean_object* v_a_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_633_; 
lean_del_object(v___x_600_);
lean_dec(v_val_598_);
lean_dec(v_mvarId_580_);
lean_dec(v_fvarId_579_);
v_a_626_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_633_ == 0)
{
v___x_628_ = v___x_606_;
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_a_626_);
lean_dec(v___x_606_);
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
lean_object* v___x_634_; 
lean_del_object(v___x_600_);
lean_dec(v_val_598_);
v___x_634_ = lean_box(0);
v_a_591_ = v___x_634_;
goto v___jp_590_;
}
}
}
}
else
{
lean_object* v___x_636_; 
lean_dec(v_mvarId_580_);
lean_dec(v_fvarId_579_);
v___x_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_636_, 0, v_b_584_);
return v___x_636_;
}
v___jp_590_:
{
size_t v___x_592_; size_t v___x_593_; lean_object* v___x_594_; 
v___x_592_ = ((size_t)1ULL);
v___x_593_ = lean_usize_add(v_i_582_, v___x_592_);
v___x_594_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9(v_fvarId_579_, v_mvarId_580_, v_as_581_, v___x_593_, v_stop_583_, v_a_591_, v___y_585_, v___y_586_, v___y_587_, v___y_588_);
return v___x_594_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_579_ = stack[0].m_obj;
lean_object* v_mvarId_580_ = stack[1].m_obj;
lean_object* v_as_581_ = stack[2].m_obj;
size_t v_i_582_ = stack[3].m_num;
size_t v_stop_583_ = stack[4].m_num;
lean_object* v_b_584_ = stack[5].m_obj;
lean_object* v___y_585_ = stack[6].m_obj;
lean_object* v___y_586_ = stack[7].m_obj;
lean_object* v___y_587_ = stack[8].m_obj;
lean_object* v___y_588_ = stack[9].m_obj;
lean_object* v_res_637_;
v_res_637_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_579_, v_mvarId_580_, v_as_581_, v_i_582_, v_stop_583_, v_b_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_);
stack->m_obj
 = v_res_637_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5___boxed(lean_object* v_fvarId_638_, lean_object* v_mvarId_639_, lean_object* v_as_640_, lean_object* v_i_641_, lean_object* v_stop_642_, lean_object* v_b_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_){
_start:
{
size_t v_i_boxed_649_; size_t v_stop_boxed_650_; lean_object* v_res_651_; 
v_i_boxed_649_ = lean_unbox_usize(v_i_641_);
lean_dec(v_i_641_);
v_stop_boxed_650_ = lean_unbox_usize(v_stop_642_);
lean_dec(v_stop_642_);
v_res_651_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_638_, v_mvarId_639_, v_as_640_, v_i_boxed_649_, v_stop_boxed_650_, v_b_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec(v___y_645_);
lean_dec_ref(v___y_644_);
lean_dec_ref(v_as_640_);
return v_res_651_;
}
}
lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6(lean_object* v_fvarId_652_, lean_object* v_mvarId_653_, lean_object* v_x_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
if (lean_obj_tag(v_x_654_) == 0)
{
lean_object* v_cs_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_674_; 
v_cs_660_ = lean_ctor_get(v_x_654_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v_x_654_);
if (v_isSharedCheck_674_ == 0)
{
v___x_662_ = v_x_654_;
v_isShared_663_ = v_isSharedCheck_674_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_cs_660_);
lean_dec(v_x_654_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_674_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_664_ = lean_unsigned_to_nat(0u);
v___x_665_ = lean_array_get_size(v_cs_660_);
v___x_666_ = lean_box(0);
v___x_667_ = lean_nat_dec_lt(v___x_664_, v___x_665_);
if (v___x_667_ == 0)
{
lean_object* v___x_669_; 
lean_dec_ref(v_cs_660_);
lean_dec(v_mvarId_653_);
lean_dec(v_fvarId_652_);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 0, v___x_666_);
v___x_669_ = v___x_662_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_666_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
else
{
size_t v___x_671_; size_t v___x_672_; lean_object* v___x_673_; 
lean_del_object(v___x_662_);
v___x_671_ = ((size_t)0ULL);
v___x_672_ = lean_usize_of_nat(v___x_665_);
v___x_673_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(v_fvarId_652_, v_mvarId_653_, v_cs_660_, v___x_671_, v___x_672_, v___x_666_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
lean_dec_ref(v_cs_660_);
return v___x_673_;
}
}
}
else
{
lean_object* v_vs_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_689_; 
v_vs_675_ = lean_ctor_get(v_x_654_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v_x_654_);
if (v_isSharedCheck_689_ == 0)
{
v___x_677_ = v_x_654_;
v_isShared_678_ = v_isSharedCheck_689_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_vs_675_);
lean_dec(v_x_654_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_689_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; uint8_t v___x_682_; 
v___x_679_ = lean_unsigned_to_nat(0u);
v___x_680_ = lean_array_get_size(v_vs_675_);
v___x_681_ = lean_box(0);
v___x_682_ = lean_nat_dec_lt(v___x_679_, v___x_680_);
if (v___x_682_ == 0)
{
lean_object* v___x_684_; 
lean_dec_ref(v_vs_675_);
lean_dec(v_mvarId_653_);
lean_dec(v_fvarId_652_);
if (v_isShared_678_ == 0)
{
lean_ctor_set_tag(v___x_677_, 0);
lean_ctor_set(v___x_677_, 0, v___x_681_);
v___x_684_ = v___x_677_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_681_);
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
lean_del_object(v___x_677_);
v___x_686_ = ((size_t)0ULL);
v___x_687_ = lean_usize_of_nat(v___x_680_);
v___x_688_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_652_, v_mvarId_653_, v_vs_675_, v___x_686_, v___x_687_, v___x_681_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
lean_dec_ref(v_vs_675_);
return v___x_688_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_652_ = stack[0].m_obj;
lean_object* v_mvarId_653_ = stack[1].m_obj;
lean_object* v_x_654_ = stack[2].m_obj;
lean_object* v___y_655_ = stack[3].m_obj;
lean_object* v___y_656_ = stack[4].m_obj;
lean_object* v___y_657_ = stack[5].m_obj;
lean_object* v___y_658_ = stack[6].m_obj;
lean_object* v_res_690_;
v_res_690_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6(v_fvarId_652_, v_mvarId_653_, v_x_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
stack->m_obj
 = v_res_690_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(lean_object* v_fvarId_691_, lean_object* v_mvarId_692_, lean_object* v_as_693_, size_t v_i_694_, size_t v_stop_695_, lean_object* v_b_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_691_ = stack[0].m_obj;
lean_object* v_mvarId_692_ = stack[1].m_obj;
lean_object* v_as_693_ = stack[2].m_obj;
size_t v_i_694_ = stack[3].m_num;
size_t v_stop_695_ = stack[4].m_num;
lean_object* v_b_696_ = stack[5].m_obj;
lean_object* v___y_697_ = stack[6].m_obj;
lean_object* v___y_698_ = stack[7].m_obj;
lean_object* v___y_699_ = stack[8].m_obj;
lean_object* v___y_700_ = stack[9].m_obj;
lean_object* v_res_710_;
v_res_710_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(v_fvarId_691_, v_mvarId_692_, v_as_693_, v_i_694_, v_stop_695_, v_b_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
stack->m_obj
 = v_res_710_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7___boxed(lean_object* v_fvarId_711_, lean_object* v_mvarId_712_, lean_object* v_as_713_, lean_object* v_i_714_, lean_object* v_stop_715_, lean_object* v_b_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
size_t v_i_boxed_722_; size_t v_stop_boxed_723_; lean_object* v_res_724_; 
v_i_boxed_722_ = lean_unbox_usize(v_i_714_);
lean_dec(v_i_714_);
v_stop_boxed_723_ = lean_unbox_usize(v_stop_715_);
lean_dec(v_stop_715_);
v_res_724_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(v_fvarId_711_, v_mvarId_712_, v_as_713_, v_i_boxed_722_, v_stop_boxed_723_, v_b_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec_ref(v_as_713_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6___boxed(lean_object* v_fvarId_725_, lean_object* v_mvarId_726_, lean_object* v_x_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6(v_fvarId_725_, v_mvarId_726_, v_x_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
return v_res_733_;
}
}
lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6(lean_object* v_fvarId_734_, lean_object* v_mvarId_735_, lean_object* v_t_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
lean_object* v_root_742_; lean_object* v_tail_743_; lean_object* v___x_744_; 
v_root_742_ = lean_ctor_get(v_t_736_, 0);
lean_inc_ref(v_root_742_);
v_tail_743_ = lean_ctor_get(v_t_736_, 1);
lean_inc_ref(v_tail_743_);
lean_dec_ref(v_t_736_);
lean_inc(v_mvarId_735_);
lean_inc(v_fvarId_734_);
v___x_744_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6(v_fvarId_734_, v_mvarId_735_, v_root_742_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_758_; 
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_758_ == 0)
{
lean_object* v_unused_759_; 
v_unused_759_ = lean_ctor_get(v___x_744_, 0);
lean_dec(v_unused_759_);
v___x_746_ = v___x_744_;
v_isShared_747_ = v_isSharedCheck_758_;
goto v_resetjp_745_;
}
else
{
lean_dec(v___x_744_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_758_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; uint8_t v___x_751_; 
v___x_748_ = lean_unsigned_to_nat(0u);
v___x_749_ = lean_array_get_size(v_tail_743_);
v___x_750_ = lean_box(0);
v___x_751_ = lean_nat_dec_lt(v___x_748_, v___x_749_);
if (v___x_751_ == 0)
{
lean_object* v___x_753_; 
lean_dec_ref(v_tail_743_);
lean_dec(v_mvarId_735_);
lean_dec(v_fvarId_734_);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 0, v___x_750_);
v___x_753_ = v___x_746_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_750_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
else
{
size_t v___x_755_; size_t v___x_756_; lean_object* v___x_757_; 
lean_del_object(v___x_746_);
v___x_755_ = ((size_t)0ULL);
v___x_756_ = lean_usize_of_nat(v___x_749_);
v___x_757_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_734_, v_mvarId_735_, v_tail_743_, v___x_755_, v___x_756_, v___x_750_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
lean_dec_ref(v_tail_743_);
return v___x_757_;
}
}
}
else
{
lean_dec_ref(v_tail_743_);
lean_dec(v_mvarId_735_);
lean_dec(v_fvarId_734_);
return v___x_744_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_734_ = stack[0].m_obj;
lean_object* v_mvarId_735_ = stack[1].m_obj;
lean_object* v_t_736_ = stack[2].m_obj;
lean_object* v___y_737_ = stack[3].m_obj;
lean_object* v___y_738_ = stack[4].m_obj;
lean_object* v___y_739_ = stack[5].m_obj;
lean_object* v___y_740_ = stack[6].m_obj;
lean_object* v_res_760_;
v_res_760_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6(v_fvarId_734_, v_mvarId_735_, v_t_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
stack->m_obj
 = v_res_760_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6___boxed(lean_object* v_fvarId_761_, lean_object* v_mvarId_762_, lean_object* v_t_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6(v_fvarId_761_, v_mvarId_762_, v_t_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
return v_res_769_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_770_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4(lean_object* v_fvarId_771_, lean_object* v_mvarId_772_, lean_object* v_x_773_, size_t v_x_774_, size_t v_x_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
if (lean_obj_tag(v_x_773_) == 0)
{
lean_object* v_cs_781_; lean_object* v___x_782_; size_t v___x_783_; lean_object* v_j_784_; lean_object* v___x_785_; size_t v___x_786_; size_t v___x_787_; size_t v___x_788_; size_t v___x_789_; size_t v___x_790_; size_t v___x_791_; lean_object* v___x_792_; 
v_cs_781_ = lean_ctor_get(v_x_773_, 0);
lean_inc_ref(v_cs_781_);
lean_dec_ref_known(v_x_773_, 1);
v___x_782_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0);
v___x_783_ = lean_usize_shift_right(v_x_774_, v_x_775_);
v_j_784_ = lean_usize_to_nat(v___x_783_);
v___x_785_ = lean_array_get_borrowed(v___x_782_, v_cs_781_, v_j_784_);
v___x_786_ = ((size_t)1ULL);
v___x_787_ = lean_usize_shift_left(v___x_786_, v_x_775_);
v___x_788_ = lean_usize_sub(v___x_787_, v___x_786_);
v___x_789_ = lean_usize_land(v_x_774_, v___x_788_);
v___x_790_ = ((size_t)5ULL);
v___x_791_ = lean_usize_sub(v_x_775_, v___x_790_);
lean_inc(v___x_785_);
lean_inc(v_mvarId_772_);
lean_inc(v_fvarId_771_);
v___x_792_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4(v_fvarId_771_, v_mvarId_772_, v___x_785_, v___x_789_, v___x_791_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_807_; 
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_807_ == 0)
{
lean_object* v_unused_808_; 
v_unused_808_ = lean_ctor_get(v___x_792_, 0);
lean_dec(v_unused_808_);
v___x_794_ = v___x_792_;
v_isShared_795_ = v_isSharedCheck_807_;
goto v_resetjp_793_;
}
else
{
lean_dec(v___x_792_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_807_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; uint8_t v___x_800_; 
v___x_796_ = lean_unsigned_to_nat(1u);
v___x_797_ = lean_nat_add(v_j_784_, v___x_796_);
lean_dec(v_j_784_);
v___x_798_ = lean_array_get_size(v_cs_781_);
v___x_799_ = lean_box(0);
v___x_800_ = lean_nat_dec_lt(v___x_797_, v___x_798_);
if (v___x_800_ == 0)
{
lean_object* v___x_802_; 
lean_dec(v___x_797_);
lean_dec_ref(v_cs_781_);
lean_dec(v_mvarId_772_);
lean_dec(v_fvarId_771_);
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 0, v___x_799_);
v___x_802_ = v___x_794_;
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
lean_del_object(v___x_794_);
v___x_804_ = lean_usize_of_nat(v___x_797_);
lean_dec(v___x_797_);
v___x_805_ = lean_usize_of_nat(v___x_798_);
v___x_806_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(v_fvarId_771_, v_mvarId_772_, v_cs_781_, v___x_804_, v___x_805_, v___x_799_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
lean_dec_ref(v_cs_781_);
return v___x_806_;
}
}
}
else
{
lean_dec(v_j_784_);
lean_dec_ref(v_cs_781_);
lean_dec(v_mvarId_772_);
lean_dec(v_fvarId_771_);
return v___x_792_;
}
}
else
{
lean_object* v_vs_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_823_; 
v_vs_809_ = lean_ctor_get(v_x_773_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v_x_773_);
if (v_isSharedCheck_823_ == 0)
{
v___x_811_ = v_x_773_;
v_isShared_812_ = v_isSharedCheck_823_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_vs_809_);
lean_dec(v_x_773_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_823_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; uint8_t v___x_816_; 
v___x_813_ = lean_usize_to_nat(v_x_774_);
v___x_814_ = lean_array_get_size(v_vs_809_);
v___x_815_ = lean_box(0);
v___x_816_ = lean_nat_dec_lt(v___x_813_, v___x_814_);
if (v___x_816_ == 0)
{
lean_object* v___x_818_; 
lean_dec(v___x_813_);
lean_dec_ref(v_vs_809_);
lean_dec(v_mvarId_772_);
lean_dec(v_fvarId_771_);
if (v_isShared_812_ == 0)
{
lean_ctor_set_tag(v___x_811_, 0);
lean_ctor_set(v___x_811_, 0, v___x_815_);
v___x_818_ = v___x_811_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_815_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
else
{
size_t v___x_820_; size_t v___x_821_; lean_object* v___x_822_; 
lean_del_object(v___x_811_);
v___x_820_ = lean_usize_of_nat(v___x_813_);
lean_dec(v___x_813_);
v___x_821_ = lean_usize_of_nat(v___x_814_);
v___x_822_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_771_, v_mvarId_772_, v_vs_809_, v___x_820_, v___x_821_, v___x_815_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
lean_dec_ref(v_vs_809_);
return v___x_822_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_771_ = stack[0].m_obj;
lean_object* v_mvarId_772_ = stack[1].m_obj;
lean_object* v_x_773_ = stack[2].m_obj;
size_t v_x_774_ = stack[3].m_num;
size_t v_x_775_ = stack[4].m_num;
lean_object* v___y_776_ = stack[5].m_obj;
lean_object* v___y_777_ = stack[6].m_obj;
lean_object* v___y_778_ = stack[7].m_obj;
lean_object* v___y_779_ = stack[8].m_obj;
lean_object* v_res_824_;
v_res_824_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4(v_fvarId_771_, v_mvarId_772_, v_x_773_, v_x_774_, v_x_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
stack->m_obj
 = v_res_824_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___boxed(lean_object* v_fvarId_825_, lean_object* v_mvarId_826_, lean_object* v_x_827_, lean_object* v_x_828_, lean_object* v_x_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
size_t v_x_9134__boxed_835_; size_t v_x_9135__boxed_836_; lean_object* v_res_837_; 
v_x_9134__boxed_835_ = lean_unbox_usize(v_x_828_);
lean_dec(v_x_828_);
v_x_9135__boxed_836_ = lean_unbox_usize(v_x_829_);
lean_dec(v_x_829_);
v_res_837_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4(v_fvarId_825_, v_mvarId_826_, v_x_827_, v_x_9134__boxed_835_, v_x_9135__boxed_836_, v___y_830_, v___y_831_, v___y_832_, v___y_833_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
return v_res_837_;
}
}
lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1(lean_object* v_fvarId_838_, lean_object* v_mvarId_839_, lean_object* v_t_840_, lean_object* v_start_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v___x_847_; uint8_t v___x_848_; 
v___x_847_ = lean_unsigned_to_nat(0u);
v___x_848_ = lean_nat_dec_eq(v_start_841_, v___x_847_);
if (v___x_848_ == 0)
{
lean_object* v_root_849_; lean_object* v_tail_850_; size_t v_shift_851_; lean_object* v_tailOff_852_; uint8_t v___x_853_; 
v_root_849_ = lean_ctor_get(v_t_840_, 0);
lean_inc_ref(v_root_849_);
v_tail_850_ = lean_ctor_get(v_t_840_, 1);
lean_inc_ref(v_tail_850_);
v_shift_851_ = lean_ctor_get_usize(v_t_840_, 4);
v_tailOff_852_ = lean_ctor_get(v_t_840_, 3);
lean_inc(v_tailOff_852_);
lean_dec_ref(v_t_840_);
v___x_853_ = lean_nat_dec_le(v_tailOff_852_, v_start_841_);
if (v___x_853_ == 0)
{
size_t v___x_854_; lean_object* v___x_855_; 
lean_dec(v_tailOff_852_);
v___x_854_ = lean_usize_of_nat(v_start_841_);
lean_inc(v_mvarId_839_);
lean_inc(v_fvarId_838_);
v___x_855_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4(v_fvarId_838_, v_mvarId_839_, v_root_849_, v___x_854_, v_shift_851_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_868_; 
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_868_ == 0)
{
lean_object* v_unused_869_; 
v_unused_869_ = lean_ctor_get(v___x_855_, 0);
lean_dec(v_unused_869_);
v___x_857_ = v___x_855_;
v_isShared_858_ = v_isSharedCheck_868_;
goto v_resetjp_856_;
}
else
{
lean_dec(v___x_855_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_868_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_859_; lean_object* v___x_860_; uint8_t v___x_861_; 
v___x_859_ = lean_array_get_size(v_tail_850_);
v___x_860_ = lean_box(0);
v___x_861_ = lean_nat_dec_lt(v___x_847_, v___x_859_);
if (v___x_861_ == 0)
{
lean_object* v___x_863_; 
lean_dec_ref(v_tail_850_);
lean_dec(v_mvarId_839_);
lean_dec(v_fvarId_838_);
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 0, v___x_860_);
v___x_863_ = v___x_857_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_860_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
else
{
size_t v___x_865_; size_t v___x_866_; lean_object* v___x_867_; 
lean_del_object(v___x_857_);
v___x_865_ = ((size_t)0ULL);
v___x_866_ = lean_usize_of_nat(v___x_859_);
v___x_867_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_838_, v_mvarId_839_, v_tail_850_, v___x_865_, v___x_866_, v___x_860_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
lean_dec_ref(v_tail_850_);
return v___x_867_;
}
}
}
else
{
lean_dec_ref(v_tail_850_);
lean_dec(v_mvarId_839_);
lean_dec(v_fvarId_838_);
return v___x_855_;
}
}
else
{
lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; uint8_t v___x_873_; 
lean_dec_ref(v_root_849_);
v___x_870_ = lean_nat_sub(v_start_841_, v_tailOff_852_);
lean_dec(v_tailOff_852_);
v___x_871_ = lean_array_get_size(v_tail_850_);
v___x_872_ = lean_box(0);
v___x_873_ = lean_nat_dec_lt(v___x_870_, v___x_871_);
if (v___x_873_ == 0)
{
lean_object* v___x_874_; 
lean_dec(v___x_870_);
lean_dec_ref(v_tail_850_);
lean_dec(v_mvarId_839_);
lean_dec(v_fvarId_838_);
v___x_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_874_, 0, v___x_872_);
return v___x_874_;
}
else
{
size_t v___x_875_; size_t v___x_876_; lean_object* v___x_877_; 
v___x_875_ = lean_usize_of_nat(v___x_870_);
lean_dec(v___x_870_);
v___x_876_ = lean_usize_of_nat(v___x_871_);
v___x_877_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_838_, v_mvarId_839_, v_tail_850_, v___x_875_, v___x_876_, v___x_872_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
lean_dec_ref(v_tail_850_);
return v___x_877_;
}
}
}
else
{
lean_object* v___x_878_; 
v___x_878_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6(v_fvarId_838_, v_mvarId_839_, v_t_840_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
return v___x_878_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_838_ = stack[0].m_obj;
lean_object* v_mvarId_839_ = stack[1].m_obj;
lean_object* v_t_840_ = stack[2].m_obj;
lean_object* v_start_841_ = stack[3].m_obj;
lean_object* v___y_842_ = stack[4].m_obj;
lean_object* v___y_843_ = stack[5].m_obj;
lean_object* v___y_844_ = stack[6].m_obj;
lean_object* v___y_845_ = stack[7].m_obj;
lean_object* v_res_879_;
v_res_879_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1(v_fvarId_838_, v_mvarId_839_, v_t_840_, v_start_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
stack->m_obj
 = v_res_879_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1___boxed(lean_object* v_fvarId_880_, lean_object* v_mvarId_881_, lean_object* v_t_882_, lean_object* v_start_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1(v_fvarId_880_, v_mvarId_881_, v_t_882_, v_start_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
lean_dec(v_start_883_);
return v_res_889_;
}
}
lean_object* l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1(lean_object* v_fvarId_890_, lean_object* v_mvarId_891_, lean_object* v_lctx_892_, lean_object* v_start_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v_decls_899_; lean_object* v___x_900_; 
v_decls_899_ = lean_ctor_get(v_lctx_892_, 1);
lean_inc_ref(v_decls_899_);
lean_dec_ref(v_lctx_892_);
v___x_900_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1(v_fvarId_890_, v_mvarId_891_, v_decls_899_, v_start_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
return v___x_900_;
}
}
LEAN_EXPORT void l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_890_ = stack[0].m_obj;
lean_object* v_mvarId_891_ = stack[1].m_obj;
lean_object* v_lctx_892_ = stack[2].m_obj;
lean_object* v_start_893_ = stack[3].m_obj;
lean_object* v___y_894_ = stack[4].m_obj;
lean_object* v___y_895_ = stack[5].m_obj;
lean_object* v___y_896_ = stack[6].m_obj;
lean_object* v___y_897_ = stack[7].m_obj;
lean_object* v_res_901_;
v_res_901_ = l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1(v_fvarId_890_, v_mvarId_891_, v_lctx_892_, v_start_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
stack->m_obj
 = v_res_901_;
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1___boxed(lean_object* v_fvarId_902_, lean_object* v_mvarId_903_, lean_object* v_lctx_904_, lean_object* v_start_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1(v_fvarId_902_, v_mvarId_903_, v_lctx_904_, v_start_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v_start_905_);
return v_res_911_;
}
}
static lean_object* _init_l_Lean_MVarId_clear___lam__1___closed__1(void){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_913_ = ((lean_object*)(l_Lean_MVarId_clear___lam__1___closed__0));
v___x_914_ = l_Lean_stringToMessageData(v___x_913_);
return v___x_914_;
}
}
static lean_object* _init_l_Lean_MVarId_clear___lam__1___closed__3(void){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_916_ = ((lean_object*)(l_Lean_MVarId_clear___lam__1___closed__2));
v___x_917_ = l_Lean_stringToMessageData(v___x_916_);
return v___x_917_;
}
}
lean_object* l_Lean_MVarId_clear___lam__1(lean_object* v_mvarId_918_, lean_object* v___x_919_, lean_object* v_fvarId_920_, lean_object* v___f_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v___y_928_; lean_object* v___y_929_; lean_object* v___y_930_; lean_object* v___y_931_; lean_object* v___y_932_; lean_object* v___y_933_; lean_object* v___y_934_; lean_object* v___y_935_; lean_object* v___y_936_; lean_object* v___x_958_; 
lean_inc(v___x_919_);
lean_inc(v_mvarId_918_);
v___x_958_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_918_, v___x_919_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v_lctx_959_; lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v___y_967_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v___y_977_; uint8_t v___x_1034_; 
lean_dec_ref_known(v___x_958_, 1);
v_lctx_959_ = lean_ctor_get(v___y_922_, 2);
lean_inc_ref(v_lctx_959_);
v___x_1034_ = l_Lean_LocalContext_contains(v_lctx_959_, v_fvarId_920_);
if (v___x_1034_ == 0)
{
lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1035_ = lean_obj_once(&l_Lean_MVarId_clear___lam__1___closed__3, &l_Lean_MVarId_clear___lam__1___closed__3_once, _init_l_Lean_MVarId_clear___lam__1___closed__3);
lean_inc(v_fvarId_920_);
v___x_1036_ = l_Lean_mkFVar(v_fvarId_920_);
v___x_1037_ = l_Lean_MessageData_ofExpr(v___x_1036_);
v___x_1038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1035_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
v___x_1039_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7);
v___x_1040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1038_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v___x_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
lean_inc(v_mvarId_918_);
lean_inc(v___x_919_);
v___x_1042_ = l_Lean_Meta_throwTacticEx___redArg(v___x_919_, v_mvarId_918_, v___x_1041_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_dec_ref_known(v___x_1042_, 1);
v___y_974_ = v___y_922_;
v___y_975_ = v___y_923_;
v___y_976_ = v___y_924_;
v___y_977_ = v___y_925_;
goto v___jp_973_;
}
else
{
lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1050_; 
lean_dec_ref(v_lctx_959_);
lean_dec_ref(v___y_922_);
lean_dec_ref(v___f_921_);
lean_dec(v_fvarId_920_);
lean_dec(v___x_919_);
lean_dec(v_mvarId_918_);
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
else
{
v___y_974_ = v___y_922_;
v___y_975_ = v___y_923_;
v___y_976_ = v___y_924_;
v___y_977_ = v___y_925_;
goto v___jp_973_;
}
v___jp_960_:
{
lean_object* v_localInstances_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v_localInstances_968_ = lean_ctor_get(v___y_964_, 3);
v___x_969_ = l_Lean_LocalContext_erase(v_lctx_959_, v_fvarId_920_);
lean_dec(v_fvarId_920_);
lean_inc(v___y_963_);
v___x_970_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_921_, v_localInstances_968_, v___y_963_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_inc_ref(v_localInstances_968_);
v___y_928_ = v___y_966_;
v___y_929_ = v___y_961_;
v___y_930_ = v___y_965_;
v___y_931_ = v___y_964_;
v___y_932_ = v___y_967_;
v___y_933_ = v___y_962_;
v___y_934_ = v___y_963_;
v___y_935_ = v___x_969_;
v___y_936_ = v_localInstances_968_;
goto v___jp_927_;
}
else
{
lean_object* v_val_971_; lean_object* v___x_972_; 
v_val_971_ = lean_ctor_get(v___x_970_, 0);
lean_inc(v_val_971_);
lean_dec_ref_known(v___x_970_, 1);
lean_inc_ref(v_localInstances_968_);
v___x_972_ = l_Array_eraseIdx___redArg(v_localInstances_968_, v_val_971_);
v___y_928_ = v___y_966_;
v___y_929_ = v___y_961_;
v___y_930_ = v___y_965_;
v___y_931_ = v___y_964_;
v___y_932_ = v___y_967_;
v___y_933_ = v___y_962_;
v___y_934_ = v___y_963_;
v___y_935_ = v___x_969_;
v___y_936_ = v___x_972_;
goto v___jp_927_;
}
}
v___jp_973_:
{
lean_object* v___x_978_; 
lean_inc(v_mvarId_918_);
v___x_978_ = l_Lean_MVarId_getTag(v_mvarId_918_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
if (lean_obj_tag(v___x_978_) == 0)
{
lean_object* v_a_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v_a_979_ = lean_ctor_get(v___x_978_, 0);
lean_inc(v_a_979_);
lean_dec_ref_known(v___x_978_, 1);
v___x_980_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_lctx_959_);
lean_inc(v_mvarId_918_);
lean_inc(v_fvarId_920_);
v___x_981_ = l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1(v_fvarId_920_, v_mvarId_918_, v_lctx_959_, v___x_980_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v___x_982_; 
lean_dec_ref_known(v___x_981_, 1);
lean_inc(v_mvarId_918_);
v___x_982_ = l_Lean_MVarId_getDecl(v_mvarId_918_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_a_983_; lean_object* v_type_984_; lean_object* v___x_985_; lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_1009_; 
v_a_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_a_983_);
lean_dec_ref_known(v___x_982_, 1);
v_type_984_ = lean_ctor_get(v_a_983_, 2);
lean_inc_ref_n(v_type_984_, 2);
lean_dec(v_a_983_);
lean_inc(v_fvarId_920_);
v___x_985_ = l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3___redArg(v_type_984_, v_fvarId_920_, v___y_975_);
v_a_986_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_988_ = v___x_985_;
v_isShared_989_ = v_isSharedCheck_1009_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_985_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_1009_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
uint8_t v___x_990_; 
v___x_990_ = lean_unbox(v_a_986_);
lean_dec(v_a_986_);
if (v___x_990_ == 0)
{
lean_del_object(v___x_988_);
lean_dec(v___x_919_);
v___y_961_ = v_type_984_;
v___y_962_ = v_a_979_;
v___y_963_ = v___x_980_;
v___y_964_ = v___y_974_;
v___y_965_ = v___y_975_;
v___y_966_ = v___y_976_;
v___y_967_ = v___y_977_;
goto v___jp_960_;
}
else
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_998_; 
v___x_991_ = lean_obj_once(&l_Lean_MVarId_clear___lam__1___closed__1, &l_Lean_MVarId_clear___lam__1___closed__1_once, _init_l_Lean_MVarId_clear___lam__1___closed__1);
lean_inc(v_fvarId_920_);
v___x_992_ = l_Lean_mkFVar(v_fvarId_920_);
v___x_993_ = l_Lean_MessageData_ofExpr(v___x_992_);
v___x_994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_991_);
lean_ctor_set(v___x_994_, 1, v___x_993_);
v___x_995_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7);
v___x_996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_994_);
lean_ctor_set(v___x_996_, 1, v___x_995_);
if (v_isShared_989_ == 0)
{
lean_ctor_set_tag(v___x_988_, 1);
lean_ctor_set(v___x_988_, 0, v___x_996_);
v___x_998_ = v___x_988_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v___x_996_);
v___x_998_ = v_reuseFailAlloc_1008_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
lean_object* v___x_999_; 
lean_inc(v_mvarId_918_);
v___x_999_ = l_Lean_Meta_throwTacticEx___redArg(v___x_919_, v_mvarId_918_, v___x_998_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_dec_ref_known(v___x_999_, 1);
v___y_961_ = v_type_984_;
v___y_962_ = v_a_979_;
v___y_963_ = v___x_980_;
v___y_964_ = v___y_974_;
v___y_965_ = v___y_975_;
v___y_966_ = v___y_976_;
v___y_967_ = v___y_977_;
goto v___jp_960_;
}
else
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
lean_dec_ref(v_type_984_);
lean_dec(v_a_979_);
lean_dec_ref(v___y_974_);
lean_dec_ref(v_lctx_959_);
lean_dec_ref(v___f_921_);
lean_dec(v_fvarId_920_);
lean_dec(v_mvarId_918_);
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1002_ = v___x_999_;
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_999_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1005_; 
if (v_isShared_1003_ == 0)
{
v___x_1005_ = v___x_1002_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_a_1000_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
lean_dec(v_a_979_);
lean_dec_ref(v___y_974_);
lean_dec_ref(v_lctx_959_);
lean_dec_ref(v___f_921_);
lean_dec(v_fvarId_920_);
lean_dec(v___x_919_);
lean_dec(v_mvarId_918_);
v_a_1010_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_982_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_982_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1015_; 
if (v_isShared_1013_ == 0)
{
v___x_1015_ = v___x_1012_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1010_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
else
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
lean_dec(v_a_979_);
lean_dec_ref(v___y_974_);
lean_dec_ref(v_lctx_959_);
lean_dec_ref(v___f_921_);
lean_dec(v_fvarId_920_);
lean_dec(v___x_919_);
lean_dec(v_mvarId_918_);
v_a_1018_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1020_ = v___x_981_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_981_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1018_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
}
else
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1033_; 
lean_dec_ref(v___y_974_);
lean_dec_ref(v_lctx_959_);
lean_dec_ref(v___f_921_);
lean_dec(v_fvarId_920_);
lean_dec(v___x_919_);
lean_dec(v_mvarId_918_);
v_a_1026_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1028_ = v___x_978_;
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_978_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1029_ == 0)
{
v___x_1031_ = v___x_1028_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1026_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
}
else
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1058_; 
lean_dec_ref(v___y_922_);
lean_dec_ref(v___f_921_);
lean_dec(v_fvarId_920_);
lean_dec(v___x_919_);
lean_dec(v_mvarId_918_);
v_a_1051_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1053_ = v___x_958_;
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_958_);
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
v___jp_927_:
{
uint8_t v___x_937_; lean_object* v___x_938_; 
v___x_937_ = 2;
v___x_938_ = l_Lean_Meta_mkFreshExprMVarAt(v___y_935_, v___y_936_, v___y_929_, v___x_937_, v___y_933_, v___y_934_, v___y_931_, v___y_930_, v___y_928_, v___y_932_);
lean_dec_ref(v___y_931_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v_a_939_; lean_object* v___x_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_948_; 
v_a_939_ = lean_ctor_get(v___x_938_, 0);
lean_inc_n(v_a_939_, 2);
lean_dec_ref_known(v___x_938_, 1);
v___x_940_ = l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg(v_mvarId_918_, v_a_939_, v___y_930_);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_948_ == 0)
{
lean_object* v_unused_949_; 
v_unused_949_ = lean_ctor_get(v___x_940_, 0);
lean_dec(v_unused_949_);
v___x_942_ = v___x_940_;
v_isShared_943_ = v_isSharedCheck_948_;
goto v_resetjp_941_;
}
else
{
lean_dec(v___x_940_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_948_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_944_; lean_object* v___x_946_; 
v___x_944_ = l_Lean_Expr_mvarId_x21(v_a_939_);
lean_dec(v_a_939_);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 0, v___x_944_);
v___x_946_ = v___x_942_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_944_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
else
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_957_; 
lean_dec(v_mvarId_918_);
v_a_950_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_957_ == 0)
{
v___x_952_ = v___x_938_;
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_938_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_955_; 
if (v_isShared_953_ == 0)
{
v___x_955_ = v___x_952_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_950_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_clear___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_918_ = stack[0].m_obj;
lean_object* v___x_919_ = stack[1].m_obj;
lean_object* v_fvarId_920_ = stack[2].m_obj;
lean_object* v___f_921_ = stack[3].m_obj;
lean_object* v___y_922_ = stack[4].m_obj;
lean_object* v___y_923_ = stack[5].m_obj;
lean_object* v___y_924_ = stack[6].m_obj;
lean_object* v___y_925_ = stack[7].m_obj;
lean_object* v_res_1059_;
v_res_1059_ = l_Lean_MVarId_clear___lam__1(v_mvarId_918_, v___x_919_, v_fvarId_920_, v___f_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
stack->m_obj
 = v_res_1059_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clear___lam__1___boxed(lean_object* v_mvarId_1060_, lean_object* v___x_1061_, lean_object* v_fvarId_1062_, lean_object* v___f_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l_Lean_MVarId_clear___lam__1(v_mvarId_1060_, v___x_1061_, v_fvarId_1062_, v___f_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
lean_dec(v___y_1065_);
return v_res_1069_;
}
}
lean_object* l_Lean_MVarId_clear(lean_object* v_mvarId_1070_, lean_object* v_fvarId_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_){
_start:
{
lean_object* v___f_1077_; lean_object* v___x_1078_; lean_object* v___f_1079_; lean_object* v___x_1080_; 
lean_inc(v_fvarId_1071_);
v___f_1077_ = lean_alloc_closure((void*)(l_Lean_MVarId_clear___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1077_, 0, v_fvarId_1071_);
v___x_1078_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__1));
lean_inc(v_mvarId_1070_);
v___f_1079_ = lean_alloc_closure((void*)(l_Lean_MVarId_clear___lam__1___boxed), 9, 4);
lean_closure_set(v___f_1079_, 0, v_mvarId_1070_);
lean_closure_set(v___f_1079_, 1, v___x_1078_);
lean_closure_set(v___f_1079_, 2, v_fvarId_1071_);
lean_closure_set(v___f_1079_, 3, v___f_1077_);
v___x_1080_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg(v_mvarId_1070_, v___f_1079_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_);
return v___x_1080_;
}
}
LEAN_EXPORT void l_Lean_MVarId_clear_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1070_ = stack[0].m_obj;
lean_object* v_fvarId_1071_ = stack[1].m_obj;
lean_object* v_a_1072_ = stack[2].m_obj;
lean_object* v_a_1073_ = stack[3].m_obj;
lean_object* v_a_1074_ = stack[4].m_obj;
lean_object* v_a_1075_ = stack[5].m_obj;
lean_object* v_res_1081_;
v_res_1081_ = l_Lean_MVarId_clear(v_mvarId_1070_, v_fvarId_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_);
stack->m_obj
 = v_res_1081_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clear___boxed(lean_object* v_mvarId_1082_, lean_object* v_fvarId_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l_Lean_MVarId_clear(v_mvarId_1082_, v_fvarId_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
lean_dec(v_a_1087_);
lean_dec_ref(v_a_1086_);
lean_dec(v_a_1085_);
lean_dec_ref(v_a_1084_);
return v_res_1089_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2(lean_object* v_mvarId_1090_, lean_object* v_val_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
lean_object* v___x_1097_; 
v___x_1097_ = l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg(v_mvarId_1090_, v_val_1091_, v___y_1093_);
return v___x_1097_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1090_ = stack[0].m_obj;
lean_object* v_val_1091_ = stack[1].m_obj;
lean_object* v___y_1092_ = stack[2].m_obj;
lean_object* v___y_1093_ = stack[3].m_obj;
lean_object* v___y_1094_ = stack[4].m_obj;
lean_object* v___y_1095_ = stack[5].m_obj;
lean_object* v_res_1098_;
v_res_1098_ = l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2(v_mvarId_1090_, v_val_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_);
stack->m_obj
 = v_res_1098_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___boxed(lean_object* v_mvarId_1099_, lean_object* v_val_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2(v_mvarId_1099_, v_val_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3(lean_object* v_00_u03b2_1107_, lean_object* v_x_1108_, lean_object* v_x_1109_, lean_object* v_x_1110_){
_start:
{
lean_object* v___x_1111_; 
v___x_1111_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3___redArg(v_x_1108_, v_x_1109_, v_x_1110_);
return v___x_1111_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9(lean_object* v_00_u03b2_1112_, lean_object* v_x_1113_, size_t v_x_1114_, size_t v_x_1115_, lean_object* v_x_1116_, lean_object* v_x_1117_){
_start:
{
lean_object* v___x_1118_; 
v___x_1118_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_x_1113_, v_x_1114_, v_x_1115_, v_x_1116_, v_x_1117_);
return v___x_1118_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1113_ = stack[1].m_obj;
size_t v_x_1114_ = stack[2].m_num;
size_t v_x_1115_ = stack[3].m_num;
lean_object* v_x_1116_ = stack[4].m_obj;
lean_object* v_x_1117_ = stack[5].m_obj;
lean_object* v_res_1119_;
v_res_1119_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9(lean_box(0), v_x_1113_, v_x_1114_, v_x_1115_, v_x_1116_, v_x_1117_);
stack->m_obj
 = v_res_1119_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___boxed(lean_object* v_00_u03b2_1120_, lean_object* v_x_1121_, lean_object* v_x_1122_, lean_object* v_x_1123_, lean_object* v_x_1124_, lean_object* v_x_1125_){
_start:
{
size_t v_x_9962__boxed_1126_; size_t v_x_9963__boxed_1127_; lean_object* v_res_1128_; 
v_x_9962__boxed_1126_ = lean_unbox_usize(v_x_1122_);
lean_dec(v_x_1122_);
v_x_9963__boxed_1127_ = lean_unbox_usize(v_x_1123_);
lean_dec(v_x_1123_);
v_res_1128_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9(v_00_u03b2_1120_, v_x_1121_, v_x_9962__boxed_1126_, v_x_9963__boxed_1127_, v_x_1124_, v_x_1125_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13(lean_object* v_00_u03b2_1129_, lean_object* v_n_1130_, lean_object* v_k_1131_, lean_object* v_v_1132_){
_start:
{
lean_object* v___x_1133_; 
v___x_1133_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13___redArg(v_n_1130_, v_k_1131_, v_v_1132_);
return v___x_1133_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14(lean_object* v_00_u03b2_1134_, size_t v_depth_1135_, lean_object* v_keys_1136_, lean_object* v_vals_1137_, lean_object* v_heq_1138_, lean_object* v_i_1139_, lean_object* v_entries_1140_){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg(v_depth_1135_, v_keys_1136_, v_vals_1137_, v_i_1139_, v_entries_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1135_ = stack[1].m_num;
lean_object* v_keys_1136_ = stack[2].m_obj;
lean_object* v_vals_1137_ = stack[3].m_obj;
lean_object* v_i_1139_ = stack[5].m_obj;
lean_object* v_entries_1140_ = stack[6].m_obj;
lean_object* v_res_1142_;
v_res_1142_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14(lean_box(0), v_depth_1135_, v_keys_1136_, v_vals_1137_, lean_box(0), v_i_1139_, v_entries_1140_);
stack->m_obj
 = v_res_1142_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___boxed(lean_object* v_00_u03b2_1143_, lean_object* v_depth_1144_, lean_object* v_keys_1145_, lean_object* v_vals_1146_, lean_object* v_heq_1147_, lean_object* v_i_1148_, lean_object* v_entries_1149_){
_start:
{
size_t v_depth_boxed_1150_; lean_object* v_res_1151_; 
v_depth_boxed_1150_ = lean_unbox_usize(v_depth_1144_);
lean_dec(v_depth_1144_);
v_res_1151_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14(v_00_u03b2_1143_, v_depth_boxed_1150_, v_keys_1145_, v_vals_1146_, v_heq_1147_, v_i_1148_, v_entries_1149_);
lean_dec_ref(v_vals_1146_);
lean_dec_ref(v_keys_1145_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13_spec__14(lean_object* v_00_u03b2_1152_, lean_object* v_x_1153_, lean_object* v_x_1154_, lean_object* v_x_1155_, lean_object* v_x_1156_){
_start:
{
lean_object* v___x_1157_; 
v___x_1157_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13_spec__14___redArg(v_x_1153_, v_x_1154_, v_x_1155_, v_x_1156_);
return v___x_1157_;
}
}
lean_object* l_Lean_MVarId_tryClear(lean_object* v_mvarId_1158_, lean_object* v_fvarId_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_){
_start:
{
lean_object* v___x_1165_; 
v___x_1165_ = l_Lean_Meta_saveState___redArg(v_a_1161_, v_a_1163_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_a_1166_; lean_object* v___x_1167_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
lean_inc(v_a_1166_);
lean_dec_ref_known(v___x_1165_, 1);
lean_inc(v_mvarId_1158_);
v___x_1167_ = l_Lean_MVarId_clear(v_mvarId_1158_, v_fvarId_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_dec(v_a_1166_);
lean_dec(v_mvarId_1158_);
return v___x_1167_;
}
else
{
lean_object* v_a_1168_; uint8_t v___y_1170_; uint8_t v___x_1188_; 
v_a_1168_ = lean_ctor_get(v___x_1167_, 0);
v___x_1188_ = l_Lean_Exception_isInterrupt(v_a_1168_);
if (v___x_1188_ == 0)
{
uint8_t v___x_1189_; 
lean_inc(v_a_1168_);
v___x_1189_ = l_Lean_Exception_isRuntime(v_a_1168_);
v___y_1170_ = v___x_1189_;
goto v___jp_1169_;
}
else
{
v___y_1170_ = v___x_1188_;
goto v___jp_1169_;
}
v___jp_1169_:
{
if (v___y_1170_ == 0)
{
lean_object* v___x_1171_; 
lean_dec_ref_known(v___x_1167_, 1);
v___x_1171_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1166_, v_a_1161_, v_a_1163_);
if (lean_obj_tag(v___x_1171_) == 0)
{
lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1178_; 
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1178_ == 0)
{
lean_object* v_unused_1179_; 
v_unused_1179_ = lean_ctor_get(v___x_1171_, 0);
lean_dec(v_unused_1179_);
v___x_1173_ = v___x_1171_;
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
else
{
lean_dec(v___x_1171_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1176_; 
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 0, v_mvarId_1158_);
v___x_1176_ = v___x_1173_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_mvarId_1158_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
else
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1187_; 
lean_dec(v_mvarId_1158_);
v_a_1180_ = lean_ctor_get(v___x_1171_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1182_ = v___x_1171_;
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1171_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1185_; 
if (v_isShared_1183_ == 0)
{
v___x_1185_ = v___x_1182_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_a_1180_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
else
{
lean_dec(v_a_1166_);
lean_dec(v_mvarId_1158_);
return v___x_1167_;
}
}
}
}
else
{
lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1197_; 
lean_dec(v_fvarId_1159_);
lean_dec(v_mvarId_1158_);
v_a_1190_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1192_ = v___x_1165_;
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1190_);
lean_dec(v___x_1165_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1195_; 
if (v_isShared_1193_ == 0)
{
v___x_1195_ = v___x_1192_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_a_1190_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_tryClear_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1158_ = stack[0].m_obj;
lean_object* v_fvarId_1159_ = stack[1].m_obj;
lean_object* v_a_1160_ = stack[2].m_obj;
lean_object* v_a_1161_ = stack[3].m_obj;
lean_object* v_a_1162_ = stack[4].m_obj;
lean_object* v_a_1163_ = stack[5].m_obj;
lean_object* v_res_1198_;
v_res_1198_ = l_Lean_MVarId_tryClear(v_mvarId_1158_, v_fvarId_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_);
stack->m_obj
 = v_res_1198_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClear___boxed(lean_object* v_mvarId_1199_, lean_object* v_fvarId_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Lean_MVarId_tryClear(v_mvarId_1199_, v_fvarId_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_);
lean_dec(v_a_1204_);
lean_dec_ref(v_a_1203_);
lean_dec(v_a_1202_);
lean_dec_ref(v_a_1201_);
return v_res_1206_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0(lean_object* v_as_1207_, size_t v_i_1208_, size_t v_stop_1209_, lean_object* v_b_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
uint8_t v___x_1216_; 
v___x_1216_ = lean_usize_dec_eq(v_i_1208_, v_stop_1209_);
if (v___x_1216_ == 0)
{
size_t v___x_1217_; size_t v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1217_ = ((size_t)1ULL);
v___x_1218_ = lean_usize_sub(v_i_1208_, v___x_1217_);
v___x_1219_ = lean_array_uget_borrowed(v_as_1207_, v___x_1218_);
lean_inc(v___x_1219_);
v___x_1220_ = l_Lean_MVarId_tryClear(v_b_1210_, v___x_1219_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_object* v_a_1221_; 
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
lean_inc(v_a_1221_);
lean_dec_ref_known(v___x_1220_, 1);
v_i_1208_ = v___x_1218_;
v_b_1210_ = v_a_1221_;
goto _start;
}
else
{
return v___x_1220_;
}
}
else
{
lean_object* v___x_1223_; 
v___x_1223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1223_, 0, v_b_1210_);
return v___x_1223_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1207_ = stack[0].m_obj;
size_t v_i_1208_ = stack[1].m_num;
size_t v_stop_1209_ = stack[2].m_num;
lean_object* v_b_1210_ = stack[3].m_obj;
lean_object* v___y_1211_ = stack[4].m_obj;
lean_object* v___y_1212_ = stack[5].m_obj;
lean_object* v___y_1213_ = stack[6].m_obj;
lean_object* v___y_1214_ = stack[7].m_obj;
lean_object* v_res_1224_;
v_res_1224_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0(v_as_1207_, v_i_1208_, v_stop_1209_, v_b_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
stack->m_obj
 = v_res_1224_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0___boxed(lean_object* v_as_1225_, lean_object* v_i_1226_, lean_object* v_stop_1227_, lean_object* v_b_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
size_t v_i_boxed_1234_; size_t v_stop_boxed_1235_; lean_object* v_res_1236_; 
v_i_boxed_1234_ = lean_unbox_usize(v_i_1226_);
lean_dec(v_i_1226_);
v_stop_boxed_1235_ = lean_unbox_usize(v_stop_1227_);
lean_dec(v_stop_1227_);
v_res_1236_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0(v_as_1225_, v_i_boxed_1234_, v_stop_boxed_1235_, v_b_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec_ref(v_as_1225_);
return v_res_1236_;
}
}
lean_object* l_Lean_MVarId_tryClearMany(lean_object* v_mvarId_1237_, lean_object* v_fvarIds_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_){
_start:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; uint8_t v___x_1246_; 
v___x_1244_ = lean_array_get_size(v_fvarIds_1238_);
v___x_1245_ = lean_unsigned_to_nat(0u);
v___x_1246_ = lean_nat_dec_lt(v___x_1245_, v___x_1244_);
if (v___x_1246_ == 0)
{
lean_object* v___x_1247_; 
v___x_1247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1247_, 0, v_mvarId_1237_);
return v___x_1247_;
}
else
{
size_t v___x_1248_; size_t v___x_1249_; lean_object* v___x_1250_; 
v___x_1248_ = lean_usize_of_nat(v___x_1244_);
v___x_1249_ = ((size_t)0ULL);
v___x_1250_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0(v_fvarIds_1238_, v___x_1248_, v___x_1249_, v_mvarId_1237_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_);
return v___x_1250_;
}
}
}
LEAN_EXPORT void l_Lean_MVarId_tryClearMany_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1237_ = stack[0].m_obj;
lean_object* v_fvarIds_1238_ = stack[1].m_obj;
lean_object* v_a_1239_ = stack[2].m_obj;
lean_object* v_a_1240_ = stack[3].m_obj;
lean_object* v_a_1241_ = stack[4].m_obj;
lean_object* v_a_1242_ = stack[5].m_obj;
lean_object* v_res_1251_;
v_res_1251_ = l_Lean_MVarId_tryClearMany(v_mvarId_1237_, v_fvarIds_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_);
stack->m_obj
 = v_res_1251_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany___boxed(lean_object* v_mvarId_1252_, lean_object* v_fvarIds_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l_Lean_MVarId_tryClearMany(v_mvarId_1252_, v_fvarIds_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_);
lean_dec(v_a_1257_);
lean_dec_ref(v_a_1256_);
lean_dec(v_a_1255_);
lean_dec_ref(v_a_1254_);
lean_dec_ref(v_fvarIds_1253_);
return v_res_1259_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0(lean_object* v_as_1260_, size_t v_i_1261_, size_t v_stop_1262_, lean_object* v_b_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
uint8_t v___x_1269_; 
v___x_1269_ = lean_usize_dec_eq(v_i_1261_, v_stop_1262_);
if (v___x_1269_ == 0)
{
lean_object* v_fst_1270_; lean_object* v_snd_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1296_; 
v_fst_1270_ = lean_ctor_get(v_b_1263_, 0);
v_snd_1271_ = lean_ctor_get(v_b_1263_, 1);
v_isSharedCheck_1296_ = !lean_is_exclusive(v_b_1263_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1273_ = v_b_1263_;
v_isShared_1274_ = v_isSharedCheck_1296_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_snd_1271_);
lean_inc(v_fst_1270_);
lean_dec(v_b_1263_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1296_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
size_t v___x_1275_; size_t v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1275_ = ((size_t)1ULL);
v___x_1276_ = lean_usize_sub(v_i_1261_, v___x_1275_);
v___x_1277_ = lean_array_uget_borrowed(v_as_1260_, v___x_1276_);
lean_inc(v___x_1277_);
lean_inc(v_fst_1270_);
v___x_1278_ = l_Lean_MVarId_tryClear(v_fst_1270_, v___x_1277_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; lean_object* v___y_1281_; uint8_t v___x_1286_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_a_1279_);
lean_dec_ref_known(v___x_1278_, 1);
v___x_1286_ = l_Lean_instBEqMVarId_beq(v_fst_1270_, v_a_1279_);
lean_dec(v_fst_1270_);
if (v___x_1286_ == 0)
{
lean_object* v___x_1287_; 
lean_inc(v___x_1277_);
v___x_1287_ = lean_array_push(v_snd_1271_, v___x_1277_);
v___y_1281_ = v___x_1287_;
goto v___jp_1280_;
}
else
{
v___y_1281_ = v_snd_1271_;
goto v___jp_1280_;
}
v___jp_1280_:
{
lean_object* v___x_1283_; 
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 1, v___y_1281_);
lean_ctor_set(v___x_1273_, 0, v_a_1279_);
v___x_1283_ = v___x_1273_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_a_1279_);
lean_ctor_set(v_reuseFailAlloc_1285_, 1, v___y_1281_);
v___x_1283_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
v_i_1261_ = v___x_1276_;
v_b_1263_ = v___x_1283_;
goto _start;
}
}
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_del_object(v___x_1273_);
lean_dec(v_snd_1271_);
lean_dec(v_fst_1270_);
v_a_1288_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1278_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1278_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1288_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
}
else
{
lean_object* v___x_1297_; 
v___x_1297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1297_, 0, v_b_1263_);
return v___x_1297_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1260_ = stack[0].m_obj;
size_t v_i_1261_ = stack[1].m_num;
size_t v_stop_1262_ = stack[2].m_num;
lean_object* v_b_1263_ = stack[3].m_obj;
lean_object* v___y_1264_ = stack[4].m_obj;
lean_object* v___y_1265_ = stack[5].m_obj;
lean_object* v___y_1266_ = stack[6].m_obj;
lean_object* v___y_1267_ = stack[7].m_obj;
lean_object* v_res_1298_;
v_res_1298_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0(v_as_1260_, v_i_1261_, v_stop_1262_, v_b_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
stack->m_obj
 = v_res_1298_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0___boxed(lean_object* v_as_1299_, lean_object* v_i_1300_, lean_object* v_stop_1301_, lean_object* v_b_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
size_t v_i_boxed_1308_; size_t v_stop_boxed_1309_; lean_object* v_res_1310_; 
v_i_boxed_1308_ = lean_unbox_usize(v_i_1300_);
lean_dec(v_i_1300_);
v_stop_boxed_1309_ = lean_unbox_usize(v_stop_1301_);
lean_dec(v_stop_1301_);
v_res_1310_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0(v_as_1299_, v_i_boxed_1308_, v_stop_boxed_1309_, v_b_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec_ref(v_as_1299_);
return v_res_1310_;
}
}
lean_object* l_Lean_MVarId_tryClearMany_x27___lam__0(lean_object* v_fvarIds_1311_, lean_object* v_goal_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v_lctx_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; uint8_t v___x_1324_; 
v_lctx_1318_ = lean_ctor_get(v___y_1313_, 2);
v___x_1319_ = l_Lean_LocalContext_sortFVarsByContextOrder(v_lctx_1318_, v_fvarIds_1311_);
v___x_1320_ = lean_array_get_size(v___x_1319_);
v___x_1321_ = lean_mk_empty_array_with_capacity(v___x_1320_);
v___x_1322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1322_, 0, v_goal_1312_);
lean_ctor_set(v___x_1322_, 1, v___x_1321_);
v___x_1323_ = lean_unsigned_to_nat(0u);
v___x_1324_ = lean_nat_dec_lt(v___x_1323_, v___x_1320_);
if (v___x_1324_ == 0)
{
lean_object* v___x_1325_; 
lean_dec_ref(v___x_1319_);
v___x_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1322_);
return v___x_1325_;
}
else
{
size_t v___x_1326_; size_t v___x_1327_; lean_object* v___x_1328_; 
v___x_1326_ = lean_usize_of_nat(v___x_1320_);
v___x_1327_ = ((size_t)0ULL);
v___x_1328_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0(v___x_1319_, v___x_1326_, v___x_1327_, v___x_1322_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
lean_dec_ref(v___x_1319_);
return v___x_1328_;
}
}
}
LEAN_EXPORT void l_Lean_MVarId_tryClearMany_x27___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarIds_1311_ = stack[0].m_obj;
lean_object* v_goal_1312_ = stack[1].m_obj;
lean_object* v___y_1313_ = stack[2].m_obj;
lean_object* v___y_1314_ = stack[3].m_obj;
lean_object* v___y_1315_ = stack[4].m_obj;
lean_object* v___y_1316_ = stack[5].m_obj;
lean_object* v_res_1329_;
v_res_1329_ = l_Lean_MVarId_tryClearMany_x27___lam__0(v_fvarIds_1311_, v_goal_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
stack->m_obj
 = v_res_1329_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany_x27___lam__0___boxed(lean_object* v_fvarIds_1330_, lean_object* v_goal_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l_Lean_MVarId_tryClearMany_x27___lam__0(v_fvarIds_1330_, v_goal_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
return v_res_1337_;
}
}
lean_object* l_Lean_MVarId_tryClearMany_x27(lean_object* v_goal_1338_, lean_object* v_fvarIds_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_){
_start:
{
lean_object* v___f_1345_; lean_object* v___x_1346_; 
lean_inc(v_goal_1338_);
v___f_1345_ = lean_alloc_closure((void*)(l_Lean_MVarId_tryClearMany_x27___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1345_, 0, v_fvarIds_1339_);
lean_closure_set(v___f_1345_, 1, v_goal_1338_);
v___x_1346_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg(v_goal_1338_, v___f_1345_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_);
return v___x_1346_;
}
}
LEAN_EXPORT void l_Lean_MVarId_tryClearMany_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_1338_ = stack[0].m_obj;
lean_object* v_fvarIds_1339_ = stack[1].m_obj;
lean_object* v_a_1340_ = stack[2].m_obj;
lean_object* v_a_1341_ = stack[3].m_obj;
lean_object* v_a_1342_ = stack[4].m_obj;
lean_object* v_a_1343_ = stack[5].m_obj;
lean_object* v_res_1347_;
v_res_1347_ = l_Lean_MVarId_tryClearMany_x27(v_goal_1338_, v_fvarIds_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_);
stack->m_obj
 = v_res_1347_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany_x27___boxed(lean_object* v_goal_1348_, lean_object* v_fvarIds_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l_Lean_MVarId_tryClearMany_x27(v_goal_1348_, v_fvarIds_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
lean_dec(v_a_1353_);
lean_dec_ref(v_a_1352_);
lean_dec(v_a_1351_);
lean_dec_ref(v_a_1350_);
return v_res_1355_;
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
