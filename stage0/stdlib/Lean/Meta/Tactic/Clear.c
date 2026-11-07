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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_erase(lean_object*, lean_object*);
lean_object* l_Lean_LocalInstances_erase(lean_object*, lean_object*);
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
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_MVarId_clear___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "target depends on '"};
static const lean_object* l_Lean_MVarId_clear___lam__0___closed__0 = (const lean_object*)&l_Lean_MVarId_clear___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_MVarId_clear___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_clear___lam__0___closed__1;
static const lean_string_object l_Lean_MVarId_clear___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "unknown variable '"};
static const lean_object* l_Lean_MVarId_clear___lam__0___closed__2 = (const lean_object*)&l_Lean_MVarId_clear___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_MVarId_clear___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_clear___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_MVarId_clear___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_clear___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13_spec__14___redArg(lean_object* v_x_280_, lean_object* v_x_281_, lean_object* v_x_282_, lean_object* v_x_283_){
_start:
{
lean_object* v_ks_284_; lean_object* v_vs_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_309_; 
v_ks_284_ = lean_ctor_get(v_x_280_, 0);
v_vs_285_ = lean_ctor_get(v_x_280_, 1);
v_isSharedCheck_309_ = !lean_is_exclusive(v_x_280_);
if (v_isSharedCheck_309_ == 0)
{
v___x_287_ = v_x_280_;
v_isShared_288_ = v_isSharedCheck_309_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_vs_285_);
lean_inc(v_ks_284_);
lean_dec(v_x_280_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_309_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_289_; uint8_t v___x_290_; 
v___x_289_ = lean_array_get_size(v_ks_284_);
v___x_290_ = lean_nat_dec_lt(v_x_281_, v___x_289_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_294_; 
lean_dec(v_x_281_);
v___x_291_ = lean_array_push(v_ks_284_, v_x_282_);
v___x_292_ = lean_array_push(v_vs_285_, v_x_283_);
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 1, v___x_292_);
lean_ctor_set(v___x_287_, 0, v___x_291_);
v___x_294_ = v___x_287_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_291_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v___x_292_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
else
{
lean_object* v_k_x27_296_; uint8_t v___x_297_; 
v_k_x27_296_ = lean_array_fget_borrowed(v_ks_284_, v_x_281_);
v___x_297_ = l_Lean_instBEqMVarId_beq(v_x_282_, v_k_x27_296_);
if (v___x_297_ == 0)
{
lean_object* v___x_299_; 
if (v_isShared_288_ == 0)
{
v___x_299_ = v___x_287_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_ks_284_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v_vs_285_);
v___x_299_ = v_reuseFailAlloc_303_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = lean_unsigned_to_nat(1u);
v___x_301_ = lean_nat_add(v_x_281_, v___x_300_);
lean_dec(v_x_281_);
v_x_280_ = v___x_299_;
v_x_281_ = v___x_301_;
goto _start;
}
}
else
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_307_; 
v___x_304_ = lean_array_fset(v_ks_284_, v_x_281_, v_x_282_);
v___x_305_ = lean_array_fset(v_vs_285_, v_x_281_, v_x_283_);
lean_dec(v_x_281_);
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 1, v___x_305_);
lean_ctor_set(v___x_287_, 0, v___x_304_);
v___x_307_ = v___x_287_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v___x_304_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v___x_305_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13___redArg(lean_object* v_n_310_, lean_object* v_k_311_, lean_object* v_v_312_){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = lean_unsigned_to_nat(0u);
v___x_314_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13_spec__14___redArg(v_n_310_, v___x_313_, v_k_311_, v_v_312_);
return v___x_314_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(lean_object* v_x_316_, size_t v_x_317_, size_t v_x_318_, lean_object* v_x_319_, lean_object* v_x_320_){
_start:
{
if (lean_obj_tag(v_x_316_) == 0)
{
lean_object* v_es_321_; size_t v___x_322_; size_t v___x_323_; lean_object* v_j_324_; lean_object* v___x_325_; uint8_t v___x_326_; 
v_es_321_ = lean_ctor_get(v_x_316_, 0);
v___x_322_ = ((size_t)31ULL);
v___x_323_ = lean_usize_land(v_x_317_, v___x_322_);
v_j_324_ = lean_usize_to_nat(v___x_323_);
v___x_325_ = lean_array_get_size(v_es_321_);
v___x_326_ = lean_nat_dec_lt(v_j_324_, v___x_325_);
if (v___x_326_ == 0)
{
lean_dec(v_j_324_);
lean_dec(v_x_320_);
lean_dec(v_x_319_);
return v_x_316_;
}
else
{
lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_365_; 
lean_inc_ref(v_es_321_);
v_isSharedCheck_365_ = !lean_is_exclusive(v_x_316_);
if (v_isSharedCheck_365_ == 0)
{
lean_object* v_unused_366_; 
v_unused_366_ = lean_ctor_get(v_x_316_, 0);
lean_dec(v_unused_366_);
v___x_328_ = v_x_316_;
v_isShared_329_ = v_isSharedCheck_365_;
goto v_resetjp_327_;
}
else
{
lean_dec(v_x_316_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_365_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v_v_330_; lean_object* v___x_331_; lean_object* v_xs_x27_332_; lean_object* v___y_334_; 
v_v_330_ = lean_array_fget(v_es_321_, v_j_324_);
v___x_331_ = lean_box(0);
v_xs_x27_332_ = lean_array_fset(v_es_321_, v_j_324_, v___x_331_);
switch(lean_obj_tag(v_v_330_))
{
case 0:
{
lean_object* v_key_339_; lean_object* v_val_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_350_; 
v_key_339_ = lean_ctor_get(v_v_330_, 0);
v_val_340_ = lean_ctor_get(v_v_330_, 1);
v_isSharedCheck_350_ = !lean_is_exclusive(v_v_330_);
if (v_isSharedCheck_350_ == 0)
{
v___x_342_ = v_v_330_;
v_isShared_343_ = v_isSharedCheck_350_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_val_340_);
lean_inc(v_key_339_);
lean_dec(v_v_330_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_350_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
uint8_t v___x_344_; 
v___x_344_ = l_Lean_instBEqMVarId_beq(v_x_319_, v_key_339_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; lean_object* v___x_346_; 
lean_del_object(v___x_342_);
v___x_345_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_339_, v_val_340_, v_x_319_, v_x_320_);
v___x_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
v___y_334_ = v___x_346_;
goto v___jp_333_;
}
else
{
lean_object* v___x_348_; 
lean_dec(v_val_340_);
lean_dec(v_key_339_);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 1, v_x_320_);
lean_ctor_set(v___x_342_, 0, v_x_319_);
v___x_348_ = v___x_342_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_x_319_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v_x_320_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
v___y_334_ = v___x_348_;
goto v___jp_333_;
}
}
}
}
case 1:
{
lean_object* v_node_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_363_; 
v_node_351_ = lean_ctor_get(v_v_330_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v_v_330_);
if (v_isSharedCheck_363_ == 0)
{
v___x_353_ = v_v_330_;
v_isShared_354_ = v_isSharedCheck_363_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_node_351_);
lean_dec(v_v_330_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_363_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
size_t v___x_355_; size_t v___x_356_; size_t v___x_357_; size_t v___x_358_; lean_object* v___x_359_; lean_object* v___x_361_; 
v___x_355_ = ((size_t)5ULL);
v___x_356_ = lean_usize_shift_right(v_x_317_, v___x_355_);
v___x_357_ = ((size_t)1ULL);
v___x_358_ = lean_usize_add(v_x_318_, v___x_357_);
v___x_359_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_node_351_, v___x_356_, v___x_358_, v_x_319_, v_x_320_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 0, v___x_359_);
v___x_361_ = v___x_353_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_359_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
v___y_334_ = v___x_361_;
goto v___jp_333_;
}
}
}
default: 
{
lean_object* v___x_364_; 
v___x_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_364_, 0, v_x_319_);
lean_ctor_set(v___x_364_, 1, v_x_320_);
v___y_334_ = v___x_364_;
goto v___jp_333_;
}
}
v___jp_333_:
{
lean_object* v___x_335_; lean_object* v___x_337_; 
v___x_335_ = lean_array_fset(v_xs_x27_332_, v_j_324_, v___y_334_);
lean_dec(v_j_324_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 0, v___x_335_);
v___x_337_ = v___x_328_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v___x_335_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
}
}
}
else
{
lean_object* v_ks_367_; lean_object* v_vs_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_386_; 
v_ks_367_ = lean_ctor_get(v_x_316_, 0);
v_vs_368_ = lean_ctor_get(v_x_316_, 1);
v_isSharedCheck_386_ = !lean_is_exclusive(v_x_316_);
if (v_isSharedCheck_386_ == 0)
{
v___x_370_ = v_x_316_;
v_isShared_371_ = v_isSharedCheck_386_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_vs_368_);
lean_inc(v_ks_367_);
lean_dec(v_x_316_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_386_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_373_; 
if (v_isShared_371_ == 0)
{
v___x_373_ = v___x_370_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_ks_367_);
lean_ctor_set(v_reuseFailAlloc_385_, 1, v_vs_368_);
v___x_373_ = v_reuseFailAlloc_385_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
lean_object* v_newNode_374_; size_t v___x_375_; uint8_t v___x_376_; 
v_newNode_374_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13___redArg(v___x_373_, v_x_319_, v_x_320_);
v___x_375_ = ((size_t)7ULL);
v___x_376_ = lean_usize_dec_le(v___x_375_, v_x_318_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; lean_object* v___x_378_; uint8_t v___x_379_; 
v___x_377_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_374_);
v___x_378_ = lean_unsigned_to_nat(4u);
v___x_379_ = lean_nat_dec_lt(v___x_377_, v___x_378_);
lean_dec(v___x_377_);
if (v___x_379_ == 0)
{
lean_object* v_ks_380_; lean_object* v_vs_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v_ks_380_ = lean_ctor_get(v_newNode_374_, 0);
lean_inc_ref(v_ks_380_);
v_vs_381_ = lean_ctor_get(v_newNode_374_, 1);
lean_inc_ref(v_vs_381_);
lean_dec_ref(v_newNode_374_);
v___x_382_ = lean_unsigned_to_nat(0u);
v___x_383_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___closed__0);
v___x_384_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg(v_x_318_, v_ks_380_, v_vs_381_, v___x_382_, v___x_383_);
lean_dec_ref(v_vs_381_);
lean_dec_ref(v_ks_380_);
return v___x_384_;
}
else
{
return v_newNode_374_;
}
}
else
{
return v_newNode_374_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg(size_t v_depth_387_, lean_object* v_keys_388_, lean_object* v_vals_389_, lean_object* v_i_390_, lean_object* v_entries_391_){
_start:
{
lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_392_ = lean_array_get_size(v_keys_388_);
v___x_393_ = lean_nat_dec_lt(v_i_390_, v___x_392_);
if (v___x_393_ == 0)
{
lean_dec(v_i_390_);
return v_entries_391_;
}
else
{
lean_object* v_k_394_; lean_object* v_v_395_; uint64_t v___x_396_; size_t v_h_397_; size_t v___x_398_; lean_object* v___x_399_; size_t v___x_400_; size_t v___x_401_; size_t v___x_402_; size_t v_h_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v_k_394_ = lean_array_fget_borrowed(v_keys_388_, v_i_390_);
v_v_395_ = lean_array_fget_borrowed(v_vals_389_, v_i_390_);
v___x_396_ = l_Lean_instHashableMVarId_hash(v_k_394_);
v_h_397_ = lean_uint64_to_usize(v___x_396_);
v___x_398_ = ((size_t)5ULL);
v___x_399_ = lean_unsigned_to_nat(1u);
v___x_400_ = ((size_t)1ULL);
v___x_401_ = lean_usize_sub(v_depth_387_, v___x_400_);
v___x_402_ = lean_usize_mul(v___x_398_, v___x_401_);
v_h_403_ = lean_usize_shift_right(v_h_397_, v___x_402_);
v___x_404_ = lean_nat_add(v_i_390_, v___x_399_);
lean_dec(v_i_390_);
lean_inc(v_v_395_);
lean_inc(v_k_394_);
v___x_405_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_entries_391_, v_h_403_, v_depth_387_, v_k_394_, v_v_395_);
v_i_390_ = v___x_404_;
v_entries_391_ = v___x_405_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg___boxed(lean_object* v_depth_407_, lean_object* v_keys_408_, lean_object* v_vals_409_, lean_object* v_i_410_, lean_object* v_entries_411_){
_start:
{
size_t v_depth_boxed_412_; lean_object* v_res_413_; 
v_depth_boxed_412_ = lean_unbox_usize(v_depth_407_);
lean_dec(v_depth_407_);
v_res_413_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg(v_depth_boxed_412_, v_keys_408_, v_vals_409_, v_i_410_, v_entries_411_);
lean_dec_ref(v_vals_409_);
lean_dec_ref(v_keys_408_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg___boxed(lean_object* v_x_414_, lean_object* v_x_415_, lean_object* v_x_416_, lean_object* v_x_417_, lean_object* v_x_418_){
_start:
{
size_t v_x_7716__boxed_419_; size_t v_x_7717__boxed_420_; lean_object* v_res_421_; 
v_x_7716__boxed_419_ = lean_unbox_usize(v_x_415_);
lean_dec(v_x_415_);
v_x_7717__boxed_420_ = lean_unbox_usize(v_x_416_);
lean_dec(v_x_416_);
v_res_421_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_x_414_, v_x_7716__boxed_419_, v_x_7717__boxed_420_, v_x_417_, v_x_418_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3___redArg(lean_object* v_x_422_, lean_object* v_x_423_, lean_object* v_x_424_){
_start:
{
uint64_t v___x_425_; size_t v___x_426_; size_t v___x_427_; lean_object* v___x_428_; 
v___x_425_ = l_Lean_instHashableMVarId_hash(v_x_423_);
v___x_426_ = lean_uint64_to_usize(v___x_425_);
v___x_427_ = ((size_t)1ULL);
v___x_428_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_x_422_, v___x_426_, v___x_427_, v_x_423_, v_x_424_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg(lean_object* v_mvarId_429_, lean_object* v_val_430_, lean_object* v___y_431_){
_start:
{
lean_object* v___x_433_; lean_object* v_mctx_434_; lean_object* v_cache_435_; lean_object* v_zetaDeltaFVarIds_436_; lean_object* v_postponed_437_; lean_object* v_diag_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_467_; 
v___x_433_ = lean_st_ref_take(v___y_431_);
v_mctx_434_ = lean_ctor_get(v___x_433_, 0);
v_cache_435_ = lean_ctor_get(v___x_433_, 1);
v_zetaDeltaFVarIds_436_ = lean_ctor_get(v___x_433_, 2);
v_postponed_437_ = lean_ctor_get(v___x_433_, 3);
v_diag_438_ = lean_ctor_get(v___x_433_, 4);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_467_ == 0)
{
v___x_440_ = v___x_433_;
v_isShared_441_ = v_isSharedCheck_467_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_diag_438_);
lean_inc(v_postponed_437_);
lean_inc(v_zetaDeltaFVarIds_436_);
lean_inc(v_cache_435_);
lean_inc(v_mctx_434_);
lean_dec(v___x_433_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_467_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v_depth_442_; lean_object* v_levelAssignDepth_443_; lean_object* v_lmvarCounter_444_; lean_object* v_mvarCounter_445_; lean_object* v_lDecls_446_; lean_object* v_decls_447_; lean_object* v_userNames_448_; lean_object* v_lAssignment_449_; lean_object* v_eAssignment_450_; lean_object* v_dAssignment_451_; lean_object* v_instanceTypedMVars_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_466_; 
v_depth_442_ = lean_ctor_get(v_mctx_434_, 0);
v_levelAssignDepth_443_ = lean_ctor_get(v_mctx_434_, 1);
v_lmvarCounter_444_ = lean_ctor_get(v_mctx_434_, 2);
v_mvarCounter_445_ = lean_ctor_get(v_mctx_434_, 3);
v_lDecls_446_ = lean_ctor_get(v_mctx_434_, 4);
v_decls_447_ = lean_ctor_get(v_mctx_434_, 5);
v_userNames_448_ = lean_ctor_get(v_mctx_434_, 6);
v_lAssignment_449_ = lean_ctor_get(v_mctx_434_, 7);
v_eAssignment_450_ = lean_ctor_get(v_mctx_434_, 8);
v_dAssignment_451_ = lean_ctor_get(v_mctx_434_, 9);
v_instanceTypedMVars_452_ = lean_ctor_get(v_mctx_434_, 10);
v_isSharedCheck_466_ = !lean_is_exclusive(v_mctx_434_);
if (v_isSharedCheck_466_ == 0)
{
v___x_454_ = v_mctx_434_;
v_isShared_455_ = v_isSharedCheck_466_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_instanceTypedMVars_452_);
lean_inc(v_dAssignment_451_);
lean_inc(v_eAssignment_450_);
lean_inc(v_lAssignment_449_);
lean_inc(v_userNames_448_);
lean_inc(v_decls_447_);
lean_inc(v_lDecls_446_);
lean_inc(v_mvarCounter_445_);
lean_inc(v_lmvarCounter_444_);
lean_inc(v_levelAssignDepth_443_);
lean_inc(v_depth_442_);
lean_dec(v_mctx_434_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_466_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_459_; 
v___x_456_ = lean_box(0);
v___x_457_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3___redArg(v_eAssignment_450_, v_mvarId_429_, v_val_430_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 8, v___x_457_);
v___x_459_ = v___x_454_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_depth_442_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v_levelAssignDepth_443_);
lean_ctor_set(v_reuseFailAlloc_465_, 2, v_lmvarCounter_444_);
lean_ctor_set(v_reuseFailAlloc_465_, 3, v_mvarCounter_445_);
lean_ctor_set(v_reuseFailAlloc_465_, 4, v_lDecls_446_);
lean_ctor_set(v_reuseFailAlloc_465_, 5, v_decls_447_);
lean_ctor_set(v_reuseFailAlloc_465_, 6, v_userNames_448_);
lean_ctor_set(v_reuseFailAlloc_465_, 7, v_lAssignment_449_);
lean_ctor_set(v_reuseFailAlloc_465_, 8, v___x_457_);
lean_ctor_set(v_reuseFailAlloc_465_, 9, v_dAssignment_451_);
lean_ctor_set(v_reuseFailAlloc_465_, 10, v_instanceTypedMVars_452_);
v___x_459_ = v_reuseFailAlloc_465_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
lean_object* v___x_461_; 
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 0, v___x_459_);
v___x_461_ = v___x_440_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_459_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v_cache_435_);
lean_ctor_set(v_reuseFailAlloc_464_, 2, v_zetaDeltaFVarIds_436_);
lean_ctor_set(v_reuseFailAlloc_464_, 3, v_postponed_437_);
lean_ctor_set(v_reuseFailAlloc_464_, 4, v_diag_438_);
v___x_461_ = v_reuseFailAlloc_464_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = lean_st_ref_put(v___y_431_, v___x_461_);
v___x_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_463_, 0, v___x_456_);
return v___x_463_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg___boxed(lean_object* v_mvarId_468_, lean_object* v_val_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg(v_mvarId_468_, v_val_469_, v___y_470_);
lean_dec(v___y_470_);
return v_res_472_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__2));
v___x_478_ = l_Lean_stringToMessageData(v___x_477_);
return v___x_478_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5(void){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__4));
v___x_481_ = l_Lean_stringToMessageData(v___x_480_);
return v___x_481_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__6));
v___x_484_ = l_Lean_stringToMessageData(v___x_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9(lean_object* v_fvarId_485_, lean_object* v_mvarId_486_, lean_object* v_as_487_, size_t v_i_488_, size_t v_stop_489_, lean_object* v_b_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
lean_object* v_a_497_; uint8_t v___x_501_; 
v___x_501_ = lean_usize_dec_eq(v_i_488_, v_stop_489_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; 
v___x_502_ = lean_array_uget(v_as_487_, v_i_488_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v___x_503_; 
v___x_503_ = lean_box(0);
v_a_497_ = v___x_503_;
goto v___jp_496_;
}
else
{
lean_object* v_val_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_541_; 
v_val_504_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_541_ == 0)
{
v___x_506_ = v___x_502_;
v_isShared_507_ = v_isSharedCheck_541_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_val_504_);
lean_dec(v___x_502_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_541_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_508_; uint8_t v___x_509_; 
v___x_508_ = l_Lean_LocalDecl_fvarId(v_val_504_);
v___x_509_ = l_Lean_instBEqFVarId_beq(v___x_508_, v_fvarId_485_);
lean_dec(v___x_508_);
if (v___x_509_ == 0)
{
lean_object* v___x_510_; uint8_t v___x_511_; lean_object* v___x_512_; 
v___x_510_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__1));
v___x_511_ = 1;
lean_inc(v_fvarId_485_);
lean_inc(v_val_504_);
v___x_512_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg(v_val_504_, v_fvarId_485_, v___x_511_, v___y_492_);
if (lean_obj_tag(v___x_512_) == 0)
{
lean_object* v_a_513_; uint8_t v___x_514_; 
v_a_513_ = lean_ctor_get(v___x_512_, 0);
lean_inc(v_a_513_);
lean_dec_ref_known(v___x_512_, 1);
v___x_514_ = lean_unbox(v_a_513_);
lean_dec(v_a_513_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; 
lean_del_object(v___x_506_);
lean_dec(v_val_504_);
v___x_515_ = lean_box(0);
v_a_497_ = v___x_515_;
goto v___jp_496_;
}
else
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_528_; 
v___x_516_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3);
v___x_517_ = l_Lean_LocalDecl_toExpr(v_val_504_);
v___x_518_ = l_Lean_MessageData_ofExpr(v___x_517_);
v___x_519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_519_, 0, v___x_516_);
lean_ctor_set(v___x_519_, 1, v___x_518_);
v___x_520_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5);
v___x_521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_521_, 0, v___x_519_);
lean_ctor_set(v___x_521_, 1, v___x_520_);
lean_inc(v_fvarId_485_);
v___x_522_ = l_Lean_mkFVar(v_fvarId_485_);
v___x_523_ = l_Lean_MessageData_ofExpr(v___x_522_);
v___x_524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_524_, 0, v___x_521_);
lean_ctor_set(v___x_524_, 1, v___x_523_);
v___x_525_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7);
v___x_526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_524_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 0, v___x_526_);
v___x_528_ = v___x_506_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_526_);
v___x_528_ = v_reuseFailAlloc_531_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
lean_object* v___x_529_; 
lean_inc(v_mvarId_486_);
v___x_529_ = l_Lean_Meta_throwTacticEx___redArg(v___x_510_, v_mvarId_486_, v___x_528_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v_a_530_; 
v_a_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc(v_a_530_);
lean_dec_ref_known(v___x_529_, 1);
v_a_497_ = v_a_530_;
goto v___jp_496_;
}
else
{
lean_dec(v_mvarId_486_);
lean_dec(v_fvarId_485_);
return v___x_529_;
}
}
}
}
else
{
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_539_; 
lean_del_object(v___x_506_);
lean_dec(v_val_504_);
lean_dec(v_mvarId_486_);
lean_dec(v_fvarId_485_);
v_a_532_ = lean_ctor_get(v___x_512_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_512_);
if (v_isSharedCheck_539_ == 0)
{
v___x_534_ = v___x_512_;
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_512_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_a_532_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
else
{
lean_object* v___x_540_; 
lean_del_object(v___x_506_);
lean_dec(v_val_504_);
v___x_540_ = lean_box(0);
v_a_497_ = v___x_540_;
goto v___jp_496_;
}
}
}
}
else
{
lean_object* v___x_542_; 
lean_dec(v_mvarId_486_);
lean_dec(v_fvarId_485_);
v___x_542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_542_, 0, v_b_490_);
return v___x_542_;
}
v___jp_496_:
{
size_t v___x_498_; size_t v___x_499_; 
v___x_498_ = ((size_t)1ULL);
v___x_499_ = lean_usize_add(v_i_488_, v___x_498_);
v_i_488_ = v___x_499_;
v_b_490_ = v_a_497_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___boxed(lean_object* v_fvarId_543_, lean_object* v_mvarId_544_, lean_object* v_as_545_, lean_object* v_i_546_, lean_object* v_stop_547_, lean_object* v_b_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
size_t v_i_boxed_554_; size_t v_stop_boxed_555_; lean_object* v_res_556_; 
v_i_boxed_554_ = lean_unbox_usize(v_i_546_);
lean_dec(v_i_546_);
v_stop_boxed_555_ = lean_unbox_usize(v_stop_547_);
lean_dec(v_stop_547_);
v_res_556_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9(v_fvarId_543_, v_mvarId_544_, v_as_545_, v_i_boxed_554_, v_stop_boxed_555_, v_b_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec_ref(v_as_545_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(lean_object* v_fvarId_557_, lean_object* v_mvarId_558_, lean_object* v_as_559_, size_t v_i_560_, size_t v_stop_561_, lean_object* v_b_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
lean_object* v_a_569_; uint8_t v___x_573_; 
v___x_573_ = lean_usize_dec_eq(v_i_560_, v_stop_561_);
if (v___x_573_ == 0)
{
lean_object* v___x_574_; 
v___x_574_ = lean_array_uget(v_as_559_, v_i_560_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v___x_575_; 
v___x_575_ = lean_box(0);
v_a_569_ = v___x_575_;
goto v___jp_568_;
}
else
{
lean_object* v_val_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_613_; 
v_val_576_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_613_ == 0)
{
v___x_578_ = v___x_574_;
v_isShared_579_ = v_isSharedCheck_613_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_val_576_);
lean_dec(v___x_574_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_613_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_580_; uint8_t v___x_581_; 
v___x_580_ = l_Lean_LocalDecl_fvarId(v_val_576_);
v___x_581_ = l_Lean_instBEqFVarId_beq(v___x_580_, v_fvarId_557_);
lean_dec(v___x_580_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; uint8_t v___x_583_; lean_object* v___x_584_; 
v___x_582_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__1));
v___x_583_ = 1;
lean_inc(v_fvarId_557_);
lean_inc(v_val_576_);
v___x_584_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg(v_val_576_, v_fvarId_557_, v___x_583_, v___y_564_);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v_a_585_; uint8_t v___x_586_; 
v_a_585_ = lean_ctor_get(v___x_584_, 0);
lean_inc(v_a_585_);
lean_dec_ref_known(v___x_584_, 1);
v___x_586_ = lean_unbox(v_a_585_);
lean_dec(v_a_585_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; 
lean_del_object(v___x_578_);
lean_dec(v_val_576_);
v___x_587_ = lean_box(0);
v_a_569_ = v___x_587_;
goto v___jp_568_;
}
else
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_600_; 
v___x_588_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3);
v___x_589_ = l_Lean_LocalDecl_toExpr(v_val_576_);
v___x_590_ = l_Lean_MessageData_ofExpr(v___x_589_);
v___x_591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_588_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
v___x_592_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5);
v___x_593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_591_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
lean_inc(v_fvarId_557_);
v___x_594_ = l_Lean_mkFVar(v_fvarId_557_);
v___x_595_ = l_Lean_MessageData_ofExpr(v___x_594_);
v___x_596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_593_);
lean_ctor_set(v___x_596_, 1, v___x_595_);
v___x_597_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7);
v___x_598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_596_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 0, v___x_598_);
v___x_600_ = v___x_578_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_598_);
v___x_600_ = v_reuseFailAlloc_603_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
lean_object* v___x_601_; 
lean_inc(v_mvarId_558_);
v___x_601_ = l_Lean_Meta_throwTacticEx___redArg(v___x_582_, v_mvarId_558_, v___x_600_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v_a_602_; 
v_a_602_ = lean_ctor_get(v___x_601_, 0);
lean_inc(v_a_602_);
lean_dec_ref_known(v___x_601_, 1);
v_a_569_ = v_a_602_;
goto v___jp_568_;
}
else
{
lean_dec(v_mvarId_558_);
lean_dec(v_fvarId_557_);
return v___x_601_;
}
}
}
}
else
{
lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
lean_del_object(v___x_578_);
lean_dec(v_val_576_);
lean_dec(v_mvarId_558_);
lean_dec(v_fvarId_557_);
v_a_604_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_611_ == 0)
{
v___x_606_ = v___x_584_;
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_dec(v___x_584_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_604_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
else
{
lean_object* v___x_612_; 
lean_del_object(v___x_578_);
lean_dec(v_val_576_);
v___x_612_ = lean_box(0);
v_a_569_ = v___x_612_;
goto v___jp_568_;
}
}
}
}
else
{
lean_object* v___x_614_; 
lean_dec(v_mvarId_558_);
lean_dec(v_fvarId_557_);
v___x_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_614_, 0, v_b_562_);
return v___x_614_;
}
v___jp_568_:
{
size_t v___x_570_; size_t v___x_571_; lean_object* v___x_572_; 
v___x_570_ = ((size_t)1ULL);
v___x_571_ = lean_usize_add(v_i_560_, v___x_570_);
v___x_572_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9(v_fvarId_557_, v_mvarId_558_, v_as_559_, v___x_571_, v_stop_561_, v_a_569_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
return v___x_572_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5___boxed(lean_object* v_fvarId_615_, lean_object* v_mvarId_616_, lean_object* v_as_617_, lean_object* v_i_618_, lean_object* v_stop_619_, lean_object* v_b_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
size_t v_i_boxed_626_; size_t v_stop_boxed_627_; lean_object* v_res_628_; 
v_i_boxed_626_ = lean_unbox_usize(v_i_618_);
lean_dec(v_i_618_);
v_stop_boxed_627_ = lean_unbox_usize(v_stop_619_);
lean_dec(v_stop_619_);
v_res_628_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_615_, v_mvarId_616_, v_as_617_, v_i_boxed_626_, v_stop_boxed_627_, v_b_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec_ref(v_as_617_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6(lean_object* v_fvarId_629_, lean_object* v_mvarId_630_, lean_object* v_x_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
if (lean_obj_tag(v_x_631_) == 0)
{
lean_object* v_cs_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_651_; 
v_cs_637_ = lean_ctor_get(v_x_631_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v_x_631_);
if (v_isSharedCheck_651_ == 0)
{
v___x_639_ = v_x_631_;
v_isShared_640_ = v_isSharedCheck_651_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_cs_637_);
lean_dec(v_x_631_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_651_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; uint8_t v___x_644_; 
v___x_641_ = lean_unsigned_to_nat(0u);
v___x_642_ = lean_array_get_size(v_cs_637_);
v___x_643_ = lean_box(0);
v___x_644_ = lean_nat_dec_lt(v___x_641_, v___x_642_);
if (v___x_644_ == 0)
{
lean_object* v___x_646_; 
lean_dec_ref(v_cs_637_);
lean_dec(v_mvarId_630_);
lean_dec(v_fvarId_629_);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 0, v___x_643_);
v___x_646_ = v___x_639_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_643_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
else
{
size_t v___x_648_; size_t v___x_649_; lean_object* v___x_650_; 
lean_del_object(v___x_639_);
v___x_648_ = ((size_t)0ULL);
v___x_649_ = lean_usize_of_nat(v___x_642_);
v___x_650_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(v_fvarId_629_, v_mvarId_630_, v_cs_637_, v___x_648_, v___x_649_, v___x_643_, v___y_632_, v___y_633_, v___y_634_, v___y_635_);
lean_dec_ref(v_cs_637_);
return v___x_650_;
}
}
}
else
{
lean_object* v_vs_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_666_; 
v_vs_652_ = lean_ctor_get(v_x_631_, 0);
v_isSharedCheck_666_ = !lean_is_exclusive(v_x_631_);
if (v_isSharedCheck_666_ == 0)
{
v___x_654_ = v_x_631_;
v_isShared_655_ = v_isSharedCheck_666_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_vs_652_);
lean_dec(v_x_631_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_666_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_656_ = lean_unsigned_to_nat(0u);
v___x_657_ = lean_array_get_size(v_vs_652_);
v___x_658_ = lean_box(0);
v___x_659_ = lean_nat_dec_lt(v___x_656_, v___x_657_);
if (v___x_659_ == 0)
{
lean_object* v___x_661_; 
lean_dec_ref(v_vs_652_);
lean_dec(v_mvarId_630_);
lean_dec(v_fvarId_629_);
if (v_isShared_655_ == 0)
{
lean_ctor_set_tag(v___x_654_, 0);
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
size_t v___x_663_; size_t v___x_664_; lean_object* v___x_665_; 
lean_del_object(v___x_654_);
v___x_663_ = ((size_t)0ULL);
v___x_664_ = lean_usize_of_nat(v___x_657_);
v___x_665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_629_, v_mvarId_630_, v_vs_652_, v___x_663_, v___x_664_, v___x_658_, v___y_632_, v___y_633_, v___y_634_, v___y_635_);
lean_dec_ref(v_vs_652_);
return v___x_665_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(lean_object* v_fvarId_667_, lean_object* v_mvarId_668_, lean_object* v_as_669_, size_t v_i_670_, size_t v_stop_671_, lean_object* v_b_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
uint8_t v___x_678_; 
v___x_678_ = lean_usize_dec_eq(v_i_670_, v_stop_671_);
if (v___x_678_ == 0)
{
lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_679_ = lean_array_uget_borrowed(v_as_669_, v_i_670_);
lean_inc(v___x_679_);
lean_inc(v_mvarId_668_);
lean_inc(v_fvarId_667_);
v___x_680_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6(v_fvarId_667_, v_mvarId_668_, v___x_679_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v_a_681_; size_t v___x_682_; size_t v___x_683_; 
v_a_681_ = lean_ctor_get(v___x_680_, 0);
lean_inc(v_a_681_);
lean_dec_ref_known(v___x_680_, 1);
v___x_682_ = ((size_t)1ULL);
v___x_683_ = lean_usize_add(v_i_670_, v___x_682_);
v_i_670_ = v___x_683_;
v_b_672_ = v_a_681_;
goto _start;
}
else
{
lean_dec(v_mvarId_668_);
lean_dec(v_fvarId_667_);
return v___x_680_;
}
}
else
{
lean_object* v___x_685_; 
lean_dec(v_mvarId_668_);
lean_dec(v_fvarId_667_);
v___x_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_685_, 0, v_b_672_);
return v___x_685_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7___boxed(lean_object* v_fvarId_686_, lean_object* v_mvarId_687_, lean_object* v_as_688_, lean_object* v_i_689_, lean_object* v_stop_690_, lean_object* v_b_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_){
_start:
{
size_t v_i_boxed_697_; size_t v_stop_boxed_698_; lean_object* v_res_699_; 
v_i_boxed_697_ = lean_unbox_usize(v_i_689_);
lean_dec(v_i_689_);
v_stop_boxed_698_ = lean_unbox_usize(v_stop_690_);
lean_dec(v_stop_690_);
v_res_699_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(v_fvarId_686_, v_mvarId_687_, v_as_688_, v_i_boxed_697_, v_stop_boxed_698_, v_b_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec_ref(v_as_688_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6___boxed(lean_object* v_fvarId_700_, lean_object* v_mvarId_701_, lean_object* v_x_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6(v_fvarId_700_, v_mvarId_701_, v_x_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6(lean_object* v_fvarId_709_, lean_object* v_mvarId_710_, lean_object* v_t_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_){
_start:
{
lean_object* v_root_717_; lean_object* v_tail_718_; lean_object* v___x_719_; 
v_root_717_ = lean_ctor_get(v_t_711_, 0);
lean_inc_ref(v_root_717_);
v_tail_718_ = lean_ctor_get(v_t_711_, 1);
lean_inc_ref(v_tail_718_);
lean_dec_ref(v_t_711_);
lean_inc(v_mvarId_710_);
lean_inc(v_fvarId_709_);
v___x_719_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6(v_fvarId_709_, v_mvarId_710_, v_root_717_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_733_; 
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_733_ == 0)
{
lean_object* v_unused_734_; 
v_unused_734_ = lean_ctor_get(v___x_719_, 0);
lean_dec(v_unused_734_);
v___x_721_ = v___x_719_;
v_isShared_722_ = v_isSharedCheck_733_;
goto v_resetjp_720_;
}
else
{
lean_dec(v___x_719_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_733_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; uint8_t v___x_726_; 
v___x_723_ = lean_unsigned_to_nat(0u);
v___x_724_ = lean_array_get_size(v_tail_718_);
v___x_725_ = lean_box(0);
v___x_726_ = lean_nat_dec_lt(v___x_723_, v___x_724_);
if (v___x_726_ == 0)
{
lean_object* v___x_728_; 
lean_dec_ref(v_tail_718_);
lean_dec(v_mvarId_710_);
lean_dec(v_fvarId_709_);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 0, v___x_725_);
v___x_728_ = v___x_721_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_725_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
else
{
size_t v___x_730_; size_t v___x_731_; lean_object* v___x_732_; 
lean_del_object(v___x_721_);
v___x_730_ = ((size_t)0ULL);
v___x_731_ = lean_usize_of_nat(v___x_724_);
v___x_732_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_709_, v_mvarId_710_, v_tail_718_, v___x_730_, v___x_731_, v___x_725_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
lean_dec_ref(v_tail_718_);
return v___x_732_;
}
}
}
else
{
lean_dec_ref(v_tail_718_);
lean_dec(v_mvarId_710_);
lean_dec(v_fvarId_709_);
return v___x_719_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6___boxed(lean_object* v_fvarId_735_, lean_object* v_mvarId_736_, lean_object* v_t_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6(v_fvarId_735_, v_mvarId_736_, v_t_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
return v_res_743_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4(lean_object* v_fvarId_745_, lean_object* v_mvarId_746_, lean_object* v_x_747_, size_t v_x_748_, size_t v_x_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
if (lean_obj_tag(v_x_747_) == 0)
{
lean_object* v_cs_755_; lean_object* v___x_756_; size_t v___x_757_; lean_object* v_j_758_; lean_object* v___x_759_; size_t v___x_760_; size_t v___x_761_; size_t v___x_762_; size_t v___x_763_; size_t v___x_764_; size_t v___x_765_; lean_object* v___x_766_; 
v_cs_755_ = lean_ctor_get(v_x_747_, 0);
lean_inc_ref(v_cs_755_);
lean_dec_ref_known(v_x_747_, 1);
v___x_756_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0);
v___x_757_ = lean_usize_shift_right(v_x_748_, v_x_749_);
v_j_758_ = lean_usize_to_nat(v___x_757_);
v___x_759_ = lean_array_get_borrowed(v___x_756_, v_cs_755_, v_j_758_);
v___x_760_ = ((size_t)1ULL);
v___x_761_ = lean_usize_shift_left(v___x_760_, v_x_749_);
v___x_762_ = lean_usize_sub(v___x_761_, v___x_760_);
v___x_763_ = lean_usize_land(v_x_748_, v___x_762_);
v___x_764_ = ((size_t)5ULL);
v___x_765_ = lean_usize_sub(v_x_749_, v___x_764_);
lean_inc(v___x_759_);
lean_inc(v_mvarId_746_);
lean_inc(v_fvarId_745_);
v___x_766_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4(v_fvarId_745_, v_mvarId_746_, v___x_759_, v___x_763_, v___x_765_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_781_; 
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_781_ == 0)
{
lean_object* v_unused_782_; 
v_unused_782_ = lean_ctor_get(v___x_766_, 0);
lean_dec(v_unused_782_);
v___x_768_ = v___x_766_;
v_isShared_769_ = v_isSharedCheck_781_;
goto v_resetjp_767_;
}
else
{
lean_dec(v___x_766_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_781_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; uint8_t v___x_774_; 
v___x_770_ = lean_unsigned_to_nat(1u);
v___x_771_ = lean_nat_add(v_j_758_, v___x_770_);
lean_dec(v_j_758_);
v___x_772_ = lean_array_get_size(v_cs_755_);
v___x_773_ = lean_box(0);
v___x_774_ = lean_nat_dec_lt(v___x_771_, v___x_772_);
if (v___x_774_ == 0)
{
lean_object* v___x_776_; 
lean_dec(v___x_771_);
lean_dec_ref(v_cs_755_);
lean_dec(v_mvarId_746_);
lean_dec(v_fvarId_745_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 0, v___x_773_);
v___x_776_ = v___x_768_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_773_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
else
{
size_t v___x_778_; size_t v___x_779_; lean_object* v___x_780_; 
lean_del_object(v___x_768_);
v___x_778_ = lean_usize_of_nat(v___x_771_);
lean_dec(v___x_771_);
v___x_779_ = lean_usize_of_nat(v___x_772_);
v___x_780_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(v_fvarId_745_, v_mvarId_746_, v_cs_755_, v___x_778_, v___x_779_, v___x_773_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
lean_dec_ref(v_cs_755_);
return v___x_780_;
}
}
}
else
{
lean_dec(v_j_758_);
lean_dec_ref(v_cs_755_);
lean_dec(v_mvarId_746_);
lean_dec(v_fvarId_745_);
return v___x_766_;
}
}
else
{
lean_object* v_vs_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_797_; 
v_vs_783_ = lean_ctor_get(v_x_747_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v_x_747_);
if (v_isSharedCheck_797_ == 0)
{
v___x_785_ = v_x_747_;
v_isShared_786_ = v_isSharedCheck_797_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_vs_783_);
lean_dec(v_x_747_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_797_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; uint8_t v___x_790_; 
v___x_787_ = lean_usize_to_nat(v_x_748_);
v___x_788_ = lean_array_get_size(v_vs_783_);
v___x_789_ = lean_box(0);
v___x_790_ = lean_nat_dec_lt(v___x_787_, v___x_788_);
if (v___x_790_ == 0)
{
lean_object* v___x_792_; 
lean_dec(v___x_787_);
lean_dec_ref(v_vs_783_);
lean_dec(v_mvarId_746_);
lean_dec(v_fvarId_745_);
if (v_isShared_786_ == 0)
{
lean_ctor_set_tag(v___x_785_, 0);
lean_ctor_set(v___x_785_, 0, v___x_789_);
v___x_792_ = v___x_785_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_789_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
else
{
size_t v___x_794_; size_t v___x_795_; lean_object* v___x_796_; 
lean_del_object(v___x_785_);
v___x_794_ = lean_usize_of_nat(v___x_787_);
lean_dec(v___x_787_);
v___x_795_ = lean_usize_of_nat(v___x_788_);
v___x_796_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_745_, v_mvarId_746_, v_vs_783_, v___x_794_, v___x_795_, v___x_789_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
lean_dec_ref(v_vs_783_);
return v___x_796_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___boxed(lean_object* v_fvarId_798_, lean_object* v_mvarId_799_, lean_object* v_x_800_, lean_object* v_x_801_, lean_object* v_x_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
size_t v_x_8359__boxed_808_; size_t v_x_8360__boxed_809_; lean_object* v_res_810_; 
v_x_8359__boxed_808_ = lean_unbox_usize(v_x_801_);
lean_dec(v_x_801_);
v_x_8360__boxed_809_ = lean_unbox_usize(v_x_802_);
lean_dec(v_x_802_);
v_res_810_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4(v_fvarId_798_, v_mvarId_799_, v_x_800_, v_x_8359__boxed_808_, v_x_8360__boxed_809_, v___y_803_, v___y_804_, v___y_805_, v___y_806_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1(lean_object* v_fvarId_811_, lean_object* v_mvarId_812_, lean_object* v_t_813_, lean_object* v_start_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
lean_object* v___x_820_; uint8_t v___x_821_; 
v___x_820_ = lean_unsigned_to_nat(0u);
v___x_821_ = lean_nat_dec_eq(v_start_814_, v___x_820_);
if (v___x_821_ == 0)
{
lean_object* v_root_822_; lean_object* v_tail_823_; size_t v_shift_824_; lean_object* v_tailOff_825_; uint8_t v___x_826_; 
v_root_822_ = lean_ctor_get(v_t_813_, 0);
lean_inc_ref(v_root_822_);
v_tail_823_ = lean_ctor_get(v_t_813_, 1);
lean_inc_ref(v_tail_823_);
v_shift_824_ = lean_ctor_get_usize(v_t_813_, 4);
v_tailOff_825_ = lean_ctor_get(v_t_813_, 3);
lean_inc(v_tailOff_825_);
lean_dec_ref(v_t_813_);
v___x_826_ = lean_nat_dec_le(v_tailOff_825_, v_start_814_);
if (v___x_826_ == 0)
{
size_t v___x_827_; lean_object* v___x_828_; 
lean_dec(v_tailOff_825_);
v___x_827_ = lean_usize_of_nat(v_start_814_);
lean_inc(v_mvarId_812_);
lean_inc(v_fvarId_811_);
v___x_828_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4(v_fvarId_811_, v_mvarId_812_, v_root_822_, v___x_827_, v_shift_824_, v___y_815_, v___y_816_, v___y_817_, v___y_818_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_841_; 
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_841_ == 0)
{
lean_object* v_unused_842_; 
v_unused_842_ = lean_ctor_get(v___x_828_, 0);
lean_dec(v_unused_842_);
v___x_830_ = v___x_828_;
v_isShared_831_ = v_isSharedCheck_841_;
goto v_resetjp_829_;
}
else
{
lean_dec(v___x_828_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_841_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_832_; lean_object* v___x_833_; uint8_t v___x_834_; 
v___x_832_ = lean_array_get_size(v_tail_823_);
v___x_833_ = lean_box(0);
v___x_834_ = lean_nat_dec_lt(v___x_820_, v___x_832_);
if (v___x_834_ == 0)
{
lean_object* v___x_836_; 
lean_dec_ref(v_tail_823_);
lean_dec(v_mvarId_812_);
lean_dec(v_fvarId_811_);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v___x_833_);
v___x_836_ = v___x_830_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v___x_833_);
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
lean_del_object(v___x_830_);
v___x_838_ = ((size_t)0ULL);
v___x_839_ = lean_usize_of_nat(v___x_832_);
v___x_840_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_811_, v_mvarId_812_, v_tail_823_, v___x_838_, v___x_839_, v___x_833_, v___y_815_, v___y_816_, v___y_817_, v___y_818_);
lean_dec_ref(v_tail_823_);
return v___x_840_;
}
}
}
else
{
lean_dec_ref(v_tail_823_);
lean_dec(v_mvarId_812_);
lean_dec(v_fvarId_811_);
return v___x_828_;
}
}
else
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; uint8_t v___x_846_; 
lean_dec_ref(v_root_822_);
v___x_843_ = lean_nat_sub(v_start_814_, v_tailOff_825_);
lean_dec(v_tailOff_825_);
v___x_844_ = lean_array_get_size(v_tail_823_);
v___x_845_ = lean_box(0);
v___x_846_ = lean_nat_dec_lt(v___x_843_, v___x_844_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; 
lean_dec(v___x_843_);
lean_dec_ref(v_tail_823_);
lean_dec(v_mvarId_812_);
lean_dec(v_fvarId_811_);
v___x_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_847_, 0, v___x_845_);
return v___x_847_;
}
else
{
size_t v___x_848_; size_t v___x_849_; lean_object* v___x_850_; 
v___x_848_ = lean_usize_of_nat(v___x_843_);
lean_dec(v___x_843_);
v___x_849_ = lean_usize_of_nat(v___x_844_);
v___x_850_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_811_, v_mvarId_812_, v_tail_823_, v___x_848_, v___x_849_, v___x_845_, v___y_815_, v___y_816_, v___y_817_, v___y_818_);
lean_dec_ref(v_tail_823_);
return v___x_850_;
}
}
}
else
{
lean_object* v___x_851_; 
v___x_851_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6(v_fvarId_811_, v_mvarId_812_, v_t_813_, v___y_815_, v___y_816_, v___y_817_, v___y_818_);
return v___x_851_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1___boxed(lean_object* v_fvarId_852_, lean_object* v_mvarId_853_, lean_object* v_t_854_, lean_object* v_start_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1(v_fvarId_852_, v_mvarId_853_, v_t_854_, v_start_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
lean_dec(v_start_855_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1(lean_object* v_fvarId_862_, lean_object* v_mvarId_863_, lean_object* v_lctx_864_, lean_object* v_start_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v_decls_871_; lean_object* v___x_872_; 
v_decls_871_ = lean_ctor_get(v_lctx_864_, 1);
lean_inc_ref(v_decls_871_);
lean_dec_ref(v_lctx_864_);
v___x_872_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1(v_fvarId_862_, v_mvarId_863_, v_decls_871_, v_start_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1___boxed(lean_object* v_fvarId_873_, lean_object* v_mvarId_874_, lean_object* v_lctx_875_, lean_object* v_start_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1(v_fvarId_873_, v_mvarId_874_, v_lctx_875_, v_start_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
lean_dec(v_start_876_);
return v_res_882_;
}
}
static lean_object* _init_l_Lean_MVarId_clear___lam__0___closed__1(void){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_884_ = ((lean_object*)(l_Lean_MVarId_clear___lam__0___closed__0));
v___x_885_ = l_Lean_stringToMessageData(v___x_884_);
return v___x_885_;
}
}
static lean_object* _init_l_Lean_MVarId_clear___lam__0___closed__3(void){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_887_ = ((lean_object*)(l_Lean_MVarId_clear___lam__0___closed__2));
v___x_888_ = l_Lean_stringToMessageData(v___x_887_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clear___lam__0(lean_object* v_mvarId_889_, lean_object* v___x_890_, lean_object* v_fvarId_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
lean_object* v___x_897_; 
lean_inc(v___x_890_);
lean_inc(v_mvarId_889_);
v___x_897_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_889_, v___x_890_, v___y_892_, v___y_893_, v___y_894_, v___y_895_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v_lctx_898_; lean_object* v___y_900_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v___y_903_; lean_object* v___y_904_; lean_object* v___y_905_; lean_object* v___y_906_; lean_object* v___y_932_; lean_object* v___y_933_; lean_object* v___y_934_; lean_object* v___y_935_; uint8_t v___x_992_; 
lean_dec_ref_known(v___x_897_, 1);
v_lctx_898_ = lean_ctor_get(v___y_892_, 2);
lean_inc_ref(v_lctx_898_);
v___x_992_ = l_Lean_LocalContext_contains(v_lctx_898_, v_fvarId_891_);
if (v___x_992_ == 0)
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_993_ = lean_obj_once(&l_Lean_MVarId_clear___lam__0___closed__3, &l_Lean_MVarId_clear___lam__0___closed__3_once, _init_l_Lean_MVarId_clear___lam__0___closed__3);
lean_inc(v_fvarId_891_);
v___x_994_ = l_Lean_mkFVar(v_fvarId_891_);
v___x_995_ = l_Lean_MessageData_ofExpr(v___x_994_);
v___x_996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_993_);
lean_ctor_set(v___x_996_, 1, v___x_995_);
v___x_997_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7);
v___x_998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_996_);
lean_ctor_set(v___x_998_, 1, v___x_997_);
v___x_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_999_, 0, v___x_998_);
lean_inc(v_mvarId_889_);
lean_inc(v___x_890_);
v___x_1000_ = l_Lean_Meta_throwTacticEx___redArg(v___x_890_, v_mvarId_889_, v___x_999_, v___y_892_, v___y_893_, v___y_894_, v___y_895_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_dec_ref_known(v___x_1000_, 1);
v___y_932_ = v___y_892_;
v___y_933_ = v___y_893_;
v___y_934_ = v___y_894_;
v___y_935_ = v___y_895_;
goto v___jp_931_;
}
else
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1008_; 
lean_dec_ref(v_lctx_898_);
lean_dec_ref(v___y_892_);
lean_dec(v_fvarId_891_);
lean_dec(v___x_890_);
lean_dec(v_mvarId_889_);
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1003_ = v___x_1000_;
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_1000_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1006_; 
if (v_isShared_1004_ == 0)
{
v___x_1006_ = v___x_1003_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_a_1001_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
else
{
v___y_932_ = v___y_892_;
v___y_933_ = v___y_893_;
v___y_934_ = v___y_894_;
v___y_935_ = v___y_895_;
goto v___jp_931_;
}
v___jp_899_:
{
lean_object* v_localInstances_907_; lean_object* v___x_908_; lean_object* v___x_909_; uint8_t v___x_910_; lean_object* v___x_911_; 
v_localInstances_907_ = lean_ctor_get(v___y_903_, 3);
v___x_908_ = l_Lean_LocalContext_erase(v_lctx_898_, v_fvarId_891_);
lean_inc_ref(v_localInstances_907_);
v___x_909_ = l_Lean_LocalInstances_erase(v_localInstances_907_, v_fvarId_891_);
v___x_910_ = 2;
v___x_911_ = l_Lean_Meta_mkFreshExprMVarAt(v___x_908_, v___x_909_, v___y_902_, v___x_910_, v___y_900_, v___y_901_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
lean_dec_ref(v___y_903_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v_a_912_; lean_object* v___x_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_921_; 
v_a_912_ = lean_ctor_get(v___x_911_, 0);
lean_inc_n(v_a_912_, 2);
lean_dec_ref_known(v___x_911_, 1);
v___x_913_ = l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg(v_mvarId_889_, v_a_912_, v___y_904_);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_921_ == 0)
{
lean_object* v_unused_922_; 
v_unused_922_ = lean_ctor_get(v___x_913_, 0);
lean_dec(v_unused_922_);
v___x_915_ = v___x_913_;
v_isShared_916_ = v_isSharedCheck_921_;
goto v_resetjp_914_;
}
else
{
lean_dec(v___x_913_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_921_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_917_; lean_object* v___x_919_; 
v___x_917_ = l_Lean_Expr_mvarId_x21(v_a_912_);
lean_dec(v_a_912_);
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 0, v___x_917_);
v___x_919_ = v___x_915_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_917_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
else
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_930_; 
lean_dec(v_mvarId_889_);
v_a_923_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_930_ == 0)
{
v___x_925_ = v___x_911_;
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_911_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_926_ == 0)
{
v___x_928_ = v___x_925_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_a_923_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
v___jp_931_:
{
lean_object* v___x_936_; 
lean_inc(v_mvarId_889_);
v___x_936_ = l_Lean_MVarId_getTag(v_mvarId_889_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v_a_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v_a_937_ = lean_ctor_get(v___x_936_, 0);
lean_inc(v_a_937_);
lean_dec_ref_known(v___x_936_, 1);
v___x_938_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_lctx_898_);
lean_inc(v_mvarId_889_);
lean_inc(v_fvarId_891_);
v___x_939_ = l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1(v_fvarId_891_, v_mvarId_889_, v_lctx_898_, v___x_938_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
if (lean_obj_tag(v___x_939_) == 0)
{
lean_object* v___x_940_; 
lean_dec_ref_known(v___x_939_, 1);
lean_inc(v_mvarId_889_);
v___x_940_ = l_Lean_MVarId_getDecl(v_mvarId_889_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v_a_941_; lean_object* v_type_942_; lean_object* v___x_943_; lean_object* v_a_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_967_; 
v_a_941_ = lean_ctor_get(v___x_940_, 0);
lean_inc(v_a_941_);
lean_dec_ref_known(v___x_940_, 1);
v_type_942_ = lean_ctor_get(v_a_941_, 2);
lean_inc_ref_n(v_type_942_, 2);
lean_dec(v_a_941_);
lean_inc(v_fvarId_891_);
v___x_943_ = l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3___redArg(v_type_942_, v_fvarId_891_, v___y_933_);
v_a_944_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_967_ == 0)
{
v___x_946_ = v___x_943_;
v_isShared_947_ = v_isSharedCheck_967_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_a_944_);
lean_dec(v___x_943_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_967_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
uint8_t v___x_948_; 
v___x_948_ = lean_unbox(v_a_944_);
lean_dec(v_a_944_);
if (v___x_948_ == 0)
{
lean_del_object(v___x_946_);
lean_dec(v___x_890_);
v___y_900_ = v_a_937_;
v___y_901_ = v___x_938_;
v___y_902_ = v_type_942_;
v___y_903_ = v___y_932_;
v___y_904_ = v___y_933_;
v___y_905_ = v___y_934_;
v___y_906_ = v___y_935_;
goto v___jp_899_;
}
else
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_956_; 
v___x_949_ = lean_obj_once(&l_Lean_MVarId_clear___lam__0___closed__1, &l_Lean_MVarId_clear___lam__0___closed__1_once, _init_l_Lean_MVarId_clear___lam__0___closed__1);
lean_inc(v_fvarId_891_);
v___x_950_ = l_Lean_mkFVar(v_fvarId_891_);
v___x_951_ = l_Lean_MessageData_ofExpr(v___x_950_);
v___x_952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_952_, 0, v___x_949_);
lean_ctor_set(v___x_952_, 1, v___x_951_);
v___x_953_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7);
v___x_954_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_952_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
if (v_isShared_947_ == 0)
{
lean_ctor_set_tag(v___x_946_, 1);
lean_ctor_set(v___x_946_, 0, v___x_954_);
v___x_956_ = v___x_946_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___x_954_);
v___x_956_ = v_reuseFailAlloc_966_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
lean_object* v___x_957_; 
lean_inc(v_mvarId_889_);
v___x_957_ = l_Lean_Meta_throwTacticEx___redArg(v___x_890_, v_mvarId_889_, v___x_956_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_dec_ref_known(v___x_957_, 1);
v___y_900_ = v_a_937_;
v___y_901_ = v___x_938_;
v___y_902_ = v_type_942_;
v___y_903_ = v___y_932_;
v___y_904_ = v___y_933_;
v___y_905_ = v___y_934_;
v___y_906_ = v___y_935_;
goto v___jp_899_;
}
else
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
lean_dec_ref(v_type_942_);
lean_dec(v_a_937_);
lean_dec_ref(v___y_932_);
lean_dec_ref(v_lctx_898_);
lean_dec(v_fvarId_891_);
lean_dec(v_mvarId_889_);
v_a_958_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_965_ == 0)
{
v___x_960_ = v___x_957_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_957_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_963_; 
if (v_isShared_961_ == 0)
{
v___x_963_ = v___x_960_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_a_958_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_975_; 
lean_dec(v_a_937_);
lean_dec_ref(v___y_932_);
lean_dec_ref(v_lctx_898_);
lean_dec(v_fvarId_891_);
lean_dec(v___x_890_);
lean_dec(v_mvarId_889_);
v_a_968_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_975_ == 0)
{
v___x_970_ = v___x_940_;
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v___x_940_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_973_; 
if (v_isShared_971_ == 0)
{
v___x_973_ = v___x_970_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_a_968_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
}
else
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_983_; 
lean_dec(v_a_937_);
lean_dec_ref(v___y_932_);
lean_dec_ref(v_lctx_898_);
lean_dec(v_fvarId_891_);
lean_dec(v___x_890_);
lean_dec(v_mvarId_889_);
v_a_976_ = lean_ctor_get(v___x_939_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_983_ == 0)
{
v___x_978_ = v___x_939_;
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_939_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_981_; 
if (v_isShared_979_ == 0)
{
v___x_981_ = v___x_978_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_a_976_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
}
else
{
lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_991_; 
lean_dec_ref(v___y_932_);
lean_dec_ref(v_lctx_898_);
lean_dec(v_fvarId_891_);
lean_dec(v___x_890_);
lean_dec(v_mvarId_889_);
v_a_984_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_991_ == 0)
{
v___x_986_ = v___x_936_;
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_936_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_989_; 
if (v_isShared_987_ == 0)
{
v___x_989_ = v___x_986_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_a_984_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
}
}
else
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1016_; 
lean_dec_ref(v___y_892_);
lean_dec(v_fvarId_891_);
lean_dec(v___x_890_);
lean_dec(v_mvarId_889_);
v_a_1009_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1011_ = v___x_897_;
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_897_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1014_; 
if (v_isShared_1012_ == 0)
{
v___x_1014_ = v___x_1011_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_a_1009_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clear___lam__0___boxed(lean_object* v_mvarId_1017_, lean_object* v___x_1018_, lean_object* v_fvarId_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Lean_MVarId_clear___lam__0(v_mvarId_1017_, v___x_1018_, v_fvarId_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
lean_dec(v___y_1021_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clear(lean_object* v_mvarId_1026_, lean_object* v_fvarId_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_){
_start:
{
lean_object* v___x_1033_; lean_object* v___f_1034_; lean_object* v___x_1035_; 
v___x_1033_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__1));
lean_inc(v_mvarId_1026_);
v___f_1034_ = lean_alloc_closure((void*)(l_Lean_MVarId_clear___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1034_, 0, v_mvarId_1026_);
lean_closure_set(v___f_1034_, 1, v___x_1033_);
lean_closure_set(v___f_1034_, 2, v_fvarId_1027_);
v___x_1035_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg(v_mvarId_1026_, v___f_1034_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clear___boxed(lean_object* v_mvarId_1036_, lean_object* v_fvarId_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_Lean_MVarId_clear(v_mvarId_1036_, v_fvarId_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_);
lean_dec(v_a_1041_);
lean_dec_ref(v_a_1040_);
lean_dec(v_a_1039_);
lean_dec_ref(v_a_1038_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2(lean_object* v_mvarId_1044_, lean_object* v_val_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg(v_mvarId_1044_, v_val_1045_, v___y_1047_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___boxed(lean_object* v_mvarId_1052_, lean_object* v_val_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2(v_mvarId_1052_, v_val_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3(lean_object* v_00_u03b2_1060_, lean_object* v_x_1061_, lean_object* v_x_1062_, lean_object* v_x_1063_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3___redArg(v_x_1061_, v_x_1062_, v_x_1063_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9(lean_object* v_00_u03b2_1065_, lean_object* v_x_1066_, size_t v_x_1067_, size_t v_x_1068_, lean_object* v_x_1069_, lean_object* v_x_1070_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_x_1066_, v_x_1067_, v_x_1068_, v_x_1069_, v_x_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___boxed(lean_object* v_00_u03b2_1072_, lean_object* v_x_1073_, lean_object* v_x_1074_, lean_object* v_x_1075_, lean_object* v_x_1076_, lean_object* v_x_1077_){
_start:
{
size_t v_x_8880__boxed_1078_; size_t v_x_8881__boxed_1079_; lean_object* v_res_1080_; 
v_x_8880__boxed_1078_ = lean_unbox_usize(v_x_1074_);
lean_dec(v_x_1074_);
v_x_8881__boxed_1079_ = lean_unbox_usize(v_x_1075_);
lean_dec(v_x_1075_);
v_res_1080_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9(v_00_u03b2_1072_, v_x_1073_, v_x_8880__boxed_1078_, v_x_8881__boxed_1079_, v_x_1076_, v_x_1077_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13(lean_object* v_00_u03b2_1081_, lean_object* v_n_1082_, lean_object* v_k_1083_, lean_object* v_v_1084_){
_start:
{
lean_object* v___x_1085_; 
v___x_1085_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13___redArg(v_n_1082_, v_k_1083_, v_v_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14(lean_object* v_00_u03b2_1086_, size_t v_depth_1087_, lean_object* v_keys_1088_, lean_object* v_vals_1089_, lean_object* v_heq_1090_, lean_object* v_i_1091_, lean_object* v_entries_1092_){
_start:
{
lean_object* v___x_1093_; 
v___x_1093_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg(v_depth_1087_, v_keys_1088_, v_vals_1089_, v_i_1091_, v_entries_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___boxed(lean_object* v_00_u03b2_1094_, lean_object* v_depth_1095_, lean_object* v_keys_1096_, lean_object* v_vals_1097_, lean_object* v_heq_1098_, lean_object* v_i_1099_, lean_object* v_entries_1100_){
_start:
{
size_t v_depth_boxed_1101_; lean_object* v_res_1102_; 
v_depth_boxed_1101_ = lean_unbox_usize(v_depth_1095_);
lean_dec(v_depth_1095_);
v_res_1102_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14(v_00_u03b2_1094_, v_depth_boxed_1101_, v_keys_1096_, v_vals_1097_, v_heq_1098_, v_i_1099_, v_entries_1100_);
lean_dec_ref(v_vals_1097_);
lean_dec_ref(v_keys_1096_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13_spec__14(lean_object* v_00_u03b2_1103_, lean_object* v_x_1104_, lean_object* v_x_1105_, lean_object* v_x_1106_, lean_object* v_x_1107_){
_start:
{
lean_object* v___x_1108_; 
v___x_1108_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13_spec__14___redArg(v_x_1104_, v_x_1105_, v_x_1106_, v_x_1107_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClear(lean_object* v_mvarId_1109_, lean_object* v_fvarId_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = l_Lean_Meta_saveState___redArg(v_a_1112_, v_a_1114_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v_a_1117_; lean_object* v___x_1118_; 
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_a_1117_);
lean_dec_ref_known(v___x_1116_, 1);
lean_inc(v_mvarId_1109_);
v___x_1118_ = l_Lean_MVarId_clear(v_mvarId_1109_, v_fvarId_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_dec(v_a_1117_);
lean_dec(v_mvarId_1109_);
return v___x_1118_;
}
else
{
lean_object* v_a_1119_; uint8_t v___x_1120_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
v___x_1120_ = l_Lean_Exception_isInterrupt(v_a_1119_);
if (v___x_1120_ == 0)
{
uint8_t v___x_1121_; 
lean_inc(v_a_1119_);
v___x_1121_ = l_Lean_Exception_isRuntime(v_a_1119_);
if (v___x_1121_ == 0)
{
lean_object* v___x_1122_; 
lean_dec_ref_known(v___x_1118_, 1);
v___x_1122_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1117_, v_a_1112_, v_a_1114_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1129_ == 0)
{
lean_object* v_unused_1130_; 
v_unused_1130_ = lean_ctor_get(v___x_1122_, 0);
lean_dec(v_unused_1130_);
v___x_1124_ = v___x_1122_;
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
else
{
lean_dec(v___x_1122_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 0, v_mvarId_1109_);
v___x_1127_ = v___x_1124_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_mvarId_1109_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
else
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1138_; 
lean_dec(v_mvarId_1109_);
v_a_1131_ = lean_ctor_get(v___x_1122_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1133_ = v___x_1122_;
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1122_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; 
if (v_isShared_1134_ == 0)
{
v___x_1136_ = v___x_1133_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_a_1131_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
else
{
lean_dec(v_a_1117_);
lean_dec(v_mvarId_1109_);
return v___x_1118_;
}
}
else
{
lean_dec(v_a_1117_);
lean_dec(v_mvarId_1109_);
return v___x_1118_;
}
}
}
else
{
lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1146_; 
lean_dec(v_fvarId_1110_);
lean_dec(v_mvarId_1109_);
v_a_1139_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1141_ = v___x_1116_;
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v___x_1116_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1144_; 
if (v_isShared_1142_ == 0)
{
v___x_1144_ = v___x_1141_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_a_1139_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClear___boxed(lean_object* v_mvarId_1147_, lean_object* v_fvarId_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_){
_start:
{
lean_object* v_res_1154_; 
v_res_1154_ = l_Lean_MVarId_tryClear(v_mvarId_1147_, v_fvarId_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_);
lean_dec(v_a_1152_);
lean_dec_ref(v_a_1151_);
lean_dec(v_a_1150_);
lean_dec_ref(v_a_1149_);
return v_res_1154_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0(lean_object* v_as_1155_, size_t v_i_1156_, size_t v_stop_1157_, lean_object* v_b_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
uint8_t v___x_1164_; 
v___x_1164_ = lean_usize_dec_eq(v_i_1156_, v_stop_1157_);
if (v___x_1164_ == 0)
{
size_t v___x_1165_; size_t v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1165_ = ((size_t)1ULL);
v___x_1166_ = lean_usize_sub(v_i_1156_, v___x_1165_);
v___x_1167_ = lean_array_uget_borrowed(v_as_1155_, v___x_1166_);
lean_inc(v___x_1167_);
v___x_1168_ = l_Lean_MVarId_tryClear(v_b_1158_, v___x_1167_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_object* v_a_1169_; 
v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
lean_inc(v_a_1169_);
lean_dec_ref_known(v___x_1168_, 1);
v_i_1156_ = v___x_1166_;
v_b_1158_ = v_a_1169_;
goto _start;
}
else
{
return v___x_1168_;
}
}
else
{
lean_object* v___x_1171_; 
v___x_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1171_, 0, v_b_1158_);
return v___x_1171_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0___boxed(lean_object* v_as_1172_, lean_object* v_i_1173_, lean_object* v_stop_1174_, lean_object* v_b_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
size_t v_i_boxed_1181_; size_t v_stop_boxed_1182_; lean_object* v_res_1183_; 
v_i_boxed_1181_ = lean_unbox_usize(v_i_1173_);
lean_dec(v_i_1173_);
v_stop_boxed_1182_ = lean_unbox_usize(v_stop_1174_);
lean_dec(v_stop_1174_);
v_res_1183_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0(v_as_1172_, v_i_boxed_1181_, v_stop_boxed_1182_, v_b_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec_ref(v_as_1172_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany(lean_object* v_mvarId_1184_, lean_object* v_fvarIds_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_){
_start:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; uint8_t v___x_1193_; 
v___x_1191_ = lean_array_get_size(v_fvarIds_1185_);
v___x_1192_ = lean_unsigned_to_nat(0u);
v___x_1193_ = lean_nat_dec_lt(v___x_1192_, v___x_1191_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1194_; 
v___x_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1194_, 0, v_mvarId_1184_);
return v___x_1194_;
}
else
{
size_t v___x_1195_; size_t v___x_1196_; lean_object* v___x_1197_; 
v___x_1195_ = lean_usize_of_nat(v___x_1191_);
v___x_1196_ = ((size_t)0ULL);
v___x_1197_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0(v_fvarIds_1185_, v___x_1195_, v___x_1196_, v_mvarId_1184_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_);
return v___x_1197_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany___boxed(lean_object* v_mvarId_1198_, lean_object* v_fvarIds_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l_Lean_MVarId_tryClearMany(v_mvarId_1198_, v_fvarIds_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_);
lean_dec(v_a_1203_);
lean_dec_ref(v_a_1202_);
lean_dec(v_a_1201_);
lean_dec_ref(v_a_1200_);
lean_dec_ref(v_fvarIds_1199_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0(lean_object* v_as_1206_, size_t v_i_1207_, size_t v_stop_1208_, lean_object* v_b_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
uint8_t v___x_1215_; 
v___x_1215_ = lean_usize_dec_eq(v_i_1207_, v_stop_1208_);
if (v___x_1215_ == 0)
{
lean_object* v_fst_1216_; lean_object* v_snd_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1242_; 
v_fst_1216_ = lean_ctor_get(v_b_1209_, 0);
v_snd_1217_ = lean_ctor_get(v_b_1209_, 1);
v_isSharedCheck_1242_ = !lean_is_exclusive(v_b_1209_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1219_ = v_b_1209_;
v_isShared_1220_ = v_isSharedCheck_1242_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_snd_1217_);
lean_inc(v_fst_1216_);
lean_dec(v_b_1209_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1242_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
size_t v___x_1221_; size_t v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1221_ = ((size_t)1ULL);
v___x_1222_ = lean_usize_sub(v_i_1207_, v___x_1221_);
v___x_1223_ = lean_array_uget_borrowed(v_as_1206_, v___x_1222_);
lean_inc(v___x_1223_);
lean_inc(v_fst_1216_);
v___x_1224_ = l_Lean_MVarId_tryClear(v_fst_1216_, v___x_1223_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v_a_1225_; lean_object* v___y_1227_; uint8_t v___x_1232_; 
v_a_1225_ = lean_ctor_get(v___x_1224_, 0);
lean_inc(v_a_1225_);
lean_dec_ref_known(v___x_1224_, 1);
v___x_1232_ = l_Lean_instBEqMVarId_beq(v_fst_1216_, v_a_1225_);
lean_dec(v_fst_1216_);
if (v___x_1232_ == 0)
{
lean_object* v___x_1233_; 
lean_inc(v___x_1223_);
v___x_1233_ = lean_array_push(v_snd_1217_, v___x_1223_);
v___y_1227_ = v___x_1233_;
goto v___jp_1226_;
}
else
{
v___y_1227_ = v_snd_1217_;
goto v___jp_1226_;
}
v___jp_1226_:
{
lean_object* v___x_1229_; 
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 1, v___y_1227_);
lean_ctor_set(v___x_1219_, 0, v_a_1225_);
v___x_1229_ = v___x_1219_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_a_1225_);
lean_ctor_set(v_reuseFailAlloc_1231_, 1, v___y_1227_);
v___x_1229_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
v_i_1207_ = v___x_1222_;
v_b_1209_ = v___x_1229_;
goto _start;
}
}
}
else
{
lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1241_; 
lean_del_object(v___x_1219_);
lean_dec(v_snd_1217_);
lean_dec(v_fst_1216_);
v_a_1234_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1236_ = v___x_1224_;
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_a_1234_);
lean_dec(v___x_1224_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1239_; 
if (v_isShared_1237_ == 0)
{
v___x_1239_ = v___x_1236_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_a_1234_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
}
}
else
{
lean_object* v___x_1243_; 
v___x_1243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1243_, 0, v_b_1209_);
return v___x_1243_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0___boxed(lean_object* v_as_1244_, lean_object* v_i_1245_, lean_object* v_stop_1246_, lean_object* v_b_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
size_t v_i_boxed_1253_; size_t v_stop_boxed_1254_; lean_object* v_res_1255_; 
v_i_boxed_1253_ = lean_unbox_usize(v_i_1245_);
lean_dec(v_i_1245_);
v_stop_boxed_1254_ = lean_unbox_usize(v_stop_1246_);
lean_dec(v_stop_1246_);
v_res_1255_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0(v_as_1244_, v_i_boxed_1253_, v_stop_boxed_1254_, v_b_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec_ref(v_as_1244_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany_x27___lam__0(lean_object* v_fvarIds_1256_, lean_object* v_goal_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
lean_object* v_lctx_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; uint8_t v___x_1269_; 
v_lctx_1263_ = lean_ctor_get(v___y_1258_, 2);
v___x_1264_ = l_Lean_LocalContext_sortFVarsByContextOrder(v_lctx_1263_, v_fvarIds_1256_);
v___x_1265_ = lean_array_get_size(v___x_1264_);
v___x_1266_ = lean_mk_empty_array_with_capacity(v___x_1265_);
v___x_1267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1267_, 0, v_goal_1257_);
lean_ctor_set(v___x_1267_, 1, v___x_1266_);
v___x_1268_ = lean_unsigned_to_nat(0u);
v___x_1269_ = lean_nat_dec_lt(v___x_1268_, v___x_1265_);
if (v___x_1269_ == 0)
{
lean_object* v___x_1270_; 
lean_dec_ref(v___x_1264_);
v___x_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1267_);
return v___x_1270_;
}
else
{
size_t v___x_1271_; size_t v___x_1272_; lean_object* v___x_1273_; 
v___x_1271_ = lean_usize_of_nat(v___x_1265_);
v___x_1272_ = ((size_t)0ULL);
v___x_1273_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0(v___x_1264_, v___x_1271_, v___x_1272_, v___x_1267_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_);
lean_dec_ref(v___x_1264_);
return v___x_1273_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany_x27___lam__0___boxed(lean_object* v_fvarIds_1274_, lean_object* v_goal_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Lean_MVarId_tryClearMany_x27___lam__0(v_fvarIds_1274_, v_goal_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany_x27(lean_object* v_goal_1282_, lean_object* v_fvarIds_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_){
_start:
{
lean_object* v___f_1289_; lean_object* v___x_1290_; 
lean_inc(v_goal_1282_);
v___f_1289_ = lean_alloc_closure((void*)(l_Lean_MVarId_tryClearMany_x27___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1289_, 0, v_fvarIds_1283_);
lean_closure_set(v___f_1289_, 1, v_goal_1282_);
v___x_1290_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg(v_goal_1282_, v___f_1289_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany_x27___boxed(lean_object* v_goal_1291_, lean_object* v_fvarIds_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l_Lean_MVarId_tryClearMany_x27(v_goal_1291_, v_fvarIds_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_);
lean_dec(v_a_1296_);
lean_dec_ref(v_a_1295_);
lean_dec(v_a_1294_);
lean_dec_ref(v_a_1293_);
return v_res_1298_;
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
