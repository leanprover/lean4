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
size_t v_x_7712__boxed_419_; size_t v_x_7713__boxed_420_; lean_object* v_res_421_; 
v_x_7712__boxed_419_ = lean_unbox_usize(v_x_415_);
lean_dec(v_x_415_);
v_x_7713__boxed_420_ = lean_unbox_usize(v_x_416_);
lean_dec(v_x_416_);
v_res_421_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_x_414_, v_x_7712__boxed_419_, v_x_7713__boxed_420_, v_x_417_, v_x_418_);
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
lean_object* v___x_433_; lean_object* v_mctx_434_; lean_object* v_cache_435_; lean_object* v_zetaDeltaFVarIds_436_; lean_object* v_postponed_437_; lean_object* v_diag_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_466_; 
v___x_433_ = lean_st_ref_take(v___y_431_);
v_mctx_434_ = lean_ctor_get(v___x_433_, 0);
v_cache_435_ = lean_ctor_get(v___x_433_, 1);
v_zetaDeltaFVarIds_436_ = lean_ctor_get(v___x_433_, 2);
v_postponed_437_ = lean_ctor_get(v___x_433_, 3);
v_diag_438_ = lean_ctor_get(v___x_433_, 4);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_466_ == 0)
{
v___x_440_ = v___x_433_;
v_isShared_441_ = v_isSharedCheck_466_;
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
v_isShared_441_ = v_isSharedCheck_466_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v_depth_442_; lean_object* v_levelAssignDepth_443_; lean_object* v_lmvarCounter_444_; lean_object* v_mvarCounter_445_; lean_object* v_lDecls_446_; lean_object* v_decls_447_; lean_object* v_userNames_448_; lean_object* v_lAssignment_449_; lean_object* v_eAssignment_450_; lean_object* v_dAssignment_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_465_; 
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
v_isSharedCheck_465_ = !lean_is_exclusive(v_mctx_434_);
if (v_isSharedCheck_465_ == 0)
{
v___x_453_ = v_mctx_434_;
v_isShared_454_ = v_isSharedCheck_465_;
goto v_resetjp_452_;
}
else
{
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
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_465_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_458_; 
v___x_455_ = lean_box(0);
v___x_456_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3___redArg(v_eAssignment_450_, v_mvarId_429_, v_val_430_);
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 8, v___x_456_);
v___x_458_ = v___x_453_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_depth_442_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v_levelAssignDepth_443_);
lean_ctor_set(v_reuseFailAlloc_464_, 2, v_lmvarCounter_444_);
lean_ctor_set(v_reuseFailAlloc_464_, 3, v_mvarCounter_445_);
lean_ctor_set(v_reuseFailAlloc_464_, 4, v_lDecls_446_);
lean_ctor_set(v_reuseFailAlloc_464_, 5, v_decls_447_);
lean_ctor_set(v_reuseFailAlloc_464_, 6, v_userNames_448_);
lean_ctor_set(v_reuseFailAlloc_464_, 7, v_lAssignment_449_);
lean_ctor_set(v_reuseFailAlloc_464_, 8, v___x_456_);
lean_ctor_set(v_reuseFailAlloc_464_, 9, v_dAssignment_451_);
v___x_458_ = v_reuseFailAlloc_464_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
lean_object* v___x_460_; 
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 0, v___x_458_);
v___x_460_ = v___x_440_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_458_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v_cache_435_);
lean_ctor_set(v_reuseFailAlloc_463_, 2, v_zetaDeltaFVarIds_436_);
lean_ctor_set(v_reuseFailAlloc_463_, 3, v_postponed_437_);
lean_ctor_set(v_reuseFailAlloc_463_, 4, v_diag_438_);
v___x_460_ = v_reuseFailAlloc_463_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = lean_st_ref_put(v___y_431_, v___x_460_);
v___x_462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_462_, 0, v___x_455_);
return v___x_462_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg___boxed(lean_object* v_mvarId_467_, lean_object* v_val_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg(v_mvarId_467_, v_val_468_, v___y_469_);
lean_dec(v___y_469_);
return v_res_471_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3(void){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__2));
v___x_477_ = l_Lean_stringToMessageData(v___x_476_);
return v___x_477_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5(void){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__4));
v___x_480_ = l_Lean_stringToMessageData(v___x_479_);
return v___x_480_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__6));
v___x_483_ = l_Lean_stringToMessageData(v___x_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9(lean_object* v_fvarId_484_, lean_object* v_mvarId_485_, lean_object* v_as_486_, size_t v_i_487_, size_t v_stop_488_, lean_object* v_b_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
lean_object* v_a_496_; uint8_t v___x_500_; 
v___x_500_ = lean_usize_dec_eq(v_i_487_, v_stop_488_);
if (v___x_500_ == 0)
{
lean_object* v___x_501_; 
v___x_501_ = lean_array_uget(v_as_486_, v_i_487_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v___x_502_; 
v___x_502_ = lean_box(0);
v_a_496_ = v___x_502_;
goto v___jp_495_;
}
else
{
lean_object* v_val_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_540_; 
v_val_503_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_540_ == 0)
{
v___x_505_ = v___x_501_;
v_isShared_506_ = v_isSharedCheck_540_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_val_503_);
lean_dec(v___x_501_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_540_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_507_; uint8_t v___x_508_; 
v___x_507_ = l_Lean_LocalDecl_fvarId(v_val_503_);
v___x_508_ = l_Lean_instBEqFVarId_beq(v___x_507_, v_fvarId_484_);
lean_dec(v___x_507_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; uint8_t v___x_510_; lean_object* v___x_511_; 
v___x_509_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__1));
v___x_510_ = 1;
lean_inc(v_fvarId_484_);
lean_inc(v_val_503_);
v___x_511_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg(v_val_503_, v_fvarId_484_, v___x_510_, v___y_491_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_512_; uint8_t v___x_513_; 
v_a_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_a_512_);
lean_dec_ref_known(v___x_511_, 1);
v___x_513_ = lean_unbox(v_a_512_);
lean_dec(v_a_512_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; 
lean_del_object(v___x_505_);
lean_dec(v_val_503_);
v___x_514_ = lean_box(0);
v_a_496_ = v___x_514_;
goto v___jp_495_;
}
else
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_527_; 
v___x_515_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3);
v___x_516_ = l_Lean_LocalDecl_toExpr(v_val_503_);
v___x_517_ = l_Lean_MessageData_ofExpr(v___x_516_);
v___x_518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_518_, 0, v___x_515_);
lean_ctor_set(v___x_518_, 1, v___x_517_);
v___x_519_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5);
v___x_520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_518_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
lean_inc(v_fvarId_484_);
v___x_521_ = l_Lean_mkFVar(v_fvarId_484_);
v___x_522_ = l_Lean_MessageData_ofExpr(v___x_521_);
v___x_523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_520_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
v___x_524_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7);
v___x_525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_523_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 0, v___x_525_);
v___x_527_ = v___x_505_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_525_);
v___x_527_ = v_reuseFailAlloc_530_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
lean_object* v___x_528_; 
lean_inc(v_mvarId_485_);
v___x_528_ = l_Lean_Meta_throwTacticEx___redArg(v___x_509_, v_mvarId_485_, v___x_527_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
if (lean_obj_tag(v___x_528_) == 0)
{
lean_object* v_a_529_; 
v_a_529_ = lean_ctor_get(v___x_528_, 0);
lean_inc(v_a_529_);
lean_dec_ref_known(v___x_528_, 1);
v_a_496_ = v_a_529_;
goto v___jp_495_;
}
else
{
lean_dec(v_mvarId_485_);
lean_dec(v_fvarId_484_);
return v___x_528_;
}
}
}
}
else
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
lean_del_object(v___x_505_);
lean_dec(v_val_503_);
lean_dec(v_mvarId_485_);
lean_dec(v_fvarId_484_);
v_a_531_ = lean_ctor_get(v___x_511_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_538_ == 0)
{
v___x_533_ = v___x_511_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_511_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_536_; 
if (v_isShared_534_ == 0)
{
v___x_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_531_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
else
{
lean_object* v___x_539_; 
lean_del_object(v___x_505_);
lean_dec(v_val_503_);
v___x_539_ = lean_box(0);
v_a_496_ = v___x_539_;
goto v___jp_495_;
}
}
}
}
else
{
lean_object* v___x_541_; 
lean_dec(v_mvarId_485_);
lean_dec(v_fvarId_484_);
v___x_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_541_, 0, v_b_489_);
return v___x_541_;
}
v___jp_495_:
{
size_t v___x_497_; size_t v___x_498_; 
v___x_497_ = ((size_t)1ULL);
v___x_498_ = lean_usize_add(v_i_487_, v___x_497_);
v_i_487_ = v___x_498_;
v_b_489_ = v_a_496_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___boxed(lean_object* v_fvarId_542_, lean_object* v_mvarId_543_, lean_object* v_as_544_, lean_object* v_i_545_, lean_object* v_stop_546_, lean_object* v_b_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
size_t v_i_boxed_553_; size_t v_stop_boxed_554_; lean_object* v_res_555_; 
v_i_boxed_553_ = lean_unbox_usize(v_i_545_);
lean_dec(v_i_545_);
v_stop_boxed_554_ = lean_unbox_usize(v_stop_546_);
lean_dec(v_stop_546_);
v_res_555_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9(v_fvarId_542_, v_mvarId_543_, v_as_544_, v_i_boxed_553_, v_stop_boxed_554_, v_b_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_);
lean_dec(v___y_551_);
lean_dec_ref(v___y_550_);
lean_dec(v___y_549_);
lean_dec_ref(v___y_548_);
lean_dec_ref(v_as_544_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(lean_object* v_fvarId_556_, lean_object* v_mvarId_557_, lean_object* v_as_558_, size_t v_i_559_, size_t v_stop_560_, lean_object* v_b_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
lean_object* v_a_568_; uint8_t v___x_572_; 
v___x_572_ = lean_usize_dec_eq(v_i_559_, v_stop_560_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; 
v___x_573_ = lean_array_uget(v_as_558_, v_i_559_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v___x_574_; 
v___x_574_ = lean_box(0);
v_a_568_ = v___x_574_;
goto v___jp_567_;
}
else
{
lean_object* v_val_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_612_; 
v_val_575_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_612_ == 0)
{
v___x_577_ = v___x_573_;
v_isShared_578_ = v_isSharedCheck_612_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_val_575_);
lean_dec(v___x_573_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_612_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_579_; uint8_t v___x_580_; 
v___x_579_ = l_Lean_LocalDecl_fvarId(v_val_575_);
v___x_580_ = l_Lean_instBEqFVarId_beq(v___x_579_, v_fvarId_556_);
lean_dec(v___x_579_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; uint8_t v___x_582_; lean_object* v___x_583_; 
v___x_581_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__1));
v___x_582_ = 1;
lean_inc(v_fvarId_556_);
lean_inc(v_val_575_);
v___x_583_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg(v_val_575_, v_fvarId_556_, v___x_582_, v___y_563_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v_a_584_; uint8_t v___x_585_; 
v_a_584_ = lean_ctor_get(v___x_583_, 0);
lean_inc(v_a_584_);
lean_dec_ref_known(v___x_583_, 1);
v___x_585_ = lean_unbox(v_a_584_);
lean_dec(v_a_584_);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; 
lean_del_object(v___x_577_);
lean_dec(v_val_575_);
v___x_586_ = lean_box(0);
v_a_568_ = v___x_586_;
goto v___jp_567_;
}
else
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_599_; 
v___x_587_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3);
v___x_588_ = l_Lean_LocalDecl_toExpr(v_val_575_);
v___x_589_ = l_Lean_MessageData_ofExpr(v___x_588_);
v___x_590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_587_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
v___x_591_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5);
v___x_592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_590_);
lean_ctor_set(v___x_592_, 1, v___x_591_);
lean_inc(v_fvarId_556_);
v___x_593_ = l_Lean_mkFVar(v_fvarId_556_);
v___x_594_ = l_Lean_MessageData_ofExpr(v___x_593_);
v___x_595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_592_);
lean_ctor_set(v___x_595_, 1, v___x_594_);
v___x_596_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7);
v___x_597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_597_, 0, v___x_595_);
lean_ctor_set(v___x_597_, 1, v___x_596_);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 0, v___x_597_);
v___x_599_ = v___x_577_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v___x_597_);
v___x_599_ = v_reuseFailAlloc_602_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
lean_object* v___x_600_; 
lean_inc(v_mvarId_557_);
v___x_600_ = l_Lean_Meta_throwTacticEx___redArg(v___x_581_, v_mvarId_557_, v___x_599_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v_a_601_; 
v_a_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_a_601_);
lean_dec_ref_known(v___x_600_, 1);
v_a_568_ = v_a_601_;
goto v___jp_567_;
}
else
{
lean_dec(v_mvarId_557_);
lean_dec(v_fvarId_556_);
return v___x_600_;
}
}
}
}
else
{
lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_610_; 
lean_del_object(v___x_577_);
lean_dec(v_val_575_);
lean_dec(v_mvarId_557_);
lean_dec(v_fvarId_556_);
v_a_603_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_610_ == 0)
{
v___x_605_ = v___x_583_;
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_583_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_608_; 
if (v_isShared_606_ == 0)
{
v___x_608_ = v___x_605_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_a_603_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
else
{
lean_object* v___x_611_; 
lean_del_object(v___x_577_);
lean_dec(v_val_575_);
v___x_611_ = lean_box(0);
v_a_568_ = v___x_611_;
goto v___jp_567_;
}
}
}
}
else
{
lean_object* v___x_613_; 
lean_dec(v_mvarId_557_);
lean_dec(v_fvarId_556_);
v___x_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_613_, 0, v_b_561_);
return v___x_613_;
}
v___jp_567_:
{
size_t v___x_569_; size_t v___x_570_; lean_object* v___x_571_; 
v___x_569_ = ((size_t)1ULL);
v___x_570_ = lean_usize_add(v_i_559_, v___x_569_);
v___x_571_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9(v_fvarId_556_, v_mvarId_557_, v_as_558_, v___x_570_, v_stop_560_, v_a_568_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
return v___x_571_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5___boxed(lean_object* v_fvarId_614_, lean_object* v_mvarId_615_, lean_object* v_as_616_, lean_object* v_i_617_, lean_object* v_stop_618_, lean_object* v_b_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_){
_start:
{
size_t v_i_boxed_625_; size_t v_stop_boxed_626_; lean_object* v_res_627_; 
v_i_boxed_625_ = lean_unbox_usize(v_i_617_);
lean_dec(v_i_617_);
v_stop_boxed_626_ = lean_unbox_usize(v_stop_618_);
lean_dec(v_stop_618_);
v_res_627_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_614_, v_mvarId_615_, v_as_616_, v_i_boxed_625_, v_stop_boxed_626_, v_b_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec_ref(v_as_616_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6(lean_object* v_fvarId_628_, lean_object* v_mvarId_629_, lean_object* v_x_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_){
_start:
{
if (lean_obj_tag(v_x_630_) == 0)
{
lean_object* v_cs_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_650_; 
v_cs_636_ = lean_ctor_get(v_x_630_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v_x_630_);
if (v_isSharedCheck_650_ == 0)
{
v___x_638_ = v_x_630_;
v_isShared_639_ = v_isSharedCheck_650_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_cs_636_);
lean_dec(v_x_630_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_650_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; uint8_t v___x_643_; 
v___x_640_ = lean_unsigned_to_nat(0u);
v___x_641_ = lean_array_get_size(v_cs_636_);
v___x_642_ = lean_box(0);
v___x_643_ = lean_nat_dec_lt(v___x_640_, v___x_641_);
if (v___x_643_ == 0)
{
lean_object* v___x_645_; 
lean_dec_ref(v_cs_636_);
lean_dec(v_mvarId_629_);
lean_dec(v_fvarId_628_);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 0, v___x_642_);
v___x_645_ = v___x_638_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_642_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
else
{
size_t v___x_647_; size_t v___x_648_; lean_object* v___x_649_; 
lean_del_object(v___x_638_);
v___x_647_ = ((size_t)0ULL);
v___x_648_ = lean_usize_of_nat(v___x_641_);
v___x_649_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(v_fvarId_628_, v_mvarId_629_, v_cs_636_, v___x_647_, v___x_648_, v___x_642_, v___y_631_, v___y_632_, v___y_633_, v___y_634_);
lean_dec_ref(v_cs_636_);
return v___x_649_;
}
}
}
else
{
lean_object* v_vs_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_665_; 
v_vs_651_ = lean_ctor_get(v_x_630_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v_x_630_);
if (v_isSharedCheck_665_ == 0)
{
v___x_653_ = v_x_630_;
v_isShared_654_ = v_isSharedCheck_665_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_vs_651_);
lean_dec(v_x_630_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_665_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; uint8_t v___x_658_; 
v___x_655_ = lean_unsigned_to_nat(0u);
v___x_656_ = lean_array_get_size(v_vs_651_);
v___x_657_ = lean_box(0);
v___x_658_ = lean_nat_dec_lt(v___x_655_, v___x_656_);
if (v___x_658_ == 0)
{
lean_object* v___x_660_; 
lean_dec_ref(v_vs_651_);
lean_dec(v_mvarId_629_);
lean_dec(v_fvarId_628_);
if (v_isShared_654_ == 0)
{
lean_ctor_set_tag(v___x_653_, 0);
lean_ctor_set(v___x_653_, 0, v___x_657_);
v___x_660_ = v___x_653_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v___x_657_);
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
lean_del_object(v___x_653_);
v___x_662_ = ((size_t)0ULL);
v___x_663_ = lean_usize_of_nat(v___x_656_);
v___x_664_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_628_, v_mvarId_629_, v_vs_651_, v___x_662_, v___x_663_, v___x_657_, v___y_631_, v___y_632_, v___y_633_, v___y_634_);
lean_dec_ref(v_vs_651_);
return v___x_664_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(lean_object* v_fvarId_666_, lean_object* v_mvarId_667_, lean_object* v_as_668_, size_t v_i_669_, size_t v_stop_670_, lean_object* v_b_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
uint8_t v___x_677_; 
v___x_677_ = lean_usize_dec_eq(v_i_669_, v_stop_670_);
if (v___x_677_ == 0)
{
lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_678_ = lean_array_uget_borrowed(v_as_668_, v_i_669_);
lean_inc(v___x_678_);
lean_inc(v_mvarId_667_);
lean_inc(v_fvarId_666_);
v___x_679_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6(v_fvarId_666_, v_mvarId_667_, v___x_678_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_object* v_a_680_; size_t v___x_681_; size_t v___x_682_; 
v_a_680_ = lean_ctor_get(v___x_679_, 0);
lean_inc(v_a_680_);
lean_dec_ref_known(v___x_679_, 1);
v___x_681_ = ((size_t)1ULL);
v___x_682_ = lean_usize_add(v_i_669_, v___x_681_);
v_i_669_ = v___x_682_;
v_b_671_ = v_a_680_;
goto _start;
}
else
{
lean_dec(v_mvarId_667_);
lean_dec(v_fvarId_666_);
return v___x_679_;
}
}
else
{
lean_object* v___x_684_; 
lean_dec(v_mvarId_667_);
lean_dec(v_fvarId_666_);
v___x_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_684_, 0, v_b_671_);
return v___x_684_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7___boxed(lean_object* v_fvarId_685_, lean_object* v_mvarId_686_, lean_object* v_as_687_, lean_object* v_i_688_, lean_object* v_stop_689_, lean_object* v_b_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_){
_start:
{
size_t v_i_boxed_696_; size_t v_stop_boxed_697_; lean_object* v_res_698_; 
v_i_boxed_696_ = lean_unbox_usize(v_i_688_);
lean_dec(v_i_688_);
v_stop_boxed_697_ = lean_unbox_usize(v_stop_689_);
lean_dec(v_stop_689_);
v_res_698_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(v_fvarId_685_, v_mvarId_686_, v_as_687_, v_i_boxed_696_, v_stop_boxed_697_, v_b_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec_ref(v_as_687_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6___boxed(lean_object* v_fvarId_699_, lean_object* v_mvarId_700_, lean_object* v_x_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6(v_fvarId_699_, v_mvarId_700_, v_x_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6(lean_object* v_fvarId_708_, lean_object* v_mvarId_709_, lean_object* v_t_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
lean_object* v_root_716_; lean_object* v_tail_717_; lean_object* v___x_718_; 
v_root_716_ = lean_ctor_get(v_t_710_, 0);
lean_inc_ref(v_root_716_);
v_tail_717_ = lean_ctor_get(v_t_710_, 1);
lean_inc_ref(v_tail_717_);
lean_dec_ref(v_t_710_);
lean_inc(v_mvarId_709_);
lean_inc(v_fvarId_708_);
v___x_718_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6(v_fvarId_708_, v_mvarId_709_, v_root_716_, v___y_711_, v___y_712_, v___y_713_, v___y_714_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_732_; 
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_732_ == 0)
{
lean_object* v_unused_733_; 
v_unused_733_ = lean_ctor_get(v___x_718_, 0);
lean_dec(v_unused_733_);
v___x_720_ = v___x_718_;
v_isShared_721_ = v_isSharedCheck_732_;
goto v_resetjp_719_;
}
else
{
lean_dec(v___x_718_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_732_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; uint8_t v___x_725_; 
v___x_722_ = lean_unsigned_to_nat(0u);
v___x_723_ = lean_array_get_size(v_tail_717_);
v___x_724_ = lean_box(0);
v___x_725_ = lean_nat_dec_lt(v___x_722_, v___x_723_);
if (v___x_725_ == 0)
{
lean_object* v___x_727_; 
lean_dec_ref(v_tail_717_);
lean_dec(v_mvarId_709_);
lean_dec(v_fvarId_708_);
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 0, v___x_724_);
v___x_727_ = v___x_720_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_724_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
else
{
size_t v___x_729_; size_t v___x_730_; lean_object* v___x_731_; 
lean_del_object(v___x_720_);
v___x_729_ = ((size_t)0ULL);
v___x_730_ = lean_usize_of_nat(v___x_723_);
v___x_731_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_708_, v_mvarId_709_, v_tail_717_, v___x_729_, v___x_730_, v___x_724_, v___y_711_, v___y_712_, v___y_713_, v___y_714_);
lean_dec_ref(v_tail_717_);
return v___x_731_;
}
}
}
else
{
lean_dec_ref(v_tail_717_);
lean_dec(v_mvarId_709_);
lean_dec(v_fvarId_708_);
return v___x_718_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6___boxed(lean_object* v_fvarId_734_, lean_object* v_mvarId_735_, lean_object* v_t_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6(v_fvarId_734_, v_mvarId_735_, v_t_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
return v_res_742_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4(lean_object* v_fvarId_744_, lean_object* v_mvarId_745_, lean_object* v_x_746_, size_t v_x_747_, size_t v_x_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
if (lean_obj_tag(v_x_746_) == 0)
{
lean_object* v_cs_754_; lean_object* v___x_755_; size_t v___x_756_; lean_object* v_j_757_; lean_object* v___x_758_; size_t v___x_759_; size_t v___x_760_; size_t v___x_761_; size_t v___x_762_; size_t v___x_763_; size_t v___x_764_; lean_object* v___x_765_; 
v_cs_754_ = lean_ctor_get(v_x_746_, 0);
lean_inc_ref(v_cs_754_);
lean_dec_ref_known(v_x_746_, 1);
v___x_755_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0);
v___x_756_ = lean_usize_shift_right(v_x_747_, v_x_748_);
v_j_757_ = lean_usize_to_nat(v___x_756_);
v___x_758_ = lean_array_get_borrowed(v___x_755_, v_cs_754_, v_j_757_);
v___x_759_ = ((size_t)1ULL);
v___x_760_ = lean_usize_shift_left(v___x_759_, v_x_748_);
v___x_761_ = lean_usize_sub(v___x_760_, v___x_759_);
v___x_762_ = lean_usize_land(v_x_747_, v___x_761_);
v___x_763_ = ((size_t)5ULL);
v___x_764_ = lean_usize_sub(v_x_748_, v___x_763_);
lean_inc(v___x_758_);
lean_inc(v_mvarId_745_);
lean_inc(v_fvarId_744_);
v___x_765_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4(v_fvarId_744_, v_mvarId_745_, v___x_758_, v___x_762_, v___x_764_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_780_; 
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_780_ == 0)
{
lean_object* v_unused_781_; 
v_unused_781_ = lean_ctor_get(v___x_765_, 0);
lean_dec(v_unused_781_);
v___x_767_ = v___x_765_;
v_isShared_768_ = v_isSharedCheck_780_;
goto v_resetjp_766_;
}
else
{
lean_dec(v___x_765_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_780_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; uint8_t v___x_773_; 
v___x_769_ = lean_unsigned_to_nat(1u);
v___x_770_ = lean_nat_add(v_j_757_, v___x_769_);
lean_dec(v_j_757_);
v___x_771_ = lean_array_get_size(v_cs_754_);
v___x_772_ = lean_box(0);
v___x_773_ = lean_nat_dec_lt(v___x_770_, v___x_771_);
if (v___x_773_ == 0)
{
lean_object* v___x_775_; 
lean_dec(v___x_770_);
lean_dec_ref(v_cs_754_);
lean_dec(v_mvarId_745_);
lean_dec(v_fvarId_744_);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 0, v___x_772_);
v___x_775_ = v___x_767_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_772_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
else
{
size_t v___x_777_; size_t v___x_778_; lean_object* v___x_779_; 
lean_del_object(v___x_767_);
v___x_777_ = lean_usize_of_nat(v___x_770_);
lean_dec(v___x_770_);
v___x_778_ = lean_usize_of_nat(v___x_771_);
v___x_779_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(v_fvarId_744_, v_mvarId_745_, v_cs_754_, v___x_777_, v___x_778_, v___x_772_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
lean_dec_ref(v_cs_754_);
return v___x_779_;
}
}
}
else
{
lean_dec(v_j_757_);
lean_dec_ref(v_cs_754_);
lean_dec(v_mvarId_745_);
lean_dec(v_fvarId_744_);
return v___x_765_;
}
}
else
{
lean_object* v_vs_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_796_; 
v_vs_782_ = lean_ctor_get(v_x_746_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v_x_746_);
if (v_isSharedCheck_796_ == 0)
{
v___x_784_ = v_x_746_;
v_isShared_785_ = v_isSharedCheck_796_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_vs_782_);
lean_dec(v_x_746_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_796_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; uint8_t v___x_789_; 
v___x_786_ = lean_usize_to_nat(v_x_747_);
v___x_787_ = lean_array_get_size(v_vs_782_);
v___x_788_ = lean_box(0);
v___x_789_ = lean_nat_dec_lt(v___x_786_, v___x_787_);
if (v___x_789_ == 0)
{
lean_object* v___x_791_; 
lean_dec(v___x_786_);
lean_dec_ref(v_vs_782_);
lean_dec(v_mvarId_745_);
lean_dec(v_fvarId_744_);
if (v_isShared_785_ == 0)
{
lean_ctor_set_tag(v___x_784_, 0);
lean_ctor_set(v___x_784_, 0, v___x_788_);
v___x_791_ = v___x_784_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_788_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
else
{
size_t v___x_793_; size_t v___x_794_; lean_object* v___x_795_; 
lean_del_object(v___x_784_);
v___x_793_ = lean_usize_of_nat(v___x_786_);
lean_dec(v___x_786_);
v___x_794_ = lean_usize_of_nat(v___x_787_);
v___x_795_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_744_, v_mvarId_745_, v_vs_782_, v___x_793_, v___x_794_, v___x_788_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
lean_dec_ref(v_vs_782_);
return v___x_795_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___boxed(lean_object* v_fvarId_797_, lean_object* v_mvarId_798_, lean_object* v_x_799_, lean_object* v_x_800_, lean_object* v_x_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
size_t v_x_8355__boxed_807_; size_t v_x_8356__boxed_808_; lean_object* v_res_809_; 
v_x_8355__boxed_807_ = lean_unbox_usize(v_x_800_);
lean_dec(v_x_800_);
v_x_8356__boxed_808_ = lean_unbox_usize(v_x_801_);
lean_dec(v_x_801_);
v_res_809_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4(v_fvarId_797_, v_mvarId_798_, v_x_799_, v_x_8355__boxed_807_, v_x_8356__boxed_808_, v___y_802_, v___y_803_, v___y_804_, v___y_805_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1(lean_object* v_fvarId_810_, lean_object* v_mvarId_811_, lean_object* v_t_812_, lean_object* v_start_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
lean_object* v___x_819_; uint8_t v___x_820_; 
v___x_819_ = lean_unsigned_to_nat(0u);
v___x_820_ = lean_nat_dec_eq(v_start_813_, v___x_819_);
if (v___x_820_ == 0)
{
lean_object* v_root_821_; lean_object* v_tail_822_; size_t v_shift_823_; lean_object* v_tailOff_824_; uint8_t v___x_825_; 
v_root_821_ = lean_ctor_get(v_t_812_, 0);
lean_inc_ref(v_root_821_);
v_tail_822_ = lean_ctor_get(v_t_812_, 1);
lean_inc_ref(v_tail_822_);
v_shift_823_ = lean_ctor_get_usize(v_t_812_, 4);
v_tailOff_824_ = lean_ctor_get(v_t_812_, 3);
lean_inc(v_tailOff_824_);
lean_dec_ref(v_t_812_);
v___x_825_ = lean_nat_dec_le(v_tailOff_824_, v_start_813_);
if (v___x_825_ == 0)
{
size_t v___x_826_; lean_object* v___x_827_; 
lean_dec(v_tailOff_824_);
v___x_826_ = lean_usize_of_nat(v_start_813_);
lean_inc(v_mvarId_811_);
lean_inc(v_fvarId_810_);
v___x_827_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4(v_fvarId_810_, v_mvarId_811_, v_root_821_, v___x_826_, v_shift_823_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_840_; 
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_840_ == 0)
{
lean_object* v_unused_841_; 
v_unused_841_ = lean_ctor_get(v___x_827_, 0);
lean_dec(v_unused_841_);
v___x_829_ = v___x_827_;
v_isShared_830_ = v_isSharedCheck_840_;
goto v_resetjp_828_;
}
else
{
lean_dec(v___x_827_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_840_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_831_; lean_object* v___x_832_; uint8_t v___x_833_; 
v___x_831_ = lean_array_get_size(v_tail_822_);
v___x_832_ = lean_box(0);
v___x_833_ = lean_nat_dec_lt(v___x_819_, v___x_831_);
if (v___x_833_ == 0)
{
lean_object* v___x_835_; 
lean_dec_ref(v_tail_822_);
lean_dec(v_mvarId_811_);
lean_dec(v_fvarId_810_);
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 0, v___x_832_);
v___x_835_ = v___x_829_;
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
size_t v___x_837_; size_t v___x_838_; lean_object* v___x_839_; 
lean_del_object(v___x_829_);
v___x_837_ = ((size_t)0ULL);
v___x_838_ = lean_usize_of_nat(v___x_831_);
v___x_839_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_810_, v_mvarId_811_, v_tail_822_, v___x_837_, v___x_838_, v___x_832_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
lean_dec_ref(v_tail_822_);
return v___x_839_;
}
}
}
else
{
lean_dec_ref(v_tail_822_);
lean_dec(v_mvarId_811_);
lean_dec(v_fvarId_810_);
return v___x_827_;
}
}
else
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; uint8_t v___x_845_; 
lean_dec_ref(v_root_821_);
v___x_842_ = lean_nat_sub(v_start_813_, v_tailOff_824_);
lean_dec(v_tailOff_824_);
v___x_843_ = lean_array_get_size(v_tail_822_);
v___x_844_ = lean_box(0);
v___x_845_ = lean_nat_dec_lt(v___x_842_, v___x_843_);
if (v___x_845_ == 0)
{
lean_object* v___x_846_; 
lean_dec(v___x_842_);
lean_dec_ref(v_tail_822_);
lean_dec(v_mvarId_811_);
lean_dec(v_fvarId_810_);
v___x_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_846_, 0, v___x_844_);
return v___x_846_;
}
else
{
size_t v___x_847_; size_t v___x_848_; lean_object* v___x_849_; 
v___x_847_ = lean_usize_of_nat(v___x_842_);
lean_dec(v___x_842_);
v___x_848_ = lean_usize_of_nat(v___x_843_);
v___x_849_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_810_, v_mvarId_811_, v_tail_822_, v___x_847_, v___x_848_, v___x_844_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
lean_dec_ref(v_tail_822_);
return v___x_849_;
}
}
}
else
{
lean_object* v___x_850_; 
v___x_850_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6(v_fvarId_810_, v_mvarId_811_, v_t_812_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
return v___x_850_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1___boxed(lean_object* v_fvarId_851_, lean_object* v_mvarId_852_, lean_object* v_t_853_, lean_object* v_start_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1(v_fvarId_851_, v_mvarId_852_, v_t_853_, v_start_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec(v_start_854_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1(lean_object* v_fvarId_861_, lean_object* v_mvarId_862_, lean_object* v_lctx_863_, lean_object* v_start_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
lean_object* v_decls_870_; lean_object* v___x_871_; 
v_decls_870_ = lean_ctor_get(v_lctx_863_, 1);
lean_inc_ref(v_decls_870_);
lean_dec_ref(v_lctx_863_);
v___x_871_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1(v_fvarId_861_, v_mvarId_862_, v_decls_870_, v_start_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1___boxed(lean_object* v_fvarId_872_, lean_object* v_mvarId_873_, lean_object* v_lctx_874_, lean_object* v_start_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1(v_fvarId_872_, v_mvarId_873_, v_lctx_874_, v_start_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec(v_start_875_);
return v_res_881_;
}
}
static lean_object* _init_l_Lean_MVarId_clear___lam__0___closed__1(void){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = ((lean_object*)(l_Lean_MVarId_clear___lam__0___closed__0));
v___x_884_ = l_Lean_stringToMessageData(v___x_883_);
return v___x_884_;
}
}
static lean_object* _init_l_Lean_MVarId_clear___lam__0___closed__3(void){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = ((lean_object*)(l_Lean_MVarId_clear___lam__0___closed__2));
v___x_887_ = l_Lean_stringToMessageData(v___x_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clear___lam__0(lean_object* v_mvarId_888_, lean_object* v___x_889_, lean_object* v_fvarId_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
lean_object* v___x_896_; 
lean_inc(v___x_889_);
lean_inc(v_mvarId_888_);
v___x_896_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_888_, v___x_889_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
if (lean_obj_tag(v___x_896_) == 0)
{
lean_object* v_lctx_897_; lean_object* v___y_899_; lean_object* v___y_900_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v___y_903_; lean_object* v___y_904_; lean_object* v___y_905_; lean_object* v___y_931_; lean_object* v___y_932_; lean_object* v___y_933_; lean_object* v___y_934_; uint8_t v___x_991_; 
lean_dec_ref_known(v___x_896_, 1);
v_lctx_897_ = lean_ctor_get(v___y_891_, 2);
lean_inc_ref(v_lctx_897_);
v___x_991_ = l_Lean_LocalContext_contains(v_lctx_897_, v_fvarId_890_);
if (v___x_991_ == 0)
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_992_ = lean_obj_once(&l_Lean_MVarId_clear___lam__0___closed__3, &l_Lean_MVarId_clear___lam__0___closed__3_once, _init_l_Lean_MVarId_clear___lam__0___closed__3);
lean_inc(v_fvarId_890_);
v___x_993_ = l_Lean_mkFVar(v_fvarId_890_);
v___x_994_ = l_Lean_MessageData_ofExpr(v___x_993_);
v___x_995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_992_);
lean_ctor_set(v___x_995_, 1, v___x_994_);
v___x_996_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7);
v___x_997_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_995_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
v___x_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
lean_inc(v_mvarId_888_);
lean_inc(v___x_889_);
v___x_999_ = l_Lean_Meta_throwTacticEx___redArg(v___x_889_, v_mvarId_888_, v___x_998_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_dec_ref_known(v___x_999_, 1);
v___y_931_ = v___y_891_;
v___y_932_ = v___y_892_;
v___y_933_ = v___y_893_;
v___y_934_ = v___y_894_;
goto v___jp_930_;
}
else
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
lean_dec_ref(v_lctx_897_);
lean_dec_ref(v___y_891_);
lean_dec(v_fvarId_890_);
lean_dec(v___x_889_);
lean_dec(v_mvarId_888_);
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
else
{
v___y_931_ = v___y_891_;
v___y_932_ = v___y_892_;
v___y_933_ = v___y_893_;
v___y_934_ = v___y_894_;
goto v___jp_930_;
}
v___jp_898_:
{
lean_object* v_localInstances_906_; lean_object* v___x_907_; lean_object* v___x_908_; uint8_t v___x_909_; lean_object* v___x_910_; 
v_localInstances_906_ = lean_ctor_get(v___y_902_, 3);
v___x_907_ = l_Lean_LocalContext_erase(v_lctx_897_, v_fvarId_890_);
lean_inc_ref(v_localInstances_906_);
v___x_908_ = l_Lean_LocalInstances_erase(v_localInstances_906_, v_fvarId_890_);
v___x_909_ = 2;
v___x_910_ = l_Lean_Meta_mkFreshExprMVarAt(v___x_907_, v___x_908_, v___y_900_, v___x_909_, v___y_899_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
lean_dec_ref(v___y_902_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v_a_911_; lean_object* v___x_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_920_; 
v_a_911_ = lean_ctor_get(v___x_910_, 0);
lean_inc_n(v_a_911_, 2);
lean_dec_ref_known(v___x_910_, 1);
v___x_912_ = l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg(v_mvarId_888_, v_a_911_, v___y_903_);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_920_ == 0)
{
lean_object* v_unused_921_; 
v_unused_921_ = lean_ctor_get(v___x_912_, 0);
lean_dec(v_unused_921_);
v___x_914_ = v___x_912_;
v_isShared_915_ = v_isSharedCheck_920_;
goto v_resetjp_913_;
}
else
{
lean_dec(v___x_912_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_920_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_916_; lean_object* v___x_918_; 
v___x_916_ = l_Lean_Expr_mvarId_x21(v_a_911_);
lean_dec(v_a_911_);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 0, v___x_916_);
v___x_918_ = v___x_914_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v___x_916_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
else
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
lean_dec(v_mvarId_888_);
v_a_922_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_929_ == 0)
{
v___x_924_ = v___x_910_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_910_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_a_922_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
v___jp_930_:
{
lean_object* v___x_935_; 
lean_inc(v_mvarId_888_);
v___x_935_ = l_Lean_MVarId_getTag(v_mvarId_888_, v___y_931_, v___y_932_, v___y_933_, v___y_934_);
if (lean_obj_tag(v___x_935_) == 0)
{
lean_object* v_a_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v_a_936_ = lean_ctor_get(v___x_935_, 0);
lean_inc(v_a_936_);
lean_dec_ref_known(v___x_935_, 1);
v___x_937_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_lctx_897_);
lean_inc(v_mvarId_888_);
lean_inc(v_fvarId_890_);
v___x_938_ = l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1(v_fvarId_890_, v_mvarId_888_, v_lctx_897_, v___x_937_, v___y_931_, v___y_932_, v___y_933_, v___y_934_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v___x_939_; 
lean_dec_ref_known(v___x_938_, 1);
lean_inc(v_mvarId_888_);
v___x_939_ = l_Lean_MVarId_getDecl(v_mvarId_888_, v___y_931_, v___y_932_, v___y_933_, v___y_934_);
if (lean_obj_tag(v___x_939_) == 0)
{
lean_object* v_a_940_; lean_object* v_type_941_; lean_object* v___x_942_; lean_object* v_a_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_966_; 
v_a_940_ = lean_ctor_get(v___x_939_, 0);
lean_inc(v_a_940_);
lean_dec_ref_known(v___x_939_, 1);
v_type_941_ = lean_ctor_get(v_a_940_, 2);
lean_inc_ref_n(v_type_941_, 2);
lean_dec(v_a_940_);
lean_inc(v_fvarId_890_);
v___x_942_ = l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3___redArg(v_type_941_, v_fvarId_890_, v___y_932_);
v_a_943_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_966_ == 0)
{
v___x_945_ = v___x_942_;
v_isShared_946_ = v_isSharedCheck_966_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_dec(v___x_942_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_966_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
uint8_t v___x_947_; 
v___x_947_ = lean_unbox(v_a_943_);
lean_dec(v_a_943_);
if (v___x_947_ == 0)
{
lean_del_object(v___x_945_);
lean_dec(v___x_889_);
v___y_899_ = v_a_936_;
v___y_900_ = v_type_941_;
v___y_901_ = v___x_937_;
v___y_902_ = v___y_931_;
v___y_903_ = v___y_932_;
v___y_904_ = v___y_933_;
v___y_905_ = v___y_934_;
goto v___jp_898_;
}
else
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_955_; 
v___x_948_ = lean_obj_once(&l_Lean_MVarId_clear___lam__0___closed__1, &l_Lean_MVarId_clear___lam__0___closed__1_once, _init_l_Lean_MVarId_clear___lam__0___closed__1);
lean_inc(v_fvarId_890_);
v___x_949_ = l_Lean_mkFVar(v_fvarId_890_);
v___x_950_ = l_Lean_MessageData_ofExpr(v___x_949_);
v___x_951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_951_, 0, v___x_948_);
lean_ctor_set(v___x_951_, 1, v___x_950_);
v___x_952_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7);
v___x_953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_953_, 0, v___x_951_);
lean_ctor_set(v___x_953_, 1, v___x_952_);
if (v_isShared_946_ == 0)
{
lean_ctor_set_tag(v___x_945_, 1);
lean_ctor_set(v___x_945_, 0, v___x_953_);
v___x_955_ = v___x_945_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_953_);
v___x_955_ = v_reuseFailAlloc_965_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
lean_object* v___x_956_; 
lean_inc(v_mvarId_888_);
v___x_956_ = l_Lean_Meta_throwTacticEx___redArg(v___x_889_, v_mvarId_888_, v___x_955_, v___y_931_, v___y_932_, v___y_933_, v___y_934_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_dec_ref_known(v___x_956_, 1);
v___y_899_ = v_a_936_;
v___y_900_ = v_type_941_;
v___y_901_ = v___x_937_;
v___y_902_ = v___y_931_;
v___y_903_ = v___y_932_;
v___y_904_ = v___y_933_;
v___y_905_ = v___y_934_;
goto v___jp_898_;
}
else
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_964_; 
lean_dec_ref(v_type_941_);
lean_dec(v_a_936_);
lean_dec_ref(v___y_931_);
lean_dec_ref(v_lctx_897_);
lean_dec(v_fvarId_890_);
lean_dec(v_mvarId_888_);
v_a_957_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_964_ == 0)
{
v___x_959_ = v___x_956_;
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_956_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_960_ == 0)
{
v___x_962_ = v___x_959_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_a_957_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
lean_dec(v_a_936_);
lean_dec_ref(v___y_931_);
lean_dec_ref(v_lctx_897_);
lean_dec(v_fvarId_890_);
lean_dec(v___x_889_);
lean_dec(v_mvarId_888_);
v_a_967_ = lean_ctor_get(v___x_939_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_974_ == 0)
{
v___x_969_ = v___x_939_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_939_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_967_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
else
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
lean_dec(v_a_936_);
lean_dec_ref(v___y_931_);
lean_dec_ref(v_lctx_897_);
lean_dec(v_fvarId_890_);
lean_dec(v___x_889_);
lean_dec(v_mvarId_888_);
v_a_975_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_982_ == 0)
{
v___x_977_ = v___x_938_;
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_938_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_980_; 
if (v_isShared_978_ == 0)
{
v___x_980_ = v___x_977_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_a_975_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
else
{
lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_990_; 
lean_dec_ref(v___y_931_);
lean_dec_ref(v_lctx_897_);
lean_dec(v_fvarId_890_);
lean_dec(v___x_889_);
lean_dec(v_mvarId_888_);
v_a_983_ = lean_ctor_get(v___x_935_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_990_ == 0)
{
v___x_985_ = v___x_935_;
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_935_);
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
else
{
lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1015_; 
lean_dec_ref(v___y_891_);
lean_dec(v_fvarId_890_);
lean_dec(v___x_889_);
lean_dec(v_mvarId_888_);
v_a_1008_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1010_ = v___x_896_;
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_dec(v___x_896_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1013_; 
if (v_isShared_1011_ == 0)
{
v___x_1013_ = v___x_1010_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_a_1008_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clear___lam__0___boxed(lean_object* v_mvarId_1016_, lean_object* v___x_1017_, lean_object* v_fvarId_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Lean_MVarId_clear___lam__0(v_mvarId_1016_, v___x_1017_, v_fvarId_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
lean_dec(v___y_1020_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clear(lean_object* v_mvarId_1025_, lean_object* v_fvarId_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_){
_start:
{
lean_object* v___x_1032_; lean_object* v___f_1033_; lean_object* v___x_1034_; 
v___x_1032_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__1));
lean_inc(v_mvarId_1025_);
v___f_1033_ = lean_alloc_closure((void*)(l_Lean_MVarId_clear___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1033_, 0, v_mvarId_1025_);
lean_closure_set(v___f_1033_, 1, v___x_1032_);
lean_closure_set(v___f_1033_, 2, v_fvarId_1026_);
v___x_1034_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg(v_mvarId_1025_, v___f_1033_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clear___boxed(lean_object* v_mvarId_1035_, lean_object* v_fvarId_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l_Lean_MVarId_clear(v_mvarId_1035_, v_fvarId_1036_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_);
lean_dec(v_a_1040_);
lean_dec_ref(v_a_1039_);
lean_dec(v_a_1038_);
lean_dec_ref(v_a_1037_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2(lean_object* v_mvarId_1043_, lean_object* v_val_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg(v_mvarId_1043_, v_val_1044_, v___y_1046_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___boxed(lean_object* v_mvarId_1051_, lean_object* v_val_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2(v_mvarId_1051_, v_val_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3(lean_object* v_00_u03b2_1059_, lean_object* v_x_1060_, lean_object* v_x_1061_, lean_object* v_x_1062_){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3___redArg(v_x_1060_, v_x_1061_, v_x_1062_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9(lean_object* v_00_u03b2_1064_, lean_object* v_x_1065_, size_t v_x_1066_, size_t v_x_1067_, lean_object* v_x_1068_, lean_object* v_x_1069_){
_start:
{
lean_object* v___x_1070_; 
v___x_1070_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_x_1065_, v_x_1066_, v_x_1067_, v_x_1068_, v_x_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___boxed(lean_object* v_00_u03b2_1071_, lean_object* v_x_1072_, lean_object* v_x_1073_, lean_object* v_x_1074_, lean_object* v_x_1075_, lean_object* v_x_1076_){
_start:
{
size_t v_x_8876__boxed_1077_; size_t v_x_8877__boxed_1078_; lean_object* v_res_1079_; 
v_x_8876__boxed_1077_ = lean_unbox_usize(v_x_1073_);
lean_dec(v_x_1073_);
v_x_8877__boxed_1078_ = lean_unbox_usize(v_x_1074_);
lean_dec(v_x_1074_);
v_res_1079_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9(v_00_u03b2_1071_, v_x_1072_, v_x_8876__boxed_1077_, v_x_8877__boxed_1078_, v_x_1075_, v_x_1076_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13(lean_object* v_00_u03b2_1080_, lean_object* v_n_1081_, lean_object* v_k_1082_, lean_object* v_v_1083_){
_start:
{
lean_object* v___x_1084_; 
v___x_1084_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13___redArg(v_n_1081_, v_k_1082_, v_v_1083_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14(lean_object* v_00_u03b2_1085_, size_t v_depth_1086_, lean_object* v_keys_1087_, lean_object* v_vals_1088_, lean_object* v_heq_1089_, lean_object* v_i_1090_, lean_object* v_entries_1091_){
_start:
{
lean_object* v___x_1092_; 
v___x_1092_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg(v_depth_1086_, v_keys_1087_, v_vals_1088_, v_i_1090_, v_entries_1091_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___boxed(lean_object* v_00_u03b2_1093_, lean_object* v_depth_1094_, lean_object* v_keys_1095_, lean_object* v_vals_1096_, lean_object* v_heq_1097_, lean_object* v_i_1098_, lean_object* v_entries_1099_){
_start:
{
size_t v_depth_boxed_1100_; lean_object* v_res_1101_; 
v_depth_boxed_1100_ = lean_unbox_usize(v_depth_1094_);
lean_dec(v_depth_1094_);
v_res_1101_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14(v_00_u03b2_1093_, v_depth_boxed_1100_, v_keys_1095_, v_vals_1096_, v_heq_1097_, v_i_1098_, v_entries_1099_);
lean_dec_ref(v_vals_1096_);
lean_dec_ref(v_keys_1095_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13_spec__14(lean_object* v_00_u03b2_1102_, lean_object* v_x_1103_, lean_object* v_x_1104_, lean_object* v_x_1105_, lean_object* v_x_1106_){
_start:
{
lean_object* v___x_1107_; 
v___x_1107_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13_spec__14___redArg(v_x_1103_, v_x_1104_, v_x_1105_, v_x_1106_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClear(lean_object* v_mvarId_1108_, lean_object* v_fvarId_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_){
_start:
{
lean_object* v___x_1115_; 
v___x_1115_ = l_Lean_Meta_saveState___redArg(v_a_1111_, v_a_1113_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v_a_1116_; lean_object* v___x_1117_; 
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_a_1116_);
lean_dec_ref_known(v___x_1115_, 1);
lean_inc(v_mvarId_1108_);
v___x_1117_ = l_Lean_MVarId_clear(v_mvarId_1108_, v_fvarId_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_dec(v_a_1116_);
lean_dec(v_mvarId_1108_);
return v___x_1117_;
}
else
{
lean_object* v_a_1118_; uint8_t v___x_1119_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
v___x_1119_ = l_Lean_Exception_isInterrupt(v_a_1118_);
if (v___x_1119_ == 0)
{
uint8_t v___x_1120_; 
lean_inc(v_a_1118_);
v___x_1120_ = l_Lean_Exception_isRuntime(v_a_1118_);
if (v___x_1120_ == 0)
{
lean_object* v___x_1121_; 
lean_dec_ref_known(v___x_1117_, 1);
v___x_1121_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1116_, v_a_1111_, v_a_1113_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1128_; 
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1128_ == 0)
{
lean_object* v_unused_1129_; 
v_unused_1129_ = lean_ctor_get(v___x_1121_, 0);
lean_dec(v_unused_1129_);
v___x_1123_ = v___x_1121_;
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
else
{
lean_dec(v___x_1121_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1126_; 
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 0, v_mvarId_1108_);
v___x_1126_ = v___x_1123_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_mvarId_1108_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
else
{
lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1137_; 
lean_dec(v_mvarId_1108_);
v_a_1130_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1132_ = v___x_1121_;
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v___x_1121_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_a_1130_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
else
{
lean_dec(v_a_1116_);
lean_dec(v_mvarId_1108_);
return v___x_1117_;
}
}
else
{
lean_dec(v_a_1116_);
lean_dec(v_mvarId_1108_);
return v___x_1117_;
}
}
}
else
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1145_; 
lean_dec(v_fvarId_1109_);
lean_dec(v_mvarId_1108_);
v_a_1138_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1140_ = v___x_1115_;
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1115_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1143_; 
if (v_isShared_1141_ == 0)
{
v___x_1143_ = v___x_1140_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_a_1138_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClear___boxed(lean_object* v_mvarId_1146_, lean_object* v_fvarId_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_Lean_MVarId_tryClear(v_mvarId_1146_, v_fvarId_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec_ref(v_a_1148_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0(lean_object* v_as_1154_, size_t v_i_1155_, size_t v_stop_1156_, lean_object* v_b_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
uint8_t v___x_1163_; 
v___x_1163_ = lean_usize_dec_eq(v_i_1155_, v_stop_1156_);
if (v___x_1163_ == 0)
{
size_t v___x_1164_; size_t v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1164_ = ((size_t)1ULL);
v___x_1165_ = lean_usize_sub(v_i_1155_, v___x_1164_);
v___x_1166_ = lean_array_uget_borrowed(v_as_1154_, v___x_1165_);
lean_inc(v___x_1166_);
v___x_1167_ = l_Lean_MVarId_tryClear(v_b_1157_, v___x_1166_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v_a_1168_; 
v_a_1168_ = lean_ctor_get(v___x_1167_, 0);
lean_inc(v_a_1168_);
lean_dec_ref_known(v___x_1167_, 1);
v_i_1155_ = v___x_1165_;
v_b_1157_ = v_a_1168_;
goto _start;
}
else
{
return v___x_1167_;
}
}
else
{
lean_object* v___x_1170_; 
v___x_1170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1170_, 0, v_b_1157_);
return v___x_1170_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0___boxed(lean_object* v_as_1171_, lean_object* v_i_1172_, lean_object* v_stop_1173_, lean_object* v_b_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
size_t v_i_boxed_1180_; size_t v_stop_boxed_1181_; lean_object* v_res_1182_; 
v_i_boxed_1180_ = lean_unbox_usize(v_i_1172_);
lean_dec(v_i_1172_);
v_stop_boxed_1181_ = lean_unbox_usize(v_stop_1173_);
lean_dec(v_stop_1173_);
v_res_1182_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0(v_as_1171_, v_i_boxed_1180_, v_stop_boxed_1181_, v_b_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
lean_dec_ref(v_as_1171_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany(lean_object* v_mvarId_1183_, lean_object* v_fvarIds_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_){
_start:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; uint8_t v___x_1192_; 
v___x_1190_ = lean_array_get_size(v_fvarIds_1184_);
v___x_1191_ = lean_unsigned_to_nat(0u);
v___x_1192_ = lean_nat_dec_lt(v___x_1191_, v___x_1190_);
if (v___x_1192_ == 0)
{
lean_object* v___x_1193_; 
v___x_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1193_, 0, v_mvarId_1183_);
return v___x_1193_;
}
else
{
size_t v___x_1194_; size_t v___x_1195_; lean_object* v___x_1196_; 
v___x_1194_ = lean_usize_of_nat(v___x_1190_);
v___x_1195_ = ((size_t)0ULL);
v___x_1196_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0(v_fvarIds_1184_, v___x_1194_, v___x_1195_, v_mvarId_1183_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_);
return v___x_1196_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany___boxed(lean_object* v_mvarId_1197_, lean_object* v_fvarIds_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l_Lean_MVarId_tryClearMany(v_mvarId_1197_, v_fvarIds_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_);
lean_dec(v_a_1202_);
lean_dec_ref(v_a_1201_);
lean_dec(v_a_1200_);
lean_dec_ref(v_a_1199_);
lean_dec_ref(v_fvarIds_1198_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0(lean_object* v_as_1205_, size_t v_i_1206_, size_t v_stop_1207_, lean_object* v_b_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
uint8_t v___x_1214_; 
v___x_1214_ = lean_usize_dec_eq(v_i_1206_, v_stop_1207_);
if (v___x_1214_ == 0)
{
lean_object* v_fst_1215_; lean_object* v_snd_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1241_; 
v_fst_1215_ = lean_ctor_get(v_b_1208_, 0);
v_snd_1216_ = lean_ctor_get(v_b_1208_, 1);
v_isSharedCheck_1241_ = !lean_is_exclusive(v_b_1208_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1218_ = v_b_1208_;
v_isShared_1219_ = v_isSharedCheck_1241_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_snd_1216_);
lean_inc(v_fst_1215_);
lean_dec(v_b_1208_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1241_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
size_t v___x_1220_; size_t v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1220_ = ((size_t)1ULL);
v___x_1221_ = lean_usize_sub(v_i_1206_, v___x_1220_);
v___x_1222_ = lean_array_uget_borrowed(v_as_1205_, v___x_1221_);
lean_inc(v___x_1222_);
lean_inc(v_fst_1215_);
v___x_1223_ = l_Lean_MVarId_tryClear(v_fst_1215_, v___x_1222_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
if (lean_obj_tag(v___x_1223_) == 0)
{
lean_object* v_a_1224_; lean_object* v___y_1226_; uint8_t v___x_1231_; 
v_a_1224_ = lean_ctor_get(v___x_1223_, 0);
lean_inc(v_a_1224_);
lean_dec_ref_known(v___x_1223_, 1);
v___x_1231_ = l_Lean_instBEqMVarId_beq(v_fst_1215_, v_a_1224_);
lean_dec(v_fst_1215_);
if (v___x_1231_ == 0)
{
lean_object* v___x_1232_; 
lean_inc(v___x_1222_);
v___x_1232_ = lean_array_push(v_snd_1216_, v___x_1222_);
v___y_1226_ = v___x_1232_;
goto v___jp_1225_;
}
else
{
v___y_1226_ = v_snd_1216_;
goto v___jp_1225_;
}
v___jp_1225_:
{
lean_object* v___x_1228_; 
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 1, v___y_1226_);
lean_ctor_set(v___x_1218_, 0, v_a_1224_);
v___x_1228_ = v___x_1218_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_a_1224_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v___y_1226_);
v___x_1228_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
v_i_1206_ = v___x_1221_;
v_b_1208_ = v___x_1228_;
goto _start;
}
}
}
else
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1240_; 
lean_del_object(v___x_1218_);
lean_dec(v_snd_1216_);
lean_dec(v_fst_1215_);
v_a_1233_ = lean_ctor_get(v___x_1223_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1235_ = v___x_1223_;
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1223_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1238_; 
if (v_isShared_1236_ == 0)
{
v___x_1238_ = v___x_1235_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_a_1233_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
}
}
else
{
lean_object* v___x_1242_; 
v___x_1242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1242_, 0, v_b_1208_);
return v___x_1242_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0___boxed(lean_object* v_as_1243_, lean_object* v_i_1244_, lean_object* v_stop_1245_, lean_object* v_b_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
size_t v_i_boxed_1252_; size_t v_stop_boxed_1253_; lean_object* v_res_1254_; 
v_i_boxed_1252_ = lean_unbox_usize(v_i_1244_);
lean_dec(v_i_1244_);
v_stop_boxed_1253_ = lean_unbox_usize(v_stop_1245_);
lean_dec(v_stop_1245_);
v_res_1254_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0(v_as_1243_, v_i_boxed_1252_, v_stop_boxed_1253_, v_b_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec_ref(v_as_1243_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany_x27___lam__0(lean_object* v_fvarIds_1255_, lean_object* v_goal_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v_lctx_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; uint8_t v___x_1268_; 
v_lctx_1262_ = lean_ctor_get(v___y_1257_, 2);
v___x_1263_ = l_Lean_LocalContext_sortFVarsByContextOrder(v_lctx_1262_, v_fvarIds_1255_);
v___x_1264_ = lean_array_get_size(v___x_1263_);
v___x_1265_ = lean_mk_empty_array_with_capacity(v___x_1264_);
v___x_1266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1266_, 0, v_goal_1256_);
lean_ctor_set(v___x_1266_, 1, v___x_1265_);
v___x_1267_ = lean_unsigned_to_nat(0u);
v___x_1268_ = lean_nat_dec_lt(v___x_1267_, v___x_1264_);
if (v___x_1268_ == 0)
{
lean_object* v___x_1269_; 
lean_dec_ref(v___x_1263_);
v___x_1269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1266_);
return v___x_1269_;
}
else
{
size_t v___x_1270_; size_t v___x_1271_; lean_object* v___x_1272_; 
v___x_1270_ = lean_usize_of_nat(v___x_1264_);
v___x_1271_ = ((size_t)0ULL);
v___x_1272_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0(v___x_1263_, v___x_1270_, v___x_1271_, v___x_1266_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
lean_dec_ref(v___x_1263_);
return v___x_1272_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany_x27___lam__0___boxed(lean_object* v_fvarIds_1273_, lean_object* v_goal_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l_Lean_MVarId_tryClearMany_x27___lam__0(v_fvarIds_1273_, v_goal_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany_x27(lean_object* v_goal_1281_, lean_object* v_fvarIds_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_){
_start:
{
lean_object* v___f_1288_; lean_object* v___x_1289_; 
lean_inc(v_goal_1281_);
v___f_1288_ = lean_alloc_closure((void*)(l_Lean_MVarId_tryClearMany_x27___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1288_, 0, v_fvarIds_1282_);
lean_closure_set(v___f_1288_, 1, v_goal_1281_);
v___x_1289_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg(v_goal_1281_, v___f_1288_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany_x27___boxed(lean_object* v_goal_1290_, lean_object* v_fvarIds_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_Lean_MVarId_tryClearMany_x27(v_goal_1290_, v_fvarIds_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_);
lean_dec(v_a_1295_);
lean_dec_ref(v_a_1294_);
lean_dec(v_a_1293_);
lean_dec_ref(v_a_1292_);
return v_res_1297_;
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
