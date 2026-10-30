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
size_t v_x_7720__boxed_419_; size_t v_x_7721__boxed_420_; lean_object* v_res_421_; 
v_x_7720__boxed_419_ = lean_unbox_usize(v_x_415_);
lean_dec(v_x_415_);
v_x_7721__boxed_420_ = lean_unbox_usize(v_x_416_);
lean_dec(v_x_416_);
v_res_421_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_x_414_, v_x_7720__boxed_419_, v_x_7721__boxed_420_, v_x_417_, v_x_418_);
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
lean_object* v___x_433_; lean_object* v_mctx_434_; lean_object* v_cache_435_; lean_object* v_zetaDeltaFVarIds_436_; lean_object* v_postponed_437_; lean_object* v_diag_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_468_; 
v___x_433_ = lean_st_ref_take(v___y_431_);
v_mctx_434_ = lean_ctor_get(v___x_433_, 0);
v_cache_435_ = lean_ctor_get(v___x_433_, 1);
v_zetaDeltaFVarIds_436_ = lean_ctor_get(v___x_433_, 2);
v_postponed_437_ = lean_ctor_get(v___x_433_, 3);
v_diag_438_ = lean_ctor_get(v___x_433_, 4);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_468_ == 0)
{
v___x_440_ = v___x_433_;
v_isShared_441_ = v_isSharedCheck_468_;
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
v_isShared_441_ = v_isSharedCheck_468_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v_depth_442_; lean_object* v_levelAssignDepth_443_; lean_object* v_lmvarCounter_444_; lean_object* v_mvarCounter_445_; lean_object* v_lDecls_446_; lean_object* v_decls_447_; lean_object* v_userNames_448_; lean_object* v_lAssignment_449_; lean_object* v_eAssignment_450_; lean_object* v_dAssignment_451_; lean_object* v_instanceTypedMVars_452_; lean_object* v_synthNormMemo_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_467_; 
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
v_synthNormMemo_453_ = lean_ctor_get(v_mctx_434_, 11);
v_isSharedCheck_467_ = !lean_is_exclusive(v_mctx_434_);
if (v_isSharedCheck_467_ == 0)
{
v___x_455_ = v_mctx_434_;
v_isShared_456_ = v_isSharedCheck_467_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_synthNormMemo_453_);
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
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_467_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_460_; 
v___x_457_ = lean_box(0);
v___x_458_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3___redArg(v_eAssignment_450_, v_mvarId_429_, v_val_430_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 8, v___x_458_);
v___x_460_ = v___x_455_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_depth_442_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v_levelAssignDepth_443_);
lean_ctor_set(v_reuseFailAlloc_466_, 2, v_lmvarCounter_444_);
lean_ctor_set(v_reuseFailAlloc_466_, 3, v_mvarCounter_445_);
lean_ctor_set(v_reuseFailAlloc_466_, 4, v_lDecls_446_);
lean_ctor_set(v_reuseFailAlloc_466_, 5, v_decls_447_);
lean_ctor_set(v_reuseFailAlloc_466_, 6, v_userNames_448_);
lean_ctor_set(v_reuseFailAlloc_466_, 7, v_lAssignment_449_);
lean_ctor_set(v_reuseFailAlloc_466_, 8, v___x_458_);
lean_ctor_set(v_reuseFailAlloc_466_, 9, v_dAssignment_451_);
lean_ctor_set(v_reuseFailAlloc_466_, 10, v_instanceTypedMVars_452_);
lean_ctor_set(v_reuseFailAlloc_466_, 11, v_synthNormMemo_453_);
v___x_460_ = v_reuseFailAlloc_466_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
lean_object* v___x_462_; 
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 0, v___x_460_);
v___x_462_ = v___x_440_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_460_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v_cache_435_);
lean_ctor_set(v_reuseFailAlloc_465_, 2, v_zetaDeltaFVarIds_436_);
lean_ctor_set(v_reuseFailAlloc_465_, 3, v_postponed_437_);
lean_ctor_set(v_reuseFailAlloc_465_, 4, v_diag_438_);
v___x_462_ = v_reuseFailAlloc_465_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = lean_st_ref_put(v___y_431_, v___x_462_);
v___x_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_464_, 0, v___x_457_);
return v___x_464_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg___boxed(lean_object* v_mvarId_469_, lean_object* v_val_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg(v_mvarId_469_, v_val_470_, v___y_471_);
lean_dec(v___y_471_);
return v_res_473_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_478_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__2));
v___x_479_ = l_Lean_stringToMessageData(v___x_478_);
return v___x_479_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__4));
v___x_482_ = l_Lean_stringToMessageData(v___x_481_);
return v___x_482_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7(void){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__6));
v___x_485_ = l_Lean_stringToMessageData(v___x_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9(lean_object* v_fvarId_486_, lean_object* v_mvarId_487_, lean_object* v_as_488_, size_t v_i_489_, size_t v_stop_490_, lean_object* v_b_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
lean_object* v_a_498_; uint8_t v___x_502_; 
v___x_502_ = lean_usize_dec_eq(v_i_489_, v_stop_490_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; 
v___x_503_ = lean_array_uget(v_as_488_, v_i_489_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v___x_504_; 
v___x_504_ = lean_box(0);
v_a_498_ = v___x_504_;
goto v___jp_497_;
}
else
{
lean_object* v_val_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_542_; 
v_val_505_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_542_ == 0)
{
v___x_507_ = v___x_503_;
v_isShared_508_ = v_isSharedCheck_542_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_val_505_);
lean_dec(v___x_503_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_542_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_509_; uint8_t v___x_510_; 
v___x_509_ = l_Lean_LocalDecl_fvarId(v_val_505_);
v___x_510_ = l_Lean_instBEqFVarId_beq(v___x_509_, v_fvarId_486_);
lean_dec(v___x_509_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; uint8_t v___x_512_; lean_object* v___x_513_; 
v___x_511_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__1));
v___x_512_ = 1;
lean_inc(v_fvarId_486_);
lean_inc(v_val_505_);
v___x_513_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg(v_val_505_, v_fvarId_486_, v___x_512_, v___y_493_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; uint8_t v___x_515_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc(v_a_514_);
lean_dec_ref_known(v___x_513_, 1);
v___x_515_ = lean_unbox(v_a_514_);
lean_dec(v_a_514_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; 
lean_del_object(v___x_507_);
lean_dec(v_val_505_);
v___x_516_ = lean_box(0);
v_a_498_ = v___x_516_;
goto v___jp_497_;
}
else
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_529_; 
v___x_517_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3);
v___x_518_ = l_Lean_LocalDecl_toExpr(v_val_505_);
v___x_519_ = l_Lean_MessageData_ofExpr(v___x_518_);
v___x_520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_517_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
v___x_521_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5);
v___x_522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_522_, 0, v___x_520_);
lean_ctor_set(v___x_522_, 1, v___x_521_);
lean_inc(v_fvarId_486_);
v___x_523_ = l_Lean_mkFVar(v_fvarId_486_);
v___x_524_ = l_Lean_MessageData_ofExpr(v___x_523_);
v___x_525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_522_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
v___x_526_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7);
v___x_527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_525_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 0, v___x_527_);
v___x_529_ = v___x_507_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_527_);
v___x_529_ = v_reuseFailAlloc_532_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
lean_object* v___x_530_; 
lean_inc(v_mvarId_487_);
v___x_530_ = l_Lean_Meta_throwTacticEx___redArg(v___x_511_, v_mvarId_487_, v___x_529_, v___y_492_, v___y_493_, v___y_494_, v___y_495_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v_a_531_; 
v_a_531_ = lean_ctor_get(v___x_530_, 0);
lean_inc(v_a_531_);
lean_dec_ref_known(v___x_530_, 1);
v_a_498_ = v_a_531_;
goto v___jp_497_;
}
else
{
lean_dec(v_mvarId_487_);
lean_dec(v_fvarId_486_);
return v___x_530_;
}
}
}
}
else
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_540_; 
lean_del_object(v___x_507_);
lean_dec(v_val_505_);
lean_dec(v_mvarId_487_);
lean_dec(v_fvarId_486_);
v_a_533_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_540_ == 0)
{
v___x_535_ = v___x_513_;
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_513_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_538_; 
if (v_isShared_536_ == 0)
{
v___x_538_ = v___x_535_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_a_533_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
else
{
lean_object* v___x_541_; 
lean_del_object(v___x_507_);
lean_dec(v_val_505_);
v___x_541_ = lean_box(0);
v_a_498_ = v___x_541_;
goto v___jp_497_;
}
}
}
}
else
{
lean_object* v___x_543_; 
lean_dec(v_mvarId_487_);
lean_dec(v_fvarId_486_);
v___x_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_543_, 0, v_b_491_);
return v___x_543_;
}
v___jp_497_:
{
size_t v___x_499_; size_t v___x_500_; 
v___x_499_ = ((size_t)1ULL);
v___x_500_ = lean_usize_add(v_i_489_, v___x_499_);
v_i_489_ = v___x_500_;
v_b_491_ = v_a_498_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___boxed(lean_object* v_fvarId_544_, lean_object* v_mvarId_545_, lean_object* v_as_546_, lean_object* v_i_547_, lean_object* v_stop_548_, lean_object* v_b_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
size_t v_i_boxed_555_; size_t v_stop_boxed_556_; lean_object* v_res_557_; 
v_i_boxed_555_ = lean_unbox_usize(v_i_547_);
lean_dec(v_i_547_);
v_stop_boxed_556_ = lean_unbox_usize(v_stop_548_);
lean_dec(v_stop_548_);
v_res_557_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9(v_fvarId_544_, v_mvarId_545_, v_as_546_, v_i_boxed_555_, v_stop_boxed_556_, v_b_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
lean_dec(v___y_551_);
lean_dec_ref(v___y_550_);
lean_dec_ref(v_as_546_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(lean_object* v_fvarId_558_, lean_object* v_mvarId_559_, lean_object* v_as_560_, size_t v_i_561_, size_t v_stop_562_, lean_object* v_b_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
lean_object* v_a_570_; uint8_t v___x_574_; 
v___x_574_ = lean_usize_dec_eq(v_i_561_, v_stop_562_);
if (v___x_574_ == 0)
{
lean_object* v___x_575_; 
v___x_575_ = lean_array_uget(v_as_560_, v_i_561_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v___x_576_; 
v___x_576_ = lean_box(0);
v_a_570_ = v___x_576_;
goto v___jp_569_;
}
else
{
lean_object* v_val_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_614_; 
v_val_577_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_614_ == 0)
{
v___x_579_ = v___x_575_;
v_isShared_580_ = v_isSharedCheck_614_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_val_577_);
lean_dec(v___x_575_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_614_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_581_; uint8_t v___x_582_; 
v___x_581_ = l_Lean_LocalDecl_fvarId(v_val_577_);
v___x_582_ = l_Lean_instBEqFVarId_beq(v___x_581_, v_fvarId_558_);
lean_dec(v___x_581_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; uint8_t v___x_584_; lean_object* v___x_585_; 
v___x_583_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__1));
v___x_584_ = 1;
lean_inc(v_fvarId_558_);
lean_inc(v_val_577_);
v___x_585_ = l_Lean_localDeclDependsOn___at___00Lean_MVarId_clear_spec__0___redArg(v_val_577_, v_fvarId_558_, v___x_584_, v___y_565_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v_a_586_; uint8_t v___x_587_; 
v_a_586_ = lean_ctor_get(v___x_585_, 0);
lean_inc(v_a_586_);
lean_dec_ref_known(v___x_585_, 1);
v___x_587_ = lean_unbox(v_a_586_);
lean_dec(v_a_586_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; 
lean_del_object(v___x_579_);
lean_dec(v_val_577_);
v___x_588_ = lean_box(0);
v_a_570_ = v___x_588_;
goto v___jp_569_;
}
else
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_601_; 
v___x_589_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__3);
v___x_590_ = l_Lean_LocalDecl_toExpr(v_val_577_);
v___x_591_ = l_Lean_MessageData_ofExpr(v___x_590_);
v___x_592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_589_);
lean_ctor_set(v___x_592_, 1, v___x_591_);
v___x_593_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__5);
v___x_594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_594_, 0, v___x_592_);
lean_ctor_set(v___x_594_, 1, v___x_593_);
lean_inc(v_fvarId_558_);
v___x_595_ = l_Lean_mkFVar(v_fvarId_558_);
v___x_596_ = l_Lean_MessageData_ofExpr(v___x_595_);
v___x_597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_597_, 0, v___x_594_);
lean_ctor_set(v___x_597_, 1, v___x_596_);
v___x_598_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7);
v___x_599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_599_, 0, v___x_597_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 0, v___x_599_);
v___x_601_ = v___x_579_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_599_);
v___x_601_ = v_reuseFailAlloc_604_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
lean_object* v___x_602_; 
lean_inc(v_mvarId_559_);
v___x_602_ = l_Lean_Meta_throwTacticEx___redArg(v___x_583_, v_mvarId_559_, v___x_601_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v_a_603_; 
v_a_603_ = lean_ctor_get(v___x_602_, 0);
lean_inc(v_a_603_);
lean_dec_ref_known(v___x_602_, 1);
v_a_570_ = v_a_603_;
goto v___jp_569_;
}
else
{
lean_dec(v_mvarId_559_);
lean_dec(v_fvarId_558_);
return v___x_602_;
}
}
}
}
else
{
lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_612_; 
lean_del_object(v___x_579_);
lean_dec(v_val_577_);
lean_dec(v_mvarId_559_);
lean_dec(v_fvarId_558_);
v_a_605_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_612_ == 0)
{
v___x_607_ = v___x_585_;
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v___x_585_);
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
lean_object* v___x_613_; 
lean_del_object(v___x_579_);
lean_dec(v_val_577_);
v___x_613_ = lean_box(0);
v_a_570_ = v___x_613_;
goto v___jp_569_;
}
}
}
}
else
{
lean_object* v___x_615_; 
lean_dec(v_mvarId_559_);
lean_dec(v_fvarId_558_);
v___x_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_615_, 0, v_b_563_);
return v___x_615_;
}
v___jp_569_:
{
size_t v___x_571_; size_t v___x_572_; lean_object* v___x_573_; 
v___x_571_ = ((size_t)1ULL);
v___x_572_ = lean_usize_add(v_i_561_, v___x_571_);
v___x_573_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9(v_fvarId_558_, v_mvarId_559_, v_as_560_, v___x_572_, v_stop_562_, v_a_570_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
return v___x_573_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5___boxed(lean_object* v_fvarId_616_, lean_object* v_mvarId_617_, lean_object* v_as_618_, lean_object* v_i_619_, lean_object* v_stop_620_, lean_object* v_b_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
size_t v_i_boxed_627_; size_t v_stop_boxed_628_; lean_object* v_res_629_; 
v_i_boxed_627_ = lean_unbox_usize(v_i_619_);
lean_dec(v_i_619_);
v_stop_boxed_628_ = lean_unbox_usize(v_stop_620_);
lean_dec(v_stop_620_);
v_res_629_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_616_, v_mvarId_617_, v_as_618_, v_i_boxed_627_, v_stop_boxed_628_, v_b_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec_ref(v_as_618_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6(lean_object* v_fvarId_630_, lean_object* v_mvarId_631_, lean_object* v_x_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
if (lean_obj_tag(v_x_632_) == 0)
{
lean_object* v_cs_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_652_; 
v_cs_638_ = lean_ctor_get(v_x_632_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v_x_632_);
if (v_isSharedCheck_652_ == 0)
{
v___x_640_ = v_x_632_;
v_isShared_641_ = v_isSharedCheck_652_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_cs_638_);
lean_dec(v_x_632_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_652_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; uint8_t v___x_645_; 
v___x_642_ = lean_unsigned_to_nat(0u);
v___x_643_ = lean_array_get_size(v_cs_638_);
v___x_644_ = lean_box(0);
v___x_645_ = lean_nat_dec_lt(v___x_642_, v___x_643_);
if (v___x_645_ == 0)
{
lean_object* v___x_647_; 
lean_dec_ref(v_cs_638_);
lean_dec(v_mvarId_631_);
lean_dec(v_fvarId_630_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 0, v___x_644_);
v___x_647_ = v___x_640_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_644_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
else
{
size_t v___x_649_; size_t v___x_650_; lean_object* v___x_651_; 
lean_del_object(v___x_640_);
v___x_649_ = ((size_t)0ULL);
v___x_650_ = lean_usize_of_nat(v___x_643_);
v___x_651_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(v_fvarId_630_, v_mvarId_631_, v_cs_638_, v___x_649_, v___x_650_, v___x_644_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
lean_dec_ref(v_cs_638_);
return v___x_651_;
}
}
}
else
{
lean_object* v_vs_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_667_; 
v_vs_653_ = lean_ctor_get(v_x_632_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v_x_632_);
if (v_isSharedCheck_667_ == 0)
{
v___x_655_ = v_x_632_;
v_isShared_656_ = v_isSharedCheck_667_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_vs_653_);
lean_dec(v_x_632_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_667_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; uint8_t v___x_660_; 
v___x_657_ = lean_unsigned_to_nat(0u);
v___x_658_ = lean_array_get_size(v_vs_653_);
v___x_659_ = lean_box(0);
v___x_660_ = lean_nat_dec_lt(v___x_657_, v___x_658_);
if (v___x_660_ == 0)
{
lean_object* v___x_662_; 
lean_dec_ref(v_vs_653_);
lean_dec(v_mvarId_631_);
lean_dec(v_fvarId_630_);
if (v_isShared_656_ == 0)
{
lean_ctor_set_tag(v___x_655_, 0);
lean_ctor_set(v___x_655_, 0, v___x_659_);
v___x_662_ = v___x_655_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v___x_659_);
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
lean_del_object(v___x_655_);
v___x_664_ = ((size_t)0ULL);
v___x_665_ = lean_usize_of_nat(v___x_658_);
v___x_666_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_630_, v_mvarId_631_, v_vs_653_, v___x_664_, v___x_665_, v___x_659_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
lean_dec_ref(v_vs_653_);
return v___x_666_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(lean_object* v_fvarId_668_, lean_object* v_mvarId_669_, lean_object* v_as_670_, size_t v_i_671_, size_t v_stop_672_, lean_object* v_b_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
uint8_t v___x_679_; 
v___x_679_ = lean_usize_dec_eq(v_i_671_, v_stop_672_);
if (v___x_679_ == 0)
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = lean_array_uget_borrowed(v_as_670_, v_i_671_);
lean_inc(v___x_680_);
lean_inc(v_mvarId_669_);
lean_inc(v_fvarId_668_);
v___x_681_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6(v_fvarId_668_, v_mvarId_669_, v___x_680_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v_a_682_; size_t v___x_683_; size_t v___x_684_; 
v_a_682_ = lean_ctor_get(v___x_681_, 0);
lean_inc(v_a_682_);
lean_dec_ref_known(v___x_681_, 1);
v___x_683_ = ((size_t)1ULL);
v___x_684_ = lean_usize_add(v_i_671_, v___x_683_);
v_i_671_ = v___x_684_;
v_b_673_ = v_a_682_;
goto _start;
}
else
{
lean_dec(v_mvarId_669_);
lean_dec(v_fvarId_668_);
return v___x_681_;
}
}
else
{
lean_object* v___x_686_; 
lean_dec(v_mvarId_669_);
lean_dec(v_fvarId_668_);
v___x_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_686_, 0, v_b_673_);
return v___x_686_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7___boxed(lean_object* v_fvarId_687_, lean_object* v_mvarId_688_, lean_object* v_as_689_, lean_object* v_i_690_, lean_object* v_stop_691_, lean_object* v_b_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
size_t v_i_boxed_698_; size_t v_stop_boxed_699_; lean_object* v_res_700_; 
v_i_boxed_698_ = lean_unbox_usize(v_i_690_);
lean_dec(v_i_690_);
v_stop_boxed_699_ = lean_unbox_usize(v_stop_691_);
lean_dec(v_stop_691_);
v_res_700_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(v_fvarId_687_, v_mvarId_688_, v_as_689_, v_i_boxed_698_, v_stop_boxed_699_, v_b_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
lean_dec_ref(v_as_689_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6___boxed(lean_object* v_fvarId_701_, lean_object* v_mvarId_702_, lean_object* v_x_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6(v_fvarId_701_, v_mvarId_702_, v_x_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6(lean_object* v_fvarId_710_, lean_object* v_mvarId_711_, lean_object* v_t_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v_root_718_; lean_object* v_tail_719_; lean_object* v___x_720_; 
v_root_718_ = lean_ctor_get(v_t_712_, 0);
lean_inc_ref(v_root_718_);
v_tail_719_ = lean_ctor_get(v_t_712_, 1);
lean_inc_ref(v_tail_719_);
lean_dec_ref(v_t_712_);
lean_inc(v_mvarId_711_);
lean_inc(v_fvarId_710_);
v___x_720_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__6(v_fvarId_710_, v_mvarId_711_, v_root_718_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_734_; 
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_734_ == 0)
{
lean_object* v_unused_735_; 
v_unused_735_ = lean_ctor_get(v___x_720_, 0);
lean_dec(v_unused_735_);
v___x_722_ = v___x_720_;
v_isShared_723_ = v_isSharedCheck_734_;
goto v_resetjp_721_;
}
else
{
lean_dec(v___x_720_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_734_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; uint8_t v___x_727_; 
v___x_724_ = lean_unsigned_to_nat(0u);
v___x_725_ = lean_array_get_size(v_tail_719_);
v___x_726_ = lean_box(0);
v___x_727_ = lean_nat_dec_lt(v___x_724_, v___x_725_);
if (v___x_727_ == 0)
{
lean_object* v___x_729_; 
lean_dec_ref(v_tail_719_);
lean_dec(v_mvarId_711_);
lean_dec(v_fvarId_710_);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 0, v___x_726_);
v___x_729_ = v___x_722_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_726_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
else
{
size_t v___x_731_; size_t v___x_732_; lean_object* v___x_733_; 
lean_del_object(v___x_722_);
v___x_731_ = ((size_t)0ULL);
v___x_732_ = lean_usize_of_nat(v___x_725_);
v___x_733_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_710_, v_mvarId_711_, v_tail_719_, v___x_731_, v___x_732_, v___x_726_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
lean_dec_ref(v_tail_719_);
return v___x_733_;
}
}
}
else
{
lean_dec_ref(v_tail_719_);
lean_dec(v_mvarId_711_);
lean_dec(v_fvarId_710_);
return v___x_720_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6___boxed(lean_object* v_fvarId_736_, lean_object* v_mvarId_737_, lean_object* v_t_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6(v_fvarId_736_, v_mvarId_737_, v_t_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
return v_res_744_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4(lean_object* v_fvarId_746_, lean_object* v_mvarId_747_, lean_object* v_x_748_, size_t v_x_749_, size_t v_x_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
if (lean_obj_tag(v_x_748_) == 0)
{
lean_object* v_cs_756_; lean_object* v___x_757_; size_t v___x_758_; lean_object* v_j_759_; lean_object* v___x_760_; size_t v___x_761_; size_t v___x_762_; size_t v___x_763_; size_t v___x_764_; size_t v___x_765_; size_t v___x_766_; lean_object* v___x_767_; 
v_cs_756_ = lean_ctor_get(v_x_748_, 0);
lean_inc_ref(v_cs_756_);
lean_dec_ref_known(v_x_748_, 1);
v___x_757_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___closed__0);
v___x_758_ = lean_usize_shift_right(v_x_749_, v_x_750_);
v_j_759_ = lean_usize_to_nat(v___x_758_);
v___x_760_ = lean_array_get_borrowed(v___x_757_, v_cs_756_, v_j_759_);
v___x_761_ = ((size_t)1ULL);
v___x_762_ = lean_usize_shift_left(v___x_761_, v_x_750_);
v___x_763_ = lean_usize_sub(v___x_762_, v___x_761_);
v___x_764_ = lean_usize_land(v_x_749_, v___x_763_);
v___x_765_ = ((size_t)5ULL);
v___x_766_ = lean_usize_sub(v_x_750_, v___x_765_);
lean_inc(v___x_760_);
lean_inc(v_mvarId_747_);
lean_inc(v_fvarId_746_);
v___x_767_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4(v_fvarId_746_, v_mvarId_747_, v___x_760_, v___x_764_, v___x_766_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_782_; 
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_782_ == 0)
{
lean_object* v_unused_783_; 
v_unused_783_ = lean_ctor_get(v___x_767_, 0);
lean_dec(v_unused_783_);
v___x_769_ = v___x_767_;
v_isShared_770_ = v_isSharedCheck_782_;
goto v_resetjp_768_;
}
else
{
lean_dec(v___x_767_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_782_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; uint8_t v___x_775_; 
v___x_771_ = lean_unsigned_to_nat(1u);
v___x_772_ = lean_nat_add(v_j_759_, v___x_771_);
lean_dec(v_j_759_);
v___x_773_ = lean_array_get_size(v_cs_756_);
v___x_774_ = lean_box(0);
v___x_775_ = lean_nat_dec_lt(v___x_772_, v___x_773_);
if (v___x_775_ == 0)
{
lean_object* v___x_777_; 
lean_dec(v___x_772_);
lean_dec_ref(v_cs_756_);
lean_dec(v_mvarId_747_);
lean_dec(v_fvarId_746_);
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 0, v___x_774_);
v___x_777_ = v___x_769_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_774_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
else
{
size_t v___x_779_; size_t v___x_780_; lean_object* v___x_781_; 
lean_del_object(v___x_769_);
v___x_779_ = lean_usize_of_nat(v___x_772_);
lean_dec(v___x_772_);
v___x_780_ = lean_usize_of_nat(v___x_773_);
v___x_781_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4_spec__7(v_fvarId_746_, v_mvarId_747_, v_cs_756_, v___x_779_, v___x_780_, v___x_774_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
lean_dec_ref(v_cs_756_);
return v___x_781_;
}
}
}
else
{
lean_dec(v_j_759_);
lean_dec_ref(v_cs_756_);
lean_dec(v_mvarId_747_);
lean_dec(v_fvarId_746_);
return v___x_767_;
}
}
else
{
lean_object* v_vs_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_798_; 
v_vs_784_ = lean_ctor_get(v_x_748_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v_x_748_);
if (v_isSharedCheck_798_ == 0)
{
v___x_786_ = v_x_748_;
v_isShared_787_ = v_isSharedCheck_798_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_vs_784_);
lean_dec(v_x_748_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_798_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; uint8_t v___x_791_; 
v___x_788_ = lean_usize_to_nat(v_x_749_);
v___x_789_ = lean_array_get_size(v_vs_784_);
v___x_790_ = lean_box(0);
v___x_791_ = lean_nat_dec_lt(v___x_788_, v___x_789_);
if (v___x_791_ == 0)
{
lean_object* v___x_793_; 
lean_dec(v___x_788_);
lean_dec_ref(v_vs_784_);
lean_dec(v_mvarId_747_);
lean_dec(v_fvarId_746_);
if (v_isShared_787_ == 0)
{
lean_ctor_set_tag(v___x_786_, 0);
lean_ctor_set(v___x_786_, 0, v___x_790_);
v___x_793_ = v___x_786_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_790_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
else
{
size_t v___x_795_; size_t v___x_796_; lean_object* v___x_797_; 
lean_del_object(v___x_786_);
v___x_795_ = lean_usize_of_nat(v___x_788_);
lean_dec(v___x_788_);
v___x_796_ = lean_usize_of_nat(v___x_789_);
v___x_797_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_746_, v_mvarId_747_, v_vs_784_, v___x_795_, v___x_796_, v___x_790_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
lean_dec_ref(v_vs_784_);
return v___x_797_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4___boxed(lean_object* v_fvarId_799_, lean_object* v_mvarId_800_, lean_object* v_x_801_, lean_object* v_x_802_, lean_object* v_x_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
size_t v_x_8363__boxed_809_; size_t v_x_8364__boxed_810_; lean_object* v_res_811_; 
v_x_8363__boxed_809_ = lean_unbox_usize(v_x_802_);
lean_dec(v_x_802_);
v_x_8364__boxed_810_ = lean_unbox_usize(v_x_803_);
lean_dec(v_x_803_);
v_res_811_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4(v_fvarId_799_, v_mvarId_800_, v_x_801_, v_x_8363__boxed_809_, v_x_8364__boxed_810_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1(lean_object* v_fvarId_812_, lean_object* v_mvarId_813_, lean_object* v_t_814_, lean_object* v_start_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
lean_object* v___x_821_; uint8_t v___x_822_; 
v___x_821_ = lean_unsigned_to_nat(0u);
v___x_822_ = lean_nat_dec_eq(v_start_815_, v___x_821_);
if (v___x_822_ == 0)
{
lean_object* v_root_823_; lean_object* v_tail_824_; size_t v_shift_825_; lean_object* v_tailOff_826_; uint8_t v___x_827_; 
v_root_823_ = lean_ctor_get(v_t_814_, 0);
lean_inc_ref(v_root_823_);
v_tail_824_ = lean_ctor_get(v_t_814_, 1);
lean_inc_ref(v_tail_824_);
v_shift_825_ = lean_ctor_get_usize(v_t_814_, 4);
v_tailOff_826_ = lean_ctor_get(v_t_814_, 3);
lean_inc(v_tailOff_826_);
lean_dec_ref(v_t_814_);
v___x_827_ = lean_nat_dec_le(v_tailOff_826_, v_start_815_);
if (v___x_827_ == 0)
{
size_t v___x_828_; lean_object* v___x_829_; 
lean_dec(v_tailOff_826_);
v___x_828_ = lean_usize_of_nat(v_start_815_);
lean_inc(v_mvarId_813_);
lean_inc(v_fvarId_812_);
v___x_829_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__4(v_fvarId_812_, v_mvarId_813_, v_root_823_, v___x_828_, v_shift_825_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_842_; 
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_842_ == 0)
{
lean_object* v_unused_843_; 
v_unused_843_ = lean_ctor_get(v___x_829_, 0);
lean_dec(v_unused_843_);
v___x_831_ = v___x_829_;
v_isShared_832_ = v_isSharedCheck_842_;
goto v_resetjp_830_;
}
else
{
lean_dec(v___x_829_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_842_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_833_; lean_object* v___x_834_; uint8_t v___x_835_; 
v___x_833_ = lean_array_get_size(v_tail_824_);
v___x_834_ = lean_box(0);
v___x_835_ = lean_nat_dec_lt(v___x_821_, v___x_833_);
if (v___x_835_ == 0)
{
lean_object* v___x_837_; 
lean_dec_ref(v_tail_824_);
lean_dec(v_mvarId_813_);
lean_dec(v_fvarId_812_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 0, v___x_834_);
v___x_837_ = v___x_831_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_834_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
else
{
size_t v___x_839_; size_t v___x_840_; lean_object* v___x_841_; 
lean_del_object(v___x_831_);
v___x_839_ = ((size_t)0ULL);
v___x_840_ = lean_usize_of_nat(v___x_833_);
v___x_841_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_812_, v_mvarId_813_, v_tail_824_, v___x_839_, v___x_840_, v___x_834_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
lean_dec_ref(v_tail_824_);
return v___x_841_;
}
}
}
else
{
lean_dec_ref(v_tail_824_);
lean_dec(v_mvarId_813_);
lean_dec(v_fvarId_812_);
return v___x_829_;
}
}
else
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; uint8_t v___x_847_; 
lean_dec_ref(v_root_823_);
v___x_844_ = lean_nat_sub(v_start_815_, v_tailOff_826_);
lean_dec(v_tailOff_826_);
v___x_845_ = lean_array_get_size(v_tail_824_);
v___x_846_ = lean_box(0);
v___x_847_ = lean_nat_dec_lt(v___x_844_, v___x_845_);
if (v___x_847_ == 0)
{
lean_object* v___x_848_; 
lean_dec(v___x_844_);
lean_dec_ref(v_tail_824_);
lean_dec(v_mvarId_813_);
lean_dec(v_fvarId_812_);
v___x_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_848_, 0, v___x_846_);
return v___x_848_;
}
else
{
size_t v___x_849_; size_t v___x_850_; lean_object* v___x_851_; 
v___x_849_ = lean_usize_of_nat(v___x_844_);
lean_dec(v___x_844_);
v___x_850_ = lean_usize_of_nat(v___x_845_);
v___x_851_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5(v_fvarId_812_, v_mvarId_813_, v_tail_824_, v___x_849_, v___x_850_, v___x_846_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
lean_dec_ref(v_tail_824_);
return v___x_851_;
}
}
}
else
{
lean_object* v___x_852_; 
v___x_852_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__6(v_fvarId_812_, v_mvarId_813_, v_t_814_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
return v___x_852_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1___boxed(lean_object* v_fvarId_853_, lean_object* v_mvarId_854_, lean_object* v_t_855_, lean_object* v_start_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1(v_fvarId_853_, v_mvarId_854_, v_t_855_, v_start_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec(v_start_856_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1(lean_object* v_fvarId_863_, lean_object* v_mvarId_864_, lean_object* v_lctx_865_, lean_object* v_start_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v_decls_872_; lean_object* v___x_873_; 
v_decls_872_ = lean_ctor_get(v_lctx_865_, 1);
lean_inc_ref(v_decls_872_);
lean_dec_ref(v_lctx_865_);
v___x_873_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1(v_fvarId_863_, v_mvarId_864_, v_decls_872_, v_start_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1___boxed(lean_object* v_fvarId_874_, lean_object* v_mvarId_875_, lean_object* v_lctx_876_, lean_object* v_start_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1(v_fvarId_874_, v_mvarId_875_, v_lctx_876_, v_start_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v_start_877_);
return v_res_883_;
}
}
static lean_object* _init_l_Lean_MVarId_clear___lam__0___closed__1(void){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_885_ = ((lean_object*)(l_Lean_MVarId_clear___lam__0___closed__0));
v___x_886_ = l_Lean_stringToMessageData(v___x_885_);
return v___x_886_;
}
}
static lean_object* _init_l_Lean_MVarId_clear___lam__0___closed__3(void){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = ((lean_object*)(l_Lean_MVarId_clear___lam__0___closed__2));
v___x_889_ = l_Lean_stringToMessageData(v___x_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clear___lam__0(lean_object* v_mvarId_890_, lean_object* v___x_891_, lean_object* v_fvarId_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
lean_object* v___x_898_; 
lean_inc(v___x_891_);
lean_inc(v_mvarId_890_);
v___x_898_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_890_, v___x_891_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
if (lean_obj_tag(v___x_898_) == 0)
{
lean_object* v_lctx_899_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v___y_903_; lean_object* v___y_904_; lean_object* v___y_905_; lean_object* v___y_906_; lean_object* v___y_907_; lean_object* v___y_933_; lean_object* v___y_934_; lean_object* v___y_935_; lean_object* v___y_936_; uint8_t v___x_993_; 
lean_dec_ref_known(v___x_898_, 1);
v_lctx_899_ = lean_ctor_get(v___y_893_, 2);
lean_inc_ref(v_lctx_899_);
v___x_993_ = l_Lean_LocalContext_contains(v_lctx_899_, v_fvarId_892_);
if (v___x_993_ == 0)
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_994_ = lean_obj_once(&l_Lean_MVarId_clear___lam__0___closed__3, &l_Lean_MVarId_clear___lam__0___closed__3_once, _init_l_Lean_MVarId_clear___lam__0___closed__3);
lean_inc(v_fvarId_892_);
v___x_995_ = l_Lean_mkFVar(v_fvarId_892_);
v___x_996_ = l_Lean_MessageData_ofExpr(v___x_995_);
v___x_997_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_994_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
v___x_998_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7);
v___x_999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_997_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
v___x_1000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
lean_inc(v_mvarId_890_);
lean_inc(v___x_891_);
v___x_1001_ = l_Lean_Meta_throwTacticEx___redArg(v___x_891_, v_mvarId_890_, v___x_1000_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_dec_ref_known(v___x_1001_, 1);
v___y_933_ = v___y_893_;
v___y_934_ = v___y_894_;
v___y_935_ = v___y_895_;
v___y_936_ = v___y_896_;
goto v___jp_932_;
}
else
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
lean_dec_ref(v_lctx_899_);
lean_dec_ref(v___y_893_);
lean_dec(v_fvarId_892_);
lean_dec(v___x_891_);
lean_dec(v_mvarId_890_);
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1004_ = v___x_1001_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_1001_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_a_1002_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
else
{
v___y_933_ = v___y_893_;
v___y_934_ = v___y_894_;
v___y_935_ = v___y_895_;
v___y_936_ = v___y_896_;
goto v___jp_932_;
}
v___jp_900_:
{
lean_object* v_localInstances_908_; lean_object* v___x_909_; lean_object* v___x_910_; uint8_t v___x_911_; lean_object* v___x_912_; 
v_localInstances_908_ = lean_ctor_get(v___y_904_, 3);
v___x_909_ = l_Lean_LocalContext_erase(v_lctx_899_, v_fvarId_892_);
lean_inc_ref(v_localInstances_908_);
v___x_910_ = l_Lean_LocalInstances_erase(v_localInstances_908_, v_fvarId_892_);
v___x_911_ = 2;
v___x_912_ = l_Lean_Meta_mkFreshExprMVarAt(v___x_909_, v___x_910_, v___y_902_, v___x_911_, v___y_903_, v___y_901_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
lean_dec_ref(v___y_904_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v_a_913_; lean_object* v___x_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_922_; 
v_a_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc_n(v_a_913_, 2);
lean_dec_ref_known(v___x_912_, 1);
v___x_914_ = l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg(v_mvarId_890_, v_a_913_, v___y_905_);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_922_ == 0)
{
lean_object* v_unused_923_; 
v_unused_923_ = lean_ctor_get(v___x_914_, 0);
lean_dec(v_unused_923_);
v___x_916_ = v___x_914_;
v_isShared_917_ = v_isSharedCheck_922_;
goto v_resetjp_915_;
}
else
{
lean_dec(v___x_914_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_922_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_918_; lean_object* v___x_920_; 
v___x_918_ = l_Lean_Expr_mvarId_x21(v_a_913_);
lean_dec(v_a_913_);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 0, v___x_918_);
v___x_920_ = v___x_916_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_918_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
else
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
lean_dec(v_mvarId_890_);
v_a_924_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_912_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_912_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_924_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
v___jp_932_:
{
lean_object* v___x_937_; 
lean_inc(v_mvarId_890_);
v___x_937_ = l_Lean_MVarId_getTag(v_mvarId_890_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v_a_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v_a_938_ = lean_ctor_get(v___x_937_, 0);
lean_inc(v_a_938_);
lean_dec_ref_known(v___x_937_, 1);
v___x_939_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_lctx_899_);
lean_inc(v_mvarId_890_);
lean_inc(v_fvarId_892_);
v___x_940_ = l_Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1(v_fvarId_892_, v_mvarId_890_, v_lctx_899_, v___x_939_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v___x_941_; 
lean_dec_ref_known(v___x_940_, 1);
lean_inc(v_mvarId_890_);
v___x_941_ = l_Lean_MVarId_getDecl(v_mvarId_890_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
if (lean_obj_tag(v___x_941_) == 0)
{
lean_object* v_a_942_; lean_object* v_type_943_; lean_object* v___x_944_; lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_968_; 
v_a_942_ = lean_ctor_get(v___x_941_, 0);
lean_inc(v_a_942_);
lean_dec_ref_known(v___x_941_, 1);
v_type_943_ = lean_ctor_get(v_a_942_, 2);
lean_inc_ref_n(v_type_943_, 2);
lean_dec(v_a_942_);
lean_inc(v_fvarId_892_);
v___x_944_ = l_Lean_exprDependsOn___at___00Lean_MVarId_clear_spec__3___redArg(v_type_943_, v_fvarId_892_, v___y_934_);
v_a_945_ = lean_ctor_get(v___x_944_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_968_ == 0)
{
v___x_947_ = v___x_944_;
v_isShared_948_ = v_isSharedCheck_968_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_dec(v___x_944_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_968_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
uint8_t v___x_949_; 
v___x_949_ = lean_unbox(v_a_945_);
lean_dec(v_a_945_);
if (v___x_949_ == 0)
{
lean_del_object(v___x_947_);
lean_dec(v___x_891_);
v___y_901_ = v___x_939_;
v___y_902_ = v_type_943_;
v___y_903_ = v_a_938_;
v___y_904_ = v___y_933_;
v___y_905_ = v___y_934_;
v___y_906_ = v___y_935_;
v___y_907_ = v___y_936_;
goto v___jp_900_;
}
else
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_957_; 
v___x_950_ = lean_obj_once(&l_Lean_MVarId_clear___lam__0___closed__1, &l_Lean_MVarId_clear___lam__0___closed__1_once, _init_l_Lean_MVarId_clear___lam__0___closed__1);
lean_inc(v_fvarId_892_);
v___x_951_ = l_Lean_mkFVar(v_fvarId_892_);
v___x_952_ = l_Lean_MessageData_ofExpr(v___x_951_);
v___x_953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_953_, 0, v___x_950_);
lean_ctor_set(v___x_953_, 1, v___x_952_);
v___x_954_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__7);
v___x_955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_953_);
lean_ctor_set(v___x_955_, 1, v___x_954_);
if (v_isShared_948_ == 0)
{
lean_ctor_set_tag(v___x_947_, 1);
lean_ctor_set(v___x_947_, 0, v___x_955_);
v___x_957_ = v___x_947_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v___x_955_);
v___x_957_ = v_reuseFailAlloc_967_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
lean_object* v___x_958_; 
lean_inc(v_mvarId_890_);
v___x_958_ = l_Lean_Meta_throwTacticEx___redArg(v___x_891_, v_mvarId_890_, v___x_957_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_dec_ref_known(v___x_958_, 1);
v___y_901_ = v___x_939_;
v___y_902_ = v_type_943_;
v___y_903_ = v_a_938_;
v___y_904_ = v___y_933_;
v___y_905_ = v___y_934_;
v___y_906_ = v___y_935_;
v___y_907_ = v___y_936_;
goto v___jp_900_;
}
else
{
lean_object* v_a_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_966_; 
lean_dec_ref(v_type_943_);
lean_dec(v_a_938_);
lean_dec_ref(v___y_933_);
lean_dec_ref(v_lctx_899_);
lean_dec(v_fvarId_892_);
lean_dec(v_mvarId_890_);
v_a_959_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_966_ == 0)
{
v___x_961_ = v___x_958_;
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_a_959_);
lean_dec(v___x_958_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_964_; 
if (v_isShared_962_ == 0)
{
v___x_964_ = v___x_961_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_a_959_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_976_; 
lean_dec(v_a_938_);
lean_dec_ref(v___y_933_);
lean_dec_ref(v_lctx_899_);
lean_dec(v_fvarId_892_);
lean_dec(v___x_891_);
lean_dec(v_mvarId_890_);
v_a_969_ = lean_ctor_get(v___x_941_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_976_ == 0)
{
v___x_971_ = v___x_941_;
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_941_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_974_; 
if (v_isShared_972_ == 0)
{
v___x_974_ = v___x_971_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_a_969_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
}
else
{
lean_object* v_a_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_984_; 
lean_dec(v_a_938_);
lean_dec_ref(v___y_933_);
lean_dec_ref(v_lctx_899_);
lean_dec(v_fvarId_892_);
lean_dec(v___x_891_);
lean_dec(v_mvarId_890_);
v_a_977_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_984_ == 0)
{
v___x_979_ = v___x_940_;
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_a_977_);
lean_dec(v___x_940_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_982_; 
if (v_isShared_980_ == 0)
{
v___x_982_ = v___x_979_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_a_977_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
}
else
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_992_; 
lean_dec_ref(v___y_933_);
lean_dec_ref(v_lctx_899_);
lean_dec(v_fvarId_892_);
lean_dec(v___x_891_);
lean_dec(v_mvarId_890_);
v_a_985_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_992_ == 0)
{
v___x_987_ = v___x_937_;
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_937_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_990_; 
if (v_isShared_988_ == 0)
{
v___x_990_ = v___x_987_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_a_985_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
}
else
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
lean_dec_ref(v___y_893_);
lean_dec(v_fvarId_892_);
lean_dec(v___x_891_);
lean_dec(v_mvarId_890_);
v_a_1010_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_898_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_898_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clear___lam__0___boxed(lean_object* v_mvarId_1018_, lean_object* v___x_1019_, lean_object* v_fvarId_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Lean_MVarId_clear___lam__0(v_mvarId_1018_, v___x_1019_, v_fvarId_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
lean_dec(v___y_1022_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clear(lean_object* v_mvarId_1027_, lean_object* v_fvarId_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_){
_start:
{
lean_object* v___x_1034_; lean_object* v___f_1035_; lean_object* v___x_1036_; 
v___x_1034_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_MVarId_clear_spec__1_spec__1_spec__5_spec__9___closed__1));
lean_inc(v_mvarId_1027_);
v___f_1035_ = lean_alloc_closure((void*)(l_Lean_MVarId_clear___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1035_, 0, v_mvarId_1027_);
lean_closure_set(v___f_1035_, 1, v___x_1034_);
lean_closure_set(v___f_1035_, 2, v_fvarId_1028_);
v___x_1036_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg(v_mvarId_1027_, v___f_1035_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clear___boxed(lean_object* v_mvarId_1037_, lean_object* v_fvarId_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Lean_MVarId_clear(v_mvarId_1037_, v_fvarId_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_);
lean_dec(v_a_1042_);
lean_dec_ref(v_a_1041_);
lean_dec(v_a_1040_);
lean_dec_ref(v_a_1039_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2(lean_object* v_mvarId_1045_, lean_object* v_val_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v___x_1052_; 
v___x_1052_ = l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___redArg(v_mvarId_1045_, v_val_1046_, v___y_1048_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2___boxed(lean_object* v_mvarId_1053_, lean_object* v_val_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2(v_mvarId_1053_, v_val_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3(lean_object* v_00_u03b2_1061_, lean_object* v_x_1062_, lean_object* v_x_1063_, lean_object* v_x_1064_){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3___redArg(v_x_1062_, v_x_1063_, v_x_1064_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9(lean_object* v_00_u03b2_1066_, lean_object* v_x_1067_, size_t v_x_1068_, size_t v_x_1069_, lean_object* v_x_1070_, lean_object* v_x_1071_){
_start:
{
lean_object* v___x_1072_; 
v___x_1072_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___redArg(v_x_1067_, v_x_1068_, v_x_1069_, v_x_1070_, v_x_1071_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9___boxed(lean_object* v_00_u03b2_1073_, lean_object* v_x_1074_, lean_object* v_x_1075_, lean_object* v_x_1076_, lean_object* v_x_1077_, lean_object* v_x_1078_){
_start:
{
size_t v_x_8884__boxed_1079_; size_t v_x_8885__boxed_1080_; lean_object* v_res_1081_; 
v_x_8884__boxed_1079_ = lean_unbox_usize(v_x_1075_);
lean_dec(v_x_1075_);
v_x_8885__boxed_1080_ = lean_unbox_usize(v_x_1076_);
lean_dec(v_x_1076_);
v_res_1081_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9(v_00_u03b2_1073_, v_x_1074_, v_x_8884__boxed_1079_, v_x_8885__boxed_1080_, v_x_1077_, v_x_1078_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13(lean_object* v_00_u03b2_1082_, lean_object* v_n_1083_, lean_object* v_k_1084_, lean_object* v_v_1085_){
_start:
{
lean_object* v___x_1086_; 
v___x_1086_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13___redArg(v_n_1083_, v_k_1084_, v_v_1085_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14(lean_object* v_00_u03b2_1087_, size_t v_depth_1088_, lean_object* v_keys_1089_, lean_object* v_vals_1090_, lean_object* v_heq_1091_, lean_object* v_i_1092_, lean_object* v_entries_1093_){
_start:
{
lean_object* v___x_1094_; 
v___x_1094_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___redArg(v_depth_1088_, v_keys_1089_, v_vals_1090_, v_i_1092_, v_entries_1093_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14___boxed(lean_object* v_00_u03b2_1095_, lean_object* v_depth_1096_, lean_object* v_keys_1097_, lean_object* v_vals_1098_, lean_object* v_heq_1099_, lean_object* v_i_1100_, lean_object* v_entries_1101_){
_start:
{
size_t v_depth_boxed_1102_; lean_object* v_res_1103_; 
v_depth_boxed_1102_ = lean_unbox_usize(v_depth_1096_);
lean_dec(v_depth_1096_);
v_res_1103_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__14(v_00_u03b2_1095_, v_depth_boxed_1102_, v_keys_1097_, v_vals_1098_, v_heq_1099_, v_i_1100_, v_entries_1101_);
lean_dec_ref(v_vals_1098_);
lean_dec_ref(v_keys_1097_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13_spec__14(lean_object* v_00_u03b2_1104_, lean_object* v_x_1105_, lean_object* v_x_1106_, lean_object* v_x_1107_, lean_object* v_x_1108_){
_start:
{
lean_object* v___x_1109_; 
v___x_1109_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_clear_spec__2_spec__3_spec__9_spec__13_spec__14___redArg(v_x_1105_, v_x_1106_, v_x_1107_, v_x_1108_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClear(lean_object* v_mvarId_1110_, lean_object* v_fvarId_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_){
_start:
{
lean_object* v___x_1117_; 
v___x_1117_ = l_Lean_Meta_saveState___redArg(v_a_1113_, v_a_1115_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v___x_1119_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_a_1118_);
lean_dec_ref_known(v___x_1117_, 1);
lean_inc(v_mvarId_1110_);
v___x_1119_ = l_Lean_MVarId_clear(v_mvarId_1110_, v_fvarId_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_dec(v_a_1118_);
lean_dec(v_mvarId_1110_);
return v___x_1119_;
}
else
{
lean_object* v_a_1120_; uint8_t v___x_1121_; 
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
v___x_1121_ = l_Lean_Exception_isInterrupt(v_a_1120_);
if (v___x_1121_ == 0)
{
uint8_t v___x_1122_; 
lean_inc(v_a_1120_);
v___x_1122_ = l_Lean_Exception_isRuntime(v_a_1120_);
if (v___x_1122_ == 0)
{
lean_object* v___x_1123_; 
lean_dec_ref_known(v___x_1119_, 1);
v___x_1123_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1118_, v_a_1113_, v_a_1115_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1130_; 
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1130_ == 0)
{
lean_object* v_unused_1131_; 
v_unused_1131_ = lean_ctor_get(v___x_1123_, 0);
lean_dec(v_unused_1131_);
v___x_1125_ = v___x_1123_;
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
else
{
lean_dec(v___x_1123_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1128_; 
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 0, v_mvarId_1110_);
v___x_1128_ = v___x_1125_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_mvarId_1110_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
else
{
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1139_; 
lean_dec(v_mvarId_1110_);
v_a_1132_ = lean_ctor_get(v___x_1123_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1134_ = v___x_1123_;
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1123_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1137_; 
if (v_isShared_1135_ == 0)
{
v___x_1137_ = v___x_1134_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_a_1132_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
else
{
lean_dec(v_a_1118_);
lean_dec(v_mvarId_1110_);
return v___x_1119_;
}
}
else
{
lean_dec(v_a_1118_);
lean_dec(v_mvarId_1110_);
return v___x_1119_;
}
}
}
else
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1147_; 
lean_dec(v_fvarId_1111_);
lean_dec(v_mvarId_1110_);
v_a_1140_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1142_ = v___x_1117_;
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1117_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1143_ == 0)
{
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1140_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClear___boxed(lean_object* v_mvarId_1148_, lean_object* v_fvarId_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Lean_MVarId_tryClear(v_mvarId_1148_, v_fvarId_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_);
lean_dec(v_a_1153_);
lean_dec_ref(v_a_1152_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0(lean_object* v_as_1156_, size_t v_i_1157_, size_t v_stop_1158_, lean_object* v_b_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
uint8_t v___x_1165_; 
v___x_1165_ = lean_usize_dec_eq(v_i_1157_, v_stop_1158_);
if (v___x_1165_ == 0)
{
size_t v___x_1166_; size_t v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1166_ = ((size_t)1ULL);
v___x_1167_ = lean_usize_sub(v_i_1157_, v___x_1166_);
v___x_1168_ = lean_array_uget_borrowed(v_as_1156_, v___x_1167_);
lean_inc(v___x_1168_);
v___x_1169_ = l_Lean_MVarId_tryClear(v_b_1159_, v___x_1168_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_object* v_a_1170_; 
v_a_1170_ = lean_ctor_get(v___x_1169_, 0);
lean_inc(v_a_1170_);
lean_dec_ref_known(v___x_1169_, 1);
v_i_1157_ = v___x_1167_;
v_b_1159_ = v_a_1170_;
goto _start;
}
else
{
return v___x_1169_;
}
}
else
{
lean_object* v___x_1172_; 
v___x_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1172_, 0, v_b_1159_);
return v___x_1172_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0___boxed(lean_object* v_as_1173_, lean_object* v_i_1174_, lean_object* v_stop_1175_, lean_object* v_b_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
size_t v_i_boxed_1182_; size_t v_stop_boxed_1183_; lean_object* v_res_1184_; 
v_i_boxed_1182_ = lean_unbox_usize(v_i_1174_);
lean_dec(v_i_1174_);
v_stop_boxed_1183_ = lean_unbox_usize(v_stop_1175_);
lean_dec(v_stop_1175_);
v_res_1184_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0(v_as_1173_, v_i_boxed_1182_, v_stop_boxed_1183_, v_b_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
lean_dec_ref(v_as_1173_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany(lean_object* v_mvarId_1185_, lean_object* v_fvarIds_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_){
_start:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; uint8_t v___x_1194_; 
v___x_1192_ = lean_array_get_size(v_fvarIds_1186_);
v___x_1193_ = lean_unsigned_to_nat(0u);
v___x_1194_ = lean_nat_dec_lt(v___x_1193_, v___x_1192_);
if (v___x_1194_ == 0)
{
lean_object* v___x_1195_; 
v___x_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1195_, 0, v_mvarId_1185_);
return v___x_1195_;
}
else
{
size_t v___x_1196_; size_t v___x_1197_; lean_object* v___x_1198_; 
v___x_1196_ = lean_usize_of_nat(v___x_1192_);
v___x_1197_ = ((size_t)0ULL);
v___x_1198_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_spec__0(v_fvarIds_1186_, v___x_1196_, v___x_1197_, v_mvarId_1185_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_);
return v___x_1198_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany___boxed(lean_object* v_mvarId_1199_, lean_object* v_fvarIds_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Lean_MVarId_tryClearMany(v_mvarId_1199_, v_fvarIds_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_);
lean_dec(v_a_1204_);
lean_dec_ref(v_a_1203_);
lean_dec(v_a_1202_);
lean_dec_ref(v_a_1201_);
lean_dec_ref(v_fvarIds_1200_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0(lean_object* v_as_1207_, size_t v_i_1208_, size_t v_stop_1209_, lean_object* v_b_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
uint8_t v___x_1216_; 
v___x_1216_ = lean_usize_dec_eq(v_i_1208_, v_stop_1209_);
if (v___x_1216_ == 0)
{
lean_object* v_fst_1217_; lean_object* v_snd_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1243_; 
v_fst_1217_ = lean_ctor_get(v_b_1210_, 0);
v_snd_1218_ = lean_ctor_get(v_b_1210_, 1);
v_isSharedCheck_1243_ = !lean_is_exclusive(v_b_1210_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1220_ = v_b_1210_;
v_isShared_1221_ = v_isSharedCheck_1243_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_snd_1218_);
lean_inc(v_fst_1217_);
lean_dec(v_b_1210_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1243_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
size_t v___x_1222_; size_t v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1222_ = ((size_t)1ULL);
v___x_1223_ = lean_usize_sub(v_i_1208_, v___x_1222_);
v___x_1224_ = lean_array_uget_borrowed(v_as_1207_, v___x_1223_);
lean_inc(v___x_1224_);
lean_inc(v_fst_1217_);
v___x_1225_ = l_Lean_MVarId_tryClear(v_fst_1217_, v___x_1224_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v_a_1226_; lean_object* v___y_1228_; uint8_t v___x_1233_; 
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_a_1226_);
lean_dec_ref_known(v___x_1225_, 1);
v___x_1233_ = l_Lean_instBEqMVarId_beq(v_fst_1217_, v_a_1226_);
lean_dec(v_fst_1217_);
if (v___x_1233_ == 0)
{
lean_object* v___x_1234_; 
lean_inc(v___x_1224_);
v___x_1234_ = lean_array_push(v_snd_1218_, v___x_1224_);
v___y_1228_ = v___x_1234_;
goto v___jp_1227_;
}
else
{
v___y_1228_ = v_snd_1218_;
goto v___jp_1227_;
}
v___jp_1227_:
{
lean_object* v___x_1230_; 
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 1, v___y_1228_);
lean_ctor_set(v___x_1220_, 0, v_a_1226_);
v___x_1230_ = v___x_1220_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1226_);
lean_ctor_set(v_reuseFailAlloc_1232_, 1, v___y_1228_);
v___x_1230_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
v_i_1208_ = v___x_1223_;
v_b_1210_ = v___x_1230_;
goto _start;
}
}
}
else
{
lean_object* v_a_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1242_; 
lean_del_object(v___x_1220_);
lean_dec(v_snd_1218_);
lean_dec(v_fst_1217_);
v_a_1235_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1237_ = v___x_1225_;
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_dec(v___x_1225_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1240_; 
if (v_isShared_1238_ == 0)
{
v___x_1240_ = v___x_1237_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_a_1235_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
}
else
{
lean_object* v___x_1244_; 
v___x_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1244_, 0, v_b_1210_);
return v___x_1244_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0___boxed(lean_object* v_as_1245_, lean_object* v_i_1246_, lean_object* v_stop_1247_, lean_object* v_b_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
size_t v_i_boxed_1254_; size_t v_stop_boxed_1255_; lean_object* v_res_1256_; 
v_i_boxed_1254_ = lean_unbox_usize(v_i_1246_);
lean_dec(v_i_1246_);
v_stop_boxed_1255_ = lean_unbox_usize(v_stop_1247_);
lean_dec(v_stop_1247_);
v_res_1256_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0(v_as_1245_, v_i_boxed_1254_, v_stop_boxed_1255_, v_b_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec_ref(v_as_1245_);
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany_x27___lam__0(lean_object* v_fvarIds_1257_, lean_object* v_goal_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v_lctx_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; uint8_t v___x_1270_; 
v_lctx_1264_ = lean_ctor_get(v___y_1259_, 2);
v___x_1265_ = l_Lean_LocalContext_sortFVarsByContextOrder(v_lctx_1264_, v_fvarIds_1257_);
v___x_1266_ = lean_array_get_size(v___x_1265_);
v___x_1267_ = lean_mk_empty_array_with_capacity(v___x_1266_);
v___x_1268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1268_, 0, v_goal_1258_);
lean_ctor_set(v___x_1268_, 1, v___x_1267_);
v___x_1269_ = lean_unsigned_to_nat(0u);
v___x_1270_ = lean_nat_dec_lt(v___x_1269_, v___x_1266_);
if (v___x_1270_ == 0)
{
lean_object* v___x_1271_; 
lean_dec_ref(v___x_1265_);
v___x_1271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1268_);
return v___x_1271_;
}
else
{
size_t v___x_1272_; size_t v___x_1273_; lean_object* v___x_1274_; 
v___x_1272_ = lean_usize_of_nat(v___x_1266_);
v___x_1273_ = ((size_t)0ULL);
v___x_1274_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_MVarId_tryClearMany_x27_spec__0(v___x_1265_, v___x_1272_, v___x_1273_, v___x_1268_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
lean_dec_ref(v___x_1265_);
return v___x_1274_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany_x27___lam__0___boxed(lean_object* v_fvarIds_1275_, lean_object* v_goal_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_){
_start:
{
lean_object* v_res_1282_; 
v_res_1282_ = l_Lean_MVarId_tryClearMany_x27___lam__0(v_fvarIds_1275_, v_goal_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany_x27(lean_object* v_goal_1283_, lean_object* v_fvarIds_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_){
_start:
{
lean_object* v___f_1290_; lean_object* v___x_1291_; 
lean_inc(v_goal_1283_);
v___f_1290_ = lean_alloc_closure((void*)(l_Lean_MVarId_tryClearMany_x27___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1290_, 0, v_fvarIds_1284_);
lean_closure_set(v___f_1290_, 1, v_goal_1283_);
v___x_1291_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_clear_spec__4___redArg(v_goal_1283_, v___f_1290_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_tryClearMany_x27___boxed(lean_object* v_goal_1292_, lean_object* v_fvarIds_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Lean_MVarId_tryClearMany_x27(v_goal_1292_, v_fvarIds_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_);
lean_dec(v_a_1297_);
lean_dec_ref(v_a_1296_);
lean_dec(v_a_1295_);
lean_dec_ref(v_a_1294_);
return v_res_1299_;
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
