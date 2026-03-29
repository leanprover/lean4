// Lean compiler output
// Module: Lean.Meta.Tactic.Replace
// Imports: public import Lean.Elab.InfoTree.Main public import Lean.Meta.AppBuilder public import Lean.Meta.MatchUtil public import Lean.Meta.Tactic.Assert
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
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_matchEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_equal(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedTypeHint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Expr_letValue_x21(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letName_x21(lean_object*);
lean_object* l_Lean_Expr_letType_x21(lean_object*);
lean_object* l_Lean_Expr_letBody_x21(lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLet(lean_object*);
lean_object* l_Lean_MVarId_revertFrom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_index(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_get_x21(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalInstancesImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_setType(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_set___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_revert(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_mkEqMP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_MVarId_assertAfter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_replaceTargetEq___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_MVarId_replaceTargetEq___lam__0___closed__0 = (const lean_object*)&l_Lean_MVarId_replaceTargetEq___lam__0___closed__0_value;
static const lean_string_object l_Lean_MVarId_replaceTargetEq___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "mpr"};
static const lean_object* l_Lean_MVarId_replaceTargetEq___lam__0___closed__1 = (const lean_object*)&l_Lean_MVarId_replaceTargetEq___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_MVarId_replaceTargetEq___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_replaceTargetEq___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_MVarId_replaceTargetEq___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MVarId_replaceTargetEq___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_MVarId_replaceTargetEq___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(146, 109, 21, 40, 70, 113, 251, 6)}};
static const lean_object* l_Lean_MVarId_replaceTargetEq___lam__0___closed__2 = (const lean_object*)&l_Lean_MVarId_replaceTargetEq___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetEq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetEq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_replaceTargetEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "replaceTarget"};
static const lean_object* l_Lean_MVarId_replaceTargetEq___closed__0 = (const lean_object*)&l_Lean_MVarId_replaceTargetEq___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_replaceTargetEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_replaceTargetEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 169, 19, 111, 46, 176, 140, 111)}};
static const lean_object* l_Lean_MVarId_replaceTargetEq___closed__1 = (const lean_object*)&l_Lean_MVarId_replaceTargetEq___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_replaceTargetDefEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "change"};
static const lean_object* l_Lean_MVarId_replaceTargetDefEq___closed__0 = (const lean_object*)&l_Lean_MVarId_replaceTargetDefEq___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_replaceTargetDefEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_replaceTargetDefEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(125, 120, 133, 160, 129, 235, 229, 190)}};
static const lean_object* l_Lean_MVarId_replaceTargetDefEq___closed__1 = (const lean_object*)&l_Lean_MVarId_replaceTargetDefEq___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__1_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__1_spec__4___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___closed__1;
static const lean_closure_object l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__1_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2_spec__2_spec__4___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2_spec__2_spec__4(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_change___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "given type"};
static const lean_object* l_Lean_MVarId_change___lam__0___closed__0 = (const lean_object*)&l_Lean_MVarId_change___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_MVarId_change___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_change___lam__0___closed__1;
static const lean_string_object l_Lean_MVarId_change___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "\nis not definitionally equal to"};
static const lean_object* l_Lean_MVarId_change___lam__0___closed__2 = (const lean_object*)&l_Lean_MVarId_change___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_MVarId_change___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_change___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_MVarId_change___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_change___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_change(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_change___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__0;
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_withReverted_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_withReverted_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withReverted___redArg___lam__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withReverted___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_MVarId_withReverted___redArg___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l_Lean_MVarId_withReverted___redArg___boxed__const__1 = (const lean_object*)&l_Lean_MVarId_withReverted___redArg___boxed__const__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_withReverted___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withReverted___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withReverted(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withReverted___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withRevertedFrom___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withRevertedFrom___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withRevertedFrom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withRevertedFrom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_changeLocalDecl_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_changeLocalDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_changeLocalDecl___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "unexpected auxiliary target"};
static const lean_object* l_Lean_MVarId_changeLocalDecl___lam__2___closed__0 = (const lean_object*)&l_Lean_MVarId_changeLocalDecl___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_changeLocalDecl___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MVarId_changeLocalDecl___lam__2___closed__0_value)}};
static const lean_object* l_Lean_MVarId_changeLocalDecl___lam__2___closed__1 = (const lean_object*)&l_Lean_MVarId_changeLocalDecl___lam__2___closed__1_value;
static lean_once_cell_t l_Lean_MVarId_changeLocalDecl___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_changeLocalDecl___lam__2___closed__2;
static lean_once_cell_t l_Lean_MVarId_changeLocalDecl___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_changeLocalDecl___lam__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lam__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_changeLocalDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "changeLocalDecl"};
static const lean_object* l_Lean_MVarId_changeLocalDecl___closed__0 = (const lean_object*)&l_Lean_MVarId_changeLocalDecl___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_changeLocalDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_changeLocalDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(138, 31, 202, 231, 182, 71, 213, 201)}};
static const lean_object* l_Lean_MVarId_changeLocalDecl___closed__1 = (const lean_object*)&l_Lean_MVarId_changeLocalDecl___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTarget___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTarget___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_modifyTarget___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "modifyTarget"};
static const lean_object* l_Lean_MVarId_modifyTarget___closed__0 = (const lean_object*)&l_Lean_MVarId_modifyTarget___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_modifyTarget___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_modifyTarget___closed__0_value),LEAN_SCALAR_PTR_LITERAL(191, 72, 230, 156, 164, 199, 29, 209)}};
static const lean_object* l_Lean_MVarId_modifyTarget___closed__1 = (const lean_object*)&l_Lean_MVarId_modifyTarget___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "modifyTargetEqLHS"};
static const lean_object* l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__0 = (const lean_object*)&l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(210, 21, 181, 124, 160, 155, 6, 47)}};
static const lean_object* l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__1 = (const lean_object*)&l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__1_value;
static const lean_string_object l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "equality expected"};
static const lean_object* l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__2 = (const lean_object*)&l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTargetEqLHS___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTargetEqLHS___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTargetEqLHS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTargetEqLHS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_clearValue___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "cannot clear "};
static const lean_object* l_Lean_MVarId_clearValue___lam__0___closed__0 = (const lean_object*)&l_Lean_MVarId_clearValue___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_MVarId_clearValue___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_clearValue___lam__0___closed__1;
static const lean_string_object l_Lean_MVarId_clearValue___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = ", the resulting context is not type correct."};
static const lean_object* l_Lean_MVarId_clearValue___lam__0___closed__2 = (const lean_object*)&l_Lean_MVarId_clearValue___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_MVarId_clearValue___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_clearValue___lam__0___closed__3;
static const lean_string_object l_Lean_MVarId_clearValue___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "hypothesis `"};
static const lean_object* l_Lean_MVarId_clearValue___lam__0___closed__4 = (const lean_object*)&l_Lean_MVarId_clearValue___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_MVarId_clearValue___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_clearValue___lam__0___closed__5;
static const lean_string_object l_Lean_MVarId_clearValue___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "` is not a local definition."};
static const lean_object* l_Lean_MVarId_clearValue___lam__0___closed__6 = (const lean_object*)&l_Lean_MVarId_clearValue___lam__0___closed__6_value;
static lean_once_cell_t l_Lean_MVarId_clearValue___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_clearValue___lam__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_MVarId_clearValue___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_clearValue___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_clearValue___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_clearValue___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_clearValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "clear_value"};
static const lean_object* l_Lean_MVarId_clearValue___closed__0 = (const lean_object*)&l_Lean_MVarId_clearValue___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_clearValue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_clearValue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(203, 208, 55, 120, 161, 199, 100, 120)}};
static const lean_object* l_Lean_MVarId_clearValue___closed__1 = (const lean_object*)&l_Lean_MVarId_clearValue___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_clearValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_clearValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(lean_object* v_mvarId_1_, lean_object* v_x_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1_, v_x_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_);
if (lean_obj_tag(v___x_8_) == 0)
{
lean_object* v_a_9_; lean_object* v___x_11_; uint8_t v_isShared_12_; uint8_t v_isSharedCheck_16_; 
v_a_9_ = lean_ctor_get(v___x_8_, 0);
v_isSharedCheck_16_ = !lean_is_exclusive(v___x_8_);
if (v_isSharedCheck_16_ == 0)
{
v___x_11_ = v___x_8_;
v_isShared_12_ = v_isSharedCheck_16_;
goto v_resetjp_10_;
}
else
{
lean_inc(v_a_9_);
lean_dec(v___x_8_);
v___x_11_ = lean_box(0);
v_isShared_12_ = v_isSharedCheck_16_;
goto v_resetjp_10_;
}
v_resetjp_10_:
{
lean_object* v___x_14_; 
if (v_isShared_12_ == 0)
{
v___x_14_ = v___x_11_;
goto v_reusejp_13_;
}
else
{
lean_object* v_reuseFailAlloc_15_; 
v_reuseFailAlloc_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_15_, 0, v_a_9_);
v___x_14_ = v_reuseFailAlloc_15_;
goto v_reusejp_13_;
}
v_reusejp_13_:
{
return v___x_14_;
}
}
}
else
{
lean_object* v_a_17_; lean_object* v___x_19_; uint8_t v_isShared_20_; uint8_t v_isSharedCheck_24_; 
v_a_17_ = lean_ctor_get(v___x_8_, 0);
v_isSharedCheck_24_ = !lean_is_exclusive(v___x_8_);
if (v_isSharedCheck_24_ == 0)
{
v___x_19_ = v___x_8_;
v_isShared_20_ = v_isSharedCheck_24_;
goto v_resetjp_18_;
}
else
{
lean_inc(v_a_17_);
lean_dec(v___x_8_);
v___x_19_ = lean_box(0);
v_isShared_20_ = v_isSharedCheck_24_;
goto v_resetjp_18_;
}
v_resetjp_18_:
{
lean_object* v___x_22_; 
if (v_isShared_20_ == 0)
{
v___x_22_ = v___x_19_;
goto v_reusejp_21_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v_a_17_);
v___x_22_ = v_reuseFailAlloc_23_;
goto v_reusejp_21_;
}
v_reusejp_21_:
{
return v___x_22_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg___boxed(lean_object* v_mvarId_25_, lean_object* v_x_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_25_, v_x_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_);
lean_dec(v___y_30_);
lean_dec_ref(v___y_29_);
lean_dec(v___y_28_);
lean_dec_ref(v___y_27_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1(lean_object* v_00_u03b1_33_, lean_object* v_mvarId_34_, lean_object* v_x_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_34_, v_x_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___boxed(lean_object* v_00_u03b1_42_, lean_object* v_mvarId_43_, lean_object* v_x_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1(v_00_u03b1_42_, v_mvarId_43_, v_x_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_);
lean_dec(v___y_48_);
lean_dec_ref(v___y_47_);
lean_dec(v___y_46_);
lean_dec_ref(v___y_45_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(lean_object* v_x_51_, lean_object* v_x_52_, lean_object* v_x_53_, lean_object* v_x_54_){
_start:
{
lean_object* v_ks_55_; lean_object* v_vs_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_80_; 
v_ks_55_ = lean_ctor_get(v_x_51_, 0);
v_vs_56_ = lean_ctor_get(v_x_51_, 1);
v_isSharedCheck_80_ = !lean_is_exclusive(v_x_51_);
if (v_isSharedCheck_80_ == 0)
{
v___x_58_ = v_x_51_;
v_isShared_59_ = v_isSharedCheck_80_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_vs_56_);
lean_inc(v_ks_55_);
lean_dec(v_x_51_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_80_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v___x_60_; uint8_t v___x_61_; 
v___x_60_ = lean_array_get_size(v_ks_55_);
v___x_61_ = lean_nat_dec_lt(v_x_52_, v___x_60_);
if (v___x_61_ == 0)
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_65_; 
lean_dec(v_x_52_);
v___x_62_ = lean_array_push(v_ks_55_, v_x_53_);
v___x_63_ = lean_array_push(v_vs_56_, v_x_54_);
if (v_isShared_59_ == 0)
{
lean_ctor_set(v___x_58_, 1, v___x_63_);
lean_ctor_set(v___x_58_, 0, v___x_62_);
v___x_65_ = v___x_58_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v___x_62_);
lean_ctor_set(v_reuseFailAlloc_66_, 1, v___x_63_);
v___x_65_ = v_reuseFailAlloc_66_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
return v___x_65_;
}
}
else
{
lean_object* v_k_x27_67_; uint8_t v___x_68_; 
v_k_x27_67_ = lean_array_fget_borrowed(v_ks_55_, v_x_52_);
v___x_68_ = l_Lean_instBEqMVarId_beq(v_x_53_, v_k_x27_67_);
if (v___x_68_ == 0)
{
lean_object* v___x_70_; 
if (v_isShared_59_ == 0)
{
v___x_70_ = v___x_58_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v_ks_55_);
lean_ctor_set(v_reuseFailAlloc_74_, 1, v_vs_56_);
v___x_70_ = v_reuseFailAlloc_74_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = lean_unsigned_to_nat(1u);
v___x_72_ = lean_nat_add(v_x_52_, v___x_71_);
lean_dec(v_x_52_);
v_x_51_ = v___x_70_;
v_x_52_ = v___x_72_;
goto _start;
}
}
else
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_78_; 
v___x_75_ = lean_array_fset(v_ks_55_, v_x_52_, v_x_53_);
v___x_76_ = lean_array_fset(v_vs_56_, v_x_52_, v_x_54_);
lean_dec(v_x_52_);
if (v_isShared_59_ == 0)
{
lean_ctor_set(v___x_58_, 1, v___x_76_);
lean_ctor_set(v___x_58_, 0, v___x_75_);
v___x_78_ = v___x_58_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v___x_75_);
lean_ctor_set(v_reuseFailAlloc_79_, 1, v___x_76_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_n_81_, lean_object* v_k_82_, lean_object* v_v_83_){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_84_ = lean_unsigned_to_nat(0u);
v___x_85_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_n_81_, v___x_84_, v_k_82_, v_v_83_);
return v___x_85_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
size_t v___x_86_; size_t v___x_87_; size_t v___x_88_; 
v___x_86_ = ((size_t)5ULL);
v___x_87_ = ((size_t)1ULL);
v___x_88_ = lean_usize_shift_left(v___x_87_, v___x_86_);
return v___x_88_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_89_; size_t v___x_90_; size_t v___x_91_; 
v___x_89_ = ((size_t)1ULL);
v___x_90_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_91_ = lean_usize_sub(v___x_90_, v___x_89_);
return v___x_91_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg(lean_object* v_x_93_, size_t v_x_94_, size_t v_x_95_, lean_object* v_x_96_, lean_object* v_x_97_){
_start:
{
if (lean_obj_tag(v_x_93_) == 0)
{
lean_object* v_es_98_; size_t v___x_99_; size_t v___x_100_; size_t v___x_101_; size_t v___x_102_; lean_object* v_j_103_; lean_object* v___x_104_; uint8_t v___x_105_; 
v_es_98_ = lean_ctor_get(v_x_93_, 0);
v___x_99_ = ((size_t)5ULL);
v___x_100_ = ((size_t)1ULL);
v___x_101_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_102_ = lean_usize_land(v_x_94_, v___x_101_);
v_j_103_ = lean_usize_to_nat(v___x_102_);
v___x_104_ = lean_array_get_size(v_es_98_);
v___x_105_ = lean_nat_dec_lt(v_j_103_, v___x_104_);
if (v___x_105_ == 0)
{
lean_dec(v_j_103_);
lean_dec(v_x_97_);
lean_dec(v_x_96_);
return v_x_93_;
}
else
{
lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_142_; 
lean_inc_ref(v_es_98_);
v_isSharedCheck_142_ = !lean_is_exclusive(v_x_93_);
if (v_isSharedCheck_142_ == 0)
{
lean_object* v_unused_143_; 
v_unused_143_ = lean_ctor_get(v_x_93_, 0);
lean_dec(v_unused_143_);
v___x_107_ = v_x_93_;
v_isShared_108_ = v_isSharedCheck_142_;
goto v_resetjp_106_;
}
else
{
lean_dec(v_x_93_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_142_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v_v_109_; lean_object* v___x_110_; lean_object* v_xs_x27_111_; lean_object* v___y_113_; 
v_v_109_ = lean_array_fget(v_es_98_, v_j_103_);
v___x_110_ = lean_box(0);
v_xs_x27_111_ = lean_array_fset(v_es_98_, v_j_103_, v___x_110_);
switch(lean_obj_tag(v_v_109_))
{
case 0:
{
lean_object* v_key_118_; lean_object* v_val_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_129_; 
v_key_118_ = lean_ctor_get(v_v_109_, 0);
v_val_119_ = lean_ctor_get(v_v_109_, 1);
v_isSharedCheck_129_ = !lean_is_exclusive(v_v_109_);
if (v_isSharedCheck_129_ == 0)
{
v___x_121_ = v_v_109_;
v_isShared_122_ = v_isSharedCheck_129_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_val_119_);
lean_inc(v_key_118_);
lean_dec(v_v_109_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_129_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
uint8_t v___x_123_; 
v___x_123_ = l_Lean_instBEqMVarId_beq(v_x_96_, v_key_118_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; lean_object* v___x_125_; 
lean_del_object(v___x_121_);
v___x_124_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_118_, v_val_119_, v_x_96_, v_x_97_);
v___x_125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_125_, 0, v___x_124_);
v___y_113_ = v___x_125_;
goto v___jp_112_;
}
else
{
lean_object* v___x_127_; 
lean_dec(v_val_119_);
lean_dec(v_key_118_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 1, v_x_97_);
lean_ctor_set(v___x_121_, 0, v_x_96_);
v___x_127_ = v___x_121_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_x_96_);
lean_ctor_set(v_reuseFailAlloc_128_, 1, v_x_97_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
v___y_113_ = v___x_127_;
goto v___jp_112_;
}
}
}
}
case 1:
{
lean_object* v_node_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_140_; 
v_node_130_ = lean_ctor_get(v_v_109_, 0);
v_isSharedCheck_140_ = !lean_is_exclusive(v_v_109_);
if (v_isSharedCheck_140_ == 0)
{
v___x_132_ = v_v_109_;
v_isShared_133_ = v_isSharedCheck_140_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_node_130_);
lean_dec(v_v_109_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_140_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
size_t v___x_134_; size_t v___x_135_; lean_object* v___x_136_; lean_object* v___x_138_; 
v___x_134_ = lean_usize_shift_right(v_x_94_, v___x_99_);
v___x_135_ = lean_usize_add(v_x_95_, v___x_100_);
v___x_136_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg(v_node_130_, v___x_134_, v___x_135_, v_x_96_, v_x_97_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 0, v___x_136_);
v___x_138_ = v___x_132_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v___x_136_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
v___y_113_ = v___x_138_;
goto v___jp_112_;
}
}
}
default: 
{
lean_object* v___x_141_; 
v___x_141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_141_, 0, v_x_96_);
lean_ctor_set(v___x_141_, 1, v_x_97_);
v___y_113_ = v___x_141_;
goto v___jp_112_;
}
}
v___jp_112_:
{
lean_object* v___x_114_; lean_object* v___x_116_; 
v___x_114_ = lean_array_fset(v_xs_x27_111_, v_j_103_, v___y_113_);
lean_dec(v_j_103_);
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 0, v___x_114_);
v___x_116_ = v___x_107_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v___x_114_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
}
}
}
else
{
lean_object* v_ks_144_; lean_object* v_vs_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_165_; 
v_ks_144_ = lean_ctor_get(v_x_93_, 0);
v_vs_145_ = lean_ctor_get(v_x_93_, 1);
v_isSharedCheck_165_ = !lean_is_exclusive(v_x_93_);
if (v_isSharedCheck_165_ == 0)
{
v___x_147_ = v_x_93_;
v_isShared_148_ = v_isSharedCheck_165_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_vs_145_);
lean_inc(v_ks_144_);
lean_dec(v_x_93_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_165_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_150_; 
if (v_isShared_148_ == 0)
{
v___x_150_ = v___x_147_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_ks_144_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v_vs_145_);
v___x_150_ = v_reuseFailAlloc_164_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
lean_object* v_newNode_151_; uint8_t v___y_153_; size_t v___x_159_; uint8_t v___x_160_; 
v_newNode_151_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3___redArg(v___x_150_, v_x_96_, v_x_97_);
v___x_159_ = ((size_t)7ULL);
v___x_160_ = lean_usize_dec_le(v___x_159_, v_x_95_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; 
v___x_161_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_151_);
v___x_162_ = lean_unsigned_to_nat(4u);
v___x_163_ = lean_nat_dec_lt(v___x_161_, v___x_162_);
lean_dec(v___x_161_);
v___y_153_ = v___x_163_;
goto v___jp_152_;
}
else
{
v___y_153_ = v___x_160_;
goto v___jp_152_;
}
v___jp_152_:
{
if (v___y_153_ == 0)
{
lean_object* v_ks_154_; lean_object* v_vs_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v_ks_154_ = lean_ctor_get(v_newNode_151_, 0);
lean_inc_ref(v_ks_154_);
v_vs_155_ = lean_ctor_get(v_newNode_151_, 1);
lean_inc_ref(v_vs_155_);
lean_dec_ref(v_newNode_151_);
v___x_156_ = lean_unsigned_to_nat(0u);
v___x_157_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__2);
v___x_158_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4___redArg(v_x_95_, v_ks_154_, v_vs_155_, v___x_156_, v___x_157_);
lean_dec_ref(v_vs_155_);
lean_dec_ref(v_ks_154_);
return v___x_158_;
}
else
{
return v_newNode_151_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4___redArg(size_t v_depth_166_, lean_object* v_keys_167_, lean_object* v_vals_168_, lean_object* v_i_169_, lean_object* v_entries_170_){
_start:
{
lean_object* v___x_171_; uint8_t v___x_172_; 
v___x_171_ = lean_array_get_size(v_keys_167_);
v___x_172_ = lean_nat_dec_lt(v_i_169_, v___x_171_);
if (v___x_172_ == 0)
{
lean_dec(v_i_169_);
return v_entries_170_;
}
else
{
lean_object* v_k_173_; lean_object* v_v_174_; uint64_t v___x_175_; size_t v_h_176_; size_t v___x_177_; lean_object* v___x_178_; size_t v___x_179_; size_t v___x_180_; size_t v___x_181_; size_t v_h_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v_k_173_ = lean_array_fget_borrowed(v_keys_167_, v_i_169_);
v_v_174_ = lean_array_fget_borrowed(v_vals_168_, v_i_169_);
v___x_175_ = l_Lean_instHashableMVarId_hash(v_k_173_);
v_h_176_ = lean_uint64_to_usize(v___x_175_);
v___x_177_ = ((size_t)5ULL);
v___x_178_ = lean_unsigned_to_nat(1u);
v___x_179_ = ((size_t)1ULL);
v___x_180_ = lean_usize_sub(v_depth_166_, v___x_179_);
v___x_181_ = lean_usize_mul(v___x_177_, v___x_180_);
v_h_182_ = lean_usize_shift_right(v_h_176_, v___x_181_);
v___x_183_ = lean_nat_add(v_i_169_, v___x_178_);
lean_dec(v_i_169_);
lean_inc(v_v_174_);
lean_inc(v_k_173_);
v___x_184_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg(v_entries_170_, v_h_182_, v_depth_166_, v_k_173_, v_v_174_);
v_i_169_ = v___x_183_;
v_entries_170_ = v___x_184_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_depth_186_, lean_object* v_keys_187_, lean_object* v_vals_188_, lean_object* v_i_189_, lean_object* v_entries_190_){
_start:
{
size_t v_depth_boxed_191_; lean_object* v_res_192_; 
v_depth_boxed_191_ = lean_unbox_usize(v_depth_186_);
lean_dec(v_depth_186_);
v_res_192_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_boxed_191_, v_keys_187_, v_vals_188_, v_i_189_, v_entries_190_);
lean_dec_ref(v_vals_188_);
lean_dec_ref(v_keys_187_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_193_, lean_object* v_x_194_, lean_object* v_x_195_, lean_object* v_x_196_, lean_object* v_x_197_){
_start:
{
size_t v_x_1694__boxed_198_; size_t v_x_1695__boxed_199_; lean_object* v_res_200_; 
v_x_1694__boxed_198_ = lean_unbox_usize(v_x_194_);
lean_dec(v_x_194_);
v_x_1695__boxed_199_ = lean_unbox_usize(v_x_195_);
lean_dec(v_x_195_);
v_res_200_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg(v_x_193_, v_x_1694__boxed_198_, v_x_1695__boxed_199_, v_x_196_, v_x_197_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0___redArg(lean_object* v_x_201_, lean_object* v_x_202_, lean_object* v_x_203_){
_start:
{
uint64_t v___x_204_; size_t v___x_205_; size_t v___x_206_; lean_object* v___x_207_; 
v___x_204_ = l_Lean_instHashableMVarId_hash(v_x_202_);
v___x_205_ = lean_uint64_to_usize(v___x_204_);
v___x_206_ = ((size_t)1ULL);
v___x_207_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg(v_x_201_, v___x_205_, v___x_206_, v_x_202_, v_x_203_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg(lean_object* v_mvarId_208_, lean_object* v_val_209_, lean_object* v___y_210_){
_start:
{
lean_object* v___x_212_; lean_object* v_mctx_213_; lean_object* v_cache_214_; lean_object* v_zetaDeltaFVarIds_215_; lean_object* v_postponed_216_; lean_object* v_diag_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_244_; 
v___x_212_ = lean_st_ref_take(v___y_210_);
v_mctx_213_ = lean_ctor_get(v___x_212_, 0);
v_cache_214_ = lean_ctor_get(v___x_212_, 1);
v_zetaDeltaFVarIds_215_ = lean_ctor_get(v___x_212_, 2);
v_postponed_216_ = lean_ctor_get(v___x_212_, 3);
v_diag_217_ = lean_ctor_get(v___x_212_, 4);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_244_ == 0)
{
v___x_219_ = v___x_212_;
v_isShared_220_ = v_isSharedCheck_244_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_diag_217_);
lean_inc(v_postponed_216_);
lean_inc(v_zetaDeltaFVarIds_215_);
lean_inc(v_cache_214_);
lean_inc(v_mctx_213_);
lean_dec(v___x_212_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_244_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v_depth_221_; lean_object* v_levelAssignDepth_222_; lean_object* v_mvarCounter_223_; lean_object* v_lDepth_224_; lean_object* v_decls_225_; lean_object* v_userNames_226_; lean_object* v_lAssignment_227_; lean_object* v_eAssignment_228_; lean_object* v_dAssignment_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_243_; 
v_depth_221_ = lean_ctor_get(v_mctx_213_, 0);
v_levelAssignDepth_222_ = lean_ctor_get(v_mctx_213_, 1);
v_mvarCounter_223_ = lean_ctor_get(v_mctx_213_, 2);
v_lDepth_224_ = lean_ctor_get(v_mctx_213_, 3);
v_decls_225_ = lean_ctor_get(v_mctx_213_, 4);
v_userNames_226_ = lean_ctor_get(v_mctx_213_, 5);
v_lAssignment_227_ = lean_ctor_get(v_mctx_213_, 6);
v_eAssignment_228_ = lean_ctor_get(v_mctx_213_, 7);
v_dAssignment_229_ = lean_ctor_get(v_mctx_213_, 8);
v_isSharedCheck_243_ = !lean_is_exclusive(v_mctx_213_);
if (v_isSharedCheck_243_ == 0)
{
v___x_231_ = v_mctx_213_;
v_isShared_232_ = v_isSharedCheck_243_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_dAssignment_229_);
lean_inc(v_eAssignment_228_);
lean_inc(v_lAssignment_227_);
lean_inc(v_userNames_226_);
lean_inc(v_decls_225_);
lean_inc(v_lDepth_224_);
lean_inc(v_mvarCounter_223_);
lean_inc(v_levelAssignDepth_222_);
lean_inc(v_depth_221_);
lean_dec(v_mctx_213_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_243_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_233_; lean_object* v___x_235_; 
v___x_233_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0___redArg(v_eAssignment_228_, v_mvarId_208_, v_val_209_);
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 7, v___x_233_);
v___x_235_ = v___x_231_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_depth_221_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v_levelAssignDepth_222_);
lean_ctor_set(v_reuseFailAlloc_242_, 2, v_mvarCounter_223_);
lean_ctor_set(v_reuseFailAlloc_242_, 3, v_lDepth_224_);
lean_ctor_set(v_reuseFailAlloc_242_, 4, v_decls_225_);
lean_ctor_set(v_reuseFailAlloc_242_, 5, v_userNames_226_);
lean_ctor_set(v_reuseFailAlloc_242_, 6, v_lAssignment_227_);
lean_ctor_set(v_reuseFailAlloc_242_, 7, v___x_233_);
lean_ctor_set(v_reuseFailAlloc_242_, 8, v_dAssignment_229_);
v___x_235_ = v_reuseFailAlloc_242_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
lean_object* v___x_237_; 
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 0, v___x_235_);
v___x_237_ = v___x_219_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_235_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v_cache_214_);
lean_ctor_set(v_reuseFailAlloc_241_, 2, v_zetaDeltaFVarIds_215_);
lean_ctor_set(v_reuseFailAlloc_241_, 3, v_postponed_216_);
lean_ctor_set(v_reuseFailAlloc_241_, 4, v_diag_217_);
v___x_237_ = v_reuseFailAlloc_241_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_238_ = lean_st_ref_set(v___y_210_, v___x_237_);
v___x_239_ = lean_box(0);
v___x_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
return v___x_240_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg___boxed(lean_object* v_mvarId_245_, lean_object* v_val_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg(v_mvarId_245_, v_val_246_, v___y_247_);
lean_dec(v___y_247_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetEq___lam__0(lean_object* v_mvarId_255_, lean_object* v___x_256_, lean_object* v_targetNew_257_, lean_object* v_eqProof_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_){
_start:
{
lean_object* v___x_264_; 
lean_inc(v_mvarId_255_);
v___x_264_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_255_, v___x_256_, v___y_259_, v___y_260_, v___y_261_, v___y_262_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v___x_265_; 
lean_dec_ref(v___x_264_);
lean_inc(v_mvarId_255_);
v___x_265_ = l_Lean_MVarId_getTag(v_mvarId_255_, v___y_259_, v___y_260_, v___y_261_, v___y_262_);
if (lean_obj_tag(v___x_265_) == 0)
{
lean_object* v_a_266_; lean_object* v___x_267_; 
v_a_266_ = lean_ctor_get(v___x_265_, 0);
lean_inc(v_a_266_);
lean_dec_ref(v___x_265_);
lean_inc_ref(v_targetNew_257_);
v___x_267_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_targetNew_257_, v_a_266_, v___y_259_, v___y_260_, v___y_261_, v___y_262_);
if (lean_obj_tag(v___x_267_) == 0)
{
lean_object* v_a_268_; lean_object* v___x_269_; 
v_a_268_ = lean_ctor_get(v___x_267_, 0);
lean_inc(v_a_268_);
lean_dec_ref(v___x_267_);
lean_inc(v_mvarId_255_);
v___x_269_ = l_Lean_MVarId_getType(v_mvarId_255_, v___y_259_, v___y_260_, v___y_261_, v___y_262_);
if (lean_obj_tag(v___x_269_) == 0)
{
lean_object* v_a_270_; lean_object* v___x_271_; 
v_a_270_ = lean_ctor_get(v___x_269_, 0);
lean_inc_n(v_a_270_, 2);
lean_dec_ref(v___x_269_);
v___x_271_ = l_Lean_Meta_getLevel(v_a_270_, v___y_259_, v___y_260_, v___y_261_, v___y_262_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v_a_272_; lean_object* v___x_273_; 
v_a_272_ = lean_ctor_get(v___x_271_, 0);
lean_inc(v_a_272_);
lean_dec_ref(v___x_271_);
lean_inc_ref(v_targetNew_257_);
lean_inc(v_a_270_);
v___x_273_ = l_Lean_Meta_mkEq(v_a_270_, v_targetNew_257_, v___y_259_, v___y_260_, v___y_261_, v___y_262_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v_a_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_295_; 
v_a_274_ = lean_ctor_get(v___x_273_, 0);
lean_inc(v_a_274_);
lean_dec_ref(v___x_273_);
v___x_275_ = l_Lean_Meta_mkExpectedPropHint(v_eqProof_258_, v_a_274_);
v___x_276_ = ((lean_object*)(l_Lean_MVarId_replaceTargetEq___lam__0___closed__2));
v___x_277_ = lean_box(0);
v___x_278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_278_, 0, v_a_272_);
lean_ctor_set(v___x_278_, 1, v___x_277_);
v___x_279_ = l_Lean_mkConst(v___x_276_, v___x_278_);
v___x_280_ = lean_unsigned_to_nat(4u);
v___x_281_ = lean_mk_empty_array_with_capacity(v___x_280_);
v___x_282_ = lean_array_push(v___x_281_, v_a_270_);
v___x_283_ = lean_array_push(v___x_282_, v_targetNew_257_);
v___x_284_ = lean_array_push(v___x_283_, v___x_275_);
lean_inc(v_a_268_);
v___x_285_ = lean_array_push(v___x_284_, v_a_268_);
v___x_286_ = l_Lean_mkAppN(v___x_279_, v___x_285_);
lean_dec_ref(v___x_285_);
v___x_287_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg(v_mvarId_255_, v___x_286_, v___y_260_);
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_295_ == 0)
{
lean_object* v_unused_296_; 
v_unused_296_ = lean_ctor_get(v___x_287_, 0);
lean_dec(v_unused_296_);
v___x_289_ = v___x_287_;
v_isShared_290_ = v_isSharedCheck_295_;
goto v_resetjp_288_;
}
else
{
lean_dec(v___x_287_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_295_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_291_; lean_object* v___x_293_; 
v___x_291_ = l_Lean_Expr_mvarId_x21(v_a_268_);
lean_dec(v_a_268_);
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 0, v___x_291_);
v___x_293_ = v___x_289_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_291_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
else
{
lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_304_; 
lean_dec(v_a_272_);
lean_dec(v_a_270_);
lean_dec(v_a_268_);
lean_dec_ref(v_eqProof_258_);
lean_dec_ref(v_targetNew_257_);
lean_dec(v_mvarId_255_);
v_a_297_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_304_ == 0)
{
v___x_299_ = v___x_273_;
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_a_297_);
lean_dec(v___x_273_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_302_; 
if (v_isShared_300_ == 0)
{
v___x_302_ = v___x_299_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_a_297_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
}
}
else
{
lean_object* v_a_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_312_; 
lean_dec(v_a_270_);
lean_dec(v_a_268_);
lean_dec_ref(v_eqProof_258_);
lean_dec_ref(v_targetNew_257_);
lean_dec(v_mvarId_255_);
v_a_305_ = lean_ctor_get(v___x_271_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_312_ == 0)
{
v___x_307_ = v___x_271_;
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_a_305_);
lean_dec(v___x_271_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_310_; 
if (v_isShared_308_ == 0)
{
v___x_310_ = v___x_307_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_a_305_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
}
else
{
lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_320_; 
lean_dec(v_a_268_);
lean_dec_ref(v_eqProof_258_);
lean_dec_ref(v_targetNew_257_);
lean_dec(v_mvarId_255_);
v_a_313_ = lean_ctor_get(v___x_269_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_320_ == 0)
{
v___x_315_ = v___x_269_;
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_dec(v___x_269_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_316_ == 0)
{
v___x_318_ = v___x_315_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_a_313_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
}
else
{
lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_328_; 
lean_dec_ref(v_eqProof_258_);
lean_dec_ref(v_targetNew_257_);
lean_dec(v_mvarId_255_);
v_a_321_ = lean_ctor_get(v___x_267_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_328_ == 0)
{
v___x_323_ = v___x_267_;
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v___x_267_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
if (v_isShared_324_ == 0)
{
v___x_326_ = v___x_323_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_a_321_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
else
{
lean_object* v_a_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_336_; 
lean_dec_ref(v_eqProof_258_);
lean_dec_ref(v_targetNew_257_);
lean_dec(v_mvarId_255_);
v_a_329_ = lean_ctor_get(v___x_265_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_265_);
if (v_isSharedCheck_336_ == 0)
{
v___x_331_ = v___x_265_;
v_isShared_332_ = v_isSharedCheck_336_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_a_329_);
lean_dec(v___x_265_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_336_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_334_; 
if (v_isShared_332_ == 0)
{
v___x_334_ = v___x_331_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_a_329_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
}
}
else
{
lean_object* v_a_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_344_; 
lean_dec_ref(v_eqProof_258_);
lean_dec_ref(v_targetNew_257_);
lean_dec(v_mvarId_255_);
v_a_337_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_344_ == 0)
{
v___x_339_ = v___x_264_;
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_a_337_);
lean_dec(v___x_264_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_342_; 
if (v_isShared_340_ == 0)
{
v___x_342_ = v___x_339_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_a_337_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetEq___lam__0___boxed(lean_object* v_mvarId_345_, lean_object* v___x_346_, lean_object* v_targetNew_347_, lean_object* v_eqProof_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Lean_MVarId_replaceTargetEq___lam__0(v_mvarId_345_, v___x_346_, v_targetNew_347_, v_eqProof_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
lean_dec(v___y_350_);
lean_dec_ref(v___y_349_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetEq(lean_object* v_mvarId_358_, lean_object* v_targetNew_359_, lean_object* v_eqProof_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_){
_start:
{
lean_object* v___x_366_; lean_object* v___f_367_; lean_object* v___x_368_; 
v___x_366_ = ((lean_object*)(l_Lean_MVarId_replaceTargetEq___closed__1));
lean_inc(v_mvarId_358_);
v___f_367_ = lean_alloc_closure((void*)(l_Lean_MVarId_replaceTargetEq___lam__0___boxed), 9, 4);
lean_closure_set(v___f_367_, 0, v_mvarId_358_);
lean_closure_set(v___f_367_, 1, v___x_366_);
lean_closure_set(v___f_367_, 2, v_targetNew_359_);
lean_closure_set(v___f_367_, 3, v_eqProof_360_);
v___x_368_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_358_, v___f_367_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetEq___boxed(lean_object* v_mvarId_369_, lean_object* v_targetNew_370_, lean_object* v_eqProof_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lean_MVarId_replaceTargetEq(v_mvarId_369_, v_targetNew_370_, v_eqProof_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_);
lean_dec(v_a_375_);
lean_dec_ref(v_a_374_);
lean_dec(v_a_373_);
lean_dec_ref(v_a_372_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0(lean_object* v_mvarId_378_, lean_object* v_val_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg(v_mvarId_378_, v_val_379_, v___y_381_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___boxed(lean_object* v_mvarId_386_, lean_object* v_val_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0(v_mvarId_386_, v_val_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0(lean_object* v_00_u03b2_394_, lean_object* v_x_395_, lean_object* v_x_396_, lean_object* v_x_397_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0___redArg(v_x_395_, v_x_396_, v_x_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_399_, lean_object* v_x_400_, size_t v_x_401_, size_t v_x_402_, lean_object* v_x_403_, lean_object* v_x_404_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg(v_x_400_, v_x_401_, v_x_402_, v_x_403_, v_x_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_406_, lean_object* v_x_407_, lean_object* v_x_408_, lean_object* v_x_409_, lean_object* v_x_410_, lean_object* v_x_411_){
_start:
{
size_t v_x_2155__boxed_412_; size_t v_x_2156__boxed_413_; lean_object* v_res_414_; 
v_x_2155__boxed_412_ = lean_unbox_usize(v_x_408_);
lean_dec(v_x_408_);
v_x_2156__boxed_413_ = lean_unbox_usize(v_x_409_);
lean_dec(v_x_409_);
v_res_414_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2(v_00_u03b2_406_, v_x_407_, v_x_2155__boxed_412_, v_x_2156__boxed_413_, v_x_410_, v_x_411_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_415_, lean_object* v_n_416_, lean_object* v_k_417_, lean_object* v_v_418_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3___redArg(v_n_416_, v_k_417_, v_v_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_420_, size_t v_depth_421_, lean_object* v_keys_422_, lean_object* v_vals_423_, lean_object* v_heq_424_, lean_object* v_i_425_, lean_object* v_entries_426_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_421_, v_keys_422_, v_vals_423_, v_i_425_, v_entries_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_428_, lean_object* v_depth_429_, lean_object* v_keys_430_, lean_object* v_vals_431_, lean_object* v_heq_432_, lean_object* v_i_433_, lean_object* v_entries_434_){
_start:
{
size_t v_depth_boxed_435_; lean_object* v_res_436_; 
v_depth_boxed_435_ = lean_unbox_usize(v_depth_429_);
lean_dec(v_depth_429_);
v_res_436_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_428_, v_depth_boxed_435_, v_keys_430_, v_vals_431_, v_heq_432_, v_i_433_, v_entries_434_);
lean_dec_ref(v_vals_431_);
lean_dec_ref(v_keys_430_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_437_, lean_object* v_x_438_, lean_object* v_x_439_, lean_object* v_x_440_, lean_object* v_x_441_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_x_438_, v_x_439_, v_x_440_, v_x_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEq___lam__0(lean_object* v_mvarId_443_, lean_object* v___x_444_, lean_object* v_targetNew_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
lean_object* v___x_451_; 
lean_inc(v_mvarId_443_);
v___x_451_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_443_, v___x_444_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_object* v___x_452_; 
lean_dec_ref(v___x_451_);
lean_inc(v_mvarId_443_);
v___x_452_ = l_Lean_MVarId_getType(v_mvarId_443_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
if (lean_obj_tag(v___x_452_) == 0)
{
lean_object* v_a_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_501_; 
v_a_453_ = lean_ctor_get(v___x_452_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_501_ == 0)
{
v___x_455_ = v___x_452_;
v_isShared_456_ = v_isSharedCheck_501_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_a_453_);
lean_dec(v___x_452_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_501_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
uint8_t v___x_457_; 
v___x_457_ = lean_expr_equal(v_a_453_, v_targetNew_445_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; 
lean_del_object(v___x_455_);
lean_inc(v_mvarId_443_);
v___x_458_ = l_Lean_MVarId_getTag(v_mvarId_443_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v_a_459_; lean_object* v___x_460_; 
v_a_459_ = lean_ctor_get(v___x_458_, 0);
lean_inc(v_a_459_);
lean_dec_ref(v___x_458_);
v___x_460_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_targetNew_445_, v_a_459_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
if (lean_obj_tag(v___x_460_) == 0)
{
lean_object* v_a_461_; lean_object* v___x_462_; 
v_a_461_ = lean_ctor_get(v___x_460_, 0);
lean_inc_n(v_a_461_, 2);
lean_dec_ref(v___x_460_);
v___x_462_ = l_Lean_Meta_mkExpectedTypeHint(v_a_461_, v_a_453_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v_a_463_; lean_object* v___x_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_472_; 
v_a_463_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_a_463_);
lean_dec_ref(v___x_462_);
v___x_464_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg(v_mvarId_443_, v_a_463_, v___y_447_);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_472_ == 0)
{
lean_object* v_unused_473_; 
v_unused_473_ = lean_ctor_get(v___x_464_, 0);
lean_dec(v_unused_473_);
v___x_466_ = v___x_464_;
v_isShared_467_ = v_isSharedCheck_472_;
goto v_resetjp_465_;
}
else
{
lean_dec(v___x_464_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_472_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_468_; lean_object* v___x_470_; 
v___x_468_ = l_Lean_Expr_mvarId_x21(v_a_461_);
lean_dec(v_a_461_);
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 0, v___x_468_);
v___x_470_ = v___x_466_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_468_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
else
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_481_; 
lean_dec(v_a_461_);
lean_dec(v_mvarId_443_);
v_a_474_ = lean_ctor_get(v___x_462_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_481_ == 0)
{
v___x_476_ = v___x_462_;
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_462_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_479_; 
if (v_isShared_477_ == 0)
{
v___x_479_ = v___x_476_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_a_474_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
else
{
lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_489_; 
lean_dec(v_a_453_);
lean_dec(v_mvarId_443_);
v_a_482_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_489_ == 0)
{
v___x_484_ = v___x_460_;
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_dec(v___x_460_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_487_; 
if (v_isShared_485_ == 0)
{
v___x_487_ = v___x_484_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_a_482_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
}
else
{
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_497_; 
lean_dec(v_a_453_);
lean_dec_ref(v_targetNew_445_);
lean_dec(v_mvarId_443_);
v_a_490_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_497_ == 0)
{
v___x_492_ = v___x_458_;
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_458_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_495_; 
if (v_isShared_493_ == 0)
{
v___x_495_ = v___x_492_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_a_490_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
}
else
{
lean_object* v___x_499_; 
lean_dec(v_a_453_);
lean_dec_ref(v_targetNew_445_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 0, v_mvarId_443_);
v___x_499_ = v___x_455_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_mvarId_443_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
else
{
lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_509_; 
lean_dec_ref(v_targetNew_445_);
lean_dec(v_mvarId_443_);
v_a_502_ = lean_ctor_get(v___x_452_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_509_ == 0)
{
v___x_504_ = v___x_452_;
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_452_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_507_; 
if (v_isShared_505_ == 0)
{
v___x_507_ = v___x_504_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_a_502_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
else
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_517_; 
lean_dec_ref(v_targetNew_445_);
lean_dec(v_mvarId_443_);
v_a_510_ = lean_ctor_get(v___x_451_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_517_ == 0)
{
v___x_512_ = v___x_451_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_451_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_513_ == 0)
{
v___x_515_ = v___x_512_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_a_510_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEq___lam__0___boxed(lean_object* v_mvarId_518_, lean_object* v___x_519_, lean_object* v_targetNew_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Lean_MVarId_replaceTargetDefEq___lam__0(v_mvarId_518_, v___x_519_, v_targetNew_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object* v_mvarId_530_, lean_object* v_targetNew_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_){
_start:
{
lean_object* v___x_537_; lean_object* v___f_538_; lean_object* v___x_539_; 
v___x_537_ = ((lean_object*)(l_Lean_MVarId_replaceTargetDefEq___closed__1));
lean_inc(v_mvarId_530_);
v___f_538_ = lean_alloc_closure((void*)(l_Lean_MVarId_replaceTargetDefEq___lam__0___boxed), 8, 3);
lean_closure_set(v___f_538_, 0, v_mvarId_530_);
lean_closure_set(v___f_538_, 1, v___x_537_);
lean_closure_set(v___f_538_, 2, v_targetNew_531_);
v___x_539_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_530_, v___f_538_, v_a_532_, v_a_533_, v_a_534_, v_a_535_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEq___boxed(lean_object* v_mvarId_540_, lean_object* v_targetNew_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_540_, v_targetNew_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_);
lean_dec(v_a_545_);
lean_dec_ref(v_a_544_);
lean_dec(v_a_543_);
lean_dec_ref(v_a_542_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___lam__0(lean_object* v_e_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
uint8_t v___x_555_; 
v___x_555_ = l_Lean_Expr_isFVar(v_e_548_);
if (v___x_555_ == 0)
{
uint8_t v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_556_ = l_Lean_Expr_hasFVar(v_e_548_);
v___x_557_ = lean_box(v___x_556_);
v___x_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
return v___x_558_;
}
else
{
lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_559_ = l_Lean_Expr_fvarId_x21(v_e_548_);
v___x_560_ = l_Lean_FVarId_getDecl___redArg(v___x_559_, v___y_550_, v___y_552_, v___y_553_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_577_; 
v_a_561_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_577_ == 0)
{
v___x_563_ = v___x_560_;
v_isShared_564_ = v_isSharedCheck_577_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_560_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_577_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_565_; lean_object* v_snd_567_; lean_object* v___x_574_; lean_object* v___x_575_; uint8_t v___x_576_; 
v___x_565_ = lean_st_ref_take(v___y_549_);
v___x_574_ = l_Lean_LocalDecl_index(v___x_565_);
v___x_575_ = l_Lean_LocalDecl_index(v_a_561_);
v___x_576_ = lean_nat_dec_lt(v___x_574_, v___x_575_);
lean_dec(v___x_575_);
lean_dec(v___x_574_);
if (v___x_576_ == 0)
{
lean_dec(v_a_561_);
v_snd_567_ = v___x_565_;
goto v___jp_566_;
}
else
{
lean_dec(v___x_565_);
v_snd_567_ = v_a_561_;
goto v___jp_566_;
}
v___jp_566_:
{
lean_object* v___x_568_; uint8_t v___x_569_; lean_object* v___x_570_; lean_object* v___x_572_; 
v___x_568_ = lean_st_ref_set(v___y_549_, v_snd_567_);
v___x_569_ = 0;
v___x_570_ = lean_box(v___x_569_);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 0, v___x_570_);
v___x_572_ = v___x_563_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v___x_570_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
else
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_585_; 
v_a_578_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_585_ == 0)
{
v___x_580_ = v___x_560_;
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_560_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_583_; 
if (v_isShared_581_ == 0)
{
v___x_583_ = v___x_580_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_a_578_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___lam__0___boxed(lean_object* v_e_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___lam__0(v_e_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
lean_dec_ref(v_e_586_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_x_594_, lean_object* v_x_595_){
_start:
{
if (lean_obj_tag(v_x_595_) == 0)
{
return v_x_594_;
}
else
{
lean_object* v_key_596_; lean_object* v_value_597_; lean_object* v_tail_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_621_; 
v_key_596_ = lean_ctor_get(v_x_595_, 0);
v_value_597_ = lean_ctor_get(v_x_595_, 1);
v_tail_598_ = lean_ctor_get(v_x_595_, 2);
v_isSharedCheck_621_ = !lean_is_exclusive(v_x_595_);
if (v_isSharedCheck_621_ == 0)
{
v___x_600_ = v_x_595_;
v_isShared_601_ = v_isSharedCheck_621_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_tail_598_);
lean_inc(v_value_597_);
lean_inc(v_key_596_);
lean_dec(v_x_595_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_621_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_602_; uint64_t v___x_603_; uint64_t v___x_604_; uint64_t v___x_605_; uint64_t v_fold_606_; uint64_t v___x_607_; uint64_t v___x_608_; uint64_t v___x_609_; size_t v___x_610_; size_t v___x_611_; size_t v___x_612_; size_t v___x_613_; size_t v___x_614_; lean_object* v___x_615_; lean_object* v___x_617_; 
v___x_602_ = lean_array_get_size(v_x_594_);
v___x_603_ = l_Lean_Expr_hash(v_key_596_);
v___x_604_ = 32ULL;
v___x_605_ = lean_uint64_shift_right(v___x_603_, v___x_604_);
v_fold_606_ = lean_uint64_xor(v___x_603_, v___x_605_);
v___x_607_ = 16ULL;
v___x_608_ = lean_uint64_shift_right(v_fold_606_, v___x_607_);
v___x_609_ = lean_uint64_xor(v_fold_606_, v___x_608_);
v___x_610_ = lean_uint64_to_usize(v___x_609_);
v___x_611_ = lean_usize_of_nat(v___x_602_);
v___x_612_ = ((size_t)1ULL);
v___x_613_ = lean_usize_sub(v___x_611_, v___x_612_);
v___x_614_ = lean_usize_land(v___x_610_, v___x_613_);
v___x_615_ = lean_array_uget_borrowed(v_x_594_, v___x_614_);
lean_inc(v___x_615_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 2, v___x_615_);
v___x_617_ = v___x_600_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_key_596_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v_value_597_);
lean_ctor_set(v_reuseFailAlloc_620_, 2, v___x_615_);
v___x_617_ = v_reuseFailAlloc_620_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
lean_object* v___x_618_; 
v___x_618_ = lean_array_uset(v_x_594_, v___x_614_, v___x_617_);
v_x_594_ = v___x_618_;
v_x_595_ = v_tail_598_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__1_spec__4_spec__5___redArg(lean_object* v_i_622_, lean_object* v_source_623_, lean_object* v_target_624_){
_start:
{
lean_object* v___x_625_; uint8_t v___x_626_; 
v___x_625_ = lean_array_get_size(v_source_623_);
v___x_626_ = lean_nat_dec_lt(v_i_622_, v___x_625_);
if (v___x_626_ == 0)
{
lean_dec_ref(v_source_623_);
lean_dec(v_i_622_);
return v_target_624_;
}
else
{
lean_object* v_es_627_; lean_object* v___x_628_; lean_object* v_source_629_; lean_object* v_target_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v_es_627_ = lean_array_fget(v_source_623_, v_i_622_);
v___x_628_ = lean_box(0);
v_source_629_ = lean_array_fset(v_source_623_, v_i_622_, v___x_628_);
v_target_630_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_target_624_, v_es_627_);
v___x_631_ = lean_unsigned_to_nat(1u);
v___x_632_ = lean_nat_add(v_i_622_, v___x_631_);
lean_dec(v_i_622_);
v_i_622_ = v___x_632_;
v_source_623_ = v_source_629_;
v_target_624_ = v_target_630_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__1_spec__4___redArg(lean_object* v_data_634_){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v_nbuckets_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_635_ = lean_array_get_size(v_data_634_);
v___x_636_ = lean_unsigned_to_nat(2u);
v_nbuckets_637_ = lean_nat_mul(v___x_635_, v___x_636_);
v___x_638_ = lean_unsigned_to_nat(0u);
v___x_639_ = lean_box(0);
v___x_640_ = lean_mk_array(v_nbuckets_637_, v___x_639_);
v___x_641_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__1_spec__4_spec__5___redArg(v___x_638_, v_data_634_, v___x_640_);
return v___x_641_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__1_spec__3___redArg(lean_object* v_a_642_, lean_object* v_x_643_){
_start:
{
if (lean_obj_tag(v_x_643_) == 0)
{
uint8_t v___x_644_; 
v___x_644_ = 0;
return v___x_644_;
}
else
{
lean_object* v_key_645_; lean_object* v_tail_646_; uint8_t v___x_647_; 
v_key_645_ = lean_ctor_get(v_x_643_, 0);
v_tail_646_ = lean_ctor_get(v_x_643_, 2);
v___x_647_ = lean_expr_eqv(v_key_645_, v_a_642_);
if (v___x_647_ == 0)
{
v_x_643_ = v_tail_646_;
goto _start;
}
else
{
return v___x_647_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_a_649_, lean_object* v_x_650_){
_start:
{
uint8_t v_res_651_; lean_object* v_r_652_; 
v_res_651_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__1_spec__3___redArg(v_a_649_, v_x_650_);
lean_dec(v_x_650_);
lean_dec_ref(v_a_649_);
v_r_652_ = lean_box(v_res_651_);
return v_r_652_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__1_spec__5___redArg(lean_object* v_a_653_, lean_object* v_b_654_, lean_object* v_x_655_){
_start:
{
if (lean_obj_tag(v_x_655_) == 0)
{
lean_dec(v_b_654_);
lean_dec_ref(v_a_653_);
return v_x_655_;
}
else
{
lean_object* v_key_656_; lean_object* v_value_657_; lean_object* v_tail_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_670_; 
v_key_656_ = lean_ctor_get(v_x_655_, 0);
v_value_657_ = lean_ctor_get(v_x_655_, 1);
v_tail_658_ = lean_ctor_get(v_x_655_, 2);
v_isSharedCheck_670_ = !lean_is_exclusive(v_x_655_);
if (v_isSharedCheck_670_ == 0)
{
v___x_660_ = v_x_655_;
v_isShared_661_ = v_isSharedCheck_670_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_tail_658_);
lean_inc(v_value_657_);
lean_inc(v_key_656_);
lean_dec(v_x_655_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_670_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
uint8_t v___x_662_; 
v___x_662_ = lean_expr_eqv(v_key_656_, v_a_653_);
if (v___x_662_ == 0)
{
lean_object* v___x_663_; lean_object* v___x_665_; 
v___x_663_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__1_spec__5___redArg(v_a_653_, v_b_654_, v_tail_658_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 2, v___x_663_);
v___x_665_ = v___x_660_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_key_656_);
lean_ctor_set(v_reuseFailAlloc_666_, 1, v_value_657_);
lean_ctor_set(v_reuseFailAlloc_666_, 2, v___x_663_);
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
lean_object* v___x_668_; 
lean_dec(v_value_657_);
lean_dec(v_key_656_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 1, v_b_654_);
lean_ctor_set(v___x_660_, 0, v_a_653_);
v___x_668_ = v___x_660_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_a_653_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v_b_654_);
lean_ctor_set(v_reuseFailAlloc_669_, 2, v_tail_658_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__1___redArg(lean_object* v_m_671_, lean_object* v_a_672_, lean_object* v_b_673_){
_start:
{
lean_object* v_size_674_; lean_object* v_buckets_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_718_; 
v_size_674_ = lean_ctor_get(v_m_671_, 0);
v_buckets_675_ = lean_ctor_get(v_m_671_, 1);
v_isSharedCheck_718_ = !lean_is_exclusive(v_m_671_);
if (v_isSharedCheck_718_ == 0)
{
v___x_677_ = v_m_671_;
v_isShared_678_ = v_isSharedCheck_718_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_buckets_675_);
lean_inc(v_size_674_);
lean_dec(v_m_671_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_718_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_679_; uint64_t v___x_680_; uint64_t v___x_681_; uint64_t v___x_682_; uint64_t v_fold_683_; uint64_t v___x_684_; uint64_t v___x_685_; uint64_t v___x_686_; size_t v___x_687_; size_t v___x_688_; size_t v___x_689_; size_t v___x_690_; size_t v___x_691_; lean_object* v_bkt_692_; uint8_t v___x_693_; 
v___x_679_ = lean_array_get_size(v_buckets_675_);
v___x_680_ = l_Lean_Expr_hash(v_a_672_);
v___x_681_ = 32ULL;
v___x_682_ = lean_uint64_shift_right(v___x_680_, v___x_681_);
v_fold_683_ = lean_uint64_xor(v___x_680_, v___x_682_);
v___x_684_ = 16ULL;
v___x_685_ = lean_uint64_shift_right(v_fold_683_, v___x_684_);
v___x_686_ = lean_uint64_xor(v_fold_683_, v___x_685_);
v___x_687_ = lean_uint64_to_usize(v___x_686_);
v___x_688_ = lean_usize_of_nat(v___x_679_);
v___x_689_ = ((size_t)1ULL);
v___x_690_ = lean_usize_sub(v___x_688_, v___x_689_);
v___x_691_ = lean_usize_land(v___x_687_, v___x_690_);
v_bkt_692_ = lean_array_uget_borrowed(v_buckets_675_, v___x_691_);
v___x_693_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__1_spec__3___redArg(v_a_672_, v_bkt_692_);
if (v___x_693_ == 0)
{
lean_object* v___x_694_; lean_object* v_size_x27_695_; lean_object* v___x_696_; lean_object* v_buckets_x27_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; uint8_t v___x_703_; 
v___x_694_ = lean_unsigned_to_nat(1u);
v_size_x27_695_ = lean_nat_add(v_size_674_, v___x_694_);
lean_dec(v_size_674_);
lean_inc(v_bkt_692_);
v___x_696_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_696_, 0, v_a_672_);
lean_ctor_set(v___x_696_, 1, v_b_673_);
lean_ctor_set(v___x_696_, 2, v_bkt_692_);
v_buckets_x27_697_ = lean_array_uset(v_buckets_675_, v___x_691_, v___x_696_);
v___x_698_ = lean_unsigned_to_nat(4u);
v___x_699_ = lean_nat_mul(v_size_x27_695_, v___x_698_);
v___x_700_ = lean_unsigned_to_nat(3u);
v___x_701_ = lean_nat_div(v___x_699_, v___x_700_);
lean_dec(v___x_699_);
v___x_702_ = lean_array_get_size(v_buckets_x27_697_);
v___x_703_ = lean_nat_dec_le(v___x_701_, v___x_702_);
lean_dec(v___x_701_);
if (v___x_703_ == 0)
{
lean_object* v_val_704_; lean_object* v___x_706_; 
v_val_704_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__1_spec__4___redArg(v_buckets_x27_697_);
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 1, v_val_704_);
lean_ctor_set(v___x_677_, 0, v_size_x27_695_);
v___x_706_ = v___x_677_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_size_x27_695_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v_val_704_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
else
{
lean_object* v___x_709_; 
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 1, v_buckets_x27_697_);
lean_ctor_set(v___x_677_, 0, v_size_x27_695_);
v___x_709_ = v___x_677_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_size_x27_695_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v_buckets_x27_697_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
else
{
lean_object* v___x_711_; lean_object* v_buckets_x27_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_716_; 
lean_inc(v_bkt_692_);
v___x_711_ = lean_box(0);
v_buckets_x27_712_ = lean_array_uset(v_buckets_675_, v___x_691_, v___x_711_);
v___x_713_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__1_spec__5___redArg(v_a_672_, v_b_673_, v_bkt_692_);
v___x_714_ = lean_array_uset(v_buckets_x27_712_, v___x_691_, v___x_713_);
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 1, v___x_714_);
v___x_716_ = v___x_677_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_size_674_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v___x_714_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__0_spec__1___redArg(lean_object* v_a_719_, lean_object* v_x_720_){
_start:
{
if (lean_obj_tag(v_x_720_) == 0)
{
lean_object* v___x_721_; 
v___x_721_ = lean_box(0);
return v___x_721_;
}
else
{
lean_object* v_key_722_; lean_object* v_value_723_; lean_object* v_tail_724_; uint8_t v___x_725_; 
v_key_722_ = lean_ctor_get(v_x_720_, 0);
v_value_723_ = lean_ctor_get(v_x_720_, 1);
v_tail_724_ = lean_ctor_get(v_x_720_, 2);
v___x_725_ = lean_expr_eqv(v_key_722_, v_a_719_);
if (v___x_725_ == 0)
{
v_x_720_ = v_tail_724_;
goto _start;
}
else
{
lean_object* v___x_727_; 
lean_inc(v_value_723_);
v___x_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_727_, 0, v_value_723_);
return v___x_727_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_a_728_, lean_object* v_x_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__0_spec__1___redArg(v_a_728_, v_x_729_);
lean_dec(v_x_729_);
lean_dec_ref(v_a_728_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__0___redArg(lean_object* v_m_731_, lean_object* v_a_732_){
_start:
{
lean_object* v_buckets_733_; lean_object* v___x_734_; uint64_t v___x_735_; uint64_t v___x_736_; uint64_t v___x_737_; uint64_t v_fold_738_; uint64_t v___x_739_; uint64_t v___x_740_; uint64_t v___x_741_; size_t v___x_742_; size_t v___x_743_; size_t v___x_744_; size_t v___x_745_; size_t v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v_buckets_733_ = lean_ctor_get(v_m_731_, 1);
v___x_734_ = lean_array_get_size(v_buckets_733_);
v___x_735_ = l_Lean_Expr_hash(v_a_732_);
v___x_736_ = 32ULL;
v___x_737_ = lean_uint64_shift_right(v___x_735_, v___x_736_);
v_fold_738_ = lean_uint64_xor(v___x_735_, v___x_737_);
v___x_739_ = 16ULL;
v___x_740_ = lean_uint64_shift_right(v_fold_738_, v___x_739_);
v___x_741_ = lean_uint64_xor(v_fold_738_, v___x_740_);
v___x_742_ = lean_uint64_to_usize(v___x_741_);
v___x_743_ = lean_usize_of_nat(v___x_734_);
v___x_744_ = ((size_t)1ULL);
v___x_745_ = lean_usize_sub(v___x_743_, v___x_744_);
v___x_746_ = lean_usize_land(v___x_742_, v___x_745_);
v___x_747_ = lean_array_uget_borrowed(v_buckets_733_, v___x_746_);
v___x_748_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__0_spec__1___redArg(v_a_732_, v___x_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__0___redArg___boxed(lean_object* v_m_749_, lean_object* v_a_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__0___redArg(v_m_749_, v_a_750_);
lean_dec_ref(v_a_750_);
lean_dec_ref(v_m_749_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0(lean_object* v_g_752_, lean_object* v_e_753_, lean_object* v_a_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
lean_object* v_a_762_; lean_object* v___y_768_; lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_770_ = lean_st_ref_get(v_a_754_);
v___x_771_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__0___redArg(v___x_770_, v_e_753_);
lean_dec(v___x_770_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v___x_772_; 
lean_inc_ref(v_g_752_);
lean_inc(v___y_759_);
lean_inc_ref(v___y_758_);
lean_inc(v___y_757_);
lean_inc_ref(v___y_756_);
lean_inc(v___y_755_);
lean_inc_ref(v_e_753_);
v___x_772_ = lean_apply_7(v_g_752_, v_e_753_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, lean_box(0));
if (lean_obj_tag(v___x_772_) == 0)
{
lean_object* v_a_773_; lean_object* v_d_775_; lean_object* v_b_776_; lean_object* v___y_777_; uint8_t v___x_780_; 
v_a_773_ = lean_ctor_get(v___x_772_, 0);
lean_inc(v_a_773_);
lean_dec_ref(v___x_772_);
v___x_780_ = lean_unbox(v_a_773_);
lean_dec(v_a_773_);
if (v___x_780_ == 0)
{
lean_object* v___x_781_; 
lean_dec_ref(v_g_752_);
v___x_781_ = lean_box(0);
v_a_762_ = v___x_781_;
goto v___jp_761_;
}
else
{
switch(lean_obj_tag(v_e_753_))
{
case 7:
{
lean_object* v_binderType_782_; lean_object* v_body_783_; 
v_binderType_782_ = lean_ctor_get(v_e_753_, 1);
v_body_783_ = lean_ctor_get(v_e_753_, 2);
lean_inc_ref(v_body_783_);
lean_inc_ref(v_binderType_782_);
v_d_775_ = v_binderType_782_;
v_b_776_ = v_body_783_;
v___y_777_ = v_a_754_;
goto v___jp_774_;
}
case 6:
{
lean_object* v_binderType_784_; lean_object* v_body_785_; 
v_binderType_784_ = lean_ctor_get(v_e_753_, 1);
v_body_785_ = lean_ctor_get(v_e_753_, 2);
lean_inc_ref(v_body_785_);
lean_inc_ref(v_binderType_784_);
v_d_775_ = v_binderType_784_;
v_b_776_ = v_body_785_;
v___y_777_ = v_a_754_;
goto v___jp_774_;
}
case 8:
{
lean_object* v_type_786_; lean_object* v_value_787_; lean_object* v_body_788_; lean_object* v___x_789_; 
v_type_786_ = lean_ctor_get(v_e_753_, 1);
v_value_787_ = lean_ctor_get(v_e_753_, 2);
v_body_788_ = lean_ctor_get(v_e_753_, 3);
lean_inc_ref(v_type_786_);
lean_inc_ref(v_g_752_);
v___x_789_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0(v_g_752_, v_type_786_, v_a_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
if (lean_obj_tag(v___x_789_) == 0)
{
lean_object* v___x_790_; 
lean_dec_ref(v___x_789_);
lean_inc_ref(v_value_787_);
lean_inc_ref(v_g_752_);
v___x_790_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0(v_g_752_, v_value_787_, v_a_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v___x_791_; 
lean_dec_ref(v___x_790_);
lean_inc_ref(v_body_788_);
v___x_791_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0(v_g_752_, v_body_788_, v_a_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
v___y_768_ = v___x_791_;
goto v___jp_767_;
}
else
{
lean_dec_ref(v_g_752_);
v___y_768_ = v___x_790_;
goto v___jp_767_;
}
}
else
{
lean_dec_ref(v_g_752_);
v___y_768_ = v___x_789_;
goto v___jp_767_;
}
}
case 5:
{
lean_object* v_fn_792_; lean_object* v_arg_793_; lean_object* v___x_794_; 
v_fn_792_ = lean_ctor_get(v_e_753_, 0);
v_arg_793_ = lean_ctor_get(v_e_753_, 1);
lean_inc_ref(v_fn_792_);
lean_inc_ref(v_g_752_);
v___x_794_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0(v_g_752_, v_fn_792_, v_a_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v___x_795_; 
lean_dec_ref(v___x_794_);
lean_inc_ref(v_arg_793_);
v___x_795_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0(v_g_752_, v_arg_793_, v_a_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
v___y_768_ = v___x_795_;
goto v___jp_767_;
}
else
{
lean_dec_ref(v_g_752_);
v___y_768_ = v___x_794_;
goto v___jp_767_;
}
}
case 10:
{
lean_object* v_expr_796_; lean_object* v___x_797_; 
v_expr_796_ = lean_ctor_get(v_e_753_, 1);
lean_inc_ref(v_expr_796_);
v___x_797_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0(v_g_752_, v_expr_796_, v_a_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
v___y_768_ = v___x_797_;
goto v___jp_767_;
}
case 11:
{
lean_object* v_struct_798_; lean_object* v___x_799_; 
v_struct_798_ = lean_ctor_get(v_e_753_, 2);
lean_inc_ref(v_struct_798_);
v___x_799_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0(v_g_752_, v_struct_798_, v_a_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
v___y_768_ = v___x_799_;
goto v___jp_767_;
}
default: 
{
lean_object* v___x_800_; 
lean_dec_ref(v_g_752_);
v___x_800_ = lean_box(0);
v_a_762_ = v___x_800_;
goto v___jp_761_;
}
}
}
v___jp_774_:
{
lean_object* v___x_778_; 
lean_inc_ref(v_g_752_);
v___x_778_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0(v_g_752_, v_d_775_, v___y_777_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_object* v___x_779_; 
lean_dec_ref(v___x_778_);
v___x_779_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0(v_g_752_, v_b_776_, v___y_777_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
v___y_768_ = v___x_779_;
goto v___jp_767_;
}
else
{
lean_dec_ref(v_b_776_);
lean_dec_ref(v_g_752_);
v___y_768_ = v___x_778_;
goto v___jp_767_;
}
}
}
else
{
lean_object* v_a_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_808_; 
lean_dec_ref(v_e_753_);
lean_dec_ref(v_g_752_);
v_a_801_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_808_ == 0)
{
v___x_803_ = v___x_772_;
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_a_801_);
lean_dec(v___x_772_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_806_; 
if (v_isShared_804_ == 0)
{
v___x_806_ = v___x_803_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_a_801_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
}
else
{
lean_object* v_val_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_816_; 
lean_dec_ref(v_e_753_);
lean_dec_ref(v_g_752_);
v_val_809_ = lean_ctor_get(v___x_771_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_816_ == 0)
{
v___x_811_ = v___x_771_;
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_val_809_);
lean_dec(v___x_771_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
lean_ctor_set_tag(v___x_811_, 0);
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_val_809_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
v___jp_761_:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_763_ = lean_st_ref_take(v_a_754_);
v___x_764_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__1___redArg(v___x_763_, v_e_753_, v_a_762_);
v___x_765_ = lean_st_ref_set(v_a_754_, v___x_764_);
v___x_766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_766_, 0, v_a_762_);
return v___x_766_;
}
v___jp_767_:
{
if (lean_obj_tag(v___y_768_) == 0)
{
lean_object* v_a_769_; 
v_a_769_ = lean_ctor_get(v___y_768_, 0);
lean_inc(v_a_769_);
lean_dec_ref(v___y_768_);
v_a_762_ = v_a_769_;
goto v___jp_761_;
}
else
{
lean_dec_ref(v_e_753_);
return v___y_768_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0___boxed(lean_object* v_g_817_, lean_object* v_e_818_, lean_object* v_a_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0(v_g_817_, v_e_818_, v_a_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec(v___y_820_);
lean_dec(v_a_819_);
return v_res_826_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___closed__0(void){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_827_ = lean_box(0);
v___x_828_ = lean_unsigned_to_nat(16u);
v___x_829_ = lean_mk_array(v___x_828_, v___x_827_);
return v___x_829_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___closed__1(void){
_start:
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_830_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___closed__0, &l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___closed__0_once, _init_l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___closed__0);
v___x_831_ = lean_unsigned_to_nat(0u);
v___x_832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
lean_ctor_set(v___x_832_, 1, v___x_830_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar(lean_object* v_e_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___f_843_; lean_object* v___x_844_; 
v___x_841_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___closed__1, &l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___closed__1_once, _init_l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___closed__1);
v___x_842_ = lean_st_mk_ref(v___x_841_);
v___f_843_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___closed__2));
v___x_844_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0(v___f_843_, v_e_834_, v___x_842_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_853_; 
v_a_845_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_853_ == 0)
{
v___x_847_ = v___x_844_;
v_isShared_848_ = v_isSharedCheck_853_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_844_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_853_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_849_; lean_object* v___x_851_; 
v___x_849_ = lean_st_ref_get(v___x_842_);
lean_dec(v___x_842_);
lean_dec(v___x_849_);
if (v_isShared_848_ == 0)
{
v___x_851_ = v___x_847_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_a_845_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
else
{
lean_dec(v___x_842_);
return v___x_844_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___boxed(lean_object* v_e_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar(v_e_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_);
lean_dec(v_a_859_);
lean_dec_ref(v_a_858_);
lean_dec(v_a_857_);
lean_dec_ref(v_a_856_);
lean_dec(v_a_855_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__0(lean_object* v_00_u03b2_862_, lean_object* v_m_863_, lean_object* v_a_864_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__0___redArg(v_m_863_, v_a_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_866_, lean_object* v_m_867_, lean_object* v_a_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__0(v_00_u03b2_866_, v_m_867_, v_a_868_);
lean_dec_ref(v_a_868_);
lean_dec_ref(v_m_867_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__1(lean_object* v_00_u03b2_870_, lean_object* v_m_871_, lean_object* v_a_872_, lean_object* v_b_873_){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__1___redArg(v_m_871_, v_a_872_, v_b_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_875_, lean_object* v_a_876_, lean_object* v_x_877_){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__0_spec__1___redArg(v_a_876_, v_x_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_879_, lean_object* v_a_880_, lean_object* v_x_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__0_spec__1(v_00_u03b2_879_, v_a_880_, v_x_881_);
lean_dec(v_x_881_);
lean_dec_ref(v_a_880_);
return v_res_882_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_883_, lean_object* v_a_884_, lean_object* v_x_885_){
_start:
{
uint8_t v___x_886_; 
v___x_886_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__1_spec__3___redArg(v_a_884_, v_x_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_887_, lean_object* v_a_888_, lean_object* v_x_889_){
_start:
{
uint8_t v_res_890_; lean_object* v_r_891_; 
v_res_890_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__1_spec__3(v_00_u03b2_887_, v_a_888_, v_x_889_);
lean_dec(v_x_889_);
lean_dec_ref(v_a_888_);
v_r_891_ = lean_box(v_res_890_);
return v_r_891_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_892_, lean_object* v_data_893_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__1_spec__4___redArg(v_data_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_895_, lean_object* v_a_896_, lean_object* v_b_897_, lean_object* v_x_898_){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__1_spec__5___redArg(v_a_896_, v_b_897_, v_x_898_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__1_spec__4_spec__5(lean_object* v_00_u03b2_900_, lean_object* v_i_901_, lean_object* v_source_902_, lean_object* v_target_903_){
_start:
{
lean_object* v___x_904_; 
v___x_904_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__1_spec__4_spec__5___redArg(v_i_901_, v_source_902_, v_target_903_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_905_, lean_object* v_x_906_, lean_object* v_x_907_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_x_906_, v_x_907_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_spec__0___redArg(lean_object* v_e_909_, lean_object* v___y_910_){
_start:
{
uint8_t v___x_912_; 
v___x_912_ = l_Lean_Expr_hasMVar(v_e_909_);
if (v___x_912_ == 0)
{
lean_object* v___x_913_; 
v___x_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_913_, 0, v_e_909_);
return v___x_913_;
}
else
{
lean_object* v___x_914_; lean_object* v_mctx_915_; lean_object* v___x_916_; lean_object* v_fst_917_; lean_object* v_snd_918_; lean_object* v___x_919_; lean_object* v_cache_920_; lean_object* v_zetaDeltaFVarIds_921_; lean_object* v_postponed_922_; lean_object* v_diag_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_932_; 
v___x_914_ = lean_st_ref_get(v___y_910_);
v_mctx_915_ = lean_ctor_get(v___x_914_, 0);
lean_inc_ref(v_mctx_915_);
lean_dec(v___x_914_);
v___x_916_ = l_Lean_instantiateMVarsCore(v_mctx_915_, v_e_909_);
v_fst_917_ = lean_ctor_get(v___x_916_, 0);
lean_inc(v_fst_917_);
v_snd_918_ = lean_ctor_get(v___x_916_, 1);
lean_inc(v_snd_918_);
lean_dec_ref(v___x_916_);
v___x_919_ = lean_st_ref_take(v___y_910_);
v_cache_920_ = lean_ctor_get(v___x_919_, 1);
v_zetaDeltaFVarIds_921_ = lean_ctor_get(v___x_919_, 2);
v_postponed_922_ = lean_ctor_get(v___x_919_, 3);
v_diag_923_ = lean_ctor_get(v___x_919_, 4);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_932_ == 0)
{
lean_object* v_unused_933_; 
v_unused_933_ = lean_ctor_get(v___x_919_, 0);
lean_dec(v_unused_933_);
v___x_925_ = v___x_919_;
v_isShared_926_ = v_isSharedCheck_932_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_diag_923_);
lean_inc(v_postponed_922_);
lean_inc(v_zetaDeltaFVarIds_921_);
lean_inc(v_cache_920_);
lean_dec(v___x_919_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_932_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 0, v_snd_918_);
v___x_928_ = v___x_925_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_snd_918_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v_cache_920_);
lean_ctor_set(v_reuseFailAlloc_931_, 2, v_zetaDeltaFVarIds_921_);
lean_ctor_set(v_reuseFailAlloc_931_, 3, v_postponed_922_);
lean_ctor_set(v_reuseFailAlloc_931_, 4, v_diag_923_);
v___x_928_ = v_reuseFailAlloc_931_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_929_ = lean_st_ref_set(v___y_910_, v___x_928_);
v___x_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_930_, 0, v_fst_917_);
return v___x_930_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_spec__0___redArg___boxed(lean_object* v_e_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_spec__0___redArg(v_e_934_, v___y_935_);
lean_dec(v___y_935_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_spec__0(lean_object* v_e_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v___x_944_; 
v___x_944_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_spec__0___redArg(v_e_938_, v___y_940_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_spec__0___boxed(lean_object* v_e_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_spec__0(v_e_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore___lam__0(lean_object* v_fvarId_952_, lean_object* v_eqProof_953_, lean_object* v_typeNew_954_, lean_object* v_mvarId_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v___x_961_; 
lean_inc(v_fvarId_952_);
v___x_961_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_952_, v___y_956_, v___y_958_, v___y_959_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v_a_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v_a_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_a_962_);
lean_dec_ref(v___x_961_);
lean_inc(v_fvarId_952_);
v___x_963_ = l_Lean_mkFVar(v_fvarId_952_);
v___x_964_ = l_Lean_Meta_mkEqMP(v_eqProof_953_, v___x_963_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_object* v_a_965_; lean_object* v___x_966_; lean_object* v_a_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v_a_965_ = lean_ctor_get(v___x_964_, 0);
lean_inc(v_a_965_);
lean_dec_ref(v___x_964_);
lean_inc_ref(v_typeNew_954_);
v___x_966_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_spec__0___redArg(v_typeNew_954_, v___y_957_);
v_a_967_ = lean_ctor_get(v___x_966_, 0);
lean_inc(v_a_967_);
lean_dec_ref(v___x_966_);
lean_inc(v_a_962_);
v___x_968_ = lean_st_mk_ref(v_a_962_);
v___x_969_ = l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar(v_a_967_, v___x_968_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
lean_dec_ref(v___x_969_);
v___x_970_ = lean_st_ref_get(v___x_968_);
lean_dec(v___x_968_);
v___x_971_ = l_Lean_LocalDecl_fvarId(v___x_970_);
lean_dec(v___x_970_);
v___x_972_ = l_Lean_LocalDecl_userName(v_a_962_);
lean_dec(v_a_962_);
v___x_973_ = l_Lean_MVarId_assertAfter(v_mvarId_955_, v___x_971_, v___x_972_, v_typeNew_954_, v_a_965_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; lean_object* v___x_975_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_a_974_);
lean_dec_ref(v___x_973_);
v___x_975_ = l_Lean_Meta_saveState___redArg(v___y_957_, v___y_959_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; lean_object* v_fvarId_977_; lean_object* v_mvarId_978_; lean_object* v_subst_979_; lean_object* v___x_980_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_a_976_);
lean_dec_ref(v___x_975_);
v_fvarId_977_ = lean_ctor_get(v_a_974_, 0);
v_mvarId_978_ = lean_ctor_get(v_a_974_, 1);
v_subst_979_ = lean_ctor_get(v_a_974_, 2);
lean_inc(v_mvarId_978_);
v___x_980_ = l_Lean_MVarId_clear(v_mvarId_978_, v_fvarId_952_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_995_; 
lean_inc(v_subst_979_);
lean_inc(v_fvarId_977_);
lean_dec(v_a_976_);
v_isSharedCheck_995_ = !lean_is_exclusive(v_a_974_);
if (v_isSharedCheck_995_ == 0)
{
lean_object* v_unused_996_; lean_object* v_unused_997_; lean_object* v_unused_998_; 
v_unused_996_ = lean_ctor_get(v_a_974_, 2);
lean_dec(v_unused_996_);
v_unused_997_ = lean_ctor_get(v_a_974_, 1);
lean_dec(v_unused_997_);
v_unused_998_ = lean_ctor_get(v_a_974_, 0);
lean_dec(v_unused_998_);
v___x_982_ = v_a_974_;
v_isShared_983_ = v_isSharedCheck_995_;
goto v_resetjp_981_;
}
else
{
lean_dec(v_a_974_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_995_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_994_; 
v_a_984_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_994_ == 0)
{
v___x_986_ = v___x_980_;
v_isShared_987_ = v_isSharedCheck_994_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_980_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_994_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_989_; 
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 1, v_a_984_);
v___x_989_ = v___x_982_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_fvarId_977_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v_a_984_);
lean_ctor_set(v_reuseFailAlloc_993_, 2, v_subst_979_);
v___x_989_ = v_reuseFailAlloc_993_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
lean_object* v___x_991_; 
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 0, v___x_989_);
v___x_991_ = v___x_986_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v___x_989_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
}
}
else
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1027_; 
v_a_999_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1001_ = v___x_980_;
v_isShared_1002_ = v_isSharedCheck_1027_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_980_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1027_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1004_; 
lean_inc(v_a_999_);
if (v_isShared_1002_ == 0)
{
v___x_1004_ = v___x_1001_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_a_999_);
v___x_1004_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
uint8_t v___y_1006_; uint8_t v___x_1024_; 
v___x_1024_ = l_Lean_Exception_isInterrupt(v_a_999_);
if (v___x_1024_ == 0)
{
uint8_t v___x_1025_; 
v___x_1025_ = l_Lean_Exception_isRuntime(v_a_999_);
v___y_1006_ = v___x_1025_;
goto v___jp_1005_;
}
else
{
lean_dec(v_a_999_);
v___y_1006_ = v___x_1024_;
goto v___jp_1005_;
}
v___jp_1005_:
{
if (v___y_1006_ == 0)
{
lean_object* v___x_1007_; 
lean_dec_ref(v___x_1004_);
v___x_1007_ = l_Lean_Meta_SavedState_restore___redArg(v_a_976_, v___y_957_, v___y_959_);
lean_dec(v_a_976_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1014_; 
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1014_ == 0)
{
lean_object* v_unused_1015_; 
v_unused_1015_ = lean_ctor_get(v___x_1007_, 0);
lean_dec(v_unused_1015_);
v___x_1009_ = v___x_1007_;
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
else
{
lean_dec(v___x_1007_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1012_; 
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 0, v_a_974_);
v___x_1012_ = v___x_1009_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_a_974_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
else
{
lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1023_; 
lean_dec(v_a_974_);
v_a_1016_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1018_ = v___x_1007_;
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___x_1007_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1021_; 
if (v_isShared_1019_ == 0)
{
v___x_1021_ = v___x_1018_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_a_1016_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
}
else
{
lean_dec(v_a_976_);
lean_dec(v_a_974_);
return v___x_1004_;
}
}
}
}
}
}
else
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1035_; 
lean_dec(v_a_974_);
lean_dec(v_fvarId_952_);
v_a_1028_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1030_ = v___x_975_;
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_975_);
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
else
{
lean_dec(v_fvarId_952_);
return v___x_973_;
}
}
else
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1043_; 
lean_dec(v___x_968_);
lean_dec(v_a_965_);
lean_dec(v_a_962_);
lean_dec(v_mvarId_955_);
lean_dec_ref(v_typeNew_954_);
lean_dec(v_fvarId_952_);
v_a_1036_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1038_ = v___x_969_;
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_969_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_1039_ == 0)
{
v___x_1041_ = v___x_1038_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_a_1036_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
else
{
lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1051_; 
lean_dec(v_a_962_);
lean_dec(v_mvarId_955_);
lean_dec_ref(v_typeNew_954_);
lean_dec(v_fvarId_952_);
v_a_1044_ = lean_ctor_get(v___x_964_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1046_ = v___x_964_;
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_964_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1049_; 
if (v_isShared_1047_ == 0)
{
v___x_1049_ = v___x_1046_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_a_1044_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
}
else
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
lean_dec(v_mvarId_955_);
lean_dec_ref(v_typeNew_954_);
lean_dec_ref(v_eqProof_953_);
lean_dec(v_fvarId_952_);
v_a_1052_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v___x_961_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_961_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1052_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore___lam__0___boxed(lean_object* v_fvarId_1060_, lean_object* v_eqProof_1061_, lean_object* v_typeNew_1062_, lean_object* v_mvarId_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore___lam__0(v_fvarId_1060_, v_eqProof_1061_, v_typeNew_1062_, v_mvarId_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore(lean_object* v_mvarId_1070_, lean_object* v_fvarId_1071_, lean_object* v_typeNew_1072_, lean_object* v_eqProof_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_){
_start:
{
lean_object* v___f_1079_; lean_object* v___x_1080_; 
lean_inc(v_mvarId_1070_);
v___f_1079_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1079_, 0, v_fvarId_1071_);
lean_closure_set(v___f_1079_, 1, v_eqProof_1073_);
lean_closure_set(v___f_1079_, 2, v_typeNew_1072_);
lean_closure_set(v___f_1079_, 3, v_mvarId_1070_);
v___x_1080_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_1070_, v___f_1079_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore___boxed(lean_object* v_mvarId_1081_, lean_object* v_fvarId_1082_, lean_object* v_typeNew_1083_, lean_object* v_eqProof_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore(v_mvarId_1081_, v_fvarId_1082_, v_typeNew_1083_, v_eqProof_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
lean_dec(v_a_1088_);
lean_dec_ref(v_a_1087_);
lean_dec(v_a_1086_);
lean_dec_ref(v_a_1085_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDecl(lean_object* v_mvarId_1091_, lean_object* v_fvarId_1092_, lean_object* v_typeNew_1093_, lean_object* v_eqProof_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_){
_start:
{
lean_object* v___x_1100_; 
v___x_1100_ = l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore(v_mvarId_1091_, v_fvarId_1092_, v_typeNew_1093_, v_eqProof_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDecl___boxed(lean_object* v_mvarId_1101_, lean_object* v_fvarId_1102_, lean_object* v_typeNew_1103_, lean_object* v_eqProof_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l_Lean_MVarId_replaceLocalDecl(v_mvarId_1101_, v_fvarId_1102_, v_typeNew_1103_, v_eqProof_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_);
lean_dec(v_a_1108_);
lean_dec_ref(v_a_1107_);
lean_dec(v_a_1106_);
lean_dec_ref(v_a_1105_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___redArg(lean_object* v_decls_1111_, lean_object* v_x_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
lean_object* v___x_1118_; 
v___x_1118_ = l_Lean_Meta_withLocalInstancesImp___redArg(v_decls_1111_, v_x_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1126_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1121_ = v___x_1118_;
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1118_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1124_; 
if (v_isShared_1122_ == 0)
{
v___x_1124_ = v___x_1121_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_a_1119_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
else
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1134_; 
v_a_1127_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1129_ = v___x_1118_;
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1118_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
if (v_isShared_1130_ == 0)
{
v___x_1132_ = v___x_1129_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1127_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___redArg___boxed(lean_object* v_decls_1135_, lean_object* v_x_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___redArg(v_decls_1135_, v_x_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
lean_dec(v___y_1138_);
lean_dec_ref(v___y_1137_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0(lean_object* v_00_u03b1_1143_, lean_object* v_decls_1144_, lean_object* v_x_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v___x_1151_; 
v___x_1151_ = l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___redArg(v_decls_1144_, v_x_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___boxed(lean_object* v_00_u03b1_1152_, lean_object* v_decls_1153_, lean_object* v_x_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0(v_00_u03b1_1152_, v_decls_1153_, v_x_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_);
lean_dec(v___y_1158_);
lean_dec_ref(v___y_1157_);
lean_dec(v___y_1156_);
lean_dec_ref(v___y_1155_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___redArg(lean_object* v_lctx_1161_, lean_object* v_x_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_){
_start:
{
lean_object* v_keyedConfig_1168_; uint8_t v_trackZetaDelta_1169_; lean_object* v_zetaDeltaSet_1170_; lean_object* v_localInstances_1171_; lean_object* v_defEqCtx_x3f_1172_; lean_object* v_synthPendingDepth_1173_; lean_object* v_canUnfold_x3f_1174_; uint8_t v_univApprox_1175_; uint8_t v_inTypeClassResolution_1176_; uint8_t v_cacheInferType_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
v_keyedConfig_1168_ = lean_ctor_get(v___y_1163_, 0);
v_trackZetaDelta_1169_ = lean_ctor_get_uint8(v___y_1163_, sizeof(void*)*7);
v_zetaDeltaSet_1170_ = lean_ctor_get(v___y_1163_, 1);
v_localInstances_1171_ = lean_ctor_get(v___y_1163_, 3);
v_defEqCtx_x3f_1172_ = lean_ctor_get(v___y_1163_, 4);
v_synthPendingDepth_1173_ = lean_ctor_get(v___y_1163_, 5);
v_canUnfold_x3f_1174_ = lean_ctor_get(v___y_1163_, 6);
v_univApprox_1175_ = lean_ctor_get_uint8(v___y_1163_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1176_ = lean_ctor_get_uint8(v___y_1163_, sizeof(void*)*7 + 2);
v_cacheInferType_1177_ = lean_ctor_get_uint8(v___y_1163_, sizeof(void*)*7 + 3);
lean_inc(v_canUnfold_x3f_1174_);
lean_inc(v_synthPendingDepth_1173_);
lean_inc(v_defEqCtx_x3f_1172_);
lean_inc_ref(v_localInstances_1171_);
lean_inc(v_zetaDeltaSet_1170_);
lean_inc_ref(v_keyedConfig_1168_);
v___x_1178_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1178_, 0, v_keyedConfig_1168_);
lean_ctor_set(v___x_1178_, 1, v_zetaDeltaSet_1170_);
lean_ctor_set(v___x_1178_, 2, v_lctx_1161_);
lean_ctor_set(v___x_1178_, 3, v_localInstances_1171_);
lean_ctor_set(v___x_1178_, 4, v_defEqCtx_x3f_1172_);
lean_ctor_set(v___x_1178_, 5, v_synthPendingDepth_1173_);
lean_ctor_set(v___x_1178_, 6, v_canUnfold_x3f_1174_);
lean_ctor_set_uint8(v___x_1178_, sizeof(void*)*7, v_trackZetaDelta_1169_);
lean_ctor_set_uint8(v___x_1178_, sizeof(void*)*7 + 1, v_univApprox_1175_);
lean_ctor_set_uint8(v___x_1178_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1176_);
lean_ctor_set_uint8(v___x_1178_, sizeof(void*)*7 + 3, v_cacheInferType_1177_);
lean_inc(v___y_1166_);
lean_inc_ref(v___y_1165_);
lean_inc(v___y_1164_);
v___x_1179_ = lean_apply_5(v_x_1162_, v___x_1178_, v___y_1164_, v___y_1165_, v___y_1166_, lean_box(0));
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___redArg___boxed(lean_object* v_lctx_1180_, lean_object* v_x_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___redArg(v_lctx_1180_, v_x_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
lean_dec(v___y_1183_);
lean_dec_ref(v___y_1182_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1(lean_object* v_00_u03b1_1188_, lean_object* v_lctx_1189_, lean_object* v_x_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___redArg(v_lctx_1189_, v_x_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___boxed(lean_object* v_00_u03b1_1197_, lean_object* v_lctx_1198_, lean_object* v_x_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1(v_00_u03b1_1197_, v_lctx_1198_, v_x_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq___lam__0(lean_object* v___x_1206_, uint8_t v_kind_1207_, lean_object* v_userName_1208_, lean_object* v_mvarId_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v___x_1215_; 
v___x_1215_ = l_Lean_Meta_mkFreshExprMVar(v___x_1206_, v_kind_1207_, v_userName_1208_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_object* v_a_1216_; lean_object* v___x_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1225_; 
v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
lean_inc_n(v_a_1216_, 2);
lean_dec_ref(v___x_1215_);
v___x_1217_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg(v_mvarId_1209_, v_a_1216_, v___y_1211_);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1225_ == 0)
{
lean_object* v_unused_1226_; 
v_unused_1226_ = lean_ctor_get(v___x_1217_, 0);
lean_dec(v_unused_1226_);
v___x_1219_ = v___x_1217_;
v_isShared_1220_ = v_isSharedCheck_1225_;
goto v_resetjp_1218_;
}
else
{
lean_dec(v___x_1217_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1225_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1221_; lean_object* v___x_1223_; 
v___x_1221_ = l_Lean_Expr_mvarId_x21(v_a_1216_);
lean_dec(v_a_1216_);
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 0, v___x_1221_);
v___x_1223_ = v___x_1219_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v___x_1221_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
else
{
lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1234_; 
lean_dec(v_mvarId_1209_);
v_a_1227_ = lean_ctor_get(v___x_1215_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1229_ = v___x_1215_;
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v___x_1215_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1232_; 
if (v_isShared_1230_ == 0)
{
v___x_1232_ = v___x_1229_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_a_1227_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq___lam__0___boxed(lean_object* v___x_1235_, lean_object* v_kind_1236_, lean_object* v_userName_1237_, lean_object* v_mvarId_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
uint8_t v_kind_boxed_1244_; lean_object* v_res_1245_; 
v_kind_boxed_1244_ = lean_unbox(v_kind_1236_);
v_res_1245_ = l_Lean_MVarId_replaceLocalDeclDefEq___lam__0(v___x_1235_, v_kind_boxed_1244_, v_userName_1237_, v_mvarId_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2_spec__2_spec__3_spec__4___redArg(lean_object* v_x_1246_, lean_object* v_x_1247_, lean_object* v_x_1248_, lean_object* v_x_1249_){
_start:
{
lean_object* v_ks_1250_; lean_object* v_vs_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1275_; 
v_ks_1250_ = lean_ctor_get(v_x_1246_, 0);
v_vs_1251_ = lean_ctor_get(v_x_1246_, 1);
v_isSharedCheck_1275_ = !lean_is_exclusive(v_x_1246_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1253_ = v_x_1246_;
v_isShared_1254_ = v_isSharedCheck_1275_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_vs_1251_);
lean_inc(v_ks_1250_);
lean_dec(v_x_1246_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1275_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1255_; uint8_t v___x_1256_; 
v___x_1255_ = lean_array_get_size(v_ks_1250_);
v___x_1256_ = lean_nat_dec_lt(v_x_1247_, v___x_1255_);
if (v___x_1256_ == 0)
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1260_; 
lean_dec(v_x_1247_);
v___x_1257_ = lean_array_push(v_ks_1250_, v_x_1248_);
v___x_1258_ = lean_array_push(v_vs_1251_, v_x_1249_);
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 1, v___x_1258_);
lean_ctor_set(v___x_1253_, 0, v___x_1257_);
v___x_1260_ = v___x_1253_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1257_);
lean_ctor_set(v_reuseFailAlloc_1261_, 1, v___x_1258_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
else
{
lean_object* v_k_x27_1262_; uint8_t v___x_1263_; 
v_k_x27_1262_ = lean_array_fget_borrowed(v_ks_1250_, v_x_1247_);
v___x_1263_ = l_Lean_instBEqFVarId_beq(v_x_1248_, v_k_x27_1262_);
if (v___x_1263_ == 0)
{
lean_object* v___x_1265_; 
if (v_isShared_1254_ == 0)
{
v___x_1265_ = v___x_1253_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_ks_1250_);
lean_ctor_set(v_reuseFailAlloc_1269_, 1, v_vs_1251_);
v___x_1265_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1266_ = lean_unsigned_to_nat(1u);
v___x_1267_ = lean_nat_add(v_x_1247_, v___x_1266_);
lean_dec(v_x_1247_);
v_x_1246_ = v___x_1265_;
v_x_1247_ = v___x_1267_;
goto _start;
}
}
else
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1273_; 
v___x_1270_ = lean_array_fset(v_ks_1250_, v_x_1247_, v_x_1248_);
v___x_1271_ = lean_array_fset(v_vs_1251_, v_x_1247_, v_x_1249_);
lean_dec(v_x_1247_);
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 1, v___x_1271_);
lean_ctor_set(v___x_1253_, 0, v___x_1270_);
v___x_1273_ = v___x_1253_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___x_1270_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v___x_1271_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2_spec__2_spec__3___redArg(lean_object* v_n_1276_, lean_object* v_k_1277_, lean_object* v_v_1278_){
_start:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1279_ = lean_unsigned_to_nat(0u);
v___x_1280_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2_spec__2_spec__3_spec__4___redArg(v_n_1276_, v___x_1279_, v_k_1277_, v_v_1278_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2_spec__2___redArg(lean_object* v_x_1281_, size_t v_x_1282_, size_t v_x_1283_, lean_object* v_x_1284_, lean_object* v_x_1285_){
_start:
{
if (lean_obj_tag(v_x_1281_) == 0)
{
lean_object* v_es_1286_; size_t v___x_1287_; size_t v___x_1288_; size_t v___x_1289_; size_t v___x_1290_; lean_object* v_j_1291_; lean_object* v___x_1292_; uint8_t v___x_1293_; 
v_es_1286_ = lean_ctor_get(v_x_1281_, 0);
v___x_1287_ = ((size_t)5ULL);
v___x_1288_ = ((size_t)1ULL);
v___x_1289_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_1290_ = lean_usize_land(v_x_1282_, v___x_1289_);
v_j_1291_ = lean_usize_to_nat(v___x_1290_);
v___x_1292_ = lean_array_get_size(v_es_1286_);
v___x_1293_ = lean_nat_dec_lt(v_j_1291_, v___x_1292_);
if (v___x_1293_ == 0)
{
lean_dec(v_j_1291_);
lean_dec(v_x_1285_);
lean_dec(v_x_1284_);
return v_x_1281_;
}
else
{
lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1330_; 
lean_inc_ref(v_es_1286_);
v_isSharedCheck_1330_ = !lean_is_exclusive(v_x_1281_);
if (v_isSharedCheck_1330_ == 0)
{
lean_object* v_unused_1331_; 
v_unused_1331_ = lean_ctor_get(v_x_1281_, 0);
lean_dec(v_unused_1331_);
v___x_1295_ = v_x_1281_;
v_isShared_1296_ = v_isSharedCheck_1330_;
goto v_resetjp_1294_;
}
else
{
lean_dec(v_x_1281_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1330_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v_v_1297_; lean_object* v___x_1298_; lean_object* v_xs_x27_1299_; lean_object* v___y_1301_; 
v_v_1297_ = lean_array_fget(v_es_1286_, v_j_1291_);
v___x_1298_ = lean_box(0);
v_xs_x27_1299_ = lean_array_fset(v_es_1286_, v_j_1291_, v___x_1298_);
switch(lean_obj_tag(v_v_1297_))
{
case 0:
{
lean_object* v_key_1306_; lean_object* v_val_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1317_; 
v_key_1306_ = lean_ctor_get(v_v_1297_, 0);
v_val_1307_ = lean_ctor_get(v_v_1297_, 1);
v_isSharedCheck_1317_ = !lean_is_exclusive(v_v_1297_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1309_ = v_v_1297_;
v_isShared_1310_ = v_isSharedCheck_1317_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_val_1307_);
lean_inc(v_key_1306_);
lean_dec(v_v_1297_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1317_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
uint8_t v___x_1311_; 
v___x_1311_ = l_Lean_instBEqFVarId_beq(v_x_1284_, v_key_1306_);
if (v___x_1311_ == 0)
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
lean_del_object(v___x_1309_);
v___x_1312_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1306_, v_val_1307_, v_x_1284_, v_x_1285_);
v___x_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1312_);
v___y_1301_ = v___x_1313_;
goto v___jp_1300_;
}
else
{
lean_object* v___x_1315_; 
lean_dec(v_val_1307_);
lean_dec(v_key_1306_);
if (v_isShared_1310_ == 0)
{
lean_ctor_set(v___x_1309_, 1, v_x_1285_);
lean_ctor_set(v___x_1309_, 0, v_x_1284_);
v___x_1315_ = v___x_1309_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_x_1284_);
lean_ctor_set(v_reuseFailAlloc_1316_, 1, v_x_1285_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
v___y_1301_ = v___x_1315_;
goto v___jp_1300_;
}
}
}
}
case 1:
{
lean_object* v_node_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1328_; 
v_node_1318_ = lean_ctor_get(v_v_1297_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v_v_1297_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1320_ = v_v_1297_;
v_isShared_1321_ = v_isSharedCheck_1328_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_node_1318_);
lean_dec(v_v_1297_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1328_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
size_t v___x_1322_; size_t v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1326_; 
v___x_1322_ = lean_usize_shift_right(v_x_1282_, v___x_1287_);
v___x_1323_ = lean_usize_add(v_x_1283_, v___x_1288_);
v___x_1324_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2_spec__2___redArg(v_node_1318_, v___x_1322_, v___x_1323_, v_x_1284_, v_x_1285_);
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 0, v___x_1324_);
v___x_1326_ = v___x_1320_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v___x_1324_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
v___y_1301_ = v___x_1326_;
goto v___jp_1300_;
}
}
}
default: 
{
lean_object* v___x_1329_; 
v___x_1329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1329_, 0, v_x_1284_);
lean_ctor_set(v___x_1329_, 1, v_x_1285_);
v___y_1301_ = v___x_1329_;
goto v___jp_1300_;
}
}
v___jp_1300_:
{
lean_object* v___x_1302_; lean_object* v___x_1304_; 
v___x_1302_ = lean_array_fset(v_xs_x27_1299_, v_j_1291_, v___y_1301_);
lean_dec(v_j_1291_);
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 0, v___x_1302_);
v___x_1304_ = v___x_1295_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v___x_1302_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
}
}
else
{
lean_object* v_ks_1332_; lean_object* v_vs_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1353_; 
v_ks_1332_ = lean_ctor_get(v_x_1281_, 0);
v_vs_1333_ = lean_ctor_get(v_x_1281_, 1);
v_isSharedCheck_1353_ = !lean_is_exclusive(v_x_1281_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1335_ = v_x_1281_;
v_isShared_1336_ = v_isSharedCheck_1353_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_vs_1333_);
lean_inc(v_ks_1332_);
lean_dec(v_x_1281_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1353_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_ks_1332_);
lean_ctor_set(v_reuseFailAlloc_1352_, 1, v_vs_1333_);
v___x_1338_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
lean_object* v_newNode_1339_; uint8_t v___y_1341_; size_t v___x_1347_; uint8_t v___x_1348_; 
v_newNode_1339_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2_spec__2_spec__3___redArg(v___x_1338_, v_x_1284_, v_x_1285_);
v___x_1347_ = ((size_t)7ULL);
v___x_1348_ = lean_usize_dec_le(v___x_1347_, v_x_1283_);
if (v___x_1348_ == 0)
{
lean_object* v___x_1349_; lean_object* v___x_1350_; uint8_t v___x_1351_; 
v___x_1349_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1339_);
v___x_1350_ = lean_unsigned_to_nat(4u);
v___x_1351_ = lean_nat_dec_lt(v___x_1349_, v___x_1350_);
lean_dec(v___x_1349_);
v___y_1341_ = v___x_1351_;
goto v___jp_1340_;
}
else
{
v___y_1341_ = v___x_1348_;
goto v___jp_1340_;
}
v___jp_1340_:
{
if (v___y_1341_ == 0)
{
lean_object* v_ks_1342_; lean_object* v_vs_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v_ks_1342_ = lean_ctor_get(v_newNode_1339_, 0);
lean_inc_ref(v_ks_1342_);
v_vs_1343_ = lean_ctor_get(v_newNode_1339_, 1);
lean_inc_ref(v_vs_1343_);
lean_dec_ref(v_newNode_1339_);
v___x_1344_ = lean_unsigned_to_nat(0u);
v___x_1345_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__2);
v___x_1346_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2_spec__2_spec__4___redArg(v_x_1283_, v_ks_1342_, v_vs_1343_, v___x_1344_, v___x_1345_);
lean_dec_ref(v_vs_1343_);
lean_dec_ref(v_ks_1342_);
return v___x_1346_;
}
else
{
return v_newNode_1339_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2_spec__2_spec__4___redArg(size_t v_depth_1354_, lean_object* v_keys_1355_, lean_object* v_vals_1356_, lean_object* v_i_1357_, lean_object* v_entries_1358_){
_start:
{
lean_object* v___x_1359_; uint8_t v___x_1360_; 
v___x_1359_ = lean_array_get_size(v_keys_1355_);
v___x_1360_ = lean_nat_dec_lt(v_i_1357_, v___x_1359_);
if (v___x_1360_ == 0)
{
lean_dec(v_i_1357_);
return v_entries_1358_;
}
else
{
lean_object* v_k_1361_; lean_object* v_v_1362_; uint64_t v___x_1363_; size_t v_h_1364_; size_t v___x_1365_; lean_object* v___x_1366_; size_t v___x_1367_; size_t v___x_1368_; size_t v___x_1369_; size_t v_h_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
v_k_1361_ = lean_array_fget_borrowed(v_keys_1355_, v_i_1357_);
v_v_1362_ = lean_array_fget_borrowed(v_vals_1356_, v_i_1357_);
v___x_1363_ = l_Lean_instHashableFVarId_hash(v_k_1361_);
v_h_1364_ = lean_uint64_to_usize(v___x_1363_);
v___x_1365_ = ((size_t)5ULL);
v___x_1366_ = lean_unsigned_to_nat(1u);
v___x_1367_ = ((size_t)1ULL);
v___x_1368_ = lean_usize_sub(v_depth_1354_, v___x_1367_);
v___x_1369_ = lean_usize_mul(v___x_1365_, v___x_1368_);
v_h_1370_ = lean_usize_shift_right(v_h_1364_, v___x_1369_);
v___x_1371_ = lean_nat_add(v_i_1357_, v___x_1366_);
lean_dec(v_i_1357_);
lean_inc(v_v_1362_);
lean_inc(v_k_1361_);
v___x_1372_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2_spec__2___redArg(v_entries_1358_, v_h_1370_, v_depth_1354_, v_k_1361_, v_v_1362_);
v_i_1357_ = v___x_1371_;
v_entries_1358_ = v___x_1372_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2_spec__2_spec__4___redArg___boxed(lean_object* v_depth_1374_, lean_object* v_keys_1375_, lean_object* v_vals_1376_, lean_object* v_i_1377_, lean_object* v_entries_1378_){
_start:
{
size_t v_depth_boxed_1379_; lean_object* v_res_1380_; 
v_depth_boxed_1379_ = lean_unbox_usize(v_depth_1374_);
lean_dec(v_depth_1374_);
v_res_1380_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2_spec__2_spec__4___redArg(v_depth_boxed_1379_, v_keys_1375_, v_vals_1376_, v_i_1377_, v_entries_1378_);
lean_dec_ref(v_vals_1376_);
lean_dec_ref(v_keys_1375_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2_spec__2___redArg___boxed(lean_object* v_x_1381_, lean_object* v_x_1382_, lean_object* v_x_1383_, lean_object* v_x_1384_, lean_object* v_x_1385_){
_start:
{
size_t v_x_2238__boxed_1386_; size_t v_x_2239__boxed_1387_; lean_object* v_res_1388_; 
v_x_2238__boxed_1386_ = lean_unbox_usize(v_x_1382_);
lean_dec(v_x_1382_);
v_x_2239__boxed_1387_ = lean_unbox_usize(v_x_1383_);
lean_dec(v_x_1383_);
v_res_1388_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2_spec__2___redArg(v_x_1381_, v_x_2238__boxed_1386_, v_x_2239__boxed_1387_, v_x_1384_, v_x_1385_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2___redArg(lean_object* v_x_1389_, lean_object* v_x_1390_, lean_object* v_x_1391_){
_start:
{
uint64_t v___x_1392_; size_t v___x_1393_; size_t v___x_1394_; lean_object* v___x_1395_; 
v___x_1392_ = l_Lean_instHashableFVarId_hash(v_x_1390_);
v___x_1393_ = lean_uint64_to_usize(v___x_1392_);
v___x_1394_ = ((size_t)1ULL);
v___x_1395_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2_spec__2___redArg(v_x_1389_, v___x_1393_, v___x_1394_, v_x_1390_, v_x_1391_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq___lam__1(lean_object* v_fvarId_1396_, lean_object* v_typeNew_1397_, lean_object* v_mvarId_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v___x_1404_; 
lean_inc(v_fvarId_1396_);
v___x_1404_ = l_Lean_FVarId_getType___redArg(v_fvarId_1396_, v___y_1399_, v___y_1401_, v___y_1402_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1469_; 
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1407_ = v___x_1404_;
v_isShared_1408_ = v_isSharedCheck_1469_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1404_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1469_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
uint8_t v___x_1409_; 
v___x_1409_ = lean_expr_equal(v_typeNew_1397_, v_a_1405_);
lean_dec(v_a_1405_);
if (v___x_1409_ == 0)
{
lean_object* v___x_1410_; 
lean_del_object(v___x_1407_);
lean_inc(v_mvarId_1398_);
v___x_1410_ = l_Lean_MVarId_getDecl(v_mvarId_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v_a_1411_; lean_object* v___y_1413_; lean_object* v_lctx_1425_; lean_object* v_fvarIdToDecl_1426_; lean_object* v_decls_1427_; lean_object* v_auxDeclToFullName_1428_; lean_object* v___x_1429_; 
v_a_1411_ = lean_ctor_get(v___x_1410_, 0);
lean_inc(v_a_1411_);
lean_dec_ref(v___x_1410_);
v_lctx_1425_ = lean_ctor_get(v___y_1399_, 2);
lean_inc_ref_n(v_lctx_1425_, 2);
v_fvarIdToDecl_1426_ = lean_ctor_get(v_lctx_1425_, 0);
v_decls_1427_ = lean_ctor_get(v_lctx_1425_, 1);
v_auxDeclToFullName_1428_ = lean_ctor_get(v_lctx_1425_, 2);
lean_inc(v_fvarId_1396_);
v___x_1429_ = lean_local_ctx_find(v_lctx_1425_, v_fvarId_1396_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_dec_ref(v_typeNew_1397_);
v___y_1413_ = v_lctx_1425_;
goto v___jp_1412_;
}
else
{
lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1454_; 
lean_inc(v_auxDeclToFullName_1428_);
lean_inc_ref(v_decls_1427_);
lean_inc_ref(v_fvarIdToDecl_1426_);
v_isSharedCheck_1454_ = !lean_is_exclusive(v_lctx_1425_);
if (v_isSharedCheck_1454_ == 0)
{
lean_object* v_unused_1455_; lean_object* v_unused_1456_; lean_object* v_unused_1457_; 
v_unused_1455_ = lean_ctor_get(v_lctx_1425_, 2);
lean_dec(v_unused_1455_);
v_unused_1456_ = lean_ctor_get(v_lctx_1425_, 1);
lean_dec(v_unused_1456_);
v_unused_1457_ = lean_ctor_get(v_lctx_1425_, 0);
lean_dec(v_unused_1457_);
v___x_1431_ = v_lctx_1425_;
v_isShared_1432_ = v_isSharedCheck_1454_;
goto v_resetjp_1430_;
}
else
{
lean_dec(v_lctx_1425_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1454_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v_val_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1453_; 
v_val_1433_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1435_ = v___x_1429_;
v_isShared_1436_ = v_isSharedCheck_1453_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_val_1433_);
lean_dec(v___x_1429_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1453_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1437_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1449_; lean_object* v_fvarId_1452_; 
v___x_1437_ = l_Lean_LocalDecl_setType(v_val_1433_, v_typeNew_1397_);
v_fvarId_1452_ = lean_ctor_get(v___x_1437_, 1);
lean_inc(v_fvarId_1452_);
v___y_1449_ = v_fvarId_1452_;
goto v___jp_1448_;
v___jp_1438_:
{
lean_object* v___x_1442_; 
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 0, v___x_1437_);
v___x_1442_ = v___x_1435_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1437_);
v___x_1442_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
lean_object* v___x_1443_; lean_object* v___x_1445_; 
v___x_1443_ = l_Lean_PersistentArray_set___redArg(v_decls_1427_, v___y_1440_, v___x_1442_);
lean_dec(v___y_1440_);
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 1, v___x_1443_);
lean_ctor_set(v___x_1431_, 0, v___y_1439_);
v___x_1445_ = v___x_1431_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___y_1439_);
lean_ctor_set(v_reuseFailAlloc_1446_, 1, v___x_1443_);
lean_ctor_set(v_reuseFailAlloc_1446_, 2, v_auxDeclToFullName_1428_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
v___y_1413_ = v___x_1445_;
goto v___jp_1412_;
}
}
}
v___jp_1448_:
{
lean_object* v___x_1450_; lean_object* v_index_1451_; 
lean_inc_ref(v___x_1437_);
v___x_1450_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2___redArg(v_fvarIdToDecl_1426_, v___y_1449_, v___x_1437_);
v_index_1451_ = lean_ctor_get(v___x_1437_, 0);
lean_inc(v_index_1451_);
v___y_1439_ = v___x_1450_;
v___y_1440_ = v_index_1451_;
goto v___jp_1438_;
}
}
}
}
v___jp_1412_:
{
lean_object* v_userName_1414_; lean_object* v_type_1415_; uint8_t v_kind_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___f_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v_userName_1414_ = lean_ctor_get(v_a_1411_, 0);
lean_inc(v_userName_1414_);
v_type_1415_ = lean_ctor_get(v_a_1411_, 2);
lean_inc_ref(v_type_1415_);
v_kind_1416_ = lean_ctor_get_uint8(v_a_1411_, sizeof(void*)*7);
lean_dec(v_a_1411_);
lean_inc_ref(v___y_1413_);
v___x_1417_ = l_Lean_LocalContext_get_x21(v___y_1413_, v_fvarId_1396_);
v___x_1418_ = lean_box(0);
v___x_1419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1417_);
lean_ctor_set(v___x_1419_, 1, v___x_1418_);
v___x_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1420_, 0, v_type_1415_);
v___x_1421_ = lean_box(v_kind_1416_);
v___f_1422_ = lean_alloc_closure((void*)(l_Lean_MVarId_replaceLocalDeclDefEq___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1422_, 0, v___x_1420_);
lean_closure_set(v___f_1422_, 1, v___x_1421_);
lean_closure_set(v___f_1422_, 2, v_userName_1414_);
lean_closure_set(v___f_1422_, 3, v_mvarId_1398_);
v___x_1423_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___boxed), 8, 3);
lean_closure_set(v___x_1423_, 0, lean_box(0));
lean_closure_set(v___x_1423_, 1, v___x_1419_);
lean_closure_set(v___x_1423_, 2, v___f_1422_);
v___x_1424_ = l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___redArg(v___y_1413_, v___x_1423_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
lean_dec_ref(v___y_1399_);
return v___x_1424_;
}
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
lean_dec_ref(v___y_1399_);
lean_dec(v_mvarId_1398_);
lean_dec_ref(v_typeNew_1397_);
lean_dec(v_fvarId_1396_);
v_a_1458_ = lean_ctor_get(v___x_1410_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___x_1410_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1410_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1458_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
}
else
{
lean_object* v___x_1467_; 
lean_dec_ref(v___y_1399_);
lean_dec_ref(v_typeNew_1397_);
lean_dec(v_fvarId_1396_);
if (v_isShared_1408_ == 0)
{
lean_ctor_set(v___x_1407_, 0, v_mvarId_1398_);
v___x_1467_ = v___x_1407_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_mvarId_1398_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
}
else
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
lean_dec_ref(v___y_1399_);
lean_dec(v_mvarId_1398_);
lean_dec_ref(v_typeNew_1397_);
lean_dec(v_fvarId_1396_);
v_a_1470_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1472_ = v___x_1404_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1404_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1473_ == 0)
{
v___x_1475_ = v___x_1472_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1470_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq___lam__1___boxed(lean_object* v_fvarId_1478_, lean_object* v_typeNew_1479_, lean_object* v_mvarId_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l_Lean_MVarId_replaceLocalDeclDefEq___lam__1(v_fvarId_1478_, v_typeNew_1479_, v_mvarId_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
lean_dec(v___y_1482_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq(lean_object* v_mvarId_1487_, lean_object* v_fvarId_1488_, lean_object* v_typeNew_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_){
_start:
{
lean_object* v___f_1495_; lean_object* v___x_1496_; 
lean_inc(v_mvarId_1487_);
v___f_1495_ = lean_alloc_closure((void*)(l_Lean_MVarId_replaceLocalDeclDefEq___lam__1___boxed), 8, 3);
lean_closure_set(v___f_1495_, 0, v_fvarId_1488_);
lean_closure_set(v___f_1495_, 1, v_typeNew_1489_);
lean_closure_set(v___f_1495_, 2, v_mvarId_1487_);
v___x_1496_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_1487_, v___f_1495_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq___boxed(lean_object* v_mvarId_1497_, lean_object* v_fvarId_1498_, lean_object* v_typeNew_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_mvarId_1497_, v_fvarId_1498_, v_typeNew_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_);
lean_dec(v_a_1503_);
lean_dec_ref(v_a_1502_);
lean_dec(v_a_1501_);
lean_dec_ref(v_a_1500_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2(lean_object* v_00_u03b2_1506_, lean_object* v_x_1507_, lean_object* v_x_1508_, lean_object* v_x_1509_){
_start:
{
lean_object* v___x_1510_; 
v___x_1510_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2___redArg(v_x_1507_, v_x_1508_, v_x_1509_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2_spec__2(lean_object* v_00_u03b2_1511_, lean_object* v_x_1512_, size_t v_x_1513_, size_t v_x_1514_, lean_object* v_x_1515_, lean_object* v_x_1516_){
_start:
{
lean_object* v___x_1517_; 
v___x_1517_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2_spec__2___redArg(v_x_1512_, v_x_1513_, v_x_1514_, v_x_1515_, v_x_1516_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2_spec__2___boxed(lean_object* v_00_u03b2_1518_, lean_object* v_x_1519_, lean_object* v_x_1520_, lean_object* v_x_1521_, lean_object* v_x_1522_, lean_object* v_x_1523_){
_start:
{
size_t v_x_2602__boxed_1524_; size_t v_x_2603__boxed_1525_; lean_object* v_res_1526_; 
v_x_2602__boxed_1524_ = lean_unbox_usize(v_x_1520_);
lean_dec(v_x_1520_);
v_x_2603__boxed_1525_ = lean_unbox_usize(v_x_1521_);
lean_dec(v_x_1521_);
v_res_1526_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2_spec__2(v_00_u03b2_1518_, v_x_1519_, v_x_2602__boxed_1524_, v_x_2603__boxed_1525_, v_x_1522_, v_x_1523_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2_spec__2_spec__3(lean_object* v_00_u03b2_1527_, lean_object* v_n_1528_, lean_object* v_k_1529_, lean_object* v_v_1530_){
_start:
{
lean_object* v___x_1531_; 
v___x_1531_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2_spec__2_spec__3___redArg(v_n_1528_, v_k_1529_, v_v_1530_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2_spec__2_spec__4(lean_object* v_00_u03b2_1532_, size_t v_depth_1533_, lean_object* v_keys_1534_, lean_object* v_vals_1535_, lean_object* v_heq_1536_, lean_object* v_i_1537_, lean_object* v_entries_1538_){
_start:
{
lean_object* v___x_1539_; 
v___x_1539_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2_spec__2_spec__4___redArg(v_depth_1533_, v_keys_1534_, v_vals_1535_, v_i_1537_, v_entries_1538_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1540_, lean_object* v_depth_1541_, lean_object* v_keys_1542_, lean_object* v_vals_1543_, lean_object* v_heq_1544_, lean_object* v_i_1545_, lean_object* v_entries_1546_){
_start:
{
size_t v_depth_boxed_1547_; lean_object* v_res_1548_; 
v_depth_boxed_1547_ = lean_unbox_usize(v_depth_1541_);
lean_dec(v_depth_1541_);
v_res_1548_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2_spec__2_spec__4(v_00_u03b2_1540_, v_depth_boxed_1547_, v_keys_1542_, v_vals_1543_, v_heq_1544_, v_i_1545_, v_entries_1546_);
lean_dec_ref(v_vals_1543_);
lean_dec_ref(v_keys_1542_);
return v_res_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_1549_, lean_object* v_x_1550_, lean_object* v_x_1551_, lean_object* v_x_1552_, lean_object* v_x_1553_){
_start:
{
lean_object* v___x_1554_; 
v___x_1554_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2_spec__2_spec__3_spec__4___redArg(v_x_1550_, v_x_1551_, v_x_1552_, v_x_1553_);
return v___x_1554_;
}
}
static lean_object* _init_l_Lean_MVarId_change___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1556_ = ((lean_object*)(l_Lean_MVarId_change___lam__0___closed__0));
v___x_1557_ = l_Lean_stringToMessageData(v___x_1556_);
return v___x_1557_;
}
}
static lean_object* _init_l_Lean_MVarId_change___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1559_ = ((lean_object*)(l_Lean_MVarId_change___lam__0___closed__2));
v___x_1560_ = l_Lean_stringToMessageData(v___x_1559_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_change___lam__0(lean_object* v_mvarId_1561_, uint8_t v_checkDefEq_1562_, lean_object* v_targetNew_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_){
_start:
{
lean_object* v___x_1569_; 
lean_inc(v_mvarId_1561_);
v___x_1569_ = l_Lean_MVarId_getType(v_mvarId_1561_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_);
if (lean_obj_tag(v___x_1569_) == 0)
{
if (v_checkDefEq_1562_ == 0)
{
lean_object* v___x_1570_; 
lean_dec_ref(v___x_1569_);
v___x_1570_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_1561_, v_targetNew_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_);
return v___x_1570_;
}
else
{
lean_object* v_a_1571_; lean_object* v___x_1572_; 
v_a_1571_ = lean_ctor_get(v___x_1569_, 0);
lean_inc_n(v_a_1571_, 2);
lean_dec_ref(v___x_1569_);
lean_inc_ref(v_targetNew_1563_);
v___x_1572_ = l_Lean_Meta_isExprDefEq(v_a_1571_, v_targetNew_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v_a_1573_; uint8_t v___x_1574_; 
v_a_1573_ = lean_ctor_get(v___x_1572_, 0);
lean_inc(v_a_1573_);
lean_dec_ref(v___x_1572_);
v___x_1574_ = lean_unbox(v_a_1573_);
lean_dec(v_a_1573_);
if (v___x_1574_ == 0)
{
lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1575_ = ((lean_object*)(l_Lean_MVarId_replaceTargetDefEq___closed__1));
v___x_1576_ = lean_obj_once(&l_Lean_MVarId_change___lam__0___closed__1, &l_Lean_MVarId_change___lam__0___closed__1_once, _init_l_Lean_MVarId_change___lam__0___closed__1);
lean_inc_ref(v_targetNew_1563_);
v___x_1577_ = l_Lean_indentExpr(v_targetNew_1563_);
v___x_1578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1576_);
lean_ctor_set(v___x_1578_, 1, v___x_1577_);
v___x_1579_ = lean_obj_once(&l_Lean_MVarId_change___lam__0___closed__3, &l_Lean_MVarId_change___lam__0___closed__3_once, _init_l_Lean_MVarId_change___lam__0___closed__3);
v___x_1580_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1578_);
lean_ctor_set(v___x_1580_, 1, v___x_1579_);
v___x_1581_ = l_Lean_indentExpr(v_a_1571_);
v___x_1582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1580_);
lean_ctor_set(v___x_1582_, 1, v___x_1581_);
v___x_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1582_);
lean_inc(v_mvarId_1561_);
v___x_1584_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1575_, v_mvarId_1561_, v___x_1583_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v___x_1585_; 
lean_dec_ref(v___x_1584_);
v___x_1585_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_1561_, v_targetNew_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_);
return v___x_1585_;
}
else
{
lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1593_; 
lean_dec_ref(v_targetNew_1563_);
lean_dec(v_mvarId_1561_);
v_a_1586_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1588_ = v___x_1584_;
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1584_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1591_; 
if (v_isShared_1589_ == 0)
{
v___x_1591_ = v___x_1588_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_a_1586_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
}
else
{
lean_object* v___x_1594_; 
lean_dec(v_a_1571_);
v___x_1594_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_1561_, v_targetNew_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_);
return v___x_1594_;
}
}
else
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1602_; 
lean_dec(v_a_1571_);
lean_dec_ref(v_targetNew_1563_);
lean_dec(v_mvarId_1561_);
v_a_1595_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1597_ = v___x_1572_;
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1572_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1600_; 
if (v_isShared_1598_ == 0)
{
v___x_1600_ = v___x_1597_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_a_1595_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
}
else
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1610_; 
lean_dec_ref(v_targetNew_1563_);
lean_dec(v_mvarId_1561_);
v_a_1603_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1605_ = v___x_1569_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1569_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1608_; 
if (v_isShared_1606_ == 0)
{
v___x_1608_ = v___x_1605_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1603_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_change___lam__0___boxed(lean_object* v_mvarId_1611_, lean_object* v_checkDefEq_1612_, lean_object* v_targetNew_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_){
_start:
{
uint8_t v_checkDefEq_boxed_1619_; lean_object* v_res_1620_; 
v_checkDefEq_boxed_1619_ = lean_unbox(v_checkDefEq_1612_);
v_res_1620_ = l_Lean_MVarId_change___lam__0(v_mvarId_1611_, v_checkDefEq_boxed_1619_, v_targetNew_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_change(lean_object* v_mvarId_1621_, lean_object* v_targetNew_1622_, uint8_t v_checkDefEq_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_){
_start:
{
lean_object* v___x_1629_; lean_object* v___f_1630_; lean_object* v___x_1631_; 
v___x_1629_ = lean_box(v_checkDefEq_1623_);
lean_inc(v_mvarId_1621_);
v___f_1630_ = lean_alloc_closure((void*)(l_Lean_MVarId_change___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1630_, 0, v_mvarId_1621_);
lean_closure_set(v___f_1630_, 1, v___x_1629_);
lean_closure_set(v___f_1630_, 2, v_targetNew_1622_);
v___x_1631_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_1621_, v___f_1630_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_change___boxed(lean_object* v_mvarId_1632_, lean_object* v_targetNew_1633_, lean_object* v_checkDefEq_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_){
_start:
{
uint8_t v_checkDefEq_boxed_1640_; lean_object* v_res_1641_; 
v_checkDefEq_boxed_1640_ = lean_unbox(v_checkDefEq_1634_);
v_res_1641_ = l_Lean_MVarId_change(v_mvarId_1632_, v_targetNew_1633_, v_checkDefEq_boxed_1640_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_);
lean_dec(v_a_1638_);
lean_dec_ref(v_a_1637_);
lean_dec(v_a_1636_);
lean_dec_ref(v_a_1635_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0___redArg(lean_object* v_t_1642_, lean_object* v___y_1643_){
_start:
{
lean_object* v___x_1645_; lean_object* v_infoState_1646_; uint8_t v_enabled_1647_; 
v___x_1645_ = lean_st_ref_get(v___y_1643_);
v_infoState_1646_ = lean_ctor_get(v___x_1645_, 7);
lean_inc_ref(v_infoState_1646_);
lean_dec(v___x_1645_);
v_enabled_1647_ = lean_ctor_get_uint8(v_infoState_1646_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1646_);
if (v_enabled_1647_ == 0)
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
lean_dec_ref(v_t_1642_);
v___x_1648_ = lean_box(0);
v___x_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1648_);
return v___x_1649_;
}
else
{
lean_object* v___x_1650_; lean_object* v_infoState_1651_; lean_object* v_env_1652_; lean_object* v_nextMacroScope_1653_; lean_object* v_ngen_1654_; lean_object* v_auxDeclNGen_1655_; lean_object* v_traceState_1656_; lean_object* v_cache_1657_; lean_object* v_messages_1658_; lean_object* v_snapshotTasks_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1681_; 
v___x_1650_ = lean_st_ref_take(v___y_1643_);
v_infoState_1651_ = lean_ctor_get(v___x_1650_, 7);
v_env_1652_ = lean_ctor_get(v___x_1650_, 0);
v_nextMacroScope_1653_ = lean_ctor_get(v___x_1650_, 1);
v_ngen_1654_ = lean_ctor_get(v___x_1650_, 2);
v_auxDeclNGen_1655_ = lean_ctor_get(v___x_1650_, 3);
v_traceState_1656_ = lean_ctor_get(v___x_1650_, 4);
v_cache_1657_ = lean_ctor_get(v___x_1650_, 5);
v_messages_1658_ = lean_ctor_get(v___x_1650_, 6);
v_snapshotTasks_1659_ = lean_ctor_get(v___x_1650_, 8);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1661_ = v___x_1650_;
v_isShared_1662_ = v_isSharedCheck_1681_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_snapshotTasks_1659_);
lean_inc(v_infoState_1651_);
lean_inc(v_messages_1658_);
lean_inc(v_cache_1657_);
lean_inc(v_traceState_1656_);
lean_inc(v_auxDeclNGen_1655_);
lean_inc(v_ngen_1654_);
lean_inc(v_nextMacroScope_1653_);
lean_inc(v_env_1652_);
lean_dec(v___x_1650_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1681_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
uint8_t v_enabled_1663_; lean_object* v_assignment_1664_; lean_object* v_lazyAssignment_1665_; lean_object* v_trees_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1680_; 
v_enabled_1663_ = lean_ctor_get_uint8(v_infoState_1651_, sizeof(void*)*3);
v_assignment_1664_ = lean_ctor_get(v_infoState_1651_, 0);
v_lazyAssignment_1665_ = lean_ctor_get(v_infoState_1651_, 1);
v_trees_1666_ = lean_ctor_get(v_infoState_1651_, 2);
v_isSharedCheck_1680_ = !lean_is_exclusive(v_infoState_1651_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1668_ = v_infoState_1651_;
v_isShared_1669_ = v_isSharedCheck_1680_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_trees_1666_);
lean_inc(v_lazyAssignment_1665_);
lean_inc(v_assignment_1664_);
lean_dec(v_infoState_1651_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1680_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1670_; lean_object* v___x_1672_; 
v___x_1670_ = l_Lean_PersistentArray_push___redArg(v_trees_1666_, v_t_1642_);
if (v_isShared_1669_ == 0)
{
lean_ctor_set(v___x_1668_, 2, v___x_1670_);
v___x_1672_ = v___x_1668_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_assignment_1664_);
lean_ctor_set(v_reuseFailAlloc_1679_, 1, v_lazyAssignment_1665_);
lean_ctor_set(v_reuseFailAlloc_1679_, 2, v___x_1670_);
lean_ctor_set_uint8(v_reuseFailAlloc_1679_, sizeof(void*)*3, v_enabled_1663_);
v___x_1672_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
lean_object* v___x_1674_; 
if (v_isShared_1662_ == 0)
{
lean_ctor_set(v___x_1661_, 7, v___x_1672_);
v___x_1674_ = v___x_1661_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_env_1652_);
lean_ctor_set(v_reuseFailAlloc_1678_, 1, v_nextMacroScope_1653_);
lean_ctor_set(v_reuseFailAlloc_1678_, 2, v_ngen_1654_);
lean_ctor_set(v_reuseFailAlloc_1678_, 3, v_auxDeclNGen_1655_);
lean_ctor_set(v_reuseFailAlloc_1678_, 4, v_traceState_1656_);
lean_ctor_set(v_reuseFailAlloc_1678_, 5, v_cache_1657_);
lean_ctor_set(v_reuseFailAlloc_1678_, 6, v_messages_1658_);
lean_ctor_set(v_reuseFailAlloc_1678_, 7, v___x_1672_);
lean_ctor_set(v_reuseFailAlloc_1678_, 8, v_snapshotTasks_1659_);
v___x_1674_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1675_ = lean_st_ref_set(v___y_1643_, v___x_1674_);
v___x_1676_ = lean_box(0);
v___x_1677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1676_);
return v___x_1677_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0___redArg___boxed(lean_object* v_t_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0___redArg(v_t_1682_, v___y_1683_);
lean_dec(v___y_1683_);
return v_res_1685_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1686_ = lean_unsigned_to_nat(32u);
v___x_1687_ = lean_mk_empty_array_with_capacity(v___x_1686_);
v___x_1688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1687_);
return v___x_1688_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__1(void){
_start:
{
size_t v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1689_ = ((size_t)5ULL);
v___x_1690_ = lean_unsigned_to_nat(0u);
v___x_1691_ = lean_unsigned_to_nat(32u);
v___x_1692_ = lean_mk_empty_array_with_capacity(v___x_1691_);
v___x_1693_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__0);
v___x_1694_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1694_, 0, v___x_1693_);
lean_ctor_set(v___x_1694_, 1, v___x_1692_);
lean_ctor_set(v___x_1694_, 2, v___x_1690_);
lean_ctor_set(v___x_1694_, 3, v___x_1690_);
lean_ctor_set_usize(v___x_1694_, 4, v___x_1689_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0(lean_object* v_t_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
lean_object* v___x_1701_; lean_object* v_infoState_1702_; uint8_t v_enabled_1703_; 
v___x_1701_ = lean_st_ref_get(v___y_1699_);
v_infoState_1702_ = lean_ctor_get(v___x_1701_, 7);
lean_inc_ref(v_infoState_1702_);
lean_dec(v___x_1701_);
v_enabled_1703_ = lean_ctor_get_uint8(v_infoState_1702_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1702_);
if (v_enabled_1703_ == 0)
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
lean_dec_ref(v_t_1695_);
v___x_1704_ = lean_box(0);
v___x_1705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1704_);
return v___x_1705_;
}
else
{
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1706_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__1);
v___x_1707_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1707_, 0, v_t_1695_);
lean_ctor_set(v___x_1707_, 1, v___x_1706_);
v___x_1708_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0___redArg(v___x_1707_, v___y_1699_);
return v___x_1708_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___boxed(lean_object* v_t_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0(v_t_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_withReverted_spec__1(lean_object* v_as_1716_, size_t v_sz_1717_, size_t v_i_1718_, lean_object* v_b_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v_a_1726_; uint8_t v___x_1730_; 
v___x_1730_ = lean_usize_dec_lt(v_i_1718_, v_sz_1717_);
if (v___x_1730_ == 0)
{
lean_object* v___x_1731_; 
v___x_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1731_, 0, v_b_1719_);
return v___x_1731_;
}
else
{
lean_object* v_array_1732_; lean_object* v_start_1733_; lean_object* v_stop_1734_; uint8_t v___x_1735_; 
v_array_1732_ = lean_ctor_get(v_b_1719_, 0);
v_start_1733_ = lean_ctor_get(v_b_1719_, 1);
v_stop_1734_ = lean_ctor_get(v_b_1719_, 2);
v___x_1735_ = lean_nat_dec_lt(v_start_1733_, v_stop_1734_);
if (v___x_1735_ == 0)
{
lean_object* v___x_1736_; 
v___x_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1736_, 0, v_b_1719_);
return v___x_1736_;
}
else
{
lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1775_; 
lean_inc(v_stop_1734_);
lean_inc(v_start_1733_);
lean_inc_ref(v_array_1732_);
v_isSharedCheck_1775_ = !lean_is_exclusive(v_b_1719_);
if (v_isSharedCheck_1775_ == 0)
{
lean_object* v_unused_1776_; lean_object* v_unused_1777_; lean_object* v_unused_1778_; 
v_unused_1776_ = lean_ctor_get(v_b_1719_, 2);
lean_dec(v_unused_1776_);
v_unused_1777_ = lean_ctor_get(v_b_1719_, 1);
lean_dec(v_unused_1777_);
v_unused_1778_ = lean_ctor_get(v_b_1719_, 0);
lean_dec(v_unused_1778_);
v___x_1738_ = v_b_1719_;
v_isShared_1739_ = v_isSharedCheck_1775_;
goto v_resetjp_1737_;
}
else
{
lean_dec(v_b_1719_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1775_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v_a_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1745_; 
v_a_1740_ = lean_array_uget(v_as_1716_, v_i_1718_);
v___x_1741_ = lean_array_fget(v_array_1732_, v_start_1733_);
v___x_1742_ = lean_unsigned_to_nat(1u);
v___x_1743_ = lean_nat_add(v_start_1733_, v___x_1742_);
lean_dec(v_start_1733_);
if (v_isShared_1739_ == 0)
{
lean_ctor_set(v___x_1738_, 1, v___x_1743_);
v___x_1745_ = v___x_1738_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_array_1732_);
lean_ctor_set(v_reuseFailAlloc_1774_, 1, v___x_1743_);
lean_ctor_set(v_reuseFailAlloc_1774_, 2, v_stop_1734_);
v___x_1745_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
if (lean_obj_tag(v_a_1740_) == 1)
{
lean_object* v_val_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1773_; 
v_val_1746_ = lean_ctor_get(v_a_1740_, 0);
v_isSharedCheck_1773_ = !lean_is_exclusive(v_a_1740_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1748_ = v_a_1740_;
v_isShared_1749_ = v_isSharedCheck_1773_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_val_1746_);
lean_dec(v_a_1740_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1773_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1750_; 
lean_inc(v___x_1741_);
v___x_1750_ = l_Lean_FVarId_getUserName___redArg(v___x_1741_, v___y_1720_, v___y_1722_, v___y_1723_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v_a_1751_; lean_object* v___x_1752_; lean_object* v___x_1754_; 
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
lean_inc(v_a_1751_);
lean_dec_ref(v___x_1750_);
v___x_1752_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1752_, 0, v_a_1751_);
lean_ctor_set(v___x_1752_, 1, v___x_1741_);
lean_ctor_set(v___x_1752_, 2, v_val_1746_);
if (v_isShared_1749_ == 0)
{
lean_ctor_set_tag(v___x_1748_, 11);
lean_ctor_set(v___x_1748_, 0, v___x_1752_);
v___x_1754_ = v___x_1748_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v___x_1752_);
v___x_1754_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
lean_object* v___x_1755_; 
v___x_1755_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0(v___x_1754_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_dec_ref(v___x_1755_);
v_a_1726_ = v___x_1745_;
goto v___jp_1725_;
}
else
{
lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1763_; 
lean_dec_ref(v___x_1745_);
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1758_ = v___x_1755_;
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1755_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1761_; 
if (v_isShared_1759_ == 0)
{
v___x_1761_ = v___x_1758_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_a_1756_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
}
}
else
{
lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1772_; 
lean_del_object(v___x_1748_);
lean_dec(v_val_1746_);
lean_dec_ref(v___x_1745_);
lean_dec(v___x_1741_);
v_a_1765_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1767_ = v___x_1750_;
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v___x_1750_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1770_; 
if (v_isShared_1768_ == 0)
{
v___x_1770_ = v___x_1767_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_a_1765_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
}
}
else
{
lean_dec(v___x_1741_);
lean_dec(v_a_1740_);
v_a_1726_ = v___x_1745_;
goto v___jp_1725_;
}
}
}
}
}
v___jp_1725_:
{
size_t v___x_1727_; size_t v___x_1728_; 
v___x_1727_ = ((size_t)1ULL);
v___x_1728_ = lean_usize_add(v_i_1718_, v___x_1727_);
v_i_1718_ = v___x_1728_;
v_b_1719_ = v_a_1726_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_withReverted_spec__1___boxed(lean_object* v_as_1779_, lean_object* v_sz_1780_, lean_object* v_i_1781_, lean_object* v_b_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
size_t v_sz_boxed_1788_; size_t v_i_boxed_1789_; lean_object* v_res_1790_; 
v_sz_boxed_1788_ = lean_unbox_usize(v_sz_1780_);
lean_dec(v_sz_1780_);
v_i_boxed_1789_ = lean_unbox_usize(v_i_1781_);
lean_dec(v_i_1781_);
v_res_1790_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_withReverted_spec__1(v_as_1779_, v_sz_boxed_1788_, v_i_boxed_1789_, v_b_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec_ref(v_as_1779_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withReverted___redArg___lam__0(lean_object* v_fst_1791_, size_t v_sz_1792_, size_t v___x_1793_, lean_object* v___x_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v___x_1800_; 
v___x_1800_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_withReverted_spec__1(v_fst_1791_, v_sz_1792_, v___x_1793_, v___x_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1808_; 
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1808_ == 0)
{
lean_object* v_unused_1809_; 
v_unused_1809_ = lean_ctor_get(v___x_1800_, 0);
lean_dec(v_unused_1809_);
v___x_1802_ = v___x_1800_;
v_isShared_1803_ = v_isSharedCheck_1808_;
goto v_resetjp_1801_;
}
else
{
lean_dec(v___x_1800_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1808_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1804_; lean_object* v___x_1806_; 
v___x_1804_ = lean_box(0);
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 0, v___x_1804_);
v___x_1806_ = v___x_1802_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v___x_1804_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
else
{
lean_object* v_a_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1817_; 
v_a_1810_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1812_ = v___x_1800_;
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_a_1810_);
lean_dec(v___x_1800_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1815_; 
if (v_isShared_1813_ == 0)
{
v___x_1815_ = v___x_1812_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_a_1810_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withReverted___redArg___lam__0___boxed(lean_object* v_fst_1818_, lean_object* v_sz_1819_, lean_object* v___x_1820_, lean_object* v___x_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
size_t v_sz_boxed_1827_; size_t v___x_3386__boxed_1828_; lean_object* v_res_1829_; 
v_sz_boxed_1827_ = lean_unbox_usize(v_sz_1819_);
lean_dec(v_sz_1819_);
v___x_3386__boxed_1828_ = lean_unbox_usize(v___x_1820_);
lean_dec(v___x_1820_);
v_res_1829_ = l_Lean_MVarId_withReverted___redArg___lam__0(v_fst_1818_, v_sz_boxed_1827_, v___x_3386__boxed_1828_, v___x_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec_ref(v_fst_1818_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withReverted___redArg(lean_object* v_mvarId_1832_, lean_object* v_fvarIds_1833_, lean_object* v_k_1834_, uint8_t v_clearAuxDeclsInsteadOfRevert_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_){
_start:
{
uint8_t v___x_1841_; lean_object* v___x_1842_; 
v___x_1841_ = 1;
v___x_1842_ = l_Lean_MVarId_revert(v_mvarId_1832_, v_fvarIds_1833_, v___x_1841_, v_clearAuxDeclsInsteadOfRevert_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_object* v_a_1843_; lean_object* v_fst_1844_; lean_object* v_snd_1845_; lean_object* v___x_1846_; 
v_a_1843_ = lean_ctor_get(v___x_1842_, 0);
lean_inc(v_a_1843_);
lean_dec_ref(v___x_1842_);
v_fst_1844_ = lean_ctor_get(v_a_1843_, 0);
lean_inc(v_fst_1844_);
v_snd_1845_ = lean_ctor_get(v_a_1843_, 1);
lean_inc(v_snd_1845_);
lean_dec(v_a_1843_);
lean_inc(v_a_1839_);
lean_inc_ref(v_a_1838_);
lean_inc(v_a_1837_);
lean_inc_ref(v_a_1836_);
v___x_1846_ = lean_apply_7(v_k_1834_, v_snd_1845_, v_fst_1844_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, lean_box(0));
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; lean_object* v_snd_1848_; lean_object* v_fst_1849_; lean_object* v_fst_1850_; lean_object* v_snd_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; uint8_t v___x_1854_; lean_object* v___x_1855_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
lean_inc(v_a_1847_);
lean_dec_ref(v___x_1846_);
v_snd_1848_ = lean_ctor_get(v_a_1847_, 1);
lean_inc(v_snd_1848_);
v_fst_1849_ = lean_ctor_get(v_a_1847_, 0);
lean_inc(v_fst_1849_);
lean_dec(v_a_1847_);
v_fst_1850_ = lean_ctor_get(v_snd_1848_, 0);
lean_inc(v_fst_1850_);
v_snd_1851_ = lean_ctor_get(v_snd_1848_, 1);
lean_inc(v_snd_1851_);
lean_dec(v_snd_1848_);
v___x_1852_ = lean_array_get_size(v_fst_1850_);
v___x_1853_ = lean_box(0);
v___x_1854_ = 0;
v___x_1855_ = l_Lean_Meta_introNCore(v_snd_1851_, v___x_1852_, v___x_1853_, v___x_1854_, v___x_1841_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_object* v_a_1856_; lean_object* v_fst_1857_; lean_object* v_snd_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1889_; 
v_a_1856_ = lean_ctor_get(v___x_1855_, 0);
lean_inc(v_a_1856_);
lean_dec_ref(v___x_1855_);
v_fst_1857_ = lean_ctor_get(v_a_1856_, 0);
v_snd_1858_ = lean_ctor_get(v_a_1856_, 1);
v_isSharedCheck_1889_ = !lean_is_exclusive(v_a_1856_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1860_ = v_a_1856_;
v_isShared_1861_ = v_isSharedCheck_1889_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_snd_1858_);
lean_inc(v_fst_1857_);
lean_dec(v_a_1856_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1889_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; size_t v_sz_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___f_1868_; lean_object* v___x_1869_; 
v___x_1862_ = lean_unsigned_to_nat(0u);
v___x_1863_ = lean_array_get_size(v_fst_1857_);
v___x_1864_ = l_Array_toSubarray___redArg(v_fst_1857_, v___x_1862_, v___x_1863_);
v_sz_1865_ = lean_array_size(v_fst_1850_);
v___x_1866_ = lean_box_usize(v_sz_1865_);
v___x_1867_ = ((lean_object*)(l_Lean_MVarId_withReverted___redArg___boxed__const__1));
v___f_1868_ = lean_alloc_closure((void*)(l_Lean_MVarId_withReverted___redArg___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1868_, 0, v_fst_1850_);
lean_closure_set(v___f_1868_, 1, v___x_1866_);
lean_closure_set(v___f_1868_, 2, v___x_1867_);
lean_closure_set(v___f_1868_, 3, v___x_1864_);
lean_inc(v_snd_1858_);
v___x_1869_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_snd_1858_, v___f_1868_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1879_; 
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1879_ == 0)
{
lean_object* v_unused_1880_; 
v_unused_1880_ = lean_ctor_get(v___x_1869_, 0);
lean_dec(v_unused_1880_);
v___x_1871_ = v___x_1869_;
v_isShared_1872_ = v_isSharedCheck_1879_;
goto v_resetjp_1870_;
}
else
{
lean_dec(v___x_1869_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1879_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1861_ == 0)
{
lean_ctor_set(v___x_1860_, 0, v_fst_1849_);
v___x_1874_ = v___x_1860_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_fst_1849_);
lean_ctor_set(v_reuseFailAlloc_1878_, 1, v_snd_1858_);
v___x_1874_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
lean_object* v___x_1876_; 
if (v_isShared_1872_ == 0)
{
lean_ctor_set(v___x_1871_, 0, v___x_1874_);
v___x_1876_ = v___x_1871_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v___x_1874_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
}
}
else
{
lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1888_; 
lean_del_object(v___x_1860_);
lean_dec(v_snd_1858_);
lean_dec(v_fst_1849_);
v_a_1881_ = lean_ctor_get(v___x_1869_, 0);
v_isSharedCheck_1888_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1883_ = v___x_1869_;
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_dec(v___x_1869_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1886_; 
if (v_isShared_1884_ == 0)
{
v___x_1886_ = v___x_1883_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_a_1881_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
}
}
}
else
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1897_; 
lean_dec(v_fst_1850_);
lean_dec(v_fst_1849_);
v_a_1890_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1892_ = v___x_1855_;
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1855_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1895_; 
if (v_isShared_1893_ == 0)
{
v___x_1895_ = v___x_1892_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_a_1890_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
else
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
v_a_1898_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1846_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1846_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
else
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1913_; 
lean_dec_ref(v_k_1834_);
v_a_1906_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1908_ = v___x_1842_;
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1842_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1911_; 
if (v_isShared_1909_ == 0)
{
v___x_1911_ = v___x_1908_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_a_1906_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withReverted___redArg___boxed(lean_object* v_mvarId_1914_, lean_object* v_fvarIds_1915_, lean_object* v_k_1916_, lean_object* v_clearAuxDeclsInsteadOfRevert_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_){
_start:
{
uint8_t v_clearAuxDeclsInsteadOfRevert_boxed_1923_; lean_object* v_res_1924_; 
v_clearAuxDeclsInsteadOfRevert_boxed_1923_ = lean_unbox(v_clearAuxDeclsInsteadOfRevert_1917_);
v_res_1924_ = l_Lean_MVarId_withReverted___redArg(v_mvarId_1914_, v_fvarIds_1915_, v_k_1916_, v_clearAuxDeclsInsteadOfRevert_boxed_1923_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_);
lean_dec(v_a_1921_);
lean_dec_ref(v_a_1920_);
lean_dec(v_a_1919_);
lean_dec_ref(v_a_1918_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withReverted(lean_object* v_00_u03b1_1925_, lean_object* v_mvarId_1926_, lean_object* v_fvarIds_1927_, lean_object* v_k_1928_, uint8_t v_clearAuxDeclsInsteadOfRevert_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_){
_start:
{
lean_object* v___x_1935_; 
v___x_1935_ = l_Lean_MVarId_withReverted___redArg(v_mvarId_1926_, v_fvarIds_1927_, v_k_1928_, v_clearAuxDeclsInsteadOfRevert_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
return v___x_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withReverted___boxed(lean_object* v_00_u03b1_1936_, lean_object* v_mvarId_1937_, lean_object* v_fvarIds_1938_, lean_object* v_k_1939_, lean_object* v_clearAuxDeclsInsteadOfRevert_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_){
_start:
{
uint8_t v_clearAuxDeclsInsteadOfRevert_boxed_1946_; lean_object* v_res_1947_; 
v_clearAuxDeclsInsteadOfRevert_boxed_1946_ = lean_unbox(v_clearAuxDeclsInsteadOfRevert_1940_);
v_res_1947_ = l_Lean_MVarId_withReverted(v_00_u03b1_1936_, v_mvarId_1937_, v_fvarIds_1938_, v_k_1939_, v_clearAuxDeclsInsteadOfRevert_boxed_1946_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_);
lean_dec(v_a_1944_);
lean_dec_ref(v_a_1943_);
lean_dec(v_a_1942_);
lean_dec_ref(v_a_1941_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0(lean_object* v_t_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_){
_start:
{
lean_object* v___x_1954_; 
v___x_1954_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0___redArg(v_t_1948_, v___y_1952_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0___boxed(lean_object* v_t_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0(v_t_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withRevertedFrom___redArg(lean_object* v_mvarId_1962_, lean_object* v_fvarId_1963_, lean_object* v_k_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_){
_start:
{
lean_object* v___x_1970_; 
v___x_1970_ = l_Lean_MVarId_revertFrom(v_mvarId_1962_, v_fvarId_1963_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v_a_1971_; lean_object* v_fst_1972_; lean_object* v_snd_1973_; lean_object* v___x_1974_; 
v_a_1971_ = lean_ctor_get(v___x_1970_, 0);
lean_inc(v_a_1971_);
lean_dec_ref(v___x_1970_);
v_fst_1972_ = lean_ctor_get(v_a_1971_, 0);
lean_inc(v_fst_1972_);
v_snd_1973_ = lean_ctor_get(v_a_1971_, 1);
lean_inc(v_snd_1973_);
lean_dec(v_a_1971_);
lean_inc(v_a_1968_);
lean_inc_ref(v_a_1967_);
lean_inc(v_a_1966_);
lean_inc_ref(v_a_1965_);
v___x_1974_ = lean_apply_7(v_k_1964_, v_snd_1973_, v_fst_1972_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_, lean_box(0));
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v_a_1975_; lean_object* v_snd_1976_; lean_object* v_fst_1977_; lean_object* v_fst_1978_; lean_object* v_snd_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; uint8_t v___x_1982_; uint8_t v___x_1983_; lean_object* v___x_1984_; 
v_a_1975_ = lean_ctor_get(v___x_1974_, 0);
lean_inc(v_a_1975_);
lean_dec_ref(v___x_1974_);
v_snd_1976_ = lean_ctor_get(v_a_1975_, 1);
lean_inc(v_snd_1976_);
v_fst_1977_ = lean_ctor_get(v_a_1975_, 0);
lean_inc(v_fst_1977_);
lean_dec(v_a_1975_);
v_fst_1978_ = lean_ctor_get(v_snd_1976_, 0);
lean_inc(v_fst_1978_);
v_snd_1979_ = lean_ctor_get(v_snd_1976_, 1);
lean_inc(v_snd_1979_);
lean_dec(v_snd_1976_);
v___x_1980_ = lean_array_get_size(v_fst_1978_);
v___x_1981_ = lean_box(0);
v___x_1982_ = 0;
v___x_1983_ = 1;
v___x_1984_ = l_Lean_Meta_introNCore(v_snd_1979_, v___x_1980_, v___x_1981_, v___x_1982_, v___x_1983_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_);
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_object* v_a_1985_; lean_object* v_fst_1986_; lean_object* v_snd_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_2018_; 
v_a_1985_ = lean_ctor_get(v___x_1984_, 0);
lean_inc(v_a_1985_);
lean_dec_ref(v___x_1984_);
v_fst_1986_ = lean_ctor_get(v_a_1985_, 0);
v_snd_1987_ = lean_ctor_get(v_a_1985_, 1);
v_isSharedCheck_2018_ = !lean_is_exclusive(v_a_1985_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_1989_ = v_a_1985_;
v_isShared_1990_ = v_isSharedCheck_2018_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_snd_1987_);
lean_inc(v_fst_1986_);
lean_dec(v_a_1985_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_2018_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; size_t v_sz_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___f_1997_; lean_object* v___x_1998_; 
v___x_1991_ = lean_unsigned_to_nat(0u);
v___x_1992_ = lean_array_get_size(v_fst_1986_);
v___x_1993_ = l_Array_toSubarray___redArg(v_fst_1986_, v___x_1991_, v___x_1992_);
v_sz_1994_ = lean_array_size(v_fst_1978_);
v___x_1995_ = lean_box_usize(v_sz_1994_);
v___x_1996_ = ((lean_object*)(l_Lean_MVarId_withReverted___redArg___boxed__const__1));
v___f_1997_ = lean_alloc_closure((void*)(l_Lean_MVarId_withReverted___redArg___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1997_, 0, v_fst_1978_);
lean_closure_set(v___f_1997_, 1, v___x_1995_);
lean_closure_set(v___f_1997_, 2, v___x_1996_);
lean_closure_set(v___f_1997_, 3, v___x_1993_);
lean_inc(v_snd_1987_);
v___x_1998_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_snd_1987_, v___f_1997_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2008_; 
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2008_ == 0)
{
lean_object* v_unused_2009_; 
v_unused_2009_ = lean_ctor_get(v___x_1998_, 0);
lean_dec(v_unused_2009_);
v___x_2000_ = v___x_1998_;
v_isShared_2001_ = v_isSharedCheck_2008_;
goto v_resetjp_1999_;
}
else
{
lean_dec(v___x_1998_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2008_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2003_; 
if (v_isShared_1990_ == 0)
{
lean_ctor_set(v___x_1989_, 0, v_fst_1977_);
v___x_2003_ = v___x_1989_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_fst_1977_);
lean_ctor_set(v_reuseFailAlloc_2007_, 1, v_snd_1987_);
v___x_2003_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
lean_object* v___x_2005_; 
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 0, v___x_2003_);
v___x_2005_ = v___x_2000_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v___x_2003_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
}
else
{
lean_object* v_a_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2017_; 
lean_del_object(v___x_1989_);
lean_dec(v_snd_1987_);
lean_dec(v_fst_1977_);
v_a_2010_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_2012_ = v___x_1998_;
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_a_2010_);
lean_dec(v___x_1998_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2015_; 
if (v_isShared_2013_ == 0)
{
v___x_2015_ = v___x_2012_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_a_2010_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
}
}
}
else
{
lean_object* v_a_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2026_; 
lean_dec(v_fst_1978_);
lean_dec(v_fst_1977_);
v_a_2019_ = lean_ctor_get(v___x_1984_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2021_ = v___x_1984_;
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_a_2019_);
lean_dec(v___x_1984_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2024_; 
if (v_isShared_2022_ == 0)
{
v___x_2024_ = v___x_2021_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_a_2019_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
}
else
{
lean_object* v_a_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2034_; 
v_a_2027_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2029_ = v___x_1974_;
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_a_2027_);
lean_dec(v___x_1974_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2032_; 
if (v_isShared_2030_ == 0)
{
v___x_2032_ = v___x_2029_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_a_2027_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
}
else
{
lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2042_; 
lean_dec_ref(v_k_1964_);
v_a_2035_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2037_ = v___x_1970_;
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v___x_1970_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2040_; 
if (v_isShared_2038_ == 0)
{
v___x_2040_ = v___x_2037_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_2035_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withRevertedFrom___redArg___boxed(lean_object* v_mvarId_2043_, lean_object* v_fvarId_2044_, lean_object* v_k_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_){
_start:
{
lean_object* v_res_2051_; 
v_res_2051_ = l_Lean_MVarId_withRevertedFrom___redArg(v_mvarId_2043_, v_fvarId_2044_, v_k_2045_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_);
lean_dec(v_a_2049_);
lean_dec_ref(v_a_2048_);
lean_dec(v_a_2047_);
lean_dec_ref(v_a_2046_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withRevertedFrom(lean_object* v_00_u03b1_2052_, lean_object* v_mvarId_2053_, lean_object* v_fvarId_2054_, lean_object* v_k_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_){
_start:
{
lean_object* v___x_2061_; 
v___x_2061_ = l_Lean_MVarId_withRevertedFrom___redArg(v_mvarId_2053_, v_fvarId_2054_, v_k_2055_, v_a_2056_, v_a_2057_, v_a_2058_, v_a_2059_);
return v___x_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withRevertedFrom___boxed(lean_object* v_00_u03b1_2062_, lean_object* v_mvarId_2063_, lean_object* v_fvarId_2064_, lean_object* v_k_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_){
_start:
{
lean_object* v_res_2071_; 
v_res_2071_ = l_Lean_MVarId_withRevertedFrom(v_00_u03b1_2062_, v_mvarId_2063_, v_fvarId_2064_, v_k_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_);
lean_dec(v_a_2069_);
lean_dec_ref(v_a_2068_);
lean_dec(v_a_2067_);
lean_dec_ref(v_a_2066_);
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lam__0(uint8_t v_checkDefEq_2072_, lean_object* v_typeNew_2073_, lean_object* v___x_2074_, lean_object* v_mvarId_2075_, lean_object* v_typeOld_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_){
_start:
{
if (v_checkDefEq_2072_ == 0)
{
lean_object* v___x_2082_; lean_object* v___x_2083_; 
lean_dec_ref(v_typeOld_2076_);
lean_dec(v_mvarId_2075_);
lean_dec(v___x_2074_);
lean_dec_ref(v_typeNew_2073_);
v___x_2082_ = lean_box(0);
v___x_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2082_);
return v___x_2083_;
}
else
{
lean_object* v___x_2084_; 
lean_inc_ref(v_typeOld_2076_);
lean_inc_ref(v_typeNew_2073_);
v___x_2084_ = l_Lean_Meta_isExprDefEq(v_typeNew_2073_, v_typeOld_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2103_; 
v_a_2085_ = lean_ctor_get(v___x_2084_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2087_ = v___x_2084_;
v_isShared_2088_ = v_isSharedCheck_2103_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_2084_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2103_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
uint8_t v___x_2089_; 
v___x_2089_ = lean_unbox(v_a_2085_);
lean_dec(v_a_2085_);
if (v___x_2089_ == 0)
{
lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
lean_del_object(v___x_2087_);
v___x_2090_ = lean_obj_once(&l_Lean_MVarId_change___lam__0___closed__1, &l_Lean_MVarId_change___lam__0___closed__1_once, _init_l_Lean_MVarId_change___lam__0___closed__1);
v___x_2091_ = l_Lean_indentExpr(v_typeNew_2073_);
v___x_2092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2090_);
lean_ctor_set(v___x_2092_, 1, v___x_2091_);
v___x_2093_ = lean_obj_once(&l_Lean_MVarId_change___lam__0___closed__3, &l_Lean_MVarId_change___lam__0___closed__3_once, _init_l_Lean_MVarId_change___lam__0___closed__3);
v___x_2094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2092_);
lean_ctor_set(v___x_2094_, 1, v___x_2093_);
v___x_2095_ = l_Lean_indentExpr(v_typeOld_2076_);
v___x_2096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2094_);
lean_ctor_set(v___x_2096_, 1, v___x_2095_);
v___x_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2096_);
v___x_2098_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2074_, v_mvarId_2075_, v___x_2097_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
return v___x_2098_;
}
else
{
lean_object* v___x_2099_; lean_object* v___x_2101_; 
lean_dec_ref(v_typeOld_2076_);
lean_dec(v_mvarId_2075_);
lean_dec(v___x_2074_);
lean_dec_ref(v_typeNew_2073_);
v___x_2099_ = lean_box(0);
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 0, v___x_2099_);
v___x_2101_ = v___x_2087_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v___x_2099_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
else
{
lean_object* v_a_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2111_; 
lean_dec_ref(v_typeOld_2076_);
lean_dec(v_mvarId_2075_);
lean_dec(v___x_2074_);
lean_dec_ref(v_typeNew_2073_);
v_a_2104_ = lean_ctor_get(v___x_2084_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2106_ = v___x_2084_;
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_a_2104_);
lean_dec(v___x_2084_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2109_; 
if (v_isShared_2107_ == 0)
{
v___x_2109_ = v___x_2106_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_a_2104_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lam__0___boxed(lean_object* v_checkDefEq_2112_, lean_object* v_typeNew_2113_, lean_object* v___x_2114_, lean_object* v_mvarId_2115_, lean_object* v_typeOld_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_){
_start:
{
uint8_t v_checkDefEq_boxed_2122_; lean_object* v_res_2123_; 
v_checkDefEq_boxed_2122_ = lean_unbox(v_checkDefEq_2112_);
v_res_2123_ = l_Lean_MVarId_changeLocalDecl___lam__0(v_checkDefEq_boxed_2122_, v_typeNew_2113_, v___x_2114_, v_mvarId_2115_, v_typeOld_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_changeLocalDecl_spec__0(size_t v_sz_2124_, size_t v_i_2125_, lean_object* v_bs_2126_){
_start:
{
uint8_t v___x_2127_; 
v___x_2127_ = lean_usize_dec_lt(v_i_2125_, v_sz_2124_);
if (v___x_2127_ == 0)
{
return v_bs_2126_;
}
else
{
lean_object* v_v_2128_; lean_object* v___x_2129_; lean_object* v_bs_x27_2130_; lean_object* v___x_2131_; size_t v___x_2132_; size_t v___x_2133_; lean_object* v___x_2134_; 
v_v_2128_ = lean_array_uget(v_bs_2126_, v_i_2125_);
v___x_2129_ = lean_unsigned_to_nat(0u);
v_bs_x27_2130_ = lean_array_uset(v_bs_2126_, v_i_2125_, v___x_2129_);
v___x_2131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2131_, 0, v_v_2128_);
v___x_2132_ = ((size_t)1ULL);
v___x_2133_ = lean_usize_add(v_i_2125_, v___x_2132_);
v___x_2134_ = lean_array_uset(v_bs_x27_2130_, v_i_2125_, v___x_2131_);
v_i_2125_ = v___x_2133_;
v_bs_2126_ = v___x_2134_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_changeLocalDecl_spec__0___boxed(lean_object* v_sz_2136_, lean_object* v_i_2137_, lean_object* v_bs_2138_){
_start:
{
size_t v_sz_boxed_2139_; size_t v_i_boxed_2140_; lean_object* v_res_2141_; 
v_sz_boxed_2139_ = lean_unbox_usize(v_sz_2136_);
lean_dec(v_sz_2136_);
v_i_boxed_2140_ = lean_unbox_usize(v_i_2137_);
lean_dec(v_i_2137_);
v_res_2141_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_changeLocalDecl_spec__0(v_sz_boxed_2139_, v_i_boxed_2140_, v_bs_2138_);
return v_res_2141_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lam__1(lean_object* v_mvarId_2142_, lean_object* v_fvars_2143_, lean_object* v_targetNew_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_){
_start:
{
lean_object* v___x_2150_; 
v___x_2150_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_2142_, v_targetNew_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2164_; 
v_a_2151_ = lean_ctor_get(v___x_2150_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2153_ = v___x_2150_;
v_isShared_2154_ = v_isSharedCheck_2164_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2150_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2164_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2155_; size_t v_sz_2156_; size_t v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2162_; 
v___x_2155_ = lean_box(0);
v_sz_2156_ = lean_array_size(v_fvars_2143_);
v___x_2157_ = ((size_t)0ULL);
v___x_2158_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_changeLocalDecl_spec__0(v_sz_2156_, v___x_2157_, v_fvars_2143_);
v___x_2159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2158_);
lean_ctor_set(v___x_2159_, 1, v_a_2151_);
v___x_2160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2155_);
lean_ctor_set(v___x_2160_, 1, v___x_2159_);
if (v_isShared_2154_ == 0)
{
lean_ctor_set(v___x_2153_, 0, v___x_2160_);
v___x_2162_ = v___x_2153_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2160_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
else
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2172_; 
lean_dec_ref(v_fvars_2143_);
v_a_2165_ = lean_ctor_get(v___x_2150_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2167_ = v___x_2150_;
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___x_2150_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2170_; 
if (v_isShared_2168_ == 0)
{
v___x_2170_ = v___x_2167_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_a_2165_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lam__1___boxed(lean_object* v_mvarId_2173_, lean_object* v_fvars_2174_, lean_object* v_targetNew_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_){
_start:
{
lean_object* v_res_2181_; 
v_res_2181_ = l_Lean_MVarId_changeLocalDecl___lam__1(v_mvarId_2173_, v_fvars_2174_, v_targetNew_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
lean_dec(v___y_2177_);
lean_dec_ref(v___y_2176_);
return v_res_2181_;
}
}
static lean_object* _init_l_Lean_MVarId_changeLocalDecl___lam__2___closed__2(void){
_start:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2185_ = ((lean_object*)(l_Lean_MVarId_changeLocalDecl___lam__2___closed__1));
v___x_2186_ = l_Lean_MessageData_ofFormat(v___x_2185_);
return v___x_2186_;
}
}
static lean_object* _init_l_Lean_MVarId_changeLocalDecl___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; 
v___x_2187_ = lean_obj_once(&l_Lean_MVarId_changeLocalDecl___lam__2___closed__2, &l_Lean_MVarId_changeLocalDecl___lam__2___closed__2_once, _init_l_Lean_MVarId_changeLocalDecl___lam__2___closed__2);
v___x_2188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2188_, 0, v___x_2187_);
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lam__2(lean_object* v_mvarId_2189_, lean_object* v___f_2190_, lean_object* v_typeNew_2191_, lean_object* v___f_2192_, lean_object* v___x_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
lean_object* v___x_2199_; 
lean_inc(v_mvarId_2189_);
v___x_2199_ = l_Lean_MVarId_getType(v_mvarId_2189_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_object* v_a_2200_; 
v_a_2200_ = lean_ctor_get(v___x_2199_, 0);
lean_inc(v_a_2200_);
lean_dec_ref(v___x_2199_);
switch(lean_obj_tag(v_a_2200_))
{
case 7:
{
lean_object* v_binderName_2201_; lean_object* v_binderType_2202_; lean_object* v_body_2203_; uint8_t v_binderInfo_2204_; lean_object* v___x_2205_; 
lean_dec(v___x_2193_);
lean_dec(v_mvarId_2189_);
v_binderName_2201_ = lean_ctor_get(v_a_2200_, 0);
lean_inc(v_binderName_2201_);
v_binderType_2202_ = lean_ctor_get(v_a_2200_, 1);
lean_inc_ref(v_binderType_2202_);
v_body_2203_ = lean_ctor_get(v_a_2200_, 2);
lean_inc_ref(v_body_2203_);
v_binderInfo_2204_ = lean_ctor_get_uint8(v_a_2200_, sizeof(void*)*3 + 8);
lean_dec_ref(v_a_2200_);
lean_inc(v___y_2197_);
lean_inc_ref(v___y_2196_);
lean_inc(v___y_2195_);
lean_inc_ref(v___y_2194_);
v___x_2205_ = lean_apply_6(v___f_2190_, v_binderType_2202_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, lean_box(0));
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v___x_2206_; lean_object* v___x_2207_; 
lean_dec_ref(v___x_2205_);
v___x_2206_ = l_Lean_Expr_forallE___override(v_binderName_2201_, v_typeNew_2191_, v_body_2203_, v_binderInfo_2204_);
v___x_2207_ = lean_apply_6(v___f_2192_, v___x_2206_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, lean_box(0));
return v___x_2207_;
}
else
{
lean_object* v_a_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2215_; 
lean_dec_ref(v_body_2203_);
lean_dec(v_binderName_2201_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
lean_dec(v___y_2195_);
lean_dec_ref(v___y_2194_);
lean_dec_ref(v___f_2192_);
lean_dec_ref(v_typeNew_2191_);
v_a_2208_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2210_ = v___x_2205_;
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_a_2208_);
lean_dec(v___x_2205_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2213_; 
if (v_isShared_2211_ == 0)
{
v___x_2213_ = v___x_2210_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_a_2208_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
}
case 8:
{
lean_object* v_declName_2216_; lean_object* v_type_2217_; lean_object* v_value_2218_; lean_object* v_body_2219_; uint8_t v_nondep_2220_; lean_object* v___x_2221_; 
lean_dec(v___x_2193_);
lean_dec(v_mvarId_2189_);
v_declName_2216_ = lean_ctor_get(v_a_2200_, 0);
lean_inc(v_declName_2216_);
v_type_2217_ = lean_ctor_get(v_a_2200_, 1);
lean_inc_ref(v_type_2217_);
v_value_2218_ = lean_ctor_get(v_a_2200_, 2);
lean_inc_ref(v_value_2218_);
v_body_2219_ = lean_ctor_get(v_a_2200_, 3);
lean_inc_ref(v_body_2219_);
v_nondep_2220_ = lean_ctor_get_uint8(v_a_2200_, sizeof(void*)*4 + 8);
lean_dec_ref(v_a_2200_);
lean_inc(v___y_2197_);
lean_inc_ref(v___y_2196_);
lean_inc(v___y_2195_);
lean_inc_ref(v___y_2194_);
v___x_2221_ = lean_apply_6(v___f_2190_, v_type_2217_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, lean_box(0));
if (lean_obj_tag(v___x_2221_) == 0)
{
lean_object* v___x_2222_; lean_object* v___x_2223_; 
lean_dec_ref(v___x_2221_);
v___x_2222_ = l_Lean_Expr_letE___override(v_declName_2216_, v_typeNew_2191_, v_value_2218_, v_body_2219_, v_nondep_2220_);
v___x_2223_ = lean_apply_6(v___f_2192_, v___x_2222_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, lean_box(0));
return v___x_2223_;
}
else
{
lean_object* v_a_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2231_; 
lean_dec_ref(v_body_2219_);
lean_dec_ref(v_value_2218_);
lean_dec(v_declName_2216_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
lean_dec(v___y_2195_);
lean_dec_ref(v___y_2194_);
lean_dec_ref(v___f_2192_);
lean_dec_ref(v_typeNew_2191_);
v_a_2224_ = lean_ctor_get(v___x_2221_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2226_ = v___x_2221_;
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_a_2224_);
lean_dec(v___x_2221_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v___x_2229_; 
if (v_isShared_2227_ == 0)
{
v___x_2229_ = v___x_2226_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_a_2224_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
}
}
default: 
{
lean_object* v___x_2232_; lean_object* v___x_2233_; 
lean_dec(v_a_2200_);
lean_dec_ref(v___f_2192_);
lean_dec_ref(v_typeNew_2191_);
lean_dec_ref(v___f_2190_);
v___x_2232_ = lean_obj_once(&l_Lean_MVarId_changeLocalDecl___lam__2___closed__3, &l_Lean_MVarId_changeLocalDecl___lam__2___closed__3_once, _init_l_Lean_MVarId_changeLocalDecl___lam__2___closed__3);
v___x_2233_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2193_, v_mvarId_2189_, v___x_2232_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
lean_dec(v___y_2195_);
lean_dec_ref(v___y_2194_);
return v___x_2233_;
}
}
}
else
{
lean_object* v_a_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2241_; 
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
lean_dec(v___y_2195_);
lean_dec_ref(v___y_2194_);
lean_dec(v___x_2193_);
lean_dec_ref(v___f_2192_);
lean_dec_ref(v_typeNew_2191_);
lean_dec_ref(v___f_2190_);
lean_dec(v_mvarId_2189_);
v_a_2234_ = lean_ctor_get(v___x_2199_, 0);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2236_ = v___x_2199_;
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_a_2234_);
lean_dec(v___x_2199_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2239_; 
if (v_isShared_2237_ == 0)
{
v___x_2239_ = v___x_2236_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_a_2234_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lam__2___boxed(lean_object* v_mvarId_2242_, lean_object* v___f_2243_, lean_object* v_typeNew_2244_, lean_object* v___f_2245_, lean_object* v___x_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l_Lean_MVarId_changeLocalDecl___lam__2(v_mvarId_2242_, v___f_2243_, v_typeNew_2244_, v___f_2245_, v___x_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lam__3(uint8_t v_checkDefEq_2253_, lean_object* v_typeNew_2254_, lean_object* v___x_2255_, lean_object* v_mvarId_2256_, lean_object* v_fvars_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_){
_start:
{
lean_object* v___x_2263_; lean_object* v___f_2264_; lean_object* v___f_2265_; lean_object* v___f_2266_; lean_object* v___x_2267_; 
v___x_2263_ = lean_box(v_checkDefEq_2253_);
lean_inc_n(v_mvarId_2256_, 3);
lean_inc(v___x_2255_);
lean_inc_ref(v_typeNew_2254_);
v___f_2264_ = lean_alloc_closure((void*)(l_Lean_MVarId_changeLocalDecl___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2264_, 0, v___x_2263_);
lean_closure_set(v___f_2264_, 1, v_typeNew_2254_);
lean_closure_set(v___f_2264_, 2, v___x_2255_);
lean_closure_set(v___f_2264_, 3, v_mvarId_2256_);
v___f_2265_ = lean_alloc_closure((void*)(l_Lean_MVarId_changeLocalDecl___lam__1___boxed), 8, 2);
lean_closure_set(v___f_2265_, 0, v_mvarId_2256_);
lean_closure_set(v___f_2265_, 1, v_fvars_2257_);
v___f_2266_ = lean_alloc_closure((void*)(l_Lean_MVarId_changeLocalDecl___lam__2___boxed), 10, 5);
lean_closure_set(v___f_2266_, 0, v_mvarId_2256_);
lean_closure_set(v___f_2266_, 1, v___f_2264_);
lean_closure_set(v___f_2266_, 2, v_typeNew_2254_);
lean_closure_set(v___f_2266_, 3, v___f_2265_);
lean_closure_set(v___f_2266_, 4, v___x_2255_);
v___x_2267_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_2256_, v___f_2266_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lam__3___boxed(lean_object* v_checkDefEq_2268_, lean_object* v_typeNew_2269_, lean_object* v___x_2270_, lean_object* v_mvarId_2271_, lean_object* v_fvars_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
uint8_t v_checkDefEq_boxed_2278_; lean_object* v_res_2279_; 
v_checkDefEq_boxed_2278_ = lean_unbox(v_checkDefEq_2268_);
v_res_2279_ = l_Lean_MVarId_changeLocalDecl___lam__3(v_checkDefEq_boxed_2278_, v_typeNew_2269_, v___x_2270_, v_mvarId_2271_, v_fvars_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
return v_res_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl(lean_object* v_mvarId_2283_, lean_object* v_fvarId_2284_, lean_object* v_typeNew_2285_, uint8_t v_checkDefEq_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_){
_start:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2292_ = ((lean_object*)(l_Lean_MVarId_changeLocalDecl___closed__1));
lean_inc(v_mvarId_2283_);
v___x_2293_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2283_, v___x_2292_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v___x_2294_; lean_object* v___f_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; uint8_t v___x_2299_; lean_object* v___x_2300_; 
lean_dec_ref(v___x_2293_);
v___x_2294_ = lean_box(v_checkDefEq_2286_);
v___f_2295_ = lean_alloc_closure((void*)(l_Lean_MVarId_changeLocalDecl___lam__3___boxed), 10, 3);
lean_closure_set(v___f_2295_, 0, v___x_2294_);
lean_closure_set(v___f_2295_, 1, v_typeNew_2285_);
lean_closure_set(v___f_2295_, 2, v___x_2292_);
v___x_2296_ = lean_unsigned_to_nat(1u);
v___x_2297_ = lean_mk_empty_array_with_capacity(v___x_2296_);
v___x_2298_ = lean_array_push(v___x_2297_, v_fvarId_2284_);
v___x_2299_ = 0;
v___x_2300_ = l_Lean_MVarId_withReverted___redArg(v_mvarId_2283_, v___x_2298_, v___f_2295_, v___x_2299_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_);
if (lean_obj_tag(v___x_2300_) == 0)
{
lean_object* v_a_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2309_; 
v_a_2301_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2309_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2303_ = v___x_2300_;
v_isShared_2304_ = v_isSharedCheck_2309_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_a_2301_);
lean_dec(v___x_2300_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2309_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v_snd_2305_; lean_object* v___x_2307_; 
v_snd_2305_ = lean_ctor_get(v_a_2301_, 1);
lean_inc(v_snd_2305_);
lean_dec(v_a_2301_);
if (v_isShared_2304_ == 0)
{
lean_ctor_set(v___x_2303_, 0, v_snd_2305_);
v___x_2307_ = v___x_2303_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_snd_2305_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
}
}
}
else
{
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2317_; 
v_a_2310_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2312_ = v___x_2300_;
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2300_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2315_; 
if (v_isShared_2313_ == 0)
{
v___x_2315_ = v___x_2312_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_a_2310_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
}
else
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2325_; 
lean_dec_ref(v_typeNew_2285_);
lean_dec(v_fvarId_2284_);
lean_dec(v_mvarId_2283_);
v_a_2318_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2320_ = v___x_2293_;
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2293_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2323_; 
if (v_isShared_2321_ == 0)
{
v___x_2323_ = v___x_2320_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_a_2318_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___boxed(lean_object* v_mvarId_2326_, lean_object* v_fvarId_2327_, lean_object* v_typeNew_2328_, lean_object* v_checkDefEq_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_){
_start:
{
uint8_t v_checkDefEq_boxed_2335_; lean_object* v_res_2336_; 
v_checkDefEq_boxed_2335_ = lean_unbox(v_checkDefEq_2329_);
v_res_2336_ = l_Lean_MVarId_changeLocalDecl(v_mvarId_2326_, v_fvarId_2327_, v_typeNew_2328_, v_checkDefEq_boxed_2335_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_);
lean_dec(v_a_2333_);
lean_dec_ref(v_a_2332_);
lean_dec(v_a_2331_);
lean_dec_ref(v_a_2330_);
return v_res_2336_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTarget___lam__0(lean_object* v_mvarId_2337_, lean_object* v___x_2338_, lean_object* v_f_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_){
_start:
{
lean_object* v___x_2345_; 
lean_inc(v_mvarId_2337_);
v___x_2345_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2337_, v___x_2338_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v___x_2346_; 
lean_dec_ref(v___x_2345_);
lean_inc(v_mvarId_2337_);
v___x_2346_ = l_Lean_MVarId_getType(v_mvarId_2337_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_);
if (lean_obj_tag(v___x_2346_) == 0)
{
lean_object* v_a_2347_; lean_object* v___x_2348_; 
v_a_2347_ = lean_ctor_get(v___x_2346_, 0);
lean_inc(v_a_2347_);
lean_dec_ref(v___x_2346_);
lean_inc(v___y_2343_);
lean_inc_ref(v___y_2342_);
lean_inc(v___y_2341_);
lean_inc_ref(v___y_2340_);
v___x_2348_ = lean_apply_6(v_f_2339_, v_a_2347_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, lean_box(0));
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v_a_2349_; uint8_t v___x_2350_; lean_object* v___x_2351_; 
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
lean_inc(v_a_2349_);
lean_dec_ref(v___x_2348_);
v___x_2350_ = 0;
v___x_2351_ = l_Lean_MVarId_change(v_mvarId_2337_, v_a_2349_, v___x_2350_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
lean_dec(v___y_2341_);
lean_dec_ref(v___y_2340_);
return v___x_2351_;
}
else
{
lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2359_; 
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
lean_dec(v___y_2341_);
lean_dec_ref(v___y_2340_);
lean_dec(v_mvarId_2337_);
v_a_2352_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2354_ = v___x_2348_;
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___x_2348_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2357_; 
if (v_isShared_2355_ == 0)
{
v___x_2357_ = v___x_2354_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_a_2352_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
lean_dec(v___y_2341_);
lean_dec_ref(v___y_2340_);
lean_dec_ref(v_f_2339_);
lean_dec(v_mvarId_2337_);
v_a_2360_ = lean_ctor_get(v___x_2346_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2346_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2346_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2346_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2365_; 
if (v_isShared_2363_ == 0)
{
v___x_2365_ = v___x_2362_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2360_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
else
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2375_; 
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
lean_dec(v___y_2341_);
lean_dec_ref(v___y_2340_);
lean_dec_ref(v_f_2339_);
lean_dec(v_mvarId_2337_);
v_a_2368_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2370_ = v___x_2345_;
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2345_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2373_; 
if (v_isShared_2371_ == 0)
{
v___x_2373_ = v___x_2370_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_a_2368_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTarget___lam__0___boxed(lean_object* v_mvarId_2376_, lean_object* v___x_2377_, lean_object* v_f_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l_Lean_MVarId_modifyTarget___lam__0(v_mvarId_2376_, v___x_2377_, v_f_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTarget(lean_object* v_mvarId_2388_, lean_object* v_f_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_){
_start:
{
lean_object* v___x_2395_; lean_object* v___f_2396_; lean_object* v___x_2397_; 
v___x_2395_ = ((lean_object*)(l_Lean_MVarId_modifyTarget___closed__1));
lean_inc(v_mvarId_2388_);
v___f_2396_ = lean_alloc_closure((void*)(l_Lean_MVarId_modifyTarget___lam__0___boxed), 8, 3);
lean_closure_set(v___f_2396_, 0, v_mvarId_2388_);
lean_closure_set(v___f_2396_, 1, v___x_2395_);
lean_closure_set(v___f_2396_, 2, v_f_2389_);
v___x_2397_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_2388_, v___f_2396_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTarget___boxed(lean_object* v_mvarId_2398_, lean_object* v_f_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_){
_start:
{
lean_object* v_res_2405_; 
v_res_2405_ = l_Lean_MVarId_modifyTarget(v_mvarId_2398_, v_f_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_);
lean_dec(v_a_2403_);
lean_dec_ref(v_a_2402_);
lean_dec(v_a_2401_);
lean_dec_ref(v_a_2400_);
return v_res_2405_;
}
}
static lean_object* _init_l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2410_ = ((lean_object*)(l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__2));
v___x_2411_ = l_Lean_stringToMessageData(v___x_2410_);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTargetEqLHS___lam__0(lean_object* v_f_2412_, lean_object* v_mvarId_2413_, lean_object* v_target_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_){
_start:
{
lean_object* v___x_2420_; 
lean_inc_ref(v_target_2414_);
v___x_2420_ = l_Lean_Meta_matchEq_x3f(v_target_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
if (lean_obj_tag(v___x_2420_) == 0)
{
lean_object* v_a_2421_; 
v_a_2421_ = lean_ctor_get(v___x_2420_, 0);
lean_inc(v_a_2421_);
lean_dec_ref(v___x_2420_);
if (lean_obj_tag(v_a_2421_) == 1)
{
lean_object* v_val_2422_; lean_object* v_snd_2423_; lean_object* v_fst_2424_; lean_object* v_snd_2425_; lean_object* v___x_2426_; 
lean_dec_ref(v_target_2414_);
lean_dec(v_mvarId_2413_);
v_val_2422_ = lean_ctor_get(v_a_2421_, 0);
lean_inc(v_val_2422_);
lean_dec_ref(v_a_2421_);
v_snd_2423_ = lean_ctor_get(v_val_2422_, 1);
lean_inc(v_snd_2423_);
lean_dec(v_val_2422_);
v_fst_2424_ = lean_ctor_get(v_snd_2423_, 0);
lean_inc(v_fst_2424_);
v_snd_2425_ = lean_ctor_get(v_snd_2423_, 1);
lean_inc(v_snd_2425_);
lean_dec(v_snd_2423_);
lean_inc(v___y_2418_);
lean_inc_ref(v___y_2417_);
lean_inc(v___y_2416_);
lean_inc_ref(v___y_2415_);
v___x_2426_ = lean_apply_6(v_f_2412_, v_fst_2424_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, lean_box(0));
if (lean_obj_tag(v___x_2426_) == 0)
{
lean_object* v_a_2427_; lean_object* v___x_2428_; 
v_a_2427_ = lean_ctor_get(v___x_2426_, 0);
lean_inc(v_a_2427_);
lean_dec_ref(v___x_2426_);
v___x_2428_ = l_Lean_Meta_mkEq(v_a_2427_, v_snd_2425_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
return v___x_2428_;
}
else
{
lean_dec(v_snd_2425_);
return v___x_2426_;
}
}
else
{
lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; 
lean_dec(v_a_2421_);
lean_dec_ref(v_f_2412_);
v___x_2429_ = ((lean_object*)(l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__1));
v___x_2430_ = lean_obj_once(&l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__3, &l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__3_once, _init_l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__3);
v___x_2431_ = l_Lean_indentExpr(v_target_2414_);
v___x_2432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2432_, 0, v___x_2430_);
lean_ctor_set(v___x_2432_, 1, v___x_2431_);
v___x_2433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2432_);
v___x_2434_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2429_, v_mvarId_2413_, v___x_2433_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
return v___x_2434_;
}
}
else
{
lean_object* v_a_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2442_; 
lean_dec_ref(v_target_2414_);
lean_dec(v_mvarId_2413_);
lean_dec_ref(v_f_2412_);
v_a_2435_ = lean_ctor_get(v___x_2420_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2437_ = v___x_2420_;
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_a_2435_);
lean_dec(v___x_2420_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2440_; 
if (v_isShared_2438_ == 0)
{
v___x_2440_ = v___x_2437_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v_a_2435_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
return v___x_2440_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTargetEqLHS___lam__0___boxed(lean_object* v_f_2443_, lean_object* v_mvarId_2444_, lean_object* v_target_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_){
_start:
{
lean_object* v_res_2451_; 
v_res_2451_ = l_Lean_MVarId_modifyTargetEqLHS___lam__0(v_f_2443_, v_mvarId_2444_, v_target_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
lean_dec(v___y_2449_);
lean_dec_ref(v___y_2448_);
lean_dec(v___y_2447_);
lean_dec_ref(v___y_2446_);
return v_res_2451_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTargetEqLHS(lean_object* v_mvarId_2452_, lean_object* v_f_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_){
_start:
{
lean_object* v___f_2459_; lean_object* v___x_2460_; 
lean_inc(v_mvarId_2452_);
v___f_2459_ = lean_alloc_closure((void*)(l_Lean_MVarId_modifyTargetEqLHS___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2459_, 0, v_f_2453_);
lean_closure_set(v___f_2459_, 1, v_mvarId_2452_);
v___x_2460_ = l_Lean_MVarId_modifyTarget(v_mvarId_2452_, v___f_2459_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_);
return v___x_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTargetEqLHS___boxed(lean_object* v_mvarId_2461_, lean_object* v_f_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_){
_start:
{
lean_object* v_res_2468_; 
v_res_2468_ = l_Lean_MVarId_modifyTargetEqLHS(v_mvarId_2461_, v_f_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_);
lean_dec(v_a_2466_);
lean_dec_ref(v_a_2465_);
lean_dec(v_a_2464_);
lean_dec_ref(v_a_2463_);
return v_res_2468_;
}
}
static lean_object* _init_l_Lean_MVarId_clearValue___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2470_; lean_object* v___x_2471_; 
v___x_2470_ = ((lean_object*)(l_Lean_MVarId_clearValue___lam__0___closed__0));
v___x_2471_ = l_Lean_stringToMessageData(v___x_2470_);
return v___x_2471_;
}
}
static lean_object* _init_l_Lean_MVarId_clearValue___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; 
v___x_2473_ = ((lean_object*)(l_Lean_MVarId_clearValue___lam__0___closed__2));
v___x_2474_ = l_Lean_stringToMessageData(v___x_2473_);
return v___x_2474_;
}
}
static lean_object* _init_l_Lean_MVarId_clearValue___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2476_ = ((lean_object*)(l_Lean_MVarId_clearValue___lam__0___closed__4));
v___x_2477_ = l_Lean_stringToMessageData(v___x_2476_);
return v___x_2477_;
}
}
static lean_object* _init_l_Lean_MVarId_clearValue___lam__0___closed__7(void){
_start:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2479_ = ((lean_object*)(l_Lean_MVarId_clearValue___lam__0___closed__6));
v___x_2480_ = l_Lean_stringToMessageData(v___x_2479_);
return v___x_2480_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearValue___lam__0(lean_object* v_mvarId_x27_2481_, lean_object* v_a_2482_, lean_object* v_fvars_2483_, lean_object* v_fvarId_2484_, lean_object* v___x_2485_, lean_object* v_mvarId_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_){
_start:
{
lean_object* v___x_2492_; 
lean_inc(v_mvarId_x27_2481_);
v___x_2492_ = l_Lean_MVarId_getType(v_mvarId_x27_2481_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_);
if (lean_obj_tag(v___x_2492_) == 0)
{
lean_object* v_a_2493_; lean_object* v___y_2495_; lean_object* v___y_2496_; lean_object* v___y_2497_; lean_object* v___y_2498_; lean_object* v___y_2499_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; uint8_t v___x_2574_; 
v_a_2493_ = lean_ctor_get(v___x_2492_, 0);
lean_inc(v_a_2493_);
lean_dec_ref(v___x_2492_);
v___x_2574_ = l_Lean_Expr_isLet(v_a_2493_);
if (v___x_2574_ == 0)
{
lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___x_2575_ = lean_obj_once(&l_Lean_MVarId_clearValue___lam__0___closed__5, &l_Lean_MVarId_clearValue___lam__0___closed__5_once, _init_l_Lean_MVarId_clearValue___lam__0___closed__5);
lean_inc(v_fvarId_2484_);
v___x_2576_ = l_Lean_Expr_fvar___override(v_fvarId_2484_);
v___x_2577_ = l_Lean_MessageData_ofExpr(v___x_2576_);
v___x_2578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2575_);
lean_ctor_set(v___x_2578_, 1, v___x_2577_);
v___x_2579_ = lean_obj_once(&l_Lean_MVarId_clearValue___lam__0___closed__7, &l_Lean_MVarId_clearValue___lam__0___closed__7_once, _init_l_Lean_MVarId_clearValue___lam__0___closed__7);
v___x_2580_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2580_, 0, v___x_2578_);
lean_ctor_set(v___x_2580_, 1, v___x_2579_);
v___x_2581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2580_);
lean_inc_n(v_mvarId_2486_, 2);
lean_inc(v___x_2485_);
v___x_2582_ = lean_alloc_closure((void*)(l_Lean_Meta_throwTacticEx___boxed), 9, 4);
lean_closure_set(v___x_2582_, 0, lean_box(0));
lean_closure_set(v___x_2582_, 1, v___x_2485_);
lean_closure_set(v___x_2582_, 2, v_mvarId_2486_);
lean_closure_set(v___x_2582_, 3, v___x_2581_);
v___x_2583_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_2486_, v___x_2582_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_);
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_dec_ref(v___x_2583_);
v___y_2529_ = v___y_2487_;
v___y_2530_ = v___y_2488_;
v___y_2531_ = v___y_2489_;
v___y_2532_ = v___y_2490_;
goto v___jp_2528_;
}
else
{
lean_object* v_a_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2591_; 
lean_dec(v_a_2493_);
lean_dec(v_mvarId_2486_);
lean_dec(v___x_2485_);
lean_dec(v_fvarId_2484_);
lean_dec_ref(v_fvars_2483_);
lean_dec(v_a_2482_);
lean_dec(v_mvarId_x27_2481_);
v_a_2584_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2586_ = v___x_2583_;
v_isShared_2587_ = v_isSharedCheck_2591_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_a_2584_);
lean_dec(v___x_2583_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2591_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
lean_object* v___x_2589_; 
if (v_isShared_2587_ == 0)
{
v___x_2589_ = v___x_2586_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v_a_2584_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
}
}
else
{
v___y_2529_ = v___y_2487_;
v___y_2530_ = v___y_2488_;
v___y_2531_ = v___y_2489_;
v___y_2532_ = v___y_2490_;
goto v___jp_2528_;
}
v___jp_2494_:
{
lean_object* v___x_2500_; 
v___x_2500_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_2495_, v_a_2482_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_);
if (lean_obj_tag(v___x_2500_) == 0)
{
lean_object* v_a_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2518_; 
v_a_2501_ = lean_ctor_get(v___x_2500_, 0);
lean_inc_n(v_a_2501_, 2);
lean_dec_ref(v___x_2500_);
v___x_2502_ = l_Lean_Expr_letValue_x21(v_a_2493_);
lean_dec(v_a_2493_);
v___x_2503_ = l_Lean_Expr_app___override(v_a_2501_, v___x_2502_);
v___x_2504_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg(v_mvarId_x27_2481_, v___x_2503_, v___y_2497_);
v_isSharedCheck_2518_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2518_ == 0)
{
lean_object* v_unused_2519_; 
v_unused_2519_ = lean_ctor_get(v___x_2504_, 0);
lean_dec(v_unused_2519_);
v___x_2506_ = v___x_2504_;
v_isShared_2507_ = v_isSharedCheck_2518_;
goto v_resetjp_2505_;
}
else
{
lean_dec(v___x_2504_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2518_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2508_; size_t v_sz_2509_; size_t v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2516_; 
v___x_2508_ = lean_box(0);
v_sz_2509_ = lean_array_size(v_fvars_2483_);
v___x_2510_ = ((size_t)0ULL);
v___x_2511_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_changeLocalDecl_spec__0(v_sz_2509_, v___x_2510_, v_fvars_2483_);
v___x_2512_ = l_Lean_Expr_mvarId_x21(v_a_2501_);
lean_dec(v_a_2501_);
v___x_2513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2511_);
lean_ctor_set(v___x_2513_, 1, v___x_2512_);
v___x_2514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2508_);
lean_ctor_set(v___x_2514_, 1, v___x_2513_);
if (v_isShared_2507_ == 0)
{
lean_ctor_set(v___x_2506_, 0, v___x_2514_);
v___x_2516_ = v___x_2506_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v___x_2514_);
v___x_2516_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
return v___x_2516_;
}
}
}
else
{
lean_object* v_a_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2527_; 
lean_dec(v_a_2493_);
lean_dec_ref(v_fvars_2483_);
lean_dec(v_mvarId_x27_2481_);
v_a_2520_ = lean_ctor_get(v___x_2500_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2500_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2522_ = v___x_2500_;
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_a_2520_);
lean_dec(v___x_2500_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2525_; 
if (v_isShared_2523_ == 0)
{
v___x_2525_ = v___x_2522_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v_a_2520_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
}
}
v___jp_2528_:
{
lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; uint8_t v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v_a_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2573_; 
v___x_2533_ = l_Lean_Expr_letName_x21(v_a_2493_);
v___x_2534_ = l_Lean_Expr_letType_x21(v_a_2493_);
v___x_2535_ = l_Lean_Expr_letBody_x21(v_a_2493_);
v___x_2536_ = 0;
v___x_2537_ = l_Lean_Expr_forallE___override(v___x_2533_, v___x_2534_, v___x_2535_, v___x_2536_);
v___x_2538_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_spec__0___redArg(v___x_2537_, v___y_2530_);
v_a_2539_ = lean_ctor_get(v___x_2538_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2541_ = v___x_2538_;
v_isShared_2542_ = v_isSharedCheck_2573_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_a_2539_);
lean_dec(v___x_2538_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2573_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v___x_2543_; 
lean_inc(v_a_2539_);
v___x_2543_ = l_Lean_Meta_isTypeCorrect(v_a_2539_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_object* v_a_2544_; uint8_t v___x_2545_; 
v_a_2544_ = lean_ctor_get(v___x_2543_, 0);
lean_inc(v_a_2544_);
lean_dec_ref(v___x_2543_);
v___x_2545_ = lean_unbox(v_a_2544_);
lean_dec(v_a_2544_);
if (v___x_2545_ == 0)
{
lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2553_; 
v___x_2546_ = lean_obj_once(&l_Lean_MVarId_clearValue___lam__0___closed__1, &l_Lean_MVarId_clearValue___lam__0___closed__1_once, _init_l_Lean_MVarId_clearValue___lam__0___closed__1);
v___x_2547_ = l_Lean_Expr_fvar___override(v_fvarId_2484_);
v___x_2548_ = l_Lean_MessageData_ofExpr(v___x_2547_);
v___x_2549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2549_, 0, v___x_2546_);
lean_ctor_set(v___x_2549_, 1, v___x_2548_);
v___x_2550_ = lean_obj_once(&l_Lean_MVarId_clearValue___lam__0___closed__3, &l_Lean_MVarId_clearValue___lam__0___closed__3_once, _init_l_Lean_MVarId_clearValue___lam__0___closed__3);
v___x_2551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2551_, 0, v___x_2549_);
lean_ctor_set(v___x_2551_, 1, v___x_2550_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set_tag(v___x_2541_, 1);
lean_ctor_set(v___x_2541_, 0, v___x_2551_);
v___x_2553_ = v___x_2541_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v___x_2551_);
v___x_2553_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
lean_inc(v_mvarId_2486_);
v___x_2554_ = lean_alloc_closure((void*)(l_Lean_Meta_throwTacticEx___boxed), 9, 4);
lean_closure_set(v___x_2554_, 0, lean_box(0));
lean_closure_set(v___x_2554_, 1, v___x_2485_);
lean_closure_set(v___x_2554_, 2, v_mvarId_2486_);
lean_closure_set(v___x_2554_, 3, v___x_2553_);
v___x_2555_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_2486_, v___x_2554_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_dec_ref(v___x_2555_);
v___y_2495_ = v_a_2539_;
v___y_2496_ = v___y_2529_;
v___y_2497_ = v___y_2530_;
v___y_2498_ = v___y_2531_;
v___y_2499_ = v___y_2532_;
goto v___jp_2494_;
}
else
{
lean_object* v_a_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2563_; 
lean_dec(v_a_2539_);
lean_dec(v_a_2493_);
lean_dec_ref(v_fvars_2483_);
lean_dec(v_a_2482_);
lean_dec(v_mvarId_x27_2481_);
v_a_2556_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2558_ = v___x_2555_;
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_a_2556_);
lean_dec(v___x_2555_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2561_; 
if (v_isShared_2559_ == 0)
{
v___x_2561_ = v___x_2558_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_a_2556_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
}
}
}
else
{
lean_del_object(v___x_2541_);
lean_dec(v_mvarId_2486_);
lean_dec(v___x_2485_);
lean_dec(v_fvarId_2484_);
v___y_2495_ = v_a_2539_;
v___y_2496_ = v___y_2529_;
v___y_2497_ = v___y_2530_;
v___y_2498_ = v___y_2531_;
v___y_2499_ = v___y_2532_;
goto v___jp_2494_;
}
}
else
{
lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2572_; 
lean_del_object(v___x_2541_);
lean_dec(v_a_2539_);
lean_dec(v_a_2493_);
lean_dec(v_mvarId_2486_);
lean_dec(v___x_2485_);
lean_dec(v_fvarId_2484_);
lean_dec_ref(v_fvars_2483_);
lean_dec(v_a_2482_);
lean_dec(v_mvarId_x27_2481_);
v_a_2565_ = lean_ctor_get(v___x_2543_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2567_ = v___x_2543_;
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___x_2543_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2570_; 
if (v_isShared_2568_ == 0)
{
v___x_2570_ = v___x_2567_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_a_2565_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
}
}
}
}
else
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2599_; 
lean_dec(v_mvarId_2486_);
lean_dec(v___x_2485_);
lean_dec(v_fvarId_2484_);
lean_dec_ref(v_fvars_2483_);
lean_dec(v_a_2482_);
lean_dec(v_mvarId_x27_2481_);
v_a_2592_ = lean_ctor_get(v___x_2492_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2594_ = v___x_2492_;
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2492_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2597_; 
if (v_isShared_2595_ == 0)
{
v___x_2597_ = v___x_2594_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_a_2592_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearValue___lam__0___boxed(lean_object* v_mvarId_x27_2600_, lean_object* v_a_2601_, lean_object* v_fvars_2602_, lean_object* v_fvarId_2603_, lean_object* v___x_2604_, lean_object* v_mvarId_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_){
_start:
{
lean_object* v_res_2611_; 
v_res_2611_ = l_Lean_MVarId_clearValue___lam__0(v_mvarId_x27_2600_, v_a_2601_, v_fvars_2602_, v_fvarId_2603_, v___x_2604_, v_mvarId_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2608_);
lean_dec(v___y_2607_);
lean_dec_ref(v___y_2606_);
return v_res_2611_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearValue___lam__1(lean_object* v_a_2612_, lean_object* v_fvarId_2613_, lean_object* v___x_2614_, lean_object* v_mvarId_2615_, lean_object* v_mvarId_x27_2616_, lean_object* v_fvars_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_){
_start:
{
lean_object* v___f_2623_; lean_object* v___x_2624_; 
lean_inc(v_mvarId_x27_2616_);
v___f_2623_ = lean_alloc_closure((void*)(l_Lean_MVarId_clearValue___lam__0___boxed), 11, 6);
lean_closure_set(v___f_2623_, 0, v_mvarId_x27_2616_);
lean_closure_set(v___f_2623_, 1, v_a_2612_);
lean_closure_set(v___f_2623_, 2, v_fvars_2617_);
lean_closure_set(v___f_2623_, 3, v_fvarId_2613_);
lean_closure_set(v___f_2623_, 4, v___x_2614_);
lean_closure_set(v___f_2623_, 5, v_mvarId_2615_);
v___x_2624_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_x27_2616_, v___f_2623_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
return v___x_2624_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearValue___lam__1___boxed(lean_object* v_a_2625_, lean_object* v_fvarId_2626_, lean_object* v___x_2627_, lean_object* v_mvarId_2628_, lean_object* v_mvarId_x27_2629_, lean_object* v_fvars_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_){
_start:
{
lean_object* v_res_2636_; 
v_res_2636_ = l_Lean_MVarId_clearValue___lam__1(v_a_2625_, v_fvarId_2626_, v___x_2627_, v_mvarId_2628_, v_mvarId_x27_2629_, v_fvars_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec(v___y_2632_);
lean_dec_ref(v___y_2631_);
return v_res_2636_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearValue(lean_object* v_mvarId_2640_, lean_object* v_fvarId_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_){
_start:
{
lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2647_ = ((lean_object*)(l_Lean_MVarId_clearValue___closed__1));
lean_inc(v_mvarId_2640_);
v___x_2648_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2640_, v___x_2647_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_);
if (lean_obj_tag(v___x_2648_) == 0)
{
lean_object* v___x_2649_; 
lean_dec_ref(v___x_2648_);
lean_inc(v_mvarId_2640_);
v___x_2649_ = l_Lean_MVarId_getTag(v_mvarId_2640_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_);
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_object* v_a_2650_; lean_object* v___f_2651_; lean_object* v___x_2652_; 
v_a_2650_ = lean_ctor_get(v___x_2649_, 0);
lean_inc(v_a_2650_);
lean_dec_ref(v___x_2649_);
lean_inc(v_mvarId_2640_);
lean_inc(v_fvarId_2641_);
v___f_2651_ = lean_alloc_closure((void*)(l_Lean_MVarId_clearValue___lam__1___boxed), 11, 4);
lean_closure_set(v___f_2651_, 0, v_a_2650_);
lean_closure_set(v___f_2651_, 1, v_fvarId_2641_);
lean_closure_set(v___f_2651_, 2, v___x_2647_);
lean_closure_set(v___f_2651_, 3, v_mvarId_2640_);
v___x_2652_ = l_Lean_MVarId_withRevertedFrom___redArg(v_mvarId_2640_, v_fvarId_2641_, v___f_2651_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_);
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_object* v_a_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2661_; 
v_a_2653_ = lean_ctor_get(v___x_2652_, 0);
v_isSharedCheck_2661_ = !lean_is_exclusive(v___x_2652_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2655_ = v___x_2652_;
v_isShared_2656_ = v_isSharedCheck_2661_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_a_2653_);
lean_dec(v___x_2652_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2661_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v_snd_2657_; lean_object* v___x_2659_; 
v_snd_2657_ = lean_ctor_get(v_a_2653_, 1);
lean_inc(v_snd_2657_);
lean_dec(v_a_2653_);
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 0, v_snd_2657_);
v___x_2659_ = v___x_2655_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_snd_2657_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
else
{
lean_object* v_a_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2669_; 
v_a_2662_ = lean_ctor_get(v___x_2652_, 0);
v_isSharedCheck_2669_ = !lean_is_exclusive(v___x_2652_);
if (v_isSharedCheck_2669_ == 0)
{
v___x_2664_ = v___x_2652_;
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_a_2662_);
lean_dec(v___x_2652_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v___x_2667_; 
if (v_isShared_2665_ == 0)
{
v___x_2667_ = v___x_2664_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v_a_2662_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
}
}
}
}
else
{
lean_object* v_a_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2677_; 
lean_dec(v_fvarId_2641_);
lean_dec(v_mvarId_2640_);
v_a_2670_ = lean_ctor_get(v___x_2649_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2672_ = v___x_2649_;
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_a_2670_);
lean_dec(v___x_2649_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2675_; 
if (v_isShared_2673_ == 0)
{
v___x_2675_ = v___x_2672_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_a_2670_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
}
else
{
lean_object* v_a_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2685_; 
lean_dec(v_fvarId_2641_);
lean_dec(v_mvarId_2640_);
v_a_2678_ = lean_ctor_get(v___x_2648_, 0);
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2648_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2680_ = v___x_2648_;
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_a_2678_);
lean_dec(v___x_2648_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2683_; 
if (v_isShared_2681_ == 0)
{
v___x_2683_ = v___x_2680_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_a_2678_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
return v___x_2683_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearValue___boxed(lean_object* v_mvarId_2686_, lean_object* v_fvarId_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_){
_start:
{
lean_object* v_res_2693_; 
v_res_2693_ = l_Lean_MVarId_clearValue(v_mvarId_2686_, v_fvarId_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
lean_dec(v_a_2691_);
lean_dec_ref(v_a_2690_);
lean_dec(v_a_2689_);
lean_dec_ref(v_a_2688_);
return v_res_2693_;
}
}
lean_object* runtime_initialize_Lean_Elab_InfoTree_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_MatchUtil(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Assert(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Replace(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_InfoTree_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_MatchUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Assert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Replace(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_InfoTree_Main(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_MatchUtil(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Assert(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Replace(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_InfoTree_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_MatchUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Assert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Replace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Replace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Replace(builtin);
}
#ifdef __cplusplus
}
#endif
