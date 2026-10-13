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
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_matchEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_equal(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedTypeHint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_setType___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqMP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assertAfter_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
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
lean_object* l_Lean_Expr_letValue_x21(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letName_x21(lean_object*);
lean_object* l_Lean_Expr_letType_x21(lean_object*);
lean_object* l_Lean_Expr_letBody_x21(lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLet(lean_object*);
lean_object* l_Lean_MVarId_revertFrom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_setType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_get_x21(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalInstancesImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_setFVarType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_revert(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlTOfPure___redArg(lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_MVarId_withContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_replaceTargetDefEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "change"};
static const lean_object* l_Lean_MVarId_replaceTargetDefEq___closed__0 = (const lean_object*)&l_Lean_MVarId_replaceTargetDefEq___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_replaceTargetDefEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_replaceTargetDefEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(125, 120, 133, 160, 129, 235, 229, 190)}};
static const lean_object* l_Lean_MVarId_replaceTargetDefEq___closed__1 = (const lean_object*)&l_Lean_MVarId_replaceTargetDefEq___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replace___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replace___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDecl___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDecl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_MVarId_replaceLocalDecl___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_replaceLocalDecl___closed__0;
static lean_once_cell_t l_Lean_MVarId_replaceLocalDecl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_replaceLocalDecl___closed__1;
static const lean_closure_object l_Lean_MVarId_replaceLocalDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MVarId_replaceLocalDecl___closed__2 = (const lean_object*)&l_Lean_MVarId_replaceLocalDecl___closed__2_value;
static const lean_closure_object l_Lean_MVarId_replaceLocalDecl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MVarId_replaceLocalDecl___closed__3 = (const lean_object*)&l_Lean_MVarId_replaceLocalDecl___closed__3_value;
static const lean_closure_object l_Lean_MVarId_replaceLocalDecl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MVarId_replaceLocalDecl___closed__4 = (const lean_object*)&l_Lean_MVarId_replaceLocalDecl___closed__4_value;
static const lean_closure_object l_Lean_MVarId_replaceLocalDecl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MVarId_replaceLocalDecl___closed__5 = (const lean_object*)&l_Lean_MVarId_replaceLocalDecl___closed__5_value;
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
LEAN_EXPORT lean_object* l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg(lean_object* v_x_87_, size_t v_x_88_, size_t v_x_89_, lean_object* v_x_90_, lean_object* v_x_91_){
_start:
{
if (lean_obj_tag(v_x_87_) == 0)
{
lean_object* v_es_92_; size_t v___x_93_; size_t v___x_94_; lean_object* v_j_95_; lean_object* v___x_96_; uint8_t v___x_97_; 
v_es_92_ = lean_ctor_get(v_x_87_, 0);
v___x_93_ = ((size_t)31ULL);
v___x_94_ = lean_usize_land(v_x_88_, v___x_93_);
v_j_95_ = lean_usize_to_nat(v___x_94_);
v___x_96_ = lean_array_get_size(v_es_92_);
v___x_97_ = lean_nat_dec_lt(v_j_95_, v___x_96_);
if (v___x_97_ == 0)
{
lean_dec(v_j_95_);
lean_dec(v_x_91_);
lean_dec(v_x_90_);
return v_x_87_;
}
else
{
lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_136_; 
lean_inc_ref(v_es_92_);
v_isSharedCheck_136_ = !lean_is_exclusive(v_x_87_);
if (v_isSharedCheck_136_ == 0)
{
lean_object* v_unused_137_; 
v_unused_137_ = lean_ctor_get(v_x_87_, 0);
lean_dec(v_unused_137_);
v___x_99_ = v_x_87_;
v_isShared_100_ = v_isSharedCheck_136_;
goto v_resetjp_98_;
}
else
{
lean_dec(v_x_87_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_136_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v_v_101_; lean_object* v___x_102_; lean_object* v_xs_x27_103_; lean_object* v___y_105_; 
v_v_101_ = lean_array_fget(v_es_92_, v_j_95_);
v___x_102_ = lean_box(0);
v_xs_x27_103_ = lean_array_fset(v_es_92_, v_j_95_, v___x_102_);
switch(lean_obj_tag(v_v_101_))
{
case 0:
{
lean_object* v_key_110_; lean_object* v_val_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_121_; 
v_key_110_ = lean_ctor_get(v_v_101_, 0);
v_val_111_ = lean_ctor_get(v_v_101_, 1);
v_isSharedCheck_121_ = !lean_is_exclusive(v_v_101_);
if (v_isSharedCheck_121_ == 0)
{
v___x_113_ = v_v_101_;
v_isShared_114_ = v_isSharedCheck_121_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_val_111_);
lean_inc(v_key_110_);
lean_dec(v_v_101_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_121_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
uint8_t v___x_115_; 
v___x_115_ = l_Lean_instBEqMVarId_beq(v_x_90_, v_key_110_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; lean_object* v___x_117_; 
lean_del_object(v___x_113_);
v___x_116_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_110_, v_val_111_, v_x_90_, v_x_91_);
v___x_117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
v___y_105_ = v___x_117_;
goto v___jp_104_;
}
else
{
lean_object* v___x_119_; 
lean_dec(v_val_111_);
lean_dec(v_key_110_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 1, v_x_91_);
lean_ctor_set(v___x_113_, 0, v_x_90_);
v___x_119_ = v___x_113_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v_x_90_);
lean_ctor_set(v_reuseFailAlloc_120_, 1, v_x_91_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
v___y_105_ = v___x_119_;
goto v___jp_104_;
}
}
}
}
case 1:
{
lean_object* v_node_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_134_; 
v_node_122_ = lean_ctor_get(v_v_101_, 0);
v_isSharedCheck_134_ = !lean_is_exclusive(v_v_101_);
if (v_isSharedCheck_134_ == 0)
{
v___x_124_ = v_v_101_;
v_isShared_125_ = v_isSharedCheck_134_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_node_122_);
lean_dec(v_v_101_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_134_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
size_t v___x_126_; size_t v___x_127_; size_t v___x_128_; size_t v___x_129_; lean_object* v___x_130_; lean_object* v___x_132_; 
v___x_126_ = ((size_t)5ULL);
v___x_127_ = lean_usize_shift_right(v_x_88_, v___x_126_);
v___x_128_ = ((size_t)1ULL);
v___x_129_ = lean_usize_add(v_x_89_, v___x_128_);
v___x_130_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg(v_node_122_, v___x_127_, v___x_129_, v_x_90_, v_x_91_);
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 0, v___x_130_);
v___x_132_ = v___x_124_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v___x_130_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
v___y_105_ = v___x_132_;
goto v___jp_104_;
}
}
}
default: 
{
lean_object* v___x_135_; 
v___x_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_135_, 0, v_x_90_);
lean_ctor_set(v___x_135_, 1, v_x_91_);
v___y_105_ = v___x_135_;
goto v___jp_104_;
}
}
v___jp_104_:
{
lean_object* v___x_106_; lean_object* v___x_108_; 
v___x_106_ = lean_array_fset(v_xs_x27_103_, v_j_95_, v___y_105_);
lean_dec(v_j_95_);
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 0, v___x_106_);
v___x_108_ = v___x_99_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v___x_106_);
v___x_108_ = v_reuseFailAlloc_109_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
return v___x_108_;
}
}
}
}
}
else
{
lean_object* v_ks_138_; lean_object* v_vs_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_157_; 
v_ks_138_ = lean_ctor_get(v_x_87_, 0);
v_vs_139_ = lean_ctor_get(v_x_87_, 1);
v_isSharedCheck_157_ = !lean_is_exclusive(v_x_87_);
if (v_isSharedCheck_157_ == 0)
{
v___x_141_ = v_x_87_;
v_isShared_142_ = v_isSharedCheck_157_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_vs_139_);
lean_inc(v_ks_138_);
lean_dec(v_x_87_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_157_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_144_; 
if (v_isShared_142_ == 0)
{
v___x_144_ = v___x_141_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_ks_138_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v_vs_139_);
v___x_144_ = v_reuseFailAlloc_156_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
lean_object* v_newNode_145_; size_t v___x_146_; uint8_t v___x_147_; 
v_newNode_145_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3___redArg(v___x_144_, v_x_90_, v_x_91_);
v___x_146_ = ((size_t)7ULL);
v___x_147_ = lean_usize_dec_le(v___x_146_, v_x_89_);
if (v___x_147_ == 0)
{
lean_object* v___x_148_; lean_object* v___x_149_; uint8_t v___x_150_; 
v___x_148_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_145_);
v___x_149_ = lean_unsigned_to_nat(4u);
v___x_150_ = lean_nat_dec_lt(v___x_148_, v___x_149_);
lean_dec(v___x_148_);
if (v___x_150_ == 0)
{
lean_object* v_ks_151_; lean_object* v_vs_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v_ks_151_ = lean_ctor_get(v_newNode_145_, 0);
lean_inc_ref(v_ks_151_);
v_vs_152_ = lean_ctor_get(v_newNode_145_, 1);
lean_inc_ref(v_vs_152_);
lean_dec_ref(v_newNode_145_);
v___x_153_ = lean_unsigned_to_nat(0u);
v___x_154_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_155_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4___redArg(v_x_89_, v_ks_151_, v_vs_152_, v___x_153_, v___x_154_);
lean_dec_ref(v_vs_152_);
lean_dec_ref(v_ks_151_);
return v___x_155_;
}
else
{
return v_newNode_145_;
}
}
else
{
return v_newNode_145_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4___redArg(size_t v_depth_158_, lean_object* v_keys_159_, lean_object* v_vals_160_, lean_object* v_i_161_, lean_object* v_entries_162_){
_start:
{
lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_163_ = lean_array_get_size(v_keys_159_);
v___x_164_ = lean_nat_dec_lt(v_i_161_, v___x_163_);
if (v___x_164_ == 0)
{
lean_dec(v_i_161_);
return v_entries_162_;
}
else
{
lean_object* v_k_165_; lean_object* v_v_166_; uint64_t v___x_167_; size_t v_h_168_; size_t v___x_169_; lean_object* v___x_170_; size_t v___x_171_; size_t v___x_172_; size_t v___x_173_; size_t v_h_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v_k_165_ = lean_array_fget_borrowed(v_keys_159_, v_i_161_);
v_v_166_ = lean_array_fget_borrowed(v_vals_160_, v_i_161_);
v___x_167_ = l_Lean_instHashableMVarId_hash(v_k_165_);
v_h_168_ = lean_uint64_to_usize(v___x_167_);
v___x_169_ = ((size_t)5ULL);
v___x_170_ = lean_unsigned_to_nat(1u);
v___x_171_ = ((size_t)1ULL);
v___x_172_ = lean_usize_sub(v_depth_158_, v___x_171_);
v___x_173_ = lean_usize_mul(v___x_169_, v___x_172_);
v_h_174_ = lean_usize_shift_right(v_h_168_, v___x_173_);
v___x_175_ = lean_nat_add(v_i_161_, v___x_170_);
lean_dec(v_i_161_);
lean_inc(v_v_166_);
lean_inc(v_k_165_);
v___x_176_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg(v_entries_162_, v_h_174_, v_depth_158_, v_k_165_, v_v_166_);
v_i_161_ = v___x_175_;
v_entries_162_ = v___x_176_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_depth_178_, lean_object* v_keys_179_, lean_object* v_vals_180_, lean_object* v_i_181_, lean_object* v_entries_182_){
_start:
{
size_t v_depth_boxed_183_; lean_object* v_res_184_; 
v_depth_boxed_183_ = lean_unbox_usize(v_depth_178_);
lean_dec(v_depth_178_);
v_res_184_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_boxed_183_, v_keys_179_, v_vals_180_, v_i_181_, v_entries_182_);
lean_dec_ref(v_vals_180_);
lean_dec_ref(v_keys_179_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_185_, lean_object* v_x_186_, lean_object* v_x_187_, lean_object* v_x_188_, lean_object* v_x_189_){
_start:
{
size_t v_x_1699__boxed_190_; size_t v_x_1700__boxed_191_; lean_object* v_res_192_; 
v_x_1699__boxed_190_ = lean_unbox_usize(v_x_186_);
lean_dec(v_x_186_);
v_x_1700__boxed_191_ = lean_unbox_usize(v_x_187_);
lean_dec(v_x_187_);
v_res_192_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg(v_x_185_, v_x_1699__boxed_190_, v_x_1700__boxed_191_, v_x_188_, v_x_189_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0___redArg(lean_object* v_x_193_, lean_object* v_x_194_, lean_object* v_x_195_){
_start:
{
uint64_t v___x_196_; size_t v___x_197_; size_t v___x_198_; lean_object* v___x_199_; 
v___x_196_ = l_Lean_instHashableMVarId_hash(v_x_194_);
v___x_197_ = lean_uint64_to_usize(v___x_196_);
v___x_198_ = ((size_t)1ULL);
v___x_199_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg(v_x_193_, v___x_197_, v___x_198_, v_x_194_, v_x_195_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg(lean_object* v_mvarId_200_, lean_object* v_val_201_, lean_object* v___y_202_){
_start:
{
lean_object* v___x_204_; lean_object* v_mctx_205_; lean_object* v_cache_206_; lean_object* v_zetaDeltaFVarIds_207_; lean_object* v_postponed_208_; lean_object* v_diag_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_239_; 
v___x_204_ = lean_st_ref_take(v___y_202_);
v_mctx_205_ = lean_ctor_get(v___x_204_, 0);
v_cache_206_ = lean_ctor_get(v___x_204_, 1);
v_zetaDeltaFVarIds_207_ = lean_ctor_get(v___x_204_, 2);
v_postponed_208_ = lean_ctor_get(v___x_204_, 3);
v_diag_209_ = lean_ctor_get(v___x_204_, 4);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_239_ == 0)
{
v___x_211_ = v___x_204_;
v_isShared_212_ = v_isSharedCheck_239_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_diag_209_);
lean_inc(v_postponed_208_);
lean_inc(v_zetaDeltaFVarIds_207_);
lean_inc(v_cache_206_);
lean_inc(v_mctx_205_);
lean_dec(v___x_204_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_239_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v_depth_213_; lean_object* v_levelAssignDepth_214_; lean_object* v_lmvarCounter_215_; lean_object* v_mvarCounter_216_; lean_object* v_lDecls_217_; lean_object* v_decls_218_; lean_object* v_userNames_219_; lean_object* v_lAssignment_220_; lean_object* v_eAssignment_221_; lean_object* v_dAssignment_222_; lean_object* v_instanceTypedMVars_223_; lean_object* v_synthNormMemo_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_238_; 
v_depth_213_ = lean_ctor_get(v_mctx_205_, 0);
v_levelAssignDepth_214_ = lean_ctor_get(v_mctx_205_, 1);
v_lmvarCounter_215_ = lean_ctor_get(v_mctx_205_, 2);
v_mvarCounter_216_ = lean_ctor_get(v_mctx_205_, 3);
v_lDecls_217_ = lean_ctor_get(v_mctx_205_, 4);
v_decls_218_ = lean_ctor_get(v_mctx_205_, 5);
v_userNames_219_ = lean_ctor_get(v_mctx_205_, 6);
v_lAssignment_220_ = lean_ctor_get(v_mctx_205_, 7);
v_eAssignment_221_ = lean_ctor_get(v_mctx_205_, 8);
v_dAssignment_222_ = lean_ctor_get(v_mctx_205_, 9);
v_instanceTypedMVars_223_ = lean_ctor_get(v_mctx_205_, 10);
v_synthNormMemo_224_ = lean_ctor_get(v_mctx_205_, 11);
v_isSharedCheck_238_ = !lean_is_exclusive(v_mctx_205_);
if (v_isSharedCheck_238_ == 0)
{
v___x_226_ = v_mctx_205_;
v_isShared_227_ = v_isSharedCheck_238_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_synthNormMemo_224_);
lean_inc(v_instanceTypedMVars_223_);
lean_inc(v_dAssignment_222_);
lean_inc(v_eAssignment_221_);
lean_inc(v_lAssignment_220_);
lean_inc(v_userNames_219_);
lean_inc(v_decls_218_);
lean_inc(v_lDecls_217_);
lean_inc(v_mvarCounter_216_);
lean_inc(v_lmvarCounter_215_);
lean_inc(v_levelAssignDepth_214_);
lean_inc(v_depth_213_);
lean_dec(v_mctx_205_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_238_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_231_; 
v___x_228_ = lean_box(0);
v___x_229_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0___redArg(v_eAssignment_221_, v_mvarId_200_, v_val_201_);
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 8, v___x_229_);
v___x_231_ = v___x_226_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_depth_213_);
lean_ctor_set(v_reuseFailAlloc_237_, 1, v_levelAssignDepth_214_);
lean_ctor_set(v_reuseFailAlloc_237_, 2, v_lmvarCounter_215_);
lean_ctor_set(v_reuseFailAlloc_237_, 3, v_mvarCounter_216_);
lean_ctor_set(v_reuseFailAlloc_237_, 4, v_lDecls_217_);
lean_ctor_set(v_reuseFailAlloc_237_, 5, v_decls_218_);
lean_ctor_set(v_reuseFailAlloc_237_, 6, v_userNames_219_);
lean_ctor_set(v_reuseFailAlloc_237_, 7, v_lAssignment_220_);
lean_ctor_set(v_reuseFailAlloc_237_, 8, v___x_229_);
lean_ctor_set(v_reuseFailAlloc_237_, 9, v_dAssignment_222_);
lean_ctor_set(v_reuseFailAlloc_237_, 10, v_instanceTypedMVars_223_);
lean_ctor_set(v_reuseFailAlloc_237_, 11, v_synthNormMemo_224_);
v___x_231_ = v_reuseFailAlloc_237_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
lean_object* v___x_233_; 
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 0, v___x_231_);
v___x_233_ = v___x_211_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v___x_231_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v_cache_206_);
lean_ctor_set(v_reuseFailAlloc_236_, 2, v_zetaDeltaFVarIds_207_);
lean_ctor_set(v_reuseFailAlloc_236_, 3, v_postponed_208_);
lean_ctor_set(v_reuseFailAlloc_236_, 4, v_diag_209_);
v___x_233_ = v_reuseFailAlloc_236_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = lean_st_ref_put(v___y_202_, v___x_233_);
v___x_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_235_, 0, v___x_228_);
return v___x_235_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg___boxed(lean_object* v_mvarId_240_, lean_object* v_val_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg(v_mvarId_240_, v_val_241_, v___y_242_);
lean_dec(v___y_242_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetEq___lam__0(lean_object* v_mvarId_250_, lean_object* v___x_251_, lean_object* v_targetNew_252_, lean_object* v_eqProof_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_){
_start:
{
lean_object* v___x_259_; 
lean_inc(v_mvarId_250_);
v___x_259_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_250_, v___x_251_, v___y_254_, v___y_255_, v___y_256_, v___y_257_);
if (lean_obj_tag(v___x_259_) == 0)
{
lean_object* v___x_260_; 
lean_dec_ref_known(v___x_259_, 1);
lean_inc(v_mvarId_250_);
v___x_260_ = l_Lean_MVarId_getTag(v_mvarId_250_, v___y_254_, v___y_255_, v___y_256_, v___y_257_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_object* v_a_261_; lean_object* v___x_262_; 
v_a_261_ = lean_ctor_get(v___x_260_, 0);
lean_inc(v_a_261_);
lean_dec_ref_known(v___x_260_, 1);
lean_inc_ref(v_targetNew_252_);
v___x_262_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_targetNew_252_, v_a_261_, v___y_254_, v___y_255_, v___y_256_, v___y_257_);
if (lean_obj_tag(v___x_262_) == 0)
{
lean_object* v_a_263_; lean_object* v___x_264_; 
v_a_263_ = lean_ctor_get(v___x_262_, 0);
lean_inc(v_a_263_);
lean_dec_ref_known(v___x_262_, 1);
lean_inc(v_mvarId_250_);
v___x_264_ = l_Lean_MVarId_getType(v_mvarId_250_, v___y_254_, v___y_255_, v___y_256_, v___y_257_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v_a_265_; lean_object* v___x_266_; 
v_a_265_ = lean_ctor_get(v___x_264_, 0);
lean_inc_n(v_a_265_, 2);
lean_dec_ref_known(v___x_264_, 1);
v___x_266_ = l_Lean_Meta_getLevel(v_a_265_, v___y_254_, v___y_255_, v___y_256_, v___y_257_);
if (lean_obj_tag(v___x_266_) == 0)
{
lean_object* v_a_267_; lean_object* v___x_268_; 
v_a_267_ = lean_ctor_get(v___x_266_, 0);
lean_inc(v_a_267_);
lean_dec_ref_known(v___x_266_, 1);
lean_inc_ref(v_targetNew_252_);
lean_inc(v_a_265_);
v___x_268_ = l_Lean_Meta_mkEq(v_a_265_, v_targetNew_252_, v___y_254_, v___y_255_, v___y_256_, v___y_257_);
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v_a_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_290_; 
v_a_269_ = lean_ctor_get(v___x_268_, 0);
lean_inc(v_a_269_);
lean_dec_ref_known(v___x_268_, 1);
v___x_270_ = l_Lean_Meta_mkExpectedPropHint(v_eqProof_253_, v_a_269_);
v___x_271_ = ((lean_object*)(l_Lean_MVarId_replaceTargetEq___lam__0___closed__2));
v___x_272_ = lean_box(0);
v___x_273_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_273_, 0, v_a_267_);
lean_ctor_set(v___x_273_, 1, v___x_272_);
v___x_274_ = l_Lean_mkConst(v___x_271_, v___x_273_);
v___x_275_ = lean_unsigned_to_nat(4u);
v___x_276_ = lean_mk_empty_array_with_capacity(v___x_275_);
v___x_277_ = lean_array_push(v___x_276_, v_a_265_);
v___x_278_ = lean_array_push(v___x_277_, v_targetNew_252_);
v___x_279_ = lean_array_push(v___x_278_, v___x_270_);
lean_inc(v_a_263_);
v___x_280_ = lean_array_push(v___x_279_, v_a_263_);
v___x_281_ = l_Lean_mkAppN(v___x_274_, v___x_280_);
lean_dec_ref(v___x_280_);
v___x_282_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg(v_mvarId_250_, v___x_281_, v___y_255_);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_290_ == 0)
{
lean_object* v_unused_291_; 
v_unused_291_ = lean_ctor_get(v___x_282_, 0);
lean_dec(v_unused_291_);
v___x_284_ = v___x_282_;
v_isShared_285_ = v_isSharedCheck_290_;
goto v_resetjp_283_;
}
else
{
lean_dec(v___x_282_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_290_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_286_; lean_object* v___x_288_; 
v___x_286_ = l_Lean_Expr_mvarId_x21(v_a_263_);
lean_dec(v_a_263_);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 0, v___x_286_);
v___x_288_ = v___x_284_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v___x_286_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
else
{
lean_object* v_a_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_299_; 
lean_dec(v_a_267_);
lean_dec(v_a_265_);
lean_dec(v_a_263_);
lean_dec_ref(v_eqProof_253_);
lean_dec_ref(v_targetNew_252_);
lean_dec(v_mvarId_250_);
v_a_292_ = lean_ctor_get(v___x_268_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_299_ == 0)
{
v___x_294_ = v___x_268_;
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_a_292_);
lean_dec(v___x_268_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_297_; 
if (v_isShared_295_ == 0)
{
v___x_297_ = v___x_294_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_a_292_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
}
else
{
lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_307_; 
lean_dec(v_a_265_);
lean_dec(v_a_263_);
lean_dec_ref(v_eqProof_253_);
lean_dec_ref(v_targetNew_252_);
lean_dec(v_mvarId_250_);
v_a_300_ = lean_ctor_get(v___x_266_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_307_ == 0)
{
v___x_302_ = v___x_266_;
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_dec(v___x_266_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_303_ == 0)
{
v___x_305_ = v___x_302_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_a_300_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
else
{
lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_315_; 
lean_dec(v_a_263_);
lean_dec_ref(v_eqProof_253_);
lean_dec_ref(v_targetNew_252_);
lean_dec(v_mvarId_250_);
v_a_308_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_315_ == 0)
{
v___x_310_ = v___x_264_;
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_264_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_313_; 
if (v_isShared_311_ == 0)
{
v___x_313_ = v___x_310_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_a_308_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
else
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_323_; 
lean_dec_ref(v_eqProof_253_);
lean_dec_ref(v_targetNew_252_);
lean_dec(v_mvarId_250_);
v_a_316_ = lean_ctor_get(v___x_262_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_323_ == 0)
{
v___x_318_ = v___x_262_;
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_262_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_321_; 
if (v_isShared_319_ == 0)
{
v___x_321_ = v___x_318_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_a_316_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
else
{
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_331_; 
lean_dec_ref(v_eqProof_253_);
lean_dec_ref(v_targetNew_252_);
lean_dec(v_mvarId_250_);
v_a_324_ = lean_ctor_get(v___x_260_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_331_ == 0)
{
v___x_326_ = v___x_260_;
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_260_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_329_; 
if (v_isShared_327_ == 0)
{
v___x_329_ = v___x_326_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_a_324_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
else
{
lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_339_; 
lean_dec_ref(v_eqProof_253_);
lean_dec_ref(v_targetNew_252_);
lean_dec(v_mvarId_250_);
v_a_332_ = lean_ctor_get(v___x_259_, 0);
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_339_ == 0)
{
v___x_334_ = v___x_259_;
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v___x_259_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_337_; 
if (v_isShared_335_ == 0)
{
v___x_337_ = v___x_334_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_a_332_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetEq___lam__0___boxed(lean_object* v_mvarId_340_, lean_object* v___x_341_, lean_object* v_targetNew_342_, lean_object* v_eqProof_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_MVarId_replaceTargetEq___lam__0(v_mvarId_340_, v___x_341_, v_targetNew_342_, v_eqProof_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetEq(lean_object* v_mvarId_353_, lean_object* v_targetNew_354_, lean_object* v_eqProof_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_){
_start:
{
lean_object* v___x_361_; lean_object* v___f_362_; lean_object* v___x_363_; 
v___x_361_ = ((lean_object*)(l_Lean_MVarId_replaceTargetEq___closed__1));
lean_inc(v_mvarId_353_);
v___f_362_ = lean_alloc_closure((void*)(l_Lean_MVarId_replaceTargetEq___lam__0___boxed), 9, 4);
lean_closure_set(v___f_362_, 0, v_mvarId_353_);
lean_closure_set(v___f_362_, 1, v___x_361_);
lean_closure_set(v___f_362_, 2, v_targetNew_354_);
lean_closure_set(v___f_362_, 3, v_eqProof_355_);
v___x_363_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_353_, v___f_362_, v_a_356_, v_a_357_, v_a_358_, v_a_359_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetEq___boxed(lean_object* v_mvarId_364_, lean_object* v_targetNew_365_, lean_object* v_eqProof_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Lean_MVarId_replaceTargetEq(v_mvarId_364_, v_targetNew_365_, v_eqProof_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
lean_dec(v_a_368_);
lean_dec_ref(v_a_367_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0(lean_object* v_mvarId_373_, lean_object* v_val_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg(v_mvarId_373_, v_val_374_, v___y_376_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___boxed(lean_object* v_mvarId_381_, lean_object* v_val_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0(v_mvarId_381_, v_val_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0(lean_object* v_00_u03b2_389_, lean_object* v_x_390_, lean_object* v_x_391_, lean_object* v_x_392_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0___redArg(v_x_390_, v_x_391_, v_x_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_394_, lean_object* v_x_395_, size_t v_x_396_, size_t v_x_397_, lean_object* v_x_398_, lean_object* v_x_399_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg(v_x_395_, v_x_396_, v_x_397_, v_x_398_, v_x_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_401_, lean_object* v_x_402_, lean_object* v_x_403_, lean_object* v_x_404_, lean_object* v_x_405_, lean_object* v_x_406_){
_start:
{
size_t v_x_2150__boxed_407_; size_t v_x_2151__boxed_408_; lean_object* v_res_409_; 
v_x_2150__boxed_407_ = lean_unbox_usize(v_x_403_);
lean_dec(v_x_403_);
v_x_2151__boxed_408_ = lean_unbox_usize(v_x_404_);
lean_dec(v_x_404_);
v_res_409_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2(v_00_u03b2_401_, v_x_402_, v_x_2150__boxed_407_, v_x_2151__boxed_408_, v_x_405_, v_x_406_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_410_, lean_object* v_n_411_, lean_object* v_k_412_, lean_object* v_v_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3___redArg(v_n_411_, v_k_412_, v_v_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_415_, size_t v_depth_416_, lean_object* v_keys_417_, lean_object* v_vals_418_, lean_object* v_heq_419_, lean_object* v_i_420_, lean_object* v_entries_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_416_, v_keys_417_, v_vals_418_, v_i_420_, v_entries_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_423_, lean_object* v_depth_424_, lean_object* v_keys_425_, lean_object* v_vals_426_, lean_object* v_heq_427_, lean_object* v_i_428_, lean_object* v_entries_429_){
_start:
{
size_t v_depth_boxed_430_; lean_object* v_res_431_; 
v_depth_boxed_430_ = lean_unbox_usize(v_depth_424_);
lean_dec(v_depth_424_);
v_res_431_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_423_, v_depth_boxed_430_, v_keys_425_, v_vals_426_, v_heq_427_, v_i_428_, v_entries_429_);
lean_dec_ref(v_vals_426_);
lean_dec_ref(v_keys_425_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_432_, lean_object* v_x_433_, lean_object* v_x_434_, lean_object* v_x_435_, lean_object* v_x_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_x_433_, v_x_434_, v_x_435_, v_x_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(lean_object* v_e_438_, lean_object* v___y_439_){
_start:
{
uint8_t v___x_441_; 
v___x_441_ = l_Lean_Expr_hasMVar(v_e_438_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; 
v___x_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_442_, 0, v_e_438_);
return v___x_442_;
}
else
{
lean_object* v___x_443_; lean_object* v_mctx_444_; lean_object* v___x_445_; lean_object* v_fst_446_; lean_object* v_snd_447_; lean_object* v___x_448_; lean_object* v_cache_449_; lean_object* v_zetaDeltaFVarIds_450_; lean_object* v_postponed_451_; lean_object* v_diag_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_461_; 
v___x_443_ = lean_st_ref_get(v___y_439_);
v_mctx_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc_ref(v_mctx_444_);
lean_dec(v___x_443_);
v___x_445_ = l_Lean_instantiateMVarsCore(v_mctx_444_, v_e_438_);
v_fst_446_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_fst_446_);
v_snd_447_ = lean_ctor_get(v___x_445_, 1);
lean_inc(v_snd_447_);
lean_dec_ref(v___x_445_);
v___x_448_ = lean_st_ref_take(v___y_439_);
v_cache_449_ = lean_ctor_get(v___x_448_, 1);
v_zetaDeltaFVarIds_450_ = lean_ctor_get(v___x_448_, 2);
v_postponed_451_ = lean_ctor_get(v___x_448_, 3);
v_diag_452_ = lean_ctor_get(v___x_448_, 4);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_461_ == 0)
{
lean_object* v_unused_462_; 
v_unused_462_ = lean_ctor_get(v___x_448_, 0);
lean_dec(v_unused_462_);
v___x_454_ = v___x_448_;
v_isShared_455_ = v_isSharedCheck_461_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_diag_452_);
lean_inc(v_postponed_451_);
lean_inc(v_zetaDeltaFVarIds_450_);
lean_inc(v_cache_449_);
lean_dec(v___x_448_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_461_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_457_; 
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v_snd_447_);
v___x_457_ = v___x_454_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_snd_447_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v_cache_449_);
lean_ctor_set(v_reuseFailAlloc_460_, 2, v_zetaDeltaFVarIds_450_);
lean_ctor_set(v_reuseFailAlloc_460_, 3, v_postponed_451_);
lean_ctor_set(v_reuseFailAlloc_460_, 4, v_diag_452_);
v___x_457_ = v_reuseFailAlloc_460_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = lean_st_ref_put(v___y_439_, v___x_457_);
v___x_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_459_, 0, v_fst_446_);
return v___x_459_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg___boxed(lean_object* v_e_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(v_e_463_, v___y_464_);
lean_dec(v___y_464_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0(lean_object* v_e_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(v_e_467_, v___y_469_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___boxed(lean_object* v_e_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0(v_e_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
lean_dec(v___y_476_);
lean_dec_ref(v___y_475_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEq___lam__0(lean_object* v_mvarId_481_, lean_object* v___x_482_, lean_object* v_targetNew_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
lean_object* v___x_489_; 
lean_inc(v_mvarId_481_);
v___x_489_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_481_, v___x_482_, v___y_484_, v___y_485_, v___y_486_, v___y_487_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v___x_490_; 
lean_dec_ref_known(v___x_489_, 1);
lean_inc(v_mvarId_481_);
v___x_490_ = l_Lean_MVarId_getType(v_mvarId_481_, v___y_484_, v___y_485_, v___y_486_, v___y_487_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_561_; 
v_a_491_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_561_ == 0)
{
v___x_493_ = v___x_490_;
v_isShared_494_ = v_isSharedCheck_561_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_490_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_561_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
uint8_t v___x_495_; 
v___x_495_ = lean_expr_equal(v_a_491_, v_targetNew_483_);
if (v___x_495_ == 0)
{
lean_object* v___x_496_; lean_object* v_a_497_; lean_object* v___x_498_; lean_object* v_a_499_; uint8_t v___x_500_; 
lean_del_object(v___x_493_);
v___x_496_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(v_a_491_, v___y_485_);
v_a_497_ = lean_ctor_get(v___x_496_, 0);
lean_inc(v_a_497_);
lean_dec_ref(v___x_496_);
v___x_498_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(v_targetNew_483_, v___y_485_);
v_a_499_ = lean_ctor_get(v___x_498_, 0);
lean_inc(v_a_499_);
lean_dec_ref(v___x_498_);
v___x_500_ = lean_expr_equal(v_a_497_, v_a_499_);
if (v___x_500_ == 0)
{
lean_object* v___x_501_; 
lean_inc(v_mvarId_481_);
v___x_501_ = l_Lean_MVarId_getTag(v_mvarId_481_, v___y_484_, v___y_485_, v___y_486_, v___y_487_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_a_502_; lean_object* v___x_503_; 
v_a_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_a_502_);
lean_dec_ref_known(v___x_501_, 1);
v___x_503_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_499_, v_a_502_, v___y_484_, v___y_485_, v___y_486_, v___y_487_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_a_504_; lean_object* v___x_505_; 
v_a_504_ = lean_ctor_get(v___x_503_, 0);
lean_inc_n(v_a_504_, 2);
lean_dec_ref_known(v___x_503_, 1);
v___x_505_ = l_Lean_Meta_mkExpectedTypeHint(v_a_504_, v_a_497_, v___y_484_, v___y_485_, v___y_486_, v___y_487_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; lean_object* v___x_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_515_; 
v_a_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_a_506_);
lean_dec_ref_known(v___x_505_, 1);
v___x_507_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg(v_mvarId_481_, v_a_506_, v___y_485_);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_515_ == 0)
{
lean_object* v_unused_516_; 
v_unused_516_ = lean_ctor_get(v___x_507_, 0);
lean_dec(v_unused_516_);
v___x_509_ = v___x_507_;
v_isShared_510_ = v_isSharedCheck_515_;
goto v_resetjp_508_;
}
else
{
lean_dec(v___x_507_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_515_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_511_; lean_object* v___x_513_; 
v___x_511_ = l_Lean_Expr_mvarId_x21(v_a_504_);
lean_dec(v_a_504_);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 0, v___x_511_);
v___x_513_ = v___x_509_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_511_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
else
{
lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_524_; 
lean_dec(v_a_504_);
lean_dec(v_mvarId_481_);
v_a_517_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_524_ == 0)
{
v___x_519_ = v___x_505_;
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_dec(v___x_505_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_522_; 
if (v_isShared_520_ == 0)
{
v___x_522_ = v___x_519_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_a_517_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
else
{
lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_532_; 
lean_dec(v_a_497_);
lean_dec(v_mvarId_481_);
v_a_525_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_532_ == 0)
{
v___x_527_ = v___x_503_;
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_503_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_530_; 
if (v_isShared_528_ == 0)
{
v___x_530_ = v___x_527_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_a_525_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
else
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_540_; 
lean_dec(v_a_499_);
lean_dec(v_a_497_);
lean_dec(v_mvarId_481_);
v_a_533_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_540_ == 0)
{
v___x_535_ = v___x_501_;
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_501_);
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
lean_dec(v_a_499_);
lean_inc(v_mvarId_481_);
v___x_541_ = l_Lean_MVarId_setType___redArg(v_mvarId_481_, v_a_497_, v___y_485_);
if (lean_obj_tag(v___x_541_) == 0)
{
lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_548_ == 0)
{
lean_object* v_unused_549_; 
v_unused_549_ = lean_ctor_get(v___x_541_, 0);
lean_dec(v_unused_549_);
v___x_543_ = v___x_541_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_dec(v___x_541_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 0, v_mvarId_481_);
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_mvarId_481_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
else
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_557_; 
lean_dec(v_mvarId_481_);
v_a_550_ = lean_ctor_get(v___x_541_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_557_ == 0)
{
v___x_552_ = v___x_541_;
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_541_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_555_; 
if (v_isShared_553_ == 0)
{
v___x_555_ = v___x_552_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_a_550_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
}
else
{
lean_object* v___x_559_; 
lean_dec(v_a_491_);
lean_dec_ref(v_targetNew_483_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 0, v_mvarId_481_);
v___x_559_ = v___x_493_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_mvarId_481_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
else
{
lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_569_; 
lean_dec_ref(v_targetNew_483_);
lean_dec(v_mvarId_481_);
v_a_562_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_569_ == 0)
{
v___x_564_ = v___x_490_;
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v___x_490_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_567_; 
if (v_isShared_565_ == 0)
{
v___x_567_ = v___x_564_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_a_562_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
}
else
{
lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_577_; 
lean_dec_ref(v_targetNew_483_);
lean_dec(v_mvarId_481_);
v_a_570_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_577_ == 0)
{
v___x_572_ = v___x_489_;
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v___x_489_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
if (v_isShared_573_ == 0)
{
v___x_575_ = v___x_572_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_a_570_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEq___lam__0___boxed(lean_object* v_mvarId_578_, lean_object* v___x_579_, lean_object* v_targetNew_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Lean_MVarId_replaceTargetDefEq___lam__0(v_mvarId_578_, v___x_579_, v_targetNew_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_581_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object* v_mvarId_590_, lean_object* v_targetNew_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_){
_start:
{
lean_object* v___x_597_; lean_object* v___f_598_; lean_object* v___x_599_; 
v___x_597_ = ((lean_object*)(l_Lean_MVarId_replaceTargetDefEq___closed__1));
lean_inc(v_mvarId_590_);
v___f_598_ = lean_alloc_closure((void*)(l_Lean_MVarId_replaceTargetDefEq___lam__0___boxed), 8, 3);
lean_closure_set(v___f_598_, 0, v_mvarId_590_);
lean_closure_set(v___f_598_, 1, v___x_597_);
lean_closure_set(v___f_598_, 2, v_targetNew_591_);
v___x_599_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_590_, v___f_598_, v_a_592_, v_a_593_, v_a_594_, v_a_595_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEq___boxed(lean_object* v_mvarId_600_, lean_object* v_targetNew_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_600_, v_targetNew_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_);
lean_dec(v_a_605_);
lean_dec_ref(v_a_604_);
lean_dec(v_a_603_);
lean_dec_ref(v_a_602_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replace___lam__0(lean_object* v_mvarId_608_, lean_object* v_fvarId_609_, lean_object* v_val_610_, lean_object* v_userName_x3f_611_, lean_object* v_type_x3f_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
lean_object* v___y_619_; lean_object* v_a_620_; lean_object* v_a_651_; 
if (lean_obj_tag(v_type_x3f_612_) == 0)
{
lean_object* v___x_664_; 
lean_inc(v___y_616_);
lean_inc_ref(v___y_615_);
lean_inc(v___y_614_);
lean_inc_ref(v___y_613_);
lean_inc_ref(v_val_610_);
v___x_664_ = lean_infer_type(v_val_610_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_object* v_a_665_; 
v_a_665_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_a_665_);
lean_dec_ref_known(v___x_664_, 1);
v_a_651_ = v_a_665_;
goto v___jp_650_;
}
else
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_673_; 
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v_userName_x3f_611_);
lean_dec_ref(v_val_610_);
lean_dec(v_fvarId_609_);
lean_dec(v_mvarId_608_);
v_a_666_ = lean_ctor_get(v___x_664_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_673_ == 0)
{
v___x_668_ = v___x_664_;
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_664_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_671_; 
if (v_isShared_669_ == 0)
{
v___x_671_ = v___x_668_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_a_666_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
else
{
lean_object* v_val_674_; 
v_val_674_ = lean_ctor_get(v_type_x3f_612_, 0);
lean_inc(v_val_674_);
lean_dec_ref_known(v_type_x3f_612_, 1);
v_a_651_ = v_val_674_;
goto v___jp_650_;
}
v___jp_618_:
{
lean_object* v___x_621_; 
lean_inc(v_fvarId_609_);
v___x_621_ = l_Lean_MVarId_assertAfter_x27(v_mvarId_608_, v_fvarId_609_, v_a_620_, v___y_619_, v_val_610_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v_a_622_; lean_object* v_fvarId_623_; lean_object* v_mvarId_624_; lean_object* v_subst_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_649_; 
v_a_622_ = lean_ctor_get(v___x_621_, 0);
lean_inc(v_a_622_);
lean_dec_ref_known(v___x_621_, 1);
v_fvarId_623_ = lean_ctor_get(v_a_622_, 0);
v_mvarId_624_ = lean_ctor_get(v_a_622_, 1);
v_subst_625_ = lean_ctor_get(v_a_622_, 2);
v_isSharedCheck_649_ = !lean_is_exclusive(v_a_622_);
if (v_isSharedCheck_649_ == 0)
{
v___x_627_ = v_a_622_;
v_isShared_628_ = v_isSharedCheck_649_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_subst_625_);
lean_inc(v_mvarId_624_);
lean_inc(v_fvarId_623_);
lean_dec(v_a_622_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_649_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_629_; 
v___x_629_ = l_Lean_MVarId_tryClear(v_mvarId_624_, v_fvarId_609_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_640_; 
v_a_630_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_640_ == 0)
{
v___x_632_ = v___x_629_;
v_isShared_633_ = v_isSharedCheck_640_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_629_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_640_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_635_; 
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 1, v_a_630_);
v___x_635_ = v___x_627_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_fvarId_623_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v_a_630_);
lean_ctor_set(v_reuseFailAlloc_639_, 2, v_subst_625_);
v___x_635_ = v_reuseFailAlloc_639_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
lean_object* v___x_637_; 
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 0, v___x_635_);
v___x_637_ = v___x_632_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_635_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
else
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_648_; 
lean_del_object(v___x_627_);
lean_dec(v_subst_625_);
lean_dec(v_fvarId_623_);
v_a_641_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_648_ == 0)
{
v___x_643_ = v___x_629_;
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v___x_629_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_646_; 
if (v_isShared_644_ == 0)
{
v___x_646_ = v___x_643_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_a_641_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
}
}
else
{
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v_fvarId_609_);
return v___x_621_;
}
}
v___jp_650_:
{
if (lean_obj_tag(v_userName_x3f_611_) == 0)
{
lean_object* v___x_652_; 
lean_inc(v_fvarId_609_);
v___x_652_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_609_, v___y_613_, v___y_615_, v___y_616_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; lean_object* v___x_654_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_a_653_);
lean_dec_ref_known(v___x_652_, 1);
v___x_654_ = l_Lean_LocalDecl_userName(v_a_653_);
lean_dec(v_a_653_);
v___y_619_ = v_a_651_;
v_a_620_ = v___x_654_;
goto v___jp_618_;
}
else
{
lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_662_; 
lean_dec_ref(v_a_651_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec_ref(v_val_610_);
lean_dec(v_fvarId_609_);
lean_dec(v_mvarId_608_);
v_a_655_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_662_ == 0)
{
v___x_657_ = v___x_652_;
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_652_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_660_; 
if (v_isShared_658_ == 0)
{
v___x_660_ = v___x_657_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_a_655_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
}
else
{
lean_object* v_val_663_; 
v_val_663_ = lean_ctor_get(v_userName_x3f_611_, 0);
lean_inc(v_val_663_);
lean_dec_ref_known(v_userName_x3f_611_, 1);
v___y_619_ = v_a_651_;
v_a_620_ = v_val_663_;
goto v___jp_618_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replace___lam__0___boxed(lean_object* v_mvarId_675_, lean_object* v_fvarId_676_, lean_object* v_val_677_, lean_object* v_userName_x3f_678_, lean_object* v_type_x3f_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Lean_MVarId_replace___lam__0(v_mvarId_675_, v_fvarId_676_, v_val_677_, v_userName_x3f_678_, v_type_x3f_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replace(lean_object* v_mvarId_686_, lean_object* v_fvarId_687_, lean_object* v_val_688_, lean_object* v_type_x3f_689_, lean_object* v_userName_x3f_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_){
_start:
{
lean_object* v___f_696_; lean_object* v___x_697_; 
lean_inc(v_mvarId_686_);
v___f_696_ = lean_alloc_closure((void*)(l_Lean_MVarId_replace___lam__0___boxed), 10, 5);
lean_closure_set(v___f_696_, 0, v_mvarId_686_);
lean_closure_set(v___f_696_, 1, v_fvarId_687_);
lean_closure_set(v___f_696_, 2, v_val_688_);
lean_closure_set(v___f_696_, 3, v_userName_x3f_690_);
lean_closure_set(v___f_696_, 4, v_type_x3f_689_);
v___x_697_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_686_, v___f_696_, v_a_691_, v_a_692_, v_a_693_, v_a_694_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replace___boxed(lean_object* v_mvarId_698_, lean_object* v_fvarId_699_, lean_object* v_val_700_, lean_object* v_type_x3f_701_, lean_object* v_userName_x3f_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Lean_MVarId_replace(v_mvarId_698_, v_fvarId_699_, v_val_700_, v_type_x3f_701_, v_userName_x3f_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_);
lean_dec(v_a_706_);
lean_dec_ref(v_a_705_);
lean_dec(v_a_704_);
lean_dec_ref(v_a_703_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDecl___lam__0(lean_object* v_eqProof_709_, lean_object* v___x_710_, lean_object* v_typeNew_711_, lean_object* v_mvarId_712_, lean_object* v_fvarId_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = l_Lean_Meta_mkEqMP(v_eqProof_709_, v___x_710_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v_a_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v_a_720_ = lean_ctor_get(v___x_719_, 0);
lean_inc(v_a_720_);
lean_dec_ref_known(v___x_719_, 1);
v___x_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_721_, 0, v_typeNew_711_);
v___x_722_ = lean_box(0);
v___x_723_ = l_Lean_MVarId_replace(v_mvarId_712_, v_fvarId_713_, v_a_720_, v___x_721_, v___x_722_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
return v___x_723_;
}
else
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
lean_dec(v_fvarId_713_);
lean_dec(v_mvarId_712_);
lean_dec_ref(v_typeNew_711_);
v_a_724_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_731_ == 0)
{
v___x_726_ = v___x_719_;
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_719_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_729_; 
if (v_isShared_727_ == 0)
{
v___x_729_ = v___x_726_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_a_724_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDecl___lam__0___boxed(lean_object* v_eqProof_732_, lean_object* v___x_733_, lean_object* v_typeNew_734_, lean_object* v_mvarId_735_, lean_object* v_fvarId_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Lean_MVarId_replaceLocalDecl___lam__0(v_eqProof_732_, v___x_733_, v_typeNew_734_, v_mvarId_735_, v_fvarId_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
return v_res_742_;
}
}
static lean_object* _init_l_Lean_MVarId_replaceLocalDecl___closed__0(void){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = l_instMonadEIO___redArg();
return v___x_743_;
}
}
static lean_object* _init_l_Lean_MVarId_replaceLocalDecl___closed__1(void){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_744_ = lean_obj_once(&l_Lean_MVarId_replaceLocalDecl___closed__0, &l_Lean_MVarId_replaceLocalDecl___closed__0_once, _init_l_Lean_MVarId_replaceLocalDecl___closed__0);
v___x_745_ = l_StateRefT_x27_instMonad___redArg(v___x_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDecl(lean_object* v_mvarId_750_, lean_object* v_fvarId_751_, lean_object* v_typeNew_752_, lean_object* v_eqProof_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_){
_start:
{
lean_object* v___x_759_; lean_object* v_toApplicative_760_; lean_object* v_toFunctor_761_; lean_object* v_toSeq_762_; lean_object* v_toSeqLeft_763_; lean_object* v_toSeqRight_764_; lean_object* v___f_765_; lean_object* v___f_766_; lean_object* v___f_767_; lean_object* v___f_768_; lean_object* v___x_769_; lean_object* v___f_770_; lean_object* v___f_771_; lean_object* v___f_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v_toApplicative_778_; lean_object* v_toFunctor_779_; lean_object* v_toSeq_780_; lean_object* v_toSeqLeft_781_; lean_object* v_toSeqRight_782_; lean_object* v___f_783_; lean_object* v___f_784_; lean_object* v___x_785_; lean_object* v___f_786_; lean_object* v___f_787_; lean_object* v___f_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v_toApplicative_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_823_; 
v___x_759_ = lean_obj_once(&l_Lean_MVarId_replaceLocalDecl___closed__1, &l_Lean_MVarId_replaceLocalDecl___closed__1_once, _init_l_Lean_MVarId_replaceLocalDecl___closed__1);
v_toApplicative_760_ = lean_ctor_get(v___x_759_, 0);
v_toFunctor_761_ = lean_ctor_get(v_toApplicative_760_, 0);
v_toSeq_762_ = lean_ctor_get(v_toApplicative_760_, 2);
v_toSeqLeft_763_ = lean_ctor_get(v_toApplicative_760_, 3);
v_toSeqRight_764_ = lean_ctor_get(v_toApplicative_760_, 4);
v___f_765_ = ((lean_object*)(l_Lean_MVarId_replaceLocalDecl___closed__2));
v___f_766_ = ((lean_object*)(l_Lean_MVarId_replaceLocalDecl___closed__3));
lean_inc_ref_n(v_toFunctor_761_, 2);
v___f_767_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_767_, 0, v_toFunctor_761_);
v___f_768_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_768_, 0, v_toFunctor_761_);
v___x_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_769_, 0, v___f_767_);
lean_ctor_set(v___x_769_, 1, v___f_768_);
lean_inc(v_toSeqRight_764_);
v___f_770_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_770_, 0, v_toSeqRight_764_);
lean_inc(v_toSeqLeft_763_);
v___f_771_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_771_, 0, v_toSeqLeft_763_);
lean_inc(v_toSeq_762_);
v___f_772_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_772_, 0, v_toSeq_762_);
v___x_773_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_773_, 0, v___x_769_);
lean_ctor_set(v___x_773_, 1, v___f_765_);
lean_ctor_set(v___x_773_, 2, v___f_772_);
lean_ctor_set(v___x_773_, 3, v___f_771_);
lean_ctor_set(v___x_773_, 4, v___f_770_);
v___x_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
lean_ctor_set(v___x_774_, 1, v___f_766_);
v___x_775_ = l_StateRefT_x27_instMonad___redArg(v___x_774_);
v___x_776_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_776_, 0, lean_box(0));
lean_closure_set(v___x_776_, 1, lean_box(0));
lean_closure_set(v___x_776_, 2, v___x_775_);
v___x_777_ = l_instMonadControlTOfPure___redArg(v___x_776_);
v_toApplicative_778_ = lean_ctor_get(v___x_759_, 0);
v_toFunctor_779_ = lean_ctor_get(v_toApplicative_778_, 0);
v_toSeq_780_ = lean_ctor_get(v_toApplicative_778_, 2);
v_toSeqLeft_781_ = lean_ctor_get(v_toApplicative_778_, 3);
v_toSeqRight_782_ = lean_ctor_get(v_toApplicative_778_, 4);
lean_inc_ref_n(v_toFunctor_779_, 2);
v___f_783_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_783_, 0, v_toFunctor_779_);
v___f_784_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_784_, 0, v_toFunctor_779_);
v___x_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_785_, 0, v___f_783_);
lean_ctor_set(v___x_785_, 1, v___f_784_);
lean_inc(v_toSeqRight_782_);
v___f_786_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_786_, 0, v_toSeqRight_782_);
lean_inc(v_toSeqLeft_781_);
v___f_787_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_787_, 0, v_toSeqLeft_781_);
lean_inc(v_toSeq_780_);
v___f_788_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_788_, 0, v_toSeq_780_);
v___x_789_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_789_, 0, v___x_785_);
lean_ctor_set(v___x_789_, 1, v___f_765_);
lean_ctor_set(v___x_789_, 2, v___f_788_);
lean_ctor_set(v___x_789_, 3, v___f_787_);
lean_ctor_set(v___x_789_, 4, v___f_786_);
v___x_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
lean_ctor_set(v___x_790_, 1, v___f_766_);
v___x_791_ = l_StateRefT_x27_instMonad___redArg(v___x_790_);
v_toApplicative_792_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_823_ == 0)
{
lean_object* v_unused_824_; 
v_unused_824_ = lean_ctor_get(v___x_791_, 1);
lean_dec(v_unused_824_);
v___x_794_ = v___x_791_;
v_isShared_795_ = v_isSharedCheck_823_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_toApplicative_792_);
lean_dec(v___x_791_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_823_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v_toFunctor_796_; lean_object* v_toSeq_797_; lean_object* v_toSeqLeft_798_; lean_object* v_toSeqRight_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_821_; 
v_toFunctor_796_ = lean_ctor_get(v_toApplicative_792_, 0);
v_toSeq_797_ = lean_ctor_get(v_toApplicative_792_, 2);
v_toSeqLeft_798_ = lean_ctor_get(v_toApplicative_792_, 3);
v_toSeqRight_799_ = lean_ctor_get(v_toApplicative_792_, 4);
v_isSharedCheck_821_ = !lean_is_exclusive(v_toApplicative_792_);
if (v_isSharedCheck_821_ == 0)
{
lean_object* v_unused_822_; 
v_unused_822_ = lean_ctor_get(v_toApplicative_792_, 1);
lean_dec(v_unused_822_);
v___x_801_ = v_toApplicative_792_;
v_isShared_802_ = v_isSharedCheck_821_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_toSeqRight_799_);
lean_inc(v_toSeqLeft_798_);
lean_inc(v_toSeq_797_);
lean_inc(v_toFunctor_796_);
lean_dec(v_toApplicative_792_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_821_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___f_803_; lean_object* v___f_804_; lean_object* v___f_805_; lean_object* v___f_806_; lean_object* v___x_807_; lean_object* v___f_808_; lean_object* v___f_809_; lean_object* v___f_810_; lean_object* v___x_812_; 
v___f_803_ = ((lean_object*)(l_Lean_MVarId_replaceLocalDecl___closed__4));
v___f_804_ = ((lean_object*)(l_Lean_MVarId_replaceLocalDecl___closed__5));
lean_inc_ref(v_toFunctor_796_);
v___f_805_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_805_, 0, v_toFunctor_796_);
v___f_806_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_806_, 0, v_toFunctor_796_);
v___x_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_807_, 0, v___f_805_);
lean_ctor_set(v___x_807_, 1, v___f_806_);
v___f_808_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_808_, 0, v_toSeqRight_799_);
v___f_809_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_809_, 0, v_toSeqLeft_798_);
v___f_810_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_810_, 0, v_toSeq_797_);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 4, v___f_808_);
lean_ctor_set(v___x_801_, 3, v___f_809_);
lean_ctor_set(v___x_801_, 2, v___f_810_);
lean_ctor_set(v___x_801_, 1, v___f_803_);
lean_ctor_set(v___x_801_, 0, v___x_807_);
v___x_812_ = v___x_801_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_807_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v___f_803_);
lean_ctor_set(v_reuseFailAlloc_820_, 2, v___f_810_);
lean_ctor_set(v_reuseFailAlloc_820_, 3, v___f_809_);
lean_ctor_set(v_reuseFailAlloc_820_, 4, v___f_808_);
v___x_812_ = v_reuseFailAlloc_820_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
lean_object* v___x_814_; 
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 1, v___f_804_);
lean_ctor_set(v___x_794_, 0, v___x_812_);
v___x_814_ = v___x_794_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_812_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v___f_804_);
v___x_814_ = v_reuseFailAlloc_819_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
lean_object* v___x_815_; lean_object* v___f_816_; lean_object* v___x_124__overap_817_; lean_object* v___x_818_; 
lean_inc(v_fvarId_751_);
v___x_815_ = l_Lean_mkFVar(v_fvarId_751_);
lean_inc(v_mvarId_750_);
v___f_816_ = lean_alloc_closure((void*)(l_Lean_MVarId_replaceLocalDecl___lam__0___boxed), 10, 5);
lean_closure_set(v___f_816_, 0, v_eqProof_753_);
lean_closure_set(v___f_816_, 1, v___x_815_);
lean_closure_set(v___f_816_, 2, v_typeNew_752_);
lean_closure_set(v___f_816_, 3, v_mvarId_750_);
lean_closure_set(v___f_816_, 4, v_fvarId_751_);
v___x_124__overap_817_ = l_Lean_MVarId_withContext___redArg(v___x_777_, v___x_814_, v_mvarId_750_, v___f_816_);
lean_inc(v_a_757_);
lean_inc_ref(v_a_756_);
lean_inc(v_a_755_);
lean_inc_ref(v_a_754_);
v___x_818_ = lean_apply_5(v___x_124__overap_817_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, lean_box(0));
return v___x_818_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDecl___boxed(lean_object* v_mvarId_825_, lean_object* v_fvarId_826_, lean_object* v_typeNew_827_, lean_object* v_eqProof_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_Lean_MVarId_replaceLocalDecl(v_mvarId_825_, v_fvarId_826_, v_typeNew_827_, v_eqProof_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_);
lean_dec(v_a_832_);
lean_dec_ref(v_a_831_);
lean_dec(v_a_830_);
lean_dec_ref(v_a_829_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___redArg(lean_object* v_decls_835_, lean_object* v_x_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l_Lean_Meta_withLocalInstancesImp___redArg(v_decls_835_, v_x_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_850_; 
v_a_843_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_850_ == 0)
{
v___x_845_ = v___x_842_;
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_842_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_848_; 
if (v_isShared_846_ == 0)
{
v___x_848_ = v___x_845_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_a_843_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
else
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_858_; 
v_a_851_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_858_ == 0)
{
v___x_853_ = v___x_842_;
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_842_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
v___x_856_ = v___x_853_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_a_851_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___redArg___boxed(lean_object* v_decls_859_, lean_object* v_x_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___redArg(v_decls_859_, v_x_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec(v_decls_859_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0(lean_object* v_00_u03b1_867_, lean_object* v_decls_868_, lean_object* v_x_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___redArg(v_decls_868_, v_x_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___boxed(lean_object* v_00_u03b1_876_, lean_object* v_decls_877_, lean_object* v_x_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0(v_00_u03b1_876_, v_decls_877_, v_x_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v_decls_877_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___redArg(lean_object* v_lctx_885_, lean_object* v_x_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v_keyedConfig_892_; uint8_t v_trackZetaDelta_893_; lean_object* v_zetaDeltaSet_894_; lean_object* v_localInstances_895_; lean_object* v_defEqCtx_x3f_896_; lean_object* v_synthPendingDepth_897_; lean_object* v_customCanUnfoldPredicate_x3f_898_; uint8_t v_univApprox_899_; uint8_t v_inTypeClassResolution_900_; uint8_t v_cacheInferType_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v_keyedConfig_892_ = lean_ctor_get(v___y_887_, 0);
v_trackZetaDelta_893_ = lean_ctor_get_uint8(v___y_887_, sizeof(void*)*7);
v_zetaDeltaSet_894_ = lean_ctor_get(v___y_887_, 1);
v_localInstances_895_ = lean_ctor_get(v___y_887_, 3);
v_defEqCtx_x3f_896_ = lean_ctor_get(v___y_887_, 4);
v_synthPendingDepth_897_ = lean_ctor_get(v___y_887_, 5);
v_customCanUnfoldPredicate_x3f_898_ = lean_ctor_get(v___y_887_, 6);
v_univApprox_899_ = lean_ctor_get_uint8(v___y_887_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_900_ = lean_ctor_get_uint8(v___y_887_, sizeof(void*)*7 + 2);
v_cacheInferType_901_ = lean_ctor_get_uint8(v___y_887_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_898_);
lean_inc(v_synthPendingDepth_897_);
lean_inc(v_defEqCtx_x3f_896_);
lean_inc_ref(v_localInstances_895_);
lean_inc(v_zetaDeltaSet_894_);
lean_inc_ref(v_keyedConfig_892_);
v___x_902_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_902_, 0, v_keyedConfig_892_);
lean_ctor_set(v___x_902_, 1, v_zetaDeltaSet_894_);
lean_ctor_set(v___x_902_, 2, v_lctx_885_);
lean_ctor_set(v___x_902_, 3, v_localInstances_895_);
lean_ctor_set(v___x_902_, 4, v_defEqCtx_x3f_896_);
lean_ctor_set(v___x_902_, 5, v_synthPendingDepth_897_);
lean_ctor_set(v___x_902_, 6, v_customCanUnfoldPredicate_x3f_898_);
lean_ctor_set_uint8(v___x_902_, sizeof(void*)*7, v_trackZetaDelta_893_);
lean_ctor_set_uint8(v___x_902_, sizeof(void*)*7 + 1, v_univApprox_899_);
lean_ctor_set_uint8(v___x_902_, sizeof(void*)*7 + 2, v_inTypeClassResolution_900_);
lean_ctor_set_uint8(v___x_902_, sizeof(void*)*7 + 3, v_cacheInferType_901_);
lean_inc(v___y_890_);
lean_inc_ref(v___y_889_);
lean_inc(v___y_888_);
v___x_903_ = lean_apply_5(v_x_886_, v___x_902_, v___y_888_, v___y_889_, v___y_890_, lean_box(0));
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___redArg___boxed(lean_object* v_lctx_904_, lean_object* v_x_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___redArg(v_lctx_904_, v_x_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1(lean_object* v_00_u03b1_912_, lean_object* v_lctx_913_, lean_object* v_x_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v___x_920_; 
v___x_920_ = l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___redArg(v_lctx_913_, v_x_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___boxed(lean_object* v_00_u03b1_921_, lean_object* v_lctx_922_, lean_object* v_x_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1(v_00_u03b1_921_, v_lctx_922_, v_x_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2___redArg(lean_object* v_mvarId_930_, lean_object* v_fvarId_931_, lean_object* v_type_932_, lean_object* v___y_933_){
_start:
{
lean_object* v___x_935_; lean_object* v_mctx_936_; lean_object* v_cache_937_; lean_object* v_zetaDeltaFVarIds_938_; lean_object* v_postponed_939_; lean_object* v_diag_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_951_; 
v___x_935_ = lean_st_ref_take(v___y_933_);
v_mctx_936_ = lean_ctor_get(v___x_935_, 0);
v_cache_937_ = lean_ctor_get(v___x_935_, 1);
v_zetaDeltaFVarIds_938_ = lean_ctor_get(v___x_935_, 2);
v_postponed_939_ = lean_ctor_get(v___x_935_, 3);
v_diag_940_ = lean_ctor_get(v___x_935_, 4);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_951_ == 0)
{
v___x_942_ = v___x_935_;
v_isShared_943_ = v_isSharedCheck_951_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_diag_940_);
lean_inc(v_postponed_939_);
lean_inc(v_zetaDeltaFVarIds_938_);
lean_inc(v_cache_937_);
lean_inc(v_mctx_936_);
lean_dec(v___x_935_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_951_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_947_; 
v___x_944_ = lean_box(0);
v___x_945_ = l_Lean_MetavarContext_setFVarType(v_mctx_936_, v_mvarId_930_, v_fvarId_931_, v_type_932_);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 0, v___x_945_);
v___x_947_ = v___x_942_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_945_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v_cache_937_);
lean_ctor_set(v_reuseFailAlloc_950_, 2, v_zetaDeltaFVarIds_938_);
lean_ctor_set(v_reuseFailAlloc_950_, 3, v_postponed_939_);
lean_ctor_set(v_reuseFailAlloc_950_, 4, v_diag_940_);
v___x_947_ = v_reuseFailAlloc_950_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_948_ = lean_st_ref_put(v___y_933_, v___x_947_);
v___x_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_949_, 0, v___x_944_);
return v___x_949_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2___redArg___boxed(lean_object* v_mvarId_952_, lean_object* v_fvarId_953_, lean_object* v_type_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2___redArg(v_mvarId_952_, v_fvarId_953_, v_type_954_, v___y_955_);
lean_dec(v___y_955_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2(lean_object* v_mvarId_958_, lean_object* v_fvarId_959_, lean_object* v_type_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v___x_966_; 
v___x_966_ = l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2___redArg(v_mvarId_958_, v_fvarId_959_, v_type_960_, v___y_962_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2___boxed(lean_object* v_mvarId_967_, lean_object* v_fvarId_968_, lean_object* v_type_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2(v_mvarId_967_, v_fvarId_968_, v_type_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq___lam__0(lean_object* v_mvarId_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
lean_object* v___x_982_; 
lean_inc(v_mvarId_976_);
v___x_982_ = l_Lean_MVarId_getDecl(v_mvarId_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_a_983_; lean_object* v_userName_984_; lean_object* v_type_985_; uint8_t v_kind_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v_a_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_a_983_);
lean_dec_ref_known(v___x_982_, 1);
v_userName_984_ = lean_ctor_get(v_a_983_, 0);
lean_inc(v_userName_984_);
v_type_985_ = lean_ctor_get(v_a_983_, 2);
lean_inc_ref(v_type_985_);
v_kind_986_ = lean_ctor_get_uint8(v_a_983_, sizeof(void*)*7);
lean_dec(v_a_983_);
v___x_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_987_, 0, v_type_985_);
v___x_988_ = l_Lean_Meta_mkFreshExprMVar(v___x_987_, v_kind_986_, v_userName_984_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v_a_989_; lean_object* v___x_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_998_; 
v_a_989_ = lean_ctor_get(v___x_988_, 0);
lean_inc_n(v_a_989_, 2);
lean_dec_ref_known(v___x_988_, 1);
v___x_990_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg(v_mvarId_976_, v_a_989_, v___y_978_);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_998_ == 0)
{
lean_object* v_unused_999_; 
v_unused_999_ = lean_ctor_get(v___x_990_, 0);
lean_dec(v_unused_999_);
v___x_992_ = v___x_990_;
v_isShared_993_ = v_isSharedCheck_998_;
goto v_resetjp_991_;
}
else
{
lean_dec(v___x_990_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_998_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_994_; lean_object* v___x_996_; 
v___x_994_ = l_Lean_Expr_mvarId_x21(v_a_989_);
lean_dec(v_a_989_);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 0, v___x_994_);
v___x_996_ = v___x_992_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_994_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
else
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
lean_dec(v_mvarId_976_);
v_a_1000_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1002_ = v___x_988_;
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_988_);
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
lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1015_; 
lean_dec(v_mvarId_976_);
v_a_1008_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1010_ = v___x_982_;
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_dec(v___x_982_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq___lam__0___boxed(lean_object* v_mvarId_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_Lean_MVarId_replaceLocalDeclDefEq___lam__0(v_mvarId_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq___lam__1(lean_object* v_fvarId_1023_, lean_object* v_typeNew_1024_, lean_object* v___f_1025_, lean_object* v_mvarId_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v___x_1032_; 
lean_inc(v_fvarId_1023_);
v___x_1032_ = l_Lean_FVarId_getType___redArg(v_fvarId_1023_, v___y_1027_, v___y_1029_, v___y_1030_);
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1062_; 
v_a_1033_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1035_ = v___x_1032_;
v_isShared_1036_ = v_isSharedCheck_1062_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v___x_1032_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1062_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
uint8_t v___x_1037_; 
v___x_1037_ = lean_expr_equal(v_a_1033_, v_typeNew_1024_);
if (v___x_1037_ == 0)
{
lean_object* v___x_1038_; lean_object* v_a_1039_; lean_object* v___x_1040_; lean_object* v_a_1041_; uint8_t v___x_1042_; 
lean_del_object(v___x_1035_);
v___x_1038_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(v_a_1033_, v___y_1028_);
v_a_1039_ = lean_ctor_get(v___x_1038_, 0);
lean_inc(v_a_1039_);
lean_dec_ref(v___x_1038_);
v___x_1040_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(v_typeNew_1024_, v___y_1028_);
v_a_1041_ = lean_ctor_get(v___x_1040_, 0);
lean_inc(v_a_1041_);
lean_dec_ref(v___x_1040_);
v___x_1042_ = lean_expr_equal(v_a_1039_, v_a_1041_);
if (v___x_1042_ == 0)
{
lean_object* v_lctx_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
lean_dec(v_a_1039_);
lean_dec(v_mvarId_1026_);
v_lctx_1043_ = lean_ctor_get(v___y_1027_, 2);
lean_inc(v_fvarId_1023_);
lean_inc_ref(v_lctx_1043_);
v___x_1044_ = l_Lean_LocalContext_setType(v_lctx_1043_, v_fvarId_1023_, v_a_1041_);
lean_inc_ref(v___x_1044_);
v___x_1045_ = l_Lean_LocalContext_get_x21(v___x_1044_, v_fvarId_1023_);
v___x_1046_ = lean_box(0);
v___x_1047_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1045_);
lean_ctor_set(v___x_1047_, 1, v___x_1046_);
v___x_1048_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___boxed), 8, 3);
lean_closure_set(v___x_1048_, 0, lean_box(0));
lean_closure_set(v___x_1048_, 1, v___x_1047_);
lean_closure_set(v___x_1048_, 2, v___f_1025_);
v___x_1049_ = l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___redArg(v___x_1044_, v___x_1048_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
lean_dec_ref(v___y_1027_);
return v___x_1049_;
}
else
{
lean_object* v___x_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1057_; 
lean_dec(v_a_1041_);
lean_dec_ref(v___y_1027_);
lean_dec_ref(v___f_1025_);
lean_inc(v_mvarId_1026_);
v___x_1050_ = l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2___redArg(v_mvarId_1026_, v_fvarId_1023_, v_a_1039_, v___y_1028_);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1057_ == 0)
{
lean_object* v_unused_1058_; 
v_unused_1058_ = lean_ctor_get(v___x_1050_, 0);
lean_dec(v_unused_1058_);
v___x_1052_ = v___x_1050_;
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
else
{
lean_dec(v___x_1050_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 0, v_mvarId_1026_);
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_mvarId_1026_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
else
{
lean_object* v___x_1060_; 
lean_dec(v_a_1033_);
lean_dec_ref(v___y_1027_);
lean_dec_ref(v___f_1025_);
lean_dec_ref(v_typeNew_1024_);
lean_dec(v_fvarId_1023_);
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 0, v_mvarId_1026_);
v___x_1060_ = v___x_1035_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_mvarId_1026_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
else
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1070_; 
lean_dec_ref(v___y_1027_);
lean_dec(v_mvarId_1026_);
lean_dec_ref(v___f_1025_);
lean_dec_ref(v_typeNew_1024_);
lean_dec(v_fvarId_1023_);
v_a_1063_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1065_ = v___x_1032_;
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1032_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1068_; 
if (v_isShared_1066_ == 0)
{
v___x_1068_ = v___x_1065_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_a_1063_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq___lam__1___boxed(lean_object* v_fvarId_1071_, lean_object* v_typeNew_1072_, lean_object* v___f_1073_, lean_object* v_mvarId_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_Lean_MVarId_replaceLocalDeclDefEq___lam__1(v_fvarId_1071_, v_typeNew_1072_, v___f_1073_, v_mvarId_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq(lean_object* v_mvarId_1081_, lean_object* v_fvarId_1082_, lean_object* v_typeNew_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_){
_start:
{
lean_object* v___f_1089_; lean_object* v___f_1090_; lean_object* v___x_1091_; 
lean_inc_n(v_mvarId_1081_, 2);
v___f_1089_ = lean_alloc_closure((void*)(l_Lean_MVarId_replaceLocalDeclDefEq___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1089_, 0, v_mvarId_1081_);
v___f_1090_ = lean_alloc_closure((void*)(l_Lean_MVarId_replaceLocalDeclDefEq___lam__1___boxed), 9, 4);
lean_closure_set(v___f_1090_, 0, v_fvarId_1082_);
lean_closure_set(v___f_1090_, 1, v_typeNew_1083_);
lean_closure_set(v___f_1090_, 2, v___f_1089_);
lean_closure_set(v___f_1090_, 3, v_mvarId_1081_);
v___x_1091_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_1081_, v___f_1090_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq___boxed(lean_object* v_mvarId_1092_, lean_object* v_fvarId_1093_, lean_object* v_typeNew_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_mvarId_1092_, v_fvarId_1093_, v_typeNew_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_);
lean_dec(v_a_1098_);
lean_dec_ref(v_a_1097_);
lean_dec(v_a_1096_);
lean_dec_ref(v_a_1095_);
return v_res_1100_;
}
}
static lean_object* _init_l_Lean_MVarId_change___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1102_ = ((lean_object*)(l_Lean_MVarId_change___lam__0___closed__0));
v___x_1103_ = l_Lean_stringToMessageData(v___x_1102_);
return v___x_1103_;
}
}
static lean_object* _init_l_Lean_MVarId_change___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = ((lean_object*)(l_Lean_MVarId_change___lam__0___closed__2));
v___x_1106_ = l_Lean_stringToMessageData(v___x_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_change___lam__0(lean_object* v_mvarId_1107_, uint8_t v_checkDefEq_1108_, lean_object* v_targetNew_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v___x_1115_; 
lean_inc(v_mvarId_1107_);
v___x_1115_ = l_Lean_MVarId_getType(v_mvarId_1107_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
if (lean_obj_tag(v___x_1115_) == 0)
{
if (v_checkDefEq_1108_ == 0)
{
lean_object* v___x_1116_; 
lean_dec_ref_known(v___x_1115_, 1);
v___x_1116_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_1107_, v_targetNew_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
return v___x_1116_;
}
else
{
lean_object* v_a_1117_; lean_object* v___x_1118_; 
v_a_1117_ = lean_ctor_get(v___x_1115_, 0);
lean_inc_n(v_a_1117_, 2);
lean_dec_ref_known(v___x_1115_, 1);
lean_inc_ref(v_targetNew_1109_);
v___x_1118_ = l_Lean_Meta_isExprDefEq(v_a_1117_, v_targetNew_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1119_; uint8_t v___x_1120_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
lean_inc(v_a_1119_);
lean_dec_ref_known(v___x_1118_, 1);
v___x_1120_ = lean_unbox(v_a_1119_);
lean_dec(v_a_1119_);
if (v___x_1120_ == 0)
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1121_ = ((lean_object*)(l_Lean_MVarId_replaceTargetDefEq___closed__1));
v___x_1122_ = lean_obj_once(&l_Lean_MVarId_change___lam__0___closed__1, &l_Lean_MVarId_change___lam__0___closed__1_once, _init_l_Lean_MVarId_change___lam__0___closed__1);
lean_inc_ref(v_targetNew_1109_);
v___x_1123_ = l_Lean_indentExpr(v_targetNew_1109_);
v___x_1124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1122_);
lean_ctor_set(v___x_1124_, 1, v___x_1123_);
v___x_1125_ = lean_obj_once(&l_Lean_MVarId_change___lam__0___closed__3, &l_Lean_MVarId_change___lam__0___closed__3_once, _init_l_Lean_MVarId_change___lam__0___closed__3);
v___x_1126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1124_);
lean_ctor_set(v___x_1126_, 1, v___x_1125_);
v___x_1127_ = l_Lean_indentExpr(v_a_1117_);
v___x_1128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1126_);
lean_ctor_set(v___x_1128_, 1, v___x_1127_);
v___x_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1128_);
lean_inc(v_mvarId_1107_);
v___x_1130_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1121_, v_mvarId_1107_, v___x_1129_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v___x_1131_; 
lean_dec_ref_known(v___x_1130_, 1);
v___x_1131_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_1107_, v_targetNew_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
return v___x_1131_;
}
else
{
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1139_; 
lean_dec_ref(v_targetNew_1109_);
lean_dec(v_mvarId_1107_);
v_a_1132_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1134_ = v___x_1130_;
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1130_);
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
lean_object* v___x_1140_; 
lean_dec(v_a_1117_);
v___x_1140_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_1107_, v_targetNew_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
return v___x_1140_;
}
}
else
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
lean_dec(v_a_1117_);
lean_dec_ref(v_targetNew_1109_);
lean_dec(v_mvarId_1107_);
v_a_1141_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1143_ = v___x_1118_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_1118_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_a_1141_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
}
else
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1156_; 
lean_dec_ref(v_targetNew_1109_);
lean_dec(v_mvarId_1107_);
v_a_1149_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1151_ = v___x_1115_;
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_1115_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1154_; 
if (v_isShared_1152_ == 0)
{
v___x_1154_ = v___x_1151_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_a_1149_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_change___lam__0___boxed(lean_object* v_mvarId_1157_, lean_object* v_checkDefEq_1158_, lean_object* v_targetNew_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
uint8_t v_checkDefEq_boxed_1165_; lean_object* v_res_1166_; 
v_checkDefEq_boxed_1165_ = lean_unbox(v_checkDefEq_1158_);
v_res_1166_ = l_Lean_MVarId_change___lam__0(v_mvarId_1157_, v_checkDefEq_boxed_1165_, v_targetNew_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_change(lean_object* v_mvarId_1167_, lean_object* v_targetNew_1168_, uint8_t v_checkDefEq_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_){
_start:
{
lean_object* v___x_1175_; lean_object* v___f_1176_; lean_object* v___x_1177_; 
v___x_1175_ = lean_box(v_checkDefEq_1169_);
lean_inc(v_mvarId_1167_);
v___f_1176_ = lean_alloc_closure((void*)(l_Lean_MVarId_change___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1176_, 0, v_mvarId_1167_);
lean_closure_set(v___f_1176_, 1, v___x_1175_);
lean_closure_set(v___f_1176_, 2, v_targetNew_1168_);
v___x_1177_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_1167_, v___f_1176_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_change___boxed(lean_object* v_mvarId_1178_, lean_object* v_targetNew_1179_, lean_object* v_checkDefEq_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_){
_start:
{
uint8_t v_checkDefEq_boxed_1186_; lean_object* v_res_1187_; 
v_checkDefEq_boxed_1186_ = lean_unbox(v_checkDefEq_1180_);
v_res_1187_ = l_Lean_MVarId_change(v_mvarId_1178_, v_targetNew_1179_, v_checkDefEq_boxed_1186_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_);
lean_dec(v_a_1184_);
lean_dec_ref(v_a_1183_);
lean_dec(v_a_1182_);
lean_dec_ref(v_a_1181_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0___redArg(lean_object* v_t_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v___x_1191_; lean_object* v_infoState_1192_; uint8_t v_enabled_1193_; 
v___x_1191_ = lean_st_ref_get(v___y_1189_);
v_infoState_1192_ = lean_ctor_get(v___x_1191_, 8);
lean_inc_ref(v_infoState_1192_);
lean_dec(v___x_1191_);
v_enabled_1193_ = lean_ctor_get_uint8(v_infoState_1192_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1192_);
if (v_enabled_1193_ == 0)
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
lean_dec_ref(v_t_1188_);
v___x_1194_ = lean_box(0);
v___x_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1194_);
return v___x_1195_;
}
else
{
lean_object* v___x_1196_; lean_object* v_infoState_1197_; lean_object* v_env_1198_; lean_object* v_nextMacroScope_1199_; lean_object* v_ngen_1200_; lean_object* v_auxDeclNGen_1201_; lean_object* v_traceState_1202_; lean_object* v_cache_1203_; lean_object* v_recordedDeps_1204_; lean_object* v_messages_1205_; lean_object* v_snapshotTasks_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1228_; 
v___x_1196_ = lean_st_ref_take(v___y_1189_);
v_infoState_1197_ = lean_ctor_get(v___x_1196_, 8);
v_env_1198_ = lean_ctor_get(v___x_1196_, 0);
v_nextMacroScope_1199_ = lean_ctor_get(v___x_1196_, 1);
v_ngen_1200_ = lean_ctor_get(v___x_1196_, 2);
v_auxDeclNGen_1201_ = lean_ctor_get(v___x_1196_, 3);
v_traceState_1202_ = lean_ctor_get(v___x_1196_, 4);
v_cache_1203_ = lean_ctor_get(v___x_1196_, 5);
v_recordedDeps_1204_ = lean_ctor_get(v___x_1196_, 6);
v_messages_1205_ = lean_ctor_get(v___x_1196_, 7);
v_snapshotTasks_1206_ = lean_ctor_get(v___x_1196_, 9);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1208_ = v___x_1196_;
v_isShared_1209_ = v_isSharedCheck_1228_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_snapshotTasks_1206_);
lean_inc(v_infoState_1197_);
lean_inc(v_messages_1205_);
lean_inc(v_recordedDeps_1204_);
lean_inc(v_cache_1203_);
lean_inc(v_traceState_1202_);
lean_inc(v_auxDeclNGen_1201_);
lean_inc(v_ngen_1200_);
lean_inc(v_nextMacroScope_1199_);
lean_inc(v_env_1198_);
lean_dec(v___x_1196_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1228_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
uint8_t v_enabled_1210_; lean_object* v_assignment_1211_; lean_object* v_lazyAssignment_1212_; lean_object* v_trees_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1227_; 
v_enabled_1210_ = lean_ctor_get_uint8(v_infoState_1197_, sizeof(void*)*3);
v_assignment_1211_ = lean_ctor_get(v_infoState_1197_, 0);
v_lazyAssignment_1212_ = lean_ctor_get(v_infoState_1197_, 1);
v_trees_1213_ = lean_ctor_get(v_infoState_1197_, 2);
v_isSharedCheck_1227_ = !lean_is_exclusive(v_infoState_1197_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1215_ = v_infoState_1197_;
v_isShared_1216_ = v_isSharedCheck_1227_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_trees_1213_);
lean_inc(v_lazyAssignment_1212_);
lean_inc(v_assignment_1211_);
lean_dec(v_infoState_1197_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1227_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1220_; 
v___x_1217_ = lean_box(0);
v___x_1218_ = l_Lean_PersistentArray_push___redArg(v_trees_1213_, v_t_1188_);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 2, v___x_1218_);
v___x_1220_ = v___x_1215_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_assignment_1211_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v_lazyAssignment_1212_);
lean_ctor_set(v_reuseFailAlloc_1226_, 2, v___x_1218_);
lean_ctor_set_uint8(v_reuseFailAlloc_1226_, sizeof(void*)*3, v_enabled_1210_);
v___x_1220_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
lean_object* v___x_1222_; 
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 8, v___x_1220_);
v___x_1222_ = v___x_1208_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_env_1198_);
lean_ctor_set(v_reuseFailAlloc_1225_, 1, v_nextMacroScope_1199_);
lean_ctor_set(v_reuseFailAlloc_1225_, 2, v_ngen_1200_);
lean_ctor_set(v_reuseFailAlloc_1225_, 3, v_auxDeclNGen_1201_);
lean_ctor_set(v_reuseFailAlloc_1225_, 4, v_traceState_1202_);
lean_ctor_set(v_reuseFailAlloc_1225_, 5, v_cache_1203_);
lean_ctor_set(v_reuseFailAlloc_1225_, 6, v_recordedDeps_1204_);
lean_ctor_set(v_reuseFailAlloc_1225_, 7, v_messages_1205_);
lean_ctor_set(v_reuseFailAlloc_1225_, 8, v___x_1220_);
lean_ctor_set(v_reuseFailAlloc_1225_, 9, v_snapshotTasks_1206_);
v___x_1222_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = lean_st_ref_put(v___y_1189_, v___x_1222_);
v___x_1224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1217_);
return v___x_1224_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0___redArg___boxed(lean_object* v_t_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0___redArg(v_t_1229_, v___y_1230_);
lean_dec(v___y_1230_);
return v_res_1232_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1233_ = lean_unsigned_to_nat(32u);
v___x_1234_ = lean_mk_empty_array_with_capacity(v___x_1233_);
v___x_1235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1234_);
return v___x_1235_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__1(void){
_start:
{
size_t v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1236_ = ((size_t)5ULL);
v___x_1237_ = lean_unsigned_to_nat(0u);
v___x_1238_ = lean_unsigned_to_nat(32u);
v___x_1239_ = lean_mk_empty_array_with_capacity(v___x_1238_);
v___x_1240_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__0);
v___x_1241_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
lean_ctor_set(v___x_1241_, 1, v___x_1239_);
lean_ctor_set(v___x_1241_, 2, v___x_1237_);
lean_ctor_set(v___x_1241_, 3, v___x_1237_);
lean_ctor_set_usize(v___x_1241_, 4, v___x_1236_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0(lean_object* v_t_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
lean_object* v___x_1248_; lean_object* v_infoState_1249_; uint8_t v_enabled_1250_; 
v___x_1248_ = lean_st_ref_get(v___y_1246_);
v_infoState_1249_ = lean_ctor_get(v___x_1248_, 8);
lean_inc_ref(v_infoState_1249_);
lean_dec(v___x_1248_);
v_enabled_1250_ = lean_ctor_get_uint8(v_infoState_1249_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1249_);
if (v_enabled_1250_ == 0)
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
lean_dec_ref(v_t_1242_);
v___x_1251_ = lean_box(0);
v___x_1252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1251_);
return v___x_1252_;
}
else
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1253_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__1);
v___x_1254_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1254_, 0, v_t_1242_);
lean_ctor_set(v___x_1254_, 1, v___x_1253_);
v___x_1255_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0___redArg(v___x_1254_, v___y_1246_);
return v___x_1255_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___boxed(lean_object* v_t_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0(v_t_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_withReverted_spec__1(lean_object* v_as_1263_, size_t v_sz_1264_, size_t v_i_1265_, lean_object* v_b_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v_a_1273_; uint8_t v___x_1277_; 
v___x_1277_ = lean_usize_dec_lt(v_i_1265_, v_sz_1264_);
if (v___x_1277_ == 0)
{
lean_object* v___x_1278_; 
v___x_1278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1278_, 0, v_b_1266_);
return v___x_1278_;
}
else
{
lean_object* v_array_1279_; lean_object* v_start_1280_; lean_object* v_stop_1281_; uint8_t v___x_1282_; 
v_array_1279_ = lean_ctor_get(v_b_1266_, 0);
v_start_1280_ = lean_ctor_get(v_b_1266_, 1);
v_stop_1281_ = lean_ctor_get(v_b_1266_, 2);
v___x_1282_ = lean_nat_dec_lt(v_start_1280_, v_stop_1281_);
if (v___x_1282_ == 0)
{
lean_object* v___x_1283_; 
v___x_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1283_, 0, v_b_1266_);
return v___x_1283_;
}
else
{
lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1322_; 
lean_inc(v_stop_1281_);
lean_inc(v_start_1280_);
lean_inc_ref(v_array_1279_);
v_isSharedCheck_1322_ = !lean_is_exclusive(v_b_1266_);
if (v_isSharedCheck_1322_ == 0)
{
lean_object* v_unused_1323_; lean_object* v_unused_1324_; lean_object* v_unused_1325_; 
v_unused_1323_ = lean_ctor_get(v_b_1266_, 2);
lean_dec(v_unused_1323_);
v_unused_1324_ = lean_ctor_get(v_b_1266_, 1);
lean_dec(v_unused_1324_);
v_unused_1325_ = lean_ctor_get(v_b_1266_, 0);
lean_dec(v_unused_1325_);
v___x_1285_ = v_b_1266_;
v_isShared_1286_ = v_isSharedCheck_1322_;
goto v_resetjp_1284_;
}
else
{
lean_dec(v_b_1266_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1322_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v_a_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1292_; 
v_a_1287_ = lean_array_uget(v_as_1263_, v_i_1265_);
v___x_1288_ = lean_array_fget(v_array_1279_, v_start_1280_);
v___x_1289_ = lean_unsigned_to_nat(1u);
v___x_1290_ = lean_nat_add(v_start_1280_, v___x_1289_);
lean_dec(v_start_1280_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 1, v___x_1290_);
v___x_1292_ = v___x_1285_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_array_1279_);
lean_ctor_set(v_reuseFailAlloc_1321_, 1, v___x_1290_);
lean_ctor_set(v_reuseFailAlloc_1321_, 2, v_stop_1281_);
v___x_1292_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
if (lean_obj_tag(v_a_1287_) == 1)
{
lean_object* v_val_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1320_; 
v_val_1293_ = lean_ctor_get(v_a_1287_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v_a_1287_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1295_ = v_a_1287_;
v_isShared_1296_ = v_isSharedCheck_1320_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_val_1293_);
lean_dec(v_a_1287_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1320_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1297_; 
lean_inc(v___x_1288_);
v___x_1297_ = l_Lean_FVarId_getUserName___redArg(v___x_1288_, v___y_1267_, v___y_1269_, v___y_1270_);
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v_a_1298_; lean_object* v___x_1299_; lean_object* v___x_1301_; 
v_a_1298_ = lean_ctor_get(v___x_1297_, 0);
lean_inc(v_a_1298_);
lean_dec_ref_known(v___x_1297_, 1);
v___x_1299_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1299_, 0, v_a_1298_);
lean_ctor_set(v___x_1299_, 1, v___x_1288_);
lean_ctor_set(v___x_1299_, 2, v_val_1293_);
if (v_isShared_1296_ == 0)
{
lean_ctor_set_tag(v___x_1295_, 11);
lean_ctor_set(v___x_1295_, 0, v___x_1299_);
v___x_1301_ = v___x_1295_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v___x_1299_);
v___x_1301_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
lean_object* v___x_1302_; 
v___x_1302_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0(v___x_1301_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_dec_ref_known(v___x_1302_, 1);
v_a_1273_ = v___x_1292_;
goto v___jp_1272_;
}
else
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1310_; 
lean_dec_ref(v___x_1292_);
v_a_1303_ = lean_ctor_get(v___x_1302_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1305_ = v___x_1302_;
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___x_1302_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1308_; 
if (v_isShared_1306_ == 0)
{
v___x_1308_ = v___x_1305_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_a_1303_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
}
}
else
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1319_; 
lean_del_object(v___x_1295_);
lean_dec(v_val_1293_);
lean_dec_ref(v___x_1292_);
lean_dec(v___x_1288_);
v_a_1312_ = lean_ctor_get(v___x_1297_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1314_ = v___x_1297_;
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1297_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1317_; 
if (v_isShared_1315_ == 0)
{
v___x_1317_ = v___x_1314_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_a_1312_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
}
}
else
{
lean_dec(v___x_1288_);
lean_dec(v_a_1287_);
v_a_1273_ = v___x_1292_;
goto v___jp_1272_;
}
}
}
}
}
v___jp_1272_:
{
size_t v___x_1274_; size_t v___x_1275_; 
v___x_1274_ = ((size_t)1ULL);
v___x_1275_ = lean_usize_add(v_i_1265_, v___x_1274_);
v_i_1265_ = v___x_1275_;
v_b_1266_ = v_a_1273_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_withReverted_spec__1___boxed(lean_object* v_as_1326_, lean_object* v_sz_1327_, lean_object* v_i_1328_, lean_object* v_b_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
size_t v_sz_boxed_1335_; size_t v_i_boxed_1336_; lean_object* v_res_1337_; 
v_sz_boxed_1335_ = lean_unbox_usize(v_sz_1327_);
lean_dec(v_sz_1327_);
v_i_boxed_1336_ = lean_unbox_usize(v_i_1328_);
lean_dec(v_i_1328_);
v_res_1337_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_withReverted_spec__1(v_as_1326_, v_sz_boxed_1335_, v_i_boxed_1336_, v_b_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec_ref(v_as_1326_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withReverted___redArg___lam__0(lean_object* v_fst_1338_, size_t v_sz_1339_, size_t v___x_1340_, lean_object* v___x_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v___x_1347_; 
v___x_1347_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_withReverted_spec__1(v_fst_1338_, v_sz_1339_, v___x_1340_, v___x_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1355_; 
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1355_ == 0)
{
lean_object* v_unused_1356_; 
v_unused_1356_ = lean_ctor_get(v___x_1347_, 0);
lean_dec(v_unused_1356_);
v___x_1349_ = v___x_1347_;
v_isShared_1350_ = v_isSharedCheck_1355_;
goto v_resetjp_1348_;
}
else
{
lean_dec(v___x_1347_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1355_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1351_; lean_object* v___x_1353_; 
v___x_1351_ = lean_box(0);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 0, v___x_1351_);
v___x_1353_ = v___x_1349_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1351_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
}
else
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1364_; 
v_a_1357_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1359_ = v___x_1347_;
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1347_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_a_1357_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withReverted___redArg___lam__0___boxed(lean_object* v_fst_1365_, lean_object* v_sz_1366_, lean_object* v___x_1367_, lean_object* v___x_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
size_t v_sz_boxed_1374_; size_t v___x_3383__boxed_1375_; lean_object* v_res_1376_; 
v_sz_boxed_1374_ = lean_unbox_usize(v_sz_1366_);
lean_dec(v_sz_1366_);
v___x_3383__boxed_1375_ = lean_unbox_usize(v___x_1367_);
lean_dec(v___x_1367_);
v_res_1376_ = l_Lean_MVarId_withReverted___redArg___lam__0(v_fst_1365_, v_sz_boxed_1374_, v___x_3383__boxed_1375_, v___x_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
lean_dec(v___y_1372_);
lean_dec_ref(v___y_1371_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
lean_dec_ref(v_fst_1365_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withReverted___redArg(lean_object* v_mvarId_1379_, lean_object* v_fvarIds_1380_, lean_object* v_k_1381_, uint8_t v_clearAuxDeclsInsteadOfRevert_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_){
_start:
{
uint8_t v___x_1388_; lean_object* v___x_1389_; 
v___x_1388_ = 1;
v___x_1389_ = l_Lean_MVarId_revert(v_mvarId_1379_, v_fvarIds_1380_, v___x_1388_, v_clearAuxDeclsInsteadOfRevert_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_);
if (lean_obj_tag(v___x_1389_) == 0)
{
lean_object* v_a_1390_; lean_object* v_fst_1391_; lean_object* v_snd_1392_; lean_object* v___x_1393_; 
v_a_1390_ = lean_ctor_get(v___x_1389_, 0);
lean_inc(v_a_1390_);
lean_dec_ref_known(v___x_1389_, 1);
v_fst_1391_ = lean_ctor_get(v_a_1390_, 0);
lean_inc(v_fst_1391_);
v_snd_1392_ = lean_ctor_get(v_a_1390_, 1);
lean_inc(v_snd_1392_);
lean_dec(v_a_1390_);
lean_inc(v_a_1386_);
lean_inc_ref(v_a_1385_);
lean_inc(v_a_1384_);
lean_inc_ref(v_a_1383_);
v___x_1393_ = lean_apply_7(v_k_1381_, v_snd_1392_, v_fst_1391_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_, lean_box(0));
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v_a_1394_; lean_object* v_snd_1395_; lean_object* v_fst_1396_; lean_object* v_fst_1397_; lean_object* v_snd_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; uint8_t v___x_1401_; lean_object* v___x_1402_; 
v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_a_1394_);
lean_dec_ref_known(v___x_1393_, 1);
v_snd_1395_ = lean_ctor_get(v_a_1394_, 1);
lean_inc(v_snd_1395_);
v_fst_1396_ = lean_ctor_get(v_a_1394_, 0);
lean_inc(v_fst_1396_);
lean_dec(v_a_1394_);
v_fst_1397_ = lean_ctor_get(v_snd_1395_, 0);
lean_inc(v_fst_1397_);
v_snd_1398_ = lean_ctor_get(v_snd_1395_, 1);
lean_inc(v_snd_1398_);
lean_dec(v_snd_1395_);
v___x_1399_ = lean_array_get_size(v_fst_1397_);
v___x_1400_ = lean_box(0);
v___x_1401_ = 0;
v___x_1402_ = l_Lean_Meta_introNCore(v_snd_1398_, v___x_1399_, v___x_1400_, v___x_1401_, v___x_1388_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v_a_1403_; lean_object* v_fst_1404_; lean_object* v_snd_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1436_; 
v_a_1403_ = lean_ctor_get(v___x_1402_, 0);
lean_inc(v_a_1403_);
lean_dec_ref_known(v___x_1402_, 1);
v_fst_1404_ = lean_ctor_get(v_a_1403_, 0);
v_snd_1405_ = lean_ctor_get(v_a_1403_, 1);
v_isSharedCheck_1436_ = !lean_is_exclusive(v_a_1403_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1407_ = v_a_1403_;
v_isShared_1408_ = v_isSharedCheck_1436_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_snd_1405_);
lean_inc(v_fst_1404_);
lean_dec(v_a_1403_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1436_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; size_t v_sz_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___f_1415_; lean_object* v___x_1416_; 
v___x_1409_ = lean_unsigned_to_nat(0u);
v___x_1410_ = lean_array_get_size(v_fst_1404_);
v___x_1411_ = l_Array_toSubarray___redArg(v_fst_1404_, v___x_1409_, v___x_1410_);
v_sz_1412_ = lean_array_size(v_fst_1397_);
v___x_1413_ = lean_box_usize(v_sz_1412_);
v___x_1414_ = ((lean_object*)(l_Lean_MVarId_withReverted___redArg___boxed__const__1));
v___f_1415_ = lean_alloc_closure((void*)(l_Lean_MVarId_withReverted___redArg___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1415_, 0, v_fst_1397_);
lean_closure_set(v___f_1415_, 1, v___x_1413_);
lean_closure_set(v___f_1415_, 2, v___x_1414_);
lean_closure_set(v___f_1415_, 3, v___x_1411_);
lean_inc(v_snd_1405_);
v___x_1416_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_snd_1405_, v___f_1415_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1426_; 
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1426_ == 0)
{
lean_object* v_unused_1427_; 
v_unused_1427_ = lean_ctor_get(v___x_1416_, 0);
lean_dec(v_unused_1427_);
v___x_1418_ = v___x_1416_;
v_isShared_1419_ = v_isSharedCheck_1426_;
goto v_resetjp_1417_;
}
else
{
lean_dec(v___x_1416_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1426_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1421_; 
if (v_isShared_1408_ == 0)
{
lean_ctor_set(v___x_1407_, 0, v_fst_1396_);
v___x_1421_ = v___x_1407_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_fst_1396_);
lean_ctor_set(v_reuseFailAlloc_1425_, 1, v_snd_1405_);
v___x_1421_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
lean_object* v___x_1423_; 
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 0, v___x_1421_);
v___x_1423_ = v___x_1418_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1421_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
}
else
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1435_; 
lean_del_object(v___x_1407_);
lean_dec(v_snd_1405_);
lean_dec(v_fst_1396_);
v_a_1428_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1430_ = v___x_1416_;
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1416_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1433_; 
if (v_isShared_1431_ == 0)
{
v___x_1433_ = v___x_1430_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_a_1428_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
}
}
else
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1444_; 
lean_dec(v_fst_1397_);
lean_dec(v_fst_1396_);
v_a_1437_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1439_ = v___x_1402_;
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1402_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1442_; 
if (v_isShared_1440_ == 0)
{
v___x_1442_ = v___x_1439_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_a_1437_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
}
else
{
lean_object* v_a_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1452_; 
v_a_1445_ = lean_ctor_get(v___x_1393_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1447_ = v___x_1393_;
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_a_1445_);
lean_dec(v___x_1393_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1450_; 
if (v_isShared_1448_ == 0)
{
v___x_1450_ = v___x_1447_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_a_1445_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
}
else
{
lean_object* v_a_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1460_; 
lean_dec_ref(v_k_1381_);
v_a_1453_ = lean_ctor_get(v___x_1389_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1455_ = v___x_1389_;
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_a_1453_);
lean_dec(v___x_1389_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1458_; 
if (v_isShared_1456_ == 0)
{
v___x_1458_ = v___x_1455_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_a_1453_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withReverted___redArg___boxed(lean_object* v_mvarId_1461_, lean_object* v_fvarIds_1462_, lean_object* v_k_1463_, lean_object* v_clearAuxDeclsInsteadOfRevert_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_){
_start:
{
uint8_t v_clearAuxDeclsInsteadOfRevert_boxed_1470_; lean_object* v_res_1471_; 
v_clearAuxDeclsInsteadOfRevert_boxed_1470_ = lean_unbox(v_clearAuxDeclsInsteadOfRevert_1464_);
v_res_1471_ = l_Lean_MVarId_withReverted___redArg(v_mvarId_1461_, v_fvarIds_1462_, v_k_1463_, v_clearAuxDeclsInsteadOfRevert_boxed_1470_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
lean_dec(v_a_1468_);
lean_dec_ref(v_a_1467_);
lean_dec(v_a_1466_);
lean_dec_ref(v_a_1465_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withReverted(lean_object* v_00_u03b1_1472_, lean_object* v_mvarId_1473_, lean_object* v_fvarIds_1474_, lean_object* v_k_1475_, uint8_t v_clearAuxDeclsInsteadOfRevert_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_){
_start:
{
lean_object* v___x_1482_; 
v___x_1482_ = l_Lean_MVarId_withReverted___redArg(v_mvarId_1473_, v_fvarIds_1474_, v_k_1475_, v_clearAuxDeclsInsteadOfRevert_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withReverted___boxed(lean_object* v_00_u03b1_1483_, lean_object* v_mvarId_1484_, lean_object* v_fvarIds_1485_, lean_object* v_k_1486_, lean_object* v_clearAuxDeclsInsteadOfRevert_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_){
_start:
{
uint8_t v_clearAuxDeclsInsteadOfRevert_boxed_1493_; lean_object* v_res_1494_; 
v_clearAuxDeclsInsteadOfRevert_boxed_1493_ = lean_unbox(v_clearAuxDeclsInsteadOfRevert_1487_);
v_res_1494_ = l_Lean_MVarId_withReverted(v_00_u03b1_1483_, v_mvarId_1484_, v_fvarIds_1485_, v_k_1486_, v_clearAuxDeclsInsteadOfRevert_boxed_1493_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_);
lean_dec(v_a_1491_);
lean_dec_ref(v_a_1490_);
lean_dec(v_a_1489_);
lean_dec_ref(v_a_1488_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0(lean_object* v_t_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v___x_1501_; 
v___x_1501_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0___redArg(v_t_1495_, v___y_1499_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0___boxed(lean_object* v_t_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0(v_t_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
lean_dec(v___y_1504_);
lean_dec_ref(v___y_1503_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withRevertedFrom___redArg(lean_object* v_mvarId_1509_, lean_object* v_fvarId_1510_, lean_object* v_k_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_){
_start:
{
lean_object* v___x_1517_; 
v___x_1517_ = l_Lean_MVarId_revertFrom(v_mvarId_1509_, v_fvarId_1510_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; lean_object* v_fst_1519_; lean_object* v_snd_1520_; lean_object* v___x_1521_; 
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_a_1518_);
lean_dec_ref_known(v___x_1517_, 1);
v_fst_1519_ = lean_ctor_get(v_a_1518_, 0);
lean_inc(v_fst_1519_);
v_snd_1520_ = lean_ctor_get(v_a_1518_, 1);
lean_inc(v_snd_1520_);
lean_dec(v_a_1518_);
lean_inc(v_a_1515_);
lean_inc_ref(v_a_1514_);
lean_inc(v_a_1513_);
lean_inc_ref(v_a_1512_);
v___x_1521_ = lean_apply_7(v_k_1511_, v_snd_1520_, v_fst_1519_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, lean_box(0));
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v_a_1522_; lean_object* v_snd_1523_; lean_object* v_fst_1524_; lean_object* v_fst_1525_; lean_object* v_snd_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; uint8_t v___x_1529_; uint8_t v___x_1530_; lean_object* v___x_1531_; 
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_a_1522_);
lean_dec_ref_known(v___x_1521_, 1);
v_snd_1523_ = lean_ctor_get(v_a_1522_, 1);
lean_inc(v_snd_1523_);
v_fst_1524_ = lean_ctor_get(v_a_1522_, 0);
lean_inc(v_fst_1524_);
lean_dec(v_a_1522_);
v_fst_1525_ = lean_ctor_get(v_snd_1523_, 0);
lean_inc(v_fst_1525_);
v_snd_1526_ = lean_ctor_get(v_snd_1523_, 1);
lean_inc(v_snd_1526_);
lean_dec(v_snd_1523_);
v___x_1527_ = lean_array_get_size(v_fst_1525_);
v___x_1528_ = lean_box(0);
v___x_1529_ = 0;
v___x_1530_ = 1;
v___x_1531_ = l_Lean_Meta_introNCore(v_snd_1526_, v___x_1527_, v___x_1528_, v___x_1529_, v___x_1530_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v_a_1532_; lean_object* v_fst_1533_; lean_object* v_snd_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1565_; 
v_a_1532_ = lean_ctor_get(v___x_1531_, 0);
lean_inc(v_a_1532_);
lean_dec_ref_known(v___x_1531_, 1);
v_fst_1533_ = lean_ctor_get(v_a_1532_, 0);
v_snd_1534_ = lean_ctor_get(v_a_1532_, 1);
v_isSharedCheck_1565_ = !lean_is_exclusive(v_a_1532_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1536_ = v_a_1532_;
v_isShared_1537_ = v_isSharedCheck_1565_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_snd_1534_);
lean_inc(v_fst_1533_);
lean_dec(v_a_1532_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1565_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; size_t v_sz_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___f_1544_; lean_object* v___x_1545_; 
v___x_1538_ = lean_unsigned_to_nat(0u);
v___x_1539_ = lean_array_get_size(v_fst_1533_);
v___x_1540_ = l_Array_toSubarray___redArg(v_fst_1533_, v___x_1538_, v___x_1539_);
v_sz_1541_ = lean_array_size(v_fst_1525_);
v___x_1542_ = lean_box_usize(v_sz_1541_);
v___x_1543_ = ((lean_object*)(l_Lean_MVarId_withReverted___redArg___boxed__const__1));
v___f_1544_ = lean_alloc_closure((void*)(l_Lean_MVarId_withReverted___redArg___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1544_, 0, v_fst_1525_);
lean_closure_set(v___f_1544_, 1, v___x_1542_);
lean_closure_set(v___f_1544_, 2, v___x_1543_);
lean_closure_set(v___f_1544_, 3, v___x_1540_);
lean_inc(v_snd_1534_);
v___x_1545_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_snd_1534_, v___f_1544_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1555_; 
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1555_ == 0)
{
lean_object* v_unused_1556_; 
v_unused_1556_ = lean_ctor_get(v___x_1545_, 0);
lean_dec(v_unused_1556_);
v___x_1547_ = v___x_1545_;
v_isShared_1548_ = v_isSharedCheck_1555_;
goto v_resetjp_1546_;
}
else
{
lean_dec(v___x_1545_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1555_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1550_; 
if (v_isShared_1537_ == 0)
{
lean_ctor_set(v___x_1536_, 0, v_fst_1524_);
v___x_1550_ = v___x_1536_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_fst_1524_);
lean_ctor_set(v_reuseFailAlloc_1554_, 1, v_snd_1534_);
v___x_1550_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
lean_object* v___x_1552_; 
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 0, v___x_1550_);
v___x_1552_ = v___x_1547_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1550_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
else
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
lean_del_object(v___x_1536_);
lean_dec(v_snd_1534_);
lean_dec(v_fst_1524_);
v_a_1557_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1559_ = v___x_1545_;
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1545_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1557_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
}
}
else
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1573_; 
lean_dec(v_fst_1525_);
lean_dec(v_fst_1524_);
v_a_1566_ = lean_ctor_get(v___x_1531_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1568_ = v___x_1531_;
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1531_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1571_; 
if (v_isShared_1569_ == 0)
{
v___x_1571_ = v___x_1568_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_a_1566_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
}
else
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1581_; 
v_a_1574_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1576_ = v___x_1521_;
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1521_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1579_; 
if (v_isShared_1577_ == 0)
{
v___x_1579_ = v___x_1576_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_a_1574_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
}
else
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
lean_dec_ref(v_k_1511_);
v_a_1582_ = lean_ctor_get(v___x_1517_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v___x_1517_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1517_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1582_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withRevertedFrom___redArg___boxed(lean_object* v_mvarId_1590_, lean_object* v_fvarId_1591_, lean_object* v_k_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l_Lean_MVarId_withRevertedFrom___redArg(v_mvarId_1590_, v_fvarId_1591_, v_k_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_);
lean_dec(v_a_1596_);
lean_dec_ref(v_a_1595_);
lean_dec(v_a_1594_);
lean_dec_ref(v_a_1593_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withRevertedFrom(lean_object* v_00_u03b1_1599_, lean_object* v_mvarId_1600_, lean_object* v_fvarId_1601_, lean_object* v_k_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_){
_start:
{
lean_object* v___x_1608_; 
v___x_1608_ = l_Lean_MVarId_withRevertedFrom___redArg(v_mvarId_1600_, v_fvarId_1601_, v_k_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withRevertedFrom___boxed(lean_object* v_00_u03b1_1609_, lean_object* v_mvarId_1610_, lean_object* v_fvarId_1611_, lean_object* v_k_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l_Lean_MVarId_withRevertedFrom(v_00_u03b1_1609_, v_mvarId_1610_, v_fvarId_1611_, v_k_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_);
lean_dec(v_a_1616_);
lean_dec_ref(v_a_1615_);
lean_dec(v_a_1614_);
lean_dec_ref(v_a_1613_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lam__0(uint8_t v_checkDefEq_1619_, lean_object* v_typeNew_1620_, lean_object* v___x_1621_, lean_object* v_mvarId_1622_, lean_object* v_typeOld_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
if (v_checkDefEq_1619_ == 0)
{
lean_object* v___x_1629_; lean_object* v___x_1630_; 
lean_dec_ref(v_typeOld_1623_);
lean_dec(v_mvarId_1622_);
lean_dec(v___x_1621_);
lean_dec_ref(v_typeNew_1620_);
v___x_1629_ = lean_box(0);
v___x_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1629_);
return v___x_1630_;
}
else
{
lean_object* v___x_1631_; 
lean_inc_ref(v_typeOld_1623_);
lean_inc_ref(v_typeNew_1620_);
v___x_1631_ = l_Lean_Meta_isExprDefEq(v_typeNew_1620_, v_typeOld_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1650_; 
v_a_1632_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1634_ = v___x_1631_;
v_isShared_1635_ = v_isSharedCheck_1650_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1631_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1650_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
uint8_t v___x_1636_; 
v___x_1636_ = lean_unbox(v_a_1632_);
lean_dec(v_a_1632_);
if (v___x_1636_ == 0)
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
lean_del_object(v___x_1634_);
v___x_1637_ = lean_obj_once(&l_Lean_MVarId_change___lam__0___closed__1, &l_Lean_MVarId_change___lam__0___closed__1_once, _init_l_Lean_MVarId_change___lam__0___closed__1);
v___x_1638_ = l_Lean_indentExpr(v_typeNew_1620_);
v___x_1639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1637_);
lean_ctor_set(v___x_1639_, 1, v___x_1638_);
v___x_1640_ = lean_obj_once(&l_Lean_MVarId_change___lam__0___closed__3, &l_Lean_MVarId_change___lam__0___closed__3_once, _init_l_Lean_MVarId_change___lam__0___closed__3);
v___x_1641_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1639_);
lean_ctor_set(v___x_1641_, 1, v___x_1640_);
v___x_1642_ = l_Lean_indentExpr(v_typeOld_1623_);
v___x_1643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1641_);
lean_ctor_set(v___x_1643_, 1, v___x_1642_);
v___x_1644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1643_);
v___x_1645_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1621_, v_mvarId_1622_, v___x_1644_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
return v___x_1645_;
}
else
{
lean_object* v___x_1646_; lean_object* v___x_1648_; 
lean_dec_ref(v_typeOld_1623_);
lean_dec(v_mvarId_1622_);
lean_dec(v___x_1621_);
lean_dec_ref(v_typeNew_1620_);
v___x_1646_ = lean_box(0);
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 0, v___x_1646_);
v___x_1648_ = v___x_1634_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v___x_1646_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
}
else
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1658_; 
lean_dec_ref(v_typeOld_1623_);
lean_dec(v_mvarId_1622_);
lean_dec(v___x_1621_);
lean_dec_ref(v_typeNew_1620_);
v_a_1651_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1653_ = v___x_1631_;
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___x_1631_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1656_; 
if (v_isShared_1654_ == 0)
{
v___x_1656_ = v___x_1653_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_a_1651_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lam__0___boxed(lean_object* v_checkDefEq_1659_, lean_object* v_typeNew_1660_, lean_object* v___x_1661_, lean_object* v_mvarId_1662_, lean_object* v_typeOld_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_){
_start:
{
uint8_t v_checkDefEq_boxed_1669_; lean_object* v_res_1670_; 
v_checkDefEq_boxed_1669_ = lean_unbox(v_checkDefEq_1659_);
v_res_1670_ = l_Lean_MVarId_changeLocalDecl___lam__0(v_checkDefEq_boxed_1669_, v_typeNew_1660_, v___x_1661_, v_mvarId_1662_, v_typeOld_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1664_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_changeLocalDecl_spec__0(size_t v_sz_1671_, size_t v_i_1672_, lean_object* v_bs_1673_){
_start:
{
uint8_t v___x_1674_; 
v___x_1674_ = lean_usize_dec_lt(v_i_1672_, v_sz_1671_);
if (v___x_1674_ == 0)
{
return v_bs_1673_;
}
else
{
lean_object* v_v_1675_; lean_object* v___x_1676_; lean_object* v_bs_x27_1677_; lean_object* v___x_1678_; size_t v___x_1679_; size_t v___x_1680_; lean_object* v___x_1681_; 
v_v_1675_ = lean_array_uget(v_bs_1673_, v_i_1672_);
v___x_1676_ = lean_unsigned_to_nat(0u);
v_bs_x27_1677_ = lean_array_uset(v_bs_1673_, v_i_1672_, v___x_1676_);
v___x_1678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1678_, 0, v_v_1675_);
v___x_1679_ = ((size_t)1ULL);
v___x_1680_ = lean_usize_add(v_i_1672_, v___x_1679_);
v___x_1681_ = lean_array_uset(v_bs_x27_1677_, v_i_1672_, v___x_1678_);
v_i_1672_ = v___x_1680_;
v_bs_1673_ = v___x_1681_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_changeLocalDecl_spec__0___boxed(lean_object* v_sz_1683_, lean_object* v_i_1684_, lean_object* v_bs_1685_){
_start:
{
size_t v_sz_boxed_1686_; size_t v_i_boxed_1687_; lean_object* v_res_1688_; 
v_sz_boxed_1686_ = lean_unbox_usize(v_sz_1683_);
lean_dec(v_sz_1683_);
v_i_boxed_1687_ = lean_unbox_usize(v_i_1684_);
lean_dec(v_i_1684_);
v_res_1688_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_changeLocalDecl_spec__0(v_sz_boxed_1686_, v_i_boxed_1687_, v_bs_1685_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lam__1(lean_object* v_mvarId_1689_, lean_object* v_fvars_1690_, lean_object* v_targetNew_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
lean_object* v___x_1697_; 
v___x_1697_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_1689_, v_targetNew_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_);
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1711_; 
v_a_1698_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1700_ = v___x_1697_;
v_isShared_1701_ = v_isSharedCheck_1711_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1697_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1711_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1702_; size_t v_sz_1703_; size_t v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1709_; 
v___x_1702_ = lean_box(0);
v_sz_1703_ = lean_array_size(v_fvars_1690_);
v___x_1704_ = ((size_t)0ULL);
v___x_1705_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_changeLocalDecl_spec__0(v_sz_1703_, v___x_1704_, v_fvars_1690_);
v___x_1706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1706_, 0, v___x_1705_);
lean_ctor_set(v___x_1706_, 1, v_a_1698_);
v___x_1707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1702_);
lean_ctor_set(v___x_1707_, 1, v___x_1706_);
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 0, v___x_1707_);
v___x_1709_ = v___x_1700_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v___x_1707_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
else
{
lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1719_; 
lean_dec_ref(v_fvars_1690_);
v_a_1712_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1714_ = v___x_1697_;
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___x_1697_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1717_; 
if (v_isShared_1715_ == 0)
{
v___x_1717_ = v___x_1714_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_a_1712_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lam__1___boxed(lean_object* v_mvarId_1720_, lean_object* v_fvars_1721_, lean_object* v_targetNew_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
lean_object* v_res_1728_; 
v_res_1728_ = l_Lean_MVarId_changeLocalDecl___lam__1(v_mvarId_1720_, v_fvars_1721_, v_targetNew_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
return v_res_1728_;
}
}
static lean_object* _init_l_Lean_MVarId_changeLocalDecl___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1732_ = ((lean_object*)(l_Lean_MVarId_changeLocalDecl___lam__2___closed__1));
v___x_1733_ = l_Lean_MessageData_ofFormat(v___x_1732_);
return v___x_1733_;
}
}
static lean_object* _init_l_Lean_MVarId_changeLocalDecl___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1734_ = lean_obj_once(&l_Lean_MVarId_changeLocalDecl___lam__2___closed__2, &l_Lean_MVarId_changeLocalDecl___lam__2___closed__2_once, _init_l_Lean_MVarId_changeLocalDecl___lam__2___closed__2);
v___x_1735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1735_, 0, v___x_1734_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lam__2(lean_object* v_mvarId_1736_, lean_object* v___f_1737_, lean_object* v_typeNew_1738_, lean_object* v___f_1739_, lean_object* v___x_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
lean_object* v___x_1746_; 
lean_inc(v_mvarId_1736_);
v___x_1746_ = l_Lean_MVarId_getType(v_mvarId_1736_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v_a_1747_; 
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc(v_a_1747_);
lean_dec_ref_known(v___x_1746_, 1);
switch(lean_obj_tag(v_a_1747_))
{
case 7:
{
lean_object* v_binderName_1748_; lean_object* v_binderType_1749_; lean_object* v_body_1750_; uint8_t v_binderInfo_1751_; lean_object* v___x_1752_; 
lean_dec(v___x_1740_);
lean_dec(v_mvarId_1736_);
v_binderName_1748_ = lean_ctor_get(v_a_1747_, 0);
lean_inc(v_binderName_1748_);
v_binderType_1749_ = lean_ctor_get(v_a_1747_, 1);
lean_inc_ref(v_binderType_1749_);
v_body_1750_ = lean_ctor_get(v_a_1747_, 2);
lean_inc_ref(v_body_1750_);
v_binderInfo_1751_ = lean_ctor_get_uint8(v_a_1747_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_1747_, 3);
lean_inc(v___y_1744_);
lean_inc_ref(v___y_1743_);
lean_inc(v___y_1742_);
lean_inc_ref(v___y_1741_);
v___x_1752_ = lean_apply_6(v___f_1737_, v_binderType_1749_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, lean_box(0));
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v___x_1753_; lean_object* v___x_1754_; 
lean_dec_ref_known(v___x_1752_, 1);
v___x_1753_ = l_Lean_Expr_forallE___override(v_binderName_1748_, v_typeNew_1738_, v_body_1750_, v_binderInfo_1751_);
v___x_1754_ = lean_apply_6(v___f_1739_, v___x_1753_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, lean_box(0));
return v___x_1754_;
}
else
{
lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1762_; 
lean_dec_ref(v_body_1750_);
lean_dec(v_binderName_1748_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec_ref(v___f_1739_);
lean_dec_ref(v_typeNew_1738_);
v_a_1755_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1757_ = v___x_1752_;
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___x_1752_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1760_; 
if (v_isShared_1758_ == 0)
{
v___x_1760_ = v___x_1757_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_a_1755_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
}
}
case 8:
{
lean_object* v_declName_1763_; lean_object* v_type_1764_; lean_object* v_value_1765_; lean_object* v_body_1766_; uint8_t v_nondep_1767_; lean_object* v___x_1768_; 
lean_dec(v___x_1740_);
lean_dec(v_mvarId_1736_);
v_declName_1763_ = lean_ctor_get(v_a_1747_, 0);
lean_inc(v_declName_1763_);
v_type_1764_ = lean_ctor_get(v_a_1747_, 1);
lean_inc_ref(v_type_1764_);
v_value_1765_ = lean_ctor_get(v_a_1747_, 2);
lean_inc_ref(v_value_1765_);
v_body_1766_ = lean_ctor_get(v_a_1747_, 3);
lean_inc_ref(v_body_1766_);
v_nondep_1767_ = lean_ctor_get_uint8(v_a_1747_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_a_1747_, 4);
lean_inc(v___y_1744_);
lean_inc_ref(v___y_1743_);
lean_inc(v___y_1742_);
lean_inc_ref(v___y_1741_);
v___x_1768_ = lean_apply_6(v___f_1737_, v_type_1764_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, lean_box(0));
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
lean_dec_ref_known(v___x_1768_, 1);
v___x_1769_ = l_Lean_Expr_letE___override(v_declName_1763_, v_typeNew_1738_, v_value_1765_, v_body_1766_, v_nondep_1767_);
v___x_1770_ = lean_apply_6(v___f_1739_, v___x_1769_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, lean_box(0));
return v___x_1770_;
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
lean_dec_ref(v_body_1766_);
lean_dec_ref(v_value_1765_);
lean_dec(v_declName_1763_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec_ref(v___f_1739_);
lean_dec_ref(v_typeNew_1738_);
v_a_1771_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1768_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1768_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
default: 
{
lean_object* v___x_1779_; lean_object* v___x_1780_; 
lean_dec(v_a_1747_);
lean_dec_ref(v___f_1739_);
lean_dec_ref(v_typeNew_1738_);
lean_dec_ref(v___f_1737_);
v___x_1779_ = lean_obj_once(&l_Lean_MVarId_changeLocalDecl___lam__2___closed__3, &l_Lean_MVarId_changeLocalDecl___lam__2___closed__3_once, _init_l_Lean_MVarId_changeLocalDecl___lam__2___closed__3);
v___x_1780_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1740_, v_mvarId_1736_, v___x_1779_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
return v___x_1780_;
}
}
}
else
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec(v___x_1740_);
lean_dec_ref(v___f_1739_);
lean_dec_ref(v_typeNew_1738_);
lean_dec_ref(v___f_1737_);
lean_dec(v_mvarId_1736_);
v_a_1781_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1746_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1746_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1781_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lam__2___boxed(lean_object* v_mvarId_1789_, lean_object* v___f_1790_, lean_object* v_typeNew_1791_, lean_object* v___f_1792_, lean_object* v___x_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v_res_1799_; 
v_res_1799_ = l_Lean_MVarId_changeLocalDecl___lam__2(v_mvarId_1789_, v___f_1790_, v_typeNew_1791_, v___f_1792_, v___x_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lam__3(uint8_t v_checkDefEq_1800_, lean_object* v_typeNew_1801_, lean_object* v___x_1802_, lean_object* v_mvarId_1803_, lean_object* v_fvars_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
lean_object* v___x_1810_; lean_object* v___f_1811_; lean_object* v___f_1812_; lean_object* v___f_1813_; lean_object* v___x_1814_; 
v___x_1810_ = lean_box(v_checkDefEq_1800_);
lean_inc_n(v_mvarId_1803_, 3);
lean_inc(v___x_1802_);
lean_inc_ref(v_typeNew_1801_);
v___f_1811_ = lean_alloc_closure((void*)(l_Lean_MVarId_changeLocalDecl___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1811_, 0, v___x_1810_);
lean_closure_set(v___f_1811_, 1, v_typeNew_1801_);
lean_closure_set(v___f_1811_, 2, v___x_1802_);
lean_closure_set(v___f_1811_, 3, v_mvarId_1803_);
v___f_1812_ = lean_alloc_closure((void*)(l_Lean_MVarId_changeLocalDecl___lam__1___boxed), 8, 2);
lean_closure_set(v___f_1812_, 0, v_mvarId_1803_);
lean_closure_set(v___f_1812_, 1, v_fvars_1804_);
v___f_1813_ = lean_alloc_closure((void*)(l_Lean_MVarId_changeLocalDecl___lam__2___boxed), 10, 5);
lean_closure_set(v___f_1813_, 0, v_mvarId_1803_);
lean_closure_set(v___f_1813_, 1, v___f_1811_);
lean_closure_set(v___f_1813_, 2, v_typeNew_1801_);
lean_closure_set(v___f_1813_, 3, v___f_1812_);
lean_closure_set(v___f_1813_, 4, v___x_1802_);
v___x_1814_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_1803_, v___f_1813_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_);
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lam__3___boxed(lean_object* v_checkDefEq_1815_, lean_object* v_typeNew_1816_, lean_object* v___x_1817_, lean_object* v_mvarId_1818_, lean_object* v_fvars_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
uint8_t v_checkDefEq_boxed_1825_; lean_object* v_res_1826_; 
v_checkDefEq_boxed_1825_ = lean_unbox(v_checkDefEq_1815_);
v_res_1826_ = l_Lean_MVarId_changeLocalDecl___lam__3(v_checkDefEq_boxed_1825_, v_typeNew_1816_, v___x_1817_, v_mvarId_1818_, v_fvars_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl(lean_object* v_mvarId_1830_, lean_object* v_fvarId_1831_, lean_object* v_typeNew_1832_, uint8_t v_checkDefEq_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_){
_start:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___f_1841_; lean_object* v___x_1842_; 
v___x_1839_ = ((lean_object*)(l_Lean_MVarId_changeLocalDecl___closed__1));
v___x_1840_ = lean_box(v_checkDefEq_1833_);
v___f_1841_ = lean_alloc_closure((void*)(l_Lean_MVarId_changeLocalDecl___lam__3___boxed), 10, 3);
lean_closure_set(v___f_1841_, 0, v___x_1840_);
lean_closure_set(v___f_1841_, 1, v_typeNew_1832_);
lean_closure_set(v___f_1841_, 2, v___x_1839_);
lean_inc(v_mvarId_1830_);
v___x_1842_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1830_, v___x_1839_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; uint8_t v___x_1846_; lean_object* v___x_1847_; 
lean_dec_ref_known(v___x_1842_, 1);
v___x_1843_ = lean_unsigned_to_nat(1u);
v___x_1844_ = lean_mk_empty_array_with_capacity(v___x_1843_);
v___x_1845_ = lean_array_push(v___x_1844_, v_fvarId_1831_);
v___x_1846_ = 0;
v___x_1847_ = l_Lean_MVarId_withReverted___redArg(v_mvarId_1830_, v___x_1845_, v___f_1841_, v___x_1846_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1856_; 
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1850_ = v___x_1847_;
v_isShared_1851_ = v_isSharedCheck_1856_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v___x_1847_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1856_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v_snd_1852_; lean_object* v___x_1854_; 
v_snd_1852_ = lean_ctor_get(v_a_1848_, 1);
lean_inc(v_snd_1852_);
lean_dec(v_a_1848_);
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 0, v_snd_1852_);
v___x_1854_ = v___x_1850_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_snd_1852_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
else
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1864_; 
v_a_1857_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1859_ = v___x_1847_;
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1847_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1862_; 
if (v_isShared_1860_ == 0)
{
v___x_1862_ = v___x_1859_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_a_1857_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
}
else
{
lean_object* v_a_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1872_; 
lean_dec_ref(v___f_1841_);
lean_dec(v_fvarId_1831_);
lean_dec(v_mvarId_1830_);
v_a_1865_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1867_ = v___x_1842_;
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v___x_1842_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1870_; 
if (v_isShared_1868_ == 0)
{
v___x_1870_ = v___x_1867_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_a_1865_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___boxed(lean_object* v_mvarId_1873_, lean_object* v_fvarId_1874_, lean_object* v_typeNew_1875_, lean_object* v_checkDefEq_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_){
_start:
{
uint8_t v_checkDefEq_boxed_1882_; lean_object* v_res_1883_; 
v_checkDefEq_boxed_1882_ = lean_unbox(v_checkDefEq_1876_);
v_res_1883_ = l_Lean_MVarId_changeLocalDecl(v_mvarId_1873_, v_fvarId_1874_, v_typeNew_1875_, v_checkDefEq_boxed_1882_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
lean_dec(v_a_1880_);
lean_dec_ref(v_a_1879_);
lean_dec(v_a_1878_);
lean_dec_ref(v_a_1877_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTarget___lam__0(lean_object* v_mvarId_1884_, lean_object* v___x_1885_, lean_object* v_f_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v___x_1892_; 
lean_inc(v_mvarId_1884_);
v___x_1892_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1884_, v___x_1885_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v___x_1893_; 
lean_dec_ref_known(v___x_1892_, 1);
lean_inc(v_mvarId_1884_);
v___x_1893_ = l_Lean_MVarId_getType(v_mvarId_1884_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
if (lean_obj_tag(v___x_1893_) == 0)
{
lean_object* v_a_1894_; lean_object* v___x_1895_; 
v_a_1894_ = lean_ctor_get(v___x_1893_, 0);
lean_inc(v_a_1894_);
lean_dec_ref_known(v___x_1893_, 1);
lean_inc(v___y_1890_);
lean_inc_ref(v___y_1889_);
lean_inc(v___y_1888_);
lean_inc_ref(v___y_1887_);
v___x_1895_ = lean_apply_6(v_f_1886_, v_a_1894_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, lean_box(0));
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v_a_1896_; uint8_t v___x_1897_; lean_object* v___x_1898_; 
v_a_1896_ = lean_ctor_get(v___x_1895_, 0);
lean_inc(v_a_1896_);
lean_dec_ref_known(v___x_1895_, 1);
v___x_1897_ = 0;
v___x_1898_ = l_Lean_MVarId_change(v_mvarId_1884_, v_a_1896_, v___x_1897_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
return v___x_1898_;
}
else
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1906_; 
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec(v_mvarId_1884_);
v_a_1899_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1901_ = v___x_1895_;
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1895_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1904_; 
if (v_isShared_1902_ == 0)
{
v___x_1904_ = v___x_1901_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_a_1899_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
}
}
else
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1914_; 
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec_ref(v_f_1886_);
lean_dec(v_mvarId_1884_);
v_a_1907_ = lean_ctor_get(v___x_1893_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1909_ = v___x_1893_;
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1893_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1912_; 
if (v_isShared_1910_ == 0)
{
v___x_1912_ = v___x_1909_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_a_1907_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
}
else
{
lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1922_; 
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec_ref(v_f_1886_);
lean_dec(v_mvarId_1884_);
v_a_1915_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1917_ = v___x_1892_;
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1892_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1920_; 
if (v_isShared_1918_ == 0)
{
v___x_1920_ = v___x_1917_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_a_1915_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTarget___lam__0___boxed(lean_object* v_mvarId_1923_, lean_object* v___x_1924_, lean_object* v_f_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
lean_object* v_res_1931_; 
v_res_1931_ = l_Lean_MVarId_modifyTarget___lam__0(v_mvarId_1923_, v___x_1924_, v_f_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTarget(lean_object* v_mvarId_1935_, lean_object* v_f_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_){
_start:
{
lean_object* v___x_1942_; lean_object* v___f_1943_; lean_object* v___x_1944_; 
v___x_1942_ = ((lean_object*)(l_Lean_MVarId_modifyTarget___closed__1));
lean_inc(v_mvarId_1935_);
v___f_1943_ = lean_alloc_closure((void*)(l_Lean_MVarId_modifyTarget___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1943_, 0, v_mvarId_1935_);
lean_closure_set(v___f_1943_, 1, v___x_1942_);
lean_closure_set(v___f_1943_, 2, v_f_1936_);
v___x_1944_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_1935_, v___f_1943_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_);
return v___x_1944_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTarget___boxed(lean_object* v_mvarId_1945_, lean_object* v_f_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_){
_start:
{
lean_object* v_res_1952_; 
v_res_1952_ = l_Lean_MVarId_modifyTarget(v_mvarId_1945_, v_f_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_);
lean_dec(v_a_1950_);
lean_dec_ref(v_a_1949_);
lean_dec(v_a_1948_);
lean_dec_ref(v_a_1947_);
return v_res_1952_;
}
}
static lean_object* _init_l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1957_ = ((lean_object*)(l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__2));
v___x_1958_ = l_Lean_stringToMessageData(v___x_1957_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTargetEqLHS___lam__0(lean_object* v_f_1959_, lean_object* v_mvarId_1960_, lean_object* v_target_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_){
_start:
{
lean_object* v___x_1967_; 
lean_inc_ref(v_target_1961_);
v___x_1967_ = l_Lean_Meta_matchEq_x3f(v_target_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v_a_1968_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
lean_inc(v_a_1968_);
lean_dec_ref_known(v___x_1967_, 1);
if (lean_obj_tag(v_a_1968_) == 1)
{
lean_object* v_val_1969_; lean_object* v_snd_1970_; lean_object* v_fst_1971_; lean_object* v_snd_1972_; lean_object* v___x_1973_; 
lean_dec_ref(v_target_1961_);
lean_dec(v_mvarId_1960_);
v_val_1969_ = lean_ctor_get(v_a_1968_, 0);
lean_inc(v_val_1969_);
lean_dec_ref_known(v_a_1968_, 1);
v_snd_1970_ = lean_ctor_get(v_val_1969_, 1);
lean_inc(v_snd_1970_);
lean_dec(v_val_1969_);
v_fst_1971_ = lean_ctor_get(v_snd_1970_, 0);
lean_inc(v_fst_1971_);
v_snd_1972_ = lean_ctor_get(v_snd_1970_, 1);
lean_inc(v_snd_1972_);
lean_dec(v_snd_1970_);
lean_inc(v___y_1965_);
lean_inc_ref(v___y_1964_);
lean_inc(v___y_1963_);
lean_inc_ref(v___y_1962_);
v___x_1973_ = lean_apply_6(v_f_1959_, v_fst_1971_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, lean_box(0));
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v_a_1974_; lean_object* v___x_1975_; 
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
lean_inc(v_a_1974_);
lean_dec_ref_known(v___x_1973_, 1);
v___x_1975_ = l_Lean_Meta_mkEq(v_a_1974_, v_snd_1972_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
return v___x_1975_;
}
else
{
lean_dec(v_snd_1972_);
return v___x_1973_;
}
}
else
{
lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; 
lean_dec(v_a_1968_);
lean_dec_ref(v_f_1959_);
v___x_1976_ = ((lean_object*)(l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__1));
v___x_1977_ = lean_obj_once(&l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__3, &l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__3_once, _init_l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__3);
v___x_1978_ = l_Lean_indentExpr(v_target_1961_);
v___x_1979_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1977_);
lean_ctor_set(v___x_1979_, 1, v___x_1978_);
v___x_1980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1979_);
v___x_1981_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1976_, v_mvarId_1960_, v___x_1980_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
return v___x_1981_;
}
}
else
{
lean_object* v_a_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1989_; 
lean_dec_ref(v_target_1961_);
lean_dec(v_mvarId_1960_);
lean_dec_ref(v_f_1959_);
v_a_1982_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1984_ = v___x_1967_;
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_a_1982_);
lean_dec(v___x_1967_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1987_; 
if (v_isShared_1985_ == 0)
{
v___x_1987_ = v___x_1984_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v_a_1982_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTargetEqLHS___lam__0___boxed(lean_object* v_f_1990_, lean_object* v_mvarId_1991_, lean_object* v_target_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_){
_start:
{
lean_object* v_res_1998_; 
v_res_1998_ = l_Lean_MVarId_modifyTargetEqLHS___lam__0(v_f_1990_, v_mvarId_1991_, v_target_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
return v_res_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTargetEqLHS(lean_object* v_mvarId_1999_, lean_object* v_f_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_){
_start:
{
lean_object* v___f_2006_; lean_object* v___x_2007_; 
lean_inc(v_mvarId_1999_);
v___f_2006_ = lean_alloc_closure((void*)(l_Lean_MVarId_modifyTargetEqLHS___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2006_, 0, v_f_2000_);
lean_closure_set(v___f_2006_, 1, v_mvarId_1999_);
v___x_2007_ = l_Lean_MVarId_modifyTarget(v_mvarId_1999_, v___f_2006_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTargetEqLHS___boxed(lean_object* v_mvarId_2008_, lean_object* v_f_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_){
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = l_Lean_MVarId_modifyTargetEqLHS(v_mvarId_2008_, v_f_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_);
lean_dec(v_a_2013_);
lean_dec_ref(v_a_2012_);
lean_dec(v_a_2011_);
lean_dec_ref(v_a_2010_);
return v_res_2015_;
}
}
static lean_object* _init_l_Lean_MVarId_clearValue___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; 
v___x_2017_ = ((lean_object*)(l_Lean_MVarId_clearValue___lam__0___closed__0));
v___x_2018_ = l_Lean_stringToMessageData(v___x_2017_);
return v___x_2018_;
}
}
static lean_object* _init_l_Lean_MVarId_clearValue___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2020_ = ((lean_object*)(l_Lean_MVarId_clearValue___lam__0___closed__2));
v___x_2021_ = l_Lean_stringToMessageData(v___x_2020_);
return v___x_2021_;
}
}
static lean_object* _init_l_Lean_MVarId_clearValue___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; 
v___x_2023_ = ((lean_object*)(l_Lean_MVarId_clearValue___lam__0___closed__4));
v___x_2024_ = l_Lean_stringToMessageData(v___x_2023_);
return v___x_2024_;
}
}
static lean_object* _init_l_Lean_MVarId_clearValue___lam__0___closed__7(void){
_start:
{
lean_object* v___x_2026_; lean_object* v___x_2027_; 
v___x_2026_ = ((lean_object*)(l_Lean_MVarId_clearValue___lam__0___closed__6));
v___x_2027_ = l_Lean_stringToMessageData(v___x_2026_);
return v___x_2027_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearValue___lam__0(lean_object* v_mvarId_x27_2028_, lean_object* v_a_2029_, lean_object* v_fvars_2030_, lean_object* v_fvarId_2031_, lean_object* v___x_2032_, lean_object* v_mvarId_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_){
_start:
{
lean_object* v___x_2039_; 
lean_inc(v_mvarId_x27_2028_);
v___x_2039_ = l_Lean_MVarId_getType(v_mvarId_x27_2028_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2040_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v___y_2076_; lean_object* v___y_2077_; lean_object* v___y_2078_; lean_object* v___y_2079_; uint8_t v___x_2121_; 
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
lean_inc(v_a_2040_);
lean_dec_ref_known(v___x_2039_, 1);
v___x_2121_ = l_Lean_Expr_isLet(v_a_2040_);
if (v___x_2121_ == 0)
{
lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2122_ = lean_obj_once(&l_Lean_MVarId_clearValue___lam__0___closed__5, &l_Lean_MVarId_clearValue___lam__0___closed__5_once, _init_l_Lean_MVarId_clearValue___lam__0___closed__5);
lean_inc(v_fvarId_2031_);
v___x_2123_ = l_Lean_Expr_fvar___override(v_fvarId_2031_);
v___x_2124_ = l_Lean_MessageData_ofExpr(v___x_2123_);
v___x_2125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2122_);
lean_ctor_set(v___x_2125_, 1, v___x_2124_);
v___x_2126_ = lean_obj_once(&l_Lean_MVarId_clearValue___lam__0___closed__7, &l_Lean_MVarId_clearValue___lam__0___closed__7_once, _init_l_Lean_MVarId_clearValue___lam__0___closed__7);
v___x_2127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2125_);
lean_ctor_set(v___x_2127_, 1, v___x_2126_);
v___x_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2127_);
lean_inc_n(v_mvarId_2033_, 2);
lean_inc(v___x_2032_);
v___x_2129_ = lean_alloc_closure((void*)(l_Lean_Meta_throwTacticEx___boxed), 9, 4);
lean_closure_set(v___x_2129_, 0, lean_box(0));
lean_closure_set(v___x_2129_, 1, v___x_2032_);
lean_closure_set(v___x_2129_, 2, v_mvarId_2033_);
lean_closure_set(v___x_2129_, 3, v___x_2128_);
v___x_2130_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_2033_, v___x_2129_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_dec_ref_known(v___x_2130_, 1);
v___y_2076_ = v___y_2034_;
v___y_2077_ = v___y_2035_;
v___y_2078_ = v___y_2036_;
v___y_2079_ = v___y_2037_;
goto v___jp_2075_;
}
else
{
lean_object* v_a_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2138_; 
lean_dec(v_a_2040_);
lean_dec(v_mvarId_2033_);
lean_dec(v___x_2032_);
lean_dec(v_fvarId_2031_);
lean_dec_ref(v_fvars_2030_);
lean_dec(v_a_2029_);
lean_dec(v_mvarId_x27_2028_);
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2138_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2133_ = v___x_2130_;
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_a_2131_);
lean_dec(v___x_2130_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2136_; 
if (v_isShared_2134_ == 0)
{
v___x_2136_ = v___x_2133_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_a_2131_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
}
else
{
v___y_2076_ = v___y_2034_;
v___y_2077_ = v___y_2035_;
v___y_2078_ = v___y_2036_;
v___y_2079_ = v___y_2037_;
goto v___jp_2075_;
}
v___jp_2041_:
{
lean_object* v___x_2047_; 
v___x_2047_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_2042_, v_a_2029_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v_a_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2065_; 
v_a_2048_ = lean_ctor_get(v___x_2047_, 0);
lean_inc_n(v_a_2048_, 2);
lean_dec_ref_known(v___x_2047_, 1);
v___x_2049_ = l_Lean_Expr_letValue_x21(v_a_2040_);
lean_dec(v_a_2040_);
v___x_2050_ = l_Lean_Expr_app___override(v_a_2048_, v___x_2049_);
v___x_2051_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg(v_mvarId_x27_2028_, v___x_2050_, v___y_2044_);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2065_ == 0)
{
lean_object* v_unused_2066_; 
v_unused_2066_ = lean_ctor_get(v___x_2051_, 0);
lean_dec(v_unused_2066_);
v___x_2053_ = v___x_2051_;
v_isShared_2054_ = v_isSharedCheck_2065_;
goto v_resetjp_2052_;
}
else
{
lean_dec(v___x_2051_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2065_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2055_; size_t v_sz_2056_; size_t v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2063_; 
v___x_2055_ = lean_box(0);
v_sz_2056_ = lean_array_size(v_fvars_2030_);
v___x_2057_ = ((size_t)0ULL);
v___x_2058_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_changeLocalDecl_spec__0(v_sz_2056_, v___x_2057_, v_fvars_2030_);
v___x_2059_ = l_Lean_Expr_mvarId_x21(v_a_2048_);
lean_dec(v_a_2048_);
v___x_2060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2058_);
lean_ctor_set(v___x_2060_, 1, v___x_2059_);
v___x_2061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2055_);
lean_ctor_set(v___x_2061_, 1, v___x_2060_);
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 0, v___x_2061_);
v___x_2063_ = v___x_2053_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v___x_2061_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
else
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2074_; 
lean_dec(v_a_2040_);
lean_dec_ref(v_fvars_2030_);
lean_dec(v_mvarId_x27_2028_);
v_a_2067_ = lean_ctor_get(v___x_2047_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2069_ = v___x_2047_;
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2047_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2072_; 
if (v_isShared_2070_ == 0)
{
v___x_2072_ = v___x_2069_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2067_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
}
v___jp_2075_:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; uint8_t v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2120_; 
v___x_2080_ = l_Lean_Expr_letName_x21(v_a_2040_);
v___x_2081_ = l_Lean_Expr_letType_x21(v_a_2040_);
v___x_2082_ = l_Lean_Expr_letBody_x21(v_a_2040_);
v___x_2083_ = 0;
v___x_2084_ = l_Lean_Expr_forallE___override(v___x_2080_, v___x_2081_, v___x_2082_, v___x_2083_);
v___x_2085_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(v___x_2084_, v___y_2077_);
v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2088_ = v___x_2085_;
v_isShared_2089_ = v_isSharedCheck_2120_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_2085_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2120_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2090_; 
lean_inc(v_a_2086_);
v___x_2090_ = l_Lean_Meta_isTypeCorrect(v_a_2086_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v_a_2091_; uint8_t v___x_2092_; 
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_a_2091_);
lean_dec_ref_known(v___x_2090_, 1);
v___x_2092_ = lean_unbox(v_a_2091_);
lean_dec(v_a_2091_);
if (v___x_2092_ == 0)
{
lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2100_; 
v___x_2093_ = lean_obj_once(&l_Lean_MVarId_clearValue___lam__0___closed__1, &l_Lean_MVarId_clearValue___lam__0___closed__1_once, _init_l_Lean_MVarId_clearValue___lam__0___closed__1);
v___x_2094_ = l_Lean_Expr_fvar___override(v_fvarId_2031_);
v___x_2095_ = l_Lean_MessageData_ofExpr(v___x_2094_);
v___x_2096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2093_);
lean_ctor_set(v___x_2096_, 1, v___x_2095_);
v___x_2097_ = lean_obj_once(&l_Lean_MVarId_clearValue___lam__0___closed__3, &l_Lean_MVarId_clearValue___lam__0___closed__3_once, _init_l_Lean_MVarId_clearValue___lam__0___closed__3);
v___x_2098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2096_);
lean_ctor_set(v___x_2098_, 1, v___x_2097_);
if (v_isShared_2089_ == 0)
{
lean_ctor_set_tag(v___x_2088_, 1);
lean_ctor_set(v___x_2088_, 0, v___x_2098_);
v___x_2100_ = v___x_2088_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v___x_2098_);
v___x_2100_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; 
lean_inc(v_mvarId_2033_);
v___x_2101_ = lean_alloc_closure((void*)(l_Lean_Meta_throwTacticEx___boxed), 9, 4);
lean_closure_set(v___x_2101_, 0, lean_box(0));
lean_closure_set(v___x_2101_, 1, v___x_2032_);
lean_closure_set(v___x_2101_, 2, v_mvarId_2033_);
lean_closure_set(v___x_2101_, 3, v___x_2100_);
v___x_2102_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_2033_, v___x_2101_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_dec_ref_known(v___x_2102_, 1);
v___y_2042_ = v_a_2086_;
v___y_2043_ = v___y_2076_;
v___y_2044_ = v___y_2077_;
v___y_2045_ = v___y_2078_;
v___y_2046_ = v___y_2079_;
goto v___jp_2041_;
}
else
{
lean_object* v_a_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2110_; 
lean_dec(v_a_2086_);
lean_dec(v_a_2040_);
lean_dec_ref(v_fvars_2030_);
lean_dec(v_a_2029_);
lean_dec(v_mvarId_x27_2028_);
v_a_2103_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2105_ = v___x_2102_;
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_a_2103_);
lean_dec(v___x_2102_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2108_; 
if (v_isShared_2106_ == 0)
{
v___x_2108_ = v___x_2105_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_a_2103_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
}
}
else
{
lean_del_object(v___x_2088_);
lean_dec(v_mvarId_2033_);
lean_dec(v___x_2032_);
lean_dec(v_fvarId_2031_);
v___y_2042_ = v_a_2086_;
v___y_2043_ = v___y_2076_;
v___y_2044_ = v___y_2077_;
v___y_2045_ = v___y_2078_;
v___y_2046_ = v___y_2079_;
goto v___jp_2041_;
}
}
else
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
lean_del_object(v___x_2088_);
lean_dec(v_a_2086_);
lean_dec(v_a_2040_);
lean_dec(v_mvarId_2033_);
lean_dec(v___x_2032_);
lean_dec(v_fvarId_2031_);
lean_dec_ref(v_fvars_2030_);
lean_dec(v_a_2029_);
lean_dec(v_mvarId_x27_2028_);
v_a_2112_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2114_ = v___x_2090_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2090_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2117_; 
if (v_isShared_2115_ == 0)
{
v___x_2117_ = v___x_2114_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_a_2112_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
}
}
}
else
{
lean_object* v_a_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2146_; 
lean_dec(v_mvarId_2033_);
lean_dec(v___x_2032_);
lean_dec(v_fvarId_2031_);
lean_dec_ref(v_fvars_2030_);
lean_dec(v_a_2029_);
lean_dec(v_mvarId_x27_2028_);
v_a_2139_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2141_ = v___x_2039_;
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_a_2139_);
lean_dec(v___x_2039_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2144_; 
if (v_isShared_2142_ == 0)
{
v___x_2144_ = v___x_2141_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_a_2139_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearValue___lam__0___boxed(lean_object* v_mvarId_x27_2147_, lean_object* v_a_2148_, lean_object* v_fvars_2149_, lean_object* v_fvarId_2150_, lean_object* v___x_2151_, lean_object* v_mvarId_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_){
_start:
{
lean_object* v_res_2158_; 
v_res_2158_ = l_Lean_MVarId_clearValue___lam__0(v_mvarId_x27_2147_, v_a_2148_, v_fvars_2149_, v_fvarId_2150_, v___x_2151_, v_mvarId_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
return v_res_2158_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearValue___lam__1(lean_object* v_a_2159_, lean_object* v_fvarId_2160_, lean_object* v___x_2161_, lean_object* v_mvarId_2162_, lean_object* v_mvarId_x27_2163_, lean_object* v_fvars_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_){
_start:
{
lean_object* v___f_2170_; lean_object* v___x_2171_; 
lean_inc(v_mvarId_x27_2163_);
v___f_2170_ = lean_alloc_closure((void*)(l_Lean_MVarId_clearValue___lam__0___boxed), 11, 6);
lean_closure_set(v___f_2170_, 0, v_mvarId_x27_2163_);
lean_closure_set(v___f_2170_, 1, v_a_2159_);
lean_closure_set(v___f_2170_, 2, v_fvars_2164_);
lean_closure_set(v___f_2170_, 3, v_fvarId_2160_);
lean_closure_set(v___f_2170_, 4, v___x_2161_);
lean_closure_set(v___f_2170_, 5, v_mvarId_2162_);
v___x_2171_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_x27_2163_, v___f_2170_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
return v___x_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearValue___lam__1___boxed(lean_object* v_a_2172_, lean_object* v_fvarId_2173_, lean_object* v___x_2174_, lean_object* v_mvarId_2175_, lean_object* v_mvarId_x27_2176_, lean_object* v_fvars_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_){
_start:
{
lean_object* v_res_2183_; 
v_res_2183_ = l_Lean_MVarId_clearValue___lam__1(v_a_2172_, v_fvarId_2173_, v___x_2174_, v_mvarId_2175_, v_mvarId_x27_2176_, v_fvars_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearValue(lean_object* v_mvarId_2187_, lean_object* v_fvarId_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_){
_start:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2194_ = ((lean_object*)(l_Lean_MVarId_clearValue___closed__1));
lean_inc(v_mvarId_2187_);
v___x_2195_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2187_, v___x_2194_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_object* v___x_2196_; 
lean_dec_ref_known(v___x_2195_, 1);
lean_inc(v_mvarId_2187_);
v___x_2196_ = l_Lean_MVarId_getTag(v_mvarId_2187_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_);
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_object* v_a_2197_; lean_object* v___f_2198_; lean_object* v___x_2199_; 
v_a_2197_ = lean_ctor_get(v___x_2196_, 0);
lean_inc(v_a_2197_);
lean_dec_ref_known(v___x_2196_, 1);
lean_inc(v_mvarId_2187_);
lean_inc(v_fvarId_2188_);
v___f_2198_ = lean_alloc_closure((void*)(l_Lean_MVarId_clearValue___lam__1___boxed), 11, 4);
lean_closure_set(v___f_2198_, 0, v_a_2197_);
lean_closure_set(v___f_2198_, 1, v_fvarId_2188_);
lean_closure_set(v___f_2198_, 2, v___x_2194_);
lean_closure_set(v___f_2198_, 3, v_mvarId_2187_);
v___x_2199_ = l_Lean_MVarId_withRevertedFrom___redArg(v_mvarId_2187_, v_fvarId_2188_, v___f_2198_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_);
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2208_; 
v_a_2200_ = lean_ctor_get(v___x_2199_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2202_ = v___x_2199_;
v_isShared_2203_ = v_isSharedCheck_2208_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2199_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2208_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v_snd_2204_; lean_object* v___x_2206_; 
v_snd_2204_ = lean_ctor_get(v_a_2200_, 1);
lean_inc(v_snd_2204_);
lean_dec(v_a_2200_);
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 0, v_snd_2204_);
v___x_2206_ = v___x_2202_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_snd_2204_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
else
{
lean_object* v_a_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2216_; 
v_a_2209_ = lean_ctor_get(v___x_2199_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2211_ = v___x_2199_;
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_a_2209_);
lean_dec(v___x_2199_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2214_; 
if (v_isShared_2212_ == 0)
{
v___x_2214_ = v___x_2211_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_a_2209_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
}
else
{
lean_object* v_a_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2224_; 
lean_dec(v_fvarId_2188_);
lean_dec(v_mvarId_2187_);
v_a_2217_ = lean_ctor_get(v___x_2196_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2219_ = v___x_2196_;
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_a_2217_);
lean_dec(v___x_2196_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2222_; 
if (v_isShared_2220_ == 0)
{
v___x_2222_ = v___x_2219_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_a_2217_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
}
else
{
lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2232_; 
lean_dec(v_fvarId_2188_);
lean_dec(v_mvarId_2187_);
v_a_2225_ = lean_ctor_get(v___x_2195_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2227_ = v___x_2195_;
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_dec(v___x_2195_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2230_; 
if (v_isShared_2228_ == 0)
{
v___x_2230_ = v___x_2227_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_a_2225_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearValue___boxed(lean_object* v_mvarId_2233_, lean_object* v_fvarId_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_){
_start:
{
lean_object* v_res_2240_; 
v_res_2240_ = l_Lean_MVarId_clearValue(v_mvarId_2233_, v_fvarId_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_);
lean_dec(v_a_2238_);
lean_dec_ref(v_a_2237_);
lean_dec(v_a_2236_);
lean_dec_ref(v_a_2235_);
return v_res_2240_;
}
}
lean_object* runtime_initialize_Lean_Elab_InfoTree_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_MatchUtil(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Assert(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Replace(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
