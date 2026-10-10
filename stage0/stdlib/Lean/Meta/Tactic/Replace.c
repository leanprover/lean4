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
lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(lean_object* v_mvarId_1_, lean_object* v_x_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_){
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
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1_ = stack[0].m_obj;
lean_object* v_x_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v___y_6_ = stack[5].m_obj;
lean_object* v_res_25_;
v_res_25_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_1_, v_x_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_);
stack->m_obj
 = v_res_25_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg___boxed(lean_object* v_mvarId_26_, lean_object* v_x_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_26_, v_x_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_);
lean_dec(v___y_31_);
lean_dec_ref(v___y_30_);
lean_dec(v___y_29_);
lean_dec_ref(v___y_28_);
return v_res_33_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1(lean_object* v_00_u03b1_34_, lean_object* v_mvarId_35_, lean_object* v_x_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_35_, v_x_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_);
return v___x_42_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_35_ = stack[1].m_obj;
lean_object* v_x_36_ = stack[2].m_obj;
lean_object* v___y_37_ = stack[3].m_obj;
lean_object* v___y_38_ = stack[4].m_obj;
lean_object* v___y_39_ = stack[5].m_obj;
lean_object* v___y_40_ = stack[6].m_obj;
lean_object* v_res_43_;
v_res_43_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1(lean_box(0), v_mvarId_35_, v_x_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_);
stack->m_obj
 = v_res_43_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___boxed(lean_object* v_00_u03b1_44_, lean_object* v_mvarId_45_, lean_object* v_x_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1(v_00_u03b1_44_, v_mvarId_45_, v_x_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_);
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
lean_dec(v___y_48_);
lean_dec_ref(v___y_47_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(lean_object* v_x_53_, lean_object* v_x_54_, lean_object* v_x_55_, lean_object* v_x_56_){
_start:
{
lean_object* v_ks_57_; lean_object* v_vs_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_82_; 
v_ks_57_ = lean_ctor_get(v_x_53_, 0);
v_vs_58_ = lean_ctor_get(v_x_53_, 1);
v_isSharedCheck_82_ = !lean_is_exclusive(v_x_53_);
if (v_isSharedCheck_82_ == 0)
{
v___x_60_ = v_x_53_;
v_isShared_61_ = v_isSharedCheck_82_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_vs_58_);
lean_inc(v_ks_57_);
lean_dec(v_x_53_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_82_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v___x_62_; uint8_t v___x_63_; 
v___x_62_ = lean_array_get_size(v_ks_57_);
v___x_63_ = lean_nat_dec_lt(v_x_54_, v___x_62_);
if (v___x_63_ == 0)
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_67_; 
lean_dec(v_x_54_);
v___x_64_ = lean_array_push(v_ks_57_, v_x_55_);
v___x_65_ = lean_array_push(v_vs_58_, v_x_56_);
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 1, v___x_65_);
lean_ctor_set(v___x_60_, 0, v___x_64_);
v___x_67_ = v___x_60_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v___x_64_);
lean_ctor_set(v_reuseFailAlloc_68_, 1, v___x_65_);
v___x_67_ = v_reuseFailAlloc_68_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
return v___x_67_;
}
}
else
{
lean_object* v_k_x27_69_; uint8_t v___x_70_; 
v_k_x27_69_ = lean_array_fget_borrowed(v_ks_57_, v_x_54_);
v___x_70_ = l_Lean_instBEqMVarId_beq(v_x_55_, v_k_x27_69_);
if (v___x_70_ == 0)
{
lean_object* v___x_72_; 
if (v_isShared_61_ == 0)
{
v___x_72_ = v___x_60_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v_ks_57_);
lean_ctor_set(v_reuseFailAlloc_76_, 1, v_vs_58_);
v___x_72_ = v_reuseFailAlloc_76_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = lean_unsigned_to_nat(1u);
v___x_74_ = lean_nat_add(v_x_54_, v___x_73_);
lean_dec(v_x_54_);
v_x_53_ = v___x_72_;
v_x_54_ = v___x_74_;
goto _start;
}
}
else
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_80_; 
v___x_77_ = lean_array_fset(v_ks_57_, v_x_54_, v_x_55_);
v___x_78_ = lean_array_fset(v_vs_58_, v_x_54_, v_x_56_);
lean_dec(v_x_54_);
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 1, v___x_78_);
lean_ctor_set(v___x_60_, 0, v___x_77_);
v___x_80_ = v___x_60_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v___x_77_);
lean_ctor_set(v_reuseFailAlloc_81_, 1, v___x_78_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_n_83_, lean_object* v_k_84_, lean_object* v_v_85_){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = lean_unsigned_to_nat(0u);
v___x_87_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_n_83_, v___x_86_, v_k_84_, v_v_85_);
return v___x_87_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_88_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg(lean_object* v_x_89_, size_t v_x_90_, size_t v_x_91_, lean_object* v_x_92_, lean_object* v_x_93_){
_start:
{
if (lean_obj_tag(v_x_89_) == 0)
{
lean_object* v_es_94_; size_t v___x_95_; size_t v___x_96_; lean_object* v_j_97_; lean_object* v___x_98_; uint8_t v___x_99_; 
v_es_94_ = lean_ctor_get(v_x_89_, 0);
v___x_95_ = ((size_t)31ULL);
v___x_96_ = lean_usize_land(v_x_90_, v___x_95_);
v_j_97_ = lean_usize_to_nat(v___x_96_);
v___x_98_ = lean_array_get_size(v_es_94_);
v___x_99_ = lean_nat_dec_lt(v_j_97_, v___x_98_);
if (v___x_99_ == 0)
{
lean_dec(v_j_97_);
lean_dec(v_x_93_);
lean_dec(v_x_92_);
return v_x_89_;
}
else
{
lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_138_; 
lean_inc_ref(v_es_94_);
v_isSharedCheck_138_ = !lean_is_exclusive(v_x_89_);
if (v_isSharedCheck_138_ == 0)
{
lean_object* v_unused_139_; 
v_unused_139_ = lean_ctor_get(v_x_89_, 0);
lean_dec(v_unused_139_);
v___x_101_ = v_x_89_;
v_isShared_102_ = v_isSharedCheck_138_;
goto v_resetjp_100_;
}
else
{
lean_dec(v_x_89_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_138_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v_v_103_; lean_object* v___x_104_; lean_object* v_xs_x27_105_; lean_object* v___y_107_; 
v_v_103_ = lean_array_fget(v_es_94_, v_j_97_);
v___x_104_ = lean_box(0);
v_xs_x27_105_ = lean_array_fset(v_es_94_, v_j_97_, v___x_104_);
switch(lean_obj_tag(v_v_103_))
{
case 0:
{
lean_object* v_key_112_; lean_object* v_val_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_123_; 
v_key_112_ = lean_ctor_get(v_v_103_, 0);
v_val_113_ = lean_ctor_get(v_v_103_, 1);
v_isSharedCheck_123_ = !lean_is_exclusive(v_v_103_);
if (v_isSharedCheck_123_ == 0)
{
v___x_115_ = v_v_103_;
v_isShared_116_ = v_isSharedCheck_123_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_val_113_);
lean_inc(v_key_112_);
lean_dec(v_v_103_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_123_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
uint8_t v___x_117_; 
v___x_117_ = l_Lean_instBEqMVarId_beq(v_x_92_, v_key_112_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; lean_object* v___x_119_; 
lean_del_object(v___x_115_);
v___x_118_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_112_, v_val_113_, v_x_92_, v_x_93_);
v___x_119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
v___y_107_ = v___x_119_;
goto v___jp_106_;
}
else
{
lean_object* v___x_121_; 
lean_dec(v_val_113_);
lean_dec(v_key_112_);
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 1, v_x_93_);
lean_ctor_set(v___x_115_, 0, v_x_92_);
v___x_121_ = v___x_115_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_x_92_);
lean_ctor_set(v_reuseFailAlloc_122_, 1, v_x_93_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
v___y_107_ = v___x_121_;
goto v___jp_106_;
}
}
}
}
case 1:
{
lean_object* v_node_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_136_; 
v_node_124_ = lean_ctor_get(v_v_103_, 0);
v_isSharedCheck_136_ = !lean_is_exclusive(v_v_103_);
if (v_isSharedCheck_136_ == 0)
{
v___x_126_ = v_v_103_;
v_isShared_127_ = v_isSharedCheck_136_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_node_124_);
lean_dec(v_v_103_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_136_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
size_t v___x_128_; size_t v___x_129_; size_t v___x_130_; size_t v___x_131_; lean_object* v___x_132_; lean_object* v___x_134_; 
v___x_128_ = ((size_t)5ULL);
v___x_129_ = lean_usize_shift_right(v_x_90_, v___x_128_);
v___x_130_ = ((size_t)1ULL);
v___x_131_ = lean_usize_add(v_x_91_, v___x_130_);
v___x_132_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg(v_node_124_, v___x_129_, v___x_131_, v_x_92_, v_x_93_);
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 0, v___x_132_);
v___x_134_ = v___x_126_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v___x_132_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
v___y_107_ = v___x_134_;
goto v___jp_106_;
}
}
}
default: 
{
lean_object* v___x_137_; 
v___x_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_137_, 0, v_x_92_);
lean_ctor_set(v___x_137_, 1, v_x_93_);
v___y_107_ = v___x_137_;
goto v___jp_106_;
}
}
v___jp_106_:
{
lean_object* v___x_108_; lean_object* v___x_110_; 
v___x_108_ = lean_array_fset(v_xs_x27_105_, v_j_97_, v___y_107_);
lean_dec(v_j_97_);
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 0, v___x_108_);
v___x_110_ = v___x_101_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v___x_108_);
v___x_110_ = v_reuseFailAlloc_111_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
return v___x_110_;
}
}
}
}
}
else
{
lean_object* v_ks_140_; lean_object* v_vs_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_159_; 
v_ks_140_ = lean_ctor_get(v_x_89_, 0);
v_vs_141_ = lean_ctor_get(v_x_89_, 1);
v_isSharedCheck_159_ = !lean_is_exclusive(v_x_89_);
if (v_isSharedCheck_159_ == 0)
{
v___x_143_ = v_x_89_;
v_isShared_144_ = v_isSharedCheck_159_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_vs_141_);
lean_inc(v_ks_140_);
lean_dec(v_x_89_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_159_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_146_; 
if (v_isShared_144_ == 0)
{
v___x_146_ = v___x_143_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_ks_140_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v_vs_141_);
v___x_146_ = v_reuseFailAlloc_158_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
lean_object* v_newNode_147_; size_t v___x_148_; uint8_t v___x_149_; 
v_newNode_147_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3___redArg(v___x_146_, v_x_92_, v_x_93_);
v___x_148_ = ((size_t)7ULL);
v___x_149_ = lean_usize_dec_le(v___x_148_, v_x_91_);
if (v___x_149_ == 0)
{
lean_object* v___x_150_; lean_object* v___x_151_; uint8_t v___x_152_; 
v___x_150_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_147_);
v___x_151_ = lean_unsigned_to_nat(4u);
v___x_152_ = lean_nat_dec_lt(v___x_150_, v___x_151_);
lean_dec(v___x_150_);
if (v___x_152_ == 0)
{
lean_object* v_ks_153_; lean_object* v_vs_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v_ks_153_ = lean_ctor_get(v_newNode_147_, 0);
lean_inc_ref(v_ks_153_);
v_vs_154_ = lean_ctor_get(v_newNode_147_, 1);
lean_inc_ref(v_vs_154_);
lean_dec_ref(v_newNode_147_);
v___x_155_ = lean_unsigned_to_nat(0u);
v___x_156_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_157_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4___redArg(v_x_91_, v_ks_153_, v_vs_154_, v___x_155_, v___x_156_);
lean_dec_ref(v_vs_154_);
lean_dec_ref(v_ks_153_);
return v___x_157_;
}
else
{
return v_newNode_147_;
}
}
else
{
return v_newNode_147_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_89_ = stack[0].m_obj;
size_t v_x_90_ = stack[1].m_num;
size_t v_x_91_ = stack[2].m_num;
lean_object* v_x_92_ = stack[3].m_obj;
lean_object* v_x_93_ = stack[4].m_obj;
lean_object* v_res_160_;
v_res_160_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg(v_x_89_, v_x_90_, v_x_91_, v_x_92_, v_x_93_);
stack->m_obj
 = v_res_160_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4___redArg(size_t v_depth_161_, lean_object* v_keys_162_, lean_object* v_vals_163_, lean_object* v_i_164_, lean_object* v_entries_165_){
_start:
{
lean_object* v___x_166_; uint8_t v___x_167_; 
v___x_166_ = lean_array_get_size(v_keys_162_);
v___x_167_ = lean_nat_dec_lt(v_i_164_, v___x_166_);
if (v___x_167_ == 0)
{
lean_dec(v_i_164_);
return v_entries_165_;
}
else
{
lean_object* v_k_168_; lean_object* v_v_169_; uint64_t v___x_170_; size_t v_h_171_; size_t v___x_172_; lean_object* v___x_173_; size_t v___x_174_; size_t v___x_175_; size_t v___x_176_; size_t v_h_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v_k_168_ = lean_array_fget_borrowed(v_keys_162_, v_i_164_);
v_v_169_ = lean_array_fget_borrowed(v_vals_163_, v_i_164_);
v___x_170_ = l_Lean_instHashableMVarId_hash(v_k_168_);
v_h_171_ = lean_uint64_to_usize(v___x_170_);
v___x_172_ = ((size_t)5ULL);
v___x_173_ = lean_unsigned_to_nat(1u);
v___x_174_ = ((size_t)1ULL);
v___x_175_ = lean_usize_sub(v_depth_161_, v___x_174_);
v___x_176_ = lean_usize_mul(v___x_172_, v___x_175_);
v_h_177_ = lean_usize_shift_right(v_h_171_, v___x_176_);
v___x_178_ = lean_nat_add(v_i_164_, v___x_173_);
lean_dec(v_i_164_);
lean_inc(v_v_169_);
lean_inc(v_k_168_);
v___x_179_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg(v_entries_165_, v_h_177_, v_depth_161_, v_k_168_, v_v_169_);
v_i_164_ = v___x_178_;
v_entries_165_ = v___x_179_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_161_ = stack[0].m_num;
lean_object* v_keys_162_ = stack[1].m_obj;
lean_object* v_vals_163_ = stack[2].m_obj;
lean_object* v_i_164_ = stack[3].m_obj;
lean_object* v_entries_165_ = stack[4].m_obj;
lean_object* v_res_181_;
v_res_181_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_161_, v_keys_162_, v_vals_163_, v_i_164_, v_entries_165_);
stack->m_obj
 = v_res_181_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_depth_182_, lean_object* v_keys_183_, lean_object* v_vals_184_, lean_object* v_i_185_, lean_object* v_entries_186_){
_start:
{
size_t v_depth_boxed_187_; lean_object* v_res_188_; 
v_depth_boxed_187_ = lean_unbox_usize(v_depth_182_);
lean_dec(v_depth_182_);
v_res_188_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_boxed_187_, v_keys_183_, v_vals_184_, v_i_185_, v_entries_186_);
lean_dec_ref(v_vals_184_);
lean_dec_ref(v_keys_183_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_189_, lean_object* v_x_190_, lean_object* v_x_191_, lean_object* v_x_192_, lean_object* v_x_193_){
_start:
{
size_t v_x_1768__boxed_194_; size_t v_x_1769__boxed_195_; lean_object* v_res_196_; 
v_x_1768__boxed_194_ = lean_unbox_usize(v_x_190_);
lean_dec(v_x_190_);
v_x_1769__boxed_195_ = lean_unbox_usize(v_x_191_);
lean_dec(v_x_191_);
v_res_196_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg(v_x_189_, v_x_1768__boxed_194_, v_x_1769__boxed_195_, v_x_192_, v_x_193_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0___redArg(lean_object* v_x_197_, lean_object* v_x_198_, lean_object* v_x_199_){
_start:
{
uint64_t v___x_200_; size_t v___x_201_; size_t v___x_202_; lean_object* v___x_203_; 
v___x_200_ = l_Lean_instHashableMVarId_hash(v_x_198_);
v___x_201_ = lean_uint64_to_usize(v___x_200_);
v___x_202_ = ((size_t)1ULL);
v___x_203_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg(v_x_197_, v___x_201_, v___x_202_, v_x_198_, v_x_199_);
return v___x_203_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg(lean_object* v_mvarId_204_, lean_object* v_val_205_, lean_object* v___y_206_){
_start:
{
lean_object* v___x_208_; lean_object* v_mctx_209_; lean_object* v_cache_210_; lean_object* v_zetaDeltaFVarIds_211_; lean_object* v_postponed_212_; lean_object* v_diag_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_243_; 
v___x_208_ = lean_st_ref_take(v___y_206_);
v_mctx_209_ = lean_ctor_get(v___x_208_, 0);
v_cache_210_ = lean_ctor_get(v___x_208_, 1);
v_zetaDeltaFVarIds_211_ = lean_ctor_get(v___x_208_, 2);
v_postponed_212_ = lean_ctor_get(v___x_208_, 3);
v_diag_213_ = lean_ctor_get(v___x_208_, 4);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_243_ == 0)
{
v___x_215_ = v___x_208_;
v_isShared_216_ = v_isSharedCheck_243_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_diag_213_);
lean_inc(v_postponed_212_);
lean_inc(v_zetaDeltaFVarIds_211_);
lean_inc(v_cache_210_);
lean_inc(v_mctx_209_);
lean_dec(v___x_208_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_243_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v_depth_217_; lean_object* v_levelAssignDepth_218_; lean_object* v_lmvarCounter_219_; lean_object* v_mvarCounter_220_; lean_object* v_lDecls_221_; lean_object* v_decls_222_; lean_object* v_userNames_223_; lean_object* v_lAssignment_224_; lean_object* v_eAssignment_225_; lean_object* v_dAssignment_226_; lean_object* v_instanceTypedMVars_227_; lean_object* v_synthNormMemo_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_242_; 
v_depth_217_ = lean_ctor_get(v_mctx_209_, 0);
v_levelAssignDepth_218_ = lean_ctor_get(v_mctx_209_, 1);
v_lmvarCounter_219_ = lean_ctor_get(v_mctx_209_, 2);
v_mvarCounter_220_ = lean_ctor_get(v_mctx_209_, 3);
v_lDecls_221_ = lean_ctor_get(v_mctx_209_, 4);
v_decls_222_ = lean_ctor_get(v_mctx_209_, 5);
v_userNames_223_ = lean_ctor_get(v_mctx_209_, 6);
v_lAssignment_224_ = lean_ctor_get(v_mctx_209_, 7);
v_eAssignment_225_ = lean_ctor_get(v_mctx_209_, 8);
v_dAssignment_226_ = lean_ctor_get(v_mctx_209_, 9);
v_instanceTypedMVars_227_ = lean_ctor_get(v_mctx_209_, 10);
v_synthNormMemo_228_ = lean_ctor_get(v_mctx_209_, 11);
v_isSharedCheck_242_ = !lean_is_exclusive(v_mctx_209_);
if (v_isSharedCheck_242_ == 0)
{
v___x_230_ = v_mctx_209_;
v_isShared_231_ = v_isSharedCheck_242_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_synthNormMemo_228_);
lean_inc(v_instanceTypedMVars_227_);
lean_inc(v_dAssignment_226_);
lean_inc(v_eAssignment_225_);
lean_inc(v_lAssignment_224_);
lean_inc(v_userNames_223_);
lean_inc(v_decls_222_);
lean_inc(v_lDecls_221_);
lean_inc(v_mvarCounter_220_);
lean_inc(v_lmvarCounter_219_);
lean_inc(v_levelAssignDepth_218_);
lean_inc(v_depth_217_);
lean_dec(v_mctx_209_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_242_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_235_; 
v___x_232_ = lean_box(0);
v___x_233_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0___redArg(v_eAssignment_225_, v_mvarId_204_, v_val_205_);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 8, v___x_233_);
v___x_235_ = v___x_230_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_depth_217_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v_levelAssignDepth_218_);
lean_ctor_set(v_reuseFailAlloc_241_, 2, v_lmvarCounter_219_);
lean_ctor_set(v_reuseFailAlloc_241_, 3, v_mvarCounter_220_);
lean_ctor_set(v_reuseFailAlloc_241_, 4, v_lDecls_221_);
lean_ctor_set(v_reuseFailAlloc_241_, 5, v_decls_222_);
lean_ctor_set(v_reuseFailAlloc_241_, 6, v_userNames_223_);
lean_ctor_set(v_reuseFailAlloc_241_, 7, v_lAssignment_224_);
lean_ctor_set(v_reuseFailAlloc_241_, 8, v___x_233_);
lean_ctor_set(v_reuseFailAlloc_241_, 9, v_dAssignment_226_);
lean_ctor_set(v_reuseFailAlloc_241_, 10, v_instanceTypedMVars_227_);
lean_ctor_set(v_reuseFailAlloc_241_, 11, v_synthNormMemo_228_);
v___x_235_ = v_reuseFailAlloc_241_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
lean_object* v___x_237_; 
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 0, v___x_235_);
v___x_237_ = v___x_215_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_235_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v_cache_210_);
lean_ctor_set(v_reuseFailAlloc_240_, 2, v_zetaDeltaFVarIds_211_);
lean_ctor_set(v_reuseFailAlloc_240_, 3, v_postponed_212_);
lean_ctor_set(v_reuseFailAlloc_240_, 4, v_diag_213_);
v___x_237_ = v_reuseFailAlloc_240_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = lean_st_ref_put(v___y_206_, v___x_237_);
v___x_239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_239_, 0, v___x_232_);
return v___x_239_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_204_ = stack[0].m_obj;
lean_object* v_val_205_ = stack[1].m_obj;
lean_object* v___y_206_ = stack[2].m_obj;
lean_object* v_res_244_;
v_res_244_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg(v_mvarId_204_, v_val_205_, v___y_206_);
stack->m_obj
 = v_res_244_;
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
lean_object* l_Lean_MVarId_replaceTargetEq___lam__0(lean_object* v_mvarId_255_, lean_object* v___x_256_, lean_object* v_targetNew_257_, lean_object* v_eqProof_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_){
_start:
{
lean_object* v___x_264_; 
lean_inc(v_mvarId_255_);
v___x_264_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_255_, v___x_256_, v___y_259_, v___y_260_, v___y_261_, v___y_262_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v___x_265_; 
lean_dec_ref_known(v___x_264_, 1);
lean_inc(v_mvarId_255_);
v___x_265_ = l_Lean_MVarId_getTag(v_mvarId_255_, v___y_259_, v___y_260_, v___y_261_, v___y_262_);
if (lean_obj_tag(v___x_265_) == 0)
{
lean_object* v_a_266_; lean_object* v___x_267_; 
v_a_266_ = lean_ctor_get(v___x_265_, 0);
lean_inc(v_a_266_);
lean_dec_ref_known(v___x_265_, 1);
lean_inc_ref(v_targetNew_257_);
v___x_267_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_targetNew_257_, v_a_266_, v___y_259_, v___y_260_, v___y_261_, v___y_262_);
if (lean_obj_tag(v___x_267_) == 0)
{
lean_object* v_a_268_; lean_object* v___x_269_; 
v_a_268_ = lean_ctor_get(v___x_267_, 0);
lean_inc(v_a_268_);
lean_dec_ref_known(v___x_267_, 1);
lean_inc(v_mvarId_255_);
v___x_269_ = l_Lean_MVarId_getType(v_mvarId_255_, v___y_259_, v___y_260_, v___y_261_, v___y_262_);
if (lean_obj_tag(v___x_269_) == 0)
{
lean_object* v_a_270_; lean_object* v___x_271_; 
v_a_270_ = lean_ctor_get(v___x_269_, 0);
lean_inc_n(v_a_270_, 2);
lean_dec_ref_known(v___x_269_, 1);
v___x_271_ = l_Lean_Meta_getLevel(v_a_270_, v___y_259_, v___y_260_, v___y_261_, v___y_262_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v_a_272_; lean_object* v___x_273_; 
v_a_272_ = lean_ctor_get(v___x_271_, 0);
lean_inc(v_a_272_);
lean_dec_ref_known(v___x_271_, 1);
lean_inc_ref(v_targetNew_257_);
lean_inc(v_a_270_);
v___x_273_ = l_Lean_Meta_mkEq(v_a_270_, v_targetNew_257_, v___y_259_, v___y_260_, v___y_261_, v___y_262_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v_a_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_295_; 
v_a_274_ = lean_ctor_get(v___x_273_, 0);
lean_inc(v_a_274_);
lean_dec_ref_known(v___x_273_, 1);
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
LEAN_EXPORT void l_Lean_MVarId_replaceTargetEq___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_255_ = stack[0].m_obj;
lean_object* v___x_256_ = stack[1].m_obj;
lean_object* v_targetNew_257_ = stack[2].m_obj;
lean_object* v_eqProof_258_ = stack[3].m_obj;
lean_object* v___y_259_ = stack[4].m_obj;
lean_object* v___y_260_ = stack[5].m_obj;
lean_object* v___y_261_ = stack[6].m_obj;
lean_object* v___y_262_ = stack[7].m_obj;
lean_object* v_res_345_;
v_res_345_ = l_Lean_MVarId_replaceTargetEq___lam__0(v_mvarId_255_, v___x_256_, v_targetNew_257_, v_eqProof_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_);
stack->m_obj
 = v_res_345_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetEq___lam__0___boxed(lean_object* v_mvarId_346_, lean_object* v___x_347_, lean_object* v_targetNew_348_, lean_object* v_eqProof_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lean_MVarId_replaceTargetEq___lam__0(v_mvarId_346_, v___x_347_, v_targetNew_348_, v_eqProof_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_);
lean_dec(v___y_353_);
lean_dec_ref(v___y_352_);
lean_dec(v___y_351_);
lean_dec_ref(v___y_350_);
return v_res_355_;
}
}
lean_object* l_Lean_MVarId_replaceTargetEq(lean_object* v_mvarId_359_, lean_object* v_targetNew_360_, lean_object* v_eqProof_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_){
_start:
{
lean_object* v___x_367_; lean_object* v___f_368_; lean_object* v___x_369_; 
v___x_367_ = ((lean_object*)(l_Lean_MVarId_replaceTargetEq___closed__1));
lean_inc(v_mvarId_359_);
v___f_368_ = lean_alloc_closure((void*)(l_Lean_MVarId_replaceTargetEq___lam__0___boxed), 9, 4);
lean_closure_set(v___f_368_, 0, v_mvarId_359_);
lean_closure_set(v___f_368_, 1, v___x_367_);
lean_closure_set(v___f_368_, 2, v_targetNew_360_);
lean_closure_set(v___f_368_, 3, v_eqProof_361_);
v___x_369_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_359_, v___f_368_, v_a_362_, v_a_363_, v_a_364_, v_a_365_);
return v___x_369_;
}
}
LEAN_EXPORT void l_Lean_MVarId_replaceTargetEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_359_ = stack[0].m_obj;
lean_object* v_targetNew_360_ = stack[1].m_obj;
lean_object* v_eqProof_361_ = stack[2].m_obj;
lean_object* v_a_362_ = stack[3].m_obj;
lean_object* v_a_363_ = stack[4].m_obj;
lean_object* v_a_364_ = stack[5].m_obj;
lean_object* v_a_365_ = stack[6].m_obj;
lean_object* v_res_370_;
v_res_370_ = l_Lean_MVarId_replaceTargetEq(v_mvarId_359_, v_targetNew_360_, v_eqProof_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_);
stack->m_obj
 = v_res_370_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetEq___boxed(lean_object* v_mvarId_371_, lean_object* v_targetNew_372_, lean_object* v_eqProof_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_MVarId_replaceTargetEq(v_mvarId_371_, v_targetNew_372_, v_eqProof_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_);
lean_dec(v_a_377_);
lean_dec_ref(v_a_376_);
lean_dec(v_a_375_);
lean_dec_ref(v_a_374_);
return v_res_379_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0(lean_object* v_mvarId_380_, lean_object* v_val_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg(v_mvarId_380_, v_val_381_, v___y_383_);
return v___x_387_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_380_ = stack[0].m_obj;
lean_object* v_val_381_ = stack[1].m_obj;
lean_object* v___y_382_ = stack[2].m_obj;
lean_object* v___y_383_ = stack[3].m_obj;
lean_object* v___y_384_ = stack[4].m_obj;
lean_object* v___y_385_ = stack[5].m_obj;
lean_object* v_res_388_;
v_res_388_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0(v_mvarId_380_, v_val_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_);
stack->m_obj
 = v_res_388_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___boxed(lean_object* v_mvarId_389_, lean_object* v_val_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0(v_mvarId_389_, v_val_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0(lean_object* v_00_u03b2_397_, lean_object* v_x_398_, lean_object* v_x_399_, lean_object* v_x_400_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0___redArg(v_x_398_, v_x_399_, v_x_400_);
return v___x_401_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_402_, lean_object* v_x_403_, size_t v_x_404_, size_t v_x_405_, lean_object* v_x_406_, lean_object* v_x_407_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg(v_x_403_, v_x_404_, v_x_405_, v_x_406_, v_x_407_);
return v___x_408_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_403_ = stack[1].m_obj;
size_t v_x_404_ = stack[2].m_num;
size_t v_x_405_ = stack[3].m_num;
lean_object* v_x_406_ = stack[4].m_obj;
lean_object* v_x_407_ = stack[5].m_obj;
lean_object* v_res_409_;
v_res_409_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2(lean_box(0), v_x_403_, v_x_404_, v_x_405_, v_x_406_, v_x_407_);
stack->m_obj
 = v_res_409_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_410_, lean_object* v_x_411_, lean_object* v_x_412_, lean_object* v_x_413_, lean_object* v_x_414_, lean_object* v_x_415_){
_start:
{
size_t v_x_2454__boxed_416_; size_t v_x_2455__boxed_417_; lean_object* v_res_418_; 
v_x_2454__boxed_416_ = lean_unbox_usize(v_x_412_);
lean_dec(v_x_412_);
v_x_2455__boxed_417_ = lean_unbox_usize(v_x_413_);
lean_dec(v_x_413_);
v_res_418_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2(v_00_u03b2_410_, v_x_411_, v_x_2454__boxed_416_, v_x_2455__boxed_417_, v_x_414_, v_x_415_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_419_, lean_object* v_n_420_, lean_object* v_k_421_, lean_object* v_v_422_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3___redArg(v_n_420_, v_k_421_, v_v_422_);
return v___x_423_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_424_, size_t v_depth_425_, lean_object* v_keys_426_, lean_object* v_vals_427_, lean_object* v_heq_428_, lean_object* v_i_429_, lean_object* v_entries_430_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_425_, v_keys_426_, v_vals_427_, v_i_429_, v_entries_430_);
return v___x_431_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
size_t v_depth_425_ = stack[1].m_num;
lean_object* v_keys_426_ = stack[2].m_obj;
lean_object* v_vals_427_ = stack[3].m_obj;
lean_object* v_i_429_ = stack[5].m_obj;
lean_object* v_entries_430_ = stack[6].m_obj;
lean_object* v_res_432_;
v_res_432_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4(lean_box(0), v_depth_425_, v_keys_426_, v_vals_427_, lean_box(0), v_i_429_, v_entries_430_);
stack->m_obj
 = v_res_432_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_433_, lean_object* v_depth_434_, lean_object* v_keys_435_, lean_object* v_vals_436_, lean_object* v_heq_437_, lean_object* v_i_438_, lean_object* v_entries_439_){
_start:
{
size_t v_depth_boxed_440_; lean_object* v_res_441_; 
v_depth_boxed_440_ = lean_unbox_usize(v_depth_434_);
lean_dec(v_depth_434_);
v_res_441_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_433_, v_depth_boxed_440_, v_keys_435_, v_vals_436_, v_heq_437_, v_i_438_, v_entries_439_);
lean_dec_ref(v_vals_436_);
lean_dec_ref(v_keys_435_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_442_, lean_object* v_x_443_, lean_object* v_x_444_, lean_object* v_x_445_, lean_object* v_x_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_x_443_, v_x_444_, v_x_445_, v_x_446_);
return v___x_447_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(lean_object* v_e_448_, lean_object* v___y_449_){
_start:
{
uint8_t v___x_451_; 
v___x_451_ = l_Lean_Expr_hasMVar(v_e_448_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; 
v___x_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_452_, 0, v_e_448_);
return v___x_452_;
}
else
{
lean_object* v___x_453_; lean_object* v_mctx_454_; lean_object* v___x_455_; lean_object* v_fst_456_; lean_object* v_snd_457_; lean_object* v___x_458_; lean_object* v_cache_459_; lean_object* v_zetaDeltaFVarIds_460_; lean_object* v_postponed_461_; lean_object* v_diag_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_471_; 
v___x_453_ = lean_st_ref_get(v___y_449_);
v_mctx_454_ = lean_ctor_get(v___x_453_, 0);
lean_inc_ref(v_mctx_454_);
lean_dec(v___x_453_);
v___x_455_ = l_Lean_instantiateMVarsCore(v_mctx_454_, v_e_448_);
v_fst_456_ = lean_ctor_get(v___x_455_, 0);
lean_inc(v_fst_456_);
v_snd_457_ = lean_ctor_get(v___x_455_, 1);
lean_inc(v_snd_457_);
lean_dec_ref(v___x_455_);
v___x_458_ = lean_st_ref_take(v___y_449_);
v_cache_459_ = lean_ctor_get(v___x_458_, 1);
v_zetaDeltaFVarIds_460_ = lean_ctor_get(v___x_458_, 2);
v_postponed_461_ = lean_ctor_get(v___x_458_, 3);
v_diag_462_ = lean_ctor_get(v___x_458_, 4);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_471_ == 0)
{
lean_object* v_unused_472_; 
v_unused_472_ = lean_ctor_get(v___x_458_, 0);
lean_dec(v_unused_472_);
v___x_464_ = v___x_458_;
v_isShared_465_ = v_isSharedCheck_471_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_diag_462_);
lean_inc(v_postponed_461_);
lean_inc(v_zetaDeltaFVarIds_460_);
lean_inc(v_cache_459_);
lean_dec(v___x_458_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_471_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_467_; 
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 0, v_snd_457_);
v___x_467_ = v___x_464_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_snd_457_);
lean_ctor_set(v_reuseFailAlloc_470_, 1, v_cache_459_);
lean_ctor_set(v_reuseFailAlloc_470_, 2, v_zetaDeltaFVarIds_460_);
lean_ctor_set(v_reuseFailAlloc_470_, 3, v_postponed_461_);
lean_ctor_set(v_reuseFailAlloc_470_, 4, v_diag_462_);
v___x_467_ = v_reuseFailAlloc_470_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = lean_st_ref_put(v___y_449_, v___x_467_);
v___x_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_469_, 0, v_fst_456_);
return v___x_469_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_448_ = stack[0].m_obj;
lean_object* v___y_449_ = stack[1].m_obj;
lean_object* v_res_473_;
v_res_473_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(v_e_448_, v___y_449_);
stack->m_obj
 = v_res_473_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg___boxed(lean_object* v_e_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(v_e_474_, v___y_475_);
lean_dec(v___y_475_);
return v_res_477_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0(lean_object* v_e_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(v_e_478_, v___y_480_);
return v___x_484_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_478_ = stack[0].m_obj;
lean_object* v___y_479_ = stack[1].m_obj;
lean_object* v___y_480_ = stack[2].m_obj;
lean_object* v___y_481_ = stack[3].m_obj;
lean_object* v___y_482_ = stack[4].m_obj;
lean_object* v_res_485_;
v_res_485_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0(v_e_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_);
stack->m_obj
 = v_res_485_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___boxed(lean_object* v_e_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0(v_e_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_);
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
return v_res_492_;
}
}
lean_object* l_Lean_MVarId_replaceTargetDefEq___lam__0(lean_object* v_mvarId_493_, lean_object* v___x_494_, lean_object* v_targetNew_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
lean_object* v___x_501_; 
lean_inc(v_mvarId_493_);
v___x_501_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_493_, v___x_494_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v___x_502_; 
lean_dec_ref_known(v___x_501_, 1);
lean_inc(v_mvarId_493_);
v___x_502_ = l_Lean_MVarId_getType(v_mvarId_493_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_573_; 
v_a_503_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_573_ == 0)
{
v___x_505_ = v___x_502_;
v_isShared_506_ = v_isSharedCheck_573_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v___x_502_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_573_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
uint8_t v___x_507_; 
v___x_507_ = lean_expr_equal(v_a_503_, v_targetNew_495_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; lean_object* v_a_509_; lean_object* v___x_510_; lean_object* v_a_511_; uint8_t v___x_512_; 
lean_del_object(v___x_505_);
v___x_508_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(v_a_503_, v___y_497_);
v_a_509_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_a_509_);
lean_dec_ref(v___x_508_);
v___x_510_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(v_targetNew_495_, v___y_497_);
v_a_511_ = lean_ctor_get(v___x_510_, 0);
lean_inc(v_a_511_);
lean_dec_ref(v___x_510_);
v___x_512_ = lean_expr_equal(v_a_509_, v_a_511_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; 
lean_inc(v_mvarId_493_);
v___x_513_ = l_Lean_MVarId_getTag(v_mvarId_493_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; lean_object* v___x_515_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc(v_a_514_);
lean_dec_ref_known(v___x_513_, 1);
v___x_515_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_511_, v_a_514_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v_a_516_; lean_object* v___x_517_; 
v_a_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc_n(v_a_516_, 2);
lean_dec_ref_known(v___x_515_, 1);
v___x_517_ = l_Lean_Meta_mkExpectedTypeHint(v_a_516_, v_a_509_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v_a_518_; lean_object* v___x_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_527_; 
v_a_518_ = lean_ctor_get(v___x_517_, 0);
lean_inc(v_a_518_);
lean_dec_ref_known(v___x_517_, 1);
v___x_519_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg(v_mvarId_493_, v_a_518_, v___y_497_);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_527_ == 0)
{
lean_object* v_unused_528_; 
v_unused_528_ = lean_ctor_get(v___x_519_, 0);
lean_dec(v_unused_528_);
v___x_521_ = v___x_519_;
v_isShared_522_ = v_isSharedCheck_527_;
goto v_resetjp_520_;
}
else
{
lean_dec(v___x_519_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_527_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_523_; lean_object* v___x_525_; 
v___x_523_ = l_Lean_Expr_mvarId_x21(v_a_516_);
lean_dec(v_a_516_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_523_);
v___x_525_ = v___x_521_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_523_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
else
{
lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_536_; 
lean_dec(v_a_516_);
lean_dec(v_mvarId_493_);
v_a_529_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_536_ == 0)
{
v___x_531_ = v___x_517_;
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v___x_517_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_534_; 
if (v_isShared_532_ == 0)
{
v___x_534_ = v___x_531_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_a_529_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
else
{
lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_544_; 
lean_dec(v_a_509_);
lean_dec(v_mvarId_493_);
v_a_537_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_544_ == 0)
{
v___x_539_ = v___x_515_;
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_a_537_);
lean_dec(v___x_515_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_542_; 
if (v_isShared_540_ == 0)
{
v___x_542_ = v___x_539_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_a_537_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
}
else
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
lean_dec(v_a_511_);
lean_dec(v_a_509_);
lean_dec(v_mvarId_493_);
v_a_545_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v___x_513_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_513_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_a_545_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
else
{
lean_object* v___x_553_; 
lean_dec(v_a_511_);
lean_inc(v_mvarId_493_);
v___x_553_ = l_Lean_MVarId_setType___redArg(v_mvarId_493_, v_a_509_, v___y_497_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_560_; 
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_560_ == 0)
{
lean_object* v_unused_561_; 
v_unused_561_ = lean_ctor_get(v___x_553_, 0);
lean_dec(v_unused_561_);
v___x_555_ = v___x_553_;
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
else
{
lean_dec(v___x_553_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_558_; 
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 0, v_mvarId_493_);
v___x_558_ = v___x_555_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_mvarId_493_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
else
{
lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_569_; 
lean_dec(v_mvarId_493_);
v_a_562_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_569_ == 0)
{
v___x_564_ = v___x_553_;
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v___x_553_);
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
}
else
{
lean_object* v___x_571_; 
lean_dec(v_a_503_);
lean_dec_ref(v_targetNew_495_);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 0, v_mvarId_493_);
v___x_571_ = v___x_505_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_mvarId_493_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
else
{
lean_object* v_a_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_581_; 
lean_dec_ref(v_targetNew_495_);
lean_dec(v_mvarId_493_);
v_a_574_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_581_ == 0)
{
v___x_576_ = v___x_502_;
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_a_574_);
lean_dec(v___x_502_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_579_; 
if (v_isShared_577_ == 0)
{
v___x_579_ = v___x_576_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_a_574_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
}
else
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_589_; 
lean_dec_ref(v_targetNew_495_);
lean_dec(v_mvarId_493_);
v_a_582_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_589_ == 0)
{
v___x_584_ = v___x_501_;
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_501_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
if (v_isShared_585_ == 0)
{
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_a_582_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_replaceTargetDefEq___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_493_ = stack[0].m_obj;
lean_object* v___x_494_ = stack[1].m_obj;
lean_object* v_targetNew_495_ = stack[2].m_obj;
lean_object* v___y_496_ = stack[3].m_obj;
lean_object* v___y_497_ = stack[4].m_obj;
lean_object* v___y_498_ = stack[5].m_obj;
lean_object* v___y_499_ = stack[6].m_obj;
lean_object* v_res_590_;
v_res_590_ = l_Lean_MVarId_replaceTargetDefEq___lam__0(v_mvarId_493_, v___x_494_, v_targetNew_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
stack->m_obj
 = v_res_590_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEq___lam__0___boxed(lean_object* v_mvarId_591_, lean_object* v___x_592_, lean_object* v_targetNew_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Lean_MVarId_replaceTargetDefEq___lam__0(v_mvarId_591_, v___x_592_, v_targetNew_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
lean_dec(v___y_595_);
lean_dec_ref(v___y_594_);
return v_res_599_;
}
}
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object* v_mvarId_603_, lean_object* v_targetNew_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_){
_start:
{
lean_object* v___x_610_; lean_object* v___f_611_; lean_object* v___x_612_; 
v___x_610_ = ((lean_object*)(l_Lean_MVarId_replaceTargetDefEq___closed__1));
lean_inc(v_mvarId_603_);
v___f_611_ = lean_alloc_closure((void*)(l_Lean_MVarId_replaceTargetDefEq___lam__0___boxed), 8, 3);
lean_closure_set(v___f_611_, 0, v_mvarId_603_);
lean_closure_set(v___f_611_, 1, v___x_610_);
lean_closure_set(v___f_611_, 2, v_targetNew_604_);
v___x_612_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_603_, v___f_611_, v_a_605_, v_a_606_, v_a_607_, v_a_608_);
return v___x_612_;
}
}
LEAN_EXPORT void l_Lean_MVarId_replaceTargetDefEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_603_ = stack[0].m_obj;
lean_object* v_targetNew_604_ = stack[1].m_obj;
lean_object* v_a_605_ = stack[2].m_obj;
lean_object* v_a_606_ = stack[3].m_obj;
lean_object* v_a_607_ = stack[4].m_obj;
lean_object* v_a_608_ = stack[5].m_obj;
lean_object* v_res_613_;
v_res_613_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_603_, v_targetNew_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_);
stack->m_obj
 = v_res_613_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEq___boxed(lean_object* v_mvarId_614_, lean_object* v_targetNew_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_614_, v_targetNew_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_);
lean_dec(v_a_619_);
lean_dec_ref(v_a_618_);
lean_dec(v_a_617_);
lean_dec_ref(v_a_616_);
return v_res_621_;
}
}
lean_object* l_Lean_MVarId_replace___lam__0(lean_object* v_mvarId_622_, lean_object* v_fvarId_623_, lean_object* v_val_624_, lean_object* v_userName_x3f_625_, lean_object* v_type_x3f_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
lean_object* v___y_633_; lean_object* v_a_634_; lean_object* v_a_665_; 
if (lean_obj_tag(v_type_x3f_626_) == 0)
{
lean_object* v___x_678_; 
lean_inc(v___y_630_);
lean_inc_ref(v___y_629_);
lean_inc(v___y_628_);
lean_inc_ref(v___y_627_);
lean_inc_ref(v_val_624_);
v___x_678_ = lean_infer_type(v_val_624_, v___y_627_, v___y_628_, v___y_629_, v___y_630_);
if (lean_obj_tag(v___x_678_) == 0)
{
lean_object* v_a_679_; 
v_a_679_ = lean_ctor_get(v___x_678_, 0);
lean_inc(v_a_679_);
lean_dec_ref_known(v___x_678_, 1);
v_a_665_ = v_a_679_;
goto v___jp_664_;
}
else
{
lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_687_; 
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
lean_dec(v_userName_x3f_625_);
lean_dec_ref(v_val_624_);
lean_dec(v_fvarId_623_);
lean_dec(v_mvarId_622_);
v_a_680_ = lean_ctor_get(v___x_678_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_687_ == 0)
{
v___x_682_ = v___x_678_;
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_dec(v___x_678_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_685_; 
if (v_isShared_683_ == 0)
{
v___x_685_ = v___x_682_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_a_680_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
}
else
{
lean_object* v_val_688_; 
v_val_688_ = lean_ctor_get(v_type_x3f_626_, 0);
lean_inc(v_val_688_);
lean_dec_ref_known(v_type_x3f_626_, 1);
v_a_665_ = v_val_688_;
goto v___jp_664_;
}
v___jp_632_:
{
lean_object* v___x_635_; 
lean_inc(v_fvarId_623_);
v___x_635_ = l_Lean_MVarId_assertAfter_x27(v_mvarId_622_, v_fvarId_623_, v_a_634_, v___y_633_, v_val_624_, v___y_627_, v___y_628_, v___y_629_, v___y_630_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; lean_object* v_fvarId_637_; lean_object* v_mvarId_638_; lean_object* v_subst_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_663_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_a_636_);
lean_dec_ref_known(v___x_635_, 1);
v_fvarId_637_ = lean_ctor_get(v_a_636_, 0);
v_mvarId_638_ = lean_ctor_get(v_a_636_, 1);
v_subst_639_ = lean_ctor_get(v_a_636_, 2);
v_isSharedCheck_663_ = !lean_is_exclusive(v_a_636_);
if (v_isSharedCheck_663_ == 0)
{
v___x_641_ = v_a_636_;
v_isShared_642_ = v_isSharedCheck_663_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_subst_639_);
lean_inc(v_mvarId_638_);
lean_inc(v_fvarId_637_);
lean_dec(v_a_636_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_663_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_643_; 
v___x_643_ = l_Lean_MVarId_tryClear(v_mvarId_638_, v_fvarId_623_, v___y_627_, v___y_628_, v___y_629_, v___y_630_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v_a_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_654_; 
v_a_644_ = lean_ctor_get(v___x_643_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_654_ == 0)
{
v___x_646_ = v___x_643_;
v_isShared_647_ = v_isSharedCheck_654_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_a_644_);
lean_dec(v___x_643_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_654_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_649_; 
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 1, v_a_644_);
v___x_649_ = v___x_641_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_fvarId_637_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v_a_644_);
lean_ctor_set(v_reuseFailAlloc_653_, 2, v_subst_639_);
v___x_649_ = v_reuseFailAlloc_653_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
lean_object* v___x_651_; 
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 0, v___x_649_);
v___x_651_ = v___x_646_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_649_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
else
{
lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_662_; 
lean_del_object(v___x_641_);
lean_dec(v_subst_639_);
lean_dec(v_fvarId_637_);
v_a_655_ = lean_ctor_get(v___x_643_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_662_ == 0)
{
v___x_657_ = v___x_643_;
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_643_);
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
}
else
{
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
lean_dec(v_fvarId_623_);
return v___x_635_;
}
}
v___jp_664_:
{
if (lean_obj_tag(v_userName_x3f_625_) == 0)
{
lean_object* v___x_666_; 
lean_inc(v_fvarId_623_);
v___x_666_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_623_, v___y_627_, v___y_629_, v___y_630_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_a_667_; lean_object* v___x_668_; 
v_a_667_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_a_667_);
lean_dec_ref_known(v___x_666_, 1);
v___x_668_ = l_Lean_LocalDecl_userName(v_a_667_);
lean_dec(v_a_667_);
v___y_633_ = v_a_665_;
v_a_634_ = v___x_668_;
goto v___jp_632_;
}
else
{
lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_676_; 
lean_dec_ref(v_a_665_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
lean_dec_ref(v_val_624_);
lean_dec(v_fvarId_623_);
lean_dec(v_mvarId_622_);
v_a_669_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_676_ == 0)
{
v___x_671_ = v___x_666_;
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_666_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_674_; 
if (v_isShared_672_ == 0)
{
v___x_674_ = v___x_671_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_a_669_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
}
else
{
lean_object* v_val_677_; 
v_val_677_ = lean_ctor_get(v_userName_x3f_625_, 0);
lean_inc(v_val_677_);
lean_dec_ref_known(v_userName_x3f_625_, 1);
v___y_633_ = v_a_665_;
v_a_634_ = v_val_677_;
goto v___jp_632_;
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_replace___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_622_ = stack[0].m_obj;
lean_object* v_fvarId_623_ = stack[1].m_obj;
lean_object* v_val_624_ = stack[2].m_obj;
lean_object* v_userName_x3f_625_ = stack[3].m_obj;
lean_object* v_type_x3f_626_ = stack[4].m_obj;
lean_object* v___y_627_ = stack[5].m_obj;
lean_object* v___y_628_ = stack[6].m_obj;
lean_object* v___y_629_ = stack[7].m_obj;
lean_object* v___y_630_ = stack[8].m_obj;
lean_object* v_res_689_;
v_res_689_ = l_Lean_MVarId_replace___lam__0(v_mvarId_622_, v_fvarId_623_, v_val_624_, v_userName_x3f_625_, v_type_x3f_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_);
stack->m_obj
 = v_res_689_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replace___lam__0___boxed(lean_object* v_mvarId_690_, lean_object* v_fvarId_691_, lean_object* v_val_692_, lean_object* v_userName_x3f_693_, lean_object* v_type_x3f_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_MVarId_replace___lam__0(v_mvarId_690_, v_fvarId_691_, v_val_692_, v_userName_x3f_693_, v_type_x3f_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
return v_res_700_;
}
}
lean_object* l_Lean_MVarId_replace(lean_object* v_mvarId_701_, lean_object* v_fvarId_702_, lean_object* v_val_703_, lean_object* v_type_x3f_704_, lean_object* v_userName_x3f_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_){
_start:
{
lean_object* v___f_711_; lean_object* v___x_712_; 
lean_inc(v_mvarId_701_);
v___f_711_ = lean_alloc_closure((void*)(l_Lean_MVarId_replace___lam__0___boxed), 10, 5);
lean_closure_set(v___f_711_, 0, v_mvarId_701_);
lean_closure_set(v___f_711_, 1, v_fvarId_702_);
lean_closure_set(v___f_711_, 2, v_val_703_);
lean_closure_set(v___f_711_, 3, v_userName_x3f_705_);
lean_closure_set(v___f_711_, 4, v_type_x3f_704_);
v___x_712_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_701_, v___f_711_, v_a_706_, v_a_707_, v_a_708_, v_a_709_);
return v___x_712_;
}
}
LEAN_EXPORT void l_Lean_MVarId_replace_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_701_ = stack[0].m_obj;
lean_object* v_fvarId_702_ = stack[1].m_obj;
lean_object* v_val_703_ = stack[2].m_obj;
lean_object* v_type_x3f_704_ = stack[3].m_obj;
lean_object* v_userName_x3f_705_ = stack[4].m_obj;
lean_object* v_a_706_ = stack[5].m_obj;
lean_object* v_a_707_ = stack[6].m_obj;
lean_object* v_a_708_ = stack[7].m_obj;
lean_object* v_a_709_ = stack[8].m_obj;
lean_object* v_res_713_;
v_res_713_ = l_Lean_MVarId_replace(v_mvarId_701_, v_fvarId_702_, v_val_703_, v_type_x3f_704_, v_userName_x3f_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_);
stack->m_obj
 = v_res_713_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replace___boxed(lean_object* v_mvarId_714_, lean_object* v_fvarId_715_, lean_object* v_val_716_, lean_object* v_type_x3f_717_, lean_object* v_userName_x3f_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_MVarId_replace(v_mvarId_714_, v_fvarId_715_, v_val_716_, v_type_x3f_717_, v_userName_x3f_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_);
lean_dec(v_a_722_);
lean_dec_ref(v_a_721_);
lean_dec(v_a_720_);
lean_dec_ref(v_a_719_);
return v_res_724_;
}
}
lean_object* l_Lean_MVarId_replaceLocalDecl___lam__0(lean_object* v_eqProof_725_, lean_object* v___x_726_, lean_object* v_typeNew_727_, lean_object* v_mvarId_728_, lean_object* v_fvarId_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_Lean_Meta_mkEqMP(v_eqProof_725_, v___x_726_, v___y_730_, v___y_731_, v___y_732_, v___y_733_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
lean_inc(v_a_736_);
lean_dec_ref_known(v___x_735_, 1);
v___x_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_737_, 0, v_typeNew_727_);
v___x_738_ = lean_box(0);
v___x_739_ = l_Lean_MVarId_replace(v_mvarId_728_, v_fvarId_729_, v_a_736_, v___x_737_, v___x_738_, v___y_730_, v___y_731_, v___y_732_, v___y_733_);
return v___x_739_;
}
else
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_747_; 
lean_dec(v_fvarId_729_);
lean_dec(v_mvarId_728_);
lean_dec_ref(v_typeNew_727_);
v_a_740_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_747_ == 0)
{
v___x_742_ = v___x_735_;
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_735_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_745_; 
if (v_isShared_743_ == 0)
{
v___x_745_ = v___x_742_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_a_740_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_replaceLocalDecl___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_eqProof_725_ = stack[0].m_obj;
lean_object* v___x_726_ = stack[1].m_obj;
lean_object* v_typeNew_727_ = stack[2].m_obj;
lean_object* v_mvarId_728_ = stack[3].m_obj;
lean_object* v_fvarId_729_ = stack[4].m_obj;
lean_object* v___y_730_ = stack[5].m_obj;
lean_object* v___y_731_ = stack[6].m_obj;
lean_object* v___y_732_ = stack[7].m_obj;
lean_object* v___y_733_ = stack[8].m_obj;
lean_object* v_res_748_;
v_res_748_ = l_Lean_MVarId_replaceLocalDecl___lam__0(v_eqProof_725_, v___x_726_, v_typeNew_727_, v_mvarId_728_, v_fvarId_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_);
stack->m_obj
 = v_res_748_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDecl___lam__0___boxed(lean_object* v_eqProof_749_, lean_object* v___x_750_, lean_object* v_typeNew_751_, lean_object* v_mvarId_752_, lean_object* v_fvarId_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_MVarId_replaceLocalDecl___lam__0(v_eqProof_749_, v___x_750_, v_typeNew_751_, v_mvarId_752_, v_fvarId_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
return v_res_759_;
}
}
static lean_object* _init_l_Lean_MVarId_replaceLocalDecl___closed__0(void){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l_instMonadEIO___redArg();
return v___x_760_;
}
}
static lean_object* _init_l_Lean_MVarId_replaceLocalDecl___closed__1(void){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = lean_obj_once(&l_Lean_MVarId_replaceLocalDecl___closed__0, &l_Lean_MVarId_replaceLocalDecl___closed__0_once, _init_l_Lean_MVarId_replaceLocalDecl___closed__0);
v___x_762_ = l_StateRefT_x27_instMonad___redArg(v___x_761_);
return v___x_762_;
}
}
lean_object* l_Lean_MVarId_replaceLocalDecl(lean_object* v_mvarId_767_, lean_object* v_fvarId_768_, lean_object* v_typeNew_769_, lean_object* v_eqProof_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_){
_start:
{
lean_object* v___x_776_; lean_object* v_toApplicative_777_; lean_object* v_toFunctor_778_; lean_object* v_toSeq_779_; lean_object* v_toSeqLeft_780_; lean_object* v_toSeqRight_781_; lean_object* v___f_782_; lean_object* v___f_783_; lean_object* v___f_784_; lean_object* v___f_785_; lean_object* v___x_786_; lean_object* v___f_787_; lean_object* v___f_788_; lean_object* v___f_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v_toApplicative_795_; lean_object* v_toFunctor_796_; lean_object* v_toSeq_797_; lean_object* v_toSeqLeft_798_; lean_object* v_toSeqRight_799_; lean_object* v___f_800_; lean_object* v___f_801_; lean_object* v___x_802_; lean_object* v___f_803_; lean_object* v___f_804_; lean_object* v___f_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v_toApplicative_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_840_; 
v___x_776_ = lean_obj_once(&l_Lean_MVarId_replaceLocalDecl___closed__1, &l_Lean_MVarId_replaceLocalDecl___closed__1_once, _init_l_Lean_MVarId_replaceLocalDecl___closed__1);
v_toApplicative_777_ = lean_ctor_get(v___x_776_, 0);
v_toFunctor_778_ = lean_ctor_get(v_toApplicative_777_, 0);
v_toSeq_779_ = lean_ctor_get(v_toApplicative_777_, 2);
v_toSeqLeft_780_ = lean_ctor_get(v_toApplicative_777_, 3);
v_toSeqRight_781_ = lean_ctor_get(v_toApplicative_777_, 4);
v___f_782_ = ((lean_object*)(l_Lean_MVarId_replaceLocalDecl___closed__2));
v___f_783_ = ((lean_object*)(l_Lean_MVarId_replaceLocalDecl___closed__3));
lean_inc_ref_n(v_toFunctor_778_, 2);
v___f_784_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_784_, 0, v_toFunctor_778_);
v___f_785_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_785_, 0, v_toFunctor_778_);
v___x_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_786_, 0, v___f_784_);
lean_ctor_set(v___x_786_, 1, v___f_785_);
lean_inc(v_toSeqRight_781_);
v___f_787_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_787_, 0, v_toSeqRight_781_);
lean_inc(v_toSeqLeft_780_);
v___f_788_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_788_, 0, v_toSeqLeft_780_);
lean_inc(v_toSeq_779_);
v___f_789_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_789_, 0, v_toSeq_779_);
v___x_790_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_790_, 0, v___x_786_);
lean_ctor_set(v___x_790_, 1, v___f_782_);
lean_ctor_set(v___x_790_, 2, v___f_789_);
lean_ctor_set(v___x_790_, 3, v___f_788_);
lean_ctor_set(v___x_790_, 4, v___f_787_);
v___x_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
lean_ctor_set(v___x_791_, 1, v___f_783_);
v___x_792_ = l_StateRefT_x27_instMonad___redArg(v___x_791_);
v___x_793_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_793_, 0, lean_box(0));
lean_closure_set(v___x_793_, 1, lean_box(0));
lean_closure_set(v___x_793_, 2, v___x_792_);
v___x_794_ = l_instMonadControlTOfPure___redArg(v___x_793_);
v_toApplicative_795_ = lean_ctor_get(v___x_776_, 0);
v_toFunctor_796_ = lean_ctor_get(v_toApplicative_795_, 0);
v_toSeq_797_ = lean_ctor_get(v_toApplicative_795_, 2);
v_toSeqLeft_798_ = lean_ctor_get(v_toApplicative_795_, 3);
v_toSeqRight_799_ = lean_ctor_get(v_toApplicative_795_, 4);
lean_inc_ref_n(v_toFunctor_796_, 2);
v___f_800_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_800_, 0, v_toFunctor_796_);
v___f_801_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_801_, 0, v_toFunctor_796_);
v___x_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_802_, 0, v___f_800_);
lean_ctor_set(v___x_802_, 1, v___f_801_);
lean_inc(v_toSeqRight_799_);
v___f_803_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_803_, 0, v_toSeqRight_799_);
lean_inc(v_toSeqLeft_798_);
v___f_804_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_804_, 0, v_toSeqLeft_798_);
lean_inc(v_toSeq_797_);
v___f_805_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_805_, 0, v_toSeq_797_);
v___x_806_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_806_, 0, v___x_802_);
lean_ctor_set(v___x_806_, 1, v___f_782_);
lean_ctor_set(v___x_806_, 2, v___f_805_);
lean_ctor_set(v___x_806_, 3, v___f_804_);
lean_ctor_set(v___x_806_, 4, v___f_803_);
v___x_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
lean_ctor_set(v___x_807_, 1, v___f_783_);
v___x_808_ = l_StateRefT_x27_instMonad___redArg(v___x_807_);
v_toApplicative_809_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_840_ == 0)
{
lean_object* v_unused_841_; 
v_unused_841_ = lean_ctor_get(v___x_808_, 1);
lean_dec(v_unused_841_);
v___x_811_ = v___x_808_;
v_isShared_812_ = v_isSharedCheck_840_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_toApplicative_809_);
lean_dec(v___x_808_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_840_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v_toFunctor_813_; lean_object* v_toSeq_814_; lean_object* v_toSeqLeft_815_; lean_object* v_toSeqRight_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_838_; 
v_toFunctor_813_ = lean_ctor_get(v_toApplicative_809_, 0);
v_toSeq_814_ = lean_ctor_get(v_toApplicative_809_, 2);
v_toSeqLeft_815_ = lean_ctor_get(v_toApplicative_809_, 3);
v_toSeqRight_816_ = lean_ctor_get(v_toApplicative_809_, 4);
v_isSharedCheck_838_ = !lean_is_exclusive(v_toApplicative_809_);
if (v_isSharedCheck_838_ == 0)
{
lean_object* v_unused_839_; 
v_unused_839_ = lean_ctor_get(v_toApplicative_809_, 1);
lean_dec(v_unused_839_);
v___x_818_ = v_toApplicative_809_;
v_isShared_819_ = v_isSharedCheck_838_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_toSeqRight_816_);
lean_inc(v_toSeqLeft_815_);
lean_inc(v_toSeq_814_);
lean_inc(v_toFunctor_813_);
lean_dec(v_toApplicative_809_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_838_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___f_820_; lean_object* v___f_821_; lean_object* v___f_822_; lean_object* v___f_823_; lean_object* v___x_824_; lean_object* v___f_825_; lean_object* v___f_826_; lean_object* v___f_827_; lean_object* v___x_829_; 
v___f_820_ = ((lean_object*)(l_Lean_MVarId_replaceLocalDecl___closed__4));
v___f_821_ = ((lean_object*)(l_Lean_MVarId_replaceLocalDecl___closed__5));
lean_inc_ref(v_toFunctor_813_);
v___f_822_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_822_, 0, v_toFunctor_813_);
v___f_823_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_823_, 0, v_toFunctor_813_);
v___x_824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_824_, 0, v___f_822_);
lean_ctor_set(v___x_824_, 1, v___f_823_);
v___f_825_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_825_, 0, v_toSeqRight_816_);
v___f_826_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_826_, 0, v_toSeqLeft_815_);
v___f_827_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_827_, 0, v_toSeq_814_);
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 4, v___f_825_);
lean_ctor_set(v___x_818_, 3, v___f_826_);
lean_ctor_set(v___x_818_, 2, v___f_827_);
lean_ctor_set(v___x_818_, 1, v___f_820_);
lean_ctor_set(v___x_818_, 0, v___x_824_);
v___x_829_ = v___x_818_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v___x_824_);
lean_ctor_set(v_reuseFailAlloc_837_, 1, v___f_820_);
lean_ctor_set(v_reuseFailAlloc_837_, 2, v___f_827_);
lean_ctor_set(v_reuseFailAlloc_837_, 3, v___f_826_);
lean_ctor_set(v_reuseFailAlloc_837_, 4, v___f_825_);
v___x_829_ = v_reuseFailAlloc_837_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
lean_object* v___x_831_; 
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 1, v___f_821_);
lean_ctor_set(v___x_811_, 0, v___x_829_);
v___x_831_ = v___x_811_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_829_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v___f_821_);
v___x_831_ = v_reuseFailAlloc_836_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
lean_object* v___x_832_; lean_object* v___f_833_; lean_object* v___x_124__overap_834_; lean_object* v___x_835_; 
lean_inc(v_fvarId_768_);
v___x_832_ = l_Lean_mkFVar(v_fvarId_768_);
lean_inc(v_mvarId_767_);
v___f_833_ = lean_alloc_closure((void*)(l_Lean_MVarId_replaceLocalDecl___lam__0___boxed), 10, 5);
lean_closure_set(v___f_833_, 0, v_eqProof_770_);
lean_closure_set(v___f_833_, 1, v___x_832_);
lean_closure_set(v___f_833_, 2, v_typeNew_769_);
lean_closure_set(v___f_833_, 3, v_mvarId_767_);
lean_closure_set(v___f_833_, 4, v_fvarId_768_);
v___x_124__overap_834_ = l_Lean_MVarId_withContext___redArg(v___x_794_, v___x_831_, v_mvarId_767_, v___f_833_);
lean_inc(v_a_774_);
lean_inc_ref(v_a_773_);
lean_inc(v_a_772_);
lean_inc_ref(v_a_771_);
v___x_835_ = lean_apply_5(v___x_124__overap_834_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, lean_box(0));
return v___x_835_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_replaceLocalDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_767_ = stack[0].m_obj;
lean_object* v_fvarId_768_ = stack[1].m_obj;
lean_object* v_typeNew_769_ = stack[2].m_obj;
lean_object* v_eqProof_770_ = stack[3].m_obj;
lean_object* v_a_771_ = stack[4].m_obj;
lean_object* v_a_772_ = stack[5].m_obj;
lean_object* v_a_773_ = stack[6].m_obj;
lean_object* v_a_774_ = stack[7].m_obj;
lean_object* v_res_842_;
v_res_842_ = l_Lean_MVarId_replaceLocalDecl(v_mvarId_767_, v_fvarId_768_, v_typeNew_769_, v_eqProof_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_);
stack->m_obj
 = v_res_842_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDecl___boxed(lean_object* v_mvarId_843_, lean_object* v_fvarId_844_, lean_object* v_typeNew_845_, lean_object* v_eqProof_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Lean_MVarId_replaceLocalDecl(v_mvarId_843_, v_fvarId_844_, v_typeNew_845_, v_eqProof_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_);
lean_dec(v_a_850_);
lean_dec_ref(v_a_849_);
lean_dec(v_a_848_);
lean_dec_ref(v_a_847_);
return v_res_852_;
}
}
lean_object* l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___redArg(lean_object* v_decls_853_, lean_object* v_x_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = l_Lean_Meta_withLocalInstancesImp___redArg(v_decls_853_, v_x_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_868_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_868_ == 0)
{
v___x_863_ = v___x_860_;
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_860_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_866_; 
if (v_isShared_864_ == 0)
{
v___x_866_ = v___x_863_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_a_861_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
else
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_876_; 
v_a_869_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_876_ == 0)
{
v___x_871_ = v___x_860_;
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_860_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_874_; 
if (v_isShared_872_ == 0)
{
v___x_874_ = v___x_871_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_a_869_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_decls_853_ = stack[0].m_obj;
lean_object* v_x_854_ = stack[1].m_obj;
lean_object* v___y_855_ = stack[2].m_obj;
lean_object* v___y_856_ = stack[3].m_obj;
lean_object* v___y_857_ = stack[4].m_obj;
lean_object* v___y_858_ = stack[5].m_obj;
lean_object* v_res_877_;
v_res_877_ = l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___redArg(v_decls_853_, v_x_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
stack->m_obj
 = v_res_877_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___redArg___boxed(lean_object* v_decls_878_, lean_object* v_x_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___redArg(v_decls_878_, v_x_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v_decls_878_);
return v_res_885_;
}
}
lean_object* l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0(lean_object* v_00_u03b1_886_, lean_object* v_decls_887_, lean_object* v_x_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___redArg(v_decls_887_, v_x_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_);
return v___x_894_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_decls_887_ = stack[1].m_obj;
lean_object* v_x_888_ = stack[2].m_obj;
lean_object* v___y_889_ = stack[3].m_obj;
lean_object* v___y_890_ = stack[4].m_obj;
lean_object* v___y_891_ = stack[5].m_obj;
lean_object* v___y_892_ = stack[6].m_obj;
lean_object* v_res_895_;
v_res_895_ = l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0(lean_box(0), v_decls_887_, v_x_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_);
stack->m_obj
 = v_res_895_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___boxed(lean_object* v_00_u03b1_896_, lean_object* v_decls_897_, lean_object* v_x_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0(v_00_u03b1_896_, v_decls_897_, v_x_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec(v_decls_897_);
return v_res_904_;
}
}
lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___redArg(lean_object* v_lctx_905_, lean_object* v_x_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v_keyedConfig_912_; uint8_t v_trackZetaDelta_913_; lean_object* v_zetaDeltaSet_914_; lean_object* v_localInstances_915_; lean_object* v_defEqCtx_x3f_916_; lean_object* v_synthPendingDepth_917_; lean_object* v_customCanUnfoldPredicate_x3f_918_; uint8_t v_univApprox_919_; uint8_t v_inTypeClassResolution_920_; uint8_t v_cacheInferType_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v_keyedConfig_912_ = lean_ctor_get(v___y_907_, 0);
v_trackZetaDelta_913_ = lean_ctor_get_uint8(v___y_907_, sizeof(void*)*7);
v_zetaDeltaSet_914_ = lean_ctor_get(v___y_907_, 1);
v_localInstances_915_ = lean_ctor_get(v___y_907_, 3);
v_defEqCtx_x3f_916_ = lean_ctor_get(v___y_907_, 4);
v_synthPendingDepth_917_ = lean_ctor_get(v___y_907_, 5);
v_customCanUnfoldPredicate_x3f_918_ = lean_ctor_get(v___y_907_, 6);
v_univApprox_919_ = lean_ctor_get_uint8(v___y_907_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_920_ = lean_ctor_get_uint8(v___y_907_, sizeof(void*)*7 + 2);
v_cacheInferType_921_ = lean_ctor_get_uint8(v___y_907_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_918_);
lean_inc(v_synthPendingDepth_917_);
lean_inc(v_defEqCtx_x3f_916_);
lean_inc_ref(v_localInstances_915_);
lean_inc(v_zetaDeltaSet_914_);
lean_inc_ref(v_keyedConfig_912_);
v___x_922_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_922_, 0, v_keyedConfig_912_);
lean_ctor_set(v___x_922_, 1, v_zetaDeltaSet_914_);
lean_ctor_set(v___x_922_, 2, v_lctx_905_);
lean_ctor_set(v___x_922_, 3, v_localInstances_915_);
lean_ctor_set(v___x_922_, 4, v_defEqCtx_x3f_916_);
lean_ctor_set(v___x_922_, 5, v_synthPendingDepth_917_);
lean_ctor_set(v___x_922_, 6, v_customCanUnfoldPredicate_x3f_918_);
lean_ctor_set_uint8(v___x_922_, sizeof(void*)*7, v_trackZetaDelta_913_);
lean_ctor_set_uint8(v___x_922_, sizeof(void*)*7 + 1, v_univApprox_919_);
lean_ctor_set_uint8(v___x_922_, sizeof(void*)*7 + 2, v_inTypeClassResolution_920_);
lean_ctor_set_uint8(v___x_922_, sizeof(void*)*7 + 3, v_cacheInferType_921_);
lean_inc(v___y_910_);
lean_inc_ref(v___y_909_);
lean_inc(v___y_908_);
v___x_923_ = lean_apply_5(v_x_906_, v___x_922_, v___y_908_, v___y_909_, v___y_910_, lean_box(0));
return v___x_923_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_905_ = stack[0].m_obj;
lean_object* v_x_906_ = stack[1].m_obj;
lean_object* v___y_907_ = stack[2].m_obj;
lean_object* v___y_908_ = stack[3].m_obj;
lean_object* v___y_909_ = stack[4].m_obj;
lean_object* v___y_910_ = stack[5].m_obj;
lean_object* v_res_924_;
v_res_924_ = l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___redArg(v_lctx_905_, v_x_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
stack->m_obj
 = v_res_924_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___redArg___boxed(lean_object* v_lctx_925_, lean_object* v_x_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___redArg(v_lctx_925_, v_x_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
return v_res_932_;
}
}
lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1(lean_object* v_00_u03b1_933_, lean_object* v_lctx_934_, lean_object* v_x_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___redArg(v_lctx_934_, v_x_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
return v___x_941_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_934_ = stack[1].m_obj;
lean_object* v_x_935_ = stack[2].m_obj;
lean_object* v___y_936_ = stack[3].m_obj;
lean_object* v___y_937_ = stack[4].m_obj;
lean_object* v___y_938_ = stack[5].m_obj;
lean_object* v___y_939_ = stack[6].m_obj;
lean_object* v_res_942_;
v_res_942_ = l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1(lean_box(0), v_lctx_934_, v_x_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
stack->m_obj
 = v_res_942_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___boxed(lean_object* v_00_u03b1_943_, lean_object* v_lctx_944_, lean_object* v_x_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1(v_00_u03b1_943_, v_lctx_944_, v_x_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
return v_res_951_;
}
}
lean_object* l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2___redArg(lean_object* v_mvarId_952_, lean_object* v_fvarId_953_, lean_object* v_type_954_, lean_object* v___y_955_){
_start:
{
lean_object* v___x_957_; lean_object* v_mctx_958_; lean_object* v_cache_959_; lean_object* v_zetaDeltaFVarIds_960_; lean_object* v_postponed_961_; lean_object* v_diag_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_973_; 
v___x_957_ = lean_st_ref_take(v___y_955_);
v_mctx_958_ = lean_ctor_get(v___x_957_, 0);
v_cache_959_ = lean_ctor_get(v___x_957_, 1);
v_zetaDeltaFVarIds_960_ = lean_ctor_get(v___x_957_, 2);
v_postponed_961_ = lean_ctor_get(v___x_957_, 3);
v_diag_962_ = lean_ctor_get(v___x_957_, 4);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_973_ == 0)
{
v___x_964_ = v___x_957_;
v_isShared_965_ = v_isSharedCheck_973_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_diag_962_);
lean_inc(v_postponed_961_);
lean_inc(v_zetaDeltaFVarIds_960_);
lean_inc(v_cache_959_);
lean_inc(v_mctx_958_);
lean_dec(v___x_957_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_973_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_969_; 
v___x_966_ = lean_box(0);
v___x_967_ = l_Lean_MetavarContext_setFVarType(v_mctx_958_, v_mvarId_952_, v_fvarId_953_, v_type_954_);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 0, v___x_967_);
v___x_969_ = v___x_964_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_967_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v_cache_959_);
lean_ctor_set(v_reuseFailAlloc_972_, 2, v_zetaDeltaFVarIds_960_);
lean_ctor_set(v_reuseFailAlloc_972_, 3, v_postponed_961_);
lean_ctor_set(v_reuseFailAlloc_972_, 4, v_diag_962_);
v___x_969_ = v_reuseFailAlloc_972_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = lean_st_ref_put(v___y_955_, v___x_969_);
v___x_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_971_, 0, v___x_966_);
return v___x_971_;
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_952_ = stack[0].m_obj;
lean_object* v_fvarId_953_ = stack[1].m_obj;
lean_object* v_type_954_ = stack[2].m_obj;
lean_object* v___y_955_ = stack[3].m_obj;
lean_object* v_res_974_;
v_res_974_ = l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2___redArg(v_mvarId_952_, v_fvarId_953_, v_type_954_, v___y_955_);
stack->m_obj
 = v_res_974_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2___redArg___boxed(lean_object* v_mvarId_975_, lean_object* v_fvarId_976_, lean_object* v_type_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2___redArg(v_mvarId_975_, v_fvarId_976_, v_type_977_, v___y_978_);
lean_dec(v___y_978_);
return v_res_980_;
}
}
lean_object* l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2(lean_object* v_mvarId_981_, lean_object* v_fvarId_982_, lean_object* v_type_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2___redArg(v_mvarId_981_, v_fvarId_982_, v_type_983_, v___y_985_);
return v___x_989_;
}
}
LEAN_EXPORT void l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_981_ = stack[0].m_obj;
lean_object* v_fvarId_982_ = stack[1].m_obj;
lean_object* v_type_983_ = stack[2].m_obj;
lean_object* v___y_984_ = stack[3].m_obj;
lean_object* v___y_985_ = stack[4].m_obj;
lean_object* v___y_986_ = stack[5].m_obj;
lean_object* v___y_987_ = stack[6].m_obj;
lean_object* v_res_990_;
v_res_990_ = l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2(v_mvarId_981_, v_fvarId_982_, v_type_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
stack->m_obj
 = v_res_990_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2___boxed(lean_object* v_mvarId_991_, lean_object* v_fvarId_992_, lean_object* v_type_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2(v_mvarId_991_, v_fvarId_992_, v_type_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
return v_res_999_;
}
}
lean_object* l_Lean_MVarId_replaceLocalDeclDefEq___lam__0(lean_object* v_mvarId_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v___x_1006_; 
lean_inc(v_mvarId_1000_);
v___x_1006_ = l_Lean_MVarId_getDecl(v_mvarId_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v_a_1007_; lean_object* v_userName_1008_; lean_object* v_type_1009_; uint8_t v_kind_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
lean_inc(v_a_1007_);
lean_dec_ref_known(v___x_1006_, 1);
v_userName_1008_ = lean_ctor_get(v_a_1007_, 0);
lean_inc(v_userName_1008_);
v_type_1009_ = lean_ctor_get(v_a_1007_, 2);
lean_inc_ref(v_type_1009_);
v_kind_1010_ = lean_ctor_get_uint8(v_a_1007_, sizeof(void*)*7);
lean_dec(v_a_1007_);
v___x_1011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1011_, 0, v_type_1009_);
v___x_1012_ = l_Lean_Meta_mkFreshExprMVar(v___x_1011_, v_kind_1010_, v_userName_1008_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v_a_1013_; lean_object* v___x_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1022_; 
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc_n(v_a_1013_, 2);
lean_dec_ref_known(v___x_1012_, 1);
v___x_1014_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg(v_mvarId_1000_, v_a_1013_, v___y_1002_);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1022_ == 0)
{
lean_object* v_unused_1023_; 
v_unused_1023_ = lean_ctor_get(v___x_1014_, 0);
lean_dec(v_unused_1023_);
v___x_1016_ = v___x_1014_;
v_isShared_1017_ = v_isSharedCheck_1022_;
goto v_resetjp_1015_;
}
else
{
lean_dec(v___x_1014_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1022_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1018_; lean_object* v___x_1020_; 
v___x_1018_ = l_Lean_Expr_mvarId_x21(v_a_1013_);
lean_dec(v_a_1013_);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 0, v___x_1018_);
v___x_1020_ = v___x_1016_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_1018_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
else
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
lean_dec(v_mvarId_1000_);
v_a_1024_ = lean_ctor_get(v___x_1012_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_1012_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1012_);
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
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
lean_dec(v_mvarId_1000_);
v_a_1032_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_1006_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_1006_);
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
}
}
LEAN_EXPORT void l_Lean_MVarId_replaceLocalDeclDefEq___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1000_ = stack[0].m_obj;
lean_object* v___y_1001_ = stack[1].m_obj;
lean_object* v___y_1002_ = stack[2].m_obj;
lean_object* v___y_1003_ = stack[3].m_obj;
lean_object* v___y_1004_ = stack[4].m_obj;
lean_object* v_res_1040_;
v_res_1040_ = l_Lean_MVarId_replaceLocalDeclDefEq___lam__0(v_mvarId_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
stack->m_obj
 = v_res_1040_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq___lam__0___boxed(lean_object* v_mvarId_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_Lean_MVarId_replaceLocalDeclDefEq___lam__0(v_mvarId_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
return v_res_1047_;
}
}
lean_object* l_Lean_MVarId_replaceLocalDeclDefEq___lam__1(lean_object* v_fvarId_1048_, lean_object* v_typeNew_1049_, lean_object* v___f_1050_, lean_object* v_mvarId_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
lean_object* v___x_1057_; 
lean_inc(v_fvarId_1048_);
v___x_1057_ = l_Lean_FVarId_getType___redArg(v_fvarId_1048_, v___y_1052_, v___y_1054_, v___y_1055_);
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1087_; 
v_a_1058_ = lean_ctor_get(v___x_1057_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1060_ = v___x_1057_;
v_isShared_1061_ = v_isSharedCheck_1087_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_1057_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1087_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
uint8_t v___x_1062_; 
v___x_1062_ = lean_expr_equal(v_a_1058_, v_typeNew_1049_);
if (v___x_1062_ == 0)
{
lean_object* v___x_1063_; lean_object* v_a_1064_; lean_object* v___x_1065_; lean_object* v_a_1066_; uint8_t v___x_1067_; 
lean_del_object(v___x_1060_);
v___x_1063_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(v_a_1058_, v___y_1053_);
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
lean_inc(v_a_1064_);
lean_dec_ref(v___x_1063_);
v___x_1065_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(v_typeNew_1049_, v___y_1053_);
v_a_1066_ = lean_ctor_get(v___x_1065_, 0);
lean_inc(v_a_1066_);
lean_dec_ref(v___x_1065_);
v___x_1067_ = lean_expr_equal(v_a_1064_, v_a_1066_);
if (v___x_1067_ == 0)
{
lean_object* v_lctx_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
lean_dec(v_a_1064_);
lean_dec(v_mvarId_1051_);
v_lctx_1068_ = lean_ctor_get(v___y_1052_, 2);
lean_inc(v_fvarId_1048_);
lean_inc_ref(v_lctx_1068_);
v___x_1069_ = l_Lean_LocalContext_setType(v_lctx_1068_, v_fvarId_1048_, v_a_1066_);
lean_inc_ref(v___x_1069_);
v___x_1070_ = l_Lean_LocalContext_get_x21(v___x_1069_, v_fvarId_1048_);
v___x_1071_ = lean_box(0);
v___x_1072_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1070_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
v___x_1073_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___boxed), 8, 3);
lean_closure_set(v___x_1073_, 0, lean_box(0));
lean_closure_set(v___x_1073_, 1, v___x_1072_);
lean_closure_set(v___x_1073_, 2, v___f_1050_);
v___x_1074_ = l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___redArg(v___x_1069_, v___x_1073_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
lean_dec_ref(v___y_1052_);
return v___x_1074_;
}
else
{
lean_object* v___x_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
lean_dec(v_a_1066_);
lean_dec_ref(v___y_1052_);
lean_dec_ref(v___f_1050_);
lean_inc(v_mvarId_1051_);
v___x_1075_ = l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2___redArg(v_mvarId_1051_, v_fvarId_1048_, v_a_1064_, v___y_1053_);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1082_ == 0)
{
lean_object* v_unused_1083_; 
v_unused_1083_ = lean_ctor_get(v___x_1075_, 0);
lean_dec(v_unused_1083_);
v___x_1077_ = v___x_1075_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_dec(v___x_1075_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 0, v_mvarId_1051_);
v___x_1080_ = v___x_1077_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_mvarId_1051_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
else
{
lean_object* v___x_1085_; 
lean_dec(v_a_1058_);
lean_dec_ref(v___y_1052_);
lean_dec_ref(v___f_1050_);
lean_dec_ref(v_typeNew_1049_);
lean_dec(v_fvarId_1048_);
if (v_isShared_1061_ == 0)
{
lean_ctor_set(v___x_1060_, 0, v_mvarId_1051_);
v___x_1085_ = v___x_1060_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_mvarId_1051_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
else
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1095_; 
lean_dec_ref(v___y_1052_);
lean_dec(v_mvarId_1051_);
lean_dec_ref(v___f_1050_);
lean_dec_ref(v_typeNew_1049_);
lean_dec(v_fvarId_1048_);
v_a_1088_ = lean_ctor_get(v___x_1057_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1090_ = v___x_1057_;
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1057_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_a_1088_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_replaceLocalDeclDefEq___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_1048_ = stack[0].m_obj;
lean_object* v_typeNew_1049_ = stack[1].m_obj;
lean_object* v___f_1050_ = stack[2].m_obj;
lean_object* v_mvarId_1051_ = stack[3].m_obj;
lean_object* v___y_1052_ = stack[4].m_obj;
lean_object* v___y_1053_ = stack[5].m_obj;
lean_object* v___y_1054_ = stack[6].m_obj;
lean_object* v___y_1055_ = stack[7].m_obj;
lean_object* v_res_1096_;
v_res_1096_ = l_Lean_MVarId_replaceLocalDeclDefEq___lam__1(v_fvarId_1048_, v_typeNew_1049_, v___f_1050_, v_mvarId_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
stack->m_obj
 = v_res_1096_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq___lam__1___boxed(lean_object* v_fvarId_1097_, lean_object* v_typeNew_1098_, lean_object* v___f_1099_, lean_object* v_mvarId_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_Lean_MVarId_replaceLocalDeclDefEq___lam__1(v_fvarId_1097_, v_typeNew_1098_, v___f_1099_, v_mvarId_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
return v_res_1106_;
}
}
lean_object* l_Lean_MVarId_replaceLocalDeclDefEq(lean_object* v_mvarId_1107_, lean_object* v_fvarId_1108_, lean_object* v_typeNew_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_){
_start:
{
lean_object* v___f_1115_; lean_object* v___f_1116_; lean_object* v___x_1117_; 
lean_inc_n(v_mvarId_1107_, 2);
v___f_1115_ = lean_alloc_closure((void*)(l_Lean_MVarId_replaceLocalDeclDefEq___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1115_, 0, v_mvarId_1107_);
v___f_1116_ = lean_alloc_closure((void*)(l_Lean_MVarId_replaceLocalDeclDefEq___lam__1___boxed), 9, 4);
lean_closure_set(v___f_1116_, 0, v_fvarId_1108_);
lean_closure_set(v___f_1116_, 1, v_typeNew_1109_);
lean_closure_set(v___f_1116_, 2, v___f_1115_);
lean_closure_set(v___f_1116_, 3, v_mvarId_1107_);
v___x_1117_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_1107_, v___f_1116_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_);
return v___x_1117_;
}
}
LEAN_EXPORT void l_Lean_MVarId_replaceLocalDeclDefEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1107_ = stack[0].m_obj;
lean_object* v_fvarId_1108_ = stack[1].m_obj;
lean_object* v_typeNew_1109_ = stack[2].m_obj;
lean_object* v_a_1110_ = stack[3].m_obj;
lean_object* v_a_1111_ = stack[4].m_obj;
lean_object* v_a_1112_ = stack[5].m_obj;
lean_object* v_a_1113_ = stack[6].m_obj;
lean_object* v_res_1118_;
v_res_1118_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_mvarId_1107_, v_fvarId_1108_, v_typeNew_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_);
stack->m_obj
 = v_res_1118_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq___boxed(lean_object* v_mvarId_1119_, lean_object* v_fvarId_1120_, lean_object* v_typeNew_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_mvarId_1119_, v_fvarId_1120_, v_typeNew_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_);
lean_dec(v_a_1125_);
lean_dec_ref(v_a_1124_);
lean_dec(v_a_1123_);
lean_dec_ref(v_a_1122_);
return v_res_1127_;
}
}
static lean_object* _init_l_Lean_MVarId_change___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = ((lean_object*)(l_Lean_MVarId_change___lam__0___closed__0));
v___x_1130_ = l_Lean_stringToMessageData(v___x_1129_);
return v___x_1130_;
}
}
static lean_object* _init_l_Lean_MVarId_change___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1132_ = ((lean_object*)(l_Lean_MVarId_change___lam__0___closed__2));
v___x_1133_ = l_Lean_stringToMessageData(v___x_1132_);
return v___x_1133_;
}
}
lean_object* l_Lean_MVarId_change___lam__0(lean_object* v_mvarId_1134_, uint8_t v_checkDefEq_1135_, lean_object* v_targetNew_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v___x_1142_; 
lean_inc(v_mvarId_1134_);
v___x_1142_ = l_Lean_MVarId_getType(v_mvarId_1134_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
if (lean_obj_tag(v___x_1142_) == 0)
{
if (v_checkDefEq_1135_ == 0)
{
lean_object* v___x_1143_; 
lean_dec_ref_known(v___x_1142_, 1);
v___x_1143_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_1134_, v_targetNew_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
return v___x_1143_;
}
else
{
lean_object* v_a_1144_; lean_object* v___x_1145_; 
v_a_1144_ = lean_ctor_get(v___x_1142_, 0);
lean_inc_n(v_a_1144_, 2);
lean_dec_ref_known(v___x_1142_, 1);
lean_inc_ref(v_targetNew_1136_);
v___x_1145_ = l_Lean_Meta_isExprDefEq(v_a_1144_, v_targetNew_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1146_; uint8_t v___x_1147_; 
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
lean_inc(v_a_1146_);
lean_dec_ref_known(v___x_1145_, 1);
v___x_1147_ = lean_unbox(v_a_1146_);
lean_dec(v_a_1146_);
if (v___x_1147_ == 0)
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1148_ = ((lean_object*)(l_Lean_MVarId_replaceTargetDefEq___closed__1));
v___x_1149_ = lean_obj_once(&l_Lean_MVarId_change___lam__0___closed__1, &l_Lean_MVarId_change___lam__0___closed__1_once, _init_l_Lean_MVarId_change___lam__0___closed__1);
lean_inc_ref(v_targetNew_1136_);
v___x_1150_ = l_Lean_indentExpr(v_targetNew_1136_);
v___x_1151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1149_);
lean_ctor_set(v___x_1151_, 1, v___x_1150_);
v___x_1152_ = lean_obj_once(&l_Lean_MVarId_change___lam__0___closed__3, &l_Lean_MVarId_change___lam__0___closed__3_once, _init_l_Lean_MVarId_change___lam__0___closed__3);
v___x_1153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1151_);
lean_ctor_set(v___x_1153_, 1, v___x_1152_);
v___x_1154_ = l_Lean_indentExpr(v_a_1144_);
v___x_1155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1153_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
v___x_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1155_);
lean_inc(v_mvarId_1134_);
v___x_1157_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1148_, v_mvarId_1134_, v___x_1156_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_object* v___x_1158_; 
lean_dec_ref_known(v___x_1157_, 1);
v___x_1158_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_1134_, v_targetNew_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
return v___x_1158_;
}
else
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
lean_dec_ref(v_targetNew_1136_);
lean_dec(v_mvarId_1134_);
v_a_1159_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1161_ = v___x_1157_;
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1157_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1164_; 
if (v_isShared_1162_ == 0)
{
v___x_1164_ = v___x_1161_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_a_1159_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
}
else
{
lean_object* v___x_1167_; 
lean_dec(v_a_1144_);
v___x_1167_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_1134_, v_targetNew_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
return v___x_1167_;
}
}
else
{
lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1175_; 
lean_dec(v_a_1144_);
lean_dec_ref(v_targetNew_1136_);
lean_dec(v_mvarId_1134_);
v_a_1168_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1170_ = v___x_1145_;
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v___x_1145_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1173_; 
if (v_isShared_1171_ == 0)
{
v___x_1173_ = v___x_1170_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_a_1168_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
}
}
else
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1183_; 
lean_dec_ref(v_targetNew_1136_);
lean_dec(v_mvarId_1134_);
v_a_1176_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1178_ = v___x_1142_;
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1142_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
if (v_isShared_1179_ == 0)
{
v___x_1181_ = v___x_1178_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1176_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_change___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1134_ = stack[0].m_obj;
uint8_t v_checkDefEq_1135_ = stack[1].m_num;
lean_object* v_targetNew_1136_ = stack[2].m_obj;
lean_object* v___y_1137_ = stack[3].m_obj;
lean_object* v___y_1138_ = stack[4].m_obj;
lean_object* v___y_1139_ = stack[5].m_obj;
lean_object* v___y_1140_ = stack[6].m_obj;
lean_object* v_res_1184_;
v_res_1184_ = l_Lean_MVarId_change___lam__0(v_mvarId_1134_, v_checkDefEq_1135_, v_targetNew_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
stack->m_obj
 = v_res_1184_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_change___lam__0___boxed(lean_object* v_mvarId_1185_, lean_object* v_checkDefEq_1186_, lean_object* v_targetNew_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
uint8_t v_checkDefEq_boxed_1193_; lean_object* v_res_1194_; 
v_checkDefEq_boxed_1193_ = lean_unbox(v_checkDefEq_1186_);
v_res_1194_ = l_Lean_MVarId_change___lam__0(v_mvarId_1185_, v_checkDefEq_boxed_1193_, v_targetNew_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
return v_res_1194_;
}
}
lean_object* l_Lean_MVarId_change(lean_object* v_mvarId_1195_, lean_object* v_targetNew_1196_, uint8_t v_checkDefEq_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_){
_start:
{
lean_object* v___x_1203_; lean_object* v___f_1204_; lean_object* v___x_1205_; 
v___x_1203_ = lean_box(v_checkDefEq_1197_);
lean_inc(v_mvarId_1195_);
v___f_1204_ = lean_alloc_closure((void*)(l_Lean_MVarId_change___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1204_, 0, v_mvarId_1195_);
lean_closure_set(v___f_1204_, 1, v___x_1203_);
lean_closure_set(v___f_1204_, 2, v_targetNew_1196_);
v___x_1205_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_1195_, v___f_1204_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_);
return v___x_1205_;
}
}
LEAN_EXPORT void l_Lean_MVarId_change_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1195_ = stack[0].m_obj;
lean_object* v_targetNew_1196_ = stack[1].m_obj;
uint8_t v_checkDefEq_1197_ = stack[2].m_num;
lean_object* v_a_1198_ = stack[3].m_obj;
lean_object* v_a_1199_ = stack[4].m_obj;
lean_object* v_a_1200_ = stack[5].m_obj;
lean_object* v_a_1201_ = stack[6].m_obj;
lean_object* v_res_1206_;
v_res_1206_ = l_Lean_MVarId_change(v_mvarId_1195_, v_targetNew_1196_, v_checkDefEq_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_);
stack->m_obj
 = v_res_1206_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_change___boxed(lean_object* v_mvarId_1207_, lean_object* v_targetNew_1208_, lean_object* v_checkDefEq_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_){
_start:
{
uint8_t v_checkDefEq_boxed_1215_; lean_object* v_res_1216_; 
v_checkDefEq_boxed_1215_ = lean_unbox(v_checkDefEq_1209_);
v_res_1216_ = l_Lean_MVarId_change(v_mvarId_1207_, v_targetNew_1208_, v_checkDefEq_boxed_1215_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
lean_dec(v_a_1213_);
lean_dec_ref(v_a_1212_);
lean_dec(v_a_1211_);
lean_dec_ref(v_a_1210_);
return v_res_1216_;
}
}
lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0___redArg(lean_object* v_t_1217_, lean_object* v___y_1218_){
_start:
{
lean_object* v___x_1220_; lean_object* v_infoState_1221_; uint8_t v_enabled_1222_; 
v___x_1220_ = lean_st_ref_get(v___y_1218_);
v_infoState_1221_ = lean_ctor_get(v___x_1220_, 8);
lean_inc_ref(v_infoState_1221_);
lean_dec(v___x_1220_);
v_enabled_1222_ = lean_ctor_get_uint8(v_infoState_1221_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1221_);
if (v_enabled_1222_ == 0)
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
lean_dec_ref(v_t_1217_);
v___x_1223_ = lean_box(0);
v___x_1224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
return v___x_1224_;
}
else
{
lean_object* v___x_1225_; lean_object* v_infoState_1226_; lean_object* v_env_1227_; lean_object* v_nextMacroScope_1228_; lean_object* v_ngen_1229_; lean_object* v_auxDeclNGen_1230_; lean_object* v_traceState_1231_; lean_object* v_cache_1232_; lean_object* v_recordedDeps_1233_; lean_object* v_messages_1234_; lean_object* v_snapshotTasks_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1257_; 
v___x_1225_ = lean_st_ref_take(v___y_1218_);
v_infoState_1226_ = lean_ctor_get(v___x_1225_, 8);
v_env_1227_ = lean_ctor_get(v___x_1225_, 0);
v_nextMacroScope_1228_ = lean_ctor_get(v___x_1225_, 1);
v_ngen_1229_ = lean_ctor_get(v___x_1225_, 2);
v_auxDeclNGen_1230_ = lean_ctor_get(v___x_1225_, 3);
v_traceState_1231_ = lean_ctor_get(v___x_1225_, 4);
v_cache_1232_ = lean_ctor_get(v___x_1225_, 5);
v_recordedDeps_1233_ = lean_ctor_get(v___x_1225_, 6);
v_messages_1234_ = lean_ctor_get(v___x_1225_, 7);
v_snapshotTasks_1235_ = lean_ctor_get(v___x_1225_, 9);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1237_ = v___x_1225_;
v_isShared_1238_ = v_isSharedCheck_1257_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_snapshotTasks_1235_);
lean_inc(v_infoState_1226_);
lean_inc(v_messages_1234_);
lean_inc(v_recordedDeps_1233_);
lean_inc(v_cache_1232_);
lean_inc(v_traceState_1231_);
lean_inc(v_auxDeclNGen_1230_);
lean_inc(v_ngen_1229_);
lean_inc(v_nextMacroScope_1228_);
lean_inc(v_env_1227_);
lean_dec(v___x_1225_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1257_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
uint8_t v_enabled_1239_; lean_object* v_assignment_1240_; lean_object* v_lazyAssignment_1241_; lean_object* v_trees_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1256_; 
v_enabled_1239_ = lean_ctor_get_uint8(v_infoState_1226_, sizeof(void*)*3);
v_assignment_1240_ = lean_ctor_get(v_infoState_1226_, 0);
v_lazyAssignment_1241_ = lean_ctor_get(v_infoState_1226_, 1);
v_trees_1242_ = lean_ctor_get(v_infoState_1226_, 2);
v_isSharedCheck_1256_ = !lean_is_exclusive(v_infoState_1226_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1244_ = v_infoState_1226_;
v_isShared_1245_ = v_isSharedCheck_1256_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_trees_1242_);
lean_inc(v_lazyAssignment_1241_);
lean_inc(v_assignment_1240_);
lean_dec(v_infoState_1226_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1256_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1249_; 
v___x_1246_ = lean_box(0);
v___x_1247_ = l_Lean_PersistentArray_push___redArg(v_trees_1242_, v_t_1217_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 2, v___x_1247_);
v___x_1249_ = v___x_1244_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_assignment_1240_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v_lazyAssignment_1241_);
lean_ctor_set(v_reuseFailAlloc_1255_, 2, v___x_1247_);
lean_ctor_set_uint8(v_reuseFailAlloc_1255_, sizeof(void*)*3, v_enabled_1239_);
v___x_1249_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
lean_object* v___x_1251_; 
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 8, v___x_1249_);
v___x_1251_ = v___x_1237_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_env_1227_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v_nextMacroScope_1228_);
lean_ctor_set(v_reuseFailAlloc_1254_, 2, v_ngen_1229_);
lean_ctor_set(v_reuseFailAlloc_1254_, 3, v_auxDeclNGen_1230_);
lean_ctor_set(v_reuseFailAlloc_1254_, 4, v_traceState_1231_);
lean_ctor_set(v_reuseFailAlloc_1254_, 5, v_cache_1232_);
lean_ctor_set(v_reuseFailAlloc_1254_, 6, v_recordedDeps_1233_);
lean_ctor_set(v_reuseFailAlloc_1254_, 7, v_messages_1234_);
lean_ctor_set(v_reuseFailAlloc_1254_, 8, v___x_1249_);
lean_ctor_set(v_reuseFailAlloc_1254_, 9, v_snapshotTasks_1235_);
v___x_1251_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = lean_st_ref_put(v___y_1218_, v___x_1251_);
v___x_1253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1246_);
return v___x_1253_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1217_ = stack[0].m_obj;
lean_object* v___y_1218_ = stack[1].m_obj;
lean_object* v_res_1258_;
v_res_1258_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0___redArg(v_t_1217_, v___y_1218_);
stack->m_obj
 = v_res_1258_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0___redArg___boxed(lean_object* v_t_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0___redArg(v_t_1259_, v___y_1260_);
lean_dec(v___y_1260_);
return v_res_1262_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1263_ = lean_unsigned_to_nat(32u);
v___x_1264_ = lean_mk_empty_array_with_capacity(v___x_1263_);
v___x_1265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1264_);
return v___x_1265_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__1(void){
_start:
{
size_t v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1266_ = ((size_t)5ULL);
v___x_1267_ = lean_unsigned_to_nat(0u);
v___x_1268_ = lean_unsigned_to_nat(32u);
v___x_1269_ = lean_mk_empty_array_with_capacity(v___x_1268_);
v___x_1270_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__0);
v___x_1271_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1271_, 0, v___x_1270_);
lean_ctor_set(v___x_1271_, 1, v___x_1269_);
lean_ctor_set(v___x_1271_, 2, v___x_1267_);
lean_ctor_set(v___x_1271_, 3, v___x_1267_);
lean_ctor_set_usize(v___x_1271_, 4, v___x_1266_);
return v___x_1271_;
}
}
lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0(lean_object* v_t_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v___x_1278_; lean_object* v_infoState_1279_; uint8_t v_enabled_1280_; 
v___x_1278_ = lean_st_ref_get(v___y_1276_);
v_infoState_1279_ = lean_ctor_get(v___x_1278_, 8);
lean_inc_ref(v_infoState_1279_);
lean_dec(v___x_1278_);
v_enabled_1280_ = lean_ctor_get_uint8(v_infoState_1279_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1279_);
if (v_enabled_1280_ == 0)
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
lean_dec_ref(v_t_1272_);
v___x_1281_ = lean_box(0);
v___x_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1281_);
return v___x_1282_;
}
else
{
lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1283_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__1);
v___x_1284_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1284_, 0, v_t_1272_);
lean_ctor_set(v___x_1284_, 1, v___x_1283_);
v___x_1285_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0___redArg(v___x_1284_, v___y_1276_);
return v___x_1285_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1272_ = stack[0].m_obj;
lean_object* v___y_1273_ = stack[1].m_obj;
lean_object* v___y_1274_ = stack[2].m_obj;
lean_object* v___y_1275_ = stack[3].m_obj;
lean_object* v___y_1276_ = stack[4].m_obj;
lean_object* v_res_1286_;
v_res_1286_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0(v_t_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
stack->m_obj
 = v_res_1286_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___boxed(lean_object* v_t_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0(v_t_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
return v_res_1293_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_withReverted_spec__1(lean_object* v_as_1294_, size_t v_sz_1295_, size_t v_i_1296_, lean_object* v_b_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_){
_start:
{
lean_object* v_a_1304_; uint8_t v___x_1308_; 
v___x_1308_ = lean_usize_dec_lt(v_i_1296_, v_sz_1295_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; 
v___x_1309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1309_, 0, v_b_1297_);
return v___x_1309_;
}
else
{
lean_object* v_array_1310_; lean_object* v_start_1311_; lean_object* v_stop_1312_; uint8_t v___x_1313_; 
v_array_1310_ = lean_ctor_get(v_b_1297_, 0);
v_start_1311_ = lean_ctor_get(v_b_1297_, 1);
v_stop_1312_ = lean_ctor_get(v_b_1297_, 2);
v___x_1313_ = lean_nat_dec_lt(v_start_1311_, v_stop_1312_);
if (v___x_1313_ == 0)
{
lean_object* v___x_1314_; 
v___x_1314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1314_, 0, v_b_1297_);
return v___x_1314_;
}
else
{
lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1353_; 
lean_inc(v_stop_1312_);
lean_inc(v_start_1311_);
lean_inc_ref(v_array_1310_);
v_isSharedCheck_1353_ = !lean_is_exclusive(v_b_1297_);
if (v_isSharedCheck_1353_ == 0)
{
lean_object* v_unused_1354_; lean_object* v_unused_1355_; lean_object* v_unused_1356_; 
v_unused_1354_ = lean_ctor_get(v_b_1297_, 2);
lean_dec(v_unused_1354_);
v_unused_1355_ = lean_ctor_get(v_b_1297_, 1);
lean_dec(v_unused_1355_);
v_unused_1356_ = lean_ctor_get(v_b_1297_, 0);
lean_dec(v_unused_1356_);
v___x_1316_ = v_b_1297_;
v_isShared_1317_ = v_isSharedCheck_1353_;
goto v_resetjp_1315_;
}
else
{
lean_dec(v_b_1297_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1353_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v_a_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1323_; 
v_a_1318_ = lean_array_uget(v_as_1294_, v_i_1296_);
v___x_1319_ = lean_array_fget(v_array_1310_, v_start_1311_);
v___x_1320_ = lean_unsigned_to_nat(1u);
v___x_1321_ = lean_nat_add(v_start_1311_, v___x_1320_);
lean_dec(v_start_1311_);
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 1, v___x_1321_);
v___x_1323_ = v___x_1316_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_array_1310_);
lean_ctor_set(v_reuseFailAlloc_1352_, 1, v___x_1321_);
lean_ctor_set(v_reuseFailAlloc_1352_, 2, v_stop_1312_);
v___x_1323_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
if (lean_obj_tag(v_a_1318_) == 1)
{
lean_object* v_val_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1351_; 
v_val_1324_ = lean_ctor_get(v_a_1318_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v_a_1318_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1326_ = v_a_1318_;
v_isShared_1327_ = v_isSharedCheck_1351_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_val_1324_);
lean_dec(v_a_1318_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1351_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1328_; 
lean_inc(v___x_1319_);
v___x_1328_ = l_Lean_FVarId_getUserName___redArg(v___x_1319_, v___y_1298_, v___y_1300_, v___y_1301_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_a_1329_; lean_object* v___x_1330_; lean_object* v___x_1332_; 
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
lean_inc(v_a_1329_);
lean_dec_ref_known(v___x_1328_, 1);
v___x_1330_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1330_, 0, v_a_1329_);
lean_ctor_set(v___x_1330_, 1, v___x_1319_);
lean_ctor_set(v___x_1330_, 2, v_val_1324_);
if (v_isShared_1327_ == 0)
{
lean_ctor_set_tag(v___x_1326_, 11);
lean_ctor_set(v___x_1326_, 0, v___x_1330_);
v___x_1332_ = v___x_1326_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1330_);
v___x_1332_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
lean_object* v___x_1333_; 
v___x_1333_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0(v___x_1332_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_dec_ref_known(v___x_1333_, 1);
v_a_1304_ = v___x_1323_;
goto v___jp_1303_;
}
else
{
lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1341_; 
lean_dec_ref(v___x_1323_);
v_a_1334_ = lean_ctor_get(v___x_1333_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1336_ = v___x_1333_;
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_dec(v___x_1333_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1339_; 
if (v_isShared_1337_ == 0)
{
v___x_1339_ = v___x_1336_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_a_1334_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
}
}
else
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1350_; 
lean_del_object(v___x_1326_);
lean_dec(v_val_1324_);
lean_dec_ref(v___x_1323_);
lean_dec(v___x_1319_);
v_a_1343_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1345_ = v___x_1328_;
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1328_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1348_; 
if (v_isShared_1346_ == 0)
{
v___x_1348_ = v___x_1345_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_a_1343_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
}
else
{
lean_dec(v___x_1319_);
lean_dec(v_a_1318_);
v_a_1304_ = v___x_1323_;
goto v___jp_1303_;
}
}
}
}
}
v___jp_1303_:
{
size_t v___x_1305_; size_t v___x_1306_; 
v___x_1305_ = ((size_t)1ULL);
v___x_1306_ = lean_usize_add(v_i_1296_, v___x_1305_);
v_i_1296_ = v___x_1306_;
v_b_1297_ = v_a_1304_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_withReverted_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1294_ = stack[0].m_obj;
size_t v_sz_1295_ = stack[1].m_num;
size_t v_i_1296_ = stack[2].m_num;
lean_object* v_b_1297_ = stack[3].m_obj;
lean_object* v___y_1298_ = stack[4].m_obj;
lean_object* v___y_1299_ = stack[5].m_obj;
lean_object* v___y_1300_ = stack[6].m_obj;
lean_object* v___y_1301_ = stack[7].m_obj;
lean_object* v_res_1357_;
v_res_1357_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_withReverted_spec__1(v_as_1294_, v_sz_1295_, v_i_1296_, v_b_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_);
stack->m_obj
 = v_res_1357_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_withReverted_spec__1___boxed(lean_object* v_as_1358_, lean_object* v_sz_1359_, lean_object* v_i_1360_, lean_object* v_b_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
size_t v_sz_boxed_1367_; size_t v_i_boxed_1368_; lean_object* v_res_1369_; 
v_sz_boxed_1367_ = lean_unbox_usize(v_sz_1359_);
lean_dec(v_sz_1359_);
v_i_boxed_1368_ = lean_unbox_usize(v_i_1360_);
lean_dec(v_i_1360_);
v_res_1369_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_withReverted_spec__1(v_as_1358_, v_sz_boxed_1367_, v_i_boxed_1368_, v_b_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
lean_dec_ref(v_as_1358_);
return v_res_1369_;
}
}
lean_object* l_Lean_MVarId_withReverted___redArg___lam__0(lean_object* v_fst_1370_, size_t v_sz_1371_, size_t v___x_1372_, lean_object* v___x_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_){
_start:
{
lean_object* v___x_1379_; 
v___x_1379_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_withReverted_spec__1(v_fst_1370_, v_sz_1371_, v___x_1372_, v___x_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1387_; 
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1387_ == 0)
{
lean_object* v_unused_1388_; 
v_unused_1388_ = lean_ctor_get(v___x_1379_, 0);
lean_dec(v_unused_1388_);
v___x_1381_ = v___x_1379_;
v_isShared_1382_ = v_isSharedCheck_1387_;
goto v_resetjp_1380_;
}
else
{
lean_dec(v___x_1379_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1387_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1383_; lean_object* v___x_1385_; 
v___x_1383_ = lean_box(0);
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 0, v___x_1383_);
v___x_1385_ = v___x_1381_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v___x_1383_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
else
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1396_; 
v_a_1389_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1391_ = v___x_1379_;
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1379_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1394_; 
if (v_isShared_1392_ == 0)
{
v___x_1394_ = v___x_1391_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_a_1389_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withReverted___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_1370_ = stack[0].m_obj;
size_t v_sz_1371_ = stack[1].m_num;
size_t v___x_1372_ = stack[2].m_num;
lean_object* v___x_1373_ = stack[3].m_obj;
lean_object* v___y_1374_ = stack[4].m_obj;
lean_object* v___y_1375_ = stack[5].m_obj;
lean_object* v___y_1376_ = stack[6].m_obj;
lean_object* v___y_1377_ = stack[7].m_obj;
lean_object* v_res_1397_;
v_res_1397_ = l_Lean_MVarId_withReverted___redArg___lam__0(v_fst_1370_, v_sz_1371_, v___x_1372_, v___x_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
stack->m_obj
 = v_res_1397_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withReverted___redArg___lam__0___boxed(lean_object* v_fst_1398_, lean_object* v_sz_1399_, lean_object* v___x_1400_, lean_object* v___x_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
size_t v_sz_boxed_1407_; size_t v___x_3494__boxed_1408_; lean_object* v_res_1409_; 
v_sz_boxed_1407_ = lean_unbox_usize(v_sz_1399_);
lean_dec(v_sz_1399_);
v___x_3494__boxed_1408_ = lean_unbox_usize(v___x_1400_);
lean_dec(v___x_1400_);
v_res_1409_ = l_Lean_MVarId_withReverted___redArg___lam__0(v_fst_1398_, v_sz_boxed_1407_, v___x_3494__boxed_1408_, v___x_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
lean_dec_ref(v_fst_1398_);
return v_res_1409_;
}
}
lean_object* l_Lean_MVarId_withReverted___redArg(lean_object* v_mvarId_1412_, lean_object* v_fvarIds_1413_, lean_object* v_k_1414_, uint8_t v_clearAuxDeclsInsteadOfRevert_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_){
_start:
{
uint8_t v___x_1421_; lean_object* v___x_1422_; 
v___x_1421_ = 1;
v___x_1422_ = l_Lean_MVarId_revert(v_mvarId_1412_, v_fvarIds_1413_, v___x_1421_, v_clearAuxDeclsInsteadOfRevert_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v_a_1423_; lean_object* v_fst_1424_; lean_object* v_snd_1425_; lean_object* v___x_1426_; 
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_a_1423_);
lean_dec_ref_known(v___x_1422_, 1);
v_fst_1424_ = lean_ctor_get(v_a_1423_, 0);
lean_inc(v_fst_1424_);
v_snd_1425_ = lean_ctor_get(v_a_1423_, 1);
lean_inc(v_snd_1425_);
lean_dec(v_a_1423_);
lean_inc(v_a_1419_);
lean_inc_ref(v_a_1418_);
lean_inc(v_a_1417_);
lean_inc_ref(v_a_1416_);
v___x_1426_ = lean_apply_7(v_k_1414_, v_snd_1425_, v_fst_1424_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_, lean_box(0));
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; lean_object* v_snd_1428_; lean_object* v_fst_1429_; lean_object* v_fst_1430_; lean_object* v_snd_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; uint8_t v___x_1434_; lean_object* v___x_1435_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
lean_inc(v_a_1427_);
lean_dec_ref_known(v___x_1426_, 1);
v_snd_1428_ = lean_ctor_get(v_a_1427_, 1);
lean_inc(v_snd_1428_);
v_fst_1429_ = lean_ctor_get(v_a_1427_, 0);
lean_inc(v_fst_1429_);
lean_dec(v_a_1427_);
v_fst_1430_ = lean_ctor_get(v_snd_1428_, 0);
lean_inc(v_fst_1430_);
v_snd_1431_ = lean_ctor_get(v_snd_1428_, 1);
lean_inc(v_snd_1431_);
lean_dec(v_snd_1428_);
v___x_1432_ = lean_array_get_size(v_fst_1430_);
v___x_1433_ = lean_box(0);
v___x_1434_ = 0;
v___x_1435_ = l_Lean_Meta_introNCore(v_snd_1431_, v___x_1432_, v___x_1433_, v___x_1434_, v___x_1421_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v_a_1436_; lean_object* v_fst_1437_; lean_object* v_snd_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1469_; 
v_a_1436_ = lean_ctor_get(v___x_1435_, 0);
lean_inc(v_a_1436_);
lean_dec_ref_known(v___x_1435_, 1);
v_fst_1437_ = lean_ctor_get(v_a_1436_, 0);
v_snd_1438_ = lean_ctor_get(v_a_1436_, 1);
v_isSharedCheck_1469_ = !lean_is_exclusive(v_a_1436_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1440_ = v_a_1436_;
v_isShared_1441_ = v_isSharedCheck_1469_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_snd_1438_);
lean_inc(v_fst_1437_);
lean_dec(v_a_1436_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1469_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; size_t v_sz_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___f_1448_; lean_object* v___x_1449_; 
v___x_1442_ = lean_unsigned_to_nat(0u);
v___x_1443_ = lean_array_get_size(v_fst_1437_);
v___x_1444_ = l_Array_toSubarray___redArg(v_fst_1437_, v___x_1442_, v___x_1443_);
v_sz_1445_ = lean_array_size(v_fst_1430_);
v___x_1446_ = lean_box_usize(v_sz_1445_);
v___x_1447_ = ((lean_object*)(l_Lean_MVarId_withReverted___redArg___boxed__const__1));
v___f_1448_ = lean_alloc_closure((void*)(l_Lean_MVarId_withReverted___redArg___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1448_, 0, v_fst_1430_);
lean_closure_set(v___f_1448_, 1, v___x_1446_);
lean_closure_set(v___f_1448_, 2, v___x_1447_);
lean_closure_set(v___f_1448_, 3, v___x_1444_);
lean_inc(v_snd_1438_);
v___x_1449_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_snd_1438_, v___f_1448_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1459_; 
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1459_ == 0)
{
lean_object* v_unused_1460_; 
v_unused_1460_ = lean_ctor_get(v___x_1449_, 0);
lean_dec(v_unused_1460_);
v___x_1451_ = v___x_1449_;
v_isShared_1452_ = v_isSharedCheck_1459_;
goto v_resetjp_1450_;
}
else
{
lean_dec(v___x_1449_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1459_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1454_; 
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 0, v_fst_1429_);
v___x_1454_ = v___x_1440_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_fst_1429_);
lean_ctor_set(v_reuseFailAlloc_1458_, 1, v_snd_1438_);
v___x_1454_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
lean_object* v___x_1456_; 
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 0, v___x_1454_);
v___x_1456_ = v___x_1451_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v___x_1454_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
else
{
lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1468_; 
lean_del_object(v___x_1440_);
lean_dec(v_snd_1438_);
lean_dec(v_fst_1429_);
v_a_1461_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1463_ = v___x_1449_;
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___x_1449_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1466_; 
if (v_isShared_1464_ == 0)
{
v___x_1466_ = v___x_1463_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_a_1461_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
}
}
else
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
lean_dec(v_fst_1430_);
lean_dec(v_fst_1429_);
v_a_1470_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1472_ = v___x_1435_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1435_);
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
else
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1485_; 
v_a_1478_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1480_ = v___x_1426_;
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1426_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1483_; 
if (v_isShared_1481_ == 0)
{
v___x_1483_ = v___x_1480_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_a_1478_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
}
else
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1493_; 
lean_dec_ref(v_k_1414_);
v_a_1486_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1488_ = v___x_1422_;
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1422_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1491_; 
if (v_isShared_1489_ == 0)
{
v___x_1491_ = v___x_1488_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_a_1486_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withReverted___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1412_ = stack[0].m_obj;
lean_object* v_fvarIds_1413_ = stack[1].m_obj;
lean_object* v_k_1414_ = stack[2].m_obj;
uint8_t v_clearAuxDeclsInsteadOfRevert_1415_ = stack[3].m_num;
lean_object* v_a_1416_ = stack[4].m_obj;
lean_object* v_a_1417_ = stack[5].m_obj;
lean_object* v_a_1418_ = stack[6].m_obj;
lean_object* v_a_1419_ = stack[7].m_obj;
lean_object* v_res_1494_;
v_res_1494_ = l_Lean_MVarId_withReverted___redArg(v_mvarId_1412_, v_fvarIds_1413_, v_k_1414_, v_clearAuxDeclsInsteadOfRevert_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_);
stack->m_obj
 = v_res_1494_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withReverted___redArg___boxed(lean_object* v_mvarId_1495_, lean_object* v_fvarIds_1496_, lean_object* v_k_1497_, lean_object* v_clearAuxDeclsInsteadOfRevert_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_){
_start:
{
uint8_t v_clearAuxDeclsInsteadOfRevert_boxed_1504_; lean_object* v_res_1505_; 
v_clearAuxDeclsInsteadOfRevert_boxed_1504_ = lean_unbox(v_clearAuxDeclsInsteadOfRevert_1498_);
v_res_1505_ = l_Lean_MVarId_withReverted___redArg(v_mvarId_1495_, v_fvarIds_1496_, v_k_1497_, v_clearAuxDeclsInsteadOfRevert_boxed_1504_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_);
lean_dec(v_a_1502_);
lean_dec_ref(v_a_1501_);
lean_dec(v_a_1500_);
lean_dec_ref(v_a_1499_);
return v_res_1505_;
}
}
lean_object* l_Lean_MVarId_withReverted(lean_object* v_00_u03b1_1506_, lean_object* v_mvarId_1507_, lean_object* v_fvarIds_1508_, lean_object* v_k_1509_, uint8_t v_clearAuxDeclsInsteadOfRevert_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_){
_start:
{
lean_object* v___x_1516_; 
v___x_1516_ = l_Lean_MVarId_withReverted___redArg(v_mvarId_1507_, v_fvarIds_1508_, v_k_1509_, v_clearAuxDeclsInsteadOfRevert_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
return v___x_1516_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withReverted_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1507_ = stack[1].m_obj;
lean_object* v_fvarIds_1508_ = stack[2].m_obj;
lean_object* v_k_1509_ = stack[3].m_obj;
uint8_t v_clearAuxDeclsInsteadOfRevert_1510_ = stack[4].m_num;
lean_object* v_a_1511_ = stack[5].m_obj;
lean_object* v_a_1512_ = stack[6].m_obj;
lean_object* v_a_1513_ = stack[7].m_obj;
lean_object* v_a_1514_ = stack[8].m_obj;
lean_object* v_res_1517_;
v_res_1517_ = l_Lean_MVarId_withReverted(lean_box(0), v_mvarId_1507_, v_fvarIds_1508_, v_k_1509_, v_clearAuxDeclsInsteadOfRevert_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
stack->m_obj
 = v_res_1517_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withReverted___boxed(lean_object* v_00_u03b1_1518_, lean_object* v_mvarId_1519_, lean_object* v_fvarIds_1520_, lean_object* v_k_1521_, lean_object* v_clearAuxDeclsInsteadOfRevert_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_){
_start:
{
uint8_t v_clearAuxDeclsInsteadOfRevert_boxed_1528_; lean_object* v_res_1529_; 
v_clearAuxDeclsInsteadOfRevert_boxed_1528_ = lean_unbox(v_clearAuxDeclsInsteadOfRevert_1522_);
v_res_1529_ = l_Lean_MVarId_withReverted(v_00_u03b1_1518_, v_mvarId_1519_, v_fvarIds_1520_, v_k_1521_, v_clearAuxDeclsInsteadOfRevert_boxed_1528_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
lean_dec(v_a_1526_);
lean_dec_ref(v_a_1525_);
lean_dec(v_a_1524_);
lean_dec_ref(v_a_1523_);
return v_res_1529_;
}
}
lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0(lean_object* v_t_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v___x_1536_; 
v___x_1536_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0___redArg(v_t_1530_, v___y_1534_);
return v___x_1536_;
}
}
LEAN_EXPORT void l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1530_ = stack[0].m_obj;
lean_object* v___y_1531_ = stack[1].m_obj;
lean_object* v___y_1532_ = stack[2].m_obj;
lean_object* v___y_1533_ = stack[3].m_obj;
lean_object* v___y_1534_ = stack[4].m_obj;
lean_object* v_res_1537_;
v_res_1537_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0(v_t_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
stack->m_obj
 = v_res_1537_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0___boxed(lean_object* v_t_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0(v_t_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
return v_res_1544_;
}
}
lean_object* l_Lean_MVarId_withRevertedFrom___redArg(lean_object* v_mvarId_1545_, lean_object* v_fvarId_1546_, lean_object* v_k_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_){
_start:
{
lean_object* v___x_1553_; 
v___x_1553_ = l_Lean_MVarId_revertFrom(v_mvarId_1545_, v_fvarId_1546_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v_a_1554_; lean_object* v_fst_1555_; lean_object* v_snd_1556_; lean_object* v___x_1557_; 
v_a_1554_ = lean_ctor_get(v___x_1553_, 0);
lean_inc(v_a_1554_);
lean_dec_ref_known(v___x_1553_, 1);
v_fst_1555_ = lean_ctor_get(v_a_1554_, 0);
lean_inc(v_fst_1555_);
v_snd_1556_ = lean_ctor_get(v_a_1554_, 1);
lean_inc(v_snd_1556_);
lean_dec(v_a_1554_);
lean_inc(v_a_1551_);
lean_inc_ref(v_a_1550_);
lean_inc(v_a_1549_);
lean_inc_ref(v_a_1548_);
v___x_1557_ = lean_apply_7(v_k_1547_, v_snd_1556_, v_fst_1555_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, lean_box(0));
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v_a_1558_; lean_object* v_snd_1559_; lean_object* v_fst_1560_; lean_object* v_fst_1561_; lean_object* v_snd_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; uint8_t v___x_1565_; uint8_t v___x_1566_; lean_object* v___x_1567_; 
v_a_1558_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_a_1558_);
lean_dec_ref_known(v___x_1557_, 1);
v_snd_1559_ = lean_ctor_get(v_a_1558_, 1);
lean_inc(v_snd_1559_);
v_fst_1560_ = lean_ctor_get(v_a_1558_, 0);
lean_inc(v_fst_1560_);
lean_dec(v_a_1558_);
v_fst_1561_ = lean_ctor_get(v_snd_1559_, 0);
lean_inc(v_fst_1561_);
v_snd_1562_ = lean_ctor_get(v_snd_1559_, 1);
lean_inc(v_snd_1562_);
lean_dec(v_snd_1559_);
v___x_1563_ = lean_array_get_size(v_fst_1561_);
v___x_1564_ = lean_box(0);
v___x_1565_ = 0;
v___x_1566_ = 1;
v___x_1567_ = l_Lean_Meta_introNCore(v_snd_1562_, v___x_1563_, v___x_1564_, v___x_1565_, v___x_1566_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; lean_object* v_fst_1569_; lean_object* v_snd_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1601_; 
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
lean_inc(v_a_1568_);
lean_dec_ref_known(v___x_1567_, 1);
v_fst_1569_ = lean_ctor_get(v_a_1568_, 0);
v_snd_1570_ = lean_ctor_get(v_a_1568_, 1);
v_isSharedCheck_1601_ = !lean_is_exclusive(v_a_1568_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1572_ = v_a_1568_;
v_isShared_1573_ = v_isSharedCheck_1601_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_snd_1570_);
lean_inc(v_fst_1569_);
lean_dec(v_a_1568_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1601_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; size_t v_sz_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___f_1580_; lean_object* v___x_1581_; 
v___x_1574_ = lean_unsigned_to_nat(0u);
v___x_1575_ = lean_array_get_size(v_fst_1569_);
v___x_1576_ = l_Array_toSubarray___redArg(v_fst_1569_, v___x_1574_, v___x_1575_);
v_sz_1577_ = lean_array_size(v_fst_1561_);
v___x_1578_ = lean_box_usize(v_sz_1577_);
v___x_1579_ = ((lean_object*)(l_Lean_MVarId_withReverted___redArg___boxed__const__1));
v___f_1580_ = lean_alloc_closure((void*)(l_Lean_MVarId_withReverted___redArg___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1580_, 0, v_fst_1561_);
lean_closure_set(v___f_1580_, 1, v___x_1578_);
lean_closure_set(v___f_1580_, 2, v___x_1579_);
lean_closure_set(v___f_1580_, 3, v___x_1576_);
lean_inc(v_snd_1570_);
v___x_1581_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_snd_1570_, v___f_1580_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1591_; 
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1591_ == 0)
{
lean_object* v_unused_1592_; 
v_unused_1592_ = lean_ctor_get(v___x_1581_, 0);
lean_dec(v_unused_1592_);
v___x_1583_ = v___x_1581_;
v_isShared_1584_ = v_isSharedCheck_1591_;
goto v_resetjp_1582_;
}
else
{
lean_dec(v___x_1581_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1591_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1586_; 
if (v_isShared_1573_ == 0)
{
lean_ctor_set(v___x_1572_, 0, v_fst_1560_);
v___x_1586_ = v___x_1572_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_fst_1560_);
lean_ctor_set(v_reuseFailAlloc_1590_, 1, v_snd_1570_);
v___x_1586_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
lean_object* v___x_1588_; 
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 0, v___x_1586_);
v___x_1588_ = v___x_1583_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1586_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
}
else
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1600_; 
lean_del_object(v___x_1572_);
lean_dec(v_snd_1570_);
lean_dec(v_fst_1560_);
v_a_1593_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1595_ = v___x_1581_;
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1581_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1598_; 
if (v_isShared_1596_ == 0)
{
v___x_1598_ = v___x_1595_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1593_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
}
}
else
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
lean_dec(v_fst_1561_);
lean_dec(v_fst_1560_);
v_a_1602_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1604_ = v___x_1567_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1567_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1607_; 
if (v_isShared_1605_ == 0)
{
v___x_1607_ = v___x_1604_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1602_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
else
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1617_; 
v_a_1610_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1612_ = v___x_1557_;
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v___x_1557_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1615_; 
if (v_isShared_1613_ == 0)
{
v___x_1615_ = v___x_1612_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_a_1610_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
}
else
{
lean_object* v_a_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1625_; 
lean_dec_ref(v_k_1547_);
v_a_1618_ = lean_ctor_get(v___x_1553_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1620_ = v___x_1553_;
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_a_1618_);
lean_dec(v___x_1553_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1623_; 
if (v_isShared_1621_ == 0)
{
v___x_1623_ = v___x_1620_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_a_1618_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withRevertedFrom___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1545_ = stack[0].m_obj;
lean_object* v_fvarId_1546_ = stack[1].m_obj;
lean_object* v_k_1547_ = stack[2].m_obj;
lean_object* v_a_1548_ = stack[3].m_obj;
lean_object* v_a_1549_ = stack[4].m_obj;
lean_object* v_a_1550_ = stack[5].m_obj;
lean_object* v_a_1551_ = stack[6].m_obj;
lean_object* v_res_1626_;
v_res_1626_ = l_Lean_MVarId_withRevertedFrom___redArg(v_mvarId_1545_, v_fvarId_1546_, v_k_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_);
stack->m_obj
 = v_res_1626_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withRevertedFrom___redArg___boxed(lean_object* v_mvarId_1627_, lean_object* v_fvarId_1628_, lean_object* v_k_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l_Lean_MVarId_withRevertedFrom___redArg(v_mvarId_1627_, v_fvarId_1628_, v_k_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_);
lean_dec(v_a_1633_);
lean_dec_ref(v_a_1632_);
lean_dec(v_a_1631_);
lean_dec_ref(v_a_1630_);
return v_res_1635_;
}
}
lean_object* l_Lean_MVarId_withRevertedFrom(lean_object* v_00_u03b1_1636_, lean_object* v_mvarId_1637_, lean_object* v_fvarId_1638_, lean_object* v_k_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_){
_start:
{
lean_object* v___x_1645_; 
v___x_1645_ = l_Lean_MVarId_withRevertedFrom___redArg(v_mvarId_1637_, v_fvarId_1638_, v_k_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
return v___x_1645_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withRevertedFrom_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1637_ = stack[1].m_obj;
lean_object* v_fvarId_1638_ = stack[2].m_obj;
lean_object* v_k_1639_ = stack[3].m_obj;
lean_object* v_a_1640_ = stack[4].m_obj;
lean_object* v_a_1641_ = stack[5].m_obj;
lean_object* v_a_1642_ = stack[6].m_obj;
lean_object* v_a_1643_ = stack[7].m_obj;
lean_object* v_res_1646_;
v_res_1646_ = l_Lean_MVarId_withRevertedFrom(lean_box(0), v_mvarId_1637_, v_fvarId_1638_, v_k_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
stack->m_obj
 = v_res_1646_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withRevertedFrom___boxed(lean_object* v_00_u03b1_1647_, lean_object* v_mvarId_1648_, lean_object* v_fvarId_1649_, lean_object* v_k_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l_Lean_MVarId_withRevertedFrom(v_00_u03b1_1647_, v_mvarId_1648_, v_fvarId_1649_, v_k_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_);
lean_dec(v_a_1654_);
lean_dec_ref(v_a_1653_);
lean_dec(v_a_1652_);
lean_dec_ref(v_a_1651_);
return v_res_1656_;
}
}
lean_object* l_Lean_MVarId_changeLocalDecl___lam__0(uint8_t v_checkDefEq_1657_, lean_object* v_typeNew_1658_, lean_object* v___x_1659_, lean_object* v_mvarId_1660_, lean_object* v_typeOld_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
if (v_checkDefEq_1657_ == 0)
{
lean_object* v___x_1667_; lean_object* v___x_1668_; 
lean_dec_ref(v_typeOld_1661_);
lean_dec(v_mvarId_1660_);
lean_dec(v___x_1659_);
lean_dec_ref(v_typeNew_1658_);
v___x_1667_ = lean_box(0);
v___x_1668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1667_);
return v___x_1668_;
}
else
{
lean_object* v___x_1669_; 
lean_inc_ref(v_typeOld_1661_);
lean_inc_ref(v_typeNew_1658_);
v___x_1669_ = l_Lean_Meta_isExprDefEq(v_typeNew_1658_, v_typeOld_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_);
if (lean_obj_tag(v___x_1669_) == 0)
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1688_; 
v_a_1670_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1672_ = v___x_1669_;
v_isShared_1673_ = v_isSharedCheck_1688_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1669_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1688_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
uint8_t v___x_1674_; 
v___x_1674_ = lean_unbox(v_a_1670_);
lean_dec(v_a_1670_);
if (v___x_1674_ == 0)
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
lean_del_object(v___x_1672_);
v___x_1675_ = lean_obj_once(&l_Lean_MVarId_change___lam__0___closed__1, &l_Lean_MVarId_change___lam__0___closed__1_once, _init_l_Lean_MVarId_change___lam__0___closed__1);
v___x_1676_ = l_Lean_indentExpr(v_typeNew_1658_);
v___x_1677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1675_);
lean_ctor_set(v___x_1677_, 1, v___x_1676_);
v___x_1678_ = lean_obj_once(&l_Lean_MVarId_change___lam__0___closed__3, &l_Lean_MVarId_change___lam__0___closed__3_once, _init_l_Lean_MVarId_change___lam__0___closed__3);
v___x_1679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1677_);
lean_ctor_set(v___x_1679_, 1, v___x_1678_);
v___x_1680_ = l_Lean_indentExpr(v_typeOld_1661_);
v___x_1681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1679_);
lean_ctor_set(v___x_1681_, 1, v___x_1680_);
v___x_1682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1682_, 0, v___x_1681_);
v___x_1683_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1659_, v_mvarId_1660_, v___x_1682_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_);
return v___x_1683_;
}
else
{
lean_object* v___x_1684_; lean_object* v___x_1686_; 
lean_dec_ref(v_typeOld_1661_);
lean_dec(v_mvarId_1660_);
lean_dec(v___x_1659_);
lean_dec_ref(v_typeNew_1658_);
v___x_1684_ = lean_box(0);
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 0, v___x_1684_);
v___x_1686_ = v___x_1672_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1684_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
}
else
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1696_; 
lean_dec_ref(v_typeOld_1661_);
lean_dec(v_mvarId_1660_);
lean_dec(v___x_1659_);
lean_dec_ref(v_typeNew_1658_);
v_a_1689_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1691_ = v___x_1669_;
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1669_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1694_; 
if (v_isShared_1692_ == 0)
{
v___x_1694_ = v___x_1691_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_a_1689_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_changeLocalDecl___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_checkDefEq_1657_ = stack[0].m_num;
lean_object* v_typeNew_1658_ = stack[1].m_obj;
lean_object* v___x_1659_ = stack[2].m_obj;
lean_object* v_mvarId_1660_ = stack[3].m_obj;
lean_object* v_typeOld_1661_ = stack[4].m_obj;
lean_object* v___y_1662_ = stack[5].m_obj;
lean_object* v___y_1663_ = stack[6].m_obj;
lean_object* v___y_1664_ = stack[7].m_obj;
lean_object* v___y_1665_ = stack[8].m_obj;
lean_object* v_res_1697_;
v_res_1697_ = l_Lean_MVarId_changeLocalDecl___lam__0(v_checkDefEq_1657_, v_typeNew_1658_, v___x_1659_, v_mvarId_1660_, v_typeOld_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_);
stack->m_obj
 = v_res_1697_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lam__0___boxed(lean_object* v_checkDefEq_1698_, lean_object* v_typeNew_1699_, lean_object* v___x_1700_, lean_object* v_mvarId_1701_, lean_object* v_typeOld_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
uint8_t v_checkDefEq_boxed_1708_; lean_object* v_res_1709_; 
v_checkDefEq_boxed_1708_ = lean_unbox(v_checkDefEq_1698_);
v_res_1709_ = l_Lean_MVarId_changeLocalDecl___lam__0(v_checkDefEq_boxed_1708_, v_typeNew_1699_, v___x_1700_, v_mvarId_1701_, v_typeOld_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
return v_res_1709_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_changeLocalDecl_spec__0(size_t v_sz_1710_, size_t v_i_1711_, lean_object* v_bs_1712_){
_start:
{
uint8_t v___x_1713_; 
v___x_1713_ = lean_usize_dec_lt(v_i_1711_, v_sz_1710_);
if (v___x_1713_ == 0)
{
return v_bs_1712_;
}
else
{
lean_object* v_v_1714_; lean_object* v___x_1715_; lean_object* v_bs_x27_1716_; lean_object* v___x_1717_; size_t v___x_1718_; size_t v___x_1719_; lean_object* v___x_1720_; 
v_v_1714_ = lean_array_uget(v_bs_1712_, v_i_1711_);
v___x_1715_ = lean_unsigned_to_nat(0u);
v_bs_x27_1716_ = lean_array_uset(v_bs_1712_, v_i_1711_, v___x_1715_);
v___x_1717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1717_, 0, v_v_1714_);
v___x_1718_ = ((size_t)1ULL);
v___x_1719_ = lean_usize_add(v_i_1711_, v___x_1718_);
v___x_1720_ = lean_array_uset(v_bs_x27_1716_, v_i_1711_, v___x_1717_);
v_i_1711_ = v___x_1719_;
v_bs_1712_ = v___x_1720_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_changeLocalDecl_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1710_ = stack[0].m_num;
size_t v_i_1711_ = stack[1].m_num;
lean_object* v_bs_1712_ = stack[2].m_obj;
lean_object* v_res_1722_;
v_res_1722_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_changeLocalDecl_spec__0(v_sz_1710_, v_i_1711_, v_bs_1712_);
stack->m_obj
 = v_res_1722_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_changeLocalDecl_spec__0___boxed(lean_object* v_sz_1723_, lean_object* v_i_1724_, lean_object* v_bs_1725_){
_start:
{
size_t v_sz_boxed_1726_; size_t v_i_boxed_1727_; lean_object* v_res_1728_; 
v_sz_boxed_1726_ = lean_unbox_usize(v_sz_1723_);
lean_dec(v_sz_1723_);
v_i_boxed_1727_ = lean_unbox_usize(v_i_1724_);
lean_dec(v_i_1724_);
v_res_1728_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_changeLocalDecl_spec__0(v_sz_boxed_1726_, v_i_boxed_1727_, v_bs_1725_);
return v_res_1728_;
}
}
lean_object* l_Lean_MVarId_changeLocalDecl___lam__1(lean_object* v_mvarId_1729_, lean_object* v_fvars_1730_, lean_object* v_targetNew_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_){
_start:
{
lean_object* v___x_1737_; 
v___x_1737_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_1729_, v_targetNew_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1751_; 
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1740_ = v___x_1737_;
v_isShared_1741_ = v_isSharedCheck_1751_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1737_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1751_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1742_; size_t v_sz_1743_; size_t v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1749_; 
v___x_1742_ = lean_box(0);
v_sz_1743_ = lean_array_size(v_fvars_1730_);
v___x_1744_ = ((size_t)0ULL);
v___x_1745_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_changeLocalDecl_spec__0(v_sz_1743_, v___x_1744_, v_fvars_1730_);
v___x_1746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1745_);
lean_ctor_set(v___x_1746_, 1, v_a_1738_);
v___x_1747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1742_);
lean_ctor_set(v___x_1747_, 1, v___x_1746_);
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 0, v___x_1747_);
v___x_1749_ = v___x_1740_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1747_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
else
{
lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1759_; 
lean_dec_ref(v_fvars_1730_);
v_a_1752_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1754_ = v___x_1737_;
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_dec(v___x_1737_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1757_; 
if (v_isShared_1755_ == 0)
{
v___x_1757_ = v___x_1754_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_a_1752_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_changeLocalDecl___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1729_ = stack[0].m_obj;
lean_object* v_fvars_1730_ = stack[1].m_obj;
lean_object* v_targetNew_1731_ = stack[2].m_obj;
lean_object* v___y_1732_ = stack[3].m_obj;
lean_object* v___y_1733_ = stack[4].m_obj;
lean_object* v___y_1734_ = stack[5].m_obj;
lean_object* v___y_1735_ = stack[6].m_obj;
lean_object* v_res_1760_;
v_res_1760_ = l_Lean_MVarId_changeLocalDecl___lam__1(v_mvarId_1729_, v_fvars_1730_, v_targetNew_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
stack->m_obj
 = v_res_1760_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lam__1___boxed(lean_object* v_mvarId_1761_, lean_object* v_fvars_1762_, lean_object* v_targetNew_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
lean_object* v_res_1769_; 
v_res_1769_ = l_Lean_MVarId_changeLocalDecl___lam__1(v_mvarId_1761_, v_fvars_1762_, v_targetNew_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
lean_dec(v___y_1767_);
lean_dec_ref(v___y_1766_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
return v_res_1769_;
}
}
static lean_object* _init_l_Lean_MVarId_changeLocalDecl___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1773_ = ((lean_object*)(l_Lean_MVarId_changeLocalDecl___lam__2___closed__1));
v___x_1774_ = l_Lean_MessageData_ofFormat(v___x_1773_);
return v___x_1774_;
}
}
static lean_object* _init_l_Lean_MVarId_changeLocalDecl___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1775_ = lean_obj_once(&l_Lean_MVarId_changeLocalDecl___lam__2___closed__2, &l_Lean_MVarId_changeLocalDecl___lam__2___closed__2_once, _init_l_Lean_MVarId_changeLocalDecl___lam__2___closed__2);
v___x_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1775_);
return v___x_1776_;
}
}
lean_object* l_Lean_MVarId_changeLocalDecl___lam__2(lean_object* v_mvarId_1777_, lean_object* v___f_1778_, lean_object* v_typeNew_1779_, lean_object* v___f_1780_, lean_object* v___x_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_){
_start:
{
lean_object* v___x_1787_; 
lean_inc(v_mvarId_1777_);
v___x_1787_ = l_Lean_MVarId_getType(v_mvarId_1777_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v_a_1788_; 
v_a_1788_ = lean_ctor_get(v___x_1787_, 0);
lean_inc(v_a_1788_);
lean_dec_ref_known(v___x_1787_, 1);
switch(lean_obj_tag(v_a_1788_))
{
case 7:
{
lean_object* v_binderName_1789_; lean_object* v_binderType_1790_; lean_object* v_body_1791_; uint8_t v_binderInfo_1792_; lean_object* v___x_1793_; 
lean_dec(v___x_1781_);
lean_dec(v_mvarId_1777_);
v_binderName_1789_ = lean_ctor_get(v_a_1788_, 0);
lean_inc(v_binderName_1789_);
v_binderType_1790_ = lean_ctor_get(v_a_1788_, 1);
lean_inc_ref(v_binderType_1790_);
v_body_1791_ = lean_ctor_get(v_a_1788_, 2);
lean_inc_ref(v_body_1791_);
v_binderInfo_1792_ = lean_ctor_get_uint8(v_a_1788_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_1788_, 3);
lean_inc(v___y_1785_);
lean_inc_ref(v___y_1784_);
lean_inc(v___y_1783_);
lean_inc_ref(v___y_1782_);
v___x_1793_ = lean_apply_6(v___f_1778_, v_binderType_1790_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, lean_box(0));
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v___x_1794_; lean_object* v___x_1795_; 
lean_dec_ref_known(v___x_1793_, 1);
v___x_1794_ = l_Lean_Expr_forallE___override(v_binderName_1789_, v_typeNew_1779_, v_body_1791_, v_binderInfo_1792_);
v___x_1795_ = lean_apply_6(v___f_1780_, v___x_1794_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, lean_box(0));
return v___x_1795_;
}
else
{
lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1803_; 
lean_dec_ref(v_body_1791_);
lean_dec(v_binderName_1789_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec_ref(v___f_1780_);
lean_dec_ref(v_typeNew_1779_);
v_a_1796_ = lean_ctor_get(v___x_1793_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1798_ = v___x_1793_;
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v___x_1793_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1801_; 
if (v_isShared_1799_ == 0)
{
v___x_1801_ = v___x_1798_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_a_1796_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
}
case 8:
{
lean_object* v_declName_1804_; lean_object* v_type_1805_; lean_object* v_value_1806_; lean_object* v_body_1807_; uint8_t v_nondep_1808_; lean_object* v___x_1809_; 
lean_dec(v___x_1781_);
lean_dec(v_mvarId_1777_);
v_declName_1804_ = lean_ctor_get(v_a_1788_, 0);
lean_inc(v_declName_1804_);
v_type_1805_ = lean_ctor_get(v_a_1788_, 1);
lean_inc_ref(v_type_1805_);
v_value_1806_ = lean_ctor_get(v_a_1788_, 2);
lean_inc_ref(v_value_1806_);
v_body_1807_ = lean_ctor_get(v_a_1788_, 3);
lean_inc_ref(v_body_1807_);
v_nondep_1808_ = lean_ctor_get_uint8(v_a_1788_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_a_1788_, 4);
lean_inc(v___y_1785_);
lean_inc_ref(v___y_1784_);
lean_inc(v___y_1783_);
lean_inc_ref(v___y_1782_);
v___x_1809_ = lean_apply_6(v___f_1778_, v_type_1805_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, lean_box(0));
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
lean_dec_ref_known(v___x_1809_, 1);
v___x_1810_ = l_Lean_Expr_letE___override(v_declName_1804_, v_typeNew_1779_, v_value_1806_, v_body_1807_, v_nondep_1808_);
v___x_1811_ = lean_apply_6(v___f_1780_, v___x_1810_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, lean_box(0));
return v___x_1811_;
}
else
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1819_; 
lean_dec_ref(v_body_1807_);
lean_dec_ref(v_value_1806_);
lean_dec(v_declName_1804_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec_ref(v___f_1780_);
lean_dec_ref(v_typeNew_1779_);
v_a_1812_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1814_ = v___x_1809_;
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1809_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1817_; 
if (v_isShared_1815_ == 0)
{
v___x_1817_ = v___x_1814_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_a_1812_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
}
default: 
{
lean_object* v___x_1820_; lean_object* v___x_1821_; 
lean_dec(v_a_1788_);
lean_dec_ref(v___f_1780_);
lean_dec_ref(v_typeNew_1779_);
lean_dec_ref(v___f_1778_);
v___x_1820_ = lean_obj_once(&l_Lean_MVarId_changeLocalDecl___lam__2___closed__3, &l_Lean_MVarId_changeLocalDecl___lam__2___closed__3_once, _init_l_Lean_MVarId_changeLocalDecl___lam__2___closed__3);
v___x_1821_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1781_, v_mvarId_1777_, v___x_1820_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
return v___x_1821_;
}
}
}
else
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1829_; 
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec(v___x_1781_);
lean_dec_ref(v___f_1780_);
lean_dec_ref(v_typeNew_1779_);
lean_dec_ref(v___f_1778_);
lean_dec(v_mvarId_1777_);
v_a_1822_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1824_ = v___x_1787_;
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1787_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1827_; 
if (v_isShared_1825_ == 0)
{
v___x_1827_ = v___x_1824_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_a_1822_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_changeLocalDecl___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1777_ = stack[0].m_obj;
lean_object* v___f_1778_ = stack[1].m_obj;
lean_object* v_typeNew_1779_ = stack[2].m_obj;
lean_object* v___f_1780_ = stack[3].m_obj;
lean_object* v___x_1781_ = stack[4].m_obj;
lean_object* v___y_1782_ = stack[5].m_obj;
lean_object* v___y_1783_ = stack[6].m_obj;
lean_object* v___y_1784_ = stack[7].m_obj;
lean_object* v___y_1785_ = stack[8].m_obj;
lean_object* v_res_1830_;
v_res_1830_ = l_Lean_MVarId_changeLocalDecl___lam__2(v_mvarId_1777_, v___f_1778_, v_typeNew_1779_, v___f_1780_, v___x_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_);
stack->m_obj
 = v_res_1830_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lam__2___boxed(lean_object* v_mvarId_1831_, lean_object* v___f_1832_, lean_object* v_typeNew_1833_, lean_object* v___f_1834_, lean_object* v___x_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l_Lean_MVarId_changeLocalDecl___lam__2(v_mvarId_1831_, v___f_1832_, v_typeNew_1833_, v___f_1834_, v___x_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_);
return v_res_1841_;
}
}
lean_object* l_Lean_MVarId_changeLocalDecl___lam__3(uint8_t v_checkDefEq_1842_, lean_object* v_typeNew_1843_, lean_object* v___x_1844_, lean_object* v_mvarId_1845_, lean_object* v_fvars_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_){
_start:
{
lean_object* v___x_1852_; lean_object* v___f_1853_; lean_object* v___f_1854_; lean_object* v___f_1855_; lean_object* v___x_1856_; 
v___x_1852_ = lean_box(v_checkDefEq_1842_);
lean_inc_n(v_mvarId_1845_, 3);
lean_inc(v___x_1844_);
lean_inc_ref(v_typeNew_1843_);
v___f_1853_ = lean_alloc_closure((void*)(l_Lean_MVarId_changeLocalDecl___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1853_, 0, v___x_1852_);
lean_closure_set(v___f_1853_, 1, v_typeNew_1843_);
lean_closure_set(v___f_1853_, 2, v___x_1844_);
lean_closure_set(v___f_1853_, 3, v_mvarId_1845_);
v___f_1854_ = lean_alloc_closure((void*)(l_Lean_MVarId_changeLocalDecl___lam__1___boxed), 8, 2);
lean_closure_set(v___f_1854_, 0, v_mvarId_1845_);
lean_closure_set(v___f_1854_, 1, v_fvars_1846_);
v___f_1855_ = lean_alloc_closure((void*)(l_Lean_MVarId_changeLocalDecl___lam__2___boxed), 10, 5);
lean_closure_set(v___f_1855_, 0, v_mvarId_1845_);
lean_closure_set(v___f_1855_, 1, v___f_1853_);
lean_closure_set(v___f_1855_, 2, v_typeNew_1843_);
lean_closure_set(v___f_1855_, 3, v___f_1854_);
lean_closure_set(v___f_1855_, 4, v___x_1844_);
v___x_1856_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_1845_, v___f_1855_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_);
return v___x_1856_;
}
}
LEAN_EXPORT void l_Lean_MVarId_changeLocalDecl___lam__3_0interp(lean_interpreter_value* stack)
{
uint8_t v_checkDefEq_1842_ = stack[0].m_num;
lean_object* v_typeNew_1843_ = stack[1].m_obj;
lean_object* v___x_1844_ = stack[2].m_obj;
lean_object* v_mvarId_1845_ = stack[3].m_obj;
lean_object* v_fvars_1846_ = stack[4].m_obj;
lean_object* v___y_1847_ = stack[5].m_obj;
lean_object* v___y_1848_ = stack[6].m_obj;
lean_object* v___y_1849_ = stack[7].m_obj;
lean_object* v___y_1850_ = stack[8].m_obj;
lean_object* v_res_1857_;
v_res_1857_ = l_Lean_MVarId_changeLocalDecl___lam__3(v_checkDefEq_1842_, v_typeNew_1843_, v___x_1844_, v_mvarId_1845_, v_fvars_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_);
stack->m_obj
 = v_res_1857_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lam__3___boxed(lean_object* v_checkDefEq_1858_, lean_object* v_typeNew_1859_, lean_object* v___x_1860_, lean_object* v_mvarId_1861_, lean_object* v_fvars_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
uint8_t v_checkDefEq_boxed_1868_; lean_object* v_res_1869_; 
v_checkDefEq_boxed_1868_ = lean_unbox(v_checkDefEq_1858_);
v_res_1869_ = l_Lean_MVarId_changeLocalDecl___lam__3(v_checkDefEq_boxed_1868_, v_typeNew_1859_, v___x_1860_, v_mvarId_1861_, v_fvars_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
return v_res_1869_;
}
}
lean_object* l_Lean_MVarId_changeLocalDecl(lean_object* v_mvarId_1873_, lean_object* v_fvarId_1874_, lean_object* v_typeNew_1875_, uint8_t v_checkDefEq_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_){
_start:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___f_1884_; lean_object* v___x_1885_; 
v___x_1882_ = ((lean_object*)(l_Lean_MVarId_changeLocalDecl___closed__1));
v___x_1883_ = lean_box(v_checkDefEq_1876_);
v___f_1884_ = lean_alloc_closure((void*)(l_Lean_MVarId_changeLocalDecl___lam__3___boxed), 10, 3);
lean_closure_set(v___f_1884_, 0, v___x_1883_);
lean_closure_set(v___f_1884_, 1, v_typeNew_1875_);
lean_closure_set(v___f_1884_, 2, v___x_1882_);
lean_inc(v_mvarId_1873_);
v___x_1885_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1873_, v___x_1882_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; uint8_t v___x_1889_; lean_object* v___x_1890_; 
lean_dec_ref_known(v___x_1885_, 1);
v___x_1886_ = lean_unsigned_to_nat(1u);
v___x_1887_ = lean_mk_empty_array_with_capacity(v___x_1886_);
v___x_1888_ = lean_array_push(v___x_1887_, v_fvarId_1874_);
v___x_1889_ = 0;
v___x_1890_ = l_Lean_MVarId_withReverted___redArg(v_mvarId_1873_, v___x_1888_, v___f_1884_, v___x_1889_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
if (lean_obj_tag(v___x_1890_) == 0)
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1899_; 
v_a_1891_ = lean_ctor_get(v___x_1890_, 0);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1893_ = v___x_1890_;
v_isShared_1894_ = v_isSharedCheck_1899_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1890_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1899_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v_snd_1895_; lean_object* v___x_1897_; 
v_snd_1895_ = lean_ctor_get(v_a_1891_, 1);
lean_inc(v_snd_1895_);
lean_dec(v_a_1891_);
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 0, v_snd_1895_);
v___x_1897_ = v___x_1893_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_snd_1895_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
return v___x_1897_;
}
}
}
else
{
lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1907_; 
v_a_1900_ = lean_ctor_get(v___x_1890_, 0);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1902_ = v___x_1890_;
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_dec(v___x_1890_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1905_; 
if (v_isShared_1903_ == 0)
{
v___x_1905_ = v___x_1902_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v_a_1900_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
return v___x_1905_;
}
}
}
}
else
{
lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1915_; 
lean_dec_ref(v___f_1884_);
lean_dec(v_fvarId_1874_);
lean_dec(v_mvarId_1873_);
v_a_1908_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1910_ = v___x_1885_;
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v___x_1885_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1913_; 
if (v_isShared_1911_ == 0)
{
v___x_1913_ = v___x_1910_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_a_1908_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_changeLocalDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1873_ = stack[0].m_obj;
lean_object* v_fvarId_1874_ = stack[1].m_obj;
lean_object* v_typeNew_1875_ = stack[2].m_obj;
uint8_t v_checkDefEq_1876_ = stack[3].m_num;
lean_object* v_a_1877_ = stack[4].m_obj;
lean_object* v_a_1878_ = stack[5].m_obj;
lean_object* v_a_1879_ = stack[6].m_obj;
lean_object* v_a_1880_ = stack[7].m_obj;
lean_object* v_res_1916_;
v_res_1916_ = l_Lean_MVarId_changeLocalDecl(v_mvarId_1873_, v_fvarId_1874_, v_typeNew_1875_, v_checkDefEq_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
stack->m_obj
 = v_res_1916_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___boxed(lean_object* v_mvarId_1917_, lean_object* v_fvarId_1918_, lean_object* v_typeNew_1919_, lean_object* v_checkDefEq_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_){
_start:
{
uint8_t v_checkDefEq_boxed_1926_; lean_object* v_res_1927_; 
v_checkDefEq_boxed_1926_ = lean_unbox(v_checkDefEq_1920_);
v_res_1927_ = l_Lean_MVarId_changeLocalDecl(v_mvarId_1917_, v_fvarId_1918_, v_typeNew_1919_, v_checkDefEq_boxed_1926_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_);
lean_dec(v_a_1924_);
lean_dec_ref(v_a_1923_);
lean_dec(v_a_1922_);
lean_dec_ref(v_a_1921_);
return v_res_1927_;
}
}
lean_object* l_Lean_MVarId_modifyTarget___lam__0(lean_object* v_mvarId_1928_, lean_object* v___x_1929_, lean_object* v_f_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_){
_start:
{
lean_object* v___x_1936_; 
lean_inc(v_mvarId_1928_);
v___x_1936_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1928_, v___x_1929_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_object* v___x_1937_; 
lean_dec_ref_known(v___x_1936_, 1);
lean_inc(v_mvarId_1928_);
v___x_1937_ = l_Lean_MVarId_getType(v_mvarId_1928_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v_a_1938_; lean_object* v___x_1939_; 
v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
lean_inc(v_a_1938_);
lean_dec_ref_known(v___x_1937_, 1);
lean_inc(v___y_1934_);
lean_inc_ref(v___y_1933_);
lean_inc(v___y_1932_);
lean_inc_ref(v___y_1931_);
v___x_1939_ = lean_apply_6(v_f_1930_, v_a_1938_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, lean_box(0));
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_object* v_a_1940_; uint8_t v___x_1941_; lean_object* v___x_1942_; 
v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
lean_inc(v_a_1940_);
lean_dec_ref_known(v___x_1939_, 1);
v___x_1941_ = 0;
v___x_1942_ = l_Lean_MVarId_change(v_mvarId_1928_, v_a_1940_, v___x_1941_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
return v___x_1942_;
}
else
{
lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1950_; 
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
lean_dec(v_mvarId_1928_);
v_a_1943_ = lean_ctor_get(v___x_1939_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1945_ = v___x_1939_;
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___x_1939_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1948_; 
if (v_isShared_1946_ == 0)
{
v___x_1948_ = v___x_1945_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_a_1943_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
else
{
lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1958_; 
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
lean_dec_ref(v_f_1930_);
lean_dec(v_mvarId_1928_);
v_a_1951_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1953_ = v___x_1937_;
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v___x_1937_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1956_; 
if (v_isShared_1954_ == 0)
{
v___x_1956_ = v___x_1953_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_a_1951_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
}
}
else
{
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1966_; 
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
lean_dec_ref(v_f_1930_);
lean_dec(v_mvarId_1928_);
v_a_1959_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1961_ = v___x_1936_;
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1936_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1964_; 
if (v_isShared_1962_ == 0)
{
v___x_1964_ = v___x_1961_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v_a_1959_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_modifyTarget___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1928_ = stack[0].m_obj;
lean_object* v___x_1929_ = stack[1].m_obj;
lean_object* v_f_1930_ = stack[2].m_obj;
lean_object* v___y_1931_ = stack[3].m_obj;
lean_object* v___y_1932_ = stack[4].m_obj;
lean_object* v___y_1933_ = stack[5].m_obj;
lean_object* v___y_1934_ = stack[6].m_obj;
lean_object* v_res_1967_;
v_res_1967_ = l_Lean_MVarId_modifyTarget___lam__0(v_mvarId_1928_, v___x_1929_, v_f_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_);
stack->m_obj
 = v_res_1967_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTarget___lam__0___boxed(lean_object* v_mvarId_1968_, lean_object* v___x_1969_, lean_object* v_f_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l_Lean_MVarId_modifyTarget___lam__0(v_mvarId_1968_, v___x_1969_, v_f_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
return v_res_1976_;
}
}
lean_object* l_Lean_MVarId_modifyTarget(lean_object* v_mvarId_1980_, lean_object* v_f_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_){
_start:
{
lean_object* v___x_1987_; lean_object* v___f_1988_; lean_object* v___x_1989_; 
v___x_1987_ = ((lean_object*)(l_Lean_MVarId_modifyTarget___closed__1));
lean_inc(v_mvarId_1980_);
v___f_1988_ = lean_alloc_closure((void*)(l_Lean_MVarId_modifyTarget___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1988_, 0, v_mvarId_1980_);
lean_closure_set(v___f_1988_, 1, v___x_1987_);
lean_closure_set(v___f_1988_, 2, v_f_1981_);
v___x_1989_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_1980_, v___f_1988_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_);
return v___x_1989_;
}
}
LEAN_EXPORT void l_Lean_MVarId_modifyTarget_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1980_ = stack[0].m_obj;
lean_object* v_f_1981_ = stack[1].m_obj;
lean_object* v_a_1982_ = stack[2].m_obj;
lean_object* v_a_1983_ = stack[3].m_obj;
lean_object* v_a_1984_ = stack[4].m_obj;
lean_object* v_a_1985_ = stack[5].m_obj;
lean_object* v_res_1990_;
v_res_1990_ = l_Lean_MVarId_modifyTarget(v_mvarId_1980_, v_f_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_);
stack->m_obj
 = v_res_1990_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTarget___boxed(lean_object* v_mvarId_1991_, lean_object* v_f_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_){
_start:
{
lean_object* v_res_1998_; 
v_res_1998_ = l_Lean_MVarId_modifyTarget(v_mvarId_1991_, v_f_1992_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_);
lean_dec(v_a_1996_);
lean_dec_ref(v_a_1995_);
lean_dec(v_a_1994_);
lean_dec_ref(v_a_1993_);
return v_res_1998_;
}
}
static lean_object* _init_l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_2003_ = ((lean_object*)(l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__2));
v___x_2004_ = l_Lean_stringToMessageData(v___x_2003_);
return v___x_2004_;
}
}
lean_object* l_Lean_MVarId_modifyTargetEqLHS___lam__0(lean_object* v_f_2005_, lean_object* v_mvarId_2006_, lean_object* v_target_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_){
_start:
{
lean_object* v___x_2013_; 
lean_inc_ref(v_target_2007_);
v___x_2013_ = l_Lean_Meta_matchEq_x3f(v_target_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v_a_2014_; 
v_a_2014_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_a_2014_);
lean_dec_ref_known(v___x_2013_, 1);
if (lean_obj_tag(v_a_2014_) == 1)
{
lean_object* v_val_2015_; lean_object* v_snd_2016_; lean_object* v_fst_2017_; lean_object* v_snd_2018_; lean_object* v___x_2019_; 
lean_dec_ref(v_target_2007_);
lean_dec(v_mvarId_2006_);
v_val_2015_ = lean_ctor_get(v_a_2014_, 0);
lean_inc(v_val_2015_);
lean_dec_ref_known(v_a_2014_, 1);
v_snd_2016_ = lean_ctor_get(v_val_2015_, 1);
lean_inc(v_snd_2016_);
lean_dec(v_val_2015_);
v_fst_2017_ = lean_ctor_get(v_snd_2016_, 0);
lean_inc(v_fst_2017_);
v_snd_2018_ = lean_ctor_get(v_snd_2016_, 1);
lean_inc(v_snd_2018_);
lean_dec(v_snd_2016_);
lean_inc(v___y_2011_);
lean_inc_ref(v___y_2010_);
lean_inc(v___y_2009_);
lean_inc_ref(v___y_2008_);
v___x_2019_ = lean_apply_6(v_f_2005_, v_fst_2017_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, lean_box(0));
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v_a_2020_; lean_object* v___x_2021_; 
v_a_2020_ = lean_ctor_get(v___x_2019_, 0);
lean_inc(v_a_2020_);
lean_dec_ref_known(v___x_2019_, 1);
v___x_2021_ = l_Lean_Meta_mkEq(v_a_2020_, v_snd_2018_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_);
return v___x_2021_;
}
else
{
lean_dec(v_snd_2018_);
return v___x_2019_;
}
}
else
{
lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
lean_dec(v_a_2014_);
lean_dec_ref(v_f_2005_);
v___x_2022_ = ((lean_object*)(l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__1));
v___x_2023_ = lean_obj_once(&l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__3, &l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__3_once, _init_l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__3);
v___x_2024_ = l_Lean_indentExpr(v_target_2007_);
v___x_2025_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2025_, 0, v___x_2023_);
lean_ctor_set(v___x_2025_, 1, v___x_2024_);
v___x_2026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2026_, 0, v___x_2025_);
v___x_2027_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2022_, v_mvarId_2006_, v___x_2026_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_);
return v___x_2027_;
}
}
else
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2035_; 
lean_dec_ref(v_target_2007_);
lean_dec(v_mvarId_2006_);
lean_dec_ref(v_f_2005_);
v_a_2028_ = lean_ctor_get(v___x_2013_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2013_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2030_ = v___x_2013_;
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2013_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2031_ == 0)
{
v___x_2033_ = v___x_2030_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_a_2028_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_modifyTargetEqLHS___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2005_ = stack[0].m_obj;
lean_object* v_mvarId_2006_ = stack[1].m_obj;
lean_object* v_target_2007_ = stack[2].m_obj;
lean_object* v___y_2008_ = stack[3].m_obj;
lean_object* v___y_2009_ = stack[4].m_obj;
lean_object* v___y_2010_ = stack[5].m_obj;
lean_object* v___y_2011_ = stack[6].m_obj;
lean_object* v_res_2036_;
v_res_2036_ = l_Lean_MVarId_modifyTargetEqLHS___lam__0(v_f_2005_, v_mvarId_2006_, v_target_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_);
stack->m_obj
 = v_res_2036_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTargetEqLHS___lam__0___boxed(lean_object* v_f_2037_, lean_object* v_mvarId_2038_, lean_object* v_target_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v_res_2045_; 
v_res_2045_ = l_Lean_MVarId_modifyTargetEqLHS___lam__0(v_f_2037_, v_mvarId_2038_, v_target_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
lean_dec(v___y_2043_);
lean_dec_ref(v___y_2042_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
return v_res_2045_;
}
}
lean_object* l_Lean_MVarId_modifyTargetEqLHS(lean_object* v_mvarId_2046_, lean_object* v_f_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_){
_start:
{
lean_object* v___f_2053_; lean_object* v___x_2054_; 
lean_inc(v_mvarId_2046_);
v___f_2053_ = lean_alloc_closure((void*)(l_Lean_MVarId_modifyTargetEqLHS___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2053_, 0, v_f_2047_);
lean_closure_set(v___f_2053_, 1, v_mvarId_2046_);
v___x_2054_ = l_Lean_MVarId_modifyTarget(v_mvarId_2046_, v___f_2053_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_);
return v___x_2054_;
}
}
LEAN_EXPORT void l_Lean_MVarId_modifyTargetEqLHS_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2046_ = stack[0].m_obj;
lean_object* v_f_2047_ = stack[1].m_obj;
lean_object* v_a_2048_ = stack[2].m_obj;
lean_object* v_a_2049_ = stack[3].m_obj;
lean_object* v_a_2050_ = stack[4].m_obj;
lean_object* v_a_2051_ = stack[5].m_obj;
lean_object* v_res_2055_;
v_res_2055_ = l_Lean_MVarId_modifyTargetEqLHS(v_mvarId_2046_, v_f_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_);
stack->m_obj
 = v_res_2055_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTargetEqLHS___boxed(lean_object* v_mvarId_2056_, lean_object* v_f_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_){
_start:
{
lean_object* v_res_2063_; 
v_res_2063_ = l_Lean_MVarId_modifyTargetEqLHS(v_mvarId_2056_, v_f_2057_, v_a_2058_, v_a_2059_, v_a_2060_, v_a_2061_);
lean_dec(v_a_2061_);
lean_dec_ref(v_a_2060_);
lean_dec(v_a_2059_);
lean_dec_ref(v_a_2058_);
return v_res_2063_;
}
}
static lean_object* _init_l_Lean_MVarId_clearValue___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2065_ = ((lean_object*)(l_Lean_MVarId_clearValue___lam__0___closed__0));
v___x_2066_ = l_Lean_stringToMessageData(v___x_2065_);
return v___x_2066_;
}
}
static lean_object* _init_l_Lean_MVarId_clearValue___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2068_ = ((lean_object*)(l_Lean_MVarId_clearValue___lam__0___closed__2));
v___x_2069_ = l_Lean_stringToMessageData(v___x_2068_);
return v___x_2069_;
}
}
static lean_object* _init_l_Lean_MVarId_clearValue___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2071_ = ((lean_object*)(l_Lean_MVarId_clearValue___lam__0___closed__4));
v___x_2072_ = l_Lean_stringToMessageData(v___x_2071_);
return v___x_2072_;
}
}
static lean_object* _init_l_Lean_MVarId_clearValue___lam__0___closed__7(void){
_start:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2074_ = ((lean_object*)(l_Lean_MVarId_clearValue___lam__0___closed__6));
v___x_2075_ = l_Lean_stringToMessageData(v___x_2074_);
return v___x_2075_;
}
}
lean_object* l_Lean_MVarId_clearValue___lam__0(lean_object* v_mvarId_x27_2076_, lean_object* v_a_2077_, lean_object* v_fvars_2078_, lean_object* v_fvarId_2079_, lean_object* v___x_2080_, lean_object* v_mvarId_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_){
_start:
{
lean_object* v___x_2087_; 
lean_inc(v_mvarId_x27_2076_);
v___x_2087_ = l_Lean_MVarId_getType(v_mvarId_x27_2076_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v_a_2088_; lean_object* v___y_2090_; lean_object* v___y_2091_; lean_object* v___y_2092_; lean_object* v___y_2093_; lean_object* v___y_2094_; lean_object* v___y_2124_; lean_object* v___y_2125_; lean_object* v___y_2126_; lean_object* v___y_2127_; uint8_t v___x_2169_; 
v_a_2088_ = lean_ctor_get(v___x_2087_, 0);
lean_inc(v_a_2088_);
lean_dec_ref_known(v___x_2087_, 1);
v___x_2169_ = l_Lean_Expr_isLet(v_a_2088_);
if (v___x_2169_ == 0)
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2170_ = lean_obj_once(&l_Lean_MVarId_clearValue___lam__0___closed__5, &l_Lean_MVarId_clearValue___lam__0___closed__5_once, _init_l_Lean_MVarId_clearValue___lam__0___closed__5);
lean_inc(v_fvarId_2079_);
v___x_2171_ = l_Lean_Expr_fvar___override(v_fvarId_2079_);
v___x_2172_ = l_Lean_MessageData_ofExpr(v___x_2171_);
v___x_2173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2173_, 0, v___x_2170_);
lean_ctor_set(v___x_2173_, 1, v___x_2172_);
v___x_2174_ = lean_obj_once(&l_Lean_MVarId_clearValue___lam__0___closed__7, &l_Lean_MVarId_clearValue___lam__0___closed__7_once, _init_l_Lean_MVarId_clearValue___lam__0___closed__7);
v___x_2175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2175_, 0, v___x_2173_);
lean_ctor_set(v___x_2175_, 1, v___x_2174_);
v___x_2176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2175_);
lean_inc_n(v_mvarId_2081_, 2);
lean_inc(v___x_2080_);
v___x_2177_ = lean_alloc_closure((void*)(l_Lean_Meta_throwTacticEx___boxed), 9, 4);
lean_closure_set(v___x_2177_, 0, lean_box(0));
lean_closure_set(v___x_2177_, 1, v___x_2080_);
lean_closure_set(v___x_2177_, 2, v_mvarId_2081_);
lean_closure_set(v___x_2177_, 3, v___x_2176_);
v___x_2178_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_2081_, v___x_2177_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_dec_ref_known(v___x_2178_, 1);
v___y_2124_ = v___y_2082_;
v___y_2125_ = v___y_2083_;
v___y_2126_ = v___y_2084_;
v___y_2127_ = v___y_2085_;
goto v___jp_2123_;
}
else
{
lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2186_; 
lean_dec(v_a_2088_);
lean_dec(v_mvarId_2081_);
lean_dec(v___x_2080_);
lean_dec(v_fvarId_2079_);
lean_dec_ref(v_fvars_2078_);
lean_dec(v_a_2077_);
lean_dec(v_mvarId_x27_2076_);
v_a_2179_ = lean_ctor_get(v___x_2178_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2181_ = v___x_2178_;
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_dec(v___x_2178_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2184_; 
if (v_isShared_2182_ == 0)
{
v___x_2184_ = v___x_2181_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_a_2179_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
}
else
{
v___y_2124_ = v___y_2082_;
v___y_2125_ = v___y_2083_;
v___y_2126_ = v___y_2084_;
v___y_2127_ = v___y_2085_;
goto v___jp_2123_;
}
v___jp_2089_:
{
lean_object* v___x_2095_; 
v___x_2095_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_2090_, v_a_2077_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_a_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2113_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
lean_inc_n(v_a_2096_, 2);
lean_dec_ref_known(v___x_2095_, 1);
v___x_2097_ = l_Lean_Expr_letValue_x21(v_a_2088_);
lean_dec(v_a_2088_);
v___x_2098_ = l_Lean_Expr_app___override(v_a_2096_, v___x_2097_);
v___x_2099_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg(v_mvarId_x27_2076_, v___x_2098_, v___y_2092_);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2113_ == 0)
{
lean_object* v_unused_2114_; 
v_unused_2114_ = lean_ctor_get(v___x_2099_, 0);
lean_dec(v_unused_2114_);
v___x_2101_ = v___x_2099_;
v_isShared_2102_ = v_isSharedCheck_2113_;
goto v_resetjp_2100_;
}
else
{
lean_dec(v___x_2099_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2113_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2103_; size_t v_sz_2104_; size_t v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2111_; 
v___x_2103_ = lean_box(0);
v_sz_2104_ = lean_array_size(v_fvars_2078_);
v___x_2105_ = ((size_t)0ULL);
v___x_2106_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_changeLocalDecl_spec__0(v_sz_2104_, v___x_2105_, v_fvars_2078_);
v___x_2107_ = l_Lean_Expr_mvarId_x21(v_a_2096_);
lean_dec(v_a_2096_);
v___x_2108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2106_);
lean_ctor_set(v___x_2108_, 1, v___x_2107_);
v___x_2109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2103_);
lean_ctor_set(v___x_2109_, 1, v___x_2108_);
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 0, v___x_2109_);
v___x_2111_ = v___x_2101_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v___x_2109_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
}
else
{
lean_object* v_a_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2122_; 
lean_dec(v_a_2088_);
lean_dec_ref(v_fvars_2078_);
lean_dec(v_mvarId_x27_2076_);
v_a_2115_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2117_ = v___x_2095_;
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_a_2115_);
lean_dec(v___x_2095_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___x_2120_; 
if (v_isShared_2118_ == 0)
{
v___x_2120_ = v___x_2117_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_a_2115_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
}
}
v___jp_2123_:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; uint8_t v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2168_; 
v___x_2128_ = l_Lean_Expr_letName_x21(v_a_2088_);
v___x_2129_ = l_Lean_Expr_letType_x21(v_a_2088_);
v___x_2130_ = l_Lean_Expr_letBody_x21(v_a_2088_);
v___x_2131_ = 0;
v___x_2132_ = l_Lean_Expr_forallE___override(v___x_2128_, v___x_2129_, v___x_2130_, v___x_2131_);
v___x_2133_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(v___x_2132_, v___y_2125_);
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2136_ = v___x_2133_;
v_isShared_2137_ = v_isSharedCheck_2168_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2133_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2168_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2138_; 
lean_inc(v_a_2134_);
v___x_2138_ = l_Lean_Meta_isTypeCorrect(v_a_2134_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v_a_2139_; uint8_t v___x_2140_; 
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_a_2139_);
lean_dec_ref_known(v___x_2138_, 1);
v___x_2140_ = lean_unbox(v_a_2139_);
lean_dec(v_a_2139_);
if (v___x_2140_ == 0)
{
lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2148_; 
v___x_2141_ = lean_obj_once(&l_Lean_MVarId_clearValue___lam__0___closed__1, &l_Lean_MVarId_clearValue___lam__0___closed__1_once, _init_l_Lean_MVarId_clearValue___lam__0___closed__1);
v___x_2142_ = l_Lean_Expr_fvar___override(v_fvarId_2079_);
v___x_2143_ = l_Lean_MessageData_ofExpr(v___x_2142_);
v___x_2144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2144_, 0, v___x_2141_);
lean_ctor_set(v___x_2144_, 1, v___x_2143_);
v___x_2145_ = lean_obj_once(&l_Lean_MVarId_clearValue___lam__0___closed__3, &l_Lean_MVarId_clearValue___lam__0___closed__3_once, _init_l_Lean_MVarId_clearValue___lam__0___closed__3);
v___x_2146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2146_, 0, v___x_2144_);
lean_ctor_set(v___x_2146_, 1, v___x_2145_);
if (v_isShared_2137_ == 0)
{
lean_ctor_set_tag(v___x_2136_, 1);
lean_ctor_set(v___x_2136_, 0, v___x_2146_);
v___x_2148_ = v___x_2136_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v___x_2146_);
v___x_2148_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; 
lean_inc(v_mvarId_2081_);
v___x_2149_ = lean_alloc_closure((void*)(l_Lean_Meta_throwTacticEx___boxed), 9, 4);
lean_closure_set(v___x_2149_, 0, lean_box(0));
lean_closure_set(v___x_2149_, 1, v___x_2080_);
lean_closure_set(v___x_2149_, 2, v_mvarId_2081_);
lean_closure_set(v___x_2149_, 3, v___x_2148_);
v___x_2150_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_2081_, v___x_2149_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_dec_ref_known(v___x_2150_, 1);
v___y_2090_ = v_a_2134_;
v___y_2091_ = v___y_2124_;
v___y_2092_ = v___y_2125_;
v___y_2093_ = v___y_2126_;
v___y_2094_ = v___y_2127_;
goto v___jp_2089_;
}
else
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2158_; 
lean_dec(v_a_2134_);
lean_dec(v_a_2088_);
lean_dec_ref(v_fvars_2078_);
lean_dec(v_a_2077_);
lean_dec(v_mvarId_x27_2076_);
v_a_2151_ = lean_ctor_get(v___x_2150_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2153_ = v___x_2150_;
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2150_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2156_; 
if (v_isShared_2154_ == 0)
{
v___x_2156_ = v___x_2153_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2151_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
}
}
else
{
lean_del_object(v___x_2136_);
lean_dec(v_mvarId_2081_);
lean_dec(v___x_2080_);
lean_dec(v_fvarId_2079_);
v___y_2090_ = v_a_2134_;
v___y_2091_ = v___y_2124_;
v___y_2092_ = v___y_2125_;
v___y_2093_ = v___y_2126_;
v___y_2094_ = v___y_2127_;
goto v___jp_2089_;
}
}
else
{
lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2167_; 
lean_del_object(v___x_2136_);
lean_dec(v_a_2134_);
lean_dec(v_a_2088_);
lean_dec(v_mvarId_2081_);
lean_dec(v___x_2080_);
lean_dec(v_fvarId_2079_);
lean_dec_ref(v_fvars_2078_);
lean_dec(v_a_2077_);
lean_dec(v_mvarId_x27_2076_);
v_a_2160_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2162_ = v___x_2138_;
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v___x_2138_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2165_; 
if (v_isShared_2163_ == 0)
{
v___x_2165_ = v___x_2162_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_a_2160_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
}
}
}
else
{
lean_object* v_a_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2194_; 
lean_dec(v_mvarId_2081_);
lean_dec(v___x_2080_);
lean_dec(v_fvarId_2079_);
lean_dec_ref(v_fvars_2078_);
lean_dec(v_a_2077_);
lean_dec(v_mvarId_x27_2076_);
v_a_2187_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2194_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2189_ = v___x_2087_;
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_a_2187_);
lean_dec(v___x_2087_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v___x_2192_; 
if (v_isShared_2190_ == 0)
{
v___x_2192_ = v___x_2189_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v_a_2187_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_clearValue___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_x27_2076_ = stack[0].m_obj;
lean_object* v_a_2077_ = stack[1].m_obj;
lean_object* v_fvars_2078_ = stack[2].m_obj;
lean_object* v_fvarId_2079_ = stack[3].m_obj;
lean_object* v___x_2080_ = stack[4].m_obj;
lean_object* v_mvarId_2081_ = stack[5].m_obj;
lean_object* v___y_2082_ = stack[6].m_obj;
lean_object* v___y_2083_ = stack[7].m_obj;
lean_object* v___y_2084_ = stack[8].m_obj;
lean_object* v___y_2085_ = stack[9].m_obj;
lean_object* v_res_2195_;
v_res_2195_ = l_Lean_MVarId_clearValue___lam__0(v_mvarId_x27_2076_, v_a_2077_, v_fvars_2078_, v_fvarId_2079_, v___x_2080_, v_mvarId_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
stack->m_obj
 = v_res_2195_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearValue___lam__0___boxed(lean_object* v_mvarId_x27_2196_, lean_object* v_a_2197_, lean_object* v_fvars_2198_, lean_object* v_fvarId_2199_, lean_object* v___x_2200_, lean_object* v_mvarId_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_){
_start:
{
lean_object* v_res_2207_; 
v_res_2207_ = l_Lean_MVarId_clearValue___lam__0(v_mvarId_x27_2196_, v_a_2197_, v_fvars_2198_, v_fvarId_2199_, v___x_2200_, v_mvarId_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
lean_dec(v___y_2203_);
lean_dec_ref(v___y_2202_);
return v_res_2207_;
}
}
lean_object* l_Lean_MVarId_clearValue___lam__1(lean_object* v_a_2208_, lean_object* v_fvarId_2209_, lean_object* v___x_2210_, lean_object* v_mvarId_2211_, lean_object* v_mvarId_x27_2212_, lean_object* v_fvars_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
lean_object* v___f_2219_; lean_object* v___x_2220_; 
lean_inc(v_mvarId_x27_2212_);
v___f_2219_ = lean_alloc_closure((void*)(l_Lean_MVarId_clearValue___lam__0___boxed), 11, 6);
lean_closure_set(v___f_2219_, 0, v_mvarId_x27_2212_);
lean_closure_set(v___f_2219_, 1, v_a_2208_);
lean_closure_set(v___f_2219_, 2, v_fvars_2213_);
lean_closure_set(v___f_2219_, 3, v_fvarId_2209_);
lean_closure_set(v___f_2219_, 4, v___x_2210_);
lean_closure_set(v___f_2219_, 5, v_mvarId_2211_);
v___x_2220_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_x27_2212_, v___f_2219_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
return v___x_2220_;
}
}
LEAN_EXPORT void l_Lean_MVarId_clearValue___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2208_ = stack[0].m_obj;
lean_object* v_fvarId_2209_ = stack[1].m_obj;
lean_object* v___x_2210_ = stack[2].m_obj;
lean_object* v_mvarId_2211_ = stack[3].m_obj;
lean_object* v_mvarId_x27_2212_ = stack[4].m_obj;
lean_object* v_fvars_2213_ = stack[5].m_obj;
lean_object* v___y_2214_ = stack[6].m_obj;
lean_object* v___y_2215_ = stack[7].m_obj;
lean_object* v___y_2216_ = stack[8].m_obj;
lean_object* v___y_2217_ = stack[9].m_obj;
lean_object* v_res_2221_;
v_res_2221_ = l_Lean_MVarId_clearValue___lam__1(v_a_2208_, v_fvarId_2209_, v___x_2210_, v_mvarId_2211_, v_mvarId_x27_2212_, v_fvars_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
stack->m_obj
 = v_res_2221_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearValue___lam__1___boxed(lean_object* v_a_2222_, lean_object* v_fvarId_2223_, lean_object* v___x_2224_, lean_object* v_mvarId_2225_, lean_object* v_mvarId_x27_2226_, lean_object* v_fvars_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
lean_object* v_res_2233_; 
v_res_2233_ = l_Lean_MVarId_clearValue___lam__1(v_a_2222_, v_fvarId_2223_, v___x_2224_, v_mvarId_2225_, v_mvarId_x27_2226_, v_fvars_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
return v_res_2233_;
}
}
lean_object* l_Lean_MVarId_clearValue(lean_object* v_mvarId_2237_, lean_object* v_fvarId_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_){
_start:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2244_ = ((lean_object*)(l_Lean_MVarId_clearValue___closed__1));
lean_inc(v_mvarId_2237_);
v___x_2245_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2237_, v___x_2244_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_);
if (lean_obj_tag(v___x_2245_) == 0)
{
lean_object* v___x_2246_; 
lean_dec_ref_known(v___x_2245_, 1);
lean_inc(v_mvarId_2237_);
v___x_2246_ = l_Lean_MVarId_getTag(v_mvarId_2237_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_);
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_object* v_a_2247_; lean_object* v___f_2248_; lean_object* v___x_2249_; 
v_a_2247_ = lean_ctor_get(v___x_2246_, 0);
lean_inc(v_a_2247_);
lean_dec_ref_known(v___x_2246_, 1);
lean_inc(v_mvarId_2237_);
lean_inc(v_fvarId_2238_);
v___f_2248_ = lean_alloc_closure((void*)(l_Lean_MVarId_clearValue___lam__1___boxed), 11, 4);
lean_closure_set(v___f_2248_, 0, v_a_2247_);
lean_closure_set(v___f_2248_, 1, v_fvarId_2238_);
lean_closure_set(v___f_2248_, 2, v___x_2244_);
lean_closure_set(v___f_2248_, 3, v_mvarId_2237_);
v___x_2249_ = l_Lean_MVarId_withRevertedFrom___redArg(v_mvarId_2237_, v_fvarId_2238_, v___f_2248_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_);
if (lean_obj_tag(v___x_2249_) == 0)
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2258_; 
v_a_2250_ = lean_ctor_get(v___x_2249_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2252_ = v___x_2249_;
v_isShared_2253_ = v_isSharedCheck_2258_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2249_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2258_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v_snd_2254_; lean_object* v___x_2256_; 
v_snd_2254_ = lean_ctor_get(v_a_2250_, 1);
lean_inc(v_snd_2254_);
lean_dec(v_a_2250_);
if (v_isShared_2253_ == 0)
{
lean_ctor_set(v___x_2252_, 0, v_snd_2254_);
v___x_2256_ = v___x_2252_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_snd_2254_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
else
{
lean_object* v_a_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2266_; 
v_a_2259_ = lean_ctor_get(v___x_2249_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2261_ = v___x_2249_;
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_a_2259_);
lean_dec(v___x_2249_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2264_; 
if (v_isShared_2262_ == 0)
{
v___x_2264_ = v___x_2261_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_a_2259_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
}
else
{
lean_object* v_a_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2274_; 
lean_dec(v_fvarId_2238_);
lean_dec(v_mvarId_2237_);
v_a_2267_ = lean_ctor_get(v___x_2246_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2269_ = v___x_2246_;
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_a_2267_);
lean_dec(v___x_2246_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v___x_2272_; 
if (v_isShared_2270_ == 0)
{
v___x_2272_ = v___x_2269_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_a_2267_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
}
else
{
lean_object* v_a_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2282_; 
lean_dec(v_fvarId_2238_);
lean_dec(v_mvarId_2237_);
v_a_2275_ = lean_ctor_get(v___x_2245_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2277_ = v___x_2245_;
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_a_2275_);
lean_dec(v___x_2245_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2280_; 
if (v_isShared_2278_ == 0)
{
v___x_2280_ = v___x_2277_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_a_2275_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_clearValue_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2237_ = stack[0].m_obj;
lean_object* v_fvarId_2238_ = stack[1].m_obj;
lean_object* v_a_2239_ = stack[2].m_obj;
lean_object* v_a_2240_ = stack[3].m_obj;
lean_object* v_a_2241_ = stack[4].m_obj;
lean_object* v_a_2242_ = stack[5].m_obj;
lean_object* v_res_2283_;
v_res_2283_ = l_Lean_MVarId_clearValue(v_mvarId_2237_, v_fvarId_2238_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_);
stack->m_obj
 = v_res_2283_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearValue___boxed(lean_object* v_mvarId_2284_, lean_object* v_fvarId_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l_Lean_MVarId_clearValue(v_mvarId_2284_, v_fvarId_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
lean_dec(v_a_2289_);
lean_dec_ref(v_a_2288_);
lean_dec(v_a_2287_);
lean_dec_ref(v_a_2286_);
return v_res_2291_;
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
